#!/usr/bin/env python3
"""Workstream E, numeric probe n02.

(a) Compare the closed forms In / Ip of Model/Device.lean with an independently
    written textbook piecewise Shichman-Hodges model that decides source and
    drain from the terminal voltages (so reverse conduction is covered).
(b) Random + corner search over the parameter box and the stated voltage ranges
    for a violation of any of the six margin theorems of Proofs/Margins.lean.
(c) Tightness: the true minimum of the device current over the box, compared
    with each claimed margin.

Fixed seed; no project code is imported.
"""
import itertools
import numpy as np

rng = np.random.default_rng(20261109)

# ---- the illustrative record (copied from designs/illustrative-1v8.json) ----
VDDlo, VDDhi = 1.62, 1.98
knlo, knhi = 160.0, 240.0
kplo, kphi = 80.0, 120.0
Vtnlo, Vtnhi = 0.45, 0.60
Vtplo, Vtphi = 0.45, 0.60
Clo, Chi = 5.0, 20.0
eps = 2.0
VIL, VIH, VOL, VOH = 0.40, 1.25, 0.25, 1.35
Vlo, Vhi = -0.10, 2.08
uHi, uLo = 0.77, 0.74


def psq(x):
    return np.maximum(x, 0.0) ** 2


# ---- closed forms exactly as in Model/Device.lean ----
def In(th, u, v):
    VDD, kn, kp, Vtn, Vtp = th
    return kn / 2 * (psq(u - Vtn) - psq(u - v - Vtn))


def Ip(th, u, v):
    VDD, kn, kp, Vtn, Vtp = th
    return kp / 2 * (psq(VDD - u - Vtp) - psq(v - u - Vtp))


def Inet(th, u, v):
    return Ip(th, u, v) - In(th, u, v)


# ---- independent textbook model: piecewise regions, source chosen by voltage ----
def nmos_textbook(k, Vt, vg, va, vb):
    """Current flowing from terminal a to terminal b through an NMOS channel."""
    if va >= vb:
        vd, vs, sign = va, vb, 1.0
    else:
        vd, vs, sign = vb, va, -1.0
    vgs, vds = vg - vs, vd - vs
    if vgs <= Vt:
        i = 0.0                                     # cutoff
    elif vds < vgs - Vt:
        i = k * ((vgs - Vt) * vds - vds ** 2 / 2)   # triode
    else:
        i = k / 2 * (vgs - Vt) ** 2                 # saturation
    return sign * i


def pmos_textbook(k, Vt, vg, va, vb):
    """Current flowing from terminal a to terminal b through a PMOS channel
    (Vt is the threshold magnitude)."""
    if va >= vb:
        vs, vd, sign = va, vb, 1.0
    else:
        vs, vd, sign = vb, va, -1.0
    vsg, vsd = vs - vg, vs - vd
    if vsg <= Vt:
        i = 0.0
    elif vsd < vsg - Vt:
        i = k * ((vsg - Vt) * vsd - vsd ** 2 / 2)
    else:
        i = k / 2 * (vsg - Vt) ** 2
    return sign * i


def sample_theta(n):
    return np.column_stack([
        rng.uniform(VDDlo, VDDhi, n), rng.uniform(knlo, knhi, n), rng.uniform(kplo, kphi, n),
        rng.uniform(Vtnlo, Vtnhi, n), rng.uniform(Vtplo, Vtphi, n)])


corners = [np.array(c) for c in itertools.product((VDDlo, VDDhi), (knlo, knhi), (kplo, kphi),
                                                    (Vtnlo, Vtnhi), (Vtplo, Vtphi))]

# (a) device law
N = 200_000
th = sample_theta(N)
u = rng.uniform(-1.0, 3.0, N)
v = rng.uniform(-1.0, 3.0, N)
worst_n = worst_p = 0.0
for i in range(N):
    VDD, kn, kp, Vtn, Vtp = th[i]
    a = nmos_textbook(kn, Vtn, u[i], v[i], 0.0)       # output node -> ground
    b = pmos_textbook(kp, Vtp, u[i], VDD, v[i])       # supply -> output node
    worst_n = max(worst_n, abs(a - In(th[i], u[i], v[i])))
    worst_p = max(worst_p, abs(b - Ip(th[i], u[i], v[i])))
print(f"(a) max |textbook - closed form| over {N} points, u,v in [-1,3]:  NMOS {worst_n:.3e}  PMOS {worst_p:.3e}")
# on-for-the-right-inputs sanity at nominal
nom = np.array([1.8, 200.0, 100.0, 0.5, 0.5])
print("    nominal: In(u=1.8,v=0.9) =", In(nom, 1.8, 0.9), " In(u=0,v=0.9) =", In(nom, 0.0, 0.9),
      " Ip(u=0,v=0.9) =", Ip(nom, 0.0, 0.9), " Ip(u=1.8,v=0.9) =", Ip(nom, 1.8, 0.9))


def Iup(c):
    return kplo / 2 * (psq(VDDlo - VIL - Vtphi) - psq(c - VIL - Vtphi)) - knhi / 2 * psq(VIL - Vtnlo)


def Idn(c):
    return knlo / 2 * (psq(VIH - Vtnhi) - psq(VIH - c - Vtnhi)) - kphi / 2 * psq(VDDhi - VIH - Vtplo)


RhiP = kplo / 2 * (psq(VDDlo - uHi - Vtphi + (Vhi - VDDhi)) - psq(VDDlo - uHi - Vtphi))
RhiN = knlo / 2 * (psq(uHi - Vtnhi) - psq(uHi - Vhi - Vtnhi))
RloN = knlo / 2 * (psq(uLo - Vlo - Vtnhi) - psq(uLo - Vtnhi))
RloP = kplo / 2 * (psq(VDDlo - uLo - Vtphi) - psq(Vlo - uLo - Vtphi))

# (b) violation search. Each line: the theorem's inequality, min slack found (must be >= 0)
N = 2_000_000
viol = {}


def thetas(n):
    t = sample_theta(n)
    # mix in exact corners so that worst cases are hit
    idx = rng.integers(0, len(corners), n // 4)
    t[: n // 4] = np.array(corners)[idx]
    return (t[:, 0], t[:, 1], t[:, 2], t[:, 3], t[:, 4])


T = thetas(N)
# Inet_ge_Iup: u <= VIL, v <= c <= VDDlo  ==>  Iup c <= Inet
c = rng.uniform(-0.5, VDDlo, N)
uu = VIL - rng.exponential(0.5, N) * rng.integers(0, 2, N)
vv = c - rng.exponential(0.3, N) * rng.integers(0, 2, N)
viol["Inet_ge_Iup        (Iup c <= Inet)"] = np.min(Inet(T, uu, vv) - Iup(c))
# Inet_le_neg_Idn: VIH <= u, 0 <= c <= v ==> Inet <= -Idn c
c = rng.uniform(0.0, 2.5, N)
uu = VIH + rng.exponential(0.5, N) * rng.integers(0, 2, N)
vv = c + rng.exponential(0.3, N) * rng.integers(0, 2, N)
viol["Inet_le_neg_Idn    (Inet <= -Idn c)"] = np.min(-Idn(c) - Inet(T, uu, vv))
# boundary lemmas
uu = uHi - rng.exponential(0.5, N) * rng.integers(0, 2, N)
viol["Inet_Vhi_le_neg_RhiP (u <= uHi)"] = np.min(-RhiP - Inet(T, uu, Vhi))
uu = uHi + rng.exponential(0.5, N) * rng.integers(0, 2, N)
viol["Inet_Vhi_le_neg_RhiN (uHi <= u)"] = np.min(-RhiN - Inet(T, uu, Vhi))
uu = uLo + rng.exponential(0.5, N) * rng.integers(0, 2, N)
viol["RloN_le_Inet_Vlo     (uLo <= u)"] = np.min(Inet(T, uu, Vlo) - RloN)
uu = uLo - rng.exponential(0.5, N) * rng.integers(0, 2, N)
viol["RloP_le_Inet_Vlo     (u <= uLo)"] = np.min(Inet(T, uu, Vlo) - RloP)
uu = rng.uniform(-3, 5, N)
viol["Inet_Vhi_lt          (all u)   "] = np.min(-eps - Inet(T, uu, Vhi))
viol["Inet_Vlo_gt          (all u)   "] = np.min(Inet(T, uu, Vlo) - eps)
print(f"(b) minimum slack found over {N} samples per theorem (a negative number would contradict a Lean theorem):")
for k, s in viol.items():
    print(f"    {k:38s} {s:+.6f}  {'ok' if s >= -1e-9 else 'VIOLATION'}")


# (c) true extremes over the box. For fixed (u, v) the current Inet is monotone in each of the
# five parameters (linear in kn, kp with a bracket of fixed sign at v = Vhi or v = Vlo; monotone
# in VDD, Vtn, Vtp because psq is monotone and convex), so the extreme over the box is attained
# at one of the 32 corners. Over u a dense grid (step 1e-4 V on [-2, 4]) is used; outside that
# range the inward current only grows.
def true_min_restoring(vb, sign):
    us = np.linspace(-2.0, 4.0, 60001)
    best = (np.inf, None, None)
    for cth in corners:
        vals = sign * Inet(cth, us, vb)
        i = int(np.argmin(vals))
        if vals[i] < best[0]:
            best = (float(vals[i]), float(us[i]), cth)
    return best


m_hi = true_min_restoring(Vhi, -1.0)
m_lo = true_min_restoring(Vlo, +1.0)
print("(c) true minimum inward device current at the safe-domain ends (32 corners x dense grid in u):")
print(f"    at Vhi: {m_hi[0]:.4f} uA at u = {m_hi[1]:.4f}, theta = {m_hi[2]}   proved bound min(RhiP, RhiN) = {min(RhiP, RhiN):.4f}")
print(f"    at Vlo: {m_lo[0]:.4f} uA at u = {m_lo[1]:.4f}, theta = {m_lo[2]}   proved bound min(RloN, RloP) = {min(RloN, RloP):.4f}")
print(f"    => by this enumeration the node cannot leave the safe domain for any eps below {min(m_hi[0], m_lo[0]):.4f} uA;")
print(f"       largest eps accepted by Admissible: {min(RhiP, RhiN, RloN, RloP):.4f} uA  (ratio {min(m_hi[0], m_lo[0]) / min(RhiP, RhiN, RloN, RloP):.2f})")
# pull-up / pull-down margins are attained at a corner
wc_up = np.array([VDDlo, knhi, kplo, Vtnlo, Vtphi])
wc_dn = np.array([VDDhi, knlo, kphi, Vtnhi, Vtplo])
print(f"    Iup(VOH) = {Iup(VOH):.4f} ; Inet at (weak pull-up corner, u = VIL, v = VOH) = {Inet(wc_up, VIL, VOH):.4f}")
print(f"    Idn(VOL) = {Idn(VOL):.4f} ; -Inet at (weak pull-down corner, u = VIH, v = VOL) = {-Inet(wc_dn, VIH, VOL):.4f}")
# best possible split points for the present proof technique
us = np.linspace(0.5, 1.2, 70001)
best_hi = max(zip(np.minimum(kplo / 2 * (psq(VDDlo - us - Vtphi + (Vhi - VDDhi)) - psq(VDDlo - us - Vtphi)),
                             knlo / 2 * (psq(us - Vtnhi) - psq(us - Vhi - Vtnhi))), us))
best_lo = max(zip(np.minimum(knlo / 2 * (psq(us - Vlo - Vtnhi) - psq(us - Vtnhi)),
                             kplo / 2 * (psq(VDDlo - us - Vtphi) - psq(Vlo - us - Vtphi))), us))
print(f"    best achievable min(RhiP,RhiN) over uHi: {best_hi[0]:.4f} at uHi = {best_hi[1]:.4f}")
print(f"    best achievable min(RloN,RloP) over uLo: {best_lo[0]:.4f} at uLo = {best_lo[1]:.4f}")
