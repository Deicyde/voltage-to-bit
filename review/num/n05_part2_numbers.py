#!/usr/bin/env python3
"""Workstream E, Part 2 (commit 9b13e95), numeric probe n05.

(a) The record restricted to one supply value V0 (Design.atSupply): all six
    margins over a grid of V0 in [VDDlo, VDDhi], compared with eps and with the
    margins of the unrestricted record; and RhiN' of Proofs/AtSupply.lean.
(b) True minimum inward device current at the SUPPLY-RELATIVE top of the
    domain, v = VDD + 0.10 (the notes file says "about 3.6 uA").
(c) The two slew numbers of Examples (28.5508 and 58.3144 V/ns), exactly, and
    the true suprema they bound.
(d) Per-instant parameter choice: slowest rise when the box point may change
    with the state, compared with the fixed-corner worst case of Part 1
    (they must agree: the worst corner does not depend on the state here).
"""
import itertools
from fractions import Fraction as Fr
import numpy as np

VDDlo, VDDhi = Fr("1.62"), Fr("1.98")
knlo, knhi = Fr(160), Fr(240)
kplo, kphi = Fr(80), Fr(120)
Vtnlo, Vtnhi = Fr("0.45"), Fr("0.60")
Vtplo, Vtphi = Fr("0.45"), Fr("0.60")
Clo, Chi, eps = Fr(5), Fr(20), Fr(2)
VIL, VIH, VOL, VOH = Fr("0.40"), Fr("1.25"), Fr("0.25"), Fr("1.35")
Vlo, Vhi = Fr("-0.10"), Fr("2.08")
uHi, uLo = Fr("0.77"), Fr("0.74")


def psq(x):
    return x * x if x > 0 else Fr(0)


def margins(vddlo, vddhi, vhi):
    up = kplo / 2 * (psq(vddlo - VIL - Vtphi) - psq(VOH - VIL - Vtphi)) - knhi / 2 * psq(VIL - Vtnlo)
    dn = knlo / 2 * (psq(VIH - Vtnhi) - psq(VIH - VOL - Vtnhi)) - kphi / 2 * psq(vddhi - VIH - Vtplo)
    hiP = kplo / 2 * (psq(vddlo - uHi - Vtphi + (vhi - vddhi)) - psq(vddlo - uHi - Vtphi))
    hiN = knlo / 2 * (psq(uHi - Vtnhi) - psq(uHi - vhi - Vtnhi))
    loN = knlo / 2 * (psq(uLo - Vlo - Vtnhi) - psq(uLo - Vtnhi))
    loP = kplo / 2 * (psq(vddlo - uLo - Vtphi) - psq(Vlo - uLo - Vtphi))
    return dict(up=up, dn=dn, hiP=hiP, hiN=hiN, loN=loN, loP=loP)


base = margins(VDDlo, VDDhi, Vhi)
RhiNp = knlo / 2 * (psq(uHi - Vtnhi) - psq(uHi - (VDDlo + (Vhi - VDDhi)) - Vtnhi))
print("(a) RhiN' =", float(RhiNp), " RhiN =", float(base["hiN"]), " equal:", RhiNp == base["hiN"])
worst = {k: None for k in base}
ok = True
for i in range(0, 361):
    V0 = VDDlo + Fr(i, 1000)
    m = margins(V0, V0, V0 + (Vhi - VDDhi))
    for k in m:
        ok &= m[k] > eps
        ok &= (m[k] >= base[k]) if k != "hiN" else (m[k] >= RhiNp)
        worst[k] = m[k] if worst[k] is None else min(worst[k], m[k])
print("    all six margins of atSupply(V0) exceed eps for 361 values of V0, and are >= those of the record"
      " (hiN: >= RhiN'):", ok)
print("    smallest value of each margin over V0:", {k: float(v) for k, v in worst.items()})
print("    deadlines of the restricted record at V0 = VDDlo:",
      "tauUp =", float(Chi * (VOH - Vlo) / (margins(VDDlo, VDDlo, VDDlo + Fr("0.10"))["up"] - eps)),
      "tauDn =", float(Chi * (VDDlo + Fr("0.10") - VOL) / (margins(VDDlo, VDDlo, VDDlo + Fr("0.10"))["dn"] - eps)))

# (b) true minimum inward current at v = VDD + 0.10 (float; corners x dense grid in u)
def fpsq(x):
    return np.maximum(x, 0.0) ** 2


def Inet(th, u, v):
    VDD, kn, kp, Vtn, Vtp = th
    return kp / 2 * (fpsq(VDD - u - Vtp) - fpsq(v - u - Vtp)) - kn / 2 * (fpsq(u - Vtn) - fpsq(u - v - Vtn))


us = np.linspace(-2.0, 4.0, 60001)
best = (np.inf, None, None)
for th in itertools.product((1.62, 1.98), (160.0, 240.0), (80.0, 120.0), (0.45, 0.60), (0.45, 0.60)):
    vals = -Inet(th, us, th[0] + 0.10)
    i = int(np.argmin(vals))
    if vals[i] < best[0]:
        best = (float(vals[i]), float(us[i]), th)
# VDD also takes interior values; scan it
for vdd in np.linspace(1.62, 1.98, 37):
    for kn, kp, vtn, vtp in itertools.product((160.0, 240.0), (80.0, 120.0), (0.45, 0.60), (0.45, 0.60)):
        vals = -Inet((vdd, kn, kp, vtn, vtp), us, vdd + 0.10)
        i = int(np.argmin(vals))
        if vals[i] < best[0]:
            best = (float(vals[i]), float(us[i]), (vdd, kn, kp, vtn, vtp))
print(f"(b) true minimum inward current at v = VDD + 0.10: {best[0]:.4f} uA at u = {best[1]:.4f}, theta = {best[2]}")
print("    (notes file: 'about 3.6 uA'; proved bound for the restricted record: RhiN' = 2.312, RhiP >= 2.4)")

# (c) slew numbers
ich = kphi / 2 * psq(VDDhi - 0 - Vtplo) + knhi / 2 * psq(Fr("0.40") - Vlo - Vtnlo)
idis = knhi / 2 * psq(Fr("1.98") - Vtnlo) + kphi / 2 * psq(Vhi - Fr("1.25") - Vtplo)
print("(c) (IchargeMax 0 0.40 + eps)/Clo =", float((ich + eps) / Clo), " == 28.5508:", (ich + eps) / Clo == Fr("28.5508"))
print("    (IdischargeMax 1.25 1.98 + eps)/Clo =", float((idis + eps) / Clo), " == 58.3144:", (idis + eps) / Clo == Fr("58.3144"))
fast = (1.98, 240.0, 120.0, 0.45, 0.45)
vs = np.linspace(-0.10, 2.08, 2181)
sup_rise = max(float(np.max(Inet(fast, u, vs))) for u in np.linspace(0.0, 0.40, 401))
sup_fall = max(float(np.max(-Inet(fast, u, vs))) for u in np.linspace(1.25, 1.98, 731))
print(f"    true supremum of the rising slew for u in [0, 0.40]: {(sup_rise + 2) / 5:.4f} V/ns (bound 28.5508)")
print(f"    true supremum of the falling slew for u in [1.25, 1.98]: {(sup_fall + 2) / 5:.4f} V/ns (bound 58.3144)")
print("    both bounds are for restricted input ranges; for u <= VIL or u >= VIH without range the slew is unbounded")

# (d) slowest rise with a state-dependent choice of the box point: at each v take the minimum of
# Inet over all corners (the extreme over the box is at a corner), u = VIL, w = -eps, C = Chi.
corners = list(itertools.product((1.62, 1.98), (160.0, 240.0), (80.0, 120.0), (0.45, 0.60), (0.45, 0.60)))
vgrid = np.linspace(-0.10, 1.35, 145001)
imin = np.min(np.array([Inet(c, 0.40, vgrid) for c in corners]), axis=0)
t_pi = float(np.trapezoid(20.0 / (imin - 2.0), vgrid))
print(f"(d) slowest rise from Vlo with a per-instant choice of the box point: {t_pi:.6f} ns "
      f"(fixed worst corner, Part 1: 2.251190 ns)")
