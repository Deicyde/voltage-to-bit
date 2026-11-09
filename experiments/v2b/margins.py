"""Task 2: closed-form margins (exact) and numerical tests of the four margin claims.

The dense grid tests are done in EXACT integer arithmetic: all grid coordinates,
design voltages and lattice parameters are integer multiples of a voltage unit
(0.1 mV), so  2 * Sk * Sv^2 * I  is an integer and numpy int64 evaluates it
without rounding (an overflow bound is asserted). A float evaluation of the
same grid is reported next to it to show the size of rounding noise, and a
seeded differential-evolution search looks for negative slack off the grid;
its best point is re-evaluated exactly.
"""
from __future__ import annotations

import math
from fractions import Fraction

import numpy as np
from scipy.optimize import differential_evolution

from . import laws
from .common import corner_array, float_design, lattice_thetas, rng_for, theta_floats
from .design import (
    THETA_KEYS,
    Design,
    I_dn,
    I_net,
    I_up,
    R_hiN,
    R_hiP,
    R_loN,
    R_loP,
    admissibility,
    closed_form,
    corners,
    dec,
    frac_record,
    is_admissible,
)

V_UNIT = Fraction(1, 10000)  # 0.1 mV


class IntModel:
    """Exact integer evaluation of the device law on a rational lattice."""

    def __init__(self, D: Design, v_unit: Fraction = V_UNIT):
        self.D = D
        self.Sv = Fraction(1) / v_unit
        if self.Sv.denominator != 1:
            raise ValueError("voltage unit must be 1/integer")
        self.Sv = int(self.Sv)
        ks = [D.lo("kn"), D.hi("kn"), D.lo("kp"), D.hi("kp")]
        self.Sk = math.lcm(*[Fraction(k).denominator for k in ks])
        self.Iscale = 2 * self.Sk * self.Sv**2  # I_int = I * Iscale
        if (D.eps * self.Iscale).denominator != 1:
            raise ValueError("eps is not representable on the integer current scale")

    def V(self, x) -> int:
        y = Fraction(x) * self.Sv
        if y.denominator != 1:
            raise ValueError(f"voltage {x} is not a multiple of the lattice unit")
        return int(y)

    def K(self, x) -> int:
        y = Fraction(x) * self.Sk
        if y.denominator != 1:
            raise ValueError(f"k {x} is not representable")
        return int(y)

    def theta(self, th) -> tuple:
        VDD, kn, kp, Vtn, Vtp = th
        return (self.V(VDD), self.K(kn), self.K(kp), self.V(Vtn), self.V(Vtp))

    def I(self, i_int) -> Fraction:
        return Fraction(int(i_int), self.Iscale)

    def check_no_overflow(self, vmax_abs_int: int) -> None:
        kmax = max(self.K(self.D.hi("kn")), self.K(self.D.hi("kp")), self.K(self.D.lo("kn")), self.K(self.D.lo("kp")))
        worst = 4 * kmax * (3 * vmax_abs_int) ** 2
        if worst >= 2**62:
            raise OverflowError("int64 would overflow on this grid; coarsen the lattice")

    @staticmethod
    def psq(x):
        m = np.maximum(x, 0)
        return m * m

    def inet(self, u, v, th_int):
        VDD, kn, kp, Vtn, Vtp = th_int
        return kp * (self.psq(VDD - u - Vtp) - self.psq(v - u - Vtp)) - kn * (self.psq(u - Vtn) - self.psq(u - v - Vtn))

    # closed-form bounds on the same integer scale -------------------------
    def iup(self, c):
        D = self.D
        return self.K(D.lo("kp")) * (
            self.psq(np.int64(self.V(D.lo("VDD") - D.VIL - D.hi("Vtp")))) - self.psq(c - self.V(D.VIL + D.hi("Vtp")))
        ) - self.K(D.hi("kn")) * self.psq(np.int64(self.V(D.VIL - D.lo("Vtn"))))

    def idn(self, c):
        D = self.D
        return self.K(D.lo("kn")) * (
            self.psq(np.int64(self.V(D.VIH - D.hi("Vtn")))) - self.psq(self.V(D.VIH - D.hi("Vtn")) - c)
        ) - self.K(D.hi("kp")) * self.psq(np.int64(self.V(D.hi("VDD") - D.VIH - D.lo("Vtp"))))

    def scal(self, x: Fraction) -> int:
        y = Fraction(x) * self.Iscale
        if y.denominator != 1:
            raise ValueError("current not representable")
        return int(y)


def _th_record(th) -> dict:
    return {k: dec(Fraction(x)) for k, x in zip(THETA_KEYS, th)}


def _theta_sets(D: Design, n_random: int, tag: str):
    cs = corners(D)
    sets = [("corner:" + c["code"], c["theta"]) for c in cs]
    if n_random > 0:
        sets += [(f"lattice:{i}", th) for i, th in enumerate(lattice_thetas(D, n_random, tag))]
    return sets


def test_up(D: Design, im: IntModel, cfg: dict) -> dict:
    """Claim: I_net(u, v; th) >= I_up(c) whenever u <= V_IL and v <= c <= VDD_min."""
    out = {"claim": "I_net(u,v;theta) >= I_up(c) for u <= V_IL, v <= c <= VDD_min"}
    res_sets = []
    for label, (hu, hv, thetas) in {
        "corners_dense": (cfg["h_dense"], cfg["h_dense"], [(n, t) for n, t in _theta_sets(D, 0, "none")]),
        "lattice_interior": (cfg["h_coarse"], cfg["h_coarse"], _theta_sets(D, cfg["n_random"], "margins/up/theta")[32:]),
    }.items():
        hu_i, hv_i = im.V(hu), im.V(hv)
        u = im.V(D.VIL) - hu_i * np.arange(0, int((D.VIL - cfg["u_far_lo"]) / hu) + 1, dtype=np.int64)
        nv = int((D.lo("VDD") - cfg["v_far_lo"]) / hv)
        v = im.V(D.lo("VDD")) - hv_i * np.arange(nv, -1, -1, dtype=np.int64)  # ascending, ends at VDD_min
        im.check_no_overflow(int(max(abs(u).max(), abs(v).max(), im.V(D.hi("VDD")))))
        iup = im.iup(v)
        best = None
        n_zero_total = 0
        n_neg = 0
        per_theta_min = []
        for name, th in thetas:
            thi = im.theta(th)
            A = im.inet(u[:, None], v[None, :], thi)
            m = A.min(axis=0)
            pm = np.minimum.accumulate(m)
            slack = pm - iup  # min over (u, v <= c) of slack at each c
            k = int(slack.argmin())
            s = int(slack[k])
            per_theta_min.append(s)
            n_neg += int(np.count_nonzero(slack < 0))
            n_zero_total += int(np.count_nonzero(A - iup[None, :] == 0))
            if best is None or s < best[0]:
                j = int(np.argmax(m[: k + 1] == pm[k]))
                i = int(A[:, j].argmin())
                best = (s, name, th, int(u[i]), int(v[j]), int(v[k]))
        s, name, th, ui, vi, ci = best
        uF, vF, cF = Fraction(ui, im.Sv), Fraction(vi, im.Sv), Fraction(ci, im.Sv)
        exact = I_net(uF, vF, tuple(Fraction(x) for x in th)) - I_up(D, cF)
        assert exact == im.I(s), "integer-lattice evaluation disagrees with Fraction evaluation"
        res_sets.append(
            {
                "set": label,
                "n_theta": len(thetas),
                "grid": {"u": [dec(Fraction(int(u.min()), im.Sv)), dec(Fraction(int(u.max()), im.Sv)), dec(Fraction(hu))], "v_and_c": [dec(Fraction(int(v.min()), im.Sv)), dec(Fraction(int(v.max()), im.Sv)), dec(Fraction(hv))], "n_u": int(u.size), "n_v": int(v.size)},
                "n_triples_covered": int(len(thetas) * u.size * v.size * (v.size + 1) // 2),
                "arithmetic": "exact int64 on the 0.1 mV lattice",
                "min_slack_uA": frac_record(im.I(s)),
                "argmin": {"theta_set": name, "theta": _th_record(th), "u": dec(uF), "v": dec(vF), "c": dec(cF)},
                "n_c_values_with_negative_min_slack": n_neg,
                "n_grid_points_with_zero_slack_at_c_eq_v": n_zero_total,
                "n_theta_with_zero_min_slack": int(sum(1 for x in per_theta_min if x == 0)),
            }
        )
    out["exact_grid"] = res_sets
    return out


def test_dn(D: Design, im: IntModel, cfg: dict) -> dict:
    """Claim: I_net(u, v; th) <= -I_dn(c) whenever u >= V_IH and v >= c >= 0."""
    out = {"claim": "I_net(u,v;theta) <= -I_dn(c) for u >= V_IH, v >= c >= 0"}
    res_sets = []
    for label, (h, thetas) in {
        "corners_dense": (cfg["h_dense"], _theta_sets(D, 0, "none")),
        "lattice_interior": (cfg["h_coarse"], _theta_sets(D, cfg["n_random"], "margins/dn/theta")[32:]),
    }.items():
        hi_ = im.V(h)
        u = im.V(D.VIH) + hi_ * np.arange(0, int((cfg["u_far_hi"] - D.VIH) / h) + 1, dtype=np.int64)
        v = hi_ * np.arange(0, int(Fraction(cfg["v_far_hi"]) / h) + 1, dtype=np.int64)  # ascending from 0
        im.check_no_overflow(int(max(abs(u).max(), abs(v).max(), im.V(D.hi("VDD")))))
        idn = im.idn(v)
        best = None
        n_neg = 0
        n_zero_total = 0
        per_theta_min = []
        for name, th in thetas:
            thi = im.theta(th)
            A = -im.inet(u[:, None], v[None, :], thi)  # pull-down current
            m = A.min(axis=0)
            sm = np.minimum.accumulate(m[::-1])[::-1]  # min over v >= c
            slack = sm - idn
            k = int(slack.argmin())
            s = int(slack[k])
            per_theta_min.append(s)
            n_neg += int(np.count_nonzero(slack < 0))
            n_zero_total += int(np.count_nonzero(A - idn[None, :] == 0))
            if best is None or s < best[0]:
                j = k + int(np.argmax(m[k:] == sm[k]))
                i = int(A[:, j].argmin())
                best = (s, name, th, int(u[i]), int(v[j]), int(v[k]))
        s, name, th, ui, vi, ci = best
        uF, vF, cF = Fraction(ui, im.Sv), Fraction(vi, im.Sv), Fraction(ci, im.Sv)
        exact = -I_dn(D, cF) - I_net(uF, vF, tuple(Fraction(x) for x in th))
        assert exact == im.I(s)
        res_sets.append(
            {
                "set": label,
                "n_theta": len(thetas),
                "grid": {"u": [dec(Fraction(int(u.min()), im.Sv)), dec(Fraction(int(u.max()), im.Sv)), dec(Fraction(h))], "v_and_c": [dec(Fraction(int(v.min()), im.Sv)), dec(Fraction(int(v.max()), im.Sv)), dec(Fraction(h))], "n_u": int(u.size), "n_v": int(v.size)},
                "n_triples_covered": int(len(thetas) * u.size * v.size * (v.size + 1) // 2),
                "arithmetic": "exact int64 on the 0.1 mV lattice",
                "min_slack_uA": frac_record(im.I(s)),
                "argmin": {"theta_set": name, "theta": _th_record(th), "u": dec(uF), "v": dec(vF), "c": dec(cF)},
                "n_c_values_with_negative_min_slack": n_neg,
                "n_grid_points_with_zero_slack_at_c_eq_v": n_zero_total,
                "n_theta_with_zero_min_slack": int(sum(1 for x in per_theta_min if x == 0)),
            }
        )
    out["exact_grid"] = res_sets
    return out


def test_barriers(D: Design, im: IntModel, cfg: dict) -> dict:
    """Claims: for EVERY real u, I_net(u, V_hi) <= -min(R_hiP, R_hiN) and I_net(u, V_lo) >= min(R_loN, R_loP)."""
    h = cfg["h_barrier"]
    u = im.V(cfg["u_far_lo"]) + im.V(h) * np.arange(0, int((cfg["u_far_hi"] - cfg["u_far_lo"]) / h) + 1, dtype=np.int64)
    im.check_no_overflow(int(max(abs(u).max(), im.V(D.Vhi))))
    Rhi = min(R_hiP(D), R_hiN(D))
    Rlo = min(R_loN(D), R_loP(D))
    thetas = _theta_sets(D, cfg["n_random_barrier"], "margins/barrier/theta")
    res = {}
    for side in ("hi", "lo"):
        best = None
        n_neg = 0
        for name, th in thetas:
            thi = im.theta(th)
            if side == "hi":
                inward = -im.inet(u, np.int64(im.V(D.Vhi)), thi)
                slack = inward - im.scal(Rhi)
            else:
                inward = im.inet(u, np.int64(im.V(D.Vlo)), thi)
                slack = inward - im.scal(Rlo)
            k = int(slack.argmin())
            n_neg += int(np.count_nonzero(slack < 0))
            if best is None or int(slack[k]) < best[0]:
                best = (int(slack[k]), name, th, int(u[k]), int(inward[k]))
        s, name, th, ui, inw = best
        res[side] = {
            "claim": (
                "for every real u: I_net(u, V_hi) <= -min(R_hiP, R_hiN)" if side == "hi" else "for every real u: I_net(u, V_lo) >= min(R_loN, R_loP)"
            ),
            "claimed_bound_uA": frac_record(Rhi if side == "hi" else Rlo),
            "n_theta": len(thetas),
            "grid_u": [dec(Fraction(int(u.min()), im.Sv)), dec(Fraction(int(u.max()), im.Sv)), dec(Fraction(h))],
            "n_points": int(len(thetas) * u.size),
            "arithmetic": "exact int64 on the 0.1 mV lattice",
            "min_slack_uA": frac_record(im.I(s)),
            "min_inward_current_uA": frac_record(im.I(inw)),
            "argmin": {"theta_set": name, "theta": _th_record(th), "u": dec(Fraction(ui, im.Sv))},
            "n_points_with_negative_slack": n_neg,
        }
    return res


def float_noise(D: Design, cfg: dict) -> dict:
    """Same binding diagonal (c = v, u = V_IL / V_IH) in float64: size of rounding noise at the tight points."""
    F = float_design(D)
    codes, C = corner_array(D)
    v = np.linspace(float(cfg["v_far_lo"]), F.VDD_lo, 20001)
    v2 = np.linspace(0.0, float(cfg["v_far_hi"]), 20001)
    iup = 0.5 * F.kp_lo * (laws.psq(F.VDD_lo - F.VIL - F.Vtp_hi) - laws.psq(v - F.VIL - F.Vtp_hi)) - 0.5 * F.kn_hi * laws.psq(F.VIL - F.Vtn_lo)
    idn = 0.5 * F.kn_lo * (laws.psq(F.VIH - F.Vtn_hi) - laws.psq(F.VIH - v2 - F.Vtn_hi)) - 0.5 * F.kp_hi * laws.psq(F.VDD_hi - F.VIH - F.Vtp_lo)
    mins_up, mins_dn = [], []
    for th in C:
        mins_up.append(float((laws.inet_formal(F.VIL, v, *th) - iup).min()))
        mins_dn.append(float((-laws.inet_formal(F.VIH, v2, *th) - idn).min()))
    return {
        "note": "float64 evaluation on the binding set (u at the band edge, c = v); negative values here are rounding noise iff the exact grid minimum is >= 0",
        "min_float_slack_up_uA": min(mins_up),
        "min_float_slack_dn_uA": min(mins_dn),
    }


def _clampF(x: float, lo: Fraction, hi: Fraction) -> Fraction:
    return min(max(Fraction(float(x)), Fraction(lo)), Fraction(hi))


def de_search(D: Design, cfg: dict) -> dict:
    """Seeded global search (float64) for negative slack off the grid; best point re-evaluated exactly."""
    F = float_design(D)
    box = [(F.lo(k), F.hi(k)) for k in THETA_KEYS]
    out = {}

    def run(tag, fun, bounds):
        seed = int(rng_for(tag).integers(0, 2**31 - 1))
        r = differential_evolution(fun, bounds, seed=seed, popsize=cfg["de_popsize"], maxiter=cfg["de_maxiter"], tol=0.0, atol=0.0, polish=True, init="sobol", updating="immediate", workers=1)
        return r, seed

    u_lo, u_hi = float(cfg["u_far_lo"]), float(cfg["u_far_hi"])
    v_lo, v_hi = float(cfg["v_far_lo"]), float(cfg["v_far_hi"])

    def iup_f(c):
        return 0.5 * F.kp_lo * (laws.psq(F.VDD_lo - F.VIL - F.Vtp_hi) - laws.psq(c - F.VIL - F.Vtp_hi)) - 0.5 * F.kn_hi * laws.psq(F.VIL - F.Vtn_lo)

    def idn_f(c):
        return 0.5 * F.kn_lo * (laws.psq(F.VIH - F.Vtn_hi) - laws.psq(F.VIH - c - F.Vtn_hi)) - 0.5 * F.kp_hi * laws.psq(F.VDD_hi - F.VIH - F.Vtp_lo)

    # UP: x = (u, v, t, theta) with c = v + t (VDD_min - v)
    def f_up(x):
        u, v, t = x[0], x[1], x[2]
        c = v + t * (F.VDD_lo - v)
        return float(laws.inet_formal(u, v, *x[3:]) - iup_f(c))

    r, seed = run("margins/de/up", f_up, [(u_lo, F.VIL), (v_lo, F.VDD_lo), (0.0, 1.0)] + box)
    u = _clampF(r.x[0], cfg["u_far_lo"], D.VIL)
    v = _clampF(r.x[1], cfg["v_far_lo"], D.lo("VDD"))
    t = _clampF(r.x[2], 0, 1)
    c = v + t * (D.lo("VDD") - v)
    th = tuple(_clampF(x, D.lo(k), D.hi(k)) for x, k in zip(r.x[3:], THETA_KEYS))
    ex = I_net(u, v, th) - I_up(D, c)
    out["up"] = {"seed": seed, "min_float_slack_uA": float(r.fun), "nfev": int(r.nfev), "argmin_float": [float(z) for z in r.x], "exact_slack_at_argmin_uA": float(ex), "exact_slack_sign": int(ex > 0) - int(ex < 0)}

    # DN: x = (u, v, t, theta) with c = t * v
    def f_dn(x):
        u, v, t = x[0], x[1], x[2]
        return float(-idn_f(t * v) - laws.inet_formal(u, v, *x[3:]))

    r, seed = run("margins/de/dn", f_dn, [(F.VIH, u_hi), (0.0, v_hi), (0.0, 1.0)] + box)
    u = _clampF(r.x[0], D.VIH, cfg["u_far_hi"])
    v = _clampF(r.x[1], 0, cfg["v_far_hi"])
    t = _clampF(r.x[2], 0, 1)
    th = tuple(_clampF(x, D.lo(k), D.hi(k)) for x, k in zip(r.x[3:], THETA_KEYS))
    ex = -I_dn(D, t * v) - I_net(u, v, th)
    out["dn"] = {"seed": seed, "min_float_slack_uA": float(r.fun), "nfev": int(r.nfev), "argmin_float": [float(z) for z in r.x], "exact_slack_at_argmin_uA": float(ex), "exact_slack_sign": int(ex > 0) - int(ex < 0)}

    Rhi = float(min(R_hiP(D), R_hiN(D)))
    Rlo = float(min(R_loN(D), R_loP(D)))

    def f_hi(x):
        return float(-Rhi - laws.inet_formal(x[0], F.Vhi, *x[1:]))

    def f_lo(x):
        return float(laws.inet_formal(x[0], F.Vlo, *x[1:]) - Rlo)

    for side, fun in (("hi", f_hi), ("lo", f_lo)):
        r, seed = run(f"margins/de/barrier_{side}", fun, [(u_lo, u_hi)] + box)
        u = _clampF(r.x[0], cfg["u_far_lo"], cfg["u_far_hi"])
        th = tuple(_clampF(x, D.lo(k), D.hi(k)) for x, k in zip(r.x[1:], THETA_KEYS))
        if side == "hi":
            ex = -min(R_hiP(D), R_hiN(D)) - I_net(u, D.Vhi, th)
        else:
            ex = I_net(u, D.Vlo, th) - min(R_loN(D), R_loP(D))
        out[f"barrier_{side}"] = {"seed": seed, "min_float_slack_uA": float(r.fun), "nfev": int(r.nfev), "argmin_float": [float(z) for z in r.x], "exact_slack_at_argmin_uA": float(ex), "exact_slack_sign": int(ex > 0) - int(ex < 0)}
    return out


def hypothesis_probes(D: Design, im: IntModel, cfg: dict) -> dict:
    """OUTSIDE the claims: is `c <= VDD_min` (up) / `c >= 0` (down) actually needed?

    A negative slack here is NOT a counterexample to the claim; it shows that the
    side condition cannot be dropped.
    """
    h = cfg["h_coarse"]
    hi_ = im.V(h)
    out = {}
    # UP with c in (VDD_min, VDD_min + 0.5], v <= c
    u = im.V(D.VIL) - hi_ * np.arange(0, int((D.VIL - cfg["u_far_lo"]) / h) + 1, dtype=np.int64)
    c = im.V(D.lo("VDD")) + hi_ * np.arange(1, int(Fraction(1, 2) / h) + 1, dtype=np.int64)
    best = None
    for cdict in corners(D):
        thi = im.theta(cdict["theta"])
        A = im.inet(u[:, None], c[None, :], thi) - im.iup(c)[None, :]  # v = c
        k = np.unravel_index(int(A.argmin()), A.shape)
        if best is None or int(A[k]) < best[0]:
            best = (int(A[k]), cdict["code"], int(u[k[0]]), int(c[k[1]]))
    out["up_with_c_above_VDD_min"] = {
        "status": "OUTSIDE THE CLAIM (hypothesis-necessity probe)",
        "min_slack_uA": frac_record(im.I(best[0])),
        "corner": best[1],
        "u": dec(Fraction(best[2], im.Sv)),
        "v_eq_c": dec(Fraction(best[3], im.Sv)),
        "conclusion": "negative => the side condition c <= VDD_min is necessary" if best[0] < 0 else "no negative slack found on this probe grid",
    }
    # DN with c in [-0.5, 0), v >= c (take v = c)
    u = im.V(D.VIH) + hi_ * np.arange(0, int((cfg["u_far_hi"] - D.VIH) / h) + 1, dtype=np.int64)
    c = -hi_ * np.arange(1, int(Fraction(1, 2) / h) + 1, dtype=np.int64)
    best = None
    for cdict in corners(D):
        thi = im.theta(cdict["theta"])
        A = -im.inet(u[:, None], c[None, :], thi) - im.idn(c)[None, :]
        k = np.unravel_index(int(A.argmin()), A.shape)
        if best is None or int(A[k]) < best[0]:
            best = (int(A[k]), cdict["code"], int(u[k[0]]), int(c[k[1]]))
    out["dn_with_c_below_0"] = {
        "status": "OUTSIDE THE CLAIM (hypothesis-necessity probe)",
        "min_slack_uA": frac_record(im.I(best[0])),
        "corner": best[1],
        "u": dec(Fraction(best[2], im.Sv)),
        "v_eq_c": dec(Fraction(best[3], im.Sv)),
        "conclusion": "negative => the side condition c >= 0 is necessary" if best[0] < 0 else "no negative slack found on this probe grid",
    }
    return out


def true_margins(D: Design, im: IntModel, cfg: dict) -> dict:
    """How conservative are the closed-form margins? Exact minima of the model over
    corners and the grid (corners suffice pointwise: I_net is monotone in each parameter)."""
    h = cfg["h_dense"]
    hi_ = im.V(h)
    out = {}
    cs = corners(D)
    # rise: min over u <= V_IL, v in [V_lo, V_OH]
    u = im.V(D.VIL) - hi_ * np.arange(0, int((D.VIL - cfg["u_far_lo"]) / h) + 1, dtype=np.int64)
    v = im.V(D.Vlo) + hi_ * np.arange(0, int((D.VOH - D.Vlo) / h) + 1, dtype=np.int64)
    best = None
    for c in cs:
        A = im.inet(u[:, None], v[None, :], im.theta(c["theta"]))
        k = np.unravel_index(int(A.argmin()), A.shape)
        if best is None or int(A[k]) < best[0]:
            best = (int(A[k]), c["code"], int(u[k[0]]), int(v[k[1]]))
    out["rise_min_pullup_uA"] = {
        "domain": "u <= V_IL, v in [V_lo, V_OH], 32 corners",
        "value": frac_record(im.I(best[0])),
        "corner": best[1],
        "u": dec(Fraction(best[2], im.Sv)),
        "v": dec(Fraction(best[3], im.Sv)),
        "closed_form_I_up(V_OH)": frac_record(I_up(D, D.VOH)),
        "closed_form_is_attained": im.I(best[0]) == I_up(D, D.VOH),
    }
    u = im.V(D.VIH) + hi_ * np.arange(0, int((cfg["u_far_hi"] - D.VIH) / h) + 1, dtype=np.int64)
    v = im.V(D.VOL) + hi_ * np.arange(0, int((D.Vhi - D.VOL) / h) + 1, dtype=np.int64)
    best = None
    for c in cs:
        A = -im.inet(u[:, None], v[None, :], im.theta(c["theta"]))
        k = np.unravel_index(int(A.argmin()), A.shape)
        if best is None or int(A[k]) < best[0]:
            best = (int(A[k]), c["code"], int(u[k[0]]), int(v[k[1]]))
    out["fall_min_pulldown_uA"] = {
        "domain": "u >= V_IH, v in [V_OL, V_hi], 32 corners",
        "value": frac_record(im.I(best[0])),
        "corner": best[1],
        "u": dec(Fraction(best[2], im.Sv)),
        "v": dec(Fraction(best[3], im.Sv)),
        "closed_form_I_dn(V_OL)": frac_record(I_dn(D, D.VOL)),
        "closed_form_is_attained": im.I(best[0]) == I_dn(D, D.VOL),
    }
    return out


def barrier_refinement(D: Design, im: IntModel, cfg: dict) -> dict:
    """PROPOSAL (not part of the claims under test): how much disturbance could a finer barrier
    certificate accept?

    At v = V_hi write the restoring current as P(u) + N(u) with P = -I_p >= 0 (PMOS reverse
    conduction) and N = I_n >= 0; at v = V_lo with P = I_p >= 0 and N = -I_n >= 0. Define
        P_hi(a) = (kp_min/2) (psq(V_hi - a - Vtp_max) - psq(VDD_max - a - Vtp_max))
        N_hi(a) = (kn_min/2) (psq(a - Vtn_max) - psq(a - V_hi - Vtn_max))            (= R_hiN at a = uHi)
        P_lo(a) = (kp_min/2) (psq(VDD_min - a - Vtp_max) - psq(V_lo - a - Vtp_max))  (= R_loP at a = uLo)
        N_lo(a) = (kn_min/2) (psq(a - V_lo - Vtn_max) - psq(a - Vtn_max))            (= R_loN at a = uLo)
    Two lemmas, CHECKED HERE ONLY ON AN EXACT GRID (32 corners), are needed:
        (L1) P(u'; theta) >= P_x(a) for every u' <= a;   (L2) N(u'; theta) >= N_x(a) for every u' >= a.
    Then for breakpoints a_1 < ... < a_K the restoring current at the boundary is at least
        min( P_x(a_1),  min_j [P_x(a_{j+1}) + N_x(a_j)],  N_x(a_K) )   for every real u.
    K = 1 is the present two-sided split (with a sharper P_hi than R_hiP).
    """
    D_ = D
    Vhi, Vlo = D.Vhi, D.Vlo
    kp, kn, Vtp, Vtn = D.lo("kp"), D.lo("kn"), D.hi("Vtp"), D.hi("Vtn")

    def P_hi(a):
        return kp / 2 * (psq_exact(Vhi - a - Vtp) - psq_exact(D.hi("VDD") - a - Vtp))

    def N_hi(a):
        return kn / 2 * (psq_exact(a - Vtn) - psq_exact(a - Vhi - Vtn))

    def P_lo(a):
        return kp / 2 * (psq_exact(D.lo("VDD") - a - Vtp) - psq_exact(Vlo - a - Vtp))

    def N_lo(a):
        return kn / 2 * (psq_exact(a - Vlo - Vtn) - psq_exact(a - Vtn))

    # exact-grid check of the two lemmas (pointwise bound + monotonicity in u, for every corner)
    h = cfg["h_barrier"]
    u = im.V(cfg["u_far_lo"]) + im.V(h) * np.arange(0, int((cfg["u_far_hi"] - cfg["u_far_lo"]) / h) + 1, dtype=np.int64)
    uF = [Fraction(int(x), im.Sv) for x in (u[0], u[-1])]
    lem = {}
    for side, v, Pb, Nb in (("hi", Vhi, P_hi, N_hi), ("lo", Vlo, P_lo, N_lo)):
        vi = np.int64(im.V(v))
        ok_p = ok_n = mono_p = mono_n = True
        pb = np.array([im.scal(Pb(Fraction(int(x), im.Sv))) for x in u[::20]], dtype=np.int64)
        nb = np.array([im.scal(Nb(Fraction(int(x), im.Sv))) for x in u[::20]], dtype=np.int64)
        for c in corners(D):
            VDD, kn_, kp_, Vtn_, Vtp_ = im.theta(c["theta"])
            ip = kp_ * (im.psq(VDD - u - Vtp_) - im.psq(vi - u - Vtp_))
            i_n = kn_ * (im.psq(u - Vtn_) - im.psq(u - vi - Vtn_))
            P = -ip if side == "hi" else ip
            N = i_n if side == "hi" else -i_n
            ok_p &= bool((P[::20] >= pb).all())
            ok_n &= bool((N[::20] >= nb).all())
            mono_p &= bool((np.diff(P) <= 0).all())
            mono_n &= bool((np.diff(N) >= 0).all())
        lem[side] = {"L1_pointwise_P_ge_bound": ok_p, "L1_P_nonincreasing_in_u": mono_p, "L2_pointwise_N_ge_bound": ok_n, "L2_N_nondecreasing_in_u": mono_n}

    def cert(Pb, Nb, pts):
        vals = [Pb(pts[0])] + [Pb(b) + Nb(a) for a, b in zip(pts[:-1], pts[1:])] + [Nb(pts[-1])]
        return min(vals)

    out = {"status": "PROPOSAL - numerically checked on a grid only; no proof", "lemma_checks_on_exact_grid": lem, "grid_u": [dec(uF[0]), dec(uF[1]), dec(Fraction(h))]}
    step = Fraction(1, 1000)
    cand = [Fraction(i, 1000) for i in range(0, 2001)]
    rows = []
    best_single = {}
    for side, Pb, Nb, cur in (("hi", P_hi, N_hi, D.uHi), ("lo", P_lo, N_lo, D.uLo)):
        single_now = cert(Pb, Nb, [cur])
        best = max(((cert(Pb, Nb, [a]), a) for a in cand), key=lambda t: t[0])
        best_single[side] = best
        rows.append([side, "present split point", 1, dec(cur), dec(single_now)])
        rows.append([side, "best single split point (1 mV grid)", 1, dec(best[1]), dec(best[0])])
        for K in (2, 4, 8, 16, 32, 64):
            # uniform breakpoints across the window where neither tail alone suffices
            a0, a1 = Fraction(3, 10), Fraction(13, 10)
            pts = [a0 + (a1 - a0) * Fraction(i, K - 1) for i in range(K)]
            rows.append([side, f"uniform on [{dec(a0)}, {dec(a1)}]", K, f"{dec(pts[0])} .. {dec(pts[-1])}", dec(cert(Pb, Nb, pts))])
    out["certified_restoring_current_uA"] = {"header": ["boundary", "breakpoints", "K", "points_V", "certified_minimum_restoring_current_uA"], "rows": rows}
    out["present_formulas"] = {"min(R_hiP, R_hiN)": dec(min(R_hiP(D), R_hiN(D))), "min(R_loN, R_loP)": dec(min(R_loN(D), R_loP(D))), "note": "R_hiP pairs VDD_min (overdrive) with VDD_max (excess voltage); P_hi above uses VDD_max in both places, which is the worst case because V_hi - u - V_tp does not depend on VDD"}
    out["sharper_R_hiP_at_present_uHi_uA"] = dec(P_hi(D.uHi))
    return out


def psq_exact(x):
    return x * x if x > 0 else x * 0


def margin_curves(D: Design, n: int = 401) -> dict:
    """Float curves for plotting (CSV twin of the margin figure)."""
    F = float_design(D)
    codes, C = corner_array(D)
    c_up = np.linspace(F.Vlo, F.VOH, n)
    c_dn = np.linspace(F.VOL, F.Vhi, n)
    iup = np.array([float(I_up(D, Fraction(float(x)))) for x in c_up])
    idn = np.array([float(I_dn(D, Fraction(float(x)))) for x in c_dn])
    min_up = np.min([laws.inet_formal(F.VIL, c_up, *th) for th in C], axis=0)
    min_dn = np.min([-laws.inet_formal(F.VIH, c_dn, *th) for th in C], axis=0)
    u = np.linspace(F.Vlo - 0.4, F.Vhi + 0.4, 2 * n - 1)
    in_hi = np.min([-laws.inet_formal(u, F.Vhi, *th) for th in C], axis=0)
    in_lo = np.min([laws.inet_formal(u, F.Vlo, *th) for th in C], axis=0)
    return {"c_up": c_up, "I_up": iup, "min_inet_up": min_up, "c_dn": c_dn, "I_dn": idn, "min_pulldown": min_dn, "u": u, "inward_hi": in_hi, "inward_lo": in_lo}


def run(D: Design, cfg: dict) -> dict:
    cf = closed_form(D)
    conds = admissibility(D)
    im = IntModel(D)
    res = {
        "closed_form": {k: frac_record(v) for k, v in cf.items()},
        "closed_form_units": {"I_up(V_OH)": "uA", "I_dn(V_OL)": "uA", "R_hiP": "uA", "R_hiN": "uA", "R_loN": "uA", "R_loP": "uA", "tau_up": "ns", "tau_dn": "ns"},
        "margin_minus_eps_uA": {k: frac_record(cf[k] - D.eps) for k in ("I_up(V_OH)", "I_dn(V_OL)", "R_hiP", "R_hiN", "R_loN", "R_loP")},
        "admissibility": {"admissible": is_admissible(D), "conditions": [c.as_dict() for c in conds]},
        "claim_up": test_up(D, im, cfg),
        "claim_dn": test_dn(D, im, cfg),
        "claim_barriers": test_barriers(D, im, cfg),
        "float_rounding_noise": float_noise(D, cfg),
        "de_search": de_search(D, cfg),
        "hypothesis_probes_outside_claims": hypothesis_probes(D, im, cfg),
        "true_margins": true_margins(D, im, cfg),
        "proposal_barrier_refinement": barrier_refinement(D, im, cfg),
    }
    return res
