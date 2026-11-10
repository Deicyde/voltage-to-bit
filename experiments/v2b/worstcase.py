"""Task 4: the model's true worst-case delays (quadrature), tightness of tau,
and multi-segment bounds with uniform and optimised breakpoints.

Rise (input low): worst case is u = V_IL, C = C_max, w = -eps, v(0) = V_lo and
    T(theta) = C_max * Integral_{V_lo}^{V_OH} dv / (I_net(V_IL, v; theta) - eps).
Fall (input high): u = V_IH, C = C_max, w = +eps, v(0) = V_hi and
    T(theta) = C_max * Integral_{V_OL}^{V_hi} dv / (-I_net(V_IH, v; theta) - eps).
That the band edge is the worst input and which parameter corner is worst are
CHECKED numerically here, not assumed.

Two notions of "worst case" are reported:
  constant theta : the ODE form with one parameter point per run (max over the box of T(theta));
  moving theta   : the trajectory notion of interface.md v1 (rev. 2), where the parameter point
                   may differ at every instant. Its worst case replaces the integrand by the
                   pointwise minimum of the drive over the box (attained at corners).
The second is never smaller than the first; they coincide iff one corner is pointwise worst.
"""
from __future__ import annotations

import math
from fractions import Fraction

import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize

from . import laws
from .common import corner_array, float_design, rng_for
from .design import THETA_KEYS, Design, I_dn, I_net, I_up, corner_by_code, corners, dec, frac_record, tau_dn, tau_up
from .sim import make_rhs, solve_ref


def _kinks(F, th, pol: str, u: float | None = None) -> list[float]:
    VDD, kn, kp, Vtn, Vtp = th
    if u is None:
        u = F.VIL if pol == "L" else F.VIH
    a, b = (F.Vlo, F.VOH) if pol == "L" else (F.VOL, F.Vhi)
    return sorted(x for x in (u + Vtp, u - Vtn, VDD) if a < x < b)


def drive(F, th, pol: str, v, eps: float, u: float | None = None):
    """Net current in the direction of the intended transition, minus eps
    (input at the valid-band edge unless ``u`` is given)."""
    if pol == "L":
        return laws.inet_formal(F.VIL if u is None else u, v, *th) - eps
    return -laws.inet_formal(F.VIH if u is None else u, v, *th) - eps


def delay_quad(F, th, pol: str, eps: float | None = None, C: float | None = None, u: float | None = None) -> float:
    eps = F.eps if eps is None else eps
    C = F.C_hi if C is None else C
    a, b = (F.Vlo, F.VOH) if pol == "L" else (F.VOL, F.Vhi)
    pts = [a] + _kinks(F, th, pol, u) + [b]
    # the drive is monotone in v, so its minimum over [a, b] is at an endpoint
    if min(float(drive(F, th, pol, a, eps, u)), float(drive(F, th, pol, b, eps, u))) <= 0.0:
        return math.inf
    tot = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        val, _err = quad(lambda v: 1.0 / float(drive(F, th, pol, v, eps, u)), lo, hi, epsabs=1e-14, epsrel=1e-13, limit=200)
        tot += val
    return C * tot


def box_drive(F, CT, pol: str, v: float, u: float | None = None) -> float:
    """Pointwise-worst drive over the box (min over the 32 corners), minus eps. ``CT`` = corners.T."""
    if pol == "L":
        return float(laws.inet_formal(F.VIL if u is None else u, v, *CT).min()) - F.eps
    return float((-laws.inet_formal(F.VIH if u is None else u, v, *CT)).min()) - F.eps


def envelope_delay(F, C_corners: np.ndarray, pol: str, u: float | None = None) -> float:
    """Worst-case delay of the rev. 2 inclusion (parameter point re-chosen adversarially at
    every instant): C_max * Integral dv / (min over the box of the drive - eps)."""
    a, b = (F.Vlo, F.VOH) if pol == "L" else (F.VOL, F.Vhi)
    CT = np.ascontiguousarray(C_corners.T)
    if min(box_drive(F, CT, pol, a, u), box_drive(F, CT, pol, b, u)) <= 0.0:
        return math.inf
    pts = sorted({a, b} | {x for th in C_corners for x in _kinks(F, th, pol, u)})
    tot = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        tot += quad(lambda v: 1.0 / box_drive(F, CT, pol, v, u), lo, hi, epsabs=1e-13, epsrel=1e-12, limit=200)[0]
    return F.C_hi * tot


def exact_bracket_box(D: Design, pol: str, n_per_piece: int) -> dict:
    """As ``exact_bracket`` but for the moving-theta worst case: the drive is the minimum over
    the 32 corners (still monotone in v, being a minimum of monotone functions)."""
    cs = [c["theta"] for c in corners(D)]
    Q = 10**24
    if pol == "L":
        a, b, u = D.Vlo, D.VOH, D.VIL
        g = lambda v: min(I_net(u, v, th) for th in cs) - D.eps  # noqa: E731
    else:
        a, b, u = D.VOL, D.Vhi, D.VIH
        g = lambda v: min(-I_net(u, v, th) for th in cs) - D.eps  # noqa: E731
    kink = set()
    for th in cs:
        kink |= {x for x in (u + th[4], u - th[3], th[0]) if a < x < b}
    pts = sorted({a, b} | kink)
    lo_sum = hi_sum = 0
    for p, q in zip(pts[:-1], pts[1:]):
        hstep = (q - p) / n_per_piece
        gprev = g(p)
        for i in range(n_per_piece):
            gnext = g(p + (i + 1) * hstep)
            gmax, gmin = max(gprev, gnext), min(gprev, gnext)
            if gmin <= 0:
                return {"error": "drive not positive on the whole range"}
            tl = D.hi("C") * hstep / gmax
            tu = D.hi("C") * hstep / gmin
            lo_sum += (tl.numerator * Q) // tl.denominator
            hi_sum += -((-tu.numerator * Q) // tu.denominator)
            gprev = gnext
    return {
        "n_segments": n_per_piece * (len(pts) - 1),
        "lower_ns": dec(Fraction(lo_sum, Q), 15),
        "upper_ns": dec(Fraction(hi_sum, Q), 15),
        "lower_float": lo_sum / Q,
        "upper_float": hi_sum / Q,
        "method": "exact rational lower/upper Riemann sums of C_max/(min over 32 corners of the drive - eps), outward-rounded at 1e-24 ns",
    }


def simulate_worst_box(D: Design, pol: str, t_end: float, dense_t=None, method="DOP853", rtol=1e-12, atol=1e-14) -> dict:
    """The slowest trajectory of the rev. 2 inclusion at the band-edge input (box_low for the rise, box_high for the fall)."""
    F = float_design(D)
    _codes, Cn = corner_array(D)
    kw = dict(eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, box=Cn)
    if pol == "L":
        rhs = make_rhs(laws.inet_formal, None, None, lambda t: F.VIL, fb=5, **kw)
        return solve_ref(rhs, F.Vlo, t_end, method=method, rtol=rtol, atol=atol, Vth=F.VOH, sgn=1, dense_t=dense_t)
    rhs = make_rhs(laws.inet_formal, None, None, lambda t: F.VIH, fb=6, **kw)
    return solve_ref(rhs, F.Vhi, t_end, method=method, rtol=rtol, atol=atol, Vth=F.VOL, sgn=-1, dense_t=dense_t)


def check_worst_input(D: Design, cfg: dict) -> dict:
    """Is the valid-band edge really the pointwise-worst input over the transition range?"""
    F = float_design(D)
    codes, Cn = corner_array(D)
    out = {}
    uL = np.linspace(float(cfg["u_far_lo"]), F.VIL, 1701)
    vL = np.linspace(F.Vlo, F.VOH, 581)
    uH = np.linspace(F.VIH, float(cfg["u_far_hi"]), 1501)
    vH = np.linspace(F.VOL, F.Vhi, 733)
    gapL = gapH = 0.0
    for th in Cn:
        A = laws.inet_formal(uL[:, None], vL[None, :], *th)
        gapL = max(gapL, float((A[-1, :] - A.min(axis=0)).max()))  # edge value minus min over u
        B = laws.inet_formal(uH[:, None], vH[None, :], *th)
        gapH = max(gapH, float((B.max(axis=0) - B[0, :]).max()))
    out["rise: max over (corner, v) of [I_net(V_IL, v) - min_{u<=V_IL} I_net(u, v)] (uA)"] = gapL
    out["fall: max over (corner, v) of [max_{u>=V_IH} I_net(u, v) - I_net(V_IH, v)] (uA)"] = gapH
    out["band_edge_is_pointwise_worst_input"] = bool(gapL <= 1e-12 and gapH <= 1e-12)
    out["grid"] = {"rise": [uL.size, vL.size], "fall": [uH.size, vH.size], "n_corners": len(codes)}
    # monotonicity in v (analytic derivative sign) on a wide grid
    uu = np.linspace(float(cfg["u_far_lo"]), float(cfg["u_far_hi"]), 801)
    vv = np.linspace(-1.0, 3.0, 801)
    mx = max(float(laws.dinet_dv_formal(uu[:, None], vv[None, :], *th).max()) for th in Cn)
    out["max d I_net / d v over wide grid and corners (uA/V)"] = mx
    out["I_net_nonincreasing_in_v"] = bool(mx <= 0.0)
    # the extremes of I_net(u, v; .) over the parameter box are attained at corners
    # (I_net is monotone in each parameter separately); box_low / box_high rely on this
    rng = rng_for("worst/corner-extremes")
    n = cfg["n_corner_extreme_samples"]
    us = rng.uniform(float(cfg["u_far_lo"]), float(cfg["u_far_hi"]), n)
    vs = rng.uniform(-1.0, 3.0, n)
    lo = np.array([F.lo(k) for k in THETA_KEYS])
    hi = np.array([F.hi(k) for k in THETA_KEYS])
    th = lo + rng.uniform(0.0, 1.0, (n, 5)) * (hi - lo)
    I = laws.inet_formal(us, vs, *th.T)
    cmin = np.full(n, np.inf)
    cmax = np.full(n, -np.inf)
    for c in Cn:
        Ic = laws.inet_formal(us, vs, *c)
        np.minimum(cmin, Ic, out=cmin)
        np.maximum(cmax, Ic, out=cmax)
    out["corner_extremes_check"] = {
        "n_random_points (u, v, theta)": n,
        "max of [min over corners - I_net(theta)] (uA)": float((cmin - I).max()),
        "max of [I_net(theta) - max over corners] (uA)": float((I - cmax).max()),
        "box_extremes_attained_at_corners": bool((cmin - I).max() <= 1e-9 and (I - cmax).max() <= 1e-9),
    }
    return out


def corner_delays(D: Design) -> dict:
    F = float_design(D)
    codes, Cn = corner_array(D)
    rows = []
    for code, th in zip(codes, Cn):
        rows.append([code, *[float(x) for x in th], delay_quad(F, th, "L"), delay_quad(F, th, "H")])
    return {"header": ["corner(VDD,kn,kp,Vtn,Vtp)", *THETA_KEYS, "T_rise_worstcase_ns", "T_fall_worstcase_ns"], "rows": rows}


def interior_max(D: Design, pol: str, cfg: dict) -> dict:
    """Search the whole box for a parameter with a larger worst-case delay than every corner."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    lo = np.array([F.lo(k) for k in THETA_KEYS])
    hi = np.array([F.hi(k) for k in THETA_KEYS])
    span = hi - lo

    def neg(x):
        return -delay_quad(F, lo + np.clip(x, 0, 1) * span, pol)

    rng = rng_for(f"worst/interior/{pol}")
    starts = [np.array([float(c == "H") for c in code]) for code in codes] + [rng.uniform(0, 1, 5) for _ in range(cfg["n_interior_starts"])]
    corner_vals = [delay_quad(F, th, pol) for th in Cn]
    best_corner = int(np.argmax(corner_vals))
    best = (corner_vals[best_corner], lo + starts[best_corner] * span)
    for x0 in starts[32:]:
        r = minimize(neg, x0, method="L-BFGS-B", bounds=[(0, 1)] * 5, options={"maxiter": 200, "ftol": 1e-15, "gtol": 1e-10})
        if -r.fun > best[0]:
            best = (-r.fun, lo + np.clip(r.x, 0, 1) * span)
    ties = [codes[i] for i, v in enumerate(corner_vals) if abs(v - corner_vals[best_corner]) <= 1e-12]
    return {
        "max_over_corners_ns": corner_vals[best_corner],
        "argmax_corner": codes[best_corner],
        "corners_within_1e-12_of_max": ties,
        "max_found_over_box_ns": best[0],
        "argmax_over_box": dict(zip(THETA_KEYS, [float(x) for x in best[1]])),
        "interior_exceeds_corner_by_ns": best[0] - corner_vals[best_corner],
        "n_random_starts": cfg["n_interior_starts"],
        "note": "local searches from seeded random interior points; finite evidence that the maximum is at a corner",
    }


def exact_bracket(D: Design, code: str, pol: str, n_per_piece: int) -> dict:
    """Rigorous bracket of the worst-corner delay from lower/upper Riemann sums in exact
    arithmetic (valid because I_net is non-increasing in v). Outward rounding at 1e-24."""
    th = corner_by_code(D, code)
    VDD, kn, kp, Vtn, Vtp = th
    Q = 10**24
    if pol == "L":
        a, b, u = D.Vlo, D.VOH, D.VIL
        g = lambda v: I_net(u, v, th) - D.eps  # noqa: E731  non-increasing in v
    else:
        a, b, u = D.VOL, D.Vhi, D.VIH
        g = lambda v: -I_net(u, v, th) - D.eps  # noqa: E731  non-decreasing in v
    pts = sorted({a, b} | {x for x in (u + Vtp, u - Vtn, VDD) if a < x < b})
    lo_sum = hi_sum = 0
    for p, q in zip(pts[:-1], pts[1:]):
        hstep = (q - p) / n_per_piece
        for i in range(n_per_piece):
            x0, x1 = p + i * hstep, p + (i + 1) * hstep
            g0, g1 = g(x0), g(x1)
            gmax, gmin = max(g0, g1), min(g0, g1)
            if gmin <= 0:
                return {"corner": code, "error": "drive not positive on the whole range"}
            tl = D.hi("C") * hstep / gmax
            tu = D.hi("C") * hstep / gmin
            lo_sum += (tl.numerator * Q) // tl.denominator  # floor
            hi_sum += -((-tu.numerator * Q) // tu.denominator)  # ceil
    return {
        "corner": code,
        "theta": {k: dec(x) for k, x in zip(THETA_KEYS, th)},
        "n_segments": n_per_piece * (len(pts) - 1),
        "lower_ns": dec(Fraction(lo_sum, Q), 15),
        "upper_ns": dec(Fraction(hi_sum, Q), 15),
        "lower_float": lo_sum / Q,
        "upper_float": hi_sum / Q,
        "method": "exact rational lower/upper Riemann sums of C_max/(drive - eps), outward-rounded at 1e-24 ns",
    }


def simulate_worst(D: Design, code: str, pol: str, t_end: float, dense_n: int = 0, method="DOP853", rtol=1e-12, atol=1e-14) -> dict:
    F = float_design(D)
    th = [float(x) for x in corner_by_code(D, code)]
    if pol == "L":
        rhs = make_rhs(laws.inet_formal, th, F.C_hi, lambda t: F.VIL, lambda t: -F.eps)
        return solve_ref(rhs, F.Vlo, t_end, method=method, rtol=rtol, atol=atol, Vth=F.VOH, sgn=1, dense_t=np.linspace(0, t_end, dense_n) if dense_n else None)
    rhs = make_rhs(laws.inet_formal, th, F.C_hi, lambda t: F.VIH, lambda t: F.eps)
    return solve_ref(rhs, F.Vhi, t_end, method=method, rtol=rtol, atol=atol, Vth=F.VOL, sgn=-1, dense_t=np.linspace(0, t_end, dense_n) if dense_n else None)


# --------------------------------------------------------------------------
# Multi-segment bounds
# --------------------------------------------------------------------------

def multiseg_bound(D: Design, pol: str, cs: list[Fraction]) -> Fraction:
    """Sum_i C_max |c_i - c_{i-1}| / (I(c_i) - eps); I = I_up (rise, ascending V_lo..V_OH)
    or I_dn (fall, descending V_hi..V_OL). Raises if the list is not a valid certificate."""
    if pol == "L":
        if not (cs[0] == D.Vlo and cs[-1] == D.VOH and all(x < y for x, y in zip(cs[:-1], cs[1:]))):
            raise ValueError("rise breakpoints must ascend strictly from V_lo to V_OH")
        if cs[-1] > D.lo("VDD"):
            raise ValueError("c_N must not exceed VDD_min")
        I = lambda c: I_up(D, c)  # noqa: E731
    else:
        if not (cs[0] == D.Vhi and cs[-1] == D.VOL and all(x > y for x, y in zip(cs[:-1], cs[1:]))):
            raise ValueError("fall breakpoints must descend strictly from V_hi to V_OL")
        if cs[-1] < 0:
            raise ValueError("c_N must not be negative")
        I = lambda c: I_dn(D, c)  # noqa: E731
    tot = Fraction(0)
    for c0, c1 in zip(cs[:-1], cs[1:]):
        m = I(c1) - D.eps
        if m <= 0:
            raise ValueError(f"margin not positive at c = {dec(c1)}")
        tot += D.hi("C") * abs(c1 - c0) / m
    return tot


def uniform_breakpoints(D: Design, pol: str, N: int) -> list[Fraction]:
    a, b = (D.Vlo, D.VOH) if pol == "L" else (D.Vhi, D.VOL)
    return [a + (b - a) * Fraction(i, N) for i in range(N + 1)]


def _bound_float(D: Design, pol: str, cs_f: np.ndarray) -> float:
    F = float_design(D)
    c1 = cs_f[1:]
    if pol == "L":
        I = 0.5 * F.kp_lo * (laws.psq(F.VDD_lo - F.VIL - F.Vtp_hi) - laws.psq(c1 - F.VIL - F.Vtp_hi)) - 0.5 * F.kn_hi * laws.psq(F.VIL - F.Vtn_lo)
    else:
        I = 0.5 * F.kn_lo * (laws.psq(F.VIH - F.Vtn_hi) - laws.psq(F.VIH - c1 - F.Vtn_hi)) - 0.5 * F.kp_hi * laws.psq(F.VDD_hi - F.VIH - F.Vtp_lo)
    return float(F.C_hi * np.sum(np.abs(np.diff(cs_f)) / (I - F.eps)))


def dp_breakpoints(D: Design, pol: str, Ns: list[int], grid: Fraction) -> dict:
    """Globally optimal N-segment breakpoints restricted to a decimal grid (dynamic programme)."""
    a, b = (D.Vlo, D.VOH) if pol == "L" else (D.Vhi, D.VOL)
    M = abs(b - a) / grid
    if M.denominator != 1:
        raise ValueError("the transition range is not a multiple of the breakpoint grid")
    M = int(M)
    sign = 1 if pol == "L" else -1
    pos = [a + sign * grid * j for j in range(M + 1)]
    x = np.array([float(abs(p - a)) for p in pos])
    If = np.array([float((I_up if pol == "L" else I_dn)(D, p) - D.eps) for p in pos])
    f = 1.0 / If
    Cmax = float(D.hi("C"))
    out = {}
    nmax = max(Ns)
    prev = Cmax * x * f  # 1 segment from index 0 to j
    prev[0] = 0.0
    back = []
    mask = np.triu(np.ones((M + 1, M + 1), dtype=bool), k=1)  # i < j allowed
    best_by_n = {1: prev.copy()}
    for n in range(2, nmax + 1):
        cand = prev[:, None] - Cmax * x[:, None] * f[None, :]
        cand = np.where(mask, cand, np.inf)
        cand[: n - 1, :] = np.inf  # need at least n-1 earlier breakpoints
        arg = cand.argmin(axis=0)
        cur = cand[arg, np.arange(M + 1)] + Cmax * x * f
        back.append(arg)
        best_by_n[n] = cur.copy()
        prev = cur
    for N in Ns:
        idx = [M]
        j = M
        for n in range(N, 1, -1):
            j = int(back[n - 2][j])
            idx.append(j)
        idx.append(0)
        idx = idx[::-1]
        cs = [pos[i] for i in idx]
        exact = multiseg_bound(D, pol, cs)
        out[N] = {"breakpoints": cs, "bound": exact, "dp_value_float": float(best_by_n[N][M])}
    return out


def polish_continuous(D: Design, pol: str, cs: list[Fraction]) -> float:
    """Continuous (off-grid) local optimum of the same bound, to show how little the 1 mV grid costs."""
    x0 = np.array([float(c) for c in cs[1:-1]])
    a, b = float(cs[0]), float(cs[-1])
    if x0.size == 0:
        return _bound_float(D, pol, np.array([a, b]))

    def obj(x):
        full = np.concatenate([[a], x, [b]])
        d = np.diff(full) * (1 if pol == "L" else -1)
        if np.any(d <= 0):
            return 1e9
        return _bound_float(D, pol, full)

    r = minimize(obj, x0, method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-14, "maxiter": 20000, "maxfev": 40000})
    return float(min(r.fun, obj(x0)))


def limit_integral(D: Design, pol: str) -> float:
    """N -> infinity limit of the multi-segment bound: C_max * Integral dc / (I(c) - eps)."""
    F = float_design(D)
    if pol == "L":
        a, b = F.Vlo, F.VOH
        kink = [x for x in (F.VIL + F.Vtp_hi,) if a < x < b]
        fun = lambda c: 1.0 / (float(I_up(D, Fraction(c))) - F.eps)  # noqa: E731
    else:
        a, b = F.VOL, F.Vhi
        kink = [x for x in (F.VIH - F.Vtn_hi,) if a < x < b]
        fun = lambda c: 1.0 / (float(I_dn(D, Fraction(c))) - F.eps)  # noqa: E731
    pts = [a] + kink + [b]
    return F.C_hi * sum(quad(fun, lo, hi, epsabs=1e-14, epsrel=1e-13, limit=200)[0] for lo, hi in zip(pts[:-1], pts[1:]))


def run(D: Design, cfg: dict) -> dict:
    F = float_design(D)
    codes, Cn = corner_array(D)
    res = {"worst_input_check": check_worst_input(D, cfg), "corner_delays": corner_delays(D)}
    taus = {"L": tau_up(D), "H": tau_dn(D)}
    for pol, name in (("L", "rise"), ("H", "fall")):
        im = interior_max(D, pol, cfg)
        code = im["argmax_corner"]
        T_const = im["max_over_corners_ns"]
        sim = simulate_worst(D, code, pol, t_end=1.2 * float(taus[pol]))
        br = exact_bracket(D, code, pol, cfg["n_bracket"])
        env = envelope_delay(F, Cn, pol)
        sim_box = simulate_worst_box(D, pol, t_end=1.2 * float(taus[pol]))
        br_box = exact_bracket_box(D, pol, cfg["n_bracket"])
        T_true = env  # the worst case of the trajectory notion in force (interface.md v1 rev. 2)
        lim = limit_integral(D, pol)
        table = []
        uni = {}
        for N in cfg["uniform_Ns"]:
            cs = uniform_breakpoints(D, pol, N)
            if N <= 64:
                val = multiseg_bound(D, pol, cs)
                uni[N] = float(val)
                if N in (1, 2, 4, 8):
                    res.setdefault("uniform_exact", {}).setdefault(name, {})[str(N)] = frac_record(val)
            else:
                uni[N] = _bound_float(D, pol, np.array([float(c) for c in cs]))
        dp = dp_breakpoints(D, pol, cfg["optimized_Ns"], Fraction(cfg["breakpoint_grid"]))
        opt = {}
        for N, rec in dp.items():
            cont = polish_continuous(D, pol, rec["breakpoints"]) if N <= 16 else None
            opt[N] = {
                "breakpoints_V": [dec(c) for c in rec["breakpoints"]],
                "bound_ns": frac_record(rec["bound"]),
                "ratio_to_true_worst_case": float(rec["bound"]) / T_true,
                "ratio_to_tau": float(rec["bound"] / taus[pol]),
                "continuous_local_optimum_ns": cont,
                "grid_cost_vs_continuous_ns": None if cont is None else float(rec["bound"]) - cont,
                "segments": [
                    {"from": dec(c0), "to": dec(c1), "I_bound_at_to_uA": dec((I_up if pol == "L" else I_dn)(D, c1)), "segment_time_ns": dec(D.hi("C") * abs(c1 - c0) / ((I_up if pol == "L" else I_dn)(D, c1) - D.eps))}
                    for c0, c1 in zip(rec["breakpoints"][:-1], rec["breakpoints"][1:])
                ],
            }
        for N in sorted(set(cfg["uniform_Ns"]) | set(cfg["optimized_Ns"])):
            table.append([name, N, uni.get(N, float("nan")), float(dp[N]["bound"]) if N in dp else float("nan"), T_true, lim, float(taus[pol])])
        res[name] = {
            "tau_ns": frac_record(taus[pol]),
            "true_worst_case": {
                "definition": "interface.md v1 rev. 2 trajectory notion (parameter point may change every instant): C_max * Integral dv / (min over the box of the drive - eps) at the band-edge input, from the far end of the safe domain",
                "quadrature_ns": T_true,
                "simulated_crossing_ns (DOP853 rtol=1e-12, event)": sim_box["t_cross"],
                "simulation_minus_quadrature_ns": sim_box["t_cross"] - T_true,
                "exact_bracket": br_box,
                "constant_theta": {
                    "definition": "one parameter point per run: max over the 32 corners of C_max * Integral dv / (drive - eps)",
                    "quadrature_ns": T_const,
                    "worst_corner": code,
                    "ties": im["corners_within_1e-12_of_max"],
                    "simulated_crossing_ns (DOP853 rtol=1e-12, event)": sim["t_cross"],
                    "simulation_minus_quadrature_ns": sim["t_cross"] - T_const,
                    "exact_bracket": br,
                    "interior_search": im,
                },
                "moving_minus_constant_theta_ns": T_true - T_const,
                "worst_corner": code,
            },
            "tightness": {
                "tau_over_true_worst_case": float(taus[pol]) / T_true,
                "true_worst_case_over_tau": T_true / float(taus[pol]),
                "limit_of_multisegment_bound_ns": lim,
                "limit_over_true_worst_case": lim / T_true,
                "tau_over_constant_theta_worst_case": float(taus[pol]) / T_const,
            },
            "optimized": {str(k): v for k, v in opt.items()},
        }
        res.setdefault("convergence_table", {"header": ["transition", "N", "uniform_bound_ns", "optimized_bound_ns(1mV grid)", "true_worst_case_ns", "N_to_infinity_limit_ns", "tau_single_segment_ns"], "rows": []})["rows"] += table
    return res
