"""Floating-point numerics for the square-law inverter model.

NUMERICAL EVIDENCE ONLY. Nothing in this module is a proof, and nothing in it
decides whether a proposal is accepted. It is used for three things:

1. the model's worst-case rise/fall delay, by quadrature, cross-checked by an
   independent time-stepping simulation (a proved deadline below this number
   would indicate an error somewhere);
2. "predicted" deadlines from simulations of non-worst-case circuits, used as
   deliberately untrustworthy proposals;
3. the model's actual restoring currents at the ends of the safe domain, to
   show how much of the disturbance tolerance the closed-form margins give up.

Only the Python standard library is used. Workstream D's simulator under
``experiments/`` is not imported.
"""
from __future__ import annotations

import itertools
import math
import random

from .exact import Design

Theta = tuple[float, float, float, float, float]  # (VDD, kn, kp, Vtn, Vtp)

THETA_NAMES = ("VDD", "kn", "kp", "Vtn", "Vtp")

# `nominal : Params := ⟨1.8, 200, 100, 0.5, 0.5⟩` in Examples/Illustrative.lean,
# and the 10 fF load of `illustrative_scenario` in the same file.
NOMINAL_THETA: Theta = (1.8, 200.0, 100.0, 0.5, 0.5)
NOMINAL_C = 10.0


def psq(x: float) -> float:
    return x * x if x > 0.0 else 0.0


def i_p(th: Theta, u: float, v: float) -> float:
    """PMOS current, supply -> output node (`Ip` in Model/Device.lean)."""
    VDD, _, kp, _, Vtp = th
    return kp / 2.0 * (psq(VDD - u - Vtp) - psq(v - u - Vtp))


def i_n(th: Theta, u: float, v: float) -> float:
    """NMOS current, output node -> ground (`In` in Model/Device.lean)."""
    _, kn, _, Vtn, _ = th
    return kn / 2.0 * (psq(u - Vtn) - psq(u - v - Vtn))


def inet(th: Theta, u: float, v: float) -> float:
    """Net device current into the output node (`Inet`)."""
    return i_p(th, u, v) - i_n(th, u, v)


# ---------------------------------------------------------------- quadrature

_S = math.sqrt(10.0 / 7.0)
_GL = (
    (0.0, 128.0 / 225.0),
    (+math.sqrt(5.0 - 2.0 * _S) / 3.0, (322.0 + 13.0 * math.sqrt(70.0)) / 900.0),
    (-math.sqrt(5.0 - 2.0 * _S) / 3.0, (322.0 + 13.0 * math.sqrt(70.0)) / 900.0),
    (+math.sqrt(5.0 + 2.0 * _S) / 3.0, (322.0 - 13.0 * math.sqrt(70.0)) / 900.0),
    (-math.sqrt(5.0 + 2.0 * _S) / 3.0, (322.0 - 13.0 * math.sqrt(70.0)) / 900.0),
)


def integrate(f, a: float, b: float, breaks=(), panels: int = 64) -> float:
    """Composite 5-point Gauss-Legendre rule on [a, b].

    The interval is first split at ``breaks`` (the kinks of the integrand, where
    a transistor changes region), so that the rule only ever sees smooth pieces.
    """
    pts = sorted({a, b, *[x for x in breaks if a < x < b]})
    total = 0.0
    for lo, hi in zip(pts, pts[1:]):
        h = (hi - lo) / panels
        for i in range(panels):
            mid = lo + (i + 0.5) * h
            for x, w in _GL:
                total += w * f(mid + 0.5 * h * x) * 0.5 * h
    return total


def integrate_checked(f, a: float, b: float, breaks=(), tol: float = 1e-12):
    """Double the number of panels until two successive values agree.

    Returns ``(value, panels, last difference)``.
    """
    n = 16
    prev = integrate(f, a, b, breaks, n)
    while n < 2 ** 13:
        n *= 2
        cur = integrate(f, a, b, breaks, n)
        diff = abs(cur - prev)
        if diff <= tol * max(1.0, abs(cur)):
            return cur, n, diff
        prev = cur
    raise RuntimeError("quadrature did not converge")


def delay(direction: str, th: Theta, u: float, C: float, w: float,
          v_from: float, v_to: float) -> float:
    """Time for the node to move from ``v_from`` to ``v_to`` under
    ``C dv/dt = Inet(th, u, v) + w`` with constant ``u`` and ``w``.

    Returns ``inf`` when the current does not keep the required sign on the
    whole range (the node would stall).
    """
    sign = 1.0 if direction == "rise" else -1.0
    lo, hi = min(v_from, v_to), max(v_from, v_to)
    breaks = (u + th[4], u - th[3], th[0])
    probes = sorted({lo, hi, *[x for x in breaks if lo < x < hi]})
    grid = [lo + (hi - lo) * i / 400 for i in range(401)] + probes
    if min(sign * (inet(th, u, v) + w) for v in grid) <= 0.0:
        return math.inf
    value, _, _ = integrate_checked(lambda v: C / (sign * (inet(th, u, v) + w)), lo, hi, breaks)
    return value


def crossing_time_rk4(direction: str, th: Theta, u: float, C: float, w: float,
                      v0: float, target: float, dt: float = 1e-4, t_max: float = 100.0) -> float:
    """Independent cross-check: classical Runge-Kutta in time until the node
    crosses ``target``; the last step is located by bisection on its length."""
    def f(v):
        return (inet(th, u, v) + w) / C

    def step(v, h):
        k1 = f(v)
        k2 = f(v + 0.5 * h * k1)
        k3 = f(v + 0.5 * h * k2)
        k4 = f(v + h * k3)
        return v + h * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0

    def crossed(v):
        return v >= target if direction == "rise" else v <= target

    t, v = 0.0, v0
    while t < t_max:
        nxt = step(v, dt)
        if crossed(nxt):
            lo, hi = 0.0, dt
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if crossed(step(v, mid)):
                    hi = mid
                else:
                    lo = mid
            return t + hi
        v, t = nxt, t + dt
    return math.inf


def trajectory_rk4(th: Theta, u: float, C: float, w: float, v0: float,
                   t_end: float, points: int = 200, substeps: int = 50):
    """A coarse trace ``[(t, v), ...]`` of ``C dv/dt = Inet + w`` for plotting."""
    def f(v):
        return (inet(th, u, v) + w) / C

    out = [(0.0, v0)]
    h = t_end / (points * substeps)
    v = v0
    for i in range(1, points + 1):
        for _ in range(substeps):
            k1 = f(v)
            k2 = f(v + 0.5 * h * k1)
            k3 = f(v + 0.5 * h * k2)
            k4 = f(v + h * k3)
            v += h * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0
        out.append((i * t_end / points, v))
    return out


# ------------------------------------------------------- worst case of the model

def box(D: Design) -> list[tuple[float, float]]:
    return [(float(D.VDDlo), float(D.VDDhi)), (float(D.knlo), float(D.knhi)),
            (float(D.kplo), float(D.kphi)), (float(D.Vtnlo), float(D.Vtnhi)),
            (float(D.Vtplo), float(D.Vtphi))]


def corners(D: Design) -> list[Theta]:
    """The 32 corners of the parameter box."""
    return [tuple(c) for c in itertools.product(*box(D))]


def stimulus(D: Design, direction: str) -> dict:
    """The adverse stimulus for one direction: input at the edge of its valid
    band, largest capacitance, disturbance at the adverse bound, start at the
    far end of the safe domain."""
    if direction == "rise":
        return {"u": float(D.VIL), "C": float(D.Chi), "w": -float(D.eps),
                "v_from": float(D.Vlo), "v_to": float(D.VOH)}
    return {"u": float(D.VIH), "C": float(D.Chi), "w": float(D.eps),
            "v_from": float(D.Vhi), "v_to": float(D.VOL)}


def worst_case(D: Design, direction: str, samples: int = 400, seed: int = 20261109) -> dict:
    """The model's worst-case delay for one direction.

    * all 32 corners of the box under the adverse stimulus (quadrature);
    * a seeded random sample of interior parameter choices, inputs inside the
      valid band, capacitances and constant disturbances within their bounds,
      to look for anything slower than the slowest corner;
    * an independent Runge-Kutta crossing time at the slowest corner.

    Finite numerical evidence: it does not prove that no slower trajectory
    exists (time-varying inputs and disturbances are not sampled; for this
    scalar system the pointwise-slowest choice is the constant one).
    """
    st = stimulus(D, direction)
    rows = []
    for th in corners(D):
        rows.append((delay(direction, th, st["u"], st["C"], st["w"], st["v_from"], st["v_to"]), th))
    rows.sort(key=lambda r: (-r[0], r[1]))
    worst_t, worst_th = rows[0]

    rng = random.Random(seed)
    bx = box(D)
    eps, clo, chi = float(D.eps), float(D.Clo), float(D.Chi)

    def draw(lo, hi):
        # half of the draws sit on an end of the range, so that the sample
        # also explores edges and faces of the box, not only its interior
        r = rng.random()
        if r < 0.25:
            return lo
        if r < 0.5:
            return hi
        return lo + (hi - lo) * rng.random()

    slowest_sample = 0.0
    for _ in range(samples):
        th = tuple(draw(lo, hi) for lo, hi in bx)
        du = draw(0.0, 0.5)
        u = st["u"] - du if direction == "rise" else st["u"] + du
        C = draw(clo, chi)
        w = draw(-eps, eps)
        slowest_sample = max(slowest_sample,
                             delay(direction, th, u, C, w, st["v_from"], st["v_to"]))

    rk4 = crossing_time_rk4(direction, worst_th, st["u"], st["C"], st["w"],
                            st["v_from"], st["v_to"])
    return {
        "direction": direction,
        "stimulus": st,
        "worst_corner": dict(zip(THETA_NAMES, worst_th)),
        "worst_case_delay_ns": worst_t,
        "rk4_crossing_time_ns": rk4,
        "abs_diff_quadrature_vs_rk4_ns": abs(rk4 - worst_t),
        "corner_delays_ns": [{"theta": dict(zip(THETA_NAMES, th)), "delay_ns": t} for t, th in rows],
        "random_sample": {"count": samples, "seed": seed,
                          "slowest_delay_ns": slowest_sample,
                          "none_slower_than_worst_corner": slowest_sample <= worst_t + 1e-12},
    }


def moving_parameter_worst_case(D: Design, direction: str) -> float:
    """Worst-case delay if the parameter point were allowed to move inside the
    box during a run: at every voltage the smallest drive current over the 32
    corners is used. At the frozen commit the parameters are constant during a
    run, so this number is only an upper bound for `worst_case`; it is the
    relevant worst case for a trajectory notion that picks a point of the box
    at each instant."""
    st = stimulus(D, direction)
    sign = 1.0 if direction == "rise" else -1.0
    cs = corners(D)
    lo, hi = min(st["v_from"], st["v_to"]), max(st["v_from"], st["v_to"])
    breaks = sorted({x for th in cs for x in (st["u"] + th[4], st["u"] - th[3], th[0])})

    def integrand(v):
        drive = min(sign * (inet(th, st["u"], v) + st["w"]) for th in cs)
        if drive <= 0.0:
            raise RuntimeError("the envelope drive current is not positive")
        return st["C"] / drive

    value, _, _ = integrate_checked(integrand, lo, hi, breaks, tol=1e-11)
    return value


def margin_float(D: Design, direction: str, c: float) -> float:
    """Float mirror of `Design.Iup c` / `Design.Idn c` (the *proved* current bound)."""
    if direction == "rise":
        return (float(D.kplo) / 2.0 * (psq(float(D.VDDlo - D.VIL - D.Vtphi))
                                       - psq(c - float(D.VIL + D.Vtphi)))
                - float(D.knhi) / 2.0 * psq(float(D.VIL - D.Vtnlo)))
    return (float(D.knlo) / 2.0 * (psq(float(D.VIH - D.Vtnhi)) - psq(float(D.VIH - D.Vtnhi) - c))
            - float(D.kphi) / 2.0 * psq(float(D.VDDhi - D.VIH - D.Vtplo)))


def certificate_infimum(D: Design, direction: str) -> float:
    """The limit of the certificate method: the integral of
    ``Chi / (margin(v) - eps)`` over the swing. Every certificate sum is a
    Riemann sum of this monotone integrand taken at the slow end of each
    segment, so every certificate deadline is above this number and
    refinement approaches it. (A numerical value, not a Lean statement.)"""
    eps, chi = float(D.eps), float(D.Chi)
    if direction == "rise":
        a, b, kink = float(D.Vlo), float(D.VOH), float(D.VIL + D.Vtphi)
    else:
        a, b, kink = float(D.VOL), float(D.Vhi), float(D.VIH - D.Vtnhi)
    value, _, _ = integrate_checked(lambda v: chi / (margin_float(D, direction, v) - eps),
                                    a, b, (kink,))
    return value


def predictions(D: Design, direction: str) -> dict:
    """Delays of *non-worst-case* circuits, used as untrustworthy 'predicted'
    deadlines.

    * ``typical``: nominal devices, nominal 10 fF load, no disturbance, ideal
      rail input, starting from the opposite rail;
    * ``nominal_devices``: nominal devices and no disturbance, but the adverse
      input level, largest load and far end of the safe domain.
    """
    st = stimulus(D, direction)
    vdd = NOMINAL_THETA[0]
    if direction == "rise":
        typical = delay("rise", NOMINAL_THETA, 0.0, NOMINAL_C, 0.0, 0.0, st["v_to"])
        typical_setup = {"u": 0.0, "C": NOMINAL_C, "w": 0.0, "v_from": 0.0, "v_to": st["v_to"]}
    else:
        typical = delay("fall", NOMINAL_THETA, vdd, NOMINAL_C, 0.0, vdd, st["v_to"])
        typical_setup = {"u": vdd, "C": NOMINAL_C, "w": 0.0, "v_from": vdd, "v_to": st["v_to"]}
    nominal_devices = delay(direction, NOMINAL_THETA, st["u"], st["C"], 0.0,
                            st["v_from"], st["v_to"])
    return {
        "nominal_theta": dict(zip(THETA_NAMES, NOMINAL_THETA)),
        "typical": {"setup": typical_setup, "delay_ns": typical},
        "nominal_devices": {"setup": {"u": st["u"], "C": st["C"], "w": 0.0,
                                      "v_from": st["v_from"], "v_to": st["v_to"]},
                            "delay_ns": nominal_devices},
    }


def boundary_margins(D: Design) -> dict:
    """The model's actual restoring current at each end of the safe domain:
    the minimum, over the 32 corners and a fine grid of input values, of the
    device current pointing into the domain. (Each term is monotone in every
    parameter, so the minimum over the box is at a corner; the input is
    scanned.) The disturbance bound the model itself could tolerate for
    safe-domain invariance is the smaller of the two numbers."""
    out = {}
    for name, v, sign in (("Vhi", float(D.Vhi), -1.0), ("Vlo", float(D.Vlo), 1.0)):
        best = (math.inf, None, None)
        for th in corners(D):
            for i in range(4001):
                u = -1.0 + i * 1e-3
                val = sign * inet(th, u, v)
                if val < best[0]:
                    best = (val, u, th)
        _, u0, th0 = best
        for i in range(4001):
            u = u0 - 2e-3 + i * 1e-6
            val = sign * inet(th0, u, v)
            if val < best[0]:
                best = (val, u, th0)
        out[name] = {"min_inward_current_uA": best[0], "at_u_V": best[1],
                     "at_corner": dict(zip(THETA_NAMES, best[2])),
                     "u_scan": {"from_V": -1.0, "to_V": 3.0, "coarse_step_V": 1e-3,
                                "fine_step_V": 1e-6}}
    out["model_tolerance_uA"] = min(out["Vhi"]["min_inward_current_uA"],
                                    out["Vlo"]["min_inward_current_uA"])
    return out


def rounded(obj, digits: int = 9):
    """Round every float in a nested structure, so that stored numerical
    evidence does not depend on the last bits of the platform's libm."""
    if isinstance(obj, float):
        if math.isinf(obj) or math.isnan(obj):
            return str(obj)
        return round(obj, digits)
    if isinstance(obj, dict):
        return {k: rounded(v, digits) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [rounded(v, digits) for v in obj]
    return obj
