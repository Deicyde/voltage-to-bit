"""Proposers.

Every proposer is UNTRUSTED. A proposer returns a claim (a list of levels and
a deadline, or a disturbance bound and two split points); whether the claim
holds is decided by Lean, never here. Proposers may use floating point,
randomness or anything else. The loop only requires that they are
deterministic given their seed, so that the record can be regenerated.

Proposers
---------
baseline          the single-segment certificate that reproduces the library's
                  closed-form deadline (record 0 of each deadline experiment)
library-prior     the three-level certificate already proved in the library
uniform-grid      equally spaced levels
random-levels     seeded random levels with a deadline rounded to NEAREST
                  (a sloppy numerical proposer: some of its claims are false)
dp-grid           dynamic programme over a 1 mV grid: the best N-level
                  certificate with levels on the grid
controls          deliberately bad proposals, each expected to be rejected
predictors        deadlines taken from simulations of non-worst-case circuits
split-search      (eps experiment) exact search for the split points
"""
from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction

from . import exact
from .exact import Design, below_dec, ceil_dec, dec_str, floor_dec, nearest_dec

TAU_PLACES = 4      # deadlines are stated in ns with 4 decimals (0.1 ps)
EPS_PLACES = 4      # disturbance bounds are stated in uA with 4 decimals


@dataclass
class Proposal:
    slug: str                       # short name, part of the record id
    kind: str                       # rise_certificate | fall_certificate | eps_split
    proposer: dict                  # who/what proposed it, with parameters and seed
    payload: dict                   # the claim itself, as decimal strings
    note: str = ""
    bypass_screen: bool = False     # send to Lean even when the screen says invalid
    expected: str | None = None     # for controls: "lean_rejects"


def level_str(c: Fraction) -> str:
    s = dec_str(c)
    return s if "." in s else s + ".0"


def formal_sum(D: Design, direction: str, levels: list[Fraction]) -> Fraction:
    """The certificate's summed segment times with Lean's arithmetic, whether
    or not the certificate is valid."""
    start = exact.start_level(D, direction)
    return exact.total_time(direction, start, exact.segments(D, direction, levels))


def cert(direction: str, slug: str, proposer: dict, levels: list[Fraction], tau: Fraction,
         tau_source: str, **kw) -> Proposal:
    payload = {"direction": direction, "levels": [level_str(c) for c in levels],
               "tau": dec_str(tau, TAU_PLACES), "tau_source": tau_source}
    return Proposal(slug=slug, kind=f"{direction}_certificate", proposer=proposer,
                    payload=payload, **kw)


UP = f"exact certificate sum rounded UP to {TAU_PLACES} decimals"


# ------------------------------------------------------------------ deadlines

def baseline(D: Design, direction: str) -> Proposal:
    levels = [exact.target_level(D, direction)]
    tau = ceil_dec(formal_sum(D, direction, levels), TAU_PLACES)
    lib = "tauUp" if direction == "rise" else "tauDn"
    return cert(direction, "baseline",
                {"name": "baseline", "kind": "baseline", "params": {}, "seed": None},
                levels, tau, UP,
                note=f"single segment; its exact sum is the library's closed form `Design.{lib}`")


def library_prior() -> Proposal:
    """`illustrative_riseCert_3` of Examples/Illustrative.lean at the frozen commit."""
    return Proposal(
        slug="library-cert3", kind="rise_certificate",
        proposer={"name": "library-prior", "kind": "prior result",
                  "params": {"source": "VoltageToBit.Examples.illustrative_riseCert_3"},
                  "seed": None},
        payload={"direction": "rise", "levels": ["1.0", "1.2", "1.35"], "tau": "2.3400",
                 "tau_source": "as stated in the library (2.34)"},
        note="already proved in the library at the frozen commit; re-checked here")


def uniform(D: Design, direction: str, n: int) -> Proposal:
    a, b = exact.start_level(D, direction), exact.target_level(D, direction)
    levels = [a + (b - a) * Fraction(k, n) for k in range(1, n + 1)]
    tau = ceil_dec(formal_sum(D, direction, levels), TAU_PLACES)
    return cert(direction, f"uniform-n{n}",
                {"name": "uniform-grid", "kind": "search", "params": {"N": n}, "seed": None},
                levels, tau, UP)


def dp_grid_levels(D: Design, direction: str, n_max: int,
                   step: Fraction = Fraction(1, 1000)) -> dict[int, list[Fraction]]:
    """Best N-level certificates with levels on a grid, for every N <= n_max.

    Dynamic programme in floating point over the grid points between the kink
    of the margin function and the output threshold. (Levels before the kink
    are never useful: the proved current bound is constant there, so moving
    such a level to the kink does not increase the sum.) The result is only a
    proposal; its exact value is computed afterwards with fractions and its
    validity is decided by Lean.
    """
    sgn = 1 if direction == "rise" else -1
    start, target = exact.start_level(D, direction), exact.target_level(D, direction)
    kink = D.VIL + D.Vtphi if direction == "rise" else D.VIH - D.Vtnhi
    kink_inside = sgn * (kink - start) > 0 and sgn * (target - kink) > 0
    bound = kink if sgn * (kink - start) > 0 else start
    grid, k = [], 0
    while sgn * (target - sgn * k * step - bound) > 0:
        grid.append(target - sgn * k * step)
        k += 1
    if kink_inside:
        grid.append(kink)
    grid.reverse()                       # ordered in the direction of travel
    margin = exact.Iup if direction == "rise" else exact.Idn
    f = [float(D.Chi / (margin(D, c) - D.eps)) for c in grid]
    g = [float(c) for c in grid]
    s0 = float(start)
    m = len(grid)
    n_max = min(n_max, m)
    inf = float("inf")
    cost = [[inf] * m for _ in range(n_max + 1)]
    back = [[-1] * m for _ in range(n_max + 1)]
    for j in range(m):
        cost[1][j] = abs(g[j] - s0) * f[j]
    for n in range(2, n_max + 1):
        prev, cur, arg = cost[n - 1], cost[n], back[n]
        for j in range(n - 1, m):
            fj, gj = f[j], g[j]
            best, bi = inf, -1
            for i in range(n - 2, j):
                val = prev[i] + abs(gj - g[i]) * fj
                if val < best:
                    best, bi = val, i
            cur[j], arg[j] = best, bi
    out = {}
    for n in range(1, n_max + 1):
        j, path = m - 1, []
        for level in range(n, 0, -1):
            path.append(grid[j])
            j = back[level][j]
        out[n] = path[::-1]
    return out


def dp_grid(D: Design, direction: str, n: int, levels: list[Fraction],
            step: Fraction = Fraction(1, 1000)) -> Proposal:
    tau = ceil_dec(formal_sum(D, direction, levels), TAU_PLACES)
    return cert(direction, f"dp-n{n}",
                {"name": "dp-grid", "kind": "search",
                 "params": {"N": n, "grid_step_V": dec_str(step),
                            "method": "dynamic programme (floating point) over grid levels"},
                 "seed": None},
                levels, tau, UP)


def random_levels(D: Design, direction: str, count: int, seed: int, n: int = 4) -> list[Proposal]:
    """A sloppy stochastic proposer.

    Draws ``n - 1`` distinct interior levels on the 1 mV grid (sorted), ends at
    the output threshold three times out of four and 10 or 20 mV off it
    otherwise, and claims the sum rounded to the NEAREST 0.1 ps. Roughly half
    of its well-formed claims are therefore too small by a fraction of 0.1 ps.
    Only ``random.Random(seed).random()`` is used, so the stream is the same on
    every platform and Python version.
    """
    rng = random.Random(seed)
    sgn = 1 if direction == "rise" else -1
    start, target = exact.start_level(D, direction), exact.target_level(D, direction)
    span = int(abs(target - start) * 1000)
    out = []
    for k in range(1, count + 1):
        offsets: set[int] = set()
        while len(offsets) < n - 1:
            offsets.add(1 + int(rng.random() * (span - 1)))
        last = span
        if rng.random() >= 0.75:
            last += (-20, -10, 10, 20)[int(rng.random() * 4)]
        levels = [start + sgn * Fraction(o, 1000) for o in sorted(offsets | {last})]
        tau = nearest_dec(formal_sum(D, direction, levels), TAU_PLACES)
        out.append(cert(direction, f"random-{k}",
                        {"name": "random-levels", "kind": "stochastic search",
                         "params": {"N": n, "draw": k, "of": count,
                                    "rounding": "nearest (not up)"},
                         "seed": seed},
                        levels, tau, f"certificate sum rounded to the NEAREST {TAU_PLACES} decimals"))
    return out


def deadline_controls(D: Design, direction: str, best_levels: list[Fraction],
                      short_levels: list[Fraction], numerics: dict,
                      floor: Fraction) -> list[Proposal]:
    """Deliberately bad proposals. Each is sent to Lean with the screen
    bypassed, and each is expected to be rejected by Lean itself.

    ``best_levels`` is the incumbent certificate (so a failure can only be due
    to the claimed deadline); ``short_levels`` is a short certificate that is
    easy to read once damaged.
    """
    sgn = 1 if direction == "rise" else -1
    target = exact.target_level(D, direction)
    margin = exact.Iup if direction == "rise" else exact.Idn
    ctl = lambda name, params=None: {"name": name, "kind": "deliberately bad control",
                                     "params": params or {}, "seed": None}
    out = []

    best_sum = formal_sum(D, direction, best_levels)
    out.append(cert(direction, "ctl-deadline-rounded-down", ctl("adversarial-control"),
                    best_levels, below_dec(best_sum, TAU_PLACES),
                    f"incumbent's exact sum rounded DOWN to {TAU_PLACES} decimals",
                    note="deadline smaller than the certificate supports, by less than 0.1 ps",
                    bypass_screen=True, expected="lean_rejects"))

    swapped = list(short_levels)
    swapped[1], swapped[2] = swapped[2], swapped[1]
    out.append(cert(direction, "ctl-levels-out-of-order", ctl("adversarial-control"),
                    swapped, ceil_dec(formal_sum(D, direction, swapped), TAU_PLACES),
                    "formula value of the damaged list, rounded up",
                    note="two interior levels exchanged",
                    bypass_screen=True, expected="lean_rejects"))

    # a level beyond the threshold at which the proved current bound is below eps
    bad, c = None, target
    while exact.start_level(D, "rise") <= c <= exact.start_level(D, "fall"):
        c += sgn * Fraction(1, 20)
        if margin(D, c) < D.eps:
            bad = c
            break
    if bad is not None:
        damaged = list(short_levels[:-1]) + [bad, target]
        out.append(cert(direction, "ctl-margin-below-eps", ctl("adversarial-control"),
                        damaged, ceil_dec(formal_sum(D, direction, damaged), TAU_PLACES),
                        "formula value of the damaged list, rounded up",
                        note=(f"extra level {level_str(bad)} V, where the proved current bound "
                              f"{float(margin(D, bad)):.3f} uA is below eps: its slope 'bound' is "
                              "negative, so the unchecked formula returns a negative time"),
                        bypass_screen=True, expected="lean_rejects"))

    short = list(short_levels[:-1]) + [target - sgn * Fraction(1, 20)]
    out.append(cert(direction, "ctl-final-level-short", ctl("adversarial-control"),
                    short, ceil_dec(formal_sum(D, direction, short), TAU_PLACES),
                    "exact sum of the shortened list, rounded up",
                    note="stops 50 mV short of the output threshold (a silently redefined threshold)",
                    bypass_screen=True, expected="lean_rejects"))

    pred = numerics["predictions"]
    out.append(cert(direction, "pred-typical-simulation",
                    {"name": "nominal-simulation-predictor", "kind": "numerical prediction",
                     "params": {"circuit": "nominal devices, 10 fF, no disturbance, rail input, "
                                           "start at the opposite rail",
                                "simulated_delay_ns": round(pred["typical"]["delay_ns"], 9)},
                     "seed": None},
                    best_levels, nearest_dec(Fraction(repr(pred["typical"]["delay_ns"])), TAU_PLACES),
                    "simulated delay of the nominal circuit, rounded to nearest",
                    note="a plausible-looking prediction that is not a worst-case bound",
                    bypass_screen=True, expected="lean_rejects"))
    out.append(cert(direction, "pred-nominal-devices",
                    {"name": "nominal-simulation-predictor", "kind": "numerical prediction",
                     "params": {"circuit": "nominal devices and no disturbance, but adverse input "
                                           "level, largest load and far end of the safe domain",
                                "simulated_delay_ns": round(pred["nominal_devices"]["delay_ns"], 9)},
                     "seed": None},
                    best_levels,
                    nearest_dec(Fraction(repr(pred["nominal_devices"]["delay_ns"])), TAU_PLACES),
                    "simulated delay with nominal devices under the adverse stimulus, rounded to nearest",
                    note="closer to the worst case, still not a bound",
                    bypass_screen=True, expected="lean_rejects"))

    worst = Fraction(repr(numerics["worst_case"]["worst_case_delay_ns"]))
    gap_tau = floor_dec(worst, 2)
    if floor < gap_tau < worst:
        out.append(cert(direction, "ctl-below-model-worst-case", ctl("adversarial-control"),
                        best_levels, gap_tau,
                        "numerical worst-case delay rounded DOWN to 2 decimals",
                        note=("between the Lean-proved floor and the numerical worst case: false "
                              "according to quadrature, but not formally refuted here"),
                        bypass_screen=True, expected="lean_rejects"))

    infimum = Fraction(repr(numerics["certificate_infimum_ns"]))
    if infimum - worst > Fraction(2, 1000):
        mid = ceil_dec(worst + (infimum - worst) / 2, 3)
        out.append(cert(direction, "ctl-true-but-out-of-reach", ctl("adversarial-control"),
                        best_levels, mid,
                        "midpoint between the numerical worst case and the method's limit",
                        note=("above the model's worst-case delay (so probably a true deadline) "
                              "but below what any certificate of this form can reach"),
                        bypass_screen=True, expected="lean_rejects"))
    return out


# ------------------------------------------------------------------------ eps

def eps_margins(D: Design) -> dict[str, Fraction]:
    """The six margins that `Admissible` compares with eps."""
    return {"up": exact.Iup(D, D.VOH), "dn": exact.Idn(D, D.VOL), "hiP": exact.RhiP(D),
            "hiN": exact.RhiN(D), "loN": exact.RloN(D), "loP": exact.RloP(D)}


def boundary_margin(D: Design, which: str, x: Fraction) -> Fraction:
    """The smaller of the two restoring-current margins at one boundary, as a
    function of that boundary's split point."""
    E = D.replace(**{which: dec_str(x)})
    return min(exact.RhiP(E), exact.RhiN(E)) if which == "uHi" else min(exact.RloN(E), exact.RloP(E))


def best_split(D: Design, which: str, places: int) -> Fraction:
    """Exact search for the split point with ``places`` decimals that maximises
    the boundary margin: a 10 mV scan of the safe domain, then one decade of
    refinement at a time (the margin is the minimum of an increasing and a
    decreasing function of the split point, hence unimodal)."""
    lo, hi = floor_dec(D.Vlo, 2), ceil_dec(D.Vhi, 2)
    cands = [lo + Fraction(k, 100) for k in range(int((hi - lo) * 100) + 1)]
    best = max(cands, key=lambda x: boundary_margin(D, which, x))
    for p in range(3, places + 1):
        cands = [best + Fraction(k, 10 ** p) for k in range(-10, 11)]
        best = max(cands, key=lambda x: boundary_margin(D, which, x))
    return best


def eps_proposal(slug: str, proposer: dict, eps: Fraction, uHi: str, uLo: str, **kw) -> Proposal:
    return Proposal(slug=slug, kind="eps_split", proposer=proposer,
                    payload={"eps": dec_str(eps), "uHi": uHi, "uLo": uLo}, **kw)


def eps_baseline(D: Design) -> Proposal:
    return eps_proposal("baseline", {"name": "baseline", "kind": "baseline", "params": {}, "seed": None},
                        D.eps, D.raw["uHi"], D.raw["uLo"],
                        note="the design record as it is")


def eps_same_splits(D: Design) -> Proposal:
    eps = below_dec(min(eps_margins(D).values()), EPS_PLACES)
    return eps_proposal("same-splits-max-eps",
                        {"name": "margin-readout", "kind": "search",
                         "params": {"rule": f"largest {EPS_PLACES}-decimal eps strictly below the "
                                            "smallest margin, split points unchanged"},
                         "seed": None},
                        eps, D.raw["uHi"], D.raw["uLo"],
                        note="slack already present in the record: no split point is changed")


def eps_split_search(D: Design, places: int) -> Proposal:
    uHi, uLo = best_split(D, "uHi", places), best_split(D, "uLo", places)
    E = D.replace(uHi=dec_str(uHi), uLo=dec_str(uLo))
    eps = below_dec(min(eps_margins(E).values()), EPS_PLACES)
    return eps_proposal(f"split-search-{places}dp",
                        {"name": "split-search", "kind": "search",
                         "params": {"split_point_decimals": places,
                                    "method": "exact decade-by-decade maximisation of the "
                                              "smaller boundary margin",
                                    "rule": f"largest {EPS_PLACES}-decimal eps strictly below the "
                                            "smallest margin"},
                         "seed": None},
                        eps, dec_str(uHi), dec_str(uLo))


def ceiling_pivot(D: Design, E: Fraction, max_places: int = 7) -> Fraction | None:
    """A split point at which BOTH upper-boundary margins are <= E, if one with
    few decimals exists. Its existence shows that no split point supports
    eps >= E (one margin is monotone up, the other monotone down)."""
    half = Fraction(1, 2)

    def both_small(x: Fraction) -> bool:
        y = D.VDDlo - x - D.Vtphi
        return (D.knlo * half * exact.psq(x - D.Vtnhi) <= E
                and D.kplo * half * (exact.psq(y + (D.Vhi - D.VDDhi)) - exact.psq(y)) <= E)

    for p in range(2, max_places + 1):
        centre = best_split(D, "uHi", p)
        for k in sorted(range(-10, 11), key=abs):
            x = centre + Fraction(k, 10 ** p)
            if both_small(x):
                return x
    return None


def eps_controls(D: Design, best: Proposal, model_tolerance: float) -> list[Proposal]:
    ctl = {"name": "adversarial-control", "kind": "deliberately bad control", "params": {}, "seed": None}
    out = []
    tight = min(eps_margins(D).values())
    if exact.is_decimal(tight):
        out.append(eps_proposal("ctl-eps-equals-margin", ctl, tight, D.raw["uHi"], D.raw["uLo"],
                                note="eps equal to the smallest margin of the unchanged record: "
                                     "the inequality must be strict",
                                bypass_screen=True, expected="lean_rejects"))
    step = Fraction(1, 10 ** EPS_PLACES)
    out.append(eps_proposal("ctl-eps-one-step-more", ctl,
                            Fraction(best.payload["eps"]) + step,
                            best.payload["uHi"], best.payload["uLo"],
                            note=f"the best accepted eps plus {dec_str(step)} uA, same split points",
                            bypass_screen=True, expected="lean_rejects"))
    guess = floor_dec(Fraction(repr(model_tolerance)), 1)
    if guess > Fraction(best.payload["eps"]):
        out.append(eps_proposal(
            "pred-model-tolerance",
            {"name": "boundary-scan-predictor", "kind": "numerical prediction",
             "params": {"model_min_inward_boundary_current_uA": round(model_tolerance, 9),
                        "rule": "numerical minimum of the model's restoring current at the ends "
                                "of the safe domain, rounded down to 1 decimal"},
             "seed": None},
            guess, best.payload["uHi"], best.payload["uLo"],
            note="what the model itself appears to tolerate numerically; not what the closed-form "
                 "margins can prove",
            bypass_screen=True, expected="lean_rejects"))
    return out
