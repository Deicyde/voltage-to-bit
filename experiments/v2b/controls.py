"""Task 6: negative controls (HANDOFF section 5). Each control ends in an explicit
rejection by the admissibility checker and/or an exhibited trajectory that
violates the guarantee. A failed sufficient precondition alone is never
reported as a failure of the circuit.
"""
from __future__ import annotations

import math
from fractions import Fraction

import numpy as np
from scipy.optimize import brentq

from . import laws
from . import trajectories as T
from .common import corner_array, float_design
from .design import (
    THETA_KEYS,
    Design,
    DesignFormatError,
    I_dn,
    I_up,
    admissibility,
    closed_form,
    corner_by_code,
    dec,
    design_from_dict,
    design_to_dict,
    frac_record,
    is_admissible,
    margins_only_pass,
    tau_dn,
    tau_up,
)
from .sim import make_rhs, solve_ref


def decode_f(v: float, F) -> str:
    """Three-valued decode on floats: 'high' / 'low' / 'undefined'."""
    if v >= F.VOH:
        return "high"
    if v <= F.VOL:
        return "low"
    return "undefined"


def _sample(law, th, C, v0, u, w, t_end, n=201, Vth=None, sgn=1, extra_t=(), early=False, rhs=None):
    """Constant-input, constant-disturbance run (or any given ``rhs``) sampled on a uniform grid
    (quadratically refined towards t = 0 if ``early``) plus ``extra_t`` (exactly)."""
    if rhs is None:
        rhs = make_rhs(law, th, C, lambda t: u, lambda t: w)
    base = t_end * np.linspace(0.0, 1.0, n) ** 2 if early else np.linspace(0.0, t_end, n)
    tt = np.unique(np.concatenate([base, np.asarray(list(extra_t), dtype=float)]))
    r = solve_ref(rhs, v0, t_end, method="DOP853", rtol=1e-11, atol=1e-13, Vth=Vth, sgn=sgn, dense_t=tt)
    return r


def _v_at(r, t: float) -> float:
    i = int(np.argmin(np.abs(r["t"] - t)))
    assert abs(r["t"][i] - t) < 1e-12, "sample time was not on the output grid"
    return float(r["v"][i])


def _failed(conds) -> list[str]:
    return [f"{c.id}: {c.statement} (lhs {dec(c.lhs)}, rhs {dec(c.rhs)})" for c in conds if not c.holds]


def control_invalid_bounds(D: Design, worst_codes: dict) -> tuple[dict, dict]:
    F = float_design(D)
    out, traj = {}, {}
    thL = [float(x) for x in corner_by_code(D, worst_codes["L"])]

    # (a) capacitance bounds inverted: "C_max" (second entry) is now the smaller number
    DA = D.with_box("C", D.hi("C"), D.lo("C"), name=D.name + "+C-bounds-inverted")
    conds = admissibility(DA)
    naive_tau = float(tau_up(DA))
    c_actual = float(max(DA.lo("C"), DA.hi("C")))
    r = _sample(laws.inet_formal, thL, c_actual, F.Vlo, F.VIL, -F.eps, 1.2 * float(tau_up(D)), Vth=F.VOH, sgn=1, extra_t=[naive_tau])
    v_at = _v_at(r, naive_tau)
    out["a_capacitance_bounds_inverted"] = {
        "design_variant": design_to_dict(DA),
        "checker_verdict": "REJECTED" if not is_admissible(DA) else "ACCEPTED",
        "failed_conditions": _failed(conds),
        "six_margins_alone_would_pass": margins_only_pass(DA),
        "naive_tau_up_ns (uses the second entry as C_max)": naive_tau,
        "exhibited_trajectory": {
            "theta": dict(zip(THETA_KEYS, thL)), "C_fF": c_actual, "note": "C lies between the two listed numbers", "u": F.VIL, "w": -F.eps, "v0": F.Vlo,
            "v_at_naive_tau_V": v_at, "decoded_at_naive_tau": decode_f(v_at, F), "actual_crossing_ns": r["t_cross"],
            "guarantee_with_naive_tau_violated": bool(v_at < F.VOH),
        },
    }
    traj["i_a_C_inverted"] = (r["t"], r["v"])

    # (b) kp bounds inverted: a margins-only check reads kp_min = 80
    DB = D.with_box("kp", "80", "10", name=D.name + "+kp-bounds-inverted")
    conds = admissibility(DB)
    thB = list(thL)
    thB[2] = 10.0  # a kp between the two listed numbers
    r = _sample(laws.inet_formal, thB, F.C_lo, F.Vlo, F.VIL, -F.eps, 60.0, n=301, Vth=F.VOH, sgn=1)
    out["b_kp_bounds_inverted"] = {
        "design_variant": design_to_dict(DB),
        "checker_verdict": "REJECTED" if not is_admissible(DB) else "ACCEPTED",
        "failed_conditions": _failed(conds),
        "six_margins_alone_would_pass": margins_only_pass(DB),
        "exhibited_trajectory": {
            "theta": dict(zip(THETA_KEYS, thB)), "C_fF": F.C_lo, "u": F.VIL, "w": -F.eps, "v0": F.Vlo, "t_end_ns": 60.0,
            "v_final_V": r["v_final"], "vmin_V": r["vmin"], "ever_valid_high": r["t_cross"] is not None,
            "left_safe_domain": bool(r["vmin"] < F.Vlo - 1e-9), "decoded_final": decode_f(r["v_final"], F),
        },
    }
    traj["i_b_kp_inverted"] = (r["t"], r["v"])

    # (c) format-level: a binary float in the record is refused outright
    bad = design_to_dict(D)
    bad["eps"] = 2.0
    try:
        design_from_dict(bad)
        verdict = "ACCEPTED (unexpected)"
    except DesignFormatError as exc:
        verdict = f"REJECTED at load: {exc}"
    out["c_float_instead_of_decimal_string"] = {"checker_verdict": verdict}
    return out, traj


def control_observation_time(D: Design, worst_codes: dict, brackets: dict) -> tuple[dict, dict]:
    """(ii) Sampling earlier than the model's own worst-case delay. The exhibited trajectory is
    the slowest one of the interface.md v1 (rev. 2) inclusion at the band-edge input: capacitance
    C_max, disturbance at the adverse bound, and at each instant the parameter point of the box
    with the weakest drive (which is one fixed corner for the rise, and switches once, as the
    output passes VDD_max, for the fall)."""
    F = float_design(D)
    _codes, Cn = corner_array(D)
    out, traj = {}, {}
    for pol, name in (("L", "rise"), ("H", "fall")):
        tau = float(tau_up(D) if pol == "L" else tau_dn(D))
        box_rhs = make_rhs(laws.inet_formal, None, None, (lambda t: F.VIL) if pol == "L" else (lambda t: F.VIH), fb=5 if pol == "L" else 6, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, box=Cn)
        L = brackets[name]["lower_float"]
        U = brackets[name]["upper_float"]
        plan = (("0.5 x lower bound", 0.5 * L), ("0.9 x lower bound", 0.9 * L), ("lower bound itself", L), ("upper bracket", U), ("midway to tau", 0.5 * (U + tau)), ("tau", tau))
        ex = [t for _, t in plan]
        if pol == "L":
            r = _sample(None, None, None, F.Vlo, None, None, 1.2 * tau, n=481, Vth=F.VOH, sgn=1, extra_t=ex, rhs=box_rhs)
        else:
            r = _sample(None, None, None, F.Vhi, None, None, 1.2 * tau, n=481, Vth=F.VOL, sgn=-1, extra_t=ex, rhs=box_rhs)
        samples = []
        for label, ts in plan:
            v = _v_at(r, ts)
            samples.append({"sample_time": label, "t_ns": ts, "v_V": v, "decoded": decode_f(v, F), "theorem_window_nonempty (t >= tau)": bool(ts >= tau), "valid_output": decode_f(v, F) == ("high" if pol == "L" else "low")})
        out[name] = {
            "trajectory": {"selection": "box_low" if pol == "L" else "box_high", "theta": "weakest-drive point of the box at each instant (constant-theta worst corner: " + worst_codes[pol] + ")", "C_fF": F.C_hi, "u": F.VIL if pol == "L" else F.VIH, "w": -F.eps if pol == "L" else F.eps, "v0": F.Vlo if pol == "L" else F.Vhi},
            "rigorous_lower_bound_on_this_trajectory_crossing_ns": brackets[name]["lower_ns"],
            "rigorous_upper_bound_ns": brackets[name]["upper_ns"],
            "tau_ns": tau,
            "observed_crossing_ns": r["t_cross"],
            "samples": samples,
            "reading": "any observation earlier than the lower bound sees an output that is not yet valid on this admissible trajectory; between the upper bracket and tau no failing trajectory was found, but the single-segment theorem does not certify it (a failed precondition, not a failed circuit)",
        }
        traj[f"ii_{name}_worst_case"] = (r["t"], r["v"])
    return out, traj


def control_miswired(D: Design, cfg: dict, jobs: int) -> tuple[dict, dict]:
    """(iii) NMOS as pull-up from VDD, PMOS as pull-down to ground, both gates on u."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    nominal = [0.5 * (F.lo(k) + F.hi(k)) for k in THETA_KEYS]
    out, traj = {}, {}
    cases = []
    for label, u, v0, want in (("input low, start low", F.VIL, F.Vlo, "high"), ("input low, start high", F.VIL, F.Vhi, "high"), ("input high, start high", F.VIH, F.Vhi, "low"), ("input high, start low", F.VIH, F.Vlo, "low")):
        r = _sample(laws.inet_miswired, nominal, F.C_lo, v0, u, 0.0, 40.0, n=301, early=True)
        got = decode_f(r["v_final"], F)
        cases.append({"case": label, "u_V": u, "v0_V": v0, "theta": "nominal (box centre)", "C_fF": F.C_lo, "w": 0.0, "t_end_ns": 40.0, "v_final_V": r["v_final"], "decoded_final": got, "inverter_requires": want, "guarantee_violated": got != want})
        traj["iii_" + label.replace(",", "").replace(" ", "_")] = (r["t"], r["v"])
    out["exhibited_trajectories"] = cases
    out["dead_zone_note"] = "with w = 0 every v in [u - V_tn, u + V_tp] is stationary (both devices off): the miswired pair is a follower with a dead zone, not an inverter"
    # the analogue of the margin test, evaluated on the miswired law
    v_up = np.linspace(F.Vlo, F.VOH, 1451)
    v_dn = np.linspace(F.VOL, F.Vhi, 1831)
    m_up = min(float(laws.inet_miswired(F.VIL, v_up, *th).min()) for th in Cn)
    m_dn = min(float((-laws.inet_miswired(F.VIH, v_dn, *th)).min()) for th in Cn)
    out["margin_analogue"] = {
        "min pull-up at u = V_IL over v in [V_lo, V_OH], 32 corners (uA)": m_up,
        "min pull-down at u = V_IH over v in [V_OL, V_hi], 32 corners (uA)": m_dn,
        "eps_uA": F.eps,
        "verdict": "REJECTED: no positive current margin" if (m_up <= F.eps or m_dn <= F.eps) else "margin positive",
    }
    mm = T.run_matrix(
        D, cfg, jobs=jobs, law=laws.inet_miswired, label="miswired",
        set_filter=lambda n: n.startswith("corner:"), dist_filter=lambda n: n in ("zero", "+eps", "-eps", "env_low", "env_high"), input_filter=lambda n: n in ("const_edge", "ramp_2V_per_ns_to_edge"),
    )
    out["matrix"] = {"n_runs": mm["totals"]["n_runs"], "n_violating_crossing_by_bound": mm["totals"]["viol_cross"], "n_violating_persistence": mm["totals"]["viol_persist"], "n_violating_safe_domain": mm["totals"]["viol_safe"], "per_polarity": mm["per_polarity"], "note": "same harness and checks as task 3, miswired law, corners x {C_min, C_max} x 6 initial states x 5 disturbances x 2 inputs"}
    return out, traj


def _stationary(F, th, u, w, lo, hi):
    f = lambda v: float(laws.inet_formal(u, v, *th)) + w  # noqa: E731
    return brentq(f, lo, hi, xtol=1e-14, rtol=1e-14)


def control_disturbance(D: Design, cfg: dict, worst_codes: dict, barrier_true: dict, jobs: int) -> tuple[dict, dict]:
    """(iv) Disturbance allowances that destroy the current margin."""
    F = float_design(D)
    out, traj = {}, {}
    cf = closed_form(D)
    order = sorted(("I_up(V_OH)", "I_dn(V_OL)", "R_hiP", "R_hiN", "R_loN", "R_loP"), key=lambda k: cf[k])
    out["certificate_limits"] = {
        "margins_sorted_uA": [{"margin": k, "value": dec(cf[k])} for k in order],
        "largest_eps_the_certificate_accepts": f"any eps < {dec(cf[order[0]])} uA (first to fail: {order[0]})",
    }

    # --- rise: smallest eps with a stationary point at or below V_OH -------
    codes, Cn = corner_array(D)
    vgrid = np.linspace(F.Vlo, F.VOH, 14501)
    mins = [float(laws.inet_formal(F.VIL, vgrid, *th).min()) for th in Cn]
    eps_crit_up_num = min(mins)
    eps_crit_up = I_up(D, D.VOH)
    thL = [float(x) for x in corner_by_code(D, worst_codes["L"])]
    runs = []
    for factor in (Fraction(1), Fraction(101, 100), Fraction(105, 100), Fraction(3, 2)):
        e = eps_crit_up * factor
        D2 = D.with_eps(e)
        ef = float(e)
        r = _sample(laws.inet_formal, thL, F.C_hi, F.Vlo, F.VIL, -ef, 120.0, n=481, Vth=F.VOH, sgn=1)
        vs = None
        try:
            vs = _stationary(F, thL, F.VIL, -ef, F.Vlo - 1.0, F.VOH + 1e-12)
        except ValueError:
            pass
        runs.append({
            "eps_uA": dec(e), "eps_over_eps_crit": dec(factor), "admissible": is_admissible(D2), "failed_conditions": [c.id for c in admissibility(D2) if not c.holds],
            "stationary_point_V": vs, "stationary_minus_V_OH_V": None if vs is None else vs - F.VOH,
            "v_final_after_120ns_V": r["v_final"], "v_final_minus_V_OH_V": r["v_final"] - F.VOH, "ever_reached_V_OH_numerically": r["t_cross"] is not None,
            "vmin_V": r["vmin"], "left_safe_domain": bool(r["vmin"] < F.Vlo - 1e-9),
            "decoded_final": decode_f(r["v_final"], F),
            "note": "KNIFE EDGE: the stationary point is V_OH itself; the exact solution approaches it but never reaches it, which float64 cannot resolve" if factor == 1 else "stuck strictly below V_OH: guarantee 2 fails for every deadline",
        })
        traj[f"iv_rise_eps_x{float(factor):g}"] = (r["t"], r["v"])
    out["rise"] = {
        "smallest_eps_with_stationary_point_at_or_below_V_OH_uA": frac_record(eps_crit_up),
        "numerical_min_pullup_over_grid_uA": eps_crit_up_num,
        "worst_corner": worst_codes["L"], "u": F.VIL, "w": "-eps'", "C_fF": F.C_hi, "v0": F.Vlo,
        "runs": runs,
        "sharpness": "at this corner the pull-up at V_OH equals I_up(V_OH) exactly, so eps < I_up(V_OH) is necessary as well as sufficient for guarantee 2 in this design",
    }

    # --- fall ---------------------------------------------------------------
    eps_crit_dn = I_dn(D, D.VOL)
    thH = [float(x) for x in corner_by_code(D, worst_codes["H"])]
    runs = []
    for factor in (Fraction(105, 100),):
        e = eps_crit_dn * factor
        ef = float(e)
        r = _sample(laws.inet_formal, thH, F.C_hi, F.Vhi, F.VIH, ef, 120.0, n=481, Vth=F.VOL, sgn=-1)
        vs = _stationary(F, thH, F.VIH, ef, F.VOL - 1e-12, F.Vhi + 1.0)
        runs.append({"eps_uA": dec(e), "eps_over_eps_crit": dec(factor), "admissible": is_admissible(D.with_eps(e)), "stationary_point_V": vs, "stationary_minus_V_OL_V": vs - F.VOL, "v_final_after_120ns_V": r["v_final"], "ever_reached_V_OL_numerically": r["t_cross"] is not None, "decoded_final": decode_f(r["v_final"], F)})
        traj[f"iv_fall_eps_x{float(factor):g}"] = (r["t"], r["v"])
    out["fall"] = {"smallest_eps_with_stationary_point_at_or_above_V_OL_uA": frac_record(eps_crit_dn), "worst_corner": worst_codes["H"], "runs": runs}

    # --- barriers -----------------------------------------------------------
    bars = {}
    for side in ("lo", "hi"):
        info = barrier_true[side]
        crit = Fraction(info["min_inward_current_uA"]["fraction"])
        u = float(Fraction(info["argmin"]["u"]))
        th = [float(Fraction(info["argmin"]["theta"][k])) for k in THETA_KEYS]
        e = crit * Fraction(105, 100)
        ef = float(e)
        v0, w = (F.Vlo, -ef) if side == "lo" else (F.Vhi, ef)
        r = _sample(laws.inet_formal, th, F.C_lo, v0, u, w, 30.0, n=301)
        vs = _stationary(F, th, u, w, F.Vlo - 2.0, F.Vhi + 2.0)
        bars[side] = {
            "model_min_inward_current_at_boundary_uA": dec(crit), "certificate_bound_uA": info["claimed_bound_uA"]["decimal"],
            "u_V": u, "theta": dict(zip(THETA_KEYS, th)), "eps_used_uA": dec(e), "admissible": is_admissible(D.with_eps(e)),
            "v0_V": v0, "w_uA": w, "C_fF": F.C_lo, "vmin_V": r["vmin"], "vmax_V": r["vmax"], "v_final_V": r["v_final"], "stationary_point_V": vs,
            "left_safe_domain": bool(r["vmin"] < F.Vlo - 1e-9 or r["vmax"] > F.Vhi + 1e-9), "excursion_beyond_boundary_V": (F.Vlo - r["vmin"]) if side == "lo" else (r["vmax"] - F.Vhi),
        }
        traj[f"iv_barrier_{side}"] = (r["t"], r["v"])
    out["barriers"] = bars

    # --- in between: precondition fails, no failing trajectory found --------
    mid = {}
    for e in cfg["eps_between"]:
        e = Fraction(e)
        D2 = D.with_eps(e)
        fails = [c.id for c in admissibility(D2) if not c.holds]
        t_up, t_dn = tau_up(D2), tau_dn(D2)
        mm = T.run_matrix(D2, cfg, jobs=jobs, label=f"eps={dec(e)}", set_filter=lambda n: n.startswith("corner:"), dist_filter=lambda n: n in ("+eps", "-eps", "adv_oppose", "adv_outward", "env_low", "env_high"))
        mid[dec(e)] = {"admissible": is_admissible(D2), "failed_conditions": fails, "tau_up_ns": float(t_up), "tau_dn_ns": float(t_dn), "n_runs": mm["totals"]["n_runs"], "violations": {k: v for k, v in mm["totals"].items() if k != "n_runs"}, "max_ratio": {p: mm["per_polarity"][p]["max_ratio"] for p in ("L", "H")}, "min_safe_margin_after_t0_V": {p: min(mm["per_polarity"][p]["min_lo_margin_later"], mm["per_polarity"][p]["min_hi_margin_later"]) for p in ("L", "H")}}
    out["between_certificate_and_model_limits"] = {"runs": mid, "reading": "the certificate rejects these eps (barrier margins), yet no violating trajectory was found in the reduced matrix: a failed sufficient precondition, not a demonstrated failure (finite evidence)"}
    return out, traj


def run(D: Design, cfg: dict, worst_codes: dict, brackets: dict, barrier_true: dict, jobs: int) -> tuple[dict, dict]:
    res, traj = {}, {}
    for key, (r, t) in (
        ("i_invalid_parameter_bounds", control_invalid_bounds(D, worst_codes)),
        ("ii_insufficient_observation_time", control_observation_time(D, worst_codes, brackets)),
        ("iii_miswired_transistor_roles", control_miswired(D, cfg, jobs)),
        ("iv_disturbance_destroys_margin", control_disturbance(D, cfg, worst_codes, barrier_true, jobs)),
    ):
        res[key] = r
        traj.update(t)
    return res, traj
