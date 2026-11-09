"""Task 5: are the reported crossing times converged?

A. Autonomous worst cases (rise, fall): the crossing time has an independent
   reference (quadrature, bracketed by exact rational Riemann sums). Sweep
   solver tolerance for five scipy methods and the step size of the fixed-step
   RK4 (linear vs cubic-Hermite event location).
B. Non-autonomous cases (ramp + sinusoid, random PWL input and disturbance,
   state feedback): cross-method agreement at tight tolerance.
C. The production batch engine: a strided subset of the task-3 matrix is re-run
   at half the step; differences in every tracked statistic are reported.
"""
from __future__ import annotations

import math
import warnings

import numpy as np
from scipy.integrate import quad

from . import laws, signals
from . import trajectories as T
from .common import float_design
from .design import Design, corner_by_code, tau_dn, tau_up
from .sim import make_rhs, rk4_single, solve_ref
from .common import corner_array
from .worstcase import delay_quad, envelope_delay

METHODS = ("RK45", "DOP853", "Radau", "BDF", "LSODA")
RTOLS = (1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10, 1e-11, 1e-12)
DTS = (0.04, 0.02, 0.01, 0.005, 0.0025, 0.001, 0.0005, 0.00025)


def autonomous(D: Design, worst_codes: dict) -> dict:
    F = float_design(D)
    rows_tol, rows_dt = [], []
    refs = {}
    for pol, name in (("L", "rise"), ("H", "fall")):
        code = worst_codes[pol]
        th = [float(x) for x in corner_by_code(D, code)]
        Tref = delay_quad(F, th, pol)
        refs[name] = {"corner": code, "reference_quadrature_ns": Tref}
        tau = float(tau_up(D) if pol == "L" else tau_dn(D))
        t_end = 1.2 * tau
        if pol == "L":
            rhs = make_rhs(laws.inet_formal, th, F.C_hi, lambda t: F.VIL, lambda t: -F.eps)
            v0, Vth, sgn = F.Vlo, F.VOH, 1
        else:
            rhs = make_rhs(laws.inet_formal, th, F.C_hi, lambda t: F.VIH, lambda t: F.eps)
            v0, Vth, sgn = F.Vhi, F.VOL, -1
        for m in METHODS:
            for rt in RTOLS:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore")
                    try:
                        r = solve_ref(rhs, v0, t_end, method=m, rtol=rt, atol=rt * 1e-2, Vth=Vth, sgn=sgn)
                        rows_tol.append([name, m, rt, rt * 1e-2, r["t_cross"], r["t_cross"] - Tref, r["nfev"]])
                    except Exception as exc:  # retained: a solver that cannot meet the tolerance
                        rows_tol.append([name, m, rt, rt * 1e-2, float("nan"), float("nan"), f"FAILED: {type(exc).__name__}"])
        prev = {}
        for dt in DTS:
            for evk in ("linear", "hermite"):
                r = rk4_single(rhs, v0, math.ceil(t_end / dt) * dt, dt, Vth=Vth, sgn=sgn, event=evk)
                err = r["t_cross"] - Tref
                order = float("nan")
                if evk in prev and prev[evk][1] != 0 and err != 0:
                    order = math.log(abs(prev[evk][1] / err)) / math.log(prev[evk][0] / dt)
                prev[evk] = (dt, err)
                rows_dt.append([name, dt, evk, r["t_cross"], err, order])
    return {
        "reference": refs,
        "tolerance_sweep": {"header": ["transition", "method", "rtol", "atol", "t_cross_ns", "error_vs_quadrature_ns", "nfev"], "rows": rows_tol},
        "rk4_step_sweep": {"header": ["transition", "dt_ns", "event_location", "t_cross_ns", "error_vs_quadrature_ns", "observed_order"], "rows": rows_dt},
    }


def nonautonomous(D: Design, cfg: dict, worst_codes: dict) -> dict:
    """Three representative non-autonomous scenarios; reference = DOP853 at rtol 1e-13 with restarts at kinks."""
    F = float_design(D)
    dt = cfg["dt"]
    cases = []
    inL = {i["name"]: i for i in T.input_specs(F, "L", dt)}
    inH = {i["name"]: i for i in T.input_specs(F, "H", dt)}
    dspecs, _ = T.disturbance_table(F, F.eps, np.linspace(0, 12, 5))  # only the specs are used
    dmap = {d["name"]: d["spec"] for d in dspecs}
    thL = [float(x) for x in corner_by_code(D, worst_codes["L"])]
    thH = [float(x) for x in corner_by_code(D, worst_codes["H"])]
    cases.append({"name": "L / ramp 2 V/ns to edge / 10 GHz sinusoid / worst rise corner / C_max / v0 = V_OL", "pol": "L", "th": thL, "C": F.C_hi, "v0": F.VOL, "inp": inL["ramp_2V_per_ns_to_edge"], "w": dmap["sin_10GHz"], "fb": 0})
    cases.append({"name": "H / random PWL input / PWL(0.02 ns, extremes) disturbance / worst fall corner / C_max / v0 = V_hi", "pol": "H", "th": thH, "C": F.C_hi, "v0": F.Vhi, "inp": inH["wander_pwl"], "w": dmap["pwl_0.02ns_extremes"], "fb": 0})
    cases.append({"name": "L / const edge / adv_outward state feedback (discontinuous at mid-domain) / worst rise corner / C_max / v0 = V_lo", "pol": "L", "th": thL, "C": F.C_hi, "v0": F.Vlo, "inp": inL["const_edge"], "w": None, "fb": 2})
    cases.append({"name": "H / const edge / box_high (parameter point re-chosen every instant: slowest fall of the rev. 2 inclusion) / v0 = V_hi", "pol": "H", "th": None, "C": None, "v0": F.Vhi, "inp": inH["const_edge"], "w": None, "fb": 6})
    _codes, Cn = corner_array(D)
    rows = []
    for c in cases:
        pol = c["pol"]
        tau = float(tau_up(D) if pol == "L" else tau_dn(D))
        sgn, Vth = (1, F.VOH) if pol == "L" else (-1, F.VOL)
        s = c["inp"]["s"]
        t_end = math.ceil((s + 1.25 * tau + 0.5) / (2 * dt)) * (2 * dt)  # a multiple of every step size used below
        u_fun = signals.scalar(c["inp"]["spec"])
        w_fun = signals.scalar(c["w"]) if c["w"] is not None else None
        rhs = make_rhs(laws.inet_formal, c["th"], c["C"], u_fun, w_fun, fb=c["fb"], sgn=sgn, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi, box=Cn)
        breaks = signals.breakpoints(c["inp"]["spec"], t_end) + (signals.breakpoints(c["w"], t_end) if c["w"] is not None else [])
        if c["fb"] == 2:
            # piecewise-autonomous: the reference is a two-piece quadrature split at the switching voltage
            vmid = 0.5 * (F.Vlo + F.Vhi)
            f1 = lambda v: 1.0 / (float(laws.inet_formal(F.VIL, v, *c["th"])) - F.eps)  # noqa: E731
            f2 = lambda v: 1.0 / (float(laws.inet_formal(F.VIL, v, *c["th"])) + F.eps)  # noqa: E731
            kink = F.VIL + c["th"][4]
            tq = quad(f1, F.Vlo, vmid, epsabs=1e-14, epsrel=1e-13)[0]
            for lo_, hi_ in ((vmid, kink), (kink, F.VOH)) if vmid < kink < F.VOH else ((vmid, F.VOH),):
                tq += quad(f2, lo_, hi_, epsabs=1e-14, epsrel=1e-13)[0]
            ref = {"t_cross": s + c["C"] * tq, "v_final": float("nan")}
            rows.append([c["name"], "two-piece quadrature (reference)", ref["t_cross"] - s, 0.0, float("nan"), float("nan")])
        elif c["fb"] == 6:
            ref = {"t_cross": s + envelope_delay(F, Cn, "H"), "v_final": float("nan")}
            rows.append([c["name"], "quadrature of the pointwise-worst drive (reference)", ref["t_cross"] - s, 0.0, float("nan"), float("nan")])
        else:
            ref = solve_ref(rhs, c["v0"], t_end, method="DOP853", rtol=1e-13, atol=1e-15, breaks=breaks, Vth=Vth, sgn=sgn, t_from=s)
            rows.append([c["name"], "DOP853 rtol=1e-13 (reference)", ref["t_cross"] - s, 0.0, ref["v_final"], 0.0])
        for m, rt in (("DOP853", 1e-10), ("RK45", 1e-10), ("Radau", 1e-9), ("LSODA", 1e-10)):
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                try:
                    r = solve_ref(rhs, c["v0"], t_end, method=m, rtol=rt, atol=rt * 1e-2, breaks=breaks, Vth=Vth, sgn=sgn, t_from=s)
                except RuntimeError as exc:  # retained, not hidden: this solver gave up on this case
                    rows.append([c["name"], f"{m} rtol={rt:g}", f"SOLVER FAILED: {exc}", float("nan"), float("nan"), float("nan")])
                    continue
            rows.append([c["name"], f"{m} rtol={rt:g}", r["t_cross"] - s, r["t_cross"] - ref["t_cross"], r["v_final"], r["v_final"] - ref["v_final"]])
        for d in (2 * dt, dt, dt / 2):
            r = rk4_single(rhs, c["v0"], t_end, d, Vth=Vth, sgn=sgn, t_from=s)
            rows.append([c["name"], f"fixed-step RK4 dt={d:g} ns, Hermite event", r["t_cross"] - s, r["t_cross"] - ref["t_cross"], r["v_final"], r["v_final"] - ref["v_final"]])
    return {"header": ["case", "integrator", "delay_ns", "delay_minus_reference_ns", "v_final_V", "v_final_minus_reference_V"], "rows": rows}


def batch_halving(D: Design, cfg: dict, jobs: int) -> dict:
    """Production engine at dt versus dt/2 on a subset: all inputs x all disturbances x corners x {C_min, C_max} x {V_lo, V_hi}."""
    sel = dict(set_filter=lambda n: n.startswith("corner:") or n.startswith("box:"), v0_filter=lambda n: n in ("V_lo", "V_hi"))
    a = T.run_matrix(D, cfg, jobs=jobs, keep_raw=True, **sel)
    cfg2 = dict(cfg, dt=cfg["dt"] / 2)
    b = T.run_matrix(D, cfg2, jobs=jobs, keep_raw=True, **sel)
    rows = []
    overall = {"n_runs": 0, "max_abs_dt_cross_ns": 0.0, "max_abs_d_vmin_V": 0.0, "max_abs_d_vmax_V": 0.0, "max_abs_d_vfinal_V": 0.0, "max_abs_dt_cross_ns_time_only_disturbances": 0.0, "max_abs_dt_cross_ns_envelope_selections": 0.0, "max_abs_dt_cross_ns_discontinuous_feedback": 0.0}
    for ra, rb in zip(a["raw"], b["raw"]):
        m = ra["meta"]
        for di, dname in enumerate(m["dist_names"]):
            sel_d = m["d"] == di
            dtc = np.abs(ra["res"]["t_cross"][sel_d] - rb["res"]["t_cross"][sel_d])
            dvmin = np.abs(ra["res"]["vmin"][sel_d] - rb["res"]["vmin"][sel_d])
            dvmax = np.abs(ra["res"]["vmax"][sel_d] - rb["res"]["vmax"][sel_d])
            dvf = np.abs(ra["res"]["v_final"][sel_d] - rb["res"]["v_final"][sel_d])
            row = [m["pol"], m["input"], dname, int(sel_d.sum()), float(np.nanmax(dtc)), float(dvmin.max()), float(dvmax.max()), float(dvf.max())]
            rows.append(row)
            overall["n_runs"] += int(sel_d.sum())
            overall["max_abs_dt_cross_ns"] = max(overall["max_abs_dt_cross_ns"], row[4])
            overall["max_abs_d_vmin_V"] = max(overall["max_abs_d_vmin_V"], row[5])
            overall["max_abs_d_vmax_V"] = max(overall["max_abs_d_vmax_V"], row[6])
            overall["max_abs_d_vfinal_V"] = max(overall["max_abs_d_vfinal_V"], row[7])
            cls = "discontinuous_feedback" if dname in ("adv_oppose", "adv_outward") else ("envelope_selections" if dname in ("env_low", "env_high", "box_low", "box_high") else "time_only_disturbances")
            overall[f"max_abs_dt_cross_ns_{cls}"] = max(overall[f"max_abs_dt_cross_ns_{cls}"], row[4])
    overall["dt_ns"] = cfg["dt"]
    overall["dt_half_ns"] = cfg["dt"] / 2
    overall["violations_at_dt"] = a["totals"]
    overall["violations_at_dt_half"] = b["totals"]
    return {"header": ["polarity", "input", "disturbance", "n_runs", "max_abs_diff_t_cross_ns", "max_abs_diff_vmin_V", "max_abs_diff_vmax_V", "max_abs_diff_vfinal_V"], "rows": rows, "overall": overall}


def run(D: Design, cfg: dict, worst_codes: dict, jobs: int) -> dict:
    return {"autonomous": autonomous(D, worst_codes), "nonautonomous": nonautonomous(D, cfg, worst_codes), "batch_halving": batch_halving(D, cfg, jobs)}
