"""Task 8 (runnable part): model-form SENSITIVITY study.

This is NOT validation against a real device. The formal device law is perturbed
with textbook corrections, coded here from their standard formulas:

* channel-length modulation, the SPICE Level-1 factor (1 + lambda * |V_DS|);
* a smooth subthreshold tail, the EKV interpolation (2 n phi_t ln(1 + exp(x / (2 n phi_t))))^2
  in place of max(x, 0)^2, with phi_t = k_B T / q;
* (extra) gate-drain "Miller" feedthrough, (C + C_gd) v' = I_net + w + C_gd u'.

For each perturbation it reports, on a finite grid over the safe domain and relative to eps_I,
 (1a) the SANDWICH residual, the obligation of interface.md v1 (rev. 2): the distance of the
      perturbed current from the interval [min, max] of the formal current over the parameter
      box (the box member may differ from point to point);
 (1b) the fixed-theta residual |Delta I| of the superseded v0 obligation, for the same
      parameters and after re-fitting the formal parameters inside the box (kept because it
      documents why rev. 2 was needed);
 (2)  whether simulated trajectories of the perturbed model still satisfy the three guarantees
      with the formal tau bounds.

Every residual number below is a statistic of a finite sample. None is a bound.
"""
from __future__ import annotations

import functools
import math

import numpy as np
from scipy.optimize import minimize

from . import laws, signals
from . import trajectories as T
from .common import corner_array, float_design, rng_for
from .design import THETA_KEYS, Design, corner_by_code, tau_dn, tau_up
from .sim import Batch, half_step_times, run_batch

T_ROOM = 300.15


def perturbations(cfg: dict) -> list[dict]:
    out = [{"name": "formal (control)", "family": "control", "lam": 0.0, "n": None, "T": None}]
    for lam in cfg["lambdas"]:
        out.append({"name": f"CLM lambda={lam:g}/V", "family": "channel-length modulation", "lam": lam, "n": None, "T": None})
    for n, Tk in cfg["tails"]:
        out.append({"name": f"tail n={n:g}, T={Tk:g} K", "family": "subthreshold tail", "lam": 0.0, "n": n, "T": Tk})
    for lam, n, Tk in cfg["combined"]:
        out.append({"name": f"CLM lambda={lam:g}/V + tail n={n:g}, T={Tk:g} K", "family": "combined", "lam": lam, "n": n, "T": Tk})
    for p in out:
        p["s"] = 0.0 if p["n"] is None else 2.0 * p["n"] * laws.thermal_voltage(p["T"])
        p["law"] = functools.partial(laws.inet_perturbed, lam_n=p["lam"], lam_p=p["lam"], s_n=p["s"], s_p=p["s"])
    return out


def residual_stats(D: Design, pert: dict, cfg: dict) -> dict:
    F = float_design(D)
    codes, Cn = corner_array(D)
    g = np.arange(F.Vlo, F.Vhi + 1e-9, cfg["residual_step"])
    U, V = np.meshgrid(g, g, indexing="ij")
    valid = (U <= F.VIL) | (U >= F.VIH)
    best = (-1.0, None)
    best_valid = (-1.0, None)
    frac_over = 0.0
    for code, th in zip(codes, Cn):
        r = np.abs(pert["law"](U, V, *th) - laws.inet_formal(U, V, *th))
        i = np.unravel_index(int(r.argmax()), r.shape)
        if r[i] > best[0]:
            best = (float(r[i]), {"corner": code, "u": float(U[i]), "v": float(V[i])})
        rv = np.where(valid, r, -1.0)
        j = np.unravel_index(int(rv.argmax()), rv.shape)
        if rv[j] > best_valid[0]:
            best_valid = (float(rv[j]), {"corner": code, "u": float(U[j]), "v": float(V[j])})
        frac_over = max(frac_over, float((r > F.eps).mean()))
    return {
        "max_abs_residual_uA_same_theta": best[0], "at": best[1], "over_eps": best[0] / F.eps,
        "max_abs_residual_uA_same_theta_valid_inputs_only": best_valid[0], "at_valid": best_valid[1], "over_eps_valid": best_valid[0] / F.eps,
        "largest_fraction_of_grid_exceeding_eps_over_corners": frac_over,
        "grid": f"(u, v) in [V_lo, V_hi]^2, step {cfg['residual_step']:g} V, {g.size}x{g.size} points, 32 corners",
    }


def _box_envelope(F, U, V, corners_arr):
    lo = np.full(U.shape, np.inf)
    hi = np.full(U.shape, -np.inf)
    for th in corners_arr:
        I = laws.inet_formal(U, V, *th)
        np.minimum(lo, I, out=lo)
        np.maximum(hi, I, out=hi)
    return lo, hi


def sandwich_residual(D: Design, law, th_true, cfg: dict) -> dict:
    """Distance of the perturbed current J(u, v) (base parameters ``th_true``) from the tube
    [min_theta I_net, max_theta I_net] spanned by the box, on a grid over the safe domain.
    Two tubes: the whole box, and the box members at the device's own supply voltage."""
    F = float_design(D)
    _codes, Cn = corner_array(D)
    g = np.arange(F.Vlo, F.Vhi + 1e-9, cfg["residual_step"])
    U, V = np.meshgrid(g, g, indexing="ij")
    J = law(U, V, *th_true)
    out = {}
    same_vdd = np.array([[th_true[0], kn, kp, vtn, vtp] for kn in (F.kn_lo, F.kn_hi) for kp in (F.kp_lo, F.kp_hi) for vtn in (F.Vtn_lo, F.Vtn_hi) for vtp in (F.Vtp_lo, F.Vtp_hi)])
    for key, arr in (("whole_box", Cn), ("box_at_device_supply", same_vdd)):
        lo, hi = _box_envelope(F, U, V, arr)
        r = np.maximum(np.maximum(lo - J, J - hi), 0.0)
        r[r < 1e-9] = 0.0  # float noise where the perturbed current coincides with a tube edge
        i = np.unravel_index(int(r.argmax()), r.shape)
        out[key] = {"max_uA": float(r[i]), "over_eps": float(r[i]) / F.eps, "u": float(U[i]), "v": float(V[i]), "side": "inside" if r[i] == 0.0 else ("below the tube" if (lo - J)[i] > 0 else "above the tube"), "fraction_of_grid_outside": float((r > 0).mean())}
    return out


def clm_limit(D: Design, th_true, cfg: dict, level: float) -> dict:
    """Largest lambda (bisection on the same grid) for which the CLM-perturbed device with base
    ``th_true`` stays within ``level`` uA of the tube. Finite grid: an estimate, not a bound."""
    out = {}
    for key in ("whole_box", "box_at_device_supply"):
        f = lambda lam: sandwich_residual(D, functools.partial(laws.inet_perturbed, lam_n=lam, lam_p=lam), th_true, cfg)[key]["max_uA"]  # noqa: E731
        lo, hi = 0.0, 1.0
        if f(hi) <= level:
            out[key] = ">= 1"
            continue
        for _ in range(40):
            mid = 0.5 * (lo + hi)
            if f(mid) <= level:
                lo = mid
            else:
                hi = mid
        out[key] = lo
    return out


def best_fit_residual(D: Design, pert: dict, th_true, cfg: dict, tag: str) -> dict:
    """min over formal (kn, kp, Vtn, Vtp) in the box (VDD kept) of max |I_pert(.; th_true) - I_formal(.; th')| on a grid.
    Local search from several starts: the value reported is an upper bound on the grid min-max."""
    F = float_design(D)
    g = np.arange(F.Vlo, F.Vhi + 1e-9, cfg["fit_step"])
    U, V = np.meshgrid(g, g, indexing="ij")
    target = pert["law"](U, V, *th_true)
    lo = np.array([F.kn_lo, F.kp_lo, F.Vtn_lo, F.Vtp_lo])
    hi = np.array([F.kn_hi, F.kp_hi, F.Vtn_hi, F.Vtp_hi])

    def obj(x):
        p = lo + np.clip(x, 0, 1) * (hi - lo)
        return float(np.abs(target - laws.inet_formal(U, V, th_true[0], p[0], p[1], p[2], p[3])).max())

    rng = rng_for(tag)
    x_true = (np.array([th_true[1], th_true[2], th_true[3], th_true[4]]) - lo) / (hi - lo)
    starts = [x_true, np.full(4, 0.5)] + [rng.uniform(0, 1, 4) for _ in range(cfg["fit_random_starts"])]
    best = (math.inf, None)
    for x0 in starts:
        r = minimize(obj, x0, method="Nelder-Mead", bounds=[(0, 1)] * 4, options={"xatol": 1e-5, "fatol": 1e-7, "maxfev": 800})
        if r.fun < best[0]:
            best = (float(r.fun), lo + np.clip(r.x, 0, 1) * (hi - lo))
    return {"minmax_residual_uA_after_refit": best[0], "over_eps": best[0] / F.eps, "fits_inside_eps_on_this_grid": bool(best[0] <= F.eps), "refit": dict(zip(("kn", "kp", "Vtn", "Vtp"), [float(x) for x in best[1]])), "same_theta_residual_uA": obj(x_true)}


def miller_runs(D: Design, cfg: dict) -> dict:
    """(C + C_gd) v' = I_net + w + C_gd u'(t): full-swing input ramps of several durations.
    Integrated exactly in x = v - kappa*u (see sim.run_batch), so the input edge is not differentiated."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    dt = cfg["miller_dt"]
    taus = {"L": float(tau_up(D)), "H": float(tau_dn(D))}
    swing = F.VDD_hi
    rows = []
    for cgd in cfg["miller_cgd_fF"]:
        for t_ramp in cfg["miller_ramp_ns"]:
            slew = swing / t_ramp
            agg = {"n": 0, "viol_safe": 0, "viol_cross": 0, "viol_persist": 0, "max_above_Vhi": -math.inf, "max_below_Vlo": -math.inf, "max_ratio": -math.inf, "worst_above": "", "worst_below": ""}

            def describe(i, pol_, a_, c_, w_, v0k_):
                return f"input {'falling' if pol_ == 'L' else 'rising'}; corner {codes[a_[i]]}; C={[F.C_lo, F.C_hi][c_[i]]:g} fF; w={['0', '+eps', '-eps'][w_[i]]}; v0={['rest rail', 'V_lo', 'V_hi'][v0k_[i]]}"

            for pol in ("L", "H"):
                edge = F.VIL if pol == "L" else F.VIH
                sgn, Vth = (1, F.VOH) if pol == "L" else (-1, F.VOL)
                start_level = swing if pol == "L" else 0.0
                t0 = 0.2  # ramp starts here (on the grid); it ends at t0 + t_ramp (on the grid)
                s_true = t0 + t_ramp * abs(start_level - edge) / swing  # input reaches the band edge
                spec = {"kind": "ramp", "edge": edge, "slew": (-slew if pol == "L" else slew), "t_edge": s_true, "lo": 0.0, "hi": swing}
                tau = taus[pol]
                s_idx = int(math.ceil(s_true / dt - 1e-9))  # first grid time at which the input is valid
                N = int(math.ceil((s_true + 1.25 * tau + 0.5) / dt))
                U = signals.evaluate(spec, half_step_times(dt, N))
                a, c, w, v0k = np.meshgrid(np.arange(len(codes)), np.arange(2), np.arange(3), np.arange(3), indexing="ij")
                a, c, w, v0k = a.ravel(), c.ravel(), w.ravel(), v0k.ravel()
                # initial states: the rail the output would be resting at, and both ends of the safe domain
                rest = F.VDD_lo if pol == "H" else 0.0
                v0 = np.array([rest, F.Vlo, F.Vhi])[v0k]
                W = np.array([np.zeros(2 * N + 1), np.full(2 * N + 1, F.eps), np.full(2 * N + 1, -F.eps)])
                b = Batch(theta=Cn[a], C=np.array([F.C_lo, F.C_hi])[c], v0=v0, w_idx=w.astype(np.int64), fb=np.zeros(a.size, dtype=np.int8), U=U, W=W, dt=dt, N=N,
                          s_idx=s_idx, deadline_idx=int(math.ceil((s_idx * dt + tau) / dt - 1e-9)), sgn=sgn, Vth=Vth, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi,
                          law=laws.inet_formal, Cgd=cgd)
                r = run_batch(b)
                delay = r["t_cross"] - s_idx * dt
                agg["n"] += a.size
                agg["viol_safe"] += int(((r["vmin"] < F.Vlo - T.TOL_V) | (r["vmax"] > F.Vhi + T.TOL_V)).sum())
                agg["viol_cross"] += int((~(delay <= tau + T.TOL_T)).sum())
                agg["viol_persist"] += int((~(r["g_after_deadline"] >= -T.TOL_V)).sum())
                ia, ib = int((r["vmax"] - F.Vhi).argmax()), int((F.Vlo - r["vmin"]).argmax())
                if float(r["vmax"][ia] - F.Vhi) > agg["max_above_Vhi"]:
                    agg["max_above_Vhi"], agg["worst_above"] = float(r["vmax"][ia] - F.Vhi), describe(ia, pol, a, c, w, v0k)
                if float(F.Vlo - r["vmin"][ib]) > agg["max_below_Vlo"]:
                    agg["max_below_Vlo"], agg["worst_below"] = float(F.Vlo - r["vmin"][ib]), describe(ib, pol, a, c, w, v0k)
                agg["max_ratio"] = max(agg["max_ratio"], T._nanmax(delay / tau))
            rows.append([cgd, t_ramp, slew, cgd * slew, cgd * slew / F.eps, agg["n"], agg["viol_safe"], agg["viol_cross"], agg["viol_persist"], agg["max_above_Vhi"], agg["max_below_Vlo"], agg["max_ratio"], agg["worst_above"] if agg["max_above_Vhi"] > 0 else "", agg["worst_below"] if agg["max_below_Vlo"] > 0 else ""])
    return {
        "header": ["C_gd_fF", "input_ramp_duration_ns", "input_slew_V_per_ns", "equivalent_disturbance_Cgd*slew_uA", "equivalent_disturbance_over_eps", "n_runs", "n_viol_safe_domain", "n_viol_crossing_by_bound", "n_viol_persistence", "max_excursion_above_V_hi_V (<= 0: stayed inside)", "max_excursion_below_V_lo_V (<= 0: stayed inside)", "max_delay_over_tau", "retained_failing_case_above_V_hi", "retained_failing_case_below_V_lo"],
        "rows": rows,
        "setup": "full-swing input ramps 0 <-> VDD_max, 32 corners x {C_min, C_max} x w in {0, +eps, -eps} x v0 in {rest rail, V_lo, V_hi}; C_gd values are illustrative, not extracted from any process",
        "slew_limit_for_feedthrough_alone_to_fit_in_eps_V_per_ns": {f"C_gd={c:g} fF": F.eps / c for c in cfg["miller_cgd_fF"]},
    }


def run(D: Design, cfg: dict, worst_codes: dict, jobs: int) -> dict:
    F = float_design(D)
    perts = perturbations(cfg)
    nominal = [0.5 * (F.lo(k) + F.hi(k)) for k in THETA_KEYS]
    trues = {"nominal": nominal, f"worst rise corner {worst_codes['L']}": [float(x) for x in corner_by_code(D, worst_codes["L"])], f"worst fall corner {worst_codes['H']}": [float(x) for x in corner_by_code(D, worst_codes["H"])]}
    rows_res, rows_fit, rows_traj, rows_sw = [], [], [], []
    for p in perts:
        for tname, tht in trues.items():
            sw = sandwich_residual(D, p["law"], tht, cfg)
            rows_sw.append([p["name"], p["family"], tname, sw["whole_box"]["max_uA"], sw["whole_box"]["over_eps"], sw["whole_box"]["side"], sw["whole_box"]["u"], sw["whole_box"]["v"], sw["whole_box"]["fraction_of_grid_outside"],
                            sw["box_at_device_supply"]["max_uA"], sw["box_at_device_supply"]["over_eps"], sw["box_at_device_supply"]["side"], sw["box_at_device_supply"]["u"], sw["box_at_device_supply"]["v"], sw["box_at_device_supply"]["fraction_of_grid_outside"]])
        rs = residual_stats(D, p, cfg)
        rows_res.append([p["name"], p["family"], p["lam"], p["n"] if p["n"] is not None else "", p["T"] if p["T"] is not None else "", rs["max_abs_residual_uA_same_theta"], rs["over_eps"], rs["at"]["corner"], rs["at"]["u"], rs["at"]["v"], rs["max_abs_residual_uA_same_theta_valid_inputs_only"], rs["over_eps_valid"], rs["largest_fraction_of_grid_exceeding_eps_over_corners"]])
        for tname, tht in trues.items():
            bf = best_fit_residual(D, p, tht, cfg, f"sens/fit/{p['name']}/{tname}")
            rows_fit.append([p["name"], tname, bf["same_theta_residual_uA"], bf["minmax_residual_uA_after_refit"], bf["over_eps"], bf["fits_inside_eps_on_this_grid"], bf["refit"]["kn"], bf["refit"]["kp"], bf["refit"]["Vtn"], bf["refit"]["Vtp"]])
        for mode, dfilt in (("model form alone (w = 0)", lambda n: n == "zero"), ("model form + full disturbance allowance", lambda n: n in ("+eps", "-eps", "adv_oppose", "adv_outward", "env_low", "env_high"))):
            mm = T.run_matrix(D, cfg, jobs=jobs, law=p["law"], label=p["name"], set_filter=lambda n: n.startswith("corner:"), dist_filter=dfilt)
            t = mm["totals"]
            pp = mm["per_polarity"]
            rows_traj.append([p["name"], mode, t["n_runs"], t["viol_safe"], t["viol_cross"], t["viol_persist"], pp["L"]["max_ratio"], pp["H"]["max_ratio"], min(pp["L"]["min_lo_margin"], pp["H"]["min_lo_margin"]), min(pp["L"]["min_hi_margin"], pp["H"]["min_hi_margin"])])
    clm = {"nominal device, residual 0": clm_limit(D, nominal, cfg, 1e-9), "nominal device, residual <= eps_I": clm_limit(D, nominal, cfg, F.eps)}
    return {
        "label": "SENSITIVITY STUDY, NOT VALIDATION. Finite grids and finite run sets; no number here is a bound.",
        "sandwich": {"header": ["perturbation", "family", "base_theta", "max_residual_uA(whole box)", "over_eps(whole box)", "side(whole box)", "u_V", "v_V", "fraction_of_grid_outside(whole box)", "max_residual_uA(box at device supply)", "over_eps(box at device supply)", "side(box at device supply)", "u_V_2", "v_V_2", "fraction_of_grid_outside(box at device supply)"], "rows": rows_sw,
                     "note": "obligation of interface.md v1 (rev. 2): the other model's current must lie between two box members up to eps_m, with eps_m + eps_w <= eps_I. A base device at a corner of the box has no room on that side, so any correction that increases its current puts it outside; the nominal device has room."},
        "largest_lambda_inside_tube": clm,
        "residual": {"header": ["perturbation", "family", "lambda_per_V", "n", "T_K", "max_abs_dI_uA(same theta)", "over_eps", "corner", "u_V", "v_V", "max_abs_dI_uA(valid inputs only)", "over_eps(valid inputs only)", "largest_fraction_of_grid_with_abs_dI_gt_eps"], "rows": rows_res},
        "refit": {"header": ["perturbation", "true_theta", "max_abs_dI_uA(same theta, fit grid)", "minmax_abs_dI_uA_after_refit_in_box", "over_eps", "fits_inside_eps_on_this_grid", "kn_fit", "kp_fit", "Vtn_fit", "Vtp_fit"], "rows": rows_fit},
        "trajectories": {"header": ["perturbation", "mode", "n_runs", "n_viol_safe_domain", "n_viol_crossing_by_bound", "n_viol_persistence", "max_delay_over_tau_rise", "max_delay_over_tau_fall", "min_vmin_minus_Vlo_V", "min_Vhi_minus_vmax_V"], "rows": rows_traj},
        "miller": miller_runs(D, cfg),
        "constants": {"k_B": laws.K_BOLTZMANN, "q": laws.Q_ELECTRON, "phi_t(300.15 K)_V": laws.thermal_voltage(T_ROOM)},
    }
