"""Task 7: behaviour near the operating-domain boundary.

(a) inputs exactly at V_IL / V_IH and progressively inside the invalid region;
(b) initial states exactly at V_lo / V_hi with the disturbance pushing outward, for every held input level;
(c) mid-rail inputs held for a long time, decoded three-valued.
"""
from __future__ import annotations

import math

import numpy as np
from scipy.optimize import brentq

from . import laws
from .common import corner_array, float_design
from .controls import decode_f
from .design import THETA_KEYS, Design, decode, tau_dn, tau_up
from .sim import Batch, half_step_times, run_batch
from .worstcase import envelope_delay


def stationary(F, th, u: float, w: float) -> float:
    """A stationary point of c v' = I_net(u, v) + w inside the safe domain (unique unless I_net + w
    vanishes on an interval, which happens only at the exact switching threshold with w = 0)."""
    f = lambda v: float(laws.inet_formal(u, v, *th)) + w  # noqa: E731
    a, b = F.Vlo, F.Vhi
    fa, fb = f(a), f(b)
    if fa <= 0:
        return a
    if fb >= 0:
        return b
    return brentq(f, a, b, xtol=1e-13, rtol=1e-13)


def edge_sweep(D: Design, cfg: dict) -> dict:
    """Worst case over the 32 corners as the held input moves from the band edge into the invalid region."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    taus = {"L": float(tau_up(D)), "H": float(tau_dn(D))}
    rows = []
    deltas = np.round(np.arange(0.0, cfg["edge_sweep_max"] + 1e-9, cfg["edge_sweep_step"]), 6)
    summary = {}
    for pol, name in (("L", "low"), ("H", "high")):
        edge = F.VIL if pol == "L" else F.VIH
        sg = 1.0 if pol == "L" else -1.0
        w_against = -F.eps if pol == "L" else F.eps
        thr = F.VOH if pol == "L" else F.VOL

        def worst_margin(u):
            # worst-corner drive at the output threshold (the drive is monotone in v, so this decides whether the output gets there)
            if pol == "L":
                return min(float(laws.inet_formal(u, thr, *th)) - F.eps for th in Cn)
            return min(-float(laws.inet_formal(u, thr, *th)) - F.eps for th in Cn)

        def worst_delay(u):
            # worst case of the rev. 2 inclusion (parameter point free at each instant)
            return envelope_delay(F, Cn, pol, u=u)

        for d in deltas:
            u = edge + sg * d
            Tw = worst_delay(u)
            vs = [stationary(F, th, u, w_against) for th in Cn]
            v_worst = min(vs) if pol == "L" else max(vs)
            rows.append([name, float(d), u, worst_margin(u), Tw, Tw / taus[pol], v_worst, decode_f(v_worst, F), "inside valid band (edge)" if d == 0 else "INVALID input"])
        # critical offsets by bisection
        lo, hi = 0.0, cfg["edge_sweep_max"]
        if worst_margin(edge + sg * hi) < 0:
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if worst_margin(edge + sg * mid) > 0:
                    lo = mid
                else:
                    hi = mid
            d_stuck = 0.5 * (lo + hi)
        else:
            d_stuck = None
        lo, hi = 0.0, d_stuck if d_stuck is not None else cfg["edge_sweep_max"]
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if worst_delay(edge + sg * mid) <= taus[pol]:
                lo = mid
            else:
                hi = mid
        d_tau = 0.5 * (lo + hi)
        summary[name] = {
            "band_edge_V": edge,
            "offset_at_which_worst_case_delay_first_exceeds_tau_V": d_tau,
            "input_level_there_V": edge + sg * d_tau,
            "offset_at_which_worst_corner_gets_stuck_short_of_threshold_V": d_stuck,
            "input_level_there_V_stuck": None if d_stuck is None else edge + sg * d_stuck,
            "reading": "between the band edge and the first offset the model still meets the timing bound although the theorem makes no claim there; beyond the second offset an admissible trajectory never produces a valid output",
        }
    return {"header": ["input_side", "offset_into_invalid_region_V", "u_V", "worst_corner_drive_at_output_threshold_minus_eps_uA", "worst_case_delay_ns", "delay_over_tau", "worst_settled_output_V", "decoded_worst_settled_output", "input_status"], "rows": rows, "summary": summary}


def edge_simulation_check(D: Design, cfg: dict) -> dict:
    """Simulated trajectories for inputs exactly at the band edge and slightly inside the invalid
    region: the slowest trajectory of the rev. 2 inclusion (box_low / box_high selection, start
    at the far end of the safe domain), compared with the quadrature values used in the sweep."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    dt = cfg["dt"]
    rows = []
    for pol, name in (("L", "low"), ("H", "high")):
        tau = float(tau_up(D) if pol == "L" else tau_dn(D))
        edge, sg = (F.VIL, 1.0) if pol == "L" else (F.VIH, -1.0)
        offs = np.array(cfg["edge_sim_offsets"])
        us = edge + sg * offs
        n = offs.size
        N = int(round(cfg["edge_sim_hold_ns"] / dt))
        b = Batch(
            theta=np.full((n, 5), np.nan), C=np.full(n, np.nan), v0=np.full(n, F.Vlo if pol == "L" else F.Vhi), w_idx=np.zeros(n, dtype=np.int64), fb=np.full(n, 5 if pol == "L" else 6, dtype=np.int8),
            U=np.zeros(2 * N + 1), W=np.zeros((1, 2 * N + 1)), dt=dt, N=N, s_idx=0, deadline_idx=int(math.ceil(tau / dt - 1e-9)), sgn=1 if pol == "L" else -1, Vth=F.VOH if pol == "L" else F.VOL,
            eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi, law=laws.inet_formal, box=Cn, u_row=us,
        )
        r = run_batch(b)
        for oi, off in enumerate(offs):
            tq = envelope_delay(F, Cn, pol, u=float(us[oi]))
            tsim = float(r["t_cross"][oi])
            rows.append([name, float(off), float(us[oi]), tsim, tq, tsim - tq if math.isfinite(tq) else float("nan"), tsim / tau, bool(tsim <= tau), float(r["vmin"][oi]), float(r["vmax"][oi]), bool(r["g_after_deadline"][oi] >= 0)])
    return {"header": ["input_side", "offset_into_invalid_region_V", "u_V", "worst_simulated_delay_ns", "worst_quadrature_delay_ns", "simulation_minus_quadrature_ns", "worst_delay_over_tau", "within_tau", "min_v_V", "max_v_V", "valid_at_every_step_from_tau"],
            "rows": rows, "hold_ns": cfg["edge_sim_hold_ns"], "note": "offset 0 is the band edge itself (inside the claim); positive offsets are OUTSIDE the claim"}


def barrier_stress(D: Design, cfg: dict) -> dict:
    """Start exactly on the domain boundary with everything pushing outward, for every held input
    level: (i) each corner with w = +-eps at C_min; (ii) the box_high / box_low selections of the
    rev. 2 inclusion, which bound every admissible trajectory for that input."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    us = np.round(np.arange(cfg["barrier_u_lo"], cfg["barrier_u_hi"] + 1e-9, cfg["barrier_u_step"]), 6)
    U, TH, S = np.meshgrid(np.arange(us.size), np.arange(len(codes)), np.arange(2), indexing="ij")
    U, TH, S = U.ravel(), TH.ravel(), S.ravel()
    nc = U.size
    UB, SB = np.meshgrid(np.arange(us.size), np.arange(2), indexing="ij")
    UB, SB = UB.ravel(), SB.ravel()
    nb = UB.size
    dt = cfg["dt"]
    N = int(round(cfg["barrier_hold_ns"] / dt))
    W = np.array([np.full(2 * N + 1, F.eps), np.full(2 * N + 1, -F.eps)])
    b = Batch(
        theta=np.vstack([Cn[TH], np.full((nb, 5), np.nan)]), C=np.concatenate([np.full(nc, F.C_lo), np.full(nb, np.nan)]),
        v0=np.concatenate([np.where(S == 0, F.Vhi, F.Vlo), np.where(SB == 0, F.Vhi, F.Vlo)]), w_idx=np.concatenate([S, np.zeros(nb, dtype=S.dtype)]).astype(np.int64),
        fb=np.concatenate([np.zeros(nc, dtype=np.int8), np.where(SB == 0, 6, 5).astype(np.int8)]),
        U=np.zeros(2 * N + 1), W=W, dt=dt, N=N, s_idx=0, deadline_idx=-1, sgn=1, Vth=F.VOH, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi,
        law=laws.inet_formal, box=Cn, u_row=np.concatenate([us[U], us[UB]]),
    )
    r = run_batch(b)
    side = np.concatenate([S, SB])
    is_box = np.concatenate([np.zeros(nc, dtype=bool), np.ones(nb, dtype=bool)])
    hi_rows, lo_rows = side == 0, side == 1
    u_all = np.concatenate([us[U], us[UB]])
    corner_all = np.array([codes[i] for i in TH] + ["box (any theta per instant)"] * nb)
    # analytic extreme stationary points: how much of the safe domain does the model actually use?
    v_plus = np.array([[stationary(F, th, float(u), F.eps) for th in Cn] for u in us])
    v_minus = np.array([[stationary(F, th, float(u), -F.eps) for th in Cn] for u in us])
    ip, im = np.unravel_index(int(v_plus.argmax()), v_plus.shape), np.unravel_index(int(v_minus.argmin()), v_minus.shape)
    i_hi = int(np.argmax(np.where(hi_rows, r["vmax_later"], -np.inf)))
    i_lo = int(np.argmin(np.where(lo_rows, r["vmin_later"], np.inf)))
    return {
        "n_runs": int(nc + nb), "n_runs_fixed_corner": int(nc), "n_runs_box_envelope": int(nb), "u_grid": [float(us[0]), float(us[-1]), cfg["barrier_u_step"]], "n_corners": len(codes), "C_fF_fixed_corner_runs": F.C_lo, "hold_ns": cfg["barrier_hold_ns"], "dt_ns": dt,
        "start_at_V_hi_pushing_up": {
            "max_v_over_all_runs_V": float(r["vmax"][hi_rows].max()), "max_v_after_t0_V": float(r["vmax_later"][hi_rows].max()),
            "min_distance_below_V_hi_after_one_step_V": float(F.Vhi - r["vmax_later"][hi_rows].max()),
            "tightest_run": {"u_V": float(u_all[i_hi]), "selection": str(corner_all[i_hi])}, "n_runs_exceeding_V_hi": int((r["vmax"][hi_rows] > F.Vhi + 1e-12).sum()),
            "box_envelope_runs_exceeding_V_hi": int((r["vmax"][hi_rows & is_box] > F.Vhi + 1e-12).sum()),
        },
        "start_at_V_lo_pushing_down": {
            "min_v_over_all_runs_V": float(r["vmin"][lo_rows].min()), "min_v_after_t0_V": float(r["vmin_later"][lo_rows].min()),
            "min_distance_above_V_lo_after_one_step_V": float(r["vmin_later"][lo_rows].min() - F.Vlo),
            "tightest_run": {"u_V": float(u_all[i_lo]), "selection": str(corner_all[i_lo])}, "n_runs_below_V_lo": int((r["vmin"][lo_rows] < F.Vlo - 1e-12).sum()),
            "box_envelope_runs_below_V_lo": int((r["vmin"][lo_rows & is_box] < F.Vlo - 1e-12).sum()),
        },
        "extreme_stationary_points": {
            "highest_stationary_output_with_w=+eps_V": float(v_plus.max()), "at_u_V": float(us[ip[0]]), "at_corner": codes[ip[1]], "headroom_to_V_hi_V": float(F.Vhi - v_plus.max()),
            "lowest_stationary_output_with_w=-eps_V": float(v_minus.min()), "at_u_V_low": float(us[im[0]]), "at_corner_low": codes[im[1]], "headroom_to_V_lo_V": float(v_minus.min() - F.Vlo),
            "note": "over the u grid and the 32 corners (the box extremes are attained at corners); every trajectory started between these two values stays between them (scalar comparison), so at this eps the model uses only this part of [V_lo, V_hi]",
        },
    }


def supply_relative(D: Design, cfg: dict) -> dict:
    """interface.md v1 (rev. 3): for a run at ONE supply value V0 the invariant interval is claimed
    to be [V_lo, V0 + (V_hi - VDD_max)], under the extra condition eps < R_hiN'. Checked here by
    (1) running the admissibility checker on the restricted record for a grid of V0, (2) the exact
    minimum restoring current at the supply-relative top over inputs and the remaining parameters,
    (3) simulation from the top with everything pushing up."""
    from fractions import Fraction

    from .design import R_hiN, R_hiN_prime, R_hiP, R_loN, R_loP, admissibility, at_supply, corners, dec, is_admissible
    from .margins import IntModel

    F = float_design(D)
    delta = D.Vhi - D.hi("VDD")
    step = Fraction(cfg["supply_step"])
    n = int((D.hi("VDD") - D.lo("VDD")) / step)
    rows = []
    worst = None
    for i in range(n + 1):
        V0 = D.lo("VDD") + i * step
        D0 = at_supply(D, V0)
        im = IntModel(D0)
        u = im.V(Fraction(-3)) + im.V(Fraction(1, 1000)) * np.arange(0, 8001, dtype=np.int64)
        top = np.int64(im.V(D0.Vhi))
        best = None
        for c in corners(D0):
            inward = -im.inet(u, top, im.theta(c["theta"]))
            k = int(inward.argmin())
            if best is None or int(inward[k]) < best[0]:
                best = (int(inward[k]), c["code"], int(u[k]))
        tmin = im.I(best[0])
        fails = [c.id for c in admissibility(D0) if not c.holds]
        rows.append([dec(V0), dec(D0.Vhi), is_admissible(D0), ";".join(fails), dec(min(R_hiP(D0), R_hiN(D0))), dec(min(R_loN(D0), R_loP(D0))), dec(tmin), dec(Fraction(best[2], im.Sv)), best[1], float(tau_up(D0)), float(tau_dn(D0))])
        if worst is None or tmin < worst[0]:
            worst = (tmin, V0, Fraction(best[2], im.Sv), best[1])
    # simulation from the supply-relative top
    sims = {}
    us = np.round(np.arange(cfg["barrier_u_lo"], cfg["barrier_u_hi"] + 1e-9, cfg["barrier_u_step"]), 6)
    dt = cfg["dt"]
    N = int(round(cfg["barrier_hold_ns"] / dt))
    for V0 in (D.lo("VDD"), (D.lo("VDD") + D.hi("VDD")) / 2, D.hi("VDD")):
        D0 = at_supply(D, V0)
        F0 = float_design(D0)
        codes0, C0 = corner_array(D0)
        U, TH = np.meshgrid(np.arange(us.size), np.arange(len(codes0)), indexing="ij")
        U, TH = U.ravel(), TH.ravel()
        nc, nb = U.size, us.size
        b = Batch(
            theta=np.vstack([C0[TH], np.full((nb, 5), np.nan)]), C=np.concatenate([np.full(nc, F.C_lo), np.full(nb, np.nan)]), v0=np.full(nc + nb, F0.Vhi),
            w_idx=np.zeros(nc + nb, dtype=np.int64), fb=np.concatenate([np.zeros(nc, dtype=np.int8), np.full(nb, 6, dtype=np.int8)]),
            U=np.zeros(2 * N + 1), W=np.full((1, 2 * N + 1), F.eps), dt=dt, N=N, s_idx=0, deadline_idx=-1, sgn=1, Vth=F.VOH, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F0.Vlo, Vhi=F0.Vhi,
            law=laws.inet_formal, box=C0, u_row=np.concatenate([us[U], us]),
        )
        r = run_batch(b)
        sims[dec(V0)] = {"top_V": F0.Vhi, "n_runs": int(nc + nb), "max_v_over_all_runs_V": float(r["vmax"].max()), "n_runs_exceeding_top": int((r["vmax"] > F0.Vhi + 1e-12).sum()), "max_v_after_t0_minus_top_V": float(r["vmax_later"].max() - F0.Vhi), "min_v_V": float(r["vmin"].min())}
    return {
        "claim": "for a run at one supply V0 in [VDD_min, VDD_max]: v stays in [V_lo, V0 + (V_hi - VDD_max)], provided eps < R_hiN'",
        "delta_V": dec(delta),
        "R_hiN_prime_uA": dec(R_hiN_prime(D)), "eps_lt_R_hiN_prime": bool(D.eps < R_hiN_prime(D)),
        "per_supply": {"header": ["V0_V", "top_V", "restricted_record_admissible (D's checker)", "failed_conditions", "min(R_hiP, R_hiN)_uA", "min(R_loN, R_loP)_uA", "model_min_restoring_current_at_top_uA (exact, u grid 1 mV, corners)", "at_u_V", "at_corner", "tau_up_restricted_ns", "tau_dn_restricted_ns"], "rows": rows},
        "n_supply_values": n + 1, "all_restricted_records_admissible": all(r[2] for r in rows),
        "smallest_model_restoring_current_at_supply_relative_top": {"uA": dec(worst[0]), "V0_V": dec(worst[1]), "u_V": dec(worst[2]), "corner": worst[3]},
        "restricted_deadlines_no_larger": bool(max(r[9] for r in rows) <= float(tau_up(D)) + 1e-12 and max(r[10] for r in rows) <= float(tau_dn(D)) + 1e-12),
        "simulation_from_the_supply_relative_top (w = +eps at C_min for each corner, and the box_high selection)": sims,
    }


def switching_threshold(th) -> float:
    """u_M where the two saturation currents balance (the vertical part of the lambda = 0 transfer curve)."""
    VDD, kn, kp, Vtn, Vtp = th
    r = math.sqrt(kp / kn)
    return (Vtn + r * (VDD - Vtp)) / (1.0 + r)


def midrail_hold(D: Design, cfg: dict) -> dict:
    """Mid-rail (invalid) inputs held for a long time; settled outputs decoded three-valued."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    nominal = np.array([0.5 * (F.lo(k) + F.hi(k)) for k in THETA_KEYS])
    thetas = np.vstack([nominal[None, :], Cn])
    tnames = ["nominal"] + codes
    u_fixed = np.round(np.arange(F.VIL + 0.05, F.VIH - 1e-9, 0.05), 6)
    ws = np.array([0.0, F.eps, -F.eps])
    v0s = np.array([F.Vlo, 0.5 * (F.VOL + F.VOH), F.Vhi])
    rows_u, rows_t, rows_w, rows_v0, kind = [], [], [], [], []
    for ti in range(thetas.shape[0]):
        ulist = list(u_fixed) + [switching_threshold(thetas[ti])]
        for ui, u in enumerate(ulist):
            for wi in range(3):
                for vi in range(3):
                    rows_u.append(u)
                    rows_t.append(ti)
                    rows_w.append(wi)
                    rows_v0.append(vi)
                    kind.append("u_M(theta)" if ui == len(ulist) - 1 else "fixed")
    rows_u, rows_t, rows_w, rows_v0, kind = np.array(rows_u), np.array(rows_t), np.array(rows_w), np.array(rows_v0), np.array(kind)
    dt = cfg["hold_dt"]
    N = int(round(cfg["hold_ns"] / dt))
    W = np.array([np.full(2 * N + 1, w) for w in ws])
    b = Batch(
        theta=thetas[rows_t], C=np.full(rows_u.size, F.C_lo), v0=v0s[rows_v0], w_idx=rows_w.astype(np.int64), fb=np.zeros(rows_u.size, dtype=np.int8),
        U=np.zeros(2 * N + 1), W=W, dt=dt, N=N, s_idx=0, deadline_idx=-1, sgn=1, Vth=F.VOH, eps=F.eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi,
        law=laws.inet_formal, u_row=rows_u,
    )
    r = run_batch(b)
    vf = r["v_final"]
    resid = np.abs(laws.inet_formal(rows_u, vf, *thetas[rows_t].T) + ws[rows_w]) / F.C_lo  # |dv/dt| at the end (V/ns)
    dec_f = np.array([decode_f(float(x), F) for x in vf])
    # decoder property: never a bit strictly between the thresholds; agrees with the exact-rational decoder
    from fractions import Fraction

    grid = np.linspace(F.Vlo, F.Vhi, 4361)
    ok_prop = all((decode_f(float(x), F) == "undefined") == (F.VOL < x < F.VOH) for x in grid)
    ok_exact = all({True: "high", False: "low", None: "undefined"}[decode(Fraction(float(x)), D)] == decode_f(float(x), F) for x in list(vf[:500]) + [F.VOH, F.VOL])
    table = []
    for u in u_fixed:
        sel = (kind == "fixed") & (rows_u == u)
        cnt = {k: int((dec_f[sel] == k).sum()) for k in ("high", "low", "undefined")}
        table.append([float(u), int(sel.sum()), cnt["high"], cnt["low"], cnt["undefined"], float(vf[sel].min()), float(vf[sel].max()), cnt["high"] > 0 and cnt["low"] > 0])
    selM = kind == "u_M(theta)"
    um_rows = []
    for ti, tn in enumerate(tnames):
        s = selM & (rows_t == ti)
        for wi, wn in enumerate(("0", "+eps", "-eps")):
            ss = s & (rows_w == wi)
            um_rows.append([tn, float(rows_u[s][0]), wn, *[float(x) for x in vf[ss]], *[str(x) for x in dec_f[ss]]])
    nom0 = selM & (rows_t == 0) & (rows_w == 0)
    cntM = {k: int((dec_f[selM] == k).sum()) for k in ("high", "low", "undefined")}
    return {
        "n_runs": int(rows_u.size), "hold_ns": cfg["hold_ns"], "dt_ns": dt, "C_fF": F.C_lo,
        "settled_check": {"max_abs_dvdt_at_end_V_per_ns": float(resid.max()), "n_runs_with_abs_dvdt_above_1e-6_V_per_ns": int((resid > 1e-6).sum()), "note": "near the switching threshold both devices are saturated and I_net does not depend on v over an interval of outputs: the output drifts across that interval at (I_net + w)/C, arbitrarily slowly as the input approaches the threshold, so some runs are still moving at the end of the hold (the decode reported is the one at the end of the hold). Exactly at u_M with w = 0 the whole interval is stationary, so the final value depends on the initial state; runs that start outside it approach its edge only algebraically (~1/t)."},
        "fixed_levels": {"header": ["u_V", "n_runs", "n_decoded_high_at_end_of_hold", "n_decoded_low_at_end_of_hold", "n_decoded_undefined_at_end_of_hold", "min_v_at_end_of_hold_V", "max_v_at_end_of_hold_V", "both_bits_occur_at_this_input"], "rows": table},
        "at_switching_threshold": {"header": ["theta", "u_M_V", "w", "v_final(v0=V_lo)", "v_final(v0=mid)", "v_final(v0=V_hi)", "decoded(v0=V_lo)", "decoded(v0=mid)", "decoded(v0=V_hi)"], "rows": um_rows, "decode_counts": cntM,
                                   "nominal_w0_final_values_V": [float(x) for x in vf[nom0]], "nominal_stationary_interval_V": [float(rows_u[nom0][0] - nominal[3]), float(rows_u[nom0][0] + nominal[4])]},
        "decoder_property": {"never_a_bit_strictly_between_thresholds": bool(ok_prop), "float_decoder_agrees_with_exact_decoder": bool(ok_exact), "n_grid": int(grid.size)},
        "decode_counts_all": {k: int((dec_f == k).sum()) for k in ("high", "low", "undefined")},
    }


def transfer_curves(D: Design, n: int = 421) -> dict:
    """DC transfer characteristic: nominal (w = 0) and the envelope over corners and |w| <= eps."""
    F = float_design(D)
    codes, Cn = corner_array(D)
    nominal = [0.5 * (F.lo(k) + F.hi(k)) for k in THETA_KEYS]
    u = np.linspace(0.0, F.VDD_hi, n)
    v_nom = np.array([stationary(F, nominal, float(x), 0.0) for x in u])
    v_min = np.array([min(stationary(F, th, float(x), -F.eps) for th in Cn) for x in u])
    v_max = np.array([max(stationary(F, th, float(x), F.eps) for th in Cn) for x in u])

    def bis(pred, lo, hi):
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if pred(mid):
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    uL = bis(lambda x: min(stationary(F, th, x, -F.eps) for th in Cn) >= F.VOH, F.VIL, F.VIH)
    uH = bis(lambda x: max(stationary(F, th, x, F.eps) for th in Cn) > F.VOL, F.VIL, F.VIH)
    return {
        "u": u, "v_nominal": v_nom, "v_min_envelope": v_min, "v_max_envelope": v_max,
        "summary": {
            "largest_u_with_settled_output_always_high_V": uL, "declared_V_IL": F.VIL, "static_slack_low_side_V": uL - F.VIL,
            "smallest_u_with_settled_output_always_low_V": uH, "declared_V_IH": F.VIH, "static_slack_high_side_V": F.VIH - uH,
            "note": "static (settled-output) limits of the model over 32 corners and |w| <= eps; they say nothing about timing. Between the two values the settled output can be high, low or undefined depending on theta and w.",
        },
    }


def run(D: Design, cfg: dict) -> dict:
    return {"edge_sweep": edge_sweep(D, cfg), "edge_simulation_check": edge_simulation_check(D, cfg), "barrier_stress": barrier_stress(D, cfg), "supply_relative": supply_relative(D, cfg), "midrail_hold": midrail_hold(D, cfg), "transfer_curves": transfer_curves(D)}
