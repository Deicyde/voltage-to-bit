#!/usr/bin/env python3
"""voltage-to-bit, workstream D: regenerate every numerical experiment from a design record.

Single entry point. From the repository root:

    uv venv .venv --python 3.14
    uv pip install --python .venv/bin/python -r experiments/requirements.txt
    .venv/bin/python experiments/run_all.py

Options:
    --design PATH      design record (default: designs/illustrative-1v8.json)
    --run-id NAME      output directory name under evidence/experiments/
                       (default: <UTC date>-D-<design name>-<first 8 hex of the design SHA-256>)
    --out DIR          parent of the run directory (default: evidence/experiments)
    --jobs N           worker processes for the trajectory batches (results do not depend on N)
    --skip STAGE ...   skip any of: trajectories convergence controls boundary sensitivity plots
    --compare-to DIR   after the run, compare every output hash with another run (determinism check)

What it does (docs/interface.md, v1 candidate rev. 2, is the model definition; the Lean sources are NOT read):
    01 margins       exact closed-form margins, admissibility, exact grid tests of the four margin claims
    02 trajectories  the run matrix: invariance, crossing by the bound, persistence
    03 worstcase     model worst-case delays by quadrature, tightness, multi-segment bounds
    04 convergence   solver tolerance / step studies behind every reported crossing time
    05 controls      negative controls (HANDOFF section 5)
    06 boundary      behaviour at and beyond the operating-domain boundary
    07 sensitivity   model-form sensitivity study (NOT validation against a device)
    08 ngspice       renders decks and the comparison plan only: PROPOSED, NOT RUN
    plots, summary.json, manifest.json

Everything is deterministic: the only random numbers come from named streams seeded with
[MASTER_SEED, crc32(stream name)], all listed in the manifest. Output files contain no timestamps;
those live only in manifest.json. ngspice is never invoked by this script.
"""
from __future__ import annotations

import argparse
import datetime as dt
import os
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
sys.path.insert(0, str(HERE))

from v2b import MASTER_SEED, boundary, common, controls, convergence, manifest, margins, sensitivity, spice, worstcase  # noqa: E402
from v2b import trajectories as traj_mod  # noqa: E402
from v2b.common import float_design, write_csv, write_json  # noqa: E402
from v2b.design import admissibility, dec, frac_record, is_admissible, load_design, tau_dn, tau_up  # noqa: E402

CFG = {
    "margins": dict(h_dense=Fr(1, 400), h_coarse=Fr(1, 100), n_random=2000, u_far_lo=Fr(-3), u_far_hi=Fr(5), v_far_lo=Fr(-1), v_far_hi=Fr(3), h_barrier=Fr(1, 2000), n_random_barrier=5000, de_popsize=20, de_maxiter=300),
    "sim": dict(dt=0.0005, horizon_factor=1.25, horizon_extra=0.5, n_interior=32),
    "worstcase": dict(u_far_lo=Fr(-3), u_far_hi=Fr(5), n_interior_starts=16, n_bracket=512, n_corner_extreme_samples=400000, uniform_Ns=[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], optimized_Ns=[1, 2, 4, 8, 16, 32], breakpoint_grid="0.001"),
    "controls": dict(eps_between=["3", "4", "5"]),
    "boundary": dict(supply_step="0.01", edge_sweep_max=0.4, edge_sweep_step=0.01, edge_sim_offsets=[0.0, 0.001, 0.01, 0.05, 0.09, 0.11, 0.15], edge_sim_hold_ns=8.0, barrier_u_lo=-0.5, barrier_u_hi=2.5, barrier_u_step=0.01, barrier_hold_ns=3.0, hold_ns=250.0, hold_dt=0.004),
    "sensitivity": dict(
        lambdas=[0.02, 0.05, 0.1, 0.2, 0.3], tails=[(1.0, 300.15), (1.3, 300.15), (1.5, 300.15), (1.3, 233.15), (1.5, 398.15)], combined=[(0.1, 1.3, 300.15), (0.3, 1.5, 398.15)],
        residual_step=0.01, fit_step=0.02, fit_random_starts=2, miller_dt=0.00025, miller_cgd_fF=[0.1, 0.25, 0.5, 1.0], miller_ramp_ns=[1.0, 0.1, 0.02],
    ),
    "reference_integrator": "scipy solve_ivp DOP853, rtol 1e-11..1e-13, atol rtol*1e-2, restarted at input/disturbance kinks, event-located crossings",
    "batch_integrator": "fixed-step classical RK4, cubic-Hermite event location, statistics on the step grid",
    "comparison_tolerances": {"TOL_V": traj_mod.TOL_V, "TOL_T": traj_mod.TOL_T},
}
STAGES = ("trajectories", "convergence", "controls", "boundary", "sensitivity", "plots")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--design", default=str(REPO / "designs" / "illustrative-1v8.json"))
    ap.add_argument("--run-id", default=None)
    ap.add_argument("--out", default=str(REPO / "evidence" / "experiments"))
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    ap.add_argument("--skip", nargs="*", default=[], choices=STAGES)
    ap.add_argument("--compare-to", default=None)
    args = ap.parse_args()

    started = dt.datetime.now(dt.timezone.utc)
    D = load_design(args.design)
    F = float_design(D)
    run_id = args.run_id or f"{started:%Y-%m-%d}-D-{D.name}-{D.sha256[:8]}"
    out = Path(args.out) / run_id
    out.mkdir(parents=True, exist_ok=True)
    stage_s: dict[str, float] = {}
    # no run id or timestamp in any output file except manifest.json, so that two runs can be compared byte for byte
    summary: dict = {"design": {"name": D.name, "sha256": D.sha256, "status": D.status}, "units": "V, uA, fF, ns"}
    completed, proposed, skipped = [], [], list(args.skip)

    def log(msg: str) -> None:
        print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)

    def timed(name):
        class _T:
            def __enter__(self_inner):
                self_inner.t = time.time()
                log(f"stage {name} ...")

            def __exit__(self_inner, *exc):
                stage_s[name] = round(time.time() - self_inner.t, 2)
                log(f"stage {name} done in {stage_s[name]} s")

        return _T()

    # ---- 01 margins ------------------------------------------------------
    with timed("01_margins"):
        mres = margins.run(D, CFG["margins"])
        d1 = out / "01_margins"
        write_json(d1 / "closed_form.json", {"closed_form": mres["closed_form"], "units": mres["closed_form_units"], "margin_minus_eps_uA": mres["margin_minus_eps_uA"], "admissibility": mres["admissibility"]})
        write_json(d1 / "margin_claims.json", {k: mres[k] for k in ("claim_up", "claim_dn", "claim_barriers", "float_rounding_noise", "de_search", "hypothesis_probes_outside_claims", "true_margins")})
        write_json(d1 / "proposal_barrier_refinement.json", mres["proposal_barrier_refinement"])
        mc = margins.margin_curves(D)
        write_csv(d1 / "margin_curves.csv", ["c_rise_V", "I_up_bound_uA", "model_min_pullup_at_VIL_uA", "c_fall_V", "I_dn_bound_uA", "model_min_pulldown_at_VIH_uA"], zip(mc["c_up"], mc["I_up"], mc["min_inet_up"], mc["c_dn"], mc["I_dn"], mc["min_pulldown"]))
        write_csv(d1 / "barrier_curves.csv", ["u_V", "model_min_inward_current_at_Vhi_uA", "model_min_inward_current_at_Vlo_uA"], zip(mc["u"], mc["inward_hi"], mc["inward_lo"]))
        slack = {
            "up": min(Fr(s["min_slack_uA"]["fraction"]) for s in mres["claim_up"]["exact_grid"]),
            "dn": min(Fr(s["min_slack_uA"]["fraction"]) for s in mres["claim_dn"]["exact_grid"]),
            "barrier_hi": Fr(mres["claim_barriers"]["hi"]["min_slack_uA"]["fraction"]),
            "barrier_lo": Fr(mres["claim_barriers"]["lo"]["min_slack_uA"]["fraction"]),
        }
        de = mres["de_search"]
        summary["margins"] = {
            "closed_form": {k: v["decimal"] if v else None for k, v in mres["closed_form"].items()},
            "closed_form_fractions": {k: v["fraction"] if v else None for k, v in mres["closed_form"].items()},
            "admissible": mres["admissibility"]["admissible"],
            "min_exact_grid_slack_uA": {k: dec(v) for k, v in slack.items()},
            "any_negative_exact_slack": any(v < 0 for v in slack.values()),
            "de_search_min_float_slack_uA": {k: de[k]["min_float_slack_uA"] for k in de},
            "de_search_exact_sign_at_argmin": {k: de[k]["exact_slack_sign"] for k in de},
            "model_min_inward_current_uA": {"V_hi": mres["claim_barriers"]["hi"]["min_inward_current_uA"]["decimal"], "V_lo": mres["claim_barriers"]["lo"]["min_inward_current_uA"]["decimal"]},
            "hypothesis_probes_outside_claims_min_slack_uA": {k: v["min_slack_uA"]["decimal"] for k, v in mres["hypothesis_probes_outside_claims"].items()},
            "float_rounding_noise": mres["float_rounding_noise"],
            "n_exact_grid_triples": {"up": sum(s_["n_triples_covered"] for s_ in mres["claim_up"]["exact_grid"]), "dn": sum(s_["n_triples_covered"] for s_ in mres["claim_dn"]["exact_grid"]), "barrier_hi": mres["claim_barriers"]["hi"]["n_points"], "barrier_lo": mres["claim_barriers"]["lo"]["n_points"]},
            "proposal_barrier_refinement (numerically checked only)": {"certified_restoring_current_uA": mres["proposal_barrier_refinement"]["certified_restoring_current_uA"]["rows"], "sharper_R_hiP_at_present_uHi_uA": mres["proposal_barrier_refinement"]["sharper_R_hiP_at_present_uHi_uA"], "lemma_checks_on_exact_grid": mres["proposal_barrier_refinement"]["lemma_checks_on_exact_grid"]},
        }
        completed += ["closed-form margins and taus (exact rationals)", "admissibility of the design record", "four margin claims on exact integer grids + seeded global search"]

    # ---- 03 worst case (needed by later stages) ---------------------------
    with timed("03_worstcase"):
        wres = worstcase.run(D, CFG["worstcase"])
        d3 = out / "03_worstcase"
        cd = wres.pop("corner_delays")
        write_csv(d3 / "corner_delays.csv", cd["header"], cd["rows"])
        ct = wres["convergence_table"]
        write_csv(d3 / "multisegment_convergence.csv", ct["header"], ct["rows"])
        bp = {name: {N: {k: v for k, v in rec.items()} for N, rec in wres[name]["optimized"].items()} for name in ("rise", "fall")}
        write_json(d3 / "breakpoints.json", {"note": "c_0..c_N as exact decimal strings; bound = sum_i C_max |c_i - c_{i-1}| / (I(c_i) - eps), I = I_up (rise) or I_dn (fall); globally optimal on a 1 mV grid (dynamic programme)", "rise": bp["rise"], "fall": bp["fall"], "uniform_exact": wres.get("uniform_exact")})
        write_json(d3 / "worst_case.json", {k: v for k, v in wres.items() if k != "convergence_table"})
        worst_codes = {"L": wres["rise"]["true_worst_case"]["worst_corner"], "H": wres["fall"]["true_worst_case"]["worst_corner"]}
        brackets = {"rise": wres["rise"]["true_worst_case"]["exact_bracket"], "fall": wres["fall"]["true_worst_case"]["exact_bracket"]}
        wt = {}
        rows = []
        for pol, name in (("L", "rise"), ("H", "fall")):
            tau = float(tau_up(D) if pol == "L" else tau_dn(D))
            r = worstcase.simulate_worst_box(D, pol, t_end=1.15 * tau, dense_t=np.linspace(0.0, 1.15 * tau, 461))
            wt[name] = (r["t"], r["v"])
            rows += [[name, t, v] for t, v in zip(r["t"], r["v"])]
        write_csv(d3 / "worst_case_trajectories.csv", ["transition", "t_ns", "v_V"], rows)
        summary["worst_case"] = {
            name: {
                "tau_ns": wres[name]["tau_ns"]["decimal"],
                "model_worst_case_delay_ns (moving theta, interface v1 rev. 2)": wres[name]["true_worst_case"]["quadrature_ns"],
                "exact_bracket_ns": [wres[name]["true_worst_case"]["exact_bracket"]["lower_ns"], wres[name]["true_worst_case"]["exact_bracket"]["upper_ns"]],
                "model_worst_case_delay_ns (constant theta)": wres[name]["true_worst_case"]["constant_theta"]["quadrature_ns"],
                "worst_corner(VDD,kn,kp,Vtn,Vtp) for constant theta": wres[name]["true_worst_case"]["worst_corner"],
                "tau_over_model_worst_case": wres[name]["tightness"]["tau_over_true_worst_case"],
                "limit_of_multisegment_bound_ns": wres[name]["tightness"]["limit_of_multisegment_bound_ns"],
                "multisegment": {N: {"breakpoints_V": wres[name]["optimized"][N]["breakpoints_V"], "bound_ns": wres[name]["optimized"][N]["bound_ns"]["decimal"], "over_model_worst_case": wres[name]["optimized"][N]["ratio_to_true_worst_case"]} for N in ("2", "4", "8")},
            }
            for name in ("rise", "fall")
        }
        summary["worst_case"]["band_edge_is_pointwise_worst_input"] = wres["worst_input_check"]["band_edge_is_pointwise_worst_input"]
        summary["worst_case"]["corner_extremes_check"] = wres["worst_input_check"]["corner_extremes_check"]
        completed += ["model worst-case delays (quadrature, exact brackets, simulation)", "multi-segment bounds: uniform and optimised breakpoints"]

    # ---- 02 trajectories ---------------------------------------------------
    tres = None
    if "trajectories" not in args.skip:
        with timed("02_trajectories"):
            tres = traj_mod.run_matrix(D, CFG["sim"], jobs=args.jobs)
            d2 = out / "02_trajectories"
            write_csv(d2 / "group_summary.csv", tres["group_header"], tres["groups"])
            write_csv(d2 / "worst_runs.csv", traj_mod.ROW_FIELDS, [[r[k] for k in traj_mod.ROW_FIELDS] for r in tres["worst"]])
            write_csv(d2 / "failing_cases.csv", traj_mod.ROW_FIELDS, [[r[k] for k in traj_mod.ROW_FIELDS] for r in tres["failing"]])
            write_json(d2 / "summary.json", {k: tres[k] for k in ("label", "totals", "per_polarity", "n_failing_total", "ratio_hist", "inputs", "n_batches")} | {
                "matrix": {"theta_C_sets": "32 corners x {C_min, C_max} + 32 seeded interior lattice points x {C_max, seeded random C}; plus the theta-free rows box_low / box_high (extremal selections of the rev. 2 inclusion, parameter point free at each instant)", "initial_states": list(traj_mod.V0_NAMES), "disturbances": "zero, +eps, -eps, sinusoids at " + ", ".join(f"{f:g}" for f in traj_mod.SIN_FREQS_GHZ) + " GHz (seeded phases), seeded random PWL (knots every " + ", ".join(f"{s:g}" for s in traj_mod.PWL_STEPS_NS) + " ns; uniform and +-eps extremes), adv_oppose, adv_outward, env_low, env_high", "checks": "(a) v in [V_lo, V_hi] at every step; (b) first valid-output crossing after s no later than s + tau, and valid at every step from s + tau to the end; also recorded: any return to invalid after the first crossing", "tolerances": CFG["comparison_tolerances"]},
            })
            boxg = [g for g in tres["groups"] if g[2] in ("box_low", "box_high")]
            summary["trajectories"] = {
                "totals": tres["totals"], "per_polarity": tres["per_polarity"],
                "box_envelope_rows (bound every trajectory of the rev. 2 inclusion for their input and initial state)": {
                    "n_runs": sum(g[3] for g in boxg), "violations": sum(g[4] + g[5] + g[6] + g[7] for g in boxg),
                    "max_ratio_rise": max(g[8] for g in boxg if g[0] == "L"), "max_ratio_fall": max(g[8] for g in boxg if g[0] == "H"),
                },
            }
            completed += [f"trajectory matrix: {tres['totals']['n_runs']} runs, three guarantee checks"]

    # ---- 04 convergence ----------------------------------------------------
    cres = None
    if "convergence" not in args.skip:
        with timed("04_convergence"):
            cres = convergence.run(D, CFG["sim"], worst_codes, args.jobs)
            d4 = out / "04_convergence"
            for key, fn in (("tolerance_sweep", "tolerance_sweep.csv"), ("rk4_step_sweep", "rk4_step_sweep.csv")):
                write_csv(d4 / fn, cres["autonomous"][key]["header"], cres["autonomous"][key]["rows"])
            write_csv(d4 / "nonautonomous.csv", cres["nonautonomous"]["header"], cres["nonautonomous"]["rows"])
            write_csv(d4 / "batch_halving.csv", cres["batch_halving"]["header"], cres["batch_halving"]["rows"])
            prod = {r[0]: r[4] for r in cres["autonomous"]["rk4_step_sweep"]["rows"] if r[1] == CFG["sim"]["dt"] and r[2] == "hermite"}
            tight = {}
            for r in cres["autonomous"]["tolerance_sweep"]["rows"]:
                if r[2] == 1e-12 and isinstance(r[5], float):
                    tight[f"{r[0]}/{r[1]}"] = r[5]
            csum = {"reference": cres["autonomous"]["reference"], "batch_engine_error_vs_quadrature_ns_at_production_step": prod, "adaptive_solver_error_vs_quadrature_ns_at_rtol_1e-12": tight, "batch_halving": cres["batch_halving"]["overall"], "note": "observed RK4 orders are irregular because psq has a discontinuous second derivative; errors, not orders, are the evidence"}
            write_json(d4 / "summary.json", csum)
            summary["convergence"] = csum
            completed += ["convergence: tolerance sweep x 5 methods, RK4 step sweep, non-autonomous cross-checks, step halving of the batch engine"]

    # ---- 05 negative controls ----------------------------------------------
    kres = ktraj = None
    if "controls" not in args.skip:
        with timed("05_negative_controls"):
            kres, ktraj = controls.run(D, CFG["sim"] | CFG["controls"], worst_codes, brackets, mres["claim_barriers"], args.jobs)
            d5 = out / "05_negative_controls"
            write_json(d5 / "controls.json", kres)
            rows = []
            for name, (t, v) in ktraj.items():
                rows += [[name, a, b] for a, b in zip(t, v)]
            write_csv(d5 / "trajectories.csv", ["control", "t_ns", "v_V"], rows)
            ii = kres["ii_insufficient_observation_time"]
            iv = kres["iv_disturbance_destroys_margin"]
            summary["negative_controls"] = {
                "i_invalid_bounds": {k: v["checker_verdict"] for k, v in kres["i_invalid_parameter_bounds"].items()},
                "i_margins_alone_would_pass": {k: v.get("six_margins_alone_would_pass") for k, v in kres["i_invalid_parameter_bounds"].items() if "six_margins_alone_would_pass" in v},
                "ii_lower_bound_on_worst_case_delay_ns": {k: ii[k]["rigorous_lower_bound_on_this_trajectory_crossing_ns"] for k in ("rise", "fall")},
                "ii_decoded_at_0.9_x_lower_bound": {k: ii[k]["samples"][1]["decoded"] for k in ("rise", "fall")},
                "iii_miswired": {"all_four_exhibited_cases_violate": all(c["guarantee_violated"] for c in kres["iii_miswired_transistor_roles"]["exhibited_trajectories"]), "matrix": {k: kres["iii_miswired_transistor_roles"]["matrix"][k] for k in ("n_runs", "n_violating_crossing_by_bound", "n_violating_persistence", "n_violating_safe_domain")}},
                "iv_smallest_eps_with_stationary_point_at_or_below_V_OH_uA": iv["rise"]["smallest_eps_with_stationary_point_at_or_below_V_OH_uA"]["decimal"],
                "iv_smallest_eps_with_stationary_point_at_or_above_V_OL_uA": iv["fall"]["smallest_eps_with_stationary_point_at_or_above_V_OL_uA"]["decimal"],
                "iv_certificate_accepts": iv["certificate_limits"]["largest_eps_the_certificate_accepts"],
                "iv_between": {k: {"admissible": v["admissible"], "violations": v["violations"]} for k, v in iv["between_certificate_and_model_limits"]["runs"].items()},
            }
            completed += ["negative controls (i)-(iv), each with a rejection and/or an exhibited trajectory"]

    # ---- 06 boundary -------------------------------------------------------
    bres = None
    if "boundary" not in args.skip:
        with timed("06_boundary"):
            bres = boundary.run(D, CFG["boundary"] | {"dt": CFG["sim"]["dt"]})
            d6 = out / "06_boundary"
            es = bres["edge_sweep"]
            write_csv(d6 / "edge_sweep.csv", es["header"], es["rows"])
            esc = bres["edge_simulation_check"]
            write_csv(d6 / "edge_simulation_check.csv", esc["header"], esc["rows"])
            sr = bres["supply_relative"]
            write_csv(d6 / "supply_relative_domain.csv", sr["per_supply"]["header"], sr["per_supply"]["rows"])
            mh = bres["midrail_hold"]
            write_csv(d6 / "midrail_fixed_levels.csv", mh["fixed_levels"]["header"], mh["fixed_levels"]["rows"])
            write_csv(d6 / "midrail_at_switching_threshold.csv", mh["at_switching_threshold"]["header"], mh["at_switching_threshold"]["rows"])
            tc = bres["transfer_curves"]
            write_csv(d6 / "transfer_curves.csv", ["u_V", "v_nominal_w0_V", "v_min_over_corners_and_w_V", "v_max_over_corners_and_w_V"], zip(tc["u"], tc["v_nominal"], tc["v_min_envelope"], tc["v_max_envelope"]))
            bsum = {
                "edge_sweep": es["summary"], "edge_simulation_check_max_abs_sim_minus_quadrature_ns": max(abs(r[5]) for r in esc["rows"] if r[5] == r[5]), "barrier_stress": bres["barrier_stress"], "supply_relative_domain": {k: v for k, v in sr.items() if k != "per_supply"}, "transfer": tc["summary"],
                "midrail_hold": {k: mh[k] for k in ("n_runs", "hold_ns", "dt_ns", "C_fF", "settled_check", "decoder_property", "decode_counts_all")} | {"at_switching_threshold": {k: mh["at_switching_threshold"][k] for k in ("decode_counts", "nominal_w0_final_values_V", "nominal_stationary_interval_V")}},
            }
            write_json(d6 / "summary.json", bsum)
            summary["boundary"] = bsum
            completed += ["boundary behaviour: edge sweep into the invalid band, barrier stress at V_lo/V_hi, long mid-rail holds, transfer curve"]

    # ---- 07 sensitivity ----------------------------------------------------
    sres = None
    if "sensitivity" not in args.skip:
        with timed("07_sensitivity"):
            sres = sensitivity.run(D, CFG["sim"] | CFG["sensitivity"], worst_codes, args.jobs)
            d7 = out / "07_sensitivity"
            for key, fn in (("sandwich", "sandwich_residual.csv"), ("residual", "fixed_theta_residual.csv"), ("refit", "fixed_theta_refit.csv"), ("trajectories", "trajectories.csv")):
                write_csv(d7 / fn, sres[key]["header"], sres[key]["rows"])
            write_csv(d7 / "miller.csv", sres["miller"]["header"], sres["miller"]["rows"])
            ssum = {
                "label": sres["label"],
                "n_perturbations": len(sres["residual"]["rows"]),
                "trajectory_violations_total": {"safe_domain": sum(r[3] for r in sres["trajectories"]["rows"]), "crossing_by_bound": sum(r[4] for r in sres["trajectories"]["rows"]), "persistence": sum(r[5] for r in sres["trajectories"]["rows"]), "n_runs": sum(r[2] for r in sres["trajectories"]["rows"])},
                "sandwich_residual_over_eps (rev. 2 obligation; whole box / box at device supply)": {f"{r[0]} | base {r[2]}": [r[4], r[10]] for r in sres["sandwich"]["rows"]},
                "largest_lambda_inside_tube": sres["largest_lambda_inside_tube"],
                "max_fixed_theta_residual_over_eps_by_family (superseded v0 obligation)": {fam: max(r[6] for r in sres["residual"]["rows"] if r[1] == fam) for fam in ("channel-length modulation", "subthreshold tail", "combined")},
                "miller": {"setup": sres["miller"]["setup"], "slew_limit": sres["miller"]["slew_limit_for_feedthrough_alone_to_fit_in_eps_V_per_ns"], "n_runs_leaving_safe_domain": sum(r[6] for r in sres["miller"]["rows"]), "n_runs": sum(r[5] for r in sres["miller"]["rows"]), "largest_excursion_V": max(max(r[9], r[10]) for r in sres["miller"]["rows"])},
                "constants": sres["constants"],
            }
            write_json(d7 / "summary.json", ssum)
            summary["sensitivity"] = ssum
            completed += ["model-form sensitivity study (channel-length modulation, subthreshold tail, gate-drain feedthrough) - a sensitivity study, not validation"]

    # ---- 08 ngspice: PROPOSED, NOT RUN -------------------------------------
    with timed("08_ngspice_render_only"):
        decks = spice.write_decks(D, HERE / "ngspice" / "decks", worst_codes)
        plan = spice.compare_plan(D)
        plan["rendered_decks"] = {name: manifest.sha256_file(HERE / "ngspice" / "decks" / name) for name in decks}
        write_json(out / "08_ngspice_PROPOSED_NOT_RUN" / "compare_plan.json", plan)
        # plumbing self-test of the runner on synthetic wrdata-layout files written from the PYTHON model
        import importlib.util
        import tempfile

        spec_ = importlib.util.spec_from_file_location("run_ngspice", HERE / "ngspice" / "run_ngspice.py")
        mod_ = importlib.util.module_from_spec(spec_)
        spec_.loader.exec_module(mod_)
        with tempfile.TemporaryDirectory() as tmp:
            st = mod_.self_test(D, Path(tmp))
        st["what_this_is"] = "NOT a SPICE run. The runner's parser and comparison code were fed files in the assumed ngspice wrdata layout, generated from the Python model. It shows the plumbing is self-consistent, nothing about ngspice or about any device."
        write_json(out / "08_ngspice_PROPOSED_NOT_RUN" / "runner_selftest_NO_SPICE.json", st)
        summary["ngspice"] = {"status": "PROPOSED, NOT RUN", "runner_selftest_without_spice_passes": st["passes"], "decks": decks}
        proposed += [
            "(a) tier T1: ngspice MOS Level-1 (LAMBDA=0, GAMMA=0, IS=1e-30) DC map and transients versus the Python simulator - PROPOSED, NOT RUN",
            "(a2) tier T2: Level-1 with one omitted effect switched back on at a time - PROPOSED, NOT RUN (decks not rendered)",
            "(b) tier T3: SKY130 BSIM4 nfet_01v8 / pfet_01v8_hvt (workstream B's recommendation, not frozen): sandwich residual versus eps_I, the four margins on the SPICE map, transient delays versus tau, excursions versus the safe domain - PROPOSED, NOT RUN",
        ]

    # ---- plots --------------------------------------------------------------
    if "plots" not in args.skip:
        with timed("plots"):
            from v2b import plots

            pd_ = out / "plots"
            plots.fig_margins(pd_ / "fig1_current_margins.png", mc, F, mres["closed_form"])
            plots.fig_barriers(pd_ / "fig2_barrier_margins.png", mc, F, mres["claim_barriers"])
            plots.fig_worst(pd_ / "fig3_worst_case_transitions.png", wt, F, wres)
            plots.fig_multiseg(pd_ / "fig5_multisegment_bounds.png", wres)
            if tres is not None:
                plots.fig_ratio_hist(pd_ / "fig4_crossing_time_ratio.png", tres)
            if cres is not None:
                plots.fig_convergence(pd_ / "fig6_convergence.png", cres)
            if kres is not None:
                plots.fig_controls(pd_ / "fig7_negative_controls.png", kres, ktraj, F, (float(tau_up(D)), float(tau_dn(D))))
            if bres is not None:
                plots.fig_transfer(pd_ / "fig8_transfer_characteristic.png", bres["transfer_curves"], F)
            if sres is not None:
                plots.fig_sensitivity(pd_ / "fig9_model_form_sensitivity.png", sres, F)

    summary["checks"] = {"COMPLETED": completed, "PROPOSED_NOT_RUN": proposed, "SKIPPED_IN_THIS_INVOCATION": skipped}
    write_json(out / "summary.json", summary)

    finished = dt.datetime.now(dt.timezone.utc)
    man = {
        "run_id": run_id,
        "workstream": "D (numerical experiments and model comparison)",
        "evidence_status": {"formal_correctness": "not addressed here (numerics are an independent check on the mathematics, not a proof)", "applicability": "the design record is ILLUSTRATIVE; these runs instantiate it", "physical_evidence": "none: no SPICE run, no measurement; the sensitivity study is not validation"},
        "design": {"path": os.path.relpath(D.path, REPO), "sha256": D.sha256, "name": D.name, "status": D.status},
        "documents_read": {p: manifest.sha256_file(REPO / p) for p in ("docs/interface.md", "docs/model.md", "HANDOFF.md") if (REPO / p).exists()},
        "documents_note": "hashes at the end of this run. The simulator was written against interface.md DRAFT v0 and updated to the v1 candidate (rev. 2) trajectory notion (parameter point free at each instant); docs/model.md (workstream B) was read only for the comparison-model recommendation and the Level-1 deck settings.",
        "lean_sources_read": False,
        "code_sha256": manifest.code_hashes(HERE),
        "environment": manifest.environment(),
        "git": manifest.git_state(REPO),
        "seeds": {"master_seed": MASTER_SEED, "rule": "numpy PCG64(SeedSequence([master_seed, crc32(stream name)]))", "streams": common.SEED_LOG},
        "solver_settings": manifest.jsonable(CFG),
        "command": [os.path.basename(sys.argv[0])] + sys.argv[1:],
        "jobs": args.jobs,
        "timestamps": {"started_utc": started.isoformat(timespec="seconds"), "finished_utc": finished.isoformat(timespec="seconds"), "stage_seconds": stage_s},
        "outputs": manifest.output_hashes(out),
        "checks": summary["checks"],
    }
    if args.compare_to:
        import json

        other = json.loads((Path(args.compare_to) / "manifest.json").read_text())["outputs"]
        mine = man["outputs"]
        diff = sorted(k for k in set(other) | set(mine) if other.get(k, {}).get("sha256") != mine.get(k, {}).get("sha256"))
        other_man = json.loads((Path(args.compare_to) / "manifest.json").read_text())
        man["determinism_check"] = {"compared_with": str(args.compare_to), "n_files": len(mine), "files_that_differ": diff, "identical": not diff}
        record = {
            "what": "a second complete run of experiments/run_all.py, compared file by file (SHA-256) with the run named below; manifest.json is excluded because it holds timestamps",
            "reference_run": {"run_id": other_man["run_id"], "jobs": other_man["jobs"], "started_utc": other_man["timestamps"]["started_utc"]},
            "second_run": {"run_id": run_id, "jobs": args.jobs, "started_utc": started.isoformat(timespec="seconds"), "finished_utc": finished.isoformat(timespec="seconds"), "kept": False},
            "same_code_and_design": other_man["code_sha256"] == man["code_sha256"] and other_man["design"]["sha256"] == man["design"]["sha256"],
            "n_files_compared": len(mine), "files_that_differ": diff, "identical": not diff,
        }
        write_json(Path(args.compare_to).with_name(Path(args.compare_to).name + ".determinism.json"), record)
        log(f"determinism check against {args.compare_to}: {'IDENTICAL' if not diff else 'DIFFERENT: ' + ', '.join(diff)}")
    write_json(out / "manifest.json", man)
    log(f"wrote {out}")
    neg = summary["margins"]["any_negative_exact_slack"]
    nviol = None if tres is None else tres["n_failing_total"]
    log(f"headline: admissible={summary['margins']['admissible']}  negative exact slack found={neg}  trajectory violations={nviol}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
