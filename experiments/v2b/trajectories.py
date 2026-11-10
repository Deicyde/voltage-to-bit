"""Task 3: the trajectory matrix and the three guarantee checks.

polarity "L": input valid-low from time s on  -> output must be >= V_OH on [s + tau_up, end]
polarity "H": input valid-high from time s on -> output must be <= V_OL on [s + tau_dn, end]

One batch = (polarity, input waveform); rows = (theta, C) x initial state x disturbance,
plus theta-independent rows "box_low" / "box_high": the extremal selections of the
interface.md v1 (rev. 2) inclusion, in which the parameter point, the capacitance and the
disturbance may all change from instant to instant. For a given input and initial state
every trajectory of that inclusion lies between those two rows.
"""
from __future__ import annotations

import math
from concurrent.futures import ProcessPoolExecutor

import numpy as np

from . import laws, signals
from .common import corner_array, float_design, lattice_thetas, rng_for, theta_floats
from .design import Design, tau_dn, tau_up
from .sim import FB_NAMES, Batch, half_step_times, run_batch

TOL_V = 1e-9  # V, tolerance on threshold / domain comparisons (reported minima are raw)
TOL_T = 1e-9  # ns

SIN_FREQS_GHZ = (0.1, 1.0, 10.0, 50.0)
PWL_STEPS_NS = (0.02, 0.2)
V0_NAMES = ("V_lo", "V_OL", "mid", "V_OH", "V_hi", "random")
FB_KINDS = (1, 2, 3, 4)
BOX_SET = "box:any-theta-per-instant"
BOX_KINDS = (5, 6)


def _ceil_to(x: float, dt: float) -> int:
    return int(math.ceil(x / dt - 1e-9))


def input_specs(F, pol: str, dt: float) -> list[dict]:
    """Seven input waveforms per polarity. ``s`` (start of the valid window) is on the time grid."""
    out = []
    rng = rng_for(f"traj/input/pwl/{pol}")
    if pol == "L":
        edge, far, opp_rail, deep_end = F.VIL, F.Vlo - 0.4, F.VDD_hi, 0.0
        sl = -1.0
        band = (F.VIL - 0.6, F.VIL)
    else:
        edge, far, opp_rail, deep_end = F.VIH, F.Vhi + 0.4, 0.0, F.VDD_hi
        sl = +1.0
        band = (F.VIH, F.VDD_hi + 0.2)
    out.append({"name": "const_edge", "desc": "u held exactly at the valid-band edge", "spec": {"kind": "const", "value": edge}, "s": 0.0})
    out.append({"name": "const_beyond_rail", "desc": "u held 0.4 V outside the safe domain (arbitrary real input)", "spec": {"kind": "const", "value": far}, "s": 0.0})
    for name, slew, end in (("ramp_20V_per_ns_to_edge", 20.0, edge), ("ramp_2V_per_ns_to_edge", 2.0, edge), ("ramp_0.4V_per_ns_full_swing", 0.4, deep_end)):
        t_ramp = abs(opp_rail - edge) / slew
        s = (_ceil_to(t_ramp + 0.05, dt)) * dt
        lo, hi = (min(end, opp_rail), max(end, opp_rail))
        out.append({"name": name, "desc": f"finite-slew ramp from the opposite rail through the mid region, reaching the band edge at t = s, ending at {end:g} V", "spec": {"kind": "ramp", "edge": edge, "slew": sl * slew, "t_edge": s, "lo": lo, "hi": hi}, "s": s})
    amp = 0.5 * (band[1] - band[0])
    if pol == "L":
        spec = {"kind": "sin", "offset": band[1] - amp, "amp": amp, "freq": 1.0 / 0.7, "phase": 0.5 * math.pi}
    else:
        spec = {"kind": "sin", "offset": band[0] + amp, "amp": amp, "freq": 1.0 / 0.7, "phase": -0.5 * math.pi}
    out.append({"name": "wander_sine", "desc": f"sine wandering over [{band[0]:g}, {band[1]:g}] V, touching the band edge every 0.7 ns", "spec": spec, "s": 0.0})
    vals = rng.uniform(band[0], band[1], size=400)
    vals[::4] = edge  # touch the band edge exactly, repeatedly
    out.append({"name": "wander_pwl", "desc": f"seeded random piecewise-linear input in [{band[0]:g}, {band[1]:g}] V, knots every 0.1 ns, every 4th knot exactly at the band edge", "spec": {"kind": "pwl", "step": 0.1, "values": vals.tolist()}, "s": 0.0})
    return out


def disturbance_table(F, eps: float, t_half: np.ndarray) -> tuple[list[dict], np.ndarray]:
    """Time-only disturbances (all |w| <= eps): zero, +-eps, sinusoids, seeded random PWL."""
    specs = [
        {"name": "zero", "spec": {"kind": "const", "value": 0.0}},
        {"name": "+eps", "spec": {"kind": "const", "value": eps}},
        {"name": "-eps", "spec": {"kind": "const", "value": -eps}},
    ]
    ph = rng_for("traj/w/sin/phase").uniform(0.0, 2.0 * math.pi, size=len(SIN_FREQS_GHZ))
    for f, p in zip(SIN_FREQS_GHZ, ph):
        specs.append({"name": f"sin_{f:g}GHz", "spec": {"kind": "sin", "offset": 0.0, "amp": eps, "freq": f, "phase": float(p)}})
    for st in PWL_STEPS_NS:
        n = int(math.ceil(12.0 / st)) + 2
        r1 = rng_for(f"traj/w/pwl/{st:g}/uniform").uniform(-eps, eps, size=n)
        r2 = eps * rng_for(f"traj/w/pwl/{st:g}/extremes").choice([-1.0, 1.0], size=n)
        specs.append({"name": f"pwl_{st:g}ns_uniform", "spec": {"kind": "pwl", "step": st, "values": r1.tolist()}})
        specs.append({"name": f"pwl_{st:g}ns_extremes", "spec": {"kind": "pwl", "step": st, "values": r2.tolist()}})
    W = np.array([signals.evaluate(s["spec"], t_half) for s in specs])
    assert np.all(np.abs(W) <= eps * (1 + 1e-12)), "disturbance exceeds the bound"
    return specs, W


def theta_c_sets(D: Design, F, n_interior: int) -> tuple[list[str], np.ndarray, np.ndarray]:
    codes, Cn = corner_array(D)
    names, th, C = [], [], []
    for code, row in zip(codes, Cn):
        for cname, cval in (("C_min", F.C_lo), ("C_max", F.C_hi)):
            names.append(f"corner:{code}/{cname}")
            th.append(row)
            C.append(cval)
    lat = theta_floats(lattice_thetas(D, n_interior, "traj/theta"))
    crand = rng_for("traj/C").uniform(F.C_lo, F.C_hi, size=n_interior)
    for i, row in enumerate(lat):
        names.append(f"interior:{i}/C_max")
        th.append(row)
        C.append(F.C_hi)
        names.append(f"interior:{i}/C_rand")
        th.append(row)
        C.append(float(crand[i]))
    return names, np.array(th), np.array(C)


def build_batch(D: Design, pol: str, inp: dict, cfg: dict, law=laws.inet_formal, eps: float | None = None, taus: tuple | None = None, set_filter=None, dist_filter=None, v0_filter=None) -> tuple[Batch, dict]:
    F = float_design(D)
    eps = F.eps if eps is None else eps
    dt = cfg["dt"]
    t_up, t_dn = taus if taus is not None else (float(tau_up(D)), float(tau_dn(D)))
    tau = t_up if pol == "L" else t_dn
    sgn, Vth = (1, F.VOH) if pol == "L" else (-1, F.VOL)
    s = inp["s"]
    N = _ceil_to(s + cfg["horizon_factor"] * tau + cfg["horizon_extra"], dt)
    th_half = half_step_times(dt, N)
    U = signals.evaluate(inp["spec"], th_half)
    dspecs, W = disturbance_table(F, eps, th_half)
    names, TH, CC = theta_c_sets(D, F, cfg["n_interior"])
    n_sets, n_v0 = len(names), len(V0_NAMES)
    dist_names = [d["name"] for d in dspecs] + [FB_NAMES[k] for k in FB_KINDS]
    n_d = len(dist_names)
    a, b_, d = np.meshgrid(np.arange(n_sets), np.arange(n_v0), np.arange(n_d), indexing="ij")
    a, b_, d = a.ravel(), b_.ravel(), d.ravel()
    keep = np.ones(a.size, dtype=bool)
    if set_filter is not None:
        keep &= np.array([set_filter(names[i]) for i in a])
    if dist_filter is not None:
        keep &= np.array([dist_filter(dist_names[i]) for i in d])
    if v0_filter is not None:
        keep &= np.array([v0_filter(V0_NAMES[i]) for i in b_])
    a, b_, d = a[keep], b_[keep], d[keep]
    v0_fixed = np.array([F.Vlo, F.VOL, 0.5 * (F.VOL + F.VOH), F.VOH, F.Vhi, np.nan])
    v0 = v0_fixed[b_]
    rnd = rng_for(f"traj/v0/{pol}/{inp['name']}").uniform(F.Vlo, F.Vhi, size=n_sets * n_v0 * n_d)[keep]
    v0 = np.where(np.isnan(v0), rnd, v0)
    n_tab = len(dspecs)
    w_idx = np.where(d < n_tab, d, 0)
    fb = np.where(d < n_tab, 0, np.array(FB_KINDS + (0,))[np.clip(d - n_tab, 0, len(FB_KINDS))]).astype(np.int8)
    theta_rows, C_rows = TH[a], CC[a]

    # rev. 2 extremal envelopes: no parameter point, no capacitance value of their own
    names = names + [BOX_SET]
    dist_names = dist_names + [FB_NAMES[k] for k in BOX_KINDS]
    bb, bk = np.meshgrid(np.arange(n_v0), np.arange(len(BOX_KINDS)), indexing="ij")
    bb, bk = bb.ravel(), bk.ravel()
    v0_box = v0_fixed[bb]
    rnd_box = rng_for(f"traj/v0box/{pol}/{inp['name']}").uniform(F.Vlo, F.Vhi, size=bb.size)
    v0_box = np.where(np.isnan(v0_box), rnd_box, v0_box)
    keep_b = np.ones(bb.size, dtype=bool)
    if set_filter is not None and not set_filter(BOX_SET):
        keep_b[:] = False
    if dist_filter is not None:
        keep_b &= np.array([dist_filter(FB_NAMES[BOX_KINDS[i]]) for i in bk])
    if v0_filter is not None:
        keep_b &= np.array([v0_filter(V0_NAMES[i]) for i in bb])
    bb, bk, v0_box = bb[keep_b], bk[keep_b], v0_box[keep_b]
    nb = bb.size
    a = np.concatenate([a, np.full(nb, n_sets, dtype=a.dtype)])
    b_ = np.concatenate([b_, bb])
    d = np.concatenate([d, n_d + bk])
    v0 = np.concatenate([v0, v0_box])
    w_idx = np.concatenate([w_idx, np.zeros(nb, dtype=w_idx.dtype)])
    fb = np.concatenate([fb, np.array(BOX_KINDS, dtype=np.int8)[bk]])
    theta_rows = np.vstack([theta_rows, np.full((nb, 5), np.nan)])
    C_rows = np.concatenate([C_rows, np.full(nb, np.nan)])
    _codes, box = corner_array(D)

    batch = Batch(
        theta=theta_rows, C=C_rows, v0=v0, w_idx=w_idx, fb=fb, U=U, W=W, dt=dt, N=N,
        s_idx=int(round(s / dt)), deadline_idx=_ceil_to(s + tau, dt), sgn=sgn, Vth=Vth,
        eps=eps, Cmin=F.C_lo, Cmax=F.C_hi, Vlo=F.Vlo, Vhi=F.Vhi, law=law, box=box,
    )
    meta = {"pol": pol, "input": inp["name"], "s": s, "tau": tau, "N": N, "T_end": N * dt, "set_names": names, "dist_names": dist_names, "a": a, "b": b_, "d": d, "n": int(a.size)}
    return batch, meta


def evaluate(batch: Batch, meta: dict, res: dict) -> dict:
    F_Vlo, F_Vhi = batch.Vlo, batch.Vhi
    delay = res["t_cross"] - meta["s"]
    ratio = delay / meta["tau"]
    viol_safe = (res["vmin"] < F_Vlo - TOL_V) | (res["vmax"] > F_Vhi + TOL_V)
    viol_cross = ~(delay <= meta["tau"] + TOL_T)
    viol_persist = ~(res["g_after_deadline"] >= -TOL_V)
    viol_recross = res["n_recross"] > 0
    return {"delay": delay, "ratio": ratio, "viol_safe": viol_safe, "viol_cross": viol_cross, "viol_persist": viol_persist, "viol_recross": viol_recross, "lo_margin": res["vmin"] - F_Vlo, "hi_margin": F_Vhi - res["vmax"], "lo_margin_later": res["vmin_later"] - F_Vlo, "hi_margin_later": F_Vhi - res["vmax_later"]}


def _row_record(batch: Batch, meta: dict, res: dict, ev: dict, i: int) -> dict:
    return {
        "polarity": meta["pol"], "input": meta["input"], "set": meta["set_names"][meta["a"][i]], "v0_kind": V0_NAMES[meta["b"][i]], "disturbance": meta["dist_names"][meta["d"][i]],
        "VDD": batch.theta[i, 0], "kn": batch.theta[i, 1], "kp": batch.theta[i, 2], "Vtn": batch.theta[i, 3], "Vtp": batch.theta[i, 4], "C": batch.C[i], "v0": batch.v0[i],
        "s_ns": meta["s"], "tau_ns": meta["tau"], "t_cross_ns": res["t_cross"][i], "delay_ns": ev["delay"][i], "ratio": ev["ratio"][i],
        "vmin": res["vmin"][i], "vmax": res["vmax"][i], "v_at_deadline": res["v_deadline"][i], "min_valid_margin_after_deadline": res["g_after_deadline"][i], "min_valid_margin_after_cross": res["g_after_cross"][i], "n_recross": res["n_recross"][i], "v_final": res["v_final"][i],
        "viol_safe": ev["viol_safe"][i], "viol_cross": ev["viol_cross"][i], "viol_persist": ev["viol_persist"][i], "viol_recross": ev["viol_recross"][i],
    }


ROW_FIELDS = ["polarity", "input", "set", "v0_kind", "disturbance", "VDD", "kn", "kp", "Vtn", "Vtp", "C", "v0", "s_ns", "tau_ns", "t_cross_ns", "delay_ns", "ratio", "vmin", "vmax", "v_at_deadline", "min_valid_margin_after_deadline", "min_valid_margin_after_cross", "n_recross", "v_final", "viol_safe", "viol_cross", "viol_persist", "viol_recross"]


def _run(b: Batch) -> dict:
    return run_batch(b)


def _nanmax(a) -> float:
    """max ignoring NaN; NaN (without a warning) if every entry is NaN."""
    a = np.asarray(a, dtype=float)
    ok = ~np.isnan(a)
    return float(a[ok].max()) if ok.any() else float("nan")


def run_matrix(D: Design, cfg: dict, jobs: int = 1, law=laws.inet_formal, label: str = "formal", eps: float | None = None, taus: tuple | None = None, set_filter=None, dist_filter=None, v0_filter=None, input_filter=None, keep_raw: bool = False) -> dict:
    """Run every (polarity, input) batch and aggregate. Deterministic irrespective of ``jobs``."""
    F = float_design(D)
    batches, metas = [], []
    input_desc = {}
    for pol in ("L", "H"):
        for inp in input_specs(F, pol, cfg["dt"]):
            if input_filter is not None and not input_filter(inp["name"]):
                continue
            b, m = build_batch(D, pol, inp, cfg, law=law, eps=eps, taus=taus, set_filter=set_filter, dist_filter=dist_filter, v0_filter=v0_filter)
            batches.append(b)
            metas.append(m)
            input_desc[f"{pol}/{inp['name']}"] = {"desc": inp["desc"], "spec_kind": inp["spec"]["kind"], "s_ns": inp["s"], "T_end_ns": m["T_end"], "n_steps": m["N"]}
    if jobs > 1:
        with ProcessPoolExecutor(max_workers=jobs) as ex:
            results = list(ex.map(_run, batches))
    else:
        results = [run_batch(b) for b in batches]

    groups, worst, failing, raw = [], [], [], []
    hist_edges = np.linspace(0.0, 1.0, 21)
    hist = {"L": np.zeros(21, dtype=np.int64), "H": np.zeros(21, dtype=np.int64)}
    tot = {"n_runs": 0, "viol_safe": 0, "viol_cross": 0, "viol_persist": 0, "viol_recross": 0}
    per_pol = {p: {"n_runs": 0, "max_ratio": -np.inf, "max_delay_ns": -np.inf, "min_lo_margin_later": np.inf, "min_hi_margin_later": np.inf, "min_lo_margin": np.inf, "min_hi_margin": np.inf, "min_valid_margin_after_deadline": np.inf, "min_valid_margin_after_cross": np.inf, "n_never_crossed": 0, "n_already_valid_at_s": 0} for p in ("L", "H")}
    for b, m, r in zip(batches, metas, results):
        ev = evaluate(b, m, r)
        pol = m["pol"]
        pp = per_pol[pol]
        pp["n_runs"] += m["n"]
        pp["max_ratio"] = max(pp["max_ratio"], _nanmax(ev["ratio"]))
        pp["max_delay_ns"] = max(pp["max_delay_ns"], _nanmax(ev["delay"]))
        pp["n_never_crossed"] += int(np.isnan(ev["delay"]).sum())
        pp["n_already_valid_at_s"] += int((ev["delay"] == 0.0).sum())
        for key, arr in (("min_lo_margin_later", ev["lo_margin_later"]), ("min_hi_margin_later", ev["hi_margin_later"]), ("min_lo_margin", ev["lo_margin"]), ("min_hi_margin", ev["hi_margin"]), ("min_valid_margin_after_deadline", r["g_after_deadline"]), ("min_valid_margin_after_cross", r["g_after_cross"])):
            pp[key] = min(pp[key], float(arr.min()))
        tot["n_runs"] += m["n"]
        for key in ("viol_safe", "viol_cross", "viol_persist", "viol_recross"):
            tot[key] += int(ev[key].sum())
        rr = np.where(np.isnan(ev["ratio"]), 2.0, ev["ratio"])
        moving = rr > 0.0  # runs whose output was already valid at s are counted separately
        hist[pol][:20] += np.histogram(np.clip(rr[moving], 0, 1), bins=hist_edges)[0]
        hist[pol][20] += int((rr > 1.0).sum())
        for di, dname in enumerate(m["dist_names"]):
            sel = m["d"] == di
            if not sel.any():
                continue
            groups.append([
                pol, m["input"], dname, int(sel.sum()),
                int(ev["viol_safe"][sel].sum()), int(ev["viol_cross"][sel].sum()), int(ev["viol_persist"][sel].sum()), int(ev["viol_recross"][sel].sum()),
                _nanmax(ev["ratio"][sel]), _nanmax(ev["delay"][sel]), m["tau"],
                float(ev["lo_margin"][sel].min()), float(ev["hi_margin"][sel].min()), float(ev["lo_margin_later"][sel].min()), float(ev["hi_margin_later"][sel].min()),
                float(r["g_after_deadline"][sel].min()), float(r["g_after_cross"][sel].min()),
            ])
        order = np.argsort(-np.where(np.isnan(ev["ratio"]), np.inf, ev["ratio"]), kind="stable")[:5]
        worst += [_row_record(b, m, r, ev, int(i)) for i in order]
        bad = np.flatnonzero(ev["viol_safe"] | ev["viol_cross"] | ev["viol_persist"] | ev["viol_recross"])
        failing += [_row_record(b, m, r, ev, int(i)) for i in bad[:200]]
        if keep_raw:
            raw.append({"meta": m, "batch": b, "res": r, "ev": ev})
    worst.sort(key=lambda x: (-(x["ratio"] if not math.isnan(x["ratio"]) else math.inf), x["polarity"], x["input"]))
    out = {
        "label": label,
        "totals": tot,
        "per_polarity": per_pol,
        "group_header": ["polarity", "input", "disturbance", "n_runs", "n_viol_safe_domain", "n_viol_crossing_by_bound", "n_viol_persistence", "n_recrossed_after_first_crossing", "max_ratio_delay_over_tau", "max_delay_ns", "tau_ns", "min_vmin_minus_Vlo", "min_Vhi_minus_vmax", "min_vmin_minus_Vlo_after_t0", "min_Vhi_minus_vmax_after_t0", "min_valid_margin_after_deadline_V", "min_valid_margin_after_first_cross_V"],
        "groups": groups,
        "worst": worst[:40],
        "failing": failing,
        "n_failing_total": int(sum(tot[k] for k in ("viol_safe", "viol_cross", "viol_persist", "viol_recross"))),
        "ratio_hist": {"bin_edges": hist_edges.tolist() + ["> 1 or never crossed"], "L": hist["L"].tolist(), "H": hist["H"].tolist(), "note": "runs whose output was already valid when the input became valid (delay 0) are excluded from the bins and counted in per_polarity.n_already_valid_at_s"},
        "inputs": input_desc,
        "n_batches": len(batches),
    }
    if keep_raw:
        out["raw"] = raw
    return out
