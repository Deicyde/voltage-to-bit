#!/usr/bin/env python3
"""ngspice runner for the model comparison.   STATUS: PROPOSED, NOT RUN.

This script has never been executed against ngspice: ngspice is not installed on
the machine it was written on and installing it is the owner's decision. What HAS
been exercised is listed under "--self-test" below; nothing else.

    .venv/bin/python experiments/ngspice/run_ngspice.py --dry-run      # list what would run (no ngspice needed)
    .venv/bin/python experiments/ngspice/run_ngspice.py --self-test    # parser/comparator plumbing on synthetic files
    .venv/bin/python experiments/ngspice/run_ngspice.py --part a       # needs ngspice on PATH
    SKY130_PR=/path/to/skywater-pdk-libs-sky130_fd_pr .venv/bin/python experiments/ngspice/run_ngspice.py --part b   # needs ngspice + model files

Part (a): MOS Level 1 with LAMBDA=0, GAMMA=0, matched to the formal model. A units,
    sign-convention and harness cross-check of the Python simulator. Not physical evidence.
Part (b): the higher-fidelity open model recommended by workstream B in docs/model.md
    section 9 (SKY130 BSIM4 nfet_01v8 / pfet_01v8_hvt; not yet frozen in the interface).
    Renders and runs the DC maps and transients over corners x supplies x temperatures;
    the comparison itself (sandwich residual against the parameter-box tube, the four
    margins on the SPICE map, delays and excursions) is specified in compare_plan.json
    and is not automated yet.

What exactly is compared, and the pass criteria for (a), are in
evidence/experiments/<run-id>/08_ngspice_PROPOSED_NOT_RUN/compare_plan.json.

--self-test writes files in ngspice `wrdata` layout from the PYTHON model and feeds
them through the same parser and comparison code. It proves only that the plumbing
is consistent with the layout this script ASSUMES (`set wr_singlescale`, `set
wr_vecnames`: one header line, then rows "scale value value ..."). VERIFY ON FIRST
RUN that the installed ngspice writes that layout.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from v2b import laws, spice  # noqa: E402
from v2b.common import corner_array, float_design, write_json  # noqa: E402
from v2b.design import THETA_KEYS, corner_by_code, load_design, tau_dn, tau_up  # noqa: E402
from v2b.sim import make_rhs, solve_ref  # noqa: E402

REPO = HERE.parent.parent
STATUS = "PROPOSED, NOT RUN"


def parse_wrdata(path: Path) -> np.ndarray:
    """Rows of floats; header / blank lines are skipped."""
    rows = []
    for line in path.read_text().splitlines():
        parts = line.split()
        try:
            rows.append([float(x) for x in parts])
        except ValueError:
            continue
    rows = [r for r in rows if r]
    return np.array(rows, dtype=float)


def run_deck(ngspice: str, deck: Path, workdir: Path, timeout: int = 900) -> None:
    log = workdir / (deck.stem + ".log")
    r = subprocess.run([ngspice, "-b", deck.name, "-o", log.name], cwd=workdir, capture_output=True, text=True, timeout=timeout)
    if r.returncode != 0:
        raise RuntimeError(f"ngspice failed on {deck.name}: see {log}")


def compare_level1_dc(data: np.ndarray, th) -> dict:
    """data columns: v(out) sweep, i(VOUT) [A], v(in) [V]."""
    v, i_uA, u = data[:, 0], 1e6 * data[:, 1], data[:, 2]
    r = i_uA - laws.inet_formal(u, v, *th)
    k = int(np.abs(r).argmax())
    return {"n_points": int(v.size), "max_abs_residual_uA": float(np.abs(r).max()), "at_u_V": float(u[k]), "at_v_V": float(v[k]), "harness_check_passes (< 1e-3 uA)": bool(np.abs(r).max() < 1e-3)}


def crossing(t_ns: np.ndarray, v: np.ndarray, thr: float, sgn: int, t_from: float) -> float | None:
    g = sgn * (v - thr)
    m = t_ns >= t_from
    idx = np.flatnonzero(m)
    if idx.size == 0:
        return None
    if g[idx[0]] >= 0:
        return float(t_ns[idx[0]])
    for j in idx[1:]:
        if g[j] >= 0 > g[j - 1]:
            return float(t_ns[j - 1] + (t_ns[j] - t_ns[j - 1]) * (-g[j - 1]) / (g[j] - g[j - 1]))
    return None


def python_level1_tran(D, th, pol: str, slew: float = 2.0, t_grid_ns=None) -> dict:
    """The Python reference for the Level-1 transient deck (same theta, C, u(t), w, v(0))."""
    F = float_design(D)
    hold = 0.05
    start, edge = (F.VDD_hi, F.VIL) if pol == "L" else (0.0, F.VIH)
    s = hold + abs(start - edge) / slew
    u_fun = lambda t: start if t <= hold else (edge if t >= s else start + (edge - start) * (t - hold) / (s - hold))  # noqa: E731
    w = -F.eps if pol == "L" else F.eps
    tau = float(tau_up(D) if pol == "L" else tau_dn(D))
    t_end = s + 1.25 * tau + 0.5
    rhs = make_rhs(laws.inet_formal, th, F.C_hi, u_fun, lambda t: w)
    sgn, thr = (1, F.VOH) if pol == "L" else (-1, F.VOL)
    tt = np.linspace(0.0, t_end, 2001) if t_grid_ns is None else t_grid_ns
    r = solve_ref(rhs, F.Vlo if pol == "L" else F.Vhi, t_end, rtol=1e-12, atol=1e-14, breaks=[hold, s], Vth=thr, sgn=sgn, t_from=s, dense_t=tt)
    return {"s_ns": s, "t_cross_ns": r["t_cross"], "t_ns": r["t"], "v": r["v"], "thr": thr, "sgn": sgn, "t_end": t_end}


def compare_level1_tran(data: np.ndarray, D, th, pol: str) -> dict:
    """data columns: time [s], v(out), v(in)."""
    t_ns, v = 1e9 * data[:, 0], data[:, 1]
    ref = python_level1_tran(D, th, pol, t_grid_ns=t_ns[t_ns <= t_ns[-1]])
    tc = crossing(t_ns, v, ref["thr"], ref["sgn"], ref["s_ns"])
    n = min(v.size, ref["v"].size)
    return {"spice_delay_ns": None if tc is None else tc - ref["s_ns"], "python_delay_ns": ref["t_cross_ns"] - ref["s_ns"], "delay_difference_ns": None if tc is None else tc - ref["t_cross_ns"], "max_abs_waveform_difference_V": float(np.abs(v[:n] - ref["v"][:n]).max())}


def self_test(D, work: Path) -> dict:
    """NO SPICE INVOLVED: synthesise wrdata-layout files from the Python model and run them through the pipeline."""
    F = float_design(D)
    out = {"status": "harness self-test only; no SPICE was run"}
    th = [0.5 * (F.lo(k) + F.hi(k)) for k in THETA_KEYS]
    vv = np.arange(F.Vlo, F.Vhi + 1e-9, 0.02)
    uu = np.arange(F.Vlo - 0.4, F.Vhi + 0.4 + 1e-9, 0.05)
    lines = [" v-sweep i(vout) v(in)"]
    for u in uu:  # outer sweep = VIN, inner = VOUT, as in the deck
        for v in vv:
            lines.append(f" {v:.12e} {1e-6 * float(laws.inet_formal(u, v, *th)):.12e} {u:.12e}")
    f = work / "selftest_dc.dat"
    f.write_text("\n".join(lines) + "\n")
    out["dc"] = compare_level1_dc(parse_wrdata(f), th)
    ref = python_level1_tran(D, th, "L")
    lines = [" time v(out) v(in)"] + [f" {1e-9 * t:.12e} {v:.12e} 0" for t, v in zip(ref["t_ns"], ref["v"])]
    f = work / "selftest_tran.dat"
    f.write_text("\n".join(lines) + "\n")
    out["tran"] = compare_level1_tran(parse_wrdata(f), D, th, "L")
    out["passes"] = bool(out["dc"]["max_abs_residual_uA"] < 1e-6 and abs(out["tran"]["delay_difference_ns"]) < 1e-4)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--design", default=str(REPO / "designs" / "illustrative-1v8.json"))
    ap.add_argument("--work", default=str(HERE / "work"), help="scratch directory for rendered decks and raw ngspice output (git-ignored content; keep small)")
    ap.add_argument("--part", choices=("a", "b"), default="a")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--out", default=None, help="where to write results.json (default: the work directory)")
    args = ap.parse_args()

    D = load_design(args.design)
    F = float_design(D)
    codes, Cn = corner_array(D)
    work = Path(args.work)

    if args.self_test:
        work.mkdir(parents=True, exist_ok=True)
        res = self_test(D, work)
        print(json.dumps(res, indent=1))
        for f in ("selftest_dc.dat", "selftest_tran.dat"):
            (work / f).unlink(missing_ok=True)
        return 0 if res["passes"] else 1

    jobs = []
    if args.part == "a":
        for code, th in zip(codes, Cn):
            jobs.append(("level1_dc", code, [float(x) for x in th], None))
        for pol in ("L", "H"):
            for code, th in zip(codes, Cn):
                jobs.append(("level1_tran", code, [float(x) for x in th], pol))
    else:
        for corner in ("tt", "ss", "ff", "sf", "fs"):
            for temp in (-40.0, 27.0, 100.0):
                for vdd in (F.VDD_lo, 0.5 * (F.VDD_lo + F.VDD_hi), F.VDD_hi):
                    jobs.append(("sky130_dc", corner, vdd, (temp,)))
                    for pol in ("L", "H"):
                        for c in (F.C_lo, F.C_hi):
                            jobs.append(("sky130_tran", corner, vdd, (temp, pol, c)))

    if args.dry_run:
        print(f"STATUS: {STATUS}. {len(jobs)} decks would be rendered into {work} and run with `ngspice -b`:")
        for j in jobs[:6]:
            print("   ", j[0], j[1], j[2] if not isinstance(j[2], list) else "", j[3] or "")
        print("    ...")
        print(json.dumps(spice.compare_plan(D)["a_level1_matched" if args.part == "a" else "b_higher_fidelity (tier T3)"], indent=1))
        return 0

    ngspice = shutil.which("ngspice")
    if ngspice is None:
        print("NOT RUN: ngspice is not on PATH. Installing it is the owner's decision; this script will not do it.")
        return 3

    work.mkdir(parents=True, exist_ok=True)
    version = subprocess.run([ngspice, "--version"], capture_output=True, text=True).stdout.strip().splitlines()[:2]
    results = {"status": "RUN", "ngspice": version, "design_sha256": D.sha256, "part": args.part, "dc": [], "tran": []}
    if args.part == "a":
        for kind, code, th, pol in jobs:
            if kind == "level1_dc":
                deck = work / f"level1_dc_{code}.cir"
                deck.write_text(spice.level1_dc(D, code, th))
                run_deck(ngspice, deck, work)
                results["dc"].append({"corner": code} | compare_level1_dc(parse_wrdata(work / f"level1_dc_{code}.dat"), th))
            else:
                name = f"level1_tran_{'rise' if pol == 'L' else 'fall'}_{code}"
                deck = work / f"{name}.cir"
                deck.write_text(spice.level1_tran(D, code, th, pol))
                run_deck(ngspice, deck, work)
                results["tran"].append({"corner": code, "transition": "rise" if pol == "L" else "fall"} | compare_level1_tran(parse_wrdata(work / f"{name}.dat"), D, th, pol))
    else:
        # Part (b) is deliberately left at "render and run"; the residual fit reuses
        # v2b.sensitivity.best_fit_residual once the model and its sizes are fixed by workstream B.
        pdk = os.environ.get("SKY130_PR")
        if not pdk:
            print("NOT RUN: part (b) needs the pinned model files; set SKY130_PR to a checkout of skywater-pdk-libs-sky130_fd_pr (docs/model.md 9.2).")
            return 3
        for kind, corner, vdd, extra in jobs:
            if kind == "sky130_dc":
                (temp,) = extra
                deck = work / f"sky130_dc_{corner}_{vdd:g}_{temp:g}.cir"
                text = spice.sky130_dc(D, vdd, corner, temp)
            else:
                temp, pol, c = extra
                deck = work / f"sky130_tran_{pol}_{corner}_{vdd:g}_{temp:g}_{c:g}.cir"
                text = spice.sky130_tran(D, vdd, pol, c, corner=corner, temp=temp)
            deck.write_text(text.replace("SKY130_PR_PLACEHOLDER", pdk))
            run_deck(ngspice, deck, work)
        results["note"] = "raw outputs written; comparison for part (b) is specified in compare_plan.json and not yet automated"
    out = Path(args.out) if args.out else work
    write_json(out / f"ngspice_part_{args.part}_results.json", results)
    print(f"wrote {out / f'ngspice_part_{args.part}_results.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
