"""Compact results: summary tables (Markdown + JSON) and two small SVG plots.

Everything here is derived from the record file and the numerics file; it adds
no information of its own. Plots are written as plain SVG with the standard
library, so they are byte-for-byte reproducible.
"""
from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

from . import exact, leanio, numeric
from .exact import Design, dec_str


# ------------------------------------------------------------------ summary

def _accepted(recs):
    return [r for r in recs if r["decision"] == "accepted"]


def _check(rec, role):
    for c in rec["formal_checks"]:
        if c["role"] == role:
            return c
    return None


def _deadline_summary(direction: str, recs: list[dict], num: dict) -> dict:
    acc = _accepted(recs)
    base, best = acc[0], acc[-1]
    worst = num["worst_case"]["worst_case_delay_ns"]
    limit = num["certificate_infimum_ns"]
    series = []
    for r in recs:
        name = r["proposer"]["name"]
        claim = _check(r, "claim")
        if name in ("baseline", "library-prior", "uniform-grid", "dp-grid") and claim and claim["passed"]:
            series.append({"record_id": r["record_id"], "proposer": name,
                           "levels": len(r["proposal"]["levels"]), "tau_ns": r["proposal"]["tau"],
                           "exact_sum_ns": float(Fraction(r["screen"]["exact_sum"])),
                           "decision": r["decision"]})
    floor = None
    proved = [r for r in recs if _check(r, "counterexample") and _check(r, "counterexample")["passed"]]
    proved.sort(key=lambda r: "pred-typical" not in r["record_id"])    # cite the predictor's record
    if proved:
        c = _check(proved[0], "counterexample")
        floor = {"record_id": proved[0]["record_id"], "lean_file": c["lean_file"],
                 "theorems": c["theorems"], "value_ns": dec_str(leanio.FLOOR[direction])}
    b, s = Fraction(base["proposal"]["tau"]), Fraction(best["proposal"]["tau"])
    prior = None
    for r in acc:
        if r["proposer"]["name"] == "library-prior":
            t = Fraction(r["proposal"]["tau"])
            prior = {"record_id": r["record_id"], "tau_ns": r["proposal"]["tau"],
                     "source": r["proposer"]["params"]["source"],
                     "reduction_percent": round(float((t - s) / t) * 100, 2)}
    return {
        "library_prior": prior,
        "baseline": {"record_id": base["record_id"], "tau_ns": base["proposal"]["tau"],
                     "exact_sum": base["screen"]["exact_sum"], "levels": base["proposal"]["levels"]},
        "best": {"record_id": best["record_id"], "tau_ns": best["proposal"]["tau"],
                 "tau_as_fraction": exact.frac_str(s),
                 "exact_sum": best["screen"]["exact_sum"],
                 "exact_sum_decimal": best["screen"]["exact_sum_decimal"],
                 "levels": best["proposal"]["levels"],
                 "lean_file": _check(best, "claim")["lean_file"]},
        "accepted_chain": [{"record_id": r["record_id"], "tau_ns": r["proposal"]["tau"],
                            "levels": len(r["proposal"]["levels"])} for r in acc],
        "reduction_percent": round(float((b - s) / b) * 100, 2),
        "model_worst_case_delay_ns": worst,
        "moving_parameter_worst_case_delay_ns": num["moving_parameter_worst_case_delay_ns"],
        "worst_corner": num["worst_case"]["worst_corner"],
        "certificate_method_limit_ns": limit,
        "best_minus_worst_case_ns": float(s) - worst,
        "method_limit_minus_worst_case_ns": limit - worst,
        "lean_floor": floor,
        "series": series,
    }


def _eps_summary(recs: list[dict], num: dict) -> dict:
    acc = _accepted(recs)
    base, best = acc[0], acc[-1]
    ceiling = None
    for r in recs:
        c = _check(r, "refutation")
        if c and c["passed"] and any(t.endswith("_no_split_points") for t in c["theorems"]):
            ceiling = {"record_id": r["record_id"], "lean_file": c["lean_file"],
                       "statement": c["statement"]}
            break
    return {
        "baseline": {"record_id": base["record_id"], **{k: base["proposal"][k] for k in ("eps", "uHi", "uLo")}},
        "best": {"record_id": best["record_id"], **{k: best["proposal"][k] for k in ("eps", "uHi", "uLo")},
                 "lean_file": _check(best, "claim")["lean_file"],
                 "variant_tauUp_ns": best["numerical_evidence"]["variant_tauUp_ns"],
                 "variant_tauDn_ns": best["numerical_evidence"]["variant_tauDn_ns"],
                 "closed_form_margins_uA": best["numerical_evidence"]["closed_form_margins_uA"]},
        "accepted_chain": [{"record_id": r["record_id"],
                            **{k: r["proposal"][k] for k in ("eps", "uHi", "uLo")}} for r in acc],
        "lean_ceiling": ceiling,
        "model_boundary_currents": num["boundary_margins"],
    }


def build(D: Design, records: list[dict], num: dict, promotion: dict, meta: dict) -> dict:
    by = {}
    for r in records:
        by.setdefault(r["experiment_id"], []).append(r)
    not_accepted = []
    for r in records:
        if r["decision"] == "accepted":
            continue
        claim = _check(r, "claim")
        not_accepted.append({
            "record_id": r["record_id"], "proposer": r["proposer"]["name"],
            "claim": _claim_short(r), "decision": r["decision"], "reason_code": r["reason_code"],
            "rejected_by": r["rejected_by"], "screen_detail": r["screen"]["detail"],
            "lean_error": claim["first_error"] if claim else None,
            "refutation_proved": bool(_check(r, "refutation") and _check(r, "refutation")["passed"]),
            "counterexample_proved": bool(_check(r, "counterexample")
                                          and _check(r, "counterexample")["passed"]),
        })
    counts = {}
    for r in records:
        counts[r["decision"]] = counts.get(r["decision"], 0) + 1
    return {
        "meta": meta,
        "counts": {"records": len(records), **counts,
                   "formal_checks_run": sum(len(r["formal_checks"]) for r in records)},
        "rise": _deadline_summary("rise", by["rise-deadline"], num["rise"]),
        "fall": _deadline_summary("fall", by["fall-deadline"], num["fall"]),
        "eps": _eps_summary(by["eps-tolerance"], num),
        "not_accepted": not_accepted,
        "promotion_candidates": {
            key: {k: v for k, v in res.items()
                  if k not in ("role", "error_count", "warning_count", "first_error",
                               "unsolved_cases", "output_file")}
            for key, res in promotion.items()},
        "predictions": {d: num[d]["predictions"] for d in ("rise", "fall")},
    }


def _claim_short(r: dict) -> str:
    p = r["proposal"]
    if p["kind"] == "eps_split":
        return f"eps = {p['eps']}, uHi = {p['uHi']}, uLo = {p['uLo']}"
    n = len(p["levels"])
    shown = ", ".join(p["levels"]) if n <= 5 else f"{n} levels"
    return f"[{shown}], tau = {p['tau']}"


# ----------------------------------------------------------------- markdown

def _md_table(head: list[str], rows: list[list]) -> str:
    out = ["| " + " | ".join(head) + " |", "| " + " | ".join("---" for _ in head) + " |"]
    out += ["| " + " | ".join(str(c) for c in row) + " |" for row in rows]
    return "\n".join(out)


def _f(x: float, n: int = 4) -> str:
    return f"{x:.{n}f}"


def markdown(summary: dict, records: list[dict]) -> str:
    """The summary as Markdown: a list of blocks joined by blank lines."""
    s, m = summary, summary["meta"]
    B: list[str] = []
    B.append("# Search results (workstream F)")
    B.append("GENERATED by `python3 search/run_search.py`. Do not edit; regenerate.")
    B.append(
        f"- Lean library: commit `{m['lean_commit']}` (frozen checkout)\n"
        f"- Design record: `designs/illustrative-1v8.json`, sha256 `{m['design_sha256']}` "
        "(ILLUSTRATIVE numbers; V, µA, fF, ns)\n"
        f"- Record file: `evidence/search/records.jsonl`, sha256 `{m['records_sha256']}`\n"
        f"- {s['counts']['records']} records: {s['counts'].get('accepted', 0)} accepted, "
        f"{s['counts'].get('rejected', 0)} rejected, "
        f"{s['counts'].get('counterexample', 0)} counterexample; "
        f"{s['counts']['formal_checks_run']} Lean checks in the record "
        f"(plus {len(s['promotion_candidates'])} for the packaging files of section 6)")
    B.append(
        "\"Proved\" means: Lean accepted the statement against the frozen commit, with no axiom "
        "beyond `propext`, `Classical.choice`, `Quot.sound`. \"Numerical\" means floating-point "
        "quadrature of the same model: evidence, not proof. Nothing here is evidence about a "
        "physical device.")

    B.append("## 1. Proved deadlines: baseline versus best accepted")
    rows = []
    for d in ("rise", "fall"):
        x = s[d]
        rows.append([d,
                     f"{x['baseline']['exact_sum']} ≈ {_f(float(Fraction(x['baseline']['exact_sum'])), 6)}",
                     x["baseline"]["tau_ns"],
                     f"{x['best']['tau_ns']} = {x['best']['tau_as_fraction']}",
                     len(x["best"]["levels"]),
                     f"−{x['reduction_percent']} %",
                     _f(x["certificate_method_limit_ns"], 6),
                     _f(x["model_worst_case_delay_ns"], 6),
                     x["lean_floor"]["value_ns"] if x["lean_floor"] else "—"])
    B.append(_md_table(["direction", "baseline, exact (ns)", "baseline, proved τ (ns)",
                        "best proved τ (ns)", "levels", "change",
                        "limit of the certificate method (numerical, ns)",
                        "model worst-case delay (numerical, ns)",
                        "Lean-proved floor on any valid deadline (ns)"], rows))
    for d in ("rise", "fall"):
        x = s[d]
        B.append(f"**{d}.** Best certificate: record `{x['best']['record_id']}`, file "
                 f"`{x['best']['lean_file']}`. Its exact sum is ≈ {x['best']['exact_sum_decimal']} ns "
                 "(the exact fraction is in the record and in the Lean file).")
        B.append(f"Levels (V): `[{', '.join(x['best']['levels'])}]`")
        if x["library_prior"]:
            pr = x["library_prior"]
            B.append(f"The frozen library already contained a certificate for this direction "
                     f"(`{pr['source']}`, τ = {pr['tau_ns']} ns, re-checked here as "
                     f"`{pr['record_id']}`). Measured against that, the best accepted τ is "
                     f"{pr['reduction_percent']} % smaller; the \"change\" column above is measured "
                     "against the single-segment deadline of the headline guarantee.")
        else:
            B.append("The frozen library contained no certificate for this direction; the "
                     "single-segment deadline was the only proved one.")
        corner = ", ".join(f"{k} = {v:g}" for k, v in x["worst_corner"].items())
        B.append(f"The best proved τ is {_f(x['best_minus_worst_case_ns'], 6)} ns above the model's "
                 f"numerical worst-case delay (slowest corner: {corner}). The limit of the "
                 f"certificate method is {_f(x['method_limit_minus_worst_case_ns'], 6)} ns above it. "
                 "At the frozen commit the parameters are constant during a run; if the parameter "
                 "point could move inside the box during a run, the numerical worst case would be "
                 f"{_f(x['moving_parameter_worst_case_delay_ns'], 6)} ns.")
        if x["lean_floor"]:
            B.append(f"Floor: `{x['lean_floor']['lean_file']}` proves "
                     + ", ".join(f"`{t}`" for t in x["lean_floor"]["theorems"][:3])
                     + f": no {d} deadline below {x['lean_floor']['value_ns']} ns is valid for "
                     "this model, whoever proposes it.")

    B.append("## 2. Proved deadline against certificate size")
    for d in ("rise", "fall"):
        rows = [[r["levels"], r["proposer"], r["tau_ns"], _f(r["exact_sum_ns"], 7), r["decision"],
                 f"`{r['record_id']}`"] for r in s[d]["series"]]
        B.append(f"{d}:")
        B.append(_md_table(["levels", "proposer", "proved τ (ns)", "exact sum (ns)", "decision",
                            "record"], rows))
    B.append("All rows are Lean-checked valid certificates. `rejected` in these two tables means "
             "\"valid, but not better than the incumbent at that point of the run\".")

    B.append("## 3. Disturbance bound provable by changing only the split points")
    e = s["eps"]
    rows = [[f"`{r['record_id']}`", r["eps"], r["uHi"], r["uLo"]] for r in e["accepted_chain"]]
    B.append(_md_table(["accepted record", "eps (µA)", "uHi (V)", "uLo (V)"], rows))
    b = e["best"]
    B.append(f"Best: eps = {b['eps']} µA with uHi = {b['uHi']}, uLo = {b['uLo']} "
             f"(`{b['lean_file']}`). Closed-form margins of that variant record (µA): "
             + ", ".join(f"{k} = {_f(v, 6)}" for k, v in b["closed_form_margins_uA"].items()) + ".")
    B.append("This changes the claim. The variant record's own closed-form deadlines are "
             f"tauUp ≈ {_f(b['variant_tauUp_ns'])} ns and tauDn ≈ {_f(b['variant_tauDn_ns'])} ns, "
             "longer than for eps = 2. The result reads \"the proof supports a larger disturbance "
             "bound for the same circuit\"; it is not an improvement of the eps = 2 guarantee.")
    if e["lean_ceiling"]:
        B.append(f"Ceiling: `{e['lean_ceiling']['lean_file']}` proves that "
                 f"{e['lean_ceiling']['statement'].split('; and ')[-1]}. This is a limit of the "
                 "closed-form margins, not evidence that the circuit fails at that eps.")
    bm = e["model_boundary_currents"]
    B.append(f"Numerical: over the box and all inputs, the model's own smallest restoring current "
             f"is {_f(bm['Vhi']['min_inward_current_uA'], 3)} µA at Vhi "
             f"(at u ≈ {_f(bm['Vhi']['at_u_V'], 3)} V) and "
             f"{_f(bm['Vlo']['min_inward_current_uA'], 3)} µA at Vlo "
             f"(at u ≈ {_f(bm['Vlo']['at_u_V'], 3)} V). The closed-form margins give up more than "
             "half of it, and no choice of split points recovers that.")

    B.append("## 4. Proposals that were not accepted")
    rows = []
    for r in s["not_accepted"]:
        extra = []
        if r["refutation_proved"]:
            extra.append("negation proved")
        if r["counterexample_proved"]:
            extra.append("violating trajectory proved")
        rows.append([f"`{r['record_id']}`", r["proposer"], r["claim"], r["decision"],
                     " + ".join(r["rejected_by"]), r["reason_code"],
                     (r["screen_detail"] or "—").replace("|", "/"), ", ".join(extra) or "—"])
    B.append(_md_table(["record", "proposer", "claim", "decision", "rejected by", "reason code",
                        "what is wrong (exact screen)", "Lean follow-up"], rows))
    B.append("\"screen (bypassed) + lean\": the screen found the claim invalid, the claim was sent "
             "to Lean anyway, and Lean rejected it by itself. The Lean error text of every rejected "
             "claim is in `search/out/<record>.claim.out`; its first message is in the record "
             "(`formal_checks[0].first_error`).")

    B.append("## 5. Predictions from simulations of non-worst-case circuits (numerical)")
    rows = []
    for d in ("rise", "fall"):
        p = s["predictions"][d]
        rows.append([d, _f(p["typical"]["delay_ns"]), _f(p["nominal_devices"]["delay_ns"]),
                     _f(s[d]["model_worst_case_delay_ns"]), s[d]["best"]["tau_ns"]])
    B.append(_md_table(["direction", "typical circuit (ns)", "nominal devices, adverse stimulus (ns)",
                        "model worst case (ns)", "best proved τ (ns)"], rows))

    B.append("## 6. Promotion candidates")
    pc = s["promotion_candidates"]["deadlines"]
    B.append(f"The accepted improvement: `{pc['lean_file']}` (sha256 `{pc['lean_file_sha256']}`), "
             f"checked with `{pc['command']}`: exit status {pc['exit_status']}, "
             f"{'passed' if pc['passed'] else 'FAILED'}. Theorems: "
             + ", ".join(f"`{t}`" for t in pc["theorems"])
             + f". Deadlines: rise {pc['rise_tau']} ns, fall {pc['fall_tau']} ns "
             f"(records `{pc['rise_record']}`, `{pc['fall_record']}`).")
    pc = s["promotion_candidates"]["limits"]
    B.append(f"Limits (not improvements): `{pc['lean_file']}` (sha256 `{pc['lean_file_sha256']}`), "
             f"exit status {pc['exit_status']}, {'passed' if pc['passed'] else 'FAILED'}. Theorems: "
             + ", ".join(f"`{t}`" for t in pc["theorems"]) + ".")

    B.append("## 7. What did and did not change")
    B.append("- Improved: two proved bounds (the rise and fall deadlines) for the same model under "
             "the same assumptions; and, as a separate claim, the disturbance bound the proof "
             "supports.\n"
             "- Unchanged: the circuit, the parameter box, the thresholds, the safe domain, the "
             "capacitance range, the device law, the model's fidelity, and the physical evidence "
             "(there is none: the numbers are illustrative).")
    return "\n\n".join(B) + "\n"


# ---------------------------------------------------------------------- SVG

class Svg:
    def __init__(self, width: int, height: int):
        self.w, self.h = width, height
        self.items = [f'<rect x="0" y="0" width="{width}" height="{height}" fill="white"/>']

    def add(self, s: str):
        self.items.append(s)

    def text(self, x, y, s, size=11, anchor="start", color="#222", rotate=None):
        tr = f' transform="rotate({rotate} {x:.1f} {y:.1f})"' if rotate is not None else ""
        s = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" font-family="Helvetica, Arial, sans-serif" '
                 f'font-size="{size}" text-anchor="{anchor}" fill="{color}"{tr}>{s}</text>')

    def line(self, x1, y1, x2, y2, color="#222", width=1.0, dash=None):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        self.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{color}" '
                 f'stroke-width="{width}"{d}/>')

    def poly(self, pts, color, width=1.6, dash=None):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        p = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
        self.add(f'<polyline points="{p}" fill="none" stroke="{color}" stroke-width="{width}"{d}/>')

    def dot(self, x, y, color, r=3.5, hollow=False):
        fill = "white" if hollow else color
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}" stroke="{color}" '
                 'stroke-width="1.4"/>')

    def render(self) -> str:
        return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
                f'viewBox="0 0 {self.w} {self.h}">\n' + "\n".join(self.items) + "\n</svg>\n")


def plot_gap(summary: dict) -> str:
    """Proved deadline minus the model's numerical worst-case delay, against
    the number of certificate levels (both axes logarithmic)."""
    svg = Svg(640, 400)
    x0, y0, w, h = 70, 40, 540, 300
    lx = lambda n: x0 + w * math.log2(n) / 6.0
    lo, hi = math.log10(0.001), math.log10(2.0)
    ly = lambda g: y0 + h * (hi - math.log10(g)) / (hi - lo)
    svg.text(x0, 22, "Proved deadline minus the model's worst-case delay", 13)
    svg.line(x0, y0, x0, y0 + h)
    svg.line(x0, y0 + h, x0 + w, y0 + h)
    for n in (1, 2, 4, 8, 16, 32, 64):
        svg.line(lx(n), y0 + h, lx(n), y0 + h + 4)
        svg.text(lx(n), y0 + h + 17, str(n), anchor="middle")
    for g in (0.001, 0.01, 0.1, 1.0):
        svg.line(x0 - 4, ly(g), x0 + w, ly(g), color="#ddd")
        svg.text(x0 - 8, ly(g) + 4, f"{g:g}", anchor="end")
    svg.text(x0 + w / 2, y0 + h + 38, "certificate levels N", anchor="middle")
    svg.text(18, y0 + h / 2, "proved τ − worst case (ns)", anchor="middle", rotate=-90)
    colors = {"rise": "#1f6fb4", "fall": "#d1601a"}
    for i, d in enumerate(("rise", "fall")):
        x = summary[d]
        worst = x["model_worst_case_delay_ns"]
        for name, hollow in (("uniform-grid", True), ("dp-grid", False)):
            pts = [(lx(r["levels"]), ly(max(float(Fraction(r["tau_ns"])) - worst, 1e-3)))
                   for r in x["series"] if r["proposer"] in (name, "baseline")]
            pts.sort()
            svg.poly(pts, colors[d], dash="4 3" if hollow else None)
            for px, py in pts:
                svg.dot(px, py, colors[d], hollow=hollow)
        gap = x["method_limit_minus_worst_case_ns"]
        if gap > 1e-3:
            svg.line(x0, ly(gap), x0 + w, ly(gap), color=colors[d], dash="2 3")
            svg.text(x0 + w - 4, ly(gap) + 13, f"{d}: limit of the method, {gap:.4f} ns above "
                     "the worst case", anchor="end", color=colors[d], size=10)
        yk = y0 + 14 + 30 * i
        svg.dot(x0 + w - 200, yk, colors[d])
        svg.text(x0 + w - 190, yk + 4, f"{d}, grid-optimal levels (dp-grid)", size=10)
        svg.dot(x0 + w - 200, yk + 14, colors[d], hollow=True)
        svg.text(x0 + w - 190, yk + 18, f"{d}, equally spaced levels", size=10)
    svg.text(x0 + 8, y0 + h - 8, "rise: the limit of the method is the worst case itself "
             "(the gap tends to 0)", color=colors["rise"], size=10)
    svg.text(x0, y0 + h + 54, "Every point is a Lean-checked certificate; the worst-case delay is "
             "numerical (quadrature). N = 1 is the baseline.", size=10, color="#555")
    return svg.render()


def plot_eps(D: Design, summary: dict) -> str:
    """Upper-boundary margins as functions of the split point uHi, and the
    model's own restoring current at Vhi as a function of the input."""
    svg = Svg(640, 400)
    x0, y0, w, h = 60, 40, 550, 300
    xa, xb, ya, yb = 0.55, 1.00, 0.0, 8.0
    X = lambda x: x0 + w * (x - xa) / (xb - xa)
    Y = lambda y: y0 + h * (yb - min(max(y, ya), yb)) / (yb - ya)
    svg.text(x0, 22, "Restoring current at the top of the safe domain (v = Vhi)", 13)
    svg.line(x0, y0, x0, y0 + h)
    svg.line(x0, y0 + h, x0 + w, y0 + h)
    for i in range(10):
        x = 0.55 + 0.05 * i
        svg.line(X(x), y0 + h, X(x), y0 + h + 4)
        svg.text(X(x), y0 + h + 17, f"{x:.2f}", anchor="middle")
    for y in range(0, 9, 2):
        svg.line(x0 - 4, Y(y), x0 + w, Y(y), color="#ddd")
        svg.text(x0 - 8, Y(y) + 4, str(y), anchor="end")
    svg.text(x0 + w / 2, y0 + h + 38, "input u, or split point uHi (V)", anchor="middle")
    svg.text(16, y0 + h / 2, "current (µA)", anchor="middle", rotate=-90)
    xs = [xa + (xb - xa) * i / 300 for i in range(301)]

    def margins(x):
        E = D.replace(uHi=f"{x:.6f}")
        return float(exact.RhiP(E)), float(exact.RhiN(E))

    mp = [margins(x) for x in xs]
    svg.poly([(X(x), Y(p)) for x, (p, n) in zip(xs, mp) if ya <= p <= yb], "#1f6fb4")
    svg.poly([(X(x), Y(n)) for x, (p, n) in zip(xs, mp) if ya <= n <= yb], "#d1601a")
    corners = numeric.corners(D)
    vhi = float(D.Vhi)
    model = [min(-numeric.inet(th, x, vhi) for th in corners) for x in xs]
    svg.poly([(X(x), Y(m)) for x, m in zip(xs, model) if ya <= m <= yb], "#2a8a3c", width=2.0)
    e = summary["eps"]
    for label, val, color in (("eps = %s (record)" % e["baseline"]["eps"], float(e["baseline"]["eps"]), "#888"),
                              ("eps = %s (best proved)" % e["best"]["eps"], float(e["best"]["eps"]), "#222")):
        svg.line(x0, Y(val), x0 + w, Y(val), color=color, dash="5 3")
        svg.text(x0 + w - 4, Y(val) - 4 if val > 2.2 else Y(val) + 13, label, anchor="end",
                 color=color, size=10)
    for key, color in (("baseline", "#888"), ("best", "#222")):
        u = float(e[key]["uHi"])
        p, n = margins(u)
        svg.dot(X(u), Y(min(p, n)), color, r=3)
    svg.text(X(0.57), Y(4.25), "RhiP(uHi): proved bound for u ≤ uHi", color="#1f6fb4", size=10)
    svg.text(X(0.79), Y(4.9), "RhiN(uHi): proved bound for u ≥ uHi", color="#d1601a", size=10)
    svg.text(X(0.56), Y(5.75), "model: smallest restoring current over the box, at input u "
             "(numerical)", color="#2a8a3c", size=10)
    svg.text(x0, y0 + h + 54, "The proof needs eps below BOTH proved bounds at one split point: "
             "at best their crossing. The model itself has far more.", size=10, color="#555")
    return svg.render()


def write(folder: Path, summary: dict, records: list[dict], num: dict, D: Design) -> None:
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "summary.json").write_text(
        json.dumps(numeric.rounded(summary), indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (folder / "summary.md").write_text(markdown(summary, records), encoding="utf-8")
    (folder / "deadline_gap.svg").write_text(plot_gap(summary), encoding="utf-8")
    (folder / "eps_margins.svg").write_text(plot_eps(D, summary), encoding="utf-8")
