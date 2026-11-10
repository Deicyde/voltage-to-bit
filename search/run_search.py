#!/usr/bin/env python3
"""Workstream F: regenerate the whole experiment record.

    python3 search/run_search.py            # full run (about 60 Lean checks)
    python3 search/run_search.py --check    # same, then compare with the stored record
    python3 search/run_search.py --help

The loop is  propose -> screen -> formally check -> evaluate -> record.

Three separately frozen experiments are run, in this order:

    rise-deadline   minimise the proved rise deadline over certificates
    fall-deadline   minimise the proved fall deadline over certificates
    eps-tolerance   maximise the disturbance bound eps for which `Admissible`
                    is provable when only the proof-only split points change

Every formal check is run from the frozen checkout of the Lean library, so it
is a check against exactly that commit. The run is deterministic: fixed seeds,
exact arithmetic for everything that is compared, and no network access. The
only non-deterministic content is the `timestamps` object of each record and
the run manifest.

Exit status: 0 on success; 1 if the record is inconsistent, a deliberately bad
proposal was accepted, the screen and Lean disagreed, or (with --check) the
regenerated record differs from the stored one; 2 if a Lean-proved bound
contradicts the numerical worst case (soundness alarm).
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from v2bsearch import exact, leanio, numeric, propose, record, report  # noqa: E402
from v2bsearch.exact import dec_str, frac_str  # noqa: E402

REPO = Path(__file__).resolve().parents[1]
SEARCH = REPO / "search"
EVIDENCE = REPO / "evidence" / "search"
DEFAULT_FROZEN = REPO.parent / "frozen-1880a36"
EXPECTED_COMMIT = "1880a3619453d865a04f3b32d25edf69af618501"
DESIGN_REL = "designs/illustrative-1v8.json"
LOOP_VERSION = "1"

SEED = 20261109                       # base seed of every stochastic proposer
UNIFORM_NS = (2, 4, 8, 16)
DP_NS = (2, 4, 8, 16, 32, 64)
RANDOM_DRAWS = 8
SPLIT_PLACES = (2, 3, 4, 5, 6)
PROMOTE_N = 16                        # certificate size suggested for the library


class SoundnessAlarm(RuntimeError):
    """A Lean-accepted bound contradicts the numerical worst case."""


# ----------------------------------------------------------------- environment

class Env:
    def __init__(self, args):
        self.repo = REPO
        self.frozen = Path(args.frozen).resolve()
        self.jobs = args.jobs
        self.lean_dir = SEARCH / "lean"
        self.out_dir = SEARCH / "out"
        self.epoch = os.environ.get("SOURCE_DATE_EPOCH")
        self.check_seconds: dict[str, float] = {}

    def now(self) -> str:
        if self.epoch is not None:
            t = datetime.datetime.fromtimestamp(int(self.epoch), datetime.timezone.utc)
        else:
            t = datetime.datetime.now(datetime.timezone.utc)
        return t.strftime("%Y-%m-%dT%H:%M:%SZ")

    def git(self, *argv: str) -> str:
        return subprocess.run(["git", "-C", str(self.frozen), *argv], capture_output=True,
                              text=True, check=True).stdout.strip()

    def preflight(self, args) -> dict:
        """Establish what the formal checks are checked against."""
        if not (self.frozen / "lakefile.toml").exists():
            raise SystemExit(f"frozen checkout not found at {self.frozen} (use --frozen)")
        self.commit = self.git("rev-parse", "HEAD")
        if self.commit != args.expect_commit:
            raise SystemExit(f"frozen checkout is at {self.commit}, expected {args.expect_commit}")
        dirty = self.git("status", "--porcelain")
        if dirty:
            raise SystemExit(f"frozen checkout has local changes:\n{dirty}")
        self.design, self.design_sha = exact.load_design(self.frozen / DESIGN_REL)
        generated = (self.frozen / "VoltageToBit/Examples/IllustrativeDesign.lean").read_text()
        m = re.search(r"sha256 of the JSON file: ([0-9a-f]{64})", generated)
        if not m or m.group(1) != self.design_sha:
            raise SystemExit("the Lean design record was not generated from this JSON file")
        self.toolchain = (self.frozen / "lean-toolchain").read_text().strip()
        manifest = json.loads((self.frozen / "lake-manifest.json").read_text())
        self.mathlib_rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
        fresh = None
        if not args.skip_freshness:
            # exit status 0 means every compiled file of the library is up to date
            # with its source at this commit; nothing is built
            proc = subprocess.run(["lake", "build", "--no-build", "VoltageToBit"],
                                  cwd=str(self.frozen), capture_output=True, text=True)
            fresh = proc.returncode == 0
            if not fresh:
                raise SystemExit("the frozen checkout's build is not up to date "
                                 "(`lake build --no-build VoltageToBit` failed)")
        floors = leanio.floor_consistent(self.design)
        if not floors["ok"]:
            raise SystemExit("the counterexample preludes do not match this design record")
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=str(self.frozen),
                                 capture_output=True, text=True).stdout.strip()
        return {"frozen_checkout": str(self.frozen), "lean_commit": self.commit,
                "worktree_clean": True, "build_up_to_date": fresh,
                "design_sha256": self.design_sha, "lean_toolchain": self.toolchain,
                "lean_version": version, "mathlib_rev": self.mathlib_rev,
                "python": sys.version.split()[0], "floors": floors}

    def header(self, exp: dict, record_id: str, role: str, proposer: str, about: str) -> dict:
        return {"RECORD": record_id, "EXPERIMENT": exp["id"], "CONTEXT": exp["context_sha256"],
                "COMMIT": self.commit, "DESIGNFILE": DESIGN_REL, "DESIGNSHA": self.design_sha,
                "ROLE": role, "PROPOSER": proposer, "ABOUT": about}

    def check_many(self, tasks: list[dict]) -> None:
        """Run the formal check on every task (in parallel); results are stored
        in each task under 'result'."""
        def one(task):
            res = leanio.run_lean(self.frozen, self.repo, task["lean"], task["out"], task["names"])
            self.check_seconds[res["lean_file"]] = round(res.pop("_seconds"), 2)
            res = {"role": task["role"], "statement": task["statement"],
                   "lean_file_sha256": task["sha"], **res}
            task["result"] = res
            mark = "accepts" if res["passed"] else "REJECTS"
            print(f"    lean {mark} {res['lean_file']}  (exit {res['exit_status']}, "
                  f"{self.check_seconds[res['lean_file']]} s)", flush=True)
        with ThreadPoolExecutor(max_workers=self.jobs) as pool:
            list(pool.map(one, tasks))


# -------------------------------------------------------------------- contexts

def make_context(env: Env, experiment_id: str, specific: dict) -> dict:
    context = {
        "experiment_id": experiment_id,
        "design_file": DESIGN_REL,
        "design_sha256": env.design_sha,
        "design_status": "ILLUSTRATIVE numbers (V, uA, fF, ns); not fitted to any process, "
                         "device model or measurement",
        "lean_commit": env.commit,
        "lean_toolchain": env.toolchain,
        "mathlib_rev": env.mathlib_rev,
        "formal_check": 'cd "$FROZEN" && lake env lean "$R/<generated file>"; accepted iff exit '
                        "status 0, no error message, and every stated theorem depends only on "
                        "the axioms propext, Classical.choice, Quot.sound",
        "evidence_status": {
            "formal": "decided by the Lean check above, against lean_commit",
            "applicability": "claims are about the concrete record `illustrative`; that its "
                             "guarantee is not vacuous is proved in the library "
                             "(illustrative_exists, illustrative_scenario, "
                             "Design.Admissible.exists_rise_run / exists_fall_run)",
            "physical": "none. The numbers are illustrative and the device law is a model; "
                        "nothing in this experiment is evidence about a manufactured device"},
        "loop_version": LOOP_VERSION,
        **specific,
    }
    return {"id": experiment_id, "context": context,
            "context_sha256": record.sha256_text(record.canonical(context))}


def deadline_context(env: Env, direction: str) -> dict:
    d = leanio.DIR[direction]
    rise = direction == "rise"
    conclusion = ("if u <= VIL on [s, e) then VOH <= v(t) for all t in [s + tau, e]" if rise else
                  "if VIH <= u on [s, e) then v(t) <= VOL for all t in [s + tau, e]")
    return make_context(env, f"{direction}-deadline", {
        "objective": {
            "name": f"proved {direction} deadline", "symbol": "tau", "unit": "ns",
            "direction": "minimize",
            "definition": f"the decimal tau for which Lean proves `illustrative.{d['Valid']} c cs tau`. "
                          f"By `IsTrajectory.{direction}_of_cert`, for every parameter choice in the "
                          "box, every input function and every trajectory that starts in the safe "
                          f"domain: {conclusion}."},
        "claim": f"VoltageToBit.Examples.illustrative.{d['Valid']} c cs tau",
        "free": ["certificate levels c :: cs", "claimed deadline tau (4 decimals)"],
        "held_fixed": {
            "design_record": dict(env.design.raw),
            "everything_else": "circuit, device law, parameter box, thresholds, safe domain, "
                               "capacitance range, disturbance bound eps, trajectory notion and "
                               "theorem statements, exactly as at lean_commit"},
        "improvement_rule": "accepted iff Lean proves the claim and tau is strictly smaller than "
                            "the incumbent's tau",
    })


def eps_context(env: Env) -> dict:
    fixed = {k: v for k, v in env.design.raw.items() if k not in ("eps", "uHi", "uLo")}
    return make_context(env, "eps-tolerance", {
        "objective": {
            "name": "proved disturbance bound", "symbol": "eps", "unit": "uA",
            "direction": "maximize",
            "definition": "the decimal eps for which Lean proves "
                          "`({ illustrative with eps := eps, uHi := x, uLo := y }).Admissible`; "
                          "every theorem of the library about admissible records then applies to "
                          "that variant record."},
        "claim": "({ VoltageToBit.Examples.illustrative with eps := eps, uHi := x, uLo := y } "
                 ": Design).Admissible",
        "free": ["eps (the objective, 4 decimals)", "uHi (proof-only split point)",
                 "uLo (proof-only split point)"],
        "held_fixed": {
            "design_record": fixed,
            "everything_else": "circuit, device law, parameter box, thresholds, safe domain, "
                               "capacitance range, trajectory notion and theorem statements, "
                               "exactly as at lean_commit"},
        "claim_change_notice":
            "Changing eps changes the claim. A larger eps enlarges the set of trajectories the "
            "theorems quantify over and lengthens the record's own closed-form deadlines tauUp and "
            "tauDn. A result of this experiment reads 'the proof supports a larger disturbance "
            "bound for the same circuit'; it is a different statement from the eps = 2 guarantee, "
            "not an improvement of it. uHi and uLo occur only in the admissibility conditions hiP, "
            "hiN, loN, loP and are not circuit or environment parameters.",
        "improvement_rule": "accepted iff Lean proves the claim and eps is strictly larger than "
                            "the incumbent's eps",
    })


# ------------------------------------------------------------------- the loop

class Experiment:
    """One frozen experiment: a growing list of records and an incumbent."""

    def __init__(self, env: Env, exp: dict, prefix: str, kind: str, evidence_fn, guard_fn):
        self.env, self.exp, self.prefix, self.kind = env, exp, prefix, kind
        self.evidence_fn, self.guard_fn = evidence_fn, guard_fn
        self.records: list[dict] = []
        self.incumbent: dict | None = None
        self.baseline_id: str | None = None
        self.maximize = exp["context"]["objective"]["direction"] == "maximize"

    # -- per-kind pieces ---------------------------------------------------
    def screen(self, p: propose.Proposal) -> dict:
        D = self.env.design
        if self.kind == "certificate":
            levels = [Fraction(x) for x in p.payload["levels"]]
            return exact.screen_certificate(D, p.payload["direction"], levels,
                                            Fraction(p.payload["tau"]))
        variant = D.replace(eps=p.payload["eps"], uHi=p.payload["uHi"], uLo=p.payload["uLo"])
        s = exact.screen_admissible(variant)
        s["variant"] = variant
        return s

    def value(self, p: propose.Proposal) -> Fraction:
        return Fraction(p.payload["tau"] if self.kind == "certificate" else p.payload["eps"])

    def claim_text(self, p: propose.Proposal) -> str:
        if self.kind == "certificate":
            d = leanio.DIR[p.payload["direction"]]
            levels = p.payload["levels"]
            return (f"illustrative.{d['Valid']} {levels[0]} [{', '.join(levels[1:])}] "
                    f"{p.payload['tau']}")
        return ("({ illustrative with eps := %s, uHi := %s, uLo := %s }).Admissible"
                % (p.payload["eps"], p.payload["uHi"], p.payload["uLo"]))

    def task(self, rid: str, role: str, p: propose.Proposal, body: str, names: list[str],
             statement: str, about: str) -> dict:
        lean = self.env.lean_dir / f"{rid}.{role}.lean"
        sha = leanio.write_lean(lean, self.env.header(self.exp, rid, role, p.proposer["name"], about),
                                body)
        return {"role": role, "lean": lean, "out": self.env.out_dir / f"{rid}.{role}.out",
                "names": names, "sha": sha, "statement": statement}

    def claim_task(self, rid: str, name: str, p: propose.Proposal, s: dict, is_baseline: bool):
        if self.kind == "certificate":
            direction = p.payload["direction"]
            body, names = leanio.cert_claim(
                direction, name, p.payload["levels"], p.payload["tau"],
                s["exact_sum"] if s["valid"] else None,
                self.env.design.raw[leanio.DIR[direction]["target"]] if is_baseline else None)
        else:
            taus = None
            if s["valid"]:
                taus = (exact.tauUp(s["variant"]), exact.tauDn(s["variant"]))
            body, names = leanio.adm_claim(name, p.payload["eps"], p.payload["uHi"],
                                           p.payload["uLo"], taus)
        return self.task(rid, "claim", p, body, names, self.claim_text(p),
                         "Claim, stated positively: " + self.claim_text(p))

    def followup_tasks(self, rid: str, name: str, p: propose.Proposal, s: dict, extra: dict):
        """Refutation / counterexample files for a claim Lean did not accept."""
        tasks = []
        if s["valid"]:
            return tasks          # screen and Lean disagree: nothing to refute with
        if self.kind == "certificate":
            direction = p.payload["direction"]
            body, names = leanio.cert_refutation(direction, name, p.payload["levels"],
                                                 p.payload["tau"], s["first_failure"])
            tasks.append(self.task(rid, "refutation", p, body, names,
                                   f"¬ ({self.claim_text(p)})",
                                   f"Negation of the claim: its `{s['first_failure']}` condition is false."))
            if Fraction(p.payload["tau"]) < leanio.FLOOR[direction]:
                body, names = leanio.cert_counterexample(direction, name, p.payload["tau"])
                tasks.append(self.task(
                    rid, "counterexample", p, body, names,
                    f"the {direction} clause of the guarantee with deadline {p.payload['tau']} ns "
                    f"fails on an explicit trajectory ({name}_not_a_deadline); generally, no "
                    f"{direction} deadline below {dec_str(leanio.FLOOR[direction])} ns is valid",
                    "An explicit trajectory of the model violates the claimed deadline."))
        else:
            ceiling = None
            if extra.get("ceiling") and Fraction(p.payload["eps"]) >= extra["ceiling"]["E"]:
                ceiling = extra["ceiling"]["constants"]
            body, names = leanio.adm_refutation(self.env.design, name, p.payload["eps"],
                                                p.payload["uHi"], p.payload["uLo"],
                                                s["first_failure"], ceiling)
            statement = f"¬ ({self.claim_text(p)})"
            if ceiling is not None:
                statement += (f"; and for every uHi, uLo and every eps >= {ceiling['E']}: "
                              "the variant record is not admissible")
            tasks.append(self.task(rid, "refutation", p, body, names, statement,
                                   f"Negation of the claim: its `{s['first_failure']}` condition is false."))
        return tasks

    # -- one generation ----------------------------------------------------
    def run(self, generation: int, proposals: list[propose.Proposal], extra: dict | None = None):
        env, extra = self.env, extra or {}
        print(f"  generation {generation}: {len(proposals)} proposal(s)", flush=True)
        items = []
        for p in proposals:
            rid = f"{self.prefix}-{len(self.records) + len(items):03d}-{p.slug}"
            items.append({"p": p, "rid": rid, "name": leanio.lean_name(rid),
                          "proposed": env.now(), "screen": self.screen(p), "tasks": []})
        # formal check of the claims (screen-valid ones, and controls with the screen bypassed)
        claims = []
        for it in items:
            if it["screen"]["valid"] or it["p"].bypass_screen:
                is_baseline = generation == 0
                it["claim"] = self.claim_task(it["rid"], it["name"], it["p"], it["screen"], is_baseline)
                it["tasks"].append(it["claim"])
                claims.append(it["claim"])
        env.check_many(claims)
        # refutations and counterexamples for what Lean rejected
        follow = []
        for it in items:
            if "claim" in it and not it["claim"]["result"]["passed"]:
                more = self.followup_tasks(it["rid"], it["name"], it["p"], it["screen"], extra)
                it["tasks"] += more
                follow += more
        env.check_many(follow)
        # evaluate and decide, in order
        for it in items:
            self.records.append(self.decide(generation, it))
        return self.records[-len(items):]

    def decide(self, generation: int, it: dict) -> dict:
        p, s, env = it["p"], it["screen"], self.env
        checks = [t["result"] for t in it["tasks"]]
        by_role = {c["role"]: c for c in checks}
        claim = by_role.get("claim")
        if claim is not None:
            # name the conjuncts of the claim that Lean left unsolved
            cases = claim["unsolved_cases"]
            claim["failed_conditions"] = ([leanio.CERT_CASES.get(c, c) for c in cases]
                                          if self.kind == "certificate" else list(cases))
        value = self.value(p)
        symbol = self.exp["context"]["objective"]["symbol"]
        unit = self.exp["context"]["objective"]["unit"]
        evidence = self.evidence_fn(p, s)
        objective_value, rejected_by = None, []
        parent = self.incumbent["record_id"] if self.incumbent else None

        if claim is None:
            decision, code = "rejected", "screen_invalid"
            reason = f"The exact screen found the claim invalid ({s['detail']}); not sent to Lean."
            rejected_by = ["screen"]
        elif claim["passed"]:
            self.guard_fn(p, value, evidence)
            objective_value = {"symbol": symbol, "unit": unit, "value": dec_str(value)}
            if self.kind == "certificate":
                objective_value["exact_certificate_sum"] = frac_str(s["exact_sum"])
            if self.incumbent is None:
                decision, code = "accepted", "baseline"
                reason = f"Baseline: Lean proved the claim; {symbol} = {dec_str(value)} {unit}."
            else:
                inc = Fraction(self.incumbent["objective_value"]["value"])
                better = value > inc if self.maximize else value < inc
                word = ">" if self.maximize else "<"
                if better:
                    decision, code = "accepted", "improves_incumbent"
                    reason = (f"Lean proved the claim; {symbol} = {dec_str(value)} {unit} {word} "
                              f"incumbent {dec_str(inc)} {unit} ({parent}), same frozen context.")
                else:
                    decision, code = "rejected", "valid_not_improving"
                    reason = (f"Lean proved the claim, but {symbol} = {dec_str(value)} {unit} does "
                              f"not improve on the incumbent {dec_str(inc)} {unit} ({parent}).")
                    rejected_by = ["evaluation"]
        else:
            rejected_by = (["screen (bypassed)"] if not s["valid"] else []) + ["lean"]
            refuted = by_role.get("refutation", {}).get("passed", False)
            cx = by_role.get("counterexample", {}).get("passed", False)
            first = claim["first_error"] or f"exit status {claim['exit_status']}"
            where = ", ".join(claim["failed_conditions"]) or "see the Lean output"
            if cx:
                decision, code = "counterexample", "claimed_bound_false"
                reason = (f"Lean rejected the claim (unsolved: {where}; {s['detail']}). The claimed "
                          "deadline is false for the model: Lean checked an explicit trajectory "
                          "that violates it. This is not an improved guarantee.")
            elif refuted:
                decision, code = "rejected", "lean_rejected_and_refuted"
                reason = (f"Lean rejected the claim (unsolved: {where}) and proved its negation "
                          f"({s['detail']}). This shows that the proposal cannot justify its "
                          "number; it does not by itself show that the circuit violates it.")
            else:
                decision, code = "rejected", "lean_rejected"
                reason = f"Lean did not accept the claim: {first}"

        # The screen and Lean must agree on validity and, for an invalid claim,
        # on exactly which conditions fail.
        agrees = None
        if claim is not None:
            agrees = s["valid"] == claim["passed"]
            if agrees and not s["valid"]:
                screen_failed = sorted(k for k, ok in s["conditions"].items() if not ok)
                agrees = screen_failed == sorted(claim["failed_conditions"])
        control = None
        if p.expected is not None:
            met = claim is not None and not claim["passed"] if p.expected == "lean_rejects" else None
            control = {"expected": p.expected, "met": met}
        screen_out = {
            "tool": "exact rational arithmetic (python fractions), search/v2bsearch/exact.py",
            "valid": s["valid"], "conditions": s["conditions"],
            "first_failure": s["first_failure"], "detail": s["detail"],
            "bypassed": bool(p.bypass_screen and not s["valid"]),
        }
        if self.kind == "certificate":
            screen_out["exact_sum"] = frac_str(s["exact_sum"])
            screen_out["exact_sum_decimal"] = f"{float(s['exact_sum']):.10f}"
        rec = record.finish({
            "schema": record.SCHEMA,
            "record_id": it["rid"],
            "experiment_id": self.exp["id"],
            "generation": generation,
            "parent_id": parent,
            "baseline_id": self.baseline_id,
            "context_sha256": self.exp["context_sha256"],
            "context": self.exp["context"],
            "proposer": p.proposer,
            "proposal": {"kind": p.kind, **p.payload, "note": p.note},
            "screen": screen_out,
            "formal_checks": checks,
            "numerical_evidence": evidence,
            "objective_value": objective_value,
            "decision": decision,
            "reason_code": code,
            "reason": reason,
            "rejected_by": rejected_by,
            "control": control,
            "screen_agrees_with_lean": agrees,
            "timestamps": {"proposed_utc": it["proposed"], "decided_utc": env.now()},
        })
        if decision == "accepted":
            self.incumbent = rec
            if self.baseline_id is None:
                self.baseline_id = rec["record_id"]
        print(f"    {rec['record_id']}: {decision} ({code})", flush=True)
        return rec


# ------------------------------------------------------------- the experiments

def deadline_experiment(env: Env, direction: str, num: dict) -> Experiment:
    D = env.design
    worst = num["worst_case"]["worst_case_delay_ns"]
    floor = leanio.FLOOR[direction]

    def evidence(p, s):
        tau = float(Fraction(p.payload["tau"]))
        return numeric.rounded({
            "kind": "quadrature of the model (floating point; evidence, not proof)",
            "model_worst_case_delay_ns": worst,
            "worst_case_if_parameters_could_move_ns": num["moving_parameter_worst_case_delay_ns"],
            "certificate_method_limit_ns": num["certificate_infimum_ns"],
            "claimed_tau_minus_worst_case_ns": tau - worst,
            "claimed_tau_at_or_above_worst_case": tau >= worst - 1e-9,
            "lean_proved_floor_ns": float(floor),
            "claimed_tau_below_lean_floor": Fraction(p.payload["tau"]) < floor,
            "details": "evidence/search/numerics.json",
        })

    def guard(p, value, ev):
        if not ev["claimed_tau_at_or_above_worst_case"]:
            raise SoundnessAlarm(
                f"Lean accepted {direction} deadline {dec_str(value)} ns, below the numerical "
                f"worst-case delay {worst:.9f} ns of the model. One of the two is wrong: STOP.")

    if float(floor) > worst + 1e-9:
        raise SoundnessAlarm(
            f"the Lean-proved floor {dec_str(floor)} ns on {direction} deadlines is above the "
            f"numerical worst-case delay {worst:.9f} ns of the model. One of the two is wrong: STOP.")
    ex = Experiment(env, deadline_context(env, direction), direction, "certificate", evidence, guard)
    print(f"experiment {ex.exp['id']}  (context {ex.exp['context_sha256'][:12]})", flush=True)
    ex.run(0, [propose.baseline(D, direction)])

    # generation 1: every proposer sees only the baseline. Order of evaluation:
    # the prior result, the stochastic proposer, then by certificate size with
    # equally spaced levels before grid-optimal levels.
    dp = propose.dp_grid_levels(D, direction, max(DP_NS))
    gen1 = [propose.library_prior()] if direction == "rise" else []
    gen1 += propose.random_levels(D, direction, RANDOM_DRAWS, SEED + (0 if direction == "rise" else 1))
    for n in sorted(set(UNIFORM_NS) | set(DP_NS)):
        if n in UNIFORM_NS:
            gen1.append(propose.uniform(D, direction, n))
        if n in DP_NS:
            gen1.append(propose.dp_grid(D, direction, n, dp[n]))
    ex.run(1, gen1)

    best_levels = [Fraction(x) for x in ex.incumbent["proposal"]["levels"]]
    ex.run(2, propose.deadline_controls(D, direction, best_levels, dp[4], num, floor))
    return ex


def eps_experiment(env: Env, num: dict) -> Experiment:
    D = env.design
    tolerance = num["boundary_margins"]["model_tolerance_uA"]
    margins = propose.eps_margins(D)
    model_cap = min(tolerance, float(margins["up"]), float(margins["dn"]))

    def evidence(p, s):
        eps = float(Fraction(p.payload["eps"]))
        v = s["variant"]
        return numeric.rounded({
            "kind": "scan of the model's boundary currents (floating point; evidence, not proof)",
            "model_min_inward_current_at_Vhi_uA": num["boundary_margins"]["Vhi"]["min_inward_current_uA"],
            "model_min_inward_current_at_Vlo_uA": num["boundary_margins"]["Vlo"]["min_inward_current_uA"],
            "model_tolerance_estimate_uA": model_cap,
            "claimed_eps_below_model_tolerance": eps < model_cap + 1e-9,
            "closed_form_margins_uA": {k: float(x) for k, x in propose.eps_margins(v).items()},
            "variant_tauUp_ns": float(exact.tauUp(v)),
            "variant_tauDn_ns": float(exact.tauDn(v)),
            "details": "evidence/search/numerics.json",
        })

    def guard(p, value, ev):
        if not ev["claimed_eps_below_model_tolerance"]:
            raise SoundnessAlarm(
                f"Lean accepted eps = {dec_str(value)} uA, above the numerical estimate "
                f"{model_cap:.6f} uA of what the model tolerates. One of the two is wrong: STOP.")

    ex = Experiment(env, eps_context(env), "eps", "admissible", evidence, guard)
    print(f"experiment {ex.exp['id']}  (context {ex.exp['context_sha256'][:12]})", flush=True)
    ex.run(0, [propose.eps_baseline(D)])
    ex.run(1, [propose.eps_same_splits(D)])
    ex.run(2, [propose.eps_split_search(D, places) for places in SPLIT_PLACES])

    best = ex.incumbent["proposal"]
    best_p = propose.eps_proposal("best", {}, Fraction(best["eps"]), best["uHi"], best["uLo"])
    E = Fraction(best["eps"]) + Fraction(1, 10 ** propose.EPS_PLACES)
    pivot = propose.ceiling_pivot(D, E)
    ceiling = None
    if pivot is not None:
        constants = leanio.ceiling_constants(D, E, pivot)
        if constants is not None:
            ceiling = {"E": E, "constants": constants}
    ex.run(3, propose.eps_controls(D, best_p, tolerance), {"ceiling": ceiling})
    ex.ceiling = ceiling
    return ex


# ------------------------------------------------------------------------ main

def compute_numerics(env: Env) -> dict:
    D = env.design
    out = {"note": "Floating-point numerical evidence. Not a proof; never used to accept a "
                   "proposal. Produced by search/v2bsearch/numeric.py.",
           "design_sha256": env.design_sha}
    for direction in ("rise", "fall"):
        out[direction] = {
            "worst_case": numeric.worst_case(D, direction, seed=SEED),
            "moving_parameter_worst_case_delay_ns": numeric.moving_parameter_worst_case(D, direction),
            "certificate_infimum_ns": numeric.certificate_infimum(D, direction),
            "predictions": numeric.predictions(D, direction),
        }
        wc = out[direction]["worst_case"]
        if wc["abs_diff_quadrature_vs_rk4_ns"] > 1e-8:
            raise SystemExit(f"{direction}: quadrature and time stepping disagree")
    out["boundary_margins"] = numeric.boundary_margins(D)
    return out


def promote(env: Env, rise: Experiment, fall: Experiment, eps: Experiment) -> dict:
    """Package the statements suggested for the library into two files and
    check both: the accepted improvement, and the limits found."""
    def pick(ex):
        for r in ex.records:
            if (r["decision"] == "accepted" and r["proposer"]["name"] == "dp-grid"
                    and r["proposer"]["params"]["N"] == PROMOTE_N):
                return r
        return ex.incumbent
    r, f, e = pick(rise), pick(fall), eps.incumbent
    strip = lambda t: dec_str(Fraction(t))
    folder = SEARCH / "promote"
    common = {"COMMIT": env.commit, "DESIGNFILE": DESIGN_REL, "DESIGNSHA": env.design_sha,
              "ROLE": "promotion candidate"}

    body, names = leanio.promotion_file(
        r["record_id"], r["proposal"]["levels"], strip(r["proposal"]["tau"]),
        f["record_id"], f["proposal"]["levels"], strip(f["proposal"]["tau"]))
    header = {"RECORD": f"{r['record_id']} + {f['record_id']}",
              "EXPERIMENT": "rise-deadline + fall-deadline",
              "CONTEXT": f"{rise.exp['context_sha256']} / {fall.exp['context_sha256']}",
              "PROPOSER": "dp-grid",
              "ABOUT": "The accepted improvement, packaged in the shape of `illustrative_guarantee`.",
              **common}
    deadlines = {"role": "promotion", "lean": folder / "RefinedDeadlines.lean",
                 "out": folder / "RefinedDeadlines.out", "names": names,
                 "sha": leanio.write_lean(folder / "RefinedDeadlines.lean", header, body),
                 "statement": "refined guarantee: same statement as illustrative_guarantee with "
                              "the two deadlines replaced"}

    variant = env.design.replace(eps=e["proposal"]["eps"], uHi=e["proposal"]["uHi"],
                                 uLo=e["proposal"]["uLo"])
    body, names = leanio.limits_file(
        env.design, e["record_id"], e["proposal"]["eps"], e["proposal"]["uHi"],
        e["proposal"]["uLo"], (exact.tauUp(variant), exact.tauDn(variant)),
        eps.ceiling["constants"] if eps.ceiling else None)
    header = {"RECORD": e["record_id"] + " and the counterexample records",
              "EXPERIMENT": "rise-deadline + fall-deadline + eps-tolerance",
              "CONTEXT": " / ".join(x.exp["context_sha256"] for x in (rise, fall, eps)),
              "PROPOSER": "split-search; workstream F (floors)",
              "ABOUT": "Limits: floors on both deadlines, the larger-eps variant record, its ceiling.",
              **common}
    limits = {"role": "promotion", "lean": folder / "Limits.lean", "out": folder / "Limits.out",
              "names": names, "sha": leanio.write_lean(folder / "Limits.lean", header, body),
              "statement": "floors on valid deadlines; admissibility of the larger-eps variant; "
                           "ceiling on eps over all split points"}
    print("  promotion candidates", flush=True)
    env.check_many([deadlines, limits])
    res = {"deadlines": deadlines["result"], "limits": limits["result"]}
    res["deadlines"].update(rise_record=r["record_id"], fall_record=f["record_id"],
                            rise_tau=strip(r["proposal"]["tau"]), fall_tau=strip(f["proposal"]["tau"]))
    res["limits"].update(eps_record=e["record_id"], eps=e["proposal"]["eps"],
                         uHi=e["proposal"]["uHi"], uLo=e["proposal"]["uLo"])
    return res


def write_evidence(env: Env, records: list[dict], num: dict, promotion: dict, sha: str) -> None:
    """Everything under evidence/search/: a copy of the record and files derived from it."""
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(SEARCH / "records" / "records.jsonl", EVIDENCE / "records.jsonl")
    (EVIDENCE / "numerics.json").write_text(
        json.dumps(numeric.rounded(num), indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    summary = report.build(env.design, records, num, promotion,
                           {"records_sha256": sha, "lean_commit": env.commit,
                            "design_sha256": env.design_sha})
    report.write(EVIDENCE, summary, records, num, env.design)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--frozen", default=os.environ.get("V2B_FROZEN", str(DEFAULT_FROZEN)),
                    help="checkout of the Lean library at the frozen commit (already built)")
    ap.add_argument("--expect-commit", default=EXPECTED_COMMIT)
    ap.add_argument("--jobs", type=int, default=2, help="Lean checks run in parallel (default 2)")
    ap.add_argument("--skip-freshness", action="store_true",
                    help="do not run `lake build --no-build` in the frozen checkout")
    ap.add_argument("--check", action="store_true",
                    help="after the run, compare with the previously stored record")
    ap.add_argument("--report-only", action="store_true",
                    help="run no Lean check: rebuild evidence/search/ (tables, plots, numerics) "
                         "from the stored record")
    args = ap.parse_args(argv)

    started = time.time()
    env = Env(args)
    info = env.preflight(args)
    print(f"frozen checkout {env.frozen}\n  commit {env.commit}\n  design sha256 {env.design_sha}",
          flush=True)

    records_path = SEARCH / "records" / "records.jsonl"
    promotion_path = SEARCH / "records" / "promotion.json"
    previous = record.read_jsonl(records_path) if records_path.exists() else None

    if args.report_only:
        # Derived files only. Nothing is decided here: the record is read, not rewritten.
        if previous is None or not promotion_path.exists():
            raise SystemExit("--report-only needs a stored record (run without it first)")
        stale = {r["context"]["lean_commit"] for r in previous} | \
                {r["context"]["design_sha256"] for r in previous}
        if stale != {env.commit, env.design_sha}:
            raise SystemExit("the stored record belongs to another commit or design file")
        problems = record.verify(previous)
        for item in problems:
            print(f"PROBLEM: {item}", file=sys.stderr)
        sha = record.sha256_text(records_path.read_text(encoding="utf-8"))
        write_evidence(env, previous, compute_numerics(env),
                       json.loads(promotion_path.read_text(encoding="utf-8")), sha)
        print(f"rebuilt {EVIDENCE} from {len(previous)} stored records (sha256 {sha}); no Lean check run")
        return 1 if problems else 0

    for folder in (env.lean_dir, env.out_dir):
        shutil.rmtree(folder, ignore_errors=True)
        folder.mkdir(parents=True)

    num = compute_numerics(env)
    try:
        rise = deadline_experiment(env, "rise", num["rise"])
        fall = deadline_experiment(env, "fall", num["fall"])
        eps = eps_experiment(env, num)
    except SoundnessAlarm as alarm:
        print(f"\nSOUNDNESS ALARM: {alarm}", file=sys.stderr)
        return 2
    promotion = promote(env, rise, fall, eps)

    records = rise.records + fall.records + eps.records
    sha = record.write_jsonl(records_path, records)
    promotion_path.write_text(json.dumps(promotion, indent=1, ensure_ascii=False) + "\n",
                              encoding="utf-8")
    write_evidence(env, records, num, promotion, sha)

    problems = record.verify(records)
    bad_controls = [r["record_id"] for r in records if r["control"] and r["control"]["met"] is False]
    disagreements = [r["record_id"] for r in records if r["screen_agrees_with_lean"] is False]
    for key, res in promotion.items():
        if not res["passed"]:
            problems.append(f"the promotion candidate file ({key}) did not pass the formal check")
    manifest = {
        "note": "Non-deterministic facts about this run (paths, times). The record itself is in "
                "records.jsonl.",
        "started_utc": datetime.datetime.fromtimestamp(started, datetime.timezone.utc)
                               .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "wall_seconds": round(time.time() - started, 1),
        "jobs": env.jobs,
        "placeholders": {"$FROZEN": str(env.frozen), "$R": str(env.repo)},
        "environment": info,
        "records": len(records),
        "records_sha256": sha,
        "content_hashes_sha256": record.sha256_text("".join(r["content_sha256"] for r in records)),
        "formal_check_seconds": env.check_seconds,
        "problems": problems, "controls_not_met": bad_controls,
        "screen_lean_disagreements": disagreements,
    }
    (SEARCH / "records" / "run_manifest.json").write_text(
        json.dumps(manifest, indent=1) + "\n", encoding="utf-8")

    counts = {}
    for r in records:
        counts[r["decision"]] = counts.get(r["decision"], 0) + 1
    print(f"\n{len(records)} records: {counts}")
    print(f"records sha256 {sha}")
    print(f"content digest {manifest['content_hashes_sha256']}")
    status = 0
    for label, items in (("PROBLEM", problems), ("CONTROL ACCEPTED", bad_controls),
                         ("SCREEN/LEAN DISAGREEMENT", disagreements)):
        for item in items:
            print(f"{label}: {item}", file=sys.stderr)
            status = 1
    if args.check:
        if previous is None:
            print("--check: no stored record to compare with", file=sys.stderr)
            status = 1
        else:
            old = [(r["record_id"], r["content_sha256"]) for r in previous]
            new = [(r["record_id"], r["content_sha256"]) for r in records]
            if old == new:
                print(f"--check: REPRODUCED, {len(new)} records identical (timestamps aside)")
            else:
                diff = sorted(set(old) ^ set(new))
                print(f"--check: DIFFERENT from the stored record: {diff[:10]}", file=sys.stderr)
                status = 1
    print(f"wall time {manifest['wall_seconds']} s")
    return status


if __name__ == "__main__":
    sys.exit(main())
