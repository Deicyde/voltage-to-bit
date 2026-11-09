#!/usr/bin/env python3
"""Unit tests of the loop's untrusted parts (no Lean needed).

    python3 search/test_loop.py

These test the exact screen against numbers that the frozen Lean library
proves (`Examples/Illustrative.lean`), the decimal helpers, the record hashing
and the soundness guard. They do not replace the formal checks: the screen is
compared with Lean, condition by condition, in every full run.
"""
from __future__ import annotations

import sys
import unittest
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import run_search  # noqa: E402
from v2bsearch import exact, leanio, numeric, propose, record  # noqa: E402

DESIGN = run_search.DEFAULT_FROZEN / run_search.DESIGN_REL


class ExactScreen(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.D, cls.sha = exact.load_design(DESIGN)

    def test_design_hash(self):
        self.assertEqual(self.sha, "06ccc32a64938f43350d6fb68d991c15e62b9d6815f0b174391be073727bc967")

    def test_margins_match_library_theorems(self):
        D = self.D
        # illustrative_Iup, _Idn, _RhiP, _RhiN, _RloN, _RloP, _tauUp, _tauDn
        self.assertEqual(exact.Iup(D, D.VOH), Fr("10.476"))
        self.assertEqual(exact.Idn(D, D.VOL), Fr("16.296"))
        self.assertEqual(exact.RhiP(D), Fr("2.4"))
        self.assertEqual(exact.RhiN(D), Fr("2.312"))
        self.assertEqual(exact.RloN(D), Fr("3.04"))
        self.assertEqual(exact.RloP(D), Fr("3.136"))
        self.assertEqual(exact.tauUp(D), Fr(7250, 2119))
        self.assertEqual(exact.tauDn(D), Fr(4575, 1787))
        self.assertTrue(exact.screen_admissible(D)["valid"])

    def test_library_certificate(self):
        # illustrative_riseCert_3 (accepted) and illustrative_riseCert_rejected
        levels = [Fr("1.0"), Fr("1.2"), Fr("1.35")]
        self.assertTrue(exact.screen_certificate(self.D, "rise", levels, Fr("2.34"))["valid"])
        s = exact.screen_certificate(self.D, "rise", levels, Fr("2.0"))
        self.assertFalse(s["valid"])
        self.assertEqual(s["first_failure"], "deadline")

    def test_each_condition_is_reported(self):
        D = self.D
        s = exact.screen_certificate(D, "rise", [Fr("1.2"), Fr("1.0"), Fr("1.35")], Fr(10))
        self.assertEqual(s["conditions"], {"segments": False, "final_level": True, "deadline": True})
        s = exact.screen_certificate(D, "rise", [Fr("1.0"), Fr("1.30")], Fr(10))
        self.assertEqual(s["conditions"], {"segments": True, "final_level": False, "deadline": True})
        s = exact.screen_certificate(D, "fall", [Fr("0.05"), Fr("0.25")], Fr(10))
        self.assertFalse(s["conditions"]["segments"])      # margin below eps at 0.05 V

    def test_division_by_zero_follows_lean(self):
        self.assertEqual(exact.lean_div(Fr(3), Fr(0)), 0)

    def test_noisy_record_is_inadmissible(self):
        # `noisy_not_admissible` in Examples/NegativeControls.lean
        s = exact.screen_admissible(self.D.replace(eps="10.76"))
        self.assertFalse(s["valid"])
        self.assertIn("up", s["failing"])

    def test_decimal_helpers(self):
        self.assertEqual(exact.dec_str(Fr("2.26"), 4), "2.2600")
        self.assertEqual(exact.dec_str(Fr("-0.10")), "-0.1")
        self.assertEqual(exact.ceil_dec(Fr(7250, 2119), 4), Fr("3.4215"))
        self.assertEqual(exact.floor_dec(Fr(7250, 2119), 4), Fr("3.4214"))
        self.assertEqual(exact.below_dec(Fr("2.312"), 4), Fr("2.3119"))
        self.assertEqual(exact.nearest_dec(Fr("2.25995"), 4), Fr("2.26"))
        self.assertRaises(ValueError, exact.dec_str, Fr(1, 3))

    def test_floor_constants(self):
        self.assertTrue(leanio.floor_consistent(self.D)["ok"])


class Proposers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.D, _ = exact.load_design(DESIGN)

    def test_dp_beats_uniform_and_is_valid(self):
        for direction in ("rise", "fall"):
            dp = propose.dp_grid_levels(self.D, direction, 16)
            for n in (2, 4, 8, 16):
                best = propose.formal_sum(self.D, direction, dp[n])
                uni = Fr(propose.uniform(self.D, direction, n).payload["tau"])
                self.assertLess(best, uni)
                self.assertEqual(len(dp[n]), n)
                tau = exact.ceil_dec(best, 4)
                self.assertTrue(exact.screen_certificate(self.D, direction, dp[n], tau)["valid"])
                self.assertFalse(exact.screen_certificate(self.D, direction, dp[n],
                                                          exact.below_dec(best, 4))["valid"])

    def test_random_proposer_is_reproducible(self):
        a = propose.random_levels(self.D, "rise", 5, 7)
        b = propose.random_levels(self.D, "rise", 5, 7)
        self.assertEqual([p.payload for p in a], [p.payload for p in b])

    def test_split_search(self):
        D = self.D
        x = propose.best_split(D, "uHi", 6)
        self.assertEqual(x, Fr("0.772486"))
        self.assertGreater(propose.boundary_margin(D, "uHi", x), Fr("2.3801"))
        pivot = propose.ceiling_pivot(D, Fr("2.3802"))
        self.assertIsNotNone(leanio.ceiling_constants(D, Fr("2.3802"), pivot))
        self.assertIsNone(leanio.ceiling_constants(D, Fr("2.3801"), pivot))


class Numerics(unittest.TestCase):
    def test_quadrature_against_closed_form(self):
        import math
        D, _ = exact.load_design(DESIGN)
        # rise: 20 * [1.1/13.376 + atanh(0.35/a)/(40 a)], a^2 = 13.376/40
        a = math.sqrt(13.376 / 40.0)
        closed = 20.0 * (1.1 / 13.376 + math.atanh(0.35 / a) / (40.0 * a))
        wc = numeric.worst_case(D, "rise", samples=20)
        self.assertAlmostEqual(wc["worst_case_delay_ns"], closed, places=10)
        self.assertLess(wc["abs_diff_quadrature_vs_rk4_ns"], 1e-9)
        self.assertAlmostEqual(numeric.certificate_infimum(D, "rise"), closed, places=10)


class LeanText(unittest.TestCase):
    def test_only_plain_decimals_reach_lean(self):
        self.assertEqual(leanio.lit("1.35"), "1.35")
        self.assertEqual(leanio.lit("-0.10"), "(-0.10)")
        for bad in ("1.35 := by sorry", "1e3", "2.26]", "", "0.5 -- x", "1/3"):
            self.assertRaises(ValueError, leanio.lit, bad)

    def test_output_parser(self):
        text = ("search/lean/x.claim.lean:26:89: error: unsolved goals\ncase hiP\n⊢ False\n\n"
                "case hiN\n⊢ False\n'VoltageToBit.Search.x' depends on axioms: [propext,\n"
                " sorryAx,\n Classical.choice]\n")
        messages = leanio.parse_messages(text)
        self.assertEqual([m["severity"] for m in messages], ["error"])
        self.assertEqual([ln.split()[1] for ln in messages[0]["lines"] if ln.startswith("case ")],
                         ["hiP", "hiN"])
        found = {m.group(1).split(".")[-1]: [a.strip() for a in m.group(2).split(",")]
                 for m in leanio.AXIOM_LINE.finditer(text)}
        self.assertEqual(found, {"x": ["propext", "sorryAx", "Classical.choice"]})


class GeneratedFiles(unittest.TestCase):
    def test_forbidden_token_scan(self):
        self.assertEqual(leanio.forbidden_tokens("theorem x : 1 = 1 := by norm_num"), [])
        self.assertEqual(leanio.forbidden_tokens("set_option debug.skipKernelTC true in\n"
                                                 "theorem x : False := by sorry"),
                         ["set_option", "skipKernelTC", "sorry"])

    def test_stored_lean_files_are_clean(self):
        """Every generated Lean file on disk: no forbidden token, and it is the
        file the record refers to (same SHA-256)."""
        import hashlib
        search = Path(__file__).resolve().parent
        files = sorted((search / "lean").glob("*.lean")) + sorted((search / "promote").rglob("*.lean"))
        for f in files:
            self.assertEqual(leanio.forbidden_tokens(f.read_text(encoding="utf-8")), [], f.name)
        stored = search / "records" / "records.jsonl"
        if not stored.exists():
            self.skipTest("no stored record")
        checked = 0
        for r in record.read_jsonl(stored):
            for c in r["formal_checks"]:
                text = (search.parent / c["lean_file"]).read_bytes()
                self.assertEqual(hashlib.sha256(text).hexdigest(), c["lean_file_sha256"], c["lean_file"])
                out = (search.parent / c["output_file"]).read_bytes()
                self.assertEqual(hashlib.sha256(out).hexdigest(), c["output_sha256"], c["output_file"])
                checked += 1
        self.assertGreater(checked, 0)


class Records(unittest.TestCase):
    def test_hash_ignores_timestamps_only(self):
        base = {k: None for k in record.KEYS if k != "content_sha256"}
        base.update(schema=record.SCHEMA, decision="rejected", record_id="x", timestamps={"a": 1})
        r1 = record.finish(dict(base))
        r2 = record.finish(dict(base, timestamps={"a": 2}))
        r3 = record.finish(dict(base, reason="different"))
        self.assertEqual(r1["content_sha256"], r2["content_sha256"])
        self.assertNotEqual(r1["content_sha256"], r3["content_sha256"])

    def test_bad_decision_is_refused(self):
        base = {k: None for k in record.KEYS if k != "content_sha256"}
        base.update(schema=record.SCHEMA, decision="improved", record_id="x")
        self.assertRaises(ValueError, record.finish, base)


class Guard(unittest.TestCase):
    def test_alarm_when_proved_bound_is_below_worst_case(self):
        class Stub:
            design, _ = exact.load_design(DESIGN)
            design_sha, commit, toolchain, mathlib_rev = "0", "0", "0", "0"
        num = {"worst_case": {"worst_case_delay_ns": 2.25}, "certificate_infimum_ns": 2.25,
               "moving_parameter_worst_case_delay_ns": 2.25, "predictions": {}}
        captured = {}
        orig = run_search.Experiment

        class Capture(orig):
            def __init__(self, env, exp, prefix, kind, evidence_fn, guard_fn):
                captured["evidence"], captured["guard"] = evidence_fn, guard_fn
                raise KeyboardInterrupt
        run_search.Experiment = Capture
        try:
            run_search.deadline_experiment(Stub(), "rise", num)
        except KeyboardInterrupt:
            pass
        finally:
            run_search.Experiment = orig
        p = propose.Proposal("x", "rise_certificate", {}, {"tau": "2.2000"})
        ev = captured["evidence"](p, None)
        self.assertRaises(run_search.SoundnessAlarm, captured["guard"], p, Fr("2.2"), ev)
        p = propose.Proposal("x", "rise_certificate", {}, {"tau": "2.2600"})
        captured["guard"](p, Fr("2.26"), captured["evidence"](p, None))     # no alarm
        # a Lean-proved floor above the numerical worst case is also an alarm
        num["worst_case"]["worst_case_delay_ns"] = 2.0
        self.assertRaises(run_search.SoundnessAlarm, run_search.deadline_experiment,
                          Stub(), "rise", num)


if __name__ == "__main__":
    unittest.main(verbosity=2)
