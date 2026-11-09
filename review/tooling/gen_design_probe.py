#!/usr/bin/env python3
"""Workstream E tooling probe: how scripts/gen_design.py treats unusual JSON.

usage: gen_design_probe.py <frozen checkout> <scratch dir>

Nothing is written into the checkout. Each case writes a modified copy of the
design JSON into the scratch dir and runs the generator on it with a scratch
output path.
"""
import json
import subprocess
import sys
from pathlib import Path

F, S = Path(sys.argv[1]), Path(sys.argv[2])
gen = F / "scripts" / "gen_design.py"
base = json.loads((F / "designs" / "illustrative-1v8.json").read_text())


def run(tag, rec, raw=None):
    j, l = S / f"{tag}.json", S / f"{tag}.lean"
    j.write_text(raw if raw is not None else json.dumps(rec, ensure_ascii=False, indent=2))
    p = subprocess.run([sys.executable, str(gen), str(j), str(l), "illustrative"], capture_output=True, text=True)
    out = l.read_text() if l.exists() and p.returncode == 0 else ""
    return p.returncode, (p.stdout + p.stderr).strip().splitlines()[-1:] , out


# 0. --check on the real record
p = subprocess.run([sys.executable, str(gen), "--check", "designs/illustrative-1v8.json",
                    "VoltageToBit/Examples/IllustrativeDesign.lean", "illustrative"], cwd=F, capture_output=True, text=True)
print("0. --check on the frozen record:", p.returncode, p.stdout.strip())

# 1. trailing newline inside a number string is accepted (Python `$` matches before a final \n)
rec = json.loads(json.dumps(base)); rec["eps"] = "2\n"
rc, msg, out = run("case1", rec)
print("1. eps = '2\\n'      -> exit", rc, msg, "| generated line:", repr([x for x in out.splitlines() if "eps" in x][:1]))

# 2. non-ASCII digits are accepted by \d (Lean will then fail to parse, i.e. fail closed)
rec = json.loads(json.dumps(base)); rec["eps"] = "٢"   # ARABIC-INDIC DIGIT TWO
rc, msg, out = run("case2", rec)
print("2. eps = U+0662      -> exit", rc, msg, "| generated line:", repr([x for x in out.splitlines() if "eps" in x][:1]))

# 3. the status string is pasted into a doc comment without escaping
rec = json.loads(json.dumps(base))
rec["status"] = "ILLUSTRATIVE -/\ntheorem injected_from_json : True := trivial\n/-- resumed comment"
rc, msg, out = run("case3", rec)
inj = [x for x in out.splitlines() if "injected_from_json" in x]
print("3. status with '-/'  -> exit", rc, msg, "| Lean code injected outside the comment:", inj)

# 4. duplicate JSON keys: Python keeps the last one silently
raw = json.dumps(base, indent=2).replace('"eps": "2"', '"eps": "2",\n  "eps": "1"')
rc, msg, out = run("case4", None, raw)
print("4. duplicate key eps -> exit", rc, msg, "| generated line:", repr([x for x in out.splitlines() if "eps" in x][:1]))

# 5. inverted bounds are not rejected by the generator (they are rejected later, by the Lean proof of Admissible)
rec = json.loads(json.dumps(base)); rec["box"]["kn"] = ["300", "240"]
rc, msg, out = run("case5", rec)
print("5. kn = [300, 240]   -> exit", rc, msg)
