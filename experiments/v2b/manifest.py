"""Run manifest: hashes of inputs, code and outputs; versions; seeds; settings; timestamps."""
from __future__ import annotations

import hashlib
import platform
import subprocess
import sys
from fractions import Fraction
from pathlib import Path


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def code_hashes(experiments_dir: Path) -> dict:
    out = {}
    for p in sorted(experiments_dir.rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and "work" not in p.parts and p.suffix in (".py", ".txt", ".cir", ".json", ".sh"):
            out[str(p.relative_to(experiments_dir.parent))] = sha256_file(p)
    return out


def output_hashes(run_dir: Path, exclude=("manifest.json",)) -> dict:
    out = {}
    for p in sorted(run_dir.rglob("*")):
        if p.is_file() and p.name not in exclude:
            out[str(p.relative_to(run_dir))] = {"sha256": sha256_file(p), "bytes": p.stat().st_size}
    return out


def environment() -> dict:
    import matplotlib
    import numpy
    import scipy

    env = {
        "python": sys.version,
        "python_executable": sys.executable,
        "platform": platform.platform(),
        "machine": platform.machine(),
        "packages": {"numpy": numpy.__version__, "scipy": scipy.__version__, "matplotlib": matplotlib.__version__},
    }
    try:
        env["uv"] = subprocess.run(["uv", "--version"], capture_output=True, text=True, timeout=20).stdout.strip()
    except Exception:  # uv is only needed to create the environment
        env["uv"] = "not found on PATH"
    return env


def git_state(repo: Path) -> dict:
    try:
        r = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True, timeout=20)
        if r.returncode == 0:
            st = subprocess.run(["git", "-C", str(repo), "status", "--porcelain", "--", "experiments"], capture_output=True, text=True, timeout=20)
            dirty = bool(st.stdout.strip())
            return {"head_commit_at_run_time": r.stdout.strip(), "experiments_tree_differs_from_head": dirty,
                    "note": "workstream D does not commit; if the experiments tree differs from HEAD (untracked or modified files) the code is identified by the per-file SHA-256 list, not by the commit"}
        return {"commit": None, "note": "repository has no commits; code is identified by the per-file SHA-256 list"}
    except Exception as exc:
        return {"commit": None, "note": f"git unavailable: {exc}"}


def jsonable(x):
    if isinstance(x, Fraction):
        return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x
