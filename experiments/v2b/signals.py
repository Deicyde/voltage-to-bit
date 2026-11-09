"""Time signals (inputs u(t) and time-only disturbances w(t)) as small JSON-able specs.

kinds
  const : value
  ramp  : clip(edge + slew * (t - t_edge), lo, hi)      (slew in V/ns, signed)
  sin   : offset + amp * sin(2 pi freq t + phase)        (freq in GHz = 1/ns)
  pwl   : continuous piecewise-linear through values[i] at t = i * step (held constant afterwards)
"""
from __future__ import annotations

import math

import numpy as np


def evaluate(spec: dict, t) -> np.ndarray:
    t = np.asarray(t, dtype=float)
    k = spec["kind"]
    if k == "const":
        return np.full(t.shape, float(spec["value"]))
    if k == "ramp":
        return np.clip(spec["edge"] + spec["slew"] * (t - spec["t_edge"]), spec["lo"], spec["hi"])
    if k == "sin":
        return spec["offset"] + spec["amp"] * np.sin(2.0 * math.pi * spec["freq"] * t + spec["phase"])
    if k == "pwl":
        vals = np.asarray(spec["values"], dtype=float)
        tk = spec["step"] * np.arange(vals.size)
        return np.interp(t, tk, vals)
    raise ValueError(f"unknown signal kind {k!r}")


def scalar(spec: dict):
    """Fast scalar callable t -> value."""
    k = spec["kind"]
    if k == "const":
        c = float(spec["value"])
        return lambda t: c
    if k == "ramp":
        e, s, te, lo, hi = spec["edge"], spec["slew"], spec["t_edge"], spec["lo"], spec["hi"]
        return lambda t: min(max(e + s * (t - te), lo), hi)
    if k == "sin":
        o, a, w, p = spec["offset"], spec["amp"], 2.0 * math.pi * spec["freq"], spec["phase"]
        return lambda t: o + a * math.sin(w * t + p)
    if k == "pwl":
        vals = np.asarray(spec["values"], dtype=float)
        step = float(spec["step"])
        n = vals.size

        def f(t):
            x = t / step
            if x <= 0.0:
                return float(vals[0])
            if x >= n - 1:
                return float(vals[-1])
            i = int(x)
            fr = x - i
            return float(vals[i] * (1.0 - fr) + vals[i + 1] * fr)

        return f
    raise ValueError(f"unknown signal kind {k!r}")


def breakpoints(spec: dict, t_end: float) -> list[float]:
    """Times in (0, t_end) where the signal has a kink (integration is restarted there)."""
    k = spec["kind"]
    out: list[float] = []
    if k == "ramp" and spec["slew"] != 0.0:
        for level in (spec["lo"], spec["hi"]):
            out.append(spec["t_edge"] + (level - spec["edge"]) / spec["slew"])
    elif k == "pwl":
        out = [spec["step"] * i for i in range(1, len(spec["values"]))]
    return sorted(x for x in out if 0.0 < x < t_end)
