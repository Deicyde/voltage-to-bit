"""Shared helpers: float view of a design, seeded RNG streams, compact writers."""
from __future__ import annotations

import csv
import json
import zlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np

from . import MASTER_SEED
from .design import THETA_KEYS, Design, corners

SEED_LOG: dict[str, list[int]] = {}


def rng_for(tag: str) -> np.random.Generator:
    """Independent, reproducible stream per named purpose. Entropy = [MASTER_SEED, crc32(tag)]."""
    entropy = [MASTER_SEED, zlib.crc32(tag.encode("utf-8"))]
    SEED_LOG[tag] = entropy
    return np.random.Generator(np.random.PCG64(np.random.SeedSequence(entropy)))


@dataclass(frozen=True)
class FD:
    """Float view of a design record."""

    VDD_lo: float
    VDD_hi: float
    kn_lo: float
    kn_hi: float
    kp_lo: float
    kp_hi: float
    Vtn_lo: float
    Vtn_hi: float
    Vtp_lo: float
    Vtp_hi: float
    C_lo: float
    C_hi: float
    eps: float
    VIL: float
    VIH: float
    VOL: float
    VOH: float
    Vlo: float
    Vhi: float
    uHi: float
    uLo: float

    def lo(self, k: str) -> float:
        return getattr(self, f"{k}_lo")

    def hi(self, k: str) -> float:
        return getattr(self, f"{k}_hi")


def float_design(D: Design) -> FD:
    kw = {}
    for k in THETA_KEYS + ("C",):
        kw[f"{k}_lo"] = float(D.lo(k))
        kw[f"{k}_hi"] = float(D.hi(k))
    for k in ("eps", "VIL", "VIH", "VOL", "VOH", "Vlo", "Vhi", "uHi", "uLo"):
        kw[k] = float(getattr(D, k))
    return FD(**kw)


def corner_array(D: Design) -> tuple[list[str], np.ndarray]:
    """(codes, array of shape (32, 5)) of the box corners as floats."""
    cs = corners(D)
    return [c["code"] for c in cs], np.array([[float(x) for x in c["theta"]] for c in cs])


def nominal_theta(D: Design) -> tuple:
    return tuple((D.lo(k) + D.hi(k)) / 2 for k in THETA_KEYS)


def lattice_thetas(D: Design, n: int, tag: str, steps: dict[str, Fraction] | None = None) -> list[tuple]:
    """Seeded random interior parameter points on a decimal lattice (exact rationals).

    Default lattice: 1 mV for voltages, 1 uA/V^2 for k. Lattice points make exact
    integer re-evaluation possible; they are still generic interior points.
    """
    steps = steps or {"VDD": Fraction(1, 1000), "Vtn": Fraction(1, 1000), "Vtp": Fraction(1, 1000), "kn": Fraction(1), "kp": Fraction(1)}
    rng = rng_for(tag)
    out = []
    for _ in range(n):
        th = []
        for k in THETA_KEYS:
            lo, hi, st = D.lo(k), D.hi(k), steps[k]
            m = int((hi - lo) / st)
            th.append(lo + st * int(rng.integers(0, m + 1)))
        out.append(tuple(th))
    return out


def theta_floats(thetas: list[tuple]) -> np.ndarray:
    return np.array([[float(x) for x in th] for th in thetas], dtype=float)


class NpEncoder(json.JSONEncoder):
    def default(self, o):  # noqa: D401
        if isinstance(o, np.integer):
            return int(o)
        if isinstance(o, np.floating):
            return float(o)
        if isinstance(o, np.bool_):
            return bool(o)
        if isinstance(o, np.ndarray):
            return o.tolist()
        if isinstance(o, Fraction):
            return f"{o.numerator}/{o.denominator}"
        return super().default(o)


def write_json(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=1, sort_keys=True, cls=NpEncoder, allow_nan=True) + "\n")


def fmt(x) -> str:
    if isinstance(x, (float, np.floating)):
        return repr(float(x))
    if isinstance(x, (np.integer,)):
        return str(int(x))
    if isinstance(x, (bool, np.bool_)):
        return "1" if x else "0"
    return str(x)


def write_csv(path: Path, header: list[str], rows) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(header)
        for r in rows:
            w.writerow([fmt(x) for x in r])
