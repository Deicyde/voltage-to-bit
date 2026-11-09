"""Exact rational mirror of the numeric conditions that Lean checks.

This is the *cheap screen*. Every function mirrors one definition of the frozen
Lean library (file and name given in each docstring) and evaluates it with
``fractions.Fraction``, so there is no rounding anywhere.

The screen is never the arbiter. It can only save a Lean run for a proposal
that is obviously invalid; a proposal is accepted only when Lean accepts it.
A disagreement between the screen and Lean is reported as a defect of the run.
"""
from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

DECIMAL = re.compile(r"^-?\d+(\.\d+)?$")

# (Lean field of `Design`, path in the JSON design record).
# Same table as scripts/gen_design.py at the frozen commit.
FIELDS = [
    ("VDDlo", ("box", "VDD", 0)),
    ("VDDhi", ("box", "VDD", 1)),
    ("knlo", ("box", "kn", 0)),
    ("knhi", ("box", "kn", 1)),
    ("kplo", ("box", "kp", 0)),
    ("kphi", ("box", "kp", 1)),
    ("Vtnlo", ("box", "Vtn", 0)),
    ("Vtnhi", ("box", "Vtn", 1)),
    ("Vtplo", ("box", "Vtp", 0)),
    ("Vtphi", ("box", "Vtp", 1)),
    ("Clo", ("box", "C", 0)),
    ("Chi", ("box", "C", 1)),
    ("eps", ("eps",)),
    ("VIL", ("thresholds", "VIL")),
    ("VIH", ("thresholds", "VIH")),
    ("VOL", ("thresholds", "VOL")),
    ("VOH", ("thresholds", "VOH")),
    ("Vlo", ("safe_domain", "Vlo")),
    ("Vhi", ("safe_domain", "Vhi")),
    ("uHi", ("barrier_split", "uHi")),
    ("uLo", ("barrier_split", "uLo")),
]
FIELD_NAMES = [name for name, _ in FIELDS]


class Design:
    """A design record: the 21 numbers of the Lean structure `Design`.

    ``raw`` keeps the decimal strings exactly as written in the JSON file;
    the attributes hold the same numbers as exact fractions.
    """

    def __init__(self, raw: dict[str, str]):
        missing = [k for k in FIELD_NAMES if k not in raw]
        if missing:
            raise ValueError(f"design record lacks fields {missing}")
        self.raw = {k: raw[k] for k in FIELD_NAMES}
        for key, text in self.raw.items():
            if not DECIMAL.match(text):
                raise ValueError(f"design field {key} must be a decimal string, got {text!r}")
            setattr(self, key, Fraction(text))

    def replace(self, **changes: str) -> "Design":
        """A copy with some fields replaced (values are decimal strings)."""
        raw = dict(self.raw)
        for key, text in changes.items():
            if key not in raw:
                raise KeyError(key)
            raw[key] = text
        return Design(raw)


def load_design(path: Path) -> tuple[Design, str]:
    """Read a JSON design record. Returns the record and the SHA-256 of the file."""
    data = Path(path).read_bytes()
    record = json.loads(data)
    raw = {}
    for name, where in FIELDS:
        value = record
        for key in where:
            value = value[key]
        if not isinstance(value, str):
            raise ValueError(f"design field {'.'.join(map(str, where))} must be a decimal string")
        raw[name] = value
    return Design(raw), hashlib.sha256(data).hexdigest()


# --------------------------------------------------------------------------
# Model/PosSq.lean, Model/Inverter.lean
# --------------------------------------------------------------------------

def psq(x: Fraction) -> Fraction:
    """`psq x = (max x 0)^2` (Model/PosSq.lean)."""
    return x * x if x >= 0 else Fraction(0)


def lean_div(a: Fraction, b: Fraction) -> Fraction:
    """Division with Lean's convention `x / 0 = 0` for real numbers."""
    return a / b if b != 0 else Fraction(0)


def Iup(D: Design, c: Fraction) -> Fraction:
    """`Design.Iup`: worst-corner pull-up current for `u <= VIL`, `v <= c`."""
    return (D.kplo / 2 * (psq(D.VDDlo - D.VIL - D.Vtphi) - psq(c - D.VIL - D.Vtphi))
            - D.knhi / 2 * psq(D.VIL - D.Vtnlo))


def Idn(D: Design, c: Fraction) -> Fraction:
    """`Design.Idn`: worst-corner pull-down current for `VIH <= u`, `c <= v`."""
    return (D.knlo / 2 * (psq(D.VIH - D.Vtnhi) - psq(D.VIH - c - D.Vtnhi))
            - D.kphi / 2 * psq(D.VDDhi - D.VIH - D.Vtplo))


def RhiP(D: Design) -> Fraction:
    """`Design.RhiP`: restoring current at `Vhi`, PMOS branch (`u <= uHi`)."""
    return D.kplo / 2 * (psq(D.VDDlo - D.uHi - D.Vtphi + (D.Vhi - D.VDDhi))
                         - psq(D.VDDlo - D.uHi - D.Vtphi))


def RhiN(D: Design) -> Fraction:
    """`Design.RhiN`: restoring current at `Vhi`, NMOS branch (`uHi <= u`)."""
    return D.knlo / 2 * (psq(D.uHi - D.Vtnhi) - psq(D.uHi - D.Vhi - D.Vtnhi))


def RloN(D: Design) -> Fraction:
    """`Design.RloN`: restoring current at `Vlo`, NMOS branch (`uLo <= u`)."""
    return D.knlo / 2 * (psq(D.uLo - D.Vlo - D.Vtnhi) - psq(D.uLo - D.Vtnhi))


def RloP(D: Design) -> Fraction:
    """`Design.RloP`: restoring current at `Vlo`, PMOS branch (`u <= uLo`)."""
    return D.kplo / 2 * (psq(D.VDDlo - D.uLo - D.Vtphi) - psq(D.Vlo - D.uLo - D.Vtphi))


def tauUp(D: Design) -> Fraction:
    """`Design.tauUp = Chi * (VOH - Vlo) / (Iup VOH - eps)`."""
    return lean_div(D.Chi * (D.VOH - D.Vlo), Iup(D, D.VOH) - D.eps)


def tauDn(D: Design) -> Fraction:
    """`Design.tauDn = Chi * (Vhi - VOL) / (Idn VOL - eps)`."""
    return lean_div(D.Chi * (D.Vhi - D.VOL), Idn(D, D.VOL) - D.eps)


def admissible_conditions(D: Design) -> list[tuple[str, bool, str]]:
    """The 24 fields of `Design.Admissible`, in Lean's order.

    Returns ``(field name, holds, exact inequality as text)`` for each.
    """
    def lt(a, b):
        return a < b, f"{show(a)} < {show(b)}"

    def le(a, b):
        return a <= b, f"{show(a)} <= {show(b)}"

    zero = Fraction(0)
    rows = [
        ("VDD_pos", lt(zero, D.VDDlo)),
        ("VDD_le", le(D.VDDlo, D.VDDhi)),
        ("kn_pos", lt(zero, D.knlo)),
        ("kn_le", le(D.knlo, D.knhi)),
        ("kp_pos", lt(zero, D.kplo)),
        ("kp_le", le(D.kplo, D.kphi)),
        ("Vtn_le", le(D.Vtnlo, D.Vtnhi)),
        ("Vtp_le", le(D.Vtplo, D.Vtphi)),
        ("C_pos", lt(zero, D.Clo)),
        ("C_le", le(D.Clo, D.Chi)),
        ("eps_nonneg", le(zero, D.eps)),
        ("Vlo_le", le(D.Vlo, zero)),
        ("Vhi_ge", le(D.VDDhi, D.Vhi)),
        ("VOL_nonneg", le(zero, D.VOL)),
        ("VOL_le_VIL", le(D.VOL, D.VIL)),
        ("VIL_lt_VIH", lt(D.VIL, D.VIH)),
        ("VIH_le_VOH", le(D.VIH, D.VOH)),
        ("VOH_le", le(D.VOH, D.VDDlo)),
        ("up", lt(D.eps, Iup(D, D.VOH))),
        ("dn", lt(D.eps, Idn(D, D.VOL))),
        ("hiP", lt(D.eps, RhiP(D))),
        ("hiN", lt(D.eps, RhiN(D))),
        ("loN", lt(D.eps, RloN(D))),
        ("loP", lt(D.eps, RloP(D))),
    ]
    return [(name, ok, text) for name, (ok, text) in rows]


# --------------------------------------------------------------------------
# Proofs/Reach.lean, Proofs/Certificate.lean
# --------------------------------------------------------------------------

def segments(D: Design, direction: str, levels: list[Fraction]) -> list[tuple[Fraction, Fraction]]:
    """`Design.upSegs` / `Design.dnSegs`: each level paired with its slope bound."""
    margin = Iup if direction == "rise" else Idn
    return [(c, lean_div(margin(D, c) - D.eps, D.Chi)) for c in levels]


def start_level(D: Design, direction: str) -> Fraction:
    return D.Vlo if direction == "rise" else D.Vhi


def target_level(D: Design, direction: str) -> Fraction:
    return D.VOH if direction == "rise" else D.VOL


def show(x: Fraction) -> str:
    """A number for messages: exact decimal when there is one, else a fraction."""
    return dec_str(x) if is_decimal(x) else f"{x.numerator}/{x.denominator}"


def segs_ok(direction: str, start: Fraction, segs) -> tuple[bool, str]:
    """`RiseSegs` / `FallSegs`: monotone levels and positive slope bounds."""
    prev = start
    for i, (c, m) in enumerate(segs):
        ordered = prev <= c if direction == "rise" else c <= prev
        if not ordered:
            rel = "<=" if direction == "rise" else ">="
            return False, (f"level {i + 1} out of order: {show(prev)} {rel} {show(c)} is false")
        if not m > 0:
            return False, (f"level {i + 1} ({show(c)} V) has slope bound {show(m)} V/ns, not "
                           "positive: its current margin does not exceed eps")
        prev = c
    return True, ""


def total_time(direction: str, start: Fraction, segs) -> Fraction:
    """`riseTime` / `fallTime`, with Lean's `x / 0 = 0`."""
    prev, total = start, Fraction(0)
    for c, m in segs:
        step = (c - prev) if direction == "rise" else (prev - c)
        total += lean_div(step, m)
        prev = c
    return total


def final_level(start: Fraction, segs) -> Fraction:
    """`finalLevel`."""
    return segs[-1][0] if segs else start


def screen_certificate(D: Design, direction: str, levels: list[Fraction], tau: Fraction) -> dict:
    """Evaluate `ValidRiseCert` / `ValidFallCert` exactly.

    The three conjuncts are reported separately, in Lean's order.
    """
    if not levels:
        raise ValueError("a certificate has at least one level")
    start = start_level(D, direction)
    segs = segments(D, direction, levels)
    ok_segs, why = segs_ok(direction, start, segs)
    ok_final = final_level(start, segs) == target_level(D, direction)
    exact_sum = total_time(direction, start, segs)
    ok_time = exact_sum <= tau
    if not ok_segs:
        first, detail = "segments", why
    elif not ok_final:
        first = "final_level"
        detail = (f"last level {show(levels[-1])} V is not the output threshold "
                  f"{show(target_level(D, direction))} V")
    elif not ok_time:
        first = "deadline"
        detail = f"exact sum {float(exact_sum):.10f} ns exceeds claimed deadline {float(tau):.10f} ns"
    else:
        first, detail = None, ""
    return {
        "valid": ok_segs and ok_final and ok_time,
        "conditions": {"segments": ok_segs, "final_level": ok_final, "deadline": ok_time},
        "first_failure": first,
        "detail": detail,
        "exact_sum": exact_sum,
    }


def screen_admissible(D: Design) -> dict:
    """Evaluate `Design.Admissible` exactly."""
    rows = admissible_conditions(D)
    failing = [name for name, ok, _ in rows if not ok]
    detail = "; ".join(f"{name}: {text} is false" for name, ok, text in rows if not ok)
    return {
        "valid": not failing,
        "conditions": {name: ok for name, ok, _ in rows},
        "first_failure": failing[0] if failing else None,
        "failing": failing,
        "detail": detail,
    }


# --------------------------------------------------------------------------
# Decimal helpers
# --------------------------------------------------------------------------

def is_decimal(x: Fraction) -> bool:
    """True when `x` has a finite decimal expansion."""
    d = x.denominator
    for p in (2, 5):
        while d % p == 0:
            d //= p
    return d == 1


def dec_str(x: Fraction, places: int | None = None) -> str:
    """Exact decimal string of `x`.

    With ``places`` the string has exactly that many decimals (and `x` must be
    representable); without it the shortest exact form is used.
    """
    if not is_decimal(x):
        raise ValueError(f"{x} has no finite decimal expansion")
    k = 0
    while (x * 10 ** k).denominator != 1:
        k += 1
    if places is not None:
        if k > places:
            raise ValueError(f"{x} needs more than {places} decimals")
        k = places
    n = int(x * 10 ** k)
    sign = "-" if n < 0 else ""
    digits = str(abs(n)).rjust(k + 1, "0")
    return sign + (digits[:-k] + "." + digits[-k:] if k else digits)


def ceil_dec(x: Fraction, places: int) -> Fraction:
    """Smallest multiple of 10^-places that is >= x."""
    q = 10 ** places
    return Fraction(-((-x.numerator * q) // x.denominator), q)


def floor_dec(x: Fraction, places: int) -> Fraction:
    """Largest multiple of 10^-places that is <= x."""
    q = 10 ** places
    return Fraction((x.numerator * q) // x.denominator, q)


def below_dec(x: Fraction, places: int) -> Fraction:
    """Largest multiple of 10^-places that is strictly < x."""
    f = floor_dec(x, places)
    return f - Fraction(1, 10 ** places) if f == x else f


def nearest_dec(x: Fraction, places: int) -> Fraction:
    """Multiple of 10^-places nearest to x (ties away from zero)."""
    q = 10 ** places
    return Fraction(int((abs(x) * q + Fraction(1, 2)) // 1), q) * (1 if x >= 0 else -1)


def frac_str(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
