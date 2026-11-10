"""Design records as exact rationals, closed-form margins, and the admissibility checker.

The record is read exactly as written: ``box[k] = (first, second)`` is taken as
``(lo, hi)`` WITHOUT sorting. Whether ``lo <= hi`` is a condition the checker
tests; it is never repaired silently.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import dataclass, replace
from fractions import Fraction
from pathlib import Path
from typing import Any

THETA_KEYS = ("VDD", "kn", "kp", "Vtn", "Vtp")
BOX_KEYS = THETA_KEYS + ("C",)


class DesignFormatError(ValueError):
    """The JSON is not a well-formed design record (distinct from inadmissible)."""


def _frac(x: Any, where: str) -> Fraction:
    if not isinstance(x, str):
        raise DesignFormatError(
            f"{where}: expected a decimal string, got {type(x).__name__} ({x!r}); "
            "binary floats are rejected so that the record stays exact"
        )
    try:
        return Fraction(x)
    except (ValueError, ZeroDivisionError) as exc:
        raise DesignFormatError(f"{where}: cannot parse {x!r} as a rational") from exc


@dataclass(frozen=True)
class Design:
    name: str
    status: str
    box: dict  # key -> (lo, hi) exactly as written
    eps: Fraction
    VIL: Fraction
    VIH: Fraction
    VOL: Fraction
    VOH: Fraction
    Vlo: Fraction
    Vhi: Fraction
    uHi: Fraction
    uLo: Fraction
    sha256: str | None = None
    path: str | None = None

    def lo(self, key: str) -> Fraction:
        return self.box[key][0]

    def hi(self, key: str) -> Fraction:
        return self.box[key][1]

    def with_box(self, key: str, lo: str | Fraction, hi: str | Fraction, name: str | None = None) -> "Design":
        box = dict(self.box)
        box[key] = (Fraction(lo), Fraction(hi))
        return replace(self, box=box, name=name or self.name, sha256=None, path=None)

    def with_eps(self, eps: str | Fraction, name: str | None = None) -> "Design":
        return replace(self, eps=Fraction(eps), name=name or self.name, sha256=None, path=None)


def at_supply(D: Design, V0) -> Design:
    """The record restricted to one supply value (docs/model.md 6.1, interface.md v1 rev. 3):
    supply range collapsed to V0 and the top of the safe domain set to V0 + (V_hi - VDD_max)."""
    V0 = Fraction(V0)
    box = dict(D.box)
    box["VDD"] = (V0, V0)
    return replace(D, box=box, Vhi=V0 + (D.Vhi - D.hi("VDD")), name=f"{D.name}@VDD={dec(V0)}", sha256=None, path=None)


def R_hiN_prime(D: Design) -> Fraction:
    """R_hiN with V_hi replaced by VDD_min + (V_hi - VDD_max) (the extra condition eps < R_hiN')."""
    vh = D.lo("VDD") + (D.Vhi - D.hi("VDD"))
    return D.lo("kn") / 2 * (psq(D.uHi - D.hi("Vtn")) - psq(D.uHi - vh - D.hi("Vtn")))


def design_from_dict(d: dict, sha256: str | None = None, path: str | None = None) -> Design:
    try:
        box = {}
        for k in BOX_KEYS:
            pair = d["box"][k]
            if not (isinstance(pair, list) and len(pair) == 2):
                raise DesignFormatError(f"box.{k}: expected [lo, hi]")
            box[k] = (_frac(pair[0], f"box.{k}[0]"), _frac(pair[1], f"box.{k}[1]"))
        th, sd, bs = d["thresholds"], d["safe_domain"], d["barrier_split"]
        return Design(
            name=str(d["name"]),
            status=str(d.get("status", "")),
            box=box,
            eps=_frac(d["eps"], "eps"),
            VIL=_frac(th["VIL"], "thresholds.VIL"),
            VIH=_frac(th["VIH"], "thresholds.VIH"),
            VOL=_frac(th["VOL"], "thresholds.VOL"),
            VOH=_frac(th["VOH"], "thresholds.VOH"),
            Vlo=_frac(sd["Vlo"], "safe_domain.Vlo"),
            Vhi=_frac(sd["Vhi"], "safe_domain.Vhi"),
            uHi=_frac(bs["uHi"], "barrier_split.uHi"),
            uLo=_frac(bs["uLo"], "barrier_split.uLo"),
            sha256=sha256,
            path=path,
        )
    except KeyError as exc:
        raise DesignFormatError(f"missing field {exc}") from exc


def load_design(path: str | Path) -> Design:
    raw = Path(path).read_bytes()
    return design_from_dict(json.loads(raw), sha256=hashlib.sha256(raw).hexdigest(), path=str(path))


def dec(x: Fraction, digits: int = 15) -> str:
    """Decimal string of a rational: exact if it terminates within 40 places, else rounded."""
    x = Fraction(x)
    den = x.denominator
    for p in (2, 5):
        while den % p == 0:
            den //= p
    if den == 1:
        # terminating decimal: print exactly
        n, d = x.numerator, x.denominator
        scale = 0
        while (10**scale) % d != 0:
            scale += 1
        q = abs(n) * (10**scale // d)
        s = str(q).rjust(scale + 1, "0")
        body = s[:-scale] + "." + s[-scale:] if scale else s
        return ("-" if n < 0 else "") + body
    sign = "-" if x < 0 else ""
    q = abs(x)
    scaled = (q.numerator * 10**digits * 2 + q.denominator) // (2 * q.denominator)  # round half up
    s = str(scaled).rjust(digits + 1, "0")
    return f"{sign}{s[:-digits]}.{s[-digits:]}"


def frac_record(x: Fraction | None) -> dict | None:
    if x is None:
        return None
    x = Fraction(x)
    den = x.denominator
    for p in (2, 5):
        while den % p == 0:
            den //= p
    return {
        "fraction": f"{x.numerator}/{x.denominator}",
        "decimal": dec(x),
        "decimal_is_exact": den == 1,
        "float": float(x),
    }


def design_to_dict(D: Design) -> dict:
    return {
        "name": D.name,
        "status": D.status,
        "box": {k: [dec(D.box[k][0]), dec(D.box[k][1])] for k in BOX_KEYS},
        "eps": dec(D.eps),
        "thresholds": {"VIL": dec(D.VIL), "VIH": dec(D.VIH), "VOL": dec(D.VOL), "VOH": dec(D.VOH)},
        "safe_domain": {"Vlo": dec(D.Vlo), "Vhi": dec(D.Vhi)},
        "barrier_split": {"uHi": dec(D.uHi), "uLo": dec(D.uLo)},
    }


# --------------------------------------------------------------------------
# Device law, exact (works for Fraction, int, float scalars)
# --------------------------------------------------------------------------

def psq(x):
    """psq(x) = max(x, 0)^2."""
    return x * x if x > 0 else x * 0


def nmos_ab(vg, va, vb, k, vt):
    """Symmetric square-law NMOS: current from terminal A to terminal B."""
    return k / 2 * (psq(vg - vb - vt) - psq(vg - va - vt))


def pmos_ab(vg, va, vb, k, vt):
    """Symmetric square-law PMOS: current from terminal A to terminal B."""
    return k / 2 * (psq(va - vg - vt) - psq(vb - vg - vt))


def I_n(u, v, kn, Vtn):
    """interface.md section 3: output -> ground."""
    return kn / 2 * (psq(u - Vtn) - psq(u - v - Vtn))


def I_p(u, v, VDD, kp, Vtp):
    """interface.md section 3: supply -> output."""
    return kp / 2 * (psq(VDD - u - Vtp) - psq(v - u - Vtp))


def I_net(u, v, th):
    """Net current into the output node. ``th`` = (VDD, kn, kp, Vtn, Vtp)."""
    VDD, kn, kp, Vtn, Vtp = th
    return I_p(u, v, VDD, kp, Vtp) - I_n(u, v, kn, Vtn)


def I_net_miswired(u, v, th):
    """Negative control: NMOS as pull-up from VDD, PMOS as pull-down to ground.

    NMOS: A = VDD (drain), B = output (source); PMOS: A = output (source), B = ground (drain).
    Both gates on u. Same device functions as the correct circuit, roles swapped.
    """
    VDD, kn, kp, Vtn, Vtp = th
    return nmos_ab(u, VDD, v, kn, Vtn) - pmos_ab(u, v, 0 * v, kp, Vtp)


# --------------------------------------------------------------------------
# Closed-form margins (exact)
# --------------------------------------------------------------------------

def I_up(D: Design, c):
    return D.lo("kp") / 2 * (
        psq(D.lo("VDD") - D.VIL - D.hi("Vtp")) - psq(c - D.VIL - D.hi("Vtp"))
    ) - D.hi("kn") / 2 * psq(D.VIL - D.lo("Vtn"))


def I_dn(D: Design, c):
    return D.lo("kn") / 2 * (
        psq(D.VIH - D.hi("Vtn")) - psq(D.VIH - c - D.hi("Vtn"))
    ) - D.hi("kp") / 2 * psq(D.hi("VDD") - D.VIH - D.lo("Vtp"))


def R_hiP(D: Design):
    a = D.lo("VDD") - D.uHi - D.hi("Vtp")
    return D.lo("kp") / 2 * (psq(a + (D.Vhi - D.hi("VDD"))) - psq(a))


def R_hiN(D: Design):
    return D.lo("kn") / 2 * (psq(D.uHi - D.hi("Vtn")) - psq(D.uHi - D.Vhi - D.hi("Vtn")))


def R_loN(D: Design):
    return D.lo("kn") / 2 * (psq(D.uLo - D.Vlo - D.hi("Vtn")) - psq(D.uLo - D.hi("Vtn")))


def R_loP(D: Design):
    return D.lo("kp") / 2 * (psq(D.lo("VDD") - D.uLo - D.hi("Vtp")) - psq(D.Vlo - D.uLo - D.hi("Vtp")))


def tau_up(D: Design) -> Fraction | None:
    m = I_up(D, D.VOH) - D.eps
    return D.hi("C") * (D.VOH - D.Vlo) / m if m > 0 else None


def tau_dn(D: Design) -> Fraction | None:
    m = I_dn(D, D.VOL) - D.eps
    return D.hi("C") * (D.Vhi - D.VOL) / m if m > 0 else None


def closed_form(D: Design) -> dict:
    return {
        "I_up(V_OH)": I_up(D, D.VOH),
        "I_dn(V_OL)": I_dn(D, D.VOL),
        "R_hiP": R_hiP(D),
        "R_hiN": R_hiN(D),
        "R_loN": R_loN(D),
        "R_loP": R_loP(D),
        "tau_up": tau_up(D),
        "tau_dn": tau_dn(D),
    }


# --------------------------------------------------------------------------
# Admissibility
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Condition:
    id: str
    group: str  # "box" | "order" | "margin"
    source: str  # where the condition comes from
    statement: str
    lhs: Fraction
    rel: str
    rhs: Fraction
    holds: bool

    def as_dict(self) -> dict:
        return {
            "id": self.id,
            "group": self.group,
            "source": self.source,
            "statement": self.statement,
            "lhs": dec(self.lhs),
            "rel": self.rel,
            "rhs": dec(self.rhs),
            "holds": self.holds,
        }


def _cond(id_, group, source, statement, lhs, rel, rhs) -> Condition:
    lhs, rhs = Fraction(lhs), Fraction(rhs)
    holds = {"<": lhs < rhs, "<=": lhs <= rhs}[rel]
    return Condition(id_, group, source, statement, lhs, rel, rhs, holds)


def admissibility(D: Design) -> list[Condition]:
    """Workstream D's reading of ``Admissible D`` (interface.md section 6).

    Groups: box consistency, threshold ordering, six current-margin inequalities.
    Conditions whose ``source`` is not "interface.md s6" are the ones the prose
    implies elsewhere (C_min > 0, [V_lo, V_hi] contains [0, VDD], V_tp > 0, eps >= 0,
    k > 0); they should be compared with the Lean definition once it exists.
    Margins are evaluated "naively" (first entry = min, second = max) even when
    the box is inverted, so that the report can show what a margins-only check
    would have concluded.
    """
    c: list[Condition] = []
    for k in BOX_KEYS:
        c.append(_cond(f"B-{k}", "box", "interface.md s6 (box consistency)", f"{k}_lo <= {k}_hi", D.lo(k), "<=", D.hi(k)))
    c.append(_cond("B-Cpos", "box", "HANDOFF s2 (0 < C_min)", "0 < C_lo", 0, "<", D.lo("C")))
    c.append(_cond("B-knpos", "box", "implied (k is a transconductance)", "0 < kn_lo", 0, "<", D.lo("kn")))
    c.append(_cond("B-kppos", "box", "implied (k is a transconductance)", "0 < kp_lo", 0, "<", D.lo("kp")))
    c.append(_cond("B-Vtppos", "box", "interface.md s3 (V_tp > 0)", "0 < Vtp_lo", 0, "<", D.lo("Vtp")))
    c.append(_cond("B-eps", "box", "implied (eps bounds an absolute value)", "0 <= eps", 0, "<=", D.eps))
    c.append(_cond("O-1", "order", "interface.md s5 (static discipline)", "V_OL <= V_IL", D.VOL, "<=", D.VIL))
    c.append(_cond("O-2", "order", "interface.md s5 (static discipline)", "V_IL < V_IH", D.VIL, "<", D.VIH))
    c.append(_cond("O-3", "order", "interface.md s5 (static discipline)", "V_IH <= V_OH", D.VIH, "<=", D.VOH))
    c.append(_cond("O-4", "order", "interface.md s5 (safe domain contains [0, VDD])", "V_lo <= 0", D.Vlo, "<=", 0))
    c.append(_cond("O-5", "order", "interface.md s5 (safe domain contains [0, VDD])", "VDD_hi <= V_hi", D.hi("VDD"), "<=", D.Vhi))
    cf = closed_form(D)
    for i, key in enumerate(("I_up(V_OH)", "I_dn(V_OL)", "R_hiP", "R_hiN", "R_loN", "R_loP"), start=1):
        c.append(_cond(f"M-{i}", "margin", "interface.md s6 (current margin)", f"eps < {key}", D.eps, "<", cf[key]))
    return c


def is_admissible(D: Design) -> bool:
    return all(x.holds for x in admissibility(D))


def margins_only_pass(D: Design) -> bool:
    """What a checker that looked only at the six margin inequalities would say."""
    return all(x.holds for x in admissibility(D) if x.group == "margin")


def corners(D: Design) -> list[dict]:
    """All 2^5 corners of the parameter box, in a fixed order (VDD, kn, kp, Vtn, Vtp)."""
    out = []
    for bits in itertools.product((0, 1), repeat=len(THETA_KEYS)):
        code = "".join("LH"[b] for b in bits)
        theta = tuple(D.box[k][b] for k, b in zip(THETA_KEYS, bits))
        out.append({"code": code, "theta": theta})
    return out


def corner_by_code(D: Design, code: str) -> tuple:
    return tuple(D.box[k]["LH".index(ch)] for k, ch in zip(THETA_KEYS, code))


def decode(v, D: Design):
    """Three-valued decoding (interface.md section 5): True / False / None (undefined)."""
    if v >= D.VOH:
        return True
    if v <= D.VOL:
        return False
    return None
