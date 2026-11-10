#!/usr/bin/env python3
"""Generate the Lean definition of a design record from a JSON design file.

The JSON file is the single source for the numbers used both by the Lean
instance and by the numerical experiments. Numbers are decimal strings and are
copied verbatim into Lean decimal literals, so no rounding can occur.

Usage:
    python3 scripts/gen_design.py designs/illustrative-1v8.json \
        VoltageToBit/Examples/IllustrativeDesign.lean illustrative
    python3 scripts/gen_design.py --check <same arguments>

With --check nothing is written; the exit status is 1 if the Lean file on disk
differs from what would be generated.

Exit status: 0 success; 1 stale (--check only); 2 the input was rejected or
the command line is wrong. A rejected input writes nothing.

What is validated before anything is generated (the JSON is treated as
untrusted text, because two of its strings end up inside a Lean comment and
its numbers end up as Lean source):

* the file is UTF-8 JSON, one object, with no duplicated key at any level;
* exactly the expected keys are present at every level (none missing, none
  unknown), and the `units` block states the units that the generated
  docstring hard-codes;
* every number is a string that fully matches `-?[0-9]+(\\.[0-9]+)?` with
  ASCII digits (no sign `+`, no exponent, no surrounding whitespace);
* `name` is a plain ASCII token; `status` contains no comment delimiter
  (`-/`, `/-`) and no control, format or line-separator character; the same
  holds for the JSON path, which is quoted in the header;
* the definition name is a plain ASCII Lean identifier;
* no interval is inverted: each box range, the safe domain, and each pair of
  logic levels has its lower number less than or equal to its upper number.

The last item is a filter for obviously malformed records. It is not the
admissibility check: that is `Design.Admissible`, proved in Lean.
"""
import hashlib
import json
import re
import sys
import unicodedata
from fractions import Fraction
from pathlib import Path

# Used with fullmatch only. `[0-9]`, not `\d`: `\d` also matches non-ASCII digits.
DECIMAL = re.compile(r"-?[0-9]+(?:\.[0-9]+)?")
NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,63}")
LEAN_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']{0,63}")
MAX_STATUS_LENGTH = 1000

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

# The schema. Every key listed is required; no other key is accepted, except
# the optional free-text `units.note`, which is never copied into the output.
TOP_KEYS = ("name", "status", "units", "box", "eps", "thresholds", "safe_domain", "barrier_split")
BOX_KEYS = ("VDD", "kn", "kp", "Vtn", "Vtp", "C")
SCALAR_BLOCKS = {
    "thresholds": ("VIL", "VIH", "VOL", "VOH"),
    "safe_domain": ("Vlo", "Vhi"),
    "barrier_split": ("uHi", "uLo"),
}
# The generated docstring says "Units: V, µA, fF, ns; transconductance in
# µA/V²". A record declaring anything else must not be given that label.
UNITS = {
    "voltage": "V",
    "current": "uA",
    "capacitance": "fF",
    "time": "ns",
    "transconductance_k": "uA/V^2",
}
UNITS_OPTIONAL = ("note",)

# Pairs (lower, upper) that must satisfy lower <= upper.
ORDERED_PAIRS = [(("box", k, 0), ("box", k, 1)) for k in BOX_KEYS] + [
    (("safe_domain", "Vlo"), ("safe_domain", "Vhi")),
    (("thresholds", "VIL"), ("thresholds", "VIH")),
    (("thresholds", "VOL"), ("thresholds", "VOH")),
]


class DesignError(Exception):
    """The design file or the command line was rejected."""


def dotted(path):
    return ".".join(map(str, path))


def reject_duplicate_keys(pairs):
    record = {}
    for key, value in pairs:
        if key in record:
            raise DesignError(f"duplicate JSON key {key!r}")
        record[key] = value
    return record


def reject_constant(text):
    raise DesignError(f"JSON constant {text} is not allowed")


def check_keys(where, obj, required, optional=()):
    if not isinstance(obj, dict):
        raise DesignError(f"{where} must be a JSON object, got {type(obj).__name__}")
    missing = [k for k in required if k not in obj]
    unknown = [k for k in obj if k not in required and k not in optional]
    if missing:
        raise DesignError(f"{where}: missing key(s) {', '.join(map(repr, missing))}")
    if unknown:
        raise DesignError(f"{where}: unknown key(s) {', '.join(map(repr, unknown))}")


def check_comment_text(where, text, max_length):
    """Reject text that cannot be pasted verbatim into a Lean comment."""
    if not isinstance(text, str):
        raise DesignError(f"{where} must be a string, got {type(text).__name__}")
    if not text or len(text) > max_length:
        raise DesignError(f"{where} must have between 1 and {max_length} characters")
    for delimiter in ("-/", "/-"):
        if delimiter in text:
            raise DesignError(f"{where} contains the Lean comment delimiter {delimiter!r}")
    for ch in text:
        category = unicodedata.category(ch)
        # C*: control, format (includes bidirectional overrides), surrogate,
        # private use, unassigned. Zl, Zp: line and paragraph separators.
        if category.startswith("C") or category in ("Zl", "Zp"):
            raise DesignError(
                f"{where} contains the character U+{ord(ch):04X} (category {category}), "
                "which is not allowed in generated comment text")


def lookup(record, path):
    value = record
    for key in path:
        value = value[key]
    return value


def check_decimal(path, value):
    if not isinstance(value, str) or not DECIMAL.fullmatch(value):
        raise DesignError(
            f"design field {dotted(path)} must be a decimal string matching "
            f"-?[0-9]+(.[0-9]+)? with ASCII digits, got {value!r}")


def load_record(raw: bytes):
    """Parse and validate a design file. Returns the validated record."""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise DesignError(f"the design file is not UTF-8: {exc}") from None
    try:
        record = json.loads(text, object_pairs_hook=reject_duplicate_keys,
                            parse_constant=reject_constant)
    except json.JSONDecodeError as exc:
        raise DesignError(f"the design file is not valid JSON: {exc}") from None
    except RecursionError:
        raise DesignError("the design file is nested too deeply") from None

    check_keys("design record", record, TOP_KEYS)

    name = record["name"]
    if not isinstance(name, str) or not NAME.fullmatch(name):
        raise DesignError(
            "design field name must match [A-Za-z0-9][A-Za-z0-9._-]{0,63} "
            f"(ASCII letters, digits, '.', '_', '-'), got {name!r}")
    check_comment_text("design field status", record["status"], MAX_STATUS_LENGTH)

    check_keys("design field units", record["units"], tuple(UNITS), UNITS_OPTIONAL)
    for key, expected in UNITS.items():
        if record["units"][key] != expected:
            raise DesignError(
                f"design field units.{key} must be {expected!r} (the generated docstring "
                f"states these units), got {record['units'][key]!r}")
    for key in UNITS_OPTIONAL:
        if key in record["units"] and not isinstance(record["units"][key], str):
            raise DesignError(f"design field units.{key} must be a string")

    check_keys("design field box", record["box"], BOX_KEYS)
    for key in BOX_KEYS:
        pair = record["box"][key]
        if not isinstance(pair, list) or len(pair) != 2:
            raise DesignError(f"design field box.{key} must be a list [lower, upper] of two decimal strings")
    for block, keys in SCALAR_BLOCKS.items():
        check_keys(f"design field {block}", record[block], keys)

    for _, path in FIELDS:
        check_decimal(path, lookup(record, path))

    for lower, upper in ORDERED_PAIRS:
        lo, hi = lookup(record, lower), lookup(record, upper)
        if Fraction(lo) > Fraction(hi):
            raise DesignError(
                f"inverted bounds: {dotted(lower)} = {lo} is greater than {dotted(upper)} = {hi}")
    return record


def lean_literal(text):
    return f"({text})" if text.startswith("-") else text


def render(json_path: Path, def_name: str) -> str:
    if not LEAN_IDENT.fullmatch(def_name):
        raise DesignError(
            f"the definition name must be a plain ASCII Lean identifier, got {def_name!r}")
    shown_path = json_path.as_posix()
    try:
        raw = json_path.read_bytes()
    except OSError as exc:
        raise DesignError(f"cannot read the design file: {exc.strerror}") from None
    record = load_record(raw)
    check_comment_text("the JSON path (quoted in the generated header)", shown_path, 1000)
    digest = hashlib.sha256(raw).hexdigest()
    lines = [
        "/-",
        f"GENERATED by scripts/gen_design.py from {shown_path}",
        f"sha256 of the JSON file: {digest}",
        "Do not edit by hand; edit the JSON file and regenerate.",
        "-/",
        "import VoltageToBit.Model.Inverter",
        "",
        "namespace VoltageToBit.Examples",
        "",
        f"/-- Design record `{record['name']}`.",
        "",
        f"Status: {record['status']}",
        "",
        "Units: V, µA, fF, ns; transconductance in µA/V². -/",
        f"noncomputable def {def_name} : Design where",
    ]
    for field, path in FIELDS:
        lines.append(f"  {field} := {lean_literal(lookup(record, path))}")
    lines += ["", "end VoltageToBit.Examples", ""]
    return "\n".join(lines)


def main(argv):
    check = False
    if argv and argv[0] == "--check":
        check = True
        argv = argv[1:]
    if len(argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    json_path, lean_path, def_name = Path(argv[0]), Path(argv[1]), argv[2]
    try:
        text = render(json_path, def_name)
    except DesignError as exc:
        print(f"gen_design.py: REJECTED {json_path}: {exc}", file=sys.stderr)
        return 2
    if check:
        try:
            # newline="" so that a file with other line endings is reported stale
            with open(lean_path, encoding="utf-8", newline="") as handle:
                on_disk = handle.read()
        except (OSError, UnicodeDecodeError):
            on_disk = None
        if on_disk != text:
            print(f"STALE: {lean_path} does not match {json_path}")
            return 1
        print(f"ok: {lean_path} matches {json_path}")
        return 0
    with open(lean_path, "w", encoding="utf-8", newline="") as handle:
        handle.write(text)
    print(f"wrote {lean_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
