#!/usr/bin/env python3
"""Read an export written by `leanexport` (newline-delimited JSON) and say
what it contains, independently of the tools that check it.

Usage:
    python3 scripts/export_census.py EXPORT [--require NAMES | --report NAMES]

NAMES is the file `constants.jsonl` written by `scripts/Audit.lean`: one
declaration name per line, as a JSON array of its components.

Printed: the SHA-256 of the export, the number of declaration records of each
kind, the number of constants they declare, the axioms among them, and how
many of the names in NAMES the export declares. `scripts/check.sh` compares
the number of declarations that each checker reports with these numbers.

Exit status 1 if
* a line is not one of the record kinds this script knows (so a change of the
  format is noticed and not silently miscounted),
* the export declares an axiom other than propext, Classical.choice and
  Quot.sound,
* with `--require`, a name in NAMES is not declared by the export.

Why this exists: the external checkers are given the export, not the compiled
library. That every declaration of the library is in the export is therefore
a fact to be checked, not assumed. This script does not check any proof.
"""
import hashlib
import json
import sys

ALLOWED_AXIOMS = {("propext",), ("Classical", "choice"), ("Quot", "sound")}
DECLARATION_KINDS = {
    b'{"thm":': "theorem",
    b'{"def":': "definition",
    b'{"inductive":': "inductive block",
    b'{"axiom":': "axiom",
    b'{"quot":': "quotient primitive",
    b'{"opaque":': "opaque",
}
# expression, level and metadata records; nothing in them is needed here
OTHER_PREFIXES = (b'{"app":', b'{"bvar":', b'{"const":', b'{"forallE":', b'{"ie":', b'{"il":')


def show(name):
    return ".".join(str(component) for component in name)


def census(path):
    names = {0: ()}
    declared = {}           # name -> kind
    records = {}            # kind -> number of records
    axioms = []
    digest = hashlib.sha256()
    meta = None
    with open(path, "rb") as handle:
        for number, line in enumerate(handle, start=1):
            digest.update(line)
            if line.startswith(b'{"in":'):
                obj = json.loads(line)
                if "str" in obj:
                    names[obj["in"]] = names[obj["str"]["pre"]] + (obj["str"]["str"],)
                else:
                    names[obj["in"]] = names[obj["num"]["pre"]] + (obj["num"]["i"],)
                continue
            if line.startswith(OTHER_PREFIXES):
                continue
            for prefix, kind in DECLARATION_KINDS.items():
                if line.startswith(prefix):
                    break
            else:
                if line.startswith(b'{"meta":') and meta is None:
                    meta = json.loads(line)["meta"]
                    continue
                raise SystemExit(f"export_census.py: {path}: line {number} is not a known kind of "
                                 f"record: {line[:60]!r}")
            obj = json.loads(line)
            records[kind] = records.get(kind, 0) + 1
            if kind == "inductive block":
                body = obj["inductive"]
                for part, part_kind in (("types", "inductive type"), ("ctors", "constructor"),
                                        ("recs", "recursor")):
                    for item in body[part]:
                        declared[names[item["name"]]] = part_kind
            else:
                name = names[next(iter(obj.values()))["name"]]
                declared[name] = kind
                if kind == "axiom":
                    axioms.append(name)
    return meta, digest.hexdigest(), records, declared, axioms


def main(argv):
    if len(argv) not in (1, 3) or (len(argv) == 3 and argv[1] not in ("--require", "--report")):
        print(__doc__, file=sys.stderr)
        return 2
    meta, digest, records, declared, axioms = census(argv[0])
    status = 0
    if meta is None:
        print("no metadata record: this is not an export of leanexport")
        status = 1
    else:
        print(f"written by: {meta['exporter']['name']} {meta['exporter']['version']}, "
              f"format {meta['format']['version']}, Lean {meta['lean']['version']} "
              f"({meta['lean']['githash']})")
    print(f"sha256: {digest}")
    total = sum(records.values())
    detail = ", ".join(f"{kind}: {records[kind]}" for kind in sorted(records))
    print(f"declaration records: {total} ({detail})")
    # the checkers count in three ways; scripts/check.sh compares what each one
    # reports with the matching number here
    quotient = records.get("quotient primitive", 0)
    print(f"declaration records, the quotient records counted as one: {total - max(quotient - 1, 0)}")
    print(f"constants declared (an inductive block declares its types, constructors and "
          f"recursors): {len(declared)}")
    print("axioms declared: " + (", ".join(sorted(show(a) for a in axioms)) or "none"))
    for axiom in axioms:
        if axiom not in ALLOWED_AXIOMS:
            print(f"AXIOM NOT ALLOWED: {show(axiom)}")
            status = 1
    if len(argv) == 3:
        with open(argv[2], encoding="utf-8") as handle:
            wanted = [tuple(json.loads(line)) for line in handle if line.strip()]
        missing = [name for name in wanted if name not in declared]
        print(f"declarations of the library present in the export: "
              f"{len(wanted) - len(missing)} of {len(wanted)}")
        print(f"declarations from outside the library (Mathlib, its dependencies, Lean core): "
              f"{len(declared) - (len(wanted) - len(missing))}")
        if missing and argv[1] == "--require":
            for name in missing:
                print(f"MISSING FROM THE EXPORT: {show(name)}")
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
