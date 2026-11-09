"""Experiment-record format (JSON Lines), canonical hashing, I/O.

One record is one proposal taken through the loop
``propose -> screen -> formal check -> evaluate -> decide``.
The format is documented field by field in ``docs/experiment-loop.md``.

Determinism
-----------
Everything in a record is a function of the frozen context and the fixed
seeds, except the ``timestamps`` object. ``content_sha256`` is the SHA-256 of
the canonical JSON of the record without ``timestamps`` and without
``content_sha256`` itself, so two runs can be compared field by field or by
that one hash.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

SCHEMA = "v2b.experiment-record/1"

DECISIONS = ("accepted", "rejected", "counterexample")

# Order of the top-level keys of a record (for readable lines).
KEYS = ["schema", "record_id", "experiment_id", "generation", "parent_id", "baseline_id",
        "context_sha256", "context", "proposer", "proposal", "screen", "formal_checks",
        "numerical_evidence", "objective_value", "decision", "reason_code", "reason",
        "rejected_by", "control", "screen_agrees_with_lean", "timestamps", "content_sha256"]

VOLATILE = ("timestamps", "content_sha256")


def canonical(obj) -> str:
    """Canonical JSON: sorted keys, no insignificant whitespace, UTF-8."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def content_hash(record: dict) -> str:
    return sha256_text(canonical({k: v for k, v in record.items() if k not in VOLATILE}))


def finish(record: dict) -> dict:
    """Validate, order the keys and attach the content hash."""
    missing = [k for k in KEYS if k not in record and k != "content_sha256"]
    extra = [k for k in record if k not in KEYS]
    if missing or extra:
        raise ValueError(f"record {record.get('record_id')}: missing {missing}, unexpected {extra}")
    if record["decision"] not in DECISIONS:
        raise ValueError(f"record {record['record_id']}: decision {record['decision']!r}")
    if record["schema"] != SCHEMA:
        raise ValueError("wrong schema tag")
    ordered = {k: record[k] for k in KEYS if k != "content_sha256"}
    ordered["content_sha256"] = content_hash(ordered)
    return ordered


def write_jsonl(path: Path, records: list[dict]) -> str:
    """Write records, one JSON object per line. Returns the file's SHA-256."""
    text = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in records)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return sha256_text(text)


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in Path(path).read_text(encoding="utf-8").splitlines() if line]


def verify(records: list[dict]) -> list[str]:
    """Internal consistency of a record file. Returns a list of problems."""
    problems = []
    seen = {}
    for r in records:
        rid = r.get("record_id")
        if rid in seen:
            problems.append(f"duplicate record id {rid}")
        seen[rid] = r
        if content_hash(r) != r.get("content_sha256"):
            problems.append(f"{rid}: content hash does not match")
        if r.get("context_sha256") != sha256_text(canonical(r.get("context"))):
            problems.append(f"{rid}: context hash does not match")
    for r in records:
        rid = r["record_id"]
        for key in ("parent_id", "baseline_id"):
            ref = r.get(key)
            if ref is not None and ref not in seen:
                problems.append(f"{rid}: {key} {ref} not in file")
            elif ref is not None and seen[ref]["context_sha256"] != r["context_sha256"]:
                problems.append(f"{rid}: {key} {ref} has a different frozen context")
        if r["decision"] == "accepted":
            claim = [c for c in r["formal_checks"] if c["role"] == "claim"]
            if not claim or not claim[0]["passed"]:
                problems.append(f"{rid}: accepted without a passed formal check")
    return problems
