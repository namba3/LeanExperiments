#!/usr/bin/env python3
"""Compare Lean's public Verification API snapshot with a reviewed baseline."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


RECORD = re.compile(r"VERIFICATION_API\|(\{.*\})$")
FIELDS = {"name", "kind", "module", "type", "axioms"}


def read_inventory(path: Path) -> dict[str, dict[str, object]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise ValueError(f"cannot read API inventory {path}: {error}") from error
    records: dict[str, dict[str, object]] = {}
    for number, line in enumerate(lines, start=1):
        if "VERIFICATION_SPEC|" in line:
            continue
        if "VERIFICATION_API|" not in line:
            if line.strip() and "info:" not in line:
                raise ValueError(f"{path}:{number}: unexpected Lean output")
            continue
        match = RECORD.search(line)
        if not match:
            raise ValueError(f"{path}:{number}: malformed API record")
        try:
            record = json.loads(match.group(1))
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{number}: invalid API JSON: {error}") from error
        if not isinstance(record, dict) or set(record) != FIELDS:
            raise ValueError(f"{path}:{number}: unexpected API record fields")
        name = record["name"]
        if not isinstance(name, str) or not name.startswith("LeanExperiments.Verification."):
            raise ValueError(f"{path}:{number}: invalid declaration name")
        if name in records:
            raise ValueError(f"{path}:{number}: duplicate declaration {name}")
        if not isinstance(record["kind"], str) or not isinstance(record["module"], str) \
                or record["module"] == "unknown" or not isinstance(record["type"], str):
            raise ValueError(f"{path}:{number}: kind, module, and type must be known strings")
        axioms = record["axioms"]
        if not isinstance(axioms, list) or not all(isinstance(item, str) for item in axioms):
            raise ValueError(f"{path}:{number}: axioms must be a string array")
        if len(set(axioms)) != len(axioms):
            raise ValueError(f"{path}:{number}: duplicate axiom dependency")
        records[name] = record
    if not records:
        raise ValueError(f"{path}: API inventory is empty")
    return records


def load_baseline(path: Path) -> dict[str, dict[str, object]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read API baseline {path}: {error}") from error
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("API baseline must have schema_version 1")
    if not isinstance(data.get("review_reason"), str) or not data["review_reason"].strip():
        raise ValueError("API baseline must record a non-empty review_reason")
    records = data.get("declarations")
    if not isinstance(records, dict) or not records:
        raise ValueError("API baseline declarations must be a non-empty object")
    for name, record in records.items():
        if not isinstance(record, dict) or set(record) != FIELDS or record.get("name") != name:
            raise ValueError(f"invalid API baseline record for {name}")
        if not all(isinstance(record[field], str) for field in ("kind", "module", "type")):
            raise ValueError(f"invalid API baseline strings for {name}")
        if not isinstance(record["axioms"], list) or not all(
            isinstance(axiom, str) for axiom in record["axioms"]
        ):
            raise ValueError(f"invalid API baseline axioms for {name}")
    return records


def compare(current: dict[str, dict[str, object]], baseline: dict[str, dict[str, object]]) -> list[str]:
    errors: list[str] = []
    for name in sorted(baseline.keys() - current.keys()):
        errors.append(f"public proposition declaration removed: {name}")
    for name in sorted(current.keys() - baseline.keys()):
        errors.append(f"new public proposition declaration requires review: {name}")
    for name in sorted(current.keys() & baseline.keys()):
        before, after = baseline[name], current[name]
        for field in sorted(FIELDS - {"name"}):
            if before[field] != after[field]:
                errors.append(f"{name}: reviewed API field changed ({field})")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("inventory", type=Path)
    update = parser.add_mutually_exclusive_group()
    update.add_argument("--write-initial-baseline", action="store_true")
    update.add_argument("--replace-reviewed-baseline", action="store_true")
    parser.add_argument("--review-reason", help="required justification for explicit baseline creation")
    options = parser.parse_args(argv)
    writing = options.write_initial_baseline or options.replace_reviewed_baseline
    if writing and not options.review_reason:
        parser.error("baseline writes require --review-reason")
    if writing:
        if options.write_initial_baseline and options.baseline.exists():
            parser.error("refusing to overwrite an existing API baseline")
        if options.replace_reviewed_baseline and not options.baseline.exists():
            parser.error("cannot replace a missing API baseline")
        try:
            current = read_inventory(options.inventory)
            previous_count = len(load_baseline(options.baseline)) if options.replace_reviewed_baseline else 0
            options.baseline.write_text(
                json.dumps({"schema_version": 1, "review_reason": options.review_reason,
                            "declarations": current}, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
        except (OSError, ValueError) as error:
            parser.error(str(error))
        action = "Replaced reviewed" if options.replace_reviewed_baseline else "Created initial reviewed"
        print(f"{action} API baseline with {len(current)} declarations (previously {previous_count})")
        return 0
    try:
        current = read_inventory(options.inventory)
        baseline = load_baseline(options.baseline)
    except ValueError as error:
        parser.error(str(error))
    errors = compare(current, baseline)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Public Verification API matches reviewed baseline ({len(current)} declarations).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
