#!/usr/bin/env python3
"""Require review when private proposition-valued definitions change."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


RECORD = re.compile(r"VERIFICATION_PRIVATE_PROP_DEF\|([^\s|]+)$")
AXIOMS = re.compile(r"VERIFICATION_PRIVATE_PROP_AXIOMS\|([^\s|]+)\|(.*)$")
ALLOWED_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}


def parse_inventory(path: Path) -> set[str]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise ValueError(f"cannot read private proposition inventory {path}: {error}") from error
    declarations: set[str] = set()
    for number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        if AXIOMS.search(line):
            continue
        match = RECORD.search(line)
        if not match:
            raise ValueError(f"{path}:{number}: unrecognized private proposition inventory output")
        declaration = match.group(1)
        if declaration in declarations:
            raise ValueError(f"{path}:{number}: duplicate private proposition declaration {declaration}")
        declarations.add(declaration)
    return declarations


def parse_axiom_records(path: Path) -> dict[str, set[str]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise ValueError(f"cannot read private proposition axiom report {path}: {error}") from error
    records: dict[str, set[str]] = {}
    for number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        match = AXIOMS.search(line)
        if not match:
            if RECORD.search(line):
                continue
            raise ValueError(f"{path}:{number}: unrecognized private proposition axiom output")
        declaration = match.group(1)
        if declaration in records:
            raise ValueError(f"{path}:{number}: duplicate private proposition axiom record {declaration}")
        payload = match.group(2)
        records[declaration] = {axiom for axiom in payload.split(",") if axiom}
    return records


def main(arguments: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("inventory", type=Path)
    options = parser.parse_args(arguments)
    try:
        baseline_data = json.loads(options.baseline.read_text(encoding="utf-8"))
        if not isinstance(baseline_data, list) or not all(
            isinstance(name, str) and name.strip() for name in baseline_data
        ):
            raise ValueError(f"{options.baseline}: baseline must be a list of declaration names")
        if len(set(baseline_data)) != len(baseline_data):
            raise ValueError(f"{options.baseline}: duplicate baseline declaration")
        expected = set(baseline_data)
        actual = parse_inventory(options.inventory)
        axiom_records = parse_axiom_records(options.inventory)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        parser.error(str(error))

    added = actual - expected
    removed = expected - actual
    if added or removed:
        if added:
            print("private proposition definitions need explicit review: " + ", ".join(sorted(added)), file=sys.stderr)
        if removed:
            print("stale private proposition baseline entries: " + ", ".join(sorted(removed)), file=sys.stderr)
        print(
            "For new source declarations, add an explicit kernel-axiom audit before updating the baseline.",
            file=sys.stderr,
        )
        return 1
    if set(axiom_records) != actual:
        print("private proposition axiom records do not match the inventory", file=sys.stderr)
        return 1
    unexpected = {
        (declaration, axiom)
        for declaration, axioms in axiom_records.items()
        for axiom in axioms - ALLOWED_AXIOMS
    }
    if unexpected:
        details = ", ".join(f"{declaration}: {axiom}" for declaration, axiom in sorted(unexpected))
        print("private proposition definitions use unapproved axioms: " + details, file=sys.stderr)
        return 1
    print(f"Private proposition-definition inventory matches its {len(expected)} reviewed helper entries.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
