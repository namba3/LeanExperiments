#!/usr/bin/env python3
"""Review structural changes to curated mathematical specifications."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


RECORD = re.compile(r"VERIFICATION_SPEC\|(\{.*\})$")
RECORD_FIELDS = {
    "name", "kind", "module", "type", "body", "expr_hash_hint",
    "reducibility", "safety", "level_params", "axioms", "lean_version",
}
BASELINE_FIELDS = (RECORD_FIELDS - {"body"}) | {"body_sha256", "source", "purpose"}


def load_manifest(path: Path) -> dict[str, dict[str, str]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read specification manifest {path}: {error}") from error
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("specification manifest must have schema_version 1")
    declarations = data.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        raise ValueError("specification manifest declarations must be a non-empty array")
    result: dict[str, dict[str, str]] = {}
    for index, entry in enumerate(declarations, start=1):
        if not isinstance(entry, dict) or set(entry) != {"name", "source", "purpose"}:
            raise ValueError(f"manifest declaration {index} must have name, source, and purpose")
        if not all(isinstance(entry[key], str) and entry[key].strip()
                   for key in ("name", "source", "purpose")):
            raise ValueError(f"manifest declaration {index} has an empty or invalid field")
        if not entry["name"].startswith("LeanExperiments.Verification."):
            raise ValueError(f"manifest declaration {index} is outside Verification")
        if entry["name"] in result:
            raise ValueError(f"duplicate specification manifest entry {entry['name']}")
        if not Path(entry["source"]).is_file():
            raise ValueError(f"specification source is missing: {entry['source']}")
        result[entry["name"]] = {"source": entry["source"], "purpose": entry["purpose"]}
    return result


def read_inventory(path: Path, manifest: dict[str, dict[str, str]]) -> dict[str, dict[str, object]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise ValueError(f"cannot read Lean inventory {path}: {error}") from error
    records: dict[str, dict[str, object]] = {}
    for number, line in enumerate(lines, start=1):
        if "VERIFICATION_SPEC|" not in line:
            if line.strip() and "info:" not in line and "VERIFICATION_API|" not in line:
                raise ValueError(f"{path}:{number}: unexpected Lean inventory output")
            continue
        match = RECORD.search(line)
        if not match:
            raise ValueError(f"{path}:{number}: malformed specification record")
        try:
            record = json.loads(match.group(1))
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{number}: invalid specification JSON: {error}") from error
        if not isinstance(record, dict) or set(record) != RECORD_FIELDS:
            raise ValueError(f"{path}:{number}: unexpected specification record fields")
        name = record["name"]
        if not isinstance(name, str) or name not in manifest:
            raise ValueError(f"{path}:{number}: unregistered critical specification {name!r}")
        if name in records:
            raise ValueError(f"{path}:{number}: duplicate specification {name}")
        if record["kind"] != "def" or not all(
            isinstance(record[field], str) and record[field]
            for field in ("module", "type", "body", "expr_hash_hint", "reducibility", "safety", "lean_version")
        ):
            raise ValueError(f"{path}:{number}: malformed specification metadata for {name}")
        if not isinstance(record["level_params"], list) or not all(
            isinstance(item, str) for item in record["level_params"]
        ):
            raise ValueError(f"{path}:{number}: invalid universe parameter list for {name}")
        if not isinstance(record["axioms"], list) or not all(
            isinstance(item, str) and item for item in record["axioms"]
        ):
            raise ValueError(f"{path}:{number}: invalid axiom dependencies for {name}")

        # Axioms form a set. Sorting also prevents output-order-only baseline churn.
        normalized = {key: value for key, value in record.items() if key != "body"}
        normalized["axioms"] = sorted(set(record["axioms"]))
        normalized["level_params"] = list(record["level_params"])
        normalized["body_sha256"] = hashlib.sha256(record["body"].encode("utf-8")).hexdigest()
        normalized.update(manifest[name])
        records[name] = normalized

    missing = manifest.keys() - records.keys()
    if missing:
        raise ValueError("critical specifications missing from Lean Environment: " + ", ".join(sorted(missing)))
    if not records:
        raise ValueError(f"{path}: no critical specification records found")
    return records


def load_baseline(path: Path) -> tuple[str, dict[str, dict[str, object]]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read specification baseline {path}: {error}") from error
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("specification baseline must have schema_version 1")
    reason = data.get("review_reason")
    if not isinstance(reason, str) or not reason.strip():
        raise ValueError("specification baseline must record a non-empty review_reason")
    records = data.get("declarations")
    if not isinstance(records, dict) or not records:
        raise ValueError("specification baseline declarations must be a non-empty object")
    for name, record in records.items():
        if not isinstance(record, dict) or set(record) != BASELINE_FIELDS or record.get("name") != name:
            raise ValueError(f"invalid specification baseline record for {name}")
        text_fields = BASELINE_FIELDS - {"level_params", "axioms"}
        if not all(isinstance(record.get(field), str) and record[field]
                   for field in text_fields):
            raise ValueError(f"invalid text metadata in baseline for {name}")
        if record.get("kind") != "def":
            raise ValueError(f"invalid declaration kind in baseline for {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", record["body_sha256"]):
            raise ValueError(f"invalid body fingerprint in baseline for {name}")
        for field in ("level_params", "axioms"):
            values = record.get(field)
            if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
                raise ValueError(f"invalid {field} in baseline for {name}")
        if record["axioms"] != sorted(set(record["axioms"])):
            raise ValueError(f"axiom dependencies are not normalized in baseline for {name}")
    return reason, records


def compare(current: dict[str, dict[str, object]], baseline: dict[str, dict[str, object]]) -> list[str]:
    errors: list[str] = []
    for name in sorted(baseline.keys() - current.keys()):
        errors.append(f"critical specification removed: {name}")
    for name in sorted(current.keys() - baseline.keys()):
        errors.append(f"new critical specification requires review: {name}")
    for name in sorted(current.keys() & baseline.keys()):
        before, after = baseline[name], current[name]
        fields = sorted((set(before) | set(after)) - {"name"})
        for field in fields:
            if before.get(field) == after.get(field):
                continue
            if field == "body_sha256":
                errors.append(
                    f"{name}: elaborated definition body changed; structural fingerprint differs, "
                    "semantic equivalence is not established"
                )
            elif field == "expr_hash_hint":
                errors.append(f"{name}: Lean Expr hash hint changed ({field})")
            elif field == "axioms":
                errors.append(f"{name}: transitive axiom dependencies changed")
            elif field == "type":
                errors.append(f"{name}: declaration type changed")
            elif field == "module":
                errors.append(f"{name}: owning module changed")
            elif field in {"reducibility", "safety", "level_params", "kind"}:
                errors.append(f"{name}: declaration metadata changed ({field})")
            elif field == "lean_version":
                errors.append(f"{name}: Lean toolchain version changed")
            elif field in {"source", "purpose"}:
                errors.append(f"{name}: specification manifest metadata changed ({field})")
            else:
                errors.append(f"{name}: specification baseline field changed ({field})")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
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
    try:
        manifest = load_manifest(options.manifest)
        current = read_inventory(options.inventory, manifest)
        if writing:
            if options.write_initial_baseline and options.baseline.exists():
                parser.error("refusing to overwrite an existing specification baseline")
            if options.replace_reviewed_baseline and not options.baseline.exists():
                parser.error("cannot replace a missing specification baseline")
            previous = load_baseline(options.baseline)[1] if options.replace_reviewed_baseline else {}
            options.baseline.write_text(json.dumps({
                "schema_version": 1,
                "review_reason": options.review_reason,
                "declarations": current,
            }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            action = "Replaced reviewed" if options.replace_reviewed_baseline else "Created initial reviewed"
            print(f"{action} specification baseline with {len(current)} declarations (previously {len(previous)}).")
            return 0
        _, baseline = load_baseline(options.baseline)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    errors = compare(current, baseline)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Critical specification fingerprints match reviewed baseline ({len(current)} declarations).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
