#!/usr/bin/env python3
"""Fail closed when a Verification source is unbuilt, unreachable, or unclassified."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from verification_source_declarations import declared_namespaces, theorem_declarations


IMPORT = re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*(?:--.*)?$")


def imports(path: Path) -> list[str]:
    found: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if match:
            found.extend(match.group(1).split())
    return found


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def reachable_modules(root_module: str) -> set[str]:
    seen: set[str] = set()
    pending = [root_module]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = module_path(module)
        if not source.is_file():
            continue
        pending.extend(name for name in imports(source) if name.startswith("LeanExperiments."))
    return seen


def audit(source_manifest: Path, axiom_manifest: Path, root_module: str,
          verification_root: Path, olean_root: Path) -> list[str]:
    errors: list[str] = []
    try:
        source_data = json.loads(source_manifest.read_text(encoding="utf-8"))
        axiom_data = json.loads(axiom_manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return [f"cannot read audit manifests: {error}"]
    if not isinstance(source_data, dict) or not isinstance(axiom_data, dict):
        return ["audit manifests must be JSON objects"]
    entries = source_data.get("sources") if source_data.get("version") == 1 else None
    if not isinstance(entries, list):
        return ["source manifest must have version 1 and a sources array"]
    for group, names in axiom_data.items():
        if not isinstance(group, str) or not isinstance(names, list) \
                or not all(isinstance(name, str) and name.strip() for name in names):
            return [f"axiom manifest group {group!r} must contain theorem-name strings"]
        if len(set(names)) != len(names):
            return [f"axiom manifest group {group!r} contains duplicate theorem names"]

    source_paths: set[Path] = set()
    public_found: set[str] = set()
    private_found: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"path", "namespace"}:
            errors.append("each source entry must contain exactly path and namespace")
            continue
        if not isinstance(entry["path"], str) or not entry["path"]:
            errors.append("source paths must be non-empty strings")
            continue
        path = Path(entry["path"])
        namespace = entry["namespace"]
        resolved = path.resolve()
        if resolved in source_paths:
            errors.append(f"duplicate source registration: {path}")
            continue
        source_paths.add(resolved)
        if not path.is_file():
            errors.append(f"registered source is missing: {path}")
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
            if namespace not in declared_namespaces(lines):
                errors.append(f"{path}: expected namespace {namespace!r}")
            for declared_namespace, name, is_private in theorem_declarations(lines):
                full_name = f"{declared_namespace}.{name}"
                (private_found if is_private else public_found).add(full_name)
        except (OSError, ValueError) as error:
            errors.append(f"{path}: cannot scan declarations safely: {error}")

    tree_paths = {path.resolve() for path in verification_root.rglob("*.lean")}
    if source_paths != tree_paths:
        errors.extend(f"source missing from manifest: {path}" for path in sorted(tree_paths - source_paths))
        errors.extend(f"stale manifest source: {path}" for path in sorted(source_paths - tree_paths))

    reachable = reachable_modules(root_module)
    for path in sorted(tree_paths):
        module = ".".join(path.relative_to(Path.cwd()).with_suffix("").parts)
        if module not in reachable:
            errors.append(f"Verification source is not reachable from {root_module}: {path}")
        olean = olean_root / Path(*module.split(".")).with_suffix(".olean")
        if not olean.is_file():
            errors.append(f"Verification source has no built olean: {olean}")

    finite_groups = {name for name in axiom_data if name.endswith("_finite")}
    general_groups = {
        name for name in axiom_data
        if not name.endswith("_finite") and not name.endswith("_private")
        and name != "environment_generated"
    }
    private_groups = {name for name in axiom_data if name.endswith("_private")}
    finite = set().union(*(set(axiom_data[name]) for name in finite_groups))
    general = set().union(*(set(axiom_data[name]) for name in general_groups))
    private = set().union(*(set(axiom_data[name]) for name in private_groups))
    if public_found - finite - general:
        errors.append("unclassified source theorems: " + ", ".join(sorted(public_found - finite - general)))
    if public_found & finite & general:
        errors.append("theorems classified as both general and finite: " + ", ".join(sorted(public_found & finite & general)))
    if (finite | general) - public_found:
        errors.append("stale public theorem registrations: " + ", ".join(sorted((finite | general) - public_found)))
    if private_found != private:
        if private_found - private:
            errors.append("unregistered private theorems: " + ", ".join(sorted(private_found - private)))
        if private - private_found:
            errors.append("stale private theorem registrations: " + ", ".join(sorted(private - private_found)))
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--axioms", type=Path, required=True)
    parser.add_argument("--root-module", default="LeanExperiments.Verification")
    parser.add_argument("--verification-root", type=Path, default=Path("LeanExperiments/Verification"))
    parser.add_argument("--olean-root", type=Path, default=Path(".lake/build/lib/lean"))
    options = parser.parse_args(argv)
    errors = audit(options.sources, options.axioms, options.root_module,
                   options.verification_root, options.olean_root)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Verification coverage passed: {len(list(options.verification_root.rglob('*.lean')))} source files built and reachable; theorem scope and private theorem registrations match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
