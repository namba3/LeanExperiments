#!/usr/bin/env python3
"""Run `#print axioms` for private theorems before module export hides their names."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from verification_source_declarations import declared_namespaces, theorem_declarations


SOURCES = {
    Path("LeanExperiments/Verification/Factorial/Spec.lean"):
        "LeanExperiments.Verification.Factorial",
    Path("LeanExperiments/Verification/Fibonacci/Spec.lean"):
        "LeanExperiments.Verification.Fibonacci",
    Path("LeanExperiments/Verification/PrimeFactors/Spec.lean"):
        "LeanExperiments.Verification.PrimeFactors",
}


def private_theorems(source: Path, expected_namespace: str) -> list[str]:
    lines = source.read_text(encoding="utf-8").splitlines()
    if expected_namespace not in declared_namespaces(lines):
        raise ValueError(f"{source}: expected namespace {expected_namespace!r}")
    return [
        f"{namespace}.{name}"
        for namespace, name, is_private in theorem_declarations(lines)
        if is_private
    ]


def main() -> int:
    for source, namespace in SOURCES.items():
        targets = private_theorems(source, namespace)
        source_text = source.read_text(encoding="utf-8")
        audit_text = source_text + "\n" + "\n".join(
            f"#print axioms {target}" for target in targets
        ) + "\n"
        audit_file = Path(".lake") / f"verification-private-{namespace.rsplit('.', 1)[-1]}.lean"
        audit_file.write_text(audit_text, encoding="utf-8")
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(audit_file)],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
        finally:
            audit_file.unlink(missing_ok=True)
        sys.stdout.write(result.stdout)
        if result.returncode != 0:
            return result.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
