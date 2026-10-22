from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_verification_specs import compare, load_baseline, load_manifest, main, read_inventory  # noqa: E402


class VerificationSpecificationBaselineTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.source = self.root / "Spec.lean"
        self.source.write_text("def spec := True\n", encoding="utf-8")
        self.manifest = self.root / "manifest.json"
        self.manifest.write_text(json.dumps({
            "schema_version": 1,
            "declarations": [{
                "name": "LeanExperiments.Verification.Example.spec",
                "source": str(self.source),
                "purpose": "A synthetic specification for audit tests.",
            }],
        }), encoding="utf-8")
        self.inventory = self.root / "inventory.txt"
        self.baseline = self.root / "baseline.json"

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write_inventory(self, *, body: str = "Expr.const `True []", axioms: list[str] | None = None) -> None:
        record = {
            "name": "LeanExperiments.Verification.Example.spec",
            "kind": "def",
            "module": "LeanExperiments.Verification.Example",
            "type": "Prop",
            "body": body,
            "expr_hash_hint": "12345",
            "reducibility": "regular:1",
            "safety": "safe",
            "level_params": [],
            "axioms": axioms or ["propext", "Classical.choice"],
            "lean_version": "Lean 4.35.0",
        }
        self.inventory.write_text(
            "VERIFICATION_API|{}\n"
            "VERIFICATION_SPEC|" + json.dumps(record) + "\n",
            encoding="utf-8",
        )

    def test_same_type_with_changed_definition_body_requires_review(self) -> None:
        manifest = load_manifest(self.manifest)
        self.write_inventory(body="Expr.const `True []")
        baseline = read_inventory(self.inventory, manifest)
        self.write_inventory(body="Expr.const `False []")
        current = read_inventory(self.inventory, manifest)

        failures = compare(current, baseline)

        self.assertTrue(any("definition body changed" in failure for failure in failures))
        self.assertTrue(any("semantic equivalence is not established" in failure for failure in failures))

    def test_axiom_order_does_not_change_specification_inventory(self) -> None:
        manifest = load_manifest(self.manifest)
        self.write_inventory(axioms=["propext", "Classical.choice"])
        first = read_inventory(self.inventory, manifest)
        self.write_inventory(axioms=["Classical.choice", "propext"])
        second = read_inventory(self.inventory, manifest)

        self.assertEqual(compare(second, first), [])

    def test_new_transitive_axiom_dependency_requires_review(self) -> None:
        manifest = load_manifest(self.manifest)
        self.write_inventory(axioms=["propext", "Quot.sound"])
        baseline = read_inventory(self.inventory, manifest)
        self.write_inventory(axioms=["propext", "Quot.sound", "Classical.choice"])
        current = read_inventory(self.inventory, manifest)

        failures = compare(current, baseline)

        self.assertTrue(any("transitive axiom dependencies changed" in failure for failure in failures))

    def test_missing_critical_definition_fails_closed(self) -> None:
        self.inventory.write_text("VERIFICATION_API|{}\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "missing from Lean Environment"):
            read_inventory(self.inventory, load_manifest(self.manifest))

    def test_unregistered_specification_fails_closed(self) -> None:
        self.write_inventory()
        line = self.inventory.read_text(encoding="utf-8").replace(
            "LeanExperiments.Verification.Example.spec",
            "LeanExperiments.Verification.Example.unregistered",
        )
        self.inventory.write_text(line, encoding="utf-8")

        with self.assertRaisesRegex(ValueError, "unregistered critical specification"):
            read_inventory(self.inventory, load_manifest(self.manifest))

    def test_non_string_definition_body_fails_closed(self) -> None:
        self.write_inventory()
        lines = self.inventory.read_text(encoding="utf-8").splitlines()
        record = json.loads(lines[1].split("|", 1)[1])
        record["body"] = None
        lines[1] = "VERIFICATION_SPEC|" + json.dumps(record)
        self.inventory.write_text("\n".join(lines) + "\n", encoding="utf-8")

        with self.assertRaisesRegex(ValueError, "malformed specification metadata"):
            read_inventory(self.inventory, load_manifest(self.manifest))

    def test_malformed_body_fingerprint_in_baseline_fails_closed(self) -> None:
        self.write_inventory()
        current = read_inventory(self.inventory, load_manifest(self.manifest))
        current[next(iter(current))]["body_sha256"] = "not-a-sha256"
        self.baseline.write_text(json.dumps({
            "schema_version": 1,
            "review_reason": "synthetic malformed baseline",
            "declarations": current,
        }), encoding="utf-8")

        with self.assertRaisesRegex(ValueError, "invalid body fingerprint"):
            load_baseline(self.baseline)

    def test_baseline_creation_requires_review_reason(self) -> None:
        self.write_inventory()
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            main([
                "--manifest", str(self.manifest),
                "--baseline", str(self.baseline),
                str(self.inventory),
                "--write-initial-baseline",
            ])
        self.assertEqual(raised.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
