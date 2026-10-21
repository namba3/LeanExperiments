from __future__ import annotations

import json
import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_verification_api import compare, main as check_api_main, read_inventory  # noqa: E402
from check_verification_coverage import audit  # noqa: E402


class VerificationApiBaselineTests(unittest.TestCase):
    def test_detects_removed_declarations_type_changes_and_new_axioms(self) -> None:
        old = {
            "Example.result": {
                "name": "Example.result", "kind": "theorem", "module": "Example", "type": "True", "axioms": ["propext"]
            },
            "Example.removed": {
                "name": "Example.removed", "kind": "theorem", "module": "Example", "type": "True", "axioms": ["propext"]
            }
        }
        new = {
            "Example.result": {
                "name": "Example.result", "kind": "theorem", "module": "Example.New", "type": "False", "axioms": ["sorryAx"]
            },
            "Example.added": {
                "name": "Example.added", "kind": "theorem", "module": "Example", "type": "True", "axioms": []
            },
        }
        failures = compare(new, old)
        self.assertTrue(any("type" in failure for failure in failures))
        self.assertTrue(any("module" in failure for failure in failures))
        self.assertTrue(any("axioms" in failure for failure in failures))
        self.assertTrue(any("new public proposition" in failure for failure in failures))
        self.assertTrue(any("removed" in failure for failure in failures))

    def test_api_inventory_rejects_empty_duplicate_and_malformed_records(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "inventory.txt"
            path.write_text("", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "empty"):
                read_inventory(path)
            record = json.dumps({
                "name": "LeanExperiments.Verification.Example.result",
                "kind": "theorem", "module": "Example", "type": "True", "axioms": []
            })
            path.write_text(f"VERIFICATION_API|{record}\nVERIFICATION_API|{record}\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate"):
                read_inventory(path)

    def test_baseline_overwrite_requires_explicit_review_reason(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = root / "baseline.json"
            inventory = root / "inventory.txt"
            baseline.write_text('{"schema_version":1,"declarations":{"X":{"name":"X"}}}', encoding="utf-8")
            inventory.write_text(
                'VERIFICATION_API|{"name":"LeanExperiments.Verification.Example","kind":"theorem","module":"LeanExperiments.Verification.Example","type":"True","axioms":[]}\n',
                encoding="utf-8",
            )
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                check_api_main(["--baseline", str(baseline), str(inventory),
                                "--replace-reviewed-baseline"])
            self.assertEqual(raised.exception.code, 2)


class VerificationCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.old_cwd = Path.cwd()
        self.root = Path(self.temp.name)
        os.chdir(self.root)
        self.verification = self.root / "LeanExperiments/Verification"
        self.verification.mkdir(parents=True)
        self.source = self.verification / "Example.lean"
        self.source.write_text(
            "namespace LeanExperiments.Verification.Example\n"
            "theorem result : True := by trivial\n"
            "private theorem helper : True := by trivial\n"
            "end LeanExperiments.Verification.Example\n",
            encoding="utf-8",
        )
        (self.root / "LeanExperiments/Verification.lean").write_text(
            "import LeanExperiments.Verification.Example\n", encoding="utf-8"
        )
        self.olean = self.root / ".lake/build/lib/lean/LeanExperiments/Verification"
        self.olean.mkdir(parents=True)
        (self.olean / "Example.olean").touch()
        self.sources = self.root / "sources.json"
        self.sources.write_text(json.dumps({
            "version": 1,
            "sources": [{"path": "LeanExperiments/Verification/Example.lean",
                         "namespace": "LeanExperiments.Verification.Example"}],
        }), encoding="utf-8")
        self.axioms = self.root / "axioms.json"
        self.axioms.write_text(json.dumps({
            "general": ["LeanExperiments.Verification.Example.result"],
            "finite_finite": [],
            "general_private": ["LeanExperiments.Verification.Example.helper"],
        }), encoding="utf-8")

    def tearDown(self) -> None:
        os.chdir(self.old_cwd)
        self.temp.cleanup()

    def check(self) -> list[str]:
        return audit(self.sources, self.axioms, "LeanExperiments.Verification",
                     Path("LeanExperiments/Verification"), Path(".lake/build/lib/lean"))

    def test_reachable_built_sources_and_explicit_scope_registration_pass(self) -> None:
        self.assertEqual(self.check(), [])

    def test_unimported_source_fails_even_when_registered_and_built(self) -> None:
        (self.root / "LeanExperiments/Verification.lean").write_text("", encoding="utf-8")
        self.assertTrue(any("not reachable" in error for error in self.check()))

    def test_missing_olean_fails(self) -> None:
        (self.olean / "Example.olean").unlink()
        self.assertTrue(any("no built olean" in error for error in self.check()))

    def test_unregistered_source_file_fails(self) -> None:
        (self.verification / "Untracked.lean").write_text("namespace X\nend X\n", encoding="utf-8")
        self.assertTrue(any("source missing from manifest" in error for error in self.check()))

    def test_unclassified_theorem_fails(self) -> None:
        self.axioms.write_text(json.dumps({"general": [], "finite_finite": [],
                                            "general_private": ["LeanExperiments.Verification.Example.helper"]}),
                               encoding="utf-8")
        self.assertTrue(any("unclassified source theorems" in error for error in self.check()))


if __name__ == "__main__":
    unittest.main()
