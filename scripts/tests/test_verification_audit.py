from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_lean_sources import check_sources  # noqa: E402
from check_verification_axioms import main as check_axioms_main  # noqa: E402
from check_verification_axioms import parse_report  # noqa: E402
from audit_private_module_axioms import private_theorems  # noqa: E402
from verification_source_declarations import (  # noqa: E402
    ad_hoc_axiom_declarations,
    theorem_declarations,
)


class SourceDeclarationScannerTests(unittest.TestCase):
    def test_tracks_nested_namespaces_sections_and_qualified_ends(self) -> None:
        declarations = list(
            theorem_declarations(
                [
                    "namespace Outer",
                    "section Local",
                    "namespace Inner.Deep",
                    "@[simp] private lemma hidden : True := by trivial",
                    "end Inner.Deep",
                    "theorem visible : True := by trivial",
                    "end Local",
                    "lemma outerLemma : True := by trivial",
                    "end Outer",
                ]
            )
        )
        self.assertEqual(
            declarations,
            [
                ("Outer.Inner.Deep", "hidden", True),
                ("Outer", "visible", False),
                ("Outer", "outerLemma", False),
            ],
        )

    def test_handles_multiline_nested_attributes_and_modifiers(self) -> None:
        declarations = list(
            theorem_declarations(
                [
                    "namespace Example",
                    "@[simp, aesop safe [apply]]",
                    "private",
                    "lemma nested_attribute : True := by trivial",
                    "end Example",
                ]
            )
        )
        self.assertEqual(declarations, [("Example", "nested_attribute", True)])

    def test_ignores_comments_and_strings(self) -> None:
        declarations = list(
            theorem_declarations(
                [
                    '"namespace Fake"',
                    "namespace Actual -- namespace InComment",
                    "/- theorem commented : False := by sorry -/",
                    "theorem real : True := by trivial -- lemma phantom : False := by sorry",
                    "end Actual",
                ]
            )
        )
        self.assertEqual(declarations, [("Actual", "real", False)])

    def test_fails_closed_on_unbalanced_scopes_and_attributes(self) -> None:
        for source in (
            ["namespace Open", "theorem one : True := by trivial"],
            ["end Missing"],
            ["namespace Open", "@[simp"],
            ["namespace Open", "open Foo; theorem one : True := by trivial", "end Open"],
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                list(theorem_declarations(source))

    def test_fails_closed_when_a_line_hides_a_second_theorem(self) -> None:
        with self.assertRaisesRegex(ValueError, "multiple theorem/lemma"):
            list(
                theorem_declarations(
                    [
                        "private",
                        "theorem visible : True := by trivial; lemma hidden : False := by sorry",
                    ]
                )
            )

    def test_private_audit_discovers_private_lemmas(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text(
                "namespace Example\n"
                "private lemma hidden : True := by trivial\n"
                "theorem public : True := by trivial\n"
                "end Example\n",
                encoding="utf-8",
            )
            self.assertEqual(private_theorems(source, "Example"), ["Example.hidden"])


class SourceTrustScannerTests(unittest.TestCase):
    def test_ad_hoc_axiom_scanner_rejects_unrecognized_and_chained_headers(self) -> None:
        with self.assertRaisesRegex(ValueError, "multiple axiom/constant"):
            list(
                ad_hoc_axiom_declarations(
                    ["private", "axiom first : True; constant hidden : False"]
                )
            )
        with self.assertRaisesRegex(ValueError, "not at a recognized declaration header"):
            list(ad_hoc_axiom_declarations(["open Foo; axiom hidden : False"]))

    def test_proof_holes_in_comments_are_not_source_holes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text(
                "-- sorry and axiom are documentation here\n"
                'def message := "admit"\n'
                "theorem valid : True := by trivial\n",
                encoding="utf-8",
            )
            self.assertTrue(check_sources([source], reject_sorry_ax_only=False))

    def test_actual_proof_holes_and_axioms_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text(
                "namespace Example\n"
                "@[simp, local_attr [enabled]]\n"
                "private\n"
                "axiom trusted : False\n"
                "theorem incomplete : True := by sorry\n"
                "end Example\n",
                encoding="utf-8",
            )
            with (
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                self.assertFalse(check_sources([source], reject_sorry_ax_only=False))


class KernelAuditReportTests(unittest.TestCase):
    def test_parses_axiom_free_and_multiline_axiom_records(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "audit.txt"
            report.write_text(
                "'Example.first' does not depend on any axioms\n"
                "'Example.second' depends on axioms: [propext,\n"
                " Classical.choice]\n",
                encoding="utf-8",
            )
            self.assertEqual(
                parse_report(report),
                [
                    ("Example.first", set()),
                    ("Example.second", {"propext", "Classical.choice"}),
                ],
            )

    def test_rejects_empty_or_unparseable_audit_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "audit.txt"
            for content in ("", "warning: partial output\n"):
                report.write_text(content, encoding="utf-8")
                with self.subTest(content=content), self.assertRaises(ValueError):
                    parse_report(report)

    def test_manifest_and_audit_must_match_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / "manifest.json"
            report = root / "audit.txt"
            summary = root / "summary.md"
            manifest.write_text(json.dumps({"general": ["Example.expected"]}), encoding="utf-8")

            report.write_text(
                "'Example.expected' does not depend on any axioms\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    check_axioms_main(
                        [
                            "--manifest",
                            str(manifest),
                            "--audit",
                            "general",
                            str(report),
                            "--github-summary",
                            str(summary),
                        ]
                    ),
                    0,
                )
            self.assertIn("General (A)", summary.read_text(encoding="utf-8"))

            report.write_text(
                "'Example.unregistered' does not depend on any axioms\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(
                    check_axioms_main(
                        ["--manifest", str(manifest), "--audit", "general", str(report)]
                    ),
                    1,
                )

            report.write_text(
                "'Example.expected' does not depend on any axioms\n"
                "'Example.expected' does not depend on any axioms\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(
                    check_axioms_main(
                        ["--manifest", str(manifest), "--audit", "general", str(report)]
                    ),
                    1,
                )

    def test_duplicate_manifest_targets_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / "manifest.json"
            report = root / "audit.txt"
            manifest.write_text(
                json.dumps({"general": ["Example.one", "Example.one"]}),
                encoding="utf-8",
            )
            report.write_text(
                "'Example.one' does not depend on any axioms\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                check_axioms_main(
                    ["--manifest", str(manifest), "--audit", "general", str(report)]
                )


if __name__ == "__main__":
    unittest.main()
