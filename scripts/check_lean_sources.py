#!/usr/bin/env python3
"""Check Lean source files and theorem-audit output without external tools."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

from verification_source_declarations import (
    ad_hoc_axiom_declarations,
    strip_comments_and_strings,
)


PROOF_HOLE = re.compile(r"\b(sorry|admit|sorryAx)\b")


def tracked_lean_sources() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return [Path(path.decode()) for path in result.stdout.split(b"\0") if path]


def check_sources(paths: list[Path], *, reject_sorry_ax_only: bool) -> bool:
    failed = False
    for path in paths:
        try:
            source = path.read_text(encoding="utf-8")
            lines = (
                source.splitlines()
                if reject_sorry_ax_only
                else strip_comments_and_strings(source).splitlines()
            )
            forbidden_axioms = (
                [] if reject_sorry_ax_only else list(ad_hoc_axiom_declarations(lines))
            )
        except OSError as error:
            print(f"{path}: unable to read file: {error}", file=sys.stderr)
            failed = True
            continue
        except ValueError as error:
            print(f"{path}: cannot safely scan Lean declarations: {error}", file=sys.stderr)
            failed = True
            continue

        for number, line in enumerate(lines, start=1):
            has_violation = (
                "sorryAx" in line
                if reject_sorry_ax_only
                else PROOF_HOLE.search(line) is not None
            )
            if has_violation:
                print(f"{path}:{number}:{line}")
                failed = True
        for number, kind in forbidden_axioms:
            print(f"{path}:{number}: ad hoc {kind} declaration")
            failed = True
    return not failed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--reject-sorry-ax",
        action="store_true",
        help="scan the provided theorem-audit output files for sorryAx",
    )
    parser.add_argument("paths", nargs="*", type=Path)
    args = parser.parse_args()

    if args.reject_sorry_ax:
        if not args.paths:
            parser.error("--reject-sorry-ax requires at least one audit output path")
        paths = args.paths
    else:
        if args.paths:
            parser.error("paths are only accepted together with --reject-sorry-ax")
        paths = tracked_lean_sources()

    if check_sources(paths, reject_sorry_ax_only=args.reject_sorry_ax):
        return 0

    if args.reject_sorry_ax:
        print("An audited theorem depends on sorryAx.", file=sys.stderr)
    else:
        print(
            "Lean sources must not contain proof holes or ad hoc axiom declarations.",
            file=sys.stderr,
        )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
