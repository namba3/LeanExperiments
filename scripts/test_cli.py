#!/usr/bin/env python3
"""Run representative end-to-end checks against every LeanExperiments CLI."""

from __future__ import annotations

import subprocess
import sys


def run_cli(application: str, input_text: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "exe", application],
        input=input_text,
        text=True,
        capture_output=True,
        check=False,
        timeout=30,
    )


def expect_output(application: str, input_text: str, expected: str) -> None:
    result = run_cli(application, input_text)
    if result.returncode != 0 or result.stdout != expected or result.stderr:
        raise AssertionError(
            f"{application}: expected exit 0, stdout {expected!r}, and empty stderr; "
            f"got exit {result.returncode}, stdout {result.stdout!r}, "
            f"stderr {result.stderr!r}"
        )


def expect_error(application: str, input_text: str, expected_error: str) -> None:
    result = run_cli(application, input_text)
    if result.returncode != 1 or result.stdout or result.stderr != expected_error:
        raise AssertionError(
            f"{application}: expected exit 1, empty stdout, and stderr "
            f"{expected_error!r}; got exit {result.returncode}, "
            f"stdout {result.stdout!r}, stderr {result.stderr!r}"
        )


def main() -> int:
    for application in (
        "heapsort",
        "heapsort-rec",
        "mergesort",
        "mergesort-loop",
        "quicksort",
        "quicksort-loop",
    ):
        expect_output(application, "7 2 5 2 0 9\n", "0 2 2 5 7 9\n")
        expect_output(application, "", "\n")

    expect_output("median", "9 1 4 2 7 3\n", "3.5\n")
    expect_output("median", "9 1 4 2 7\n", "4\n")
    expect_output("median", "", "none\n")
    # Exercise large decimal tokens and a long list through the real parser and CLI.
    large_natural = "9" * 256
    expect_output("median", f"{large_natural} {large_natural}\n", f"{large_natural}\n")
    long_values = list(range(4095, -1, -1))
    expect_output(
        "heapsort",
        " ".join(map(str, long_values)),
        " ".join(map(str, reversed(long_values))) + "\n",
    )
    expect_output("factorial", "10\n", "3628800\n")
    expect_output("factorial", "0\n", "1\n")
    expect_output("prime-factors", "360\n", "2 2 2 3 3 5\n")
    expect_output("prime-factors", "1\n", "(none)\n")
    expect_output("fibonacci", "100\n", "354224848179261915075\n")
    expect_output("fibonacci", "0\n", "0\n")

    expect_error("heapsort", "12 3x 45", "heapsort: expected non-negative integers\n")
    expect_error("factorial", "", "factorial: expected exactly one integer on standard input\n")
    expect_error(
        "factorial",
        "1 2",
        "factorial: expected exactly one integer on standard input\n",
    )
    expect_error("fibonacci", "-1", "fibonacci: expected non-negative integers\n")
    print("All CLI smoke checks passed.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error
