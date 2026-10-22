from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmark_algorithms import make_result_row, measure_case, run_repetition  # noqa: E402


class BenchmarkFailureHandlingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.time_report = Path(self.temp.name) / "time.txt"

    def tearDown(self) -> None:
        self.temp.cleanup()

    @patch("benchmark_algorithms.subprocess.run")
    def test_timeout_is_a_failed_sample_and_clears_stale_rss(self, run: object) -> None:
        self.time_report.write_text("0.01,42\n", encoding="utf-8")
        run.side_effect = subprocess.TimeoutExpired(["algo"], 3, output=b"partial")  # type: ignore[attr-defined]

        result = run_repetition(["algo"], "input", "expected", self.time_report, timeout=3)

        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["timeout_seconds"], 3)
        self.assertEqual(result["stdout"]["text"], "partial")
        self.assertNotIn("peak_rss_kib", result)

    @patch("benchmark_algorithms.subprocess.run")
    def test_wrong_output_is_classified_as_correctness_failure(self, run: object) -> None:
        run.return_value = subprocess.CompletedProcess(["algo"], 0, "wrong", "")  # type: ignore[attr-defined]
        self.time_report.write_text("0.01,42\n", encoding="utf-8")

        result = run_repetition(["algo"], "input", "expected", self.time_report)
        row = make_result_row("sort", "random", 1, 1, [result])

        self.assertEqual(row["status"], "output_mismatch")
        self.assertEqual(row["severity"], "correctness_failure")
        self.assertEqual(row["successful_repeats"], 0)
        self.assertEqual(row["samples"][0]["expected_stdout"]["text"], "expected")

    @patch("benchmark_algorithms.subprocess.run")
    def test_large_output_mismatch_has_bounded_report_and_digest(self, run: object) -> None:
        actual = "x" * 100_000
        run.return_value = subprocess.CompletedProcess(["algo"], 0, actual, "")  # type: ignore[attr-defined]

        result = run_repetition(["algo"], "input", "expected", self.time_report)

        self.assertEqual(result["status"], "output_mismatch")
        output = result["actual_stdout"]
        self.assertEqual(output["length_bytes"], len(actual))
        self.assertEqual(len(output["prefix"]) + len(output["suffix"]), 4096)
        self.assertTrue(output["truncated"])
        self.assertEqual(len(output["sha256"]), 64)

    @patch("benchmark_algorithms.subprocess.run")
    def test_nonzero_exit_is_execution_error(self, run: object) -> None:
        run.return_value = subprocess.CompletedProcess(["algo"], 2, "", "crash")  # type: ignore[attr-defined]

        result = run_repetition(["algo"], "input", "expected", self.time_report)

        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 2)
        self.assertEqual(result["stderr"]["text"], "crash")

    @patch("benchmark_algorithms.run_repetition")
    def test_timeout_does_not_skip_later_repetitions(self, run: object) -> None:
        run.side_effect = [  # type: ignore[attr-defined]
            {"status": "timeout", "wall_seconds": 2.0},
            {
                "status": "success", "wall_seconds": 0.1,
                "gnu_time_seconds": 0.1, "peak_rss_kib": 40,
            },
        ]

        row = measure_case(
            "sort", Path("sort-bin"), Path("time"), "input", "expected",
            "random", 1, 2, self.time_report,
        )

        self.assertEqual(run.call_count, 2)  # type: ignore[attr-defined]
        self.assertEqual(row["status"], "timeout")
        self.assertEqual(row["successful_repeats"], 1)
        self.assertEqual(row["wall_seconds_median"], 0.1)


if __name__ == "__main__":
    unittest.main()
