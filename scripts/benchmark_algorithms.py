#!/usr/bin/env python3
"""Measure end-to-end CLI time and child peak RSS on reproducible input shapes.

Build the executables first with `lake build`. Results include CLI parsing and
formatting; they are measurements, not asymptotic complexity proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import random
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path


ALGORITHMS = (
    "heapsort", "heapsort-rec", "mergesort", "mergesort-loop",
    "quicksort", "quicksort-loop", "median",
)
TIMEOUT_SECONDS = 120
OUTPUT_REPORT_LIMIT = 4096


def summarize_output(value: str) -> dict[str, object]:
    """Keep failure reports bounded while retaining an exact content digest."""
    encoded = value.encode("utf-8")
    summary: dict[str, object] = {
        "length_bytes": len(encoded),
        "sha256": hashlib.sha256(encoded).hexdigest(),
    }
    if len(encoded) <= OUTPUT_REPORT_LIMIT:
        summary["text"] = value
    else:
        half = OUTPUT_REPORT_LIMIT // 2
        summary["prefix"] = encoded[:half].decode("utf-8", errors="replace")
        summary["suffix"] = encoded[-half:].decode("utf-8", errors="replace")
        summary["truncated"] = True
    return summary


def run_repetition(
    command: list[str], input_text: str, expected: str, time_report: Path,
    timeout: int = TIMEOUT_SECONDS,
) -> dict[str, object]:
    """Run and classify one sample; never let a failed sample abort the suite."""
    time_report.unlink(missing_ok=True)
    started = time.perf_counter()
    try:
        result = subprocess.run(
            command, input=input_text, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False, timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        return {
            "status": "timeout",
            "wall_seconds": round(time.perf_counter() - started, 6),
            "timeout_seconds": timeout,
            "stdout": summarize_output(_as_text(error.stdout)),
            "stderr": summarize_output(_as_text(error.stderr)),
        }
    except OSError as error:
        return {
            "status": "execution_error",
            "wall_seconds": round(time.perf_counter() - started, 6),
            "error": str(error),
        }

    sample: dict[str, object] = {
        "wall_seconds": round(time.perf_counter() - started, 6),
        "exit_code": result.returncode,
    }
    try:
        if time_report.is_file():
            seconds, rss = time_report.read_text(encoding="utf-8").strip().split(",")
            sample["gnu_time_seconds"] = float(seconds)
            sample["peak_rss_kib"] = int(rss)
    except (OSError, ValueError) as error:
        sample["measurement_error"] = f"could not parse GNU time output: {error}"

    if result.returncode != 0:
        sample.update({"status": "execution_error", "stderr": summarize_output(result.stderr)})
    elif result.stdout != expected or result.stderr:
        sample.update({
            "status": "output_mismatch",
            "expected_stdout": summarize_output(expected),
            "actual_stdout": summarize_output(result.stdout),
            "stderr": summarize_output(result.stderr),
        })
    elif "gnu_time_seconds" not in sample or "peak_rss_kib" not in sample:
        sample["status"] = "execution_error"
    else:
        sample["status"] = "success"
    return sample


def _as_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    return value.decode(errors="replace") if isinstance(value, bytes) else value


def make_result_row(
    algorithm: str, shape: str, size: int, repeats: int, samples: list[dict[str, object]],
) -> dict[str, object]:
    successful = [sample for sample in samples if sample["status"] == "success"]
    statuses = {sample["status"] for sample in samples}
    status = "success" if len(successful) == repeats else (
        "output_mismatch" if "output_mismatch" in statuses else
        "execution_error" if "execution_error" in statuses else "timeout"
    )
    row: dict[str, object] = {
        "algorithm": algorithm,
        "input_shape": shape,
        "size": size,
        "repeats": repeats,
        "status": status,
        "successful_repeats": len(successful),
        "samples": samples,
    }
    if successful:
        row.update({
            "wall_seconds_median": statistics.median(sample["wall_seconds"] for sample in successful),
            "wall_seconds_gnu_time_median": statistics.median(sample["gnu_time_seconds"] for sample in successful),
            "peak_rss_kib_max": max(sample["peak_rss_kib"] for sample in successful),
        })
    if status == "output_mismatch":
        row["severity"] = "correctness_failure"
    return row


def measure_case(
    algorithm: str, binary: Path, timer: Path, input_text: str, expected: str,
    shape: str, size: int, repeats: int, time_report: Path,
) -> dict[str, object]:
    samples = []
    for _ in range(repeats):
        command = [str(timer), "-f", "%e,%M", "-o", str(time_report), str(binary)]
        samples.append(run_repetition(command, input_text, expected, time_report))
    return make_result_row(algorithm, shape, size, repeats, samples)


def make_values(size: int, shape: str, seed: int) -> list[int]:
    generator = random.Random(seed)
    if shape == "random":
        return [generator.randrange(0, max(1, size * 4)) for _ in range(size)]
    if shape == "ascending":
        return list(range(size))
    if shape == "descending":
        return list(range(size - 1, -1, -1))
    if shape == "duplicates":
        return [generator.randrange(8) for _ in range(size)]
    raise ValueError(f"unknown input shape: {shape}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", type=int, nargs="+", default=[100, 1000, 5000])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20261022)
    parser.add_argument("--output", type=Path, help="write results as JSON instead of stdout")
    args = parser.parse_args()
    if any(size < 0 for size in args.sizes) or args.repeats < 1:
        parser.error("sizes must be non-negative and repeats must be positive")
    timer = Path("/usr/bin/time")
    if not timer.exists():
        parser.error("GNU time is required to measure per-process peak RSS")

    binary_root = Path(".lake/build/bin")
    binaries = {name: binary_root / name for name in ALGORITHMS}
    missing = [str(path) for path in binaries.values() if not path.is_file()]
    if missing:
        parser.error("build all CLI executables first with `lake build`; missing: " + ", ".join(missing))

    rows: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="lean-experiments-bench-") as directory:
        time_report = Path(directory) / "time.txt"
        for size in args.sizes:
            for shape in ("random", "ascending", "descending", "duplicates"):
                values = make_values(size, shape, args.seed)
                input_text = " ".join(map(str, values)) + "\n"
                sorted_output = " ".join(map(str, sorted(values))) + "\n"
                expected_median = "none\n" if not values else None
                if values:
                    ordered = sorted(values)
                    middle = len(values) // 2
                    expected_median = (
                        f"{ordered[middle]}\n" if len(values) % 2
                        else f"{(ordered[middle - 1] + ordered[middle]) // 2}"
                        + (".5\n" if (ordered[middle - 1] + ordered[middle]) % 2 else "\n")
                    )
                for algorithm, binary in binaries.items():
                    expected = expected_median if algorithm == "median" else sorted_output
                    row = measure_case(
                        algorithm, binary, timer, input_text, expected,
                        shape, size, args.repeats, time_report,
                    )
                    rows.append(row)
                    if row["status"] != "success":
                        print(
                            f"{algorithm} {shape} size={size}: {row['status']} "
                            f"({row['successful_repeats']}/{args.repeats} successful samples)",
                            file=sys.stderr,
                        )

    report = {
        "toolchain": Path("lean-toolchain").read_text(encoding="utf-8").strip(),
        "platform": platform.platform(),
        "python": sys.version.split()[0],
        "seed": args.seed,
        "timeout_seconds": TIMEOUT_SECONDS,
        "measurement": "CLI end-to-end wall time and GNU time child peak RSS; includes parsing and output formatting",
        "complexity_claim": "none; these are empirical measurements",
        "results": rows,
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 1 if any(row["status"] != "success" for row in rows) else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error
