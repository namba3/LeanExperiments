#!/usr/bin/env python3
"""Measure end-to-end CLI time and child peak RSS on reproducible input shapes.

Build the executables first with `lake build`. Results include CLI parsing and
formatting; they are measurements, not asymptotic complexity proofs.
"""

from __future__ import annotations

import argparse
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
                    elapsed: list[float] = []
                    gnu_elapsed: list[float] = []
                    peak_rss_kib: list[int] = []
                    expected = expected_median if algorithm == "median" else sorted_output
                    for _ in range(args.repeats):
                        command = [str(timer), "-f", "%e,%M", "-o", str(time_report), str(binary)]
                        started = time.perf_counter()
                        result = subprocess.run(command, input=input_text, text=True,
                                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                                check=False, timeout=120)
                        elapsed.append(time.perf_counter() - started)
                        if result.returncode != 0 or result.stdout != expected or result.stderr:
                            raise RuntimeError(
                                f"{algorithm} failed {shape} input of size {size}: "
                                f"exit={result.returncode}, stderr={result.stderr!r}"
                            )
                        seconds, rss = time_report.read_text(encoding="utf-8").strip().split(",")
                        gnu_elapsed.append(float(seconds))
                        peak_rss_kib.append(int(rss))
                    rows.append({
                        "algorithm": algorithm,
                        "input_shape": shape,
                        "size": size,
                        "repeats": args.repeats,
                        "wall_seconds_median": round(statistics.median(elapsed), 6),
                        "wall_seconds_gnu_time_median": statistics.median(gnu_elapsed),
                        "peak_rss_kib_max": max(peak_rss_kib),
                    })

    report = {
        "toolchain": Path("lean-toolchain").read_text(encoding="utf-8").strip(),
        "platform": platform.platform(),
        "seed": args.seed,
        "measurement": "CLI end-to-end wall time and GNU time child peak RSS; includes parsing and output formatting",
        "complexity_claim": "none; these are empirical measurements",
        "results": rows,
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error
