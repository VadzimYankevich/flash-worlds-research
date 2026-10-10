"""Check saved results and optionally rerun the canonical experiments.

Python standard library only. Run from any working directory:
    python src/reproduce.py
    python src/reproduce.py --record
    python src/reproduce.py --benchmark

The *_original.json files and their historical CSV tables are never modified.
An explicit rerun replaces only its *_rerun.json and *_rerun_*.csv files.
The timed source files extracted from the snapshots remain byte-for-byte exact.
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
from itertools import permutations
import json
from math import gcd, isclose, isfinite, isqrt, lcm
import os
from pathlib import Path
from statistics import median
import subprocess
import sys
import tempfile


SRC = Path(__file__).resolve().parent
DATA = SRC.parent / "data"
MODES = ("candidate_prime", "segmented", "mr12_candidates")
COMPARISONS = (("segmented", "candidate_prime"),
               ("candidate_prime", "mr12_candidates"),
               ("segmented", "mr12_candidates"))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def benchmark_tables(result):
    rows = result["observations_raw"]
    medians = [dict(mode=mode, rounds=sum(r["mode"] == mode for r in rows),
                    median_seconds=median(r["seconds"] for r in rows
                                          if r["mode"] == mode))
               for mode in MODES]
    paired = []
    for numerator, denominator in COMPARISONS:
        ratios = []
        for round_no in sorted({r["round"] for r in rows}):
            times = {r["mode"]: r["seconds"] for r in rows
                     if r["round"] == round_no}
            ratios.append(times[numerator] / times[denominator])
        paired.append(dict(
            numerator=numerator, denominator=denominator,
            paired_rounds=len(ratios), median_paired_time_ratio=median(ratios),
            numerator_faster_rounds=sum(r < 1 for r in ratios),
            denominator_faster_rounds=sum(r > 1 for r in ratios),
            equal_rounds=sum(r == 1 for r in ratios)))
    return {"observations": rows, "medians": medians, "summary": paired}


def write_benchmark_csv(result, prefix):
    """Used only for explicit reruns; historical tables are supplied in data/."""
    for suffix, rows in benchmark_tables(result).items():
        target = DATA / (prefix + "_" + suffix + ".csv")
        with target.open("w", encoding="utf-8", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)


def verify_benchmark(result):
    rows = result["observations_raw"]
    require(result["status"] == "PASS", "Benchmark status is not PASS")
    require(result["flashes"] == 28 and result["rounds"] == 12,
            "Unexpected canonical benchmark size")
    require(len(rows) == result["observations"] == 36,
            "Unexpected number of benchmark observations")
    orders = []
    for round_no in range(1, 13):
        sample = sorted((r for r in rows if r["round"] == round_no),
                        key=lambda r: r["position"])
        require([r["position"] for r in sample] == [1, 2, 3],
                "Invalid benchmark order positions")
        orders.append(tuple(r["mode"] for r in sample))
    require(Counter(orders) == Counter(list(permutations(MODES)) * 2),
            "Each of the six benchmark orders must occur twice")
    require(all(isfinite(r["seconds"]) and r["seconds"] > 0 for r in rows),
            "Nonpositive or nonfinite elapsed time")
    tables = benchmark_tables(result)
    for row in tables["medians"]:
        require(isclose(row["median_seconds"],
                        result["median_seconds"][row["mode"]], rel_tol=1e-14),
                "Stored median differs from raw observations")
    for row in tables["summary"]:
        if row["denominator"] == "mr12_candidates":
            stored = result["median_paired_speedup_vs_mr"][row["numerator"]]
            require(isclose(row["median_paired_time_ratio"], stored,
                            rel_tol=1e-14), "Stored paired ratio differs")
    require(result["distinct_windows"] == 31,
            "Unexpected number of canonical windows")
    require(result["window_answers_compared"] == 31 * 36,
            "Unexpected window comparison count")
    require(result["final_anchor"] == 63286095838211,
            "Unexpected final anchor")
    return dict(status="PASS", observations=len(rows), paired_rounds=12,
                timing_note="Historical timing arithmetic is checked; elapsed times are not remeasured without --benchmark.")


def odd_primes(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p:limit+1:p] = b"\x00" * ((limit-p*p)//p + 1)
    return [p for p in range(3, limit + 1, 2) if flags[p]]


def verify_record(result):
    require(result["status"] == "PASS", "Record probe status is not PASS")
    exponent = result["input"]["exponent"]
    limit = result["input"]["small_prime_limit"]
    require(exponent == 136279841 and limit == 1_000_000,
            "Unexpected canonical record probe parameters")
    primes = odd_primes(limit)
    prime_set = set(primes)
    residues = {p: pow(2, exponent, p) for p in primes}
    for name in ("first_window", "extended_window"):
        window = result[name]
        require(len(window["factors"]) == window["width"], "Wrong window size")
        for j, p in enumerate(window["factors"]):
            if p is not None:
                require(p in prime_set, "Witness is not an allowed prime")
                require((3 * residues[p] + 1 - 2*j) % p == 0,
                        "Invalid exact divisor witness at position " + str(j))
        require(window["unresolved_j"] == [j for j, p in
                enumerate(window["factors"]) if p is None], "Unknown indices differ")
    # Independently rebuild the bounded coverage and its first-factor choices.
    extended = result["extended_window"]
    factors = [None] * extended["width"]
    for p in primes:
        j0 = ((3 * residues[p] + 1) * ((p + 1) // 2)) % p
        for j in range(j0, len(factors), p):
            if factors[j] is None:
                factors[j] = p
    require(factors == extended["factors"], "Bounded coverage differs")
    unknown = [j for j, p in enumerate(factors) if p is None]
    require(len(factors) == 1500 and len(unknown) == 119 and unknown[0] == 43,
            "Expected 1381 covered positions, 119 unknowns, first at j=43")
    require(4 - 2*unknown[0] == -82, "Candidate address derivation differs")
    keep = result["reuse"]["first_nine_primes"]
    require(keep == [3, 5, 7, 11, 17, 53, 89, 2749, 139291],
            "First-window retained primes differ")
    inherited = set()
    for p in keep:
        j0 = ((3 * residues[p] + 1) * ((p + 1) // 2)) % p
        inherited.update(range(j0, len(factors), p))
    require(len(inherited) == result["reuse"]["covered_by_first_nine"] == 936,
            "Inherited coverage differs")
    minimality = result["minimum_first_window_certificate"]
    for j in minimality["isolated_indices"]:
        for k in range(15):
            if j != k:
                d = abs(j-k)
                require(gcd((3*pow(2, exponent, d)+1-2*j) % d, d) == 1,
                        "Isolated-point certificate fails")
    rule = result["reusable_exponent_rule"]
    require(rule["primes"] == keep, "Exponent rule uses different primes")
    for p, order in zip(keep, rule["multiplicative_orders_of_two"]):
        require(pow(2, order, p) == 1, "Invalid exponent period")
    require(lcm(*rule["multiplicative_orders_of_two"]) ==
            rule["exponent_modulus"] == 18245318520, "Combined period differs")
    require(exponent % rule["exponent_modulus"] == rule["exponent_residue"],
            "Exponent residue differs")
    return dict(status="PASS", small_primes_checked=len(primes),
                covered_positions=1381, unresolved_positions=119,
                closed_top_positions=43, first_unknown="3P-82",
                first_unknown_primality="not established")


def verify_originals():
    benchmark = read_json(DATA / "benchmark_original.json")
    record = read_json(DATA / "record_original.json")
    for relative, source in benchmark["embedded_sources"].items():
        actual = (SRC / relative).read_bytes()
        require(actual == source.encode("utf-8"), "Source differs: " + relative)
        expected_hash = benchmark["embedded_source_sha256"][relative]
        require(hashlib.sha256(actual).hexdigest() == expected_hash,
                "Source hash differs: " + relative)
    require((SRC / "record_boundary_probe.py").read_bytes() ==
            record["embedded_source"].encode("utf-8"), "Record source differs")
    for suffix, expected in benchmark_tables(benchmark).items():
        with (DATA / ("benchmark_original_" + suffix + ".csv")).open(
                encoding="utf-8", newline="") as stream:
            actual = list(csv.DictReader(stream))
        require(actual == [{k: str(v) for k, v in row.items()} for row in expected],
                "Historical CSV differs: " + suffix)
    return dict(sources="byte-for-byte match", benchmark=verify_benchmark(benchmark),
                record=verify_record(record))


def run_benchmark():
    require(hasattr(os, "sched_getaffinity") and hasattr(os, "sched_setaffinity"),
            "The unchanged canonical benchmark requires Linux CPU-affinity APIs; use Linux or WSL.")
    completed = subprocess.run([sys.executable, "strong_baseline_probe.py"],
                               cwd=SRC, capture_output=True, text=True, check=True)
    result = json.loads(completed.stdout)
    verify_benchmark(result)
    target = DATA / "benchmark_rerun.json"
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n",
                      encoding="utf-8")
    write_benchmark_csv(result, "benchmark_rerun")
    return dict(output=str(target), median_seconds=result["median_seconds"],
                paired_ratios=result["median_paired_speedup_vs_mr"])


def run_record():
    # The unchanged canonical script writes beside itself; isolate that output.
    with tempfile.TemporaryDirectory(prefix="flash_worlds_record_") as temporary:
        script = Path(temporary) / "record_boundary_probe.py"
        script.write_bytes((SRC / script.name).read_bytes())
        subprocess.run([sys.executable, str(script)], cwd=temporary,
                       capture_output=True, text=True, check=True)
        raw = script.with_name("record_window_boundary_probe_2026-10-10.json")
        result = read_json(raw)
        verification = verify_record(result)
        target = DATA / "record_rerun.json"
        target.write_bytes(raw.read_bytes())
    return dict(output=str(target), verification=verification)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true",
                        help="Rerun all 36 canonical timed observations")
    parser.add_argument("--record", action="store_true",
                        help="Rerun the bounded symbolic record probe")
    args = parser.parse_args()
    report = dict(originals=verify_originals())
    if args.record:
        report["record_rerun"] = run_record()
    if args.benchmark:
        report["benchmark_rerun"] = run_benchmark()
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
