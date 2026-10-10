#!/usr/bin/env python3
"""Exact smooth-part certificate in the 1500-address record window (stdlib).

python src/ripple_smooth_certificate.py
python src/ripple_smooth_certificate.py --output /tmp/ripple_check.json

The corresponding CSV is written next to the JSON. Neither P nor any record
address is materialized. Only modular residues, small prime powers and the
complete Y-smooth divisors D_j are constructed. A nontrivial Y-rough residual
proves existence of a later prime divisor; its value is not recovered.
UNKNOWN addresses are never declared prime or composite without a witness.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from decimal import Decimal, localcontext
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
import platform
import sys
from time import perf_counter


ROOT = Path(__file__).resolve().parent.parent
EXPONENT = 136_279_841
LIMIT = 1_000_000
WIDTH = 1500


def odd_primes(limit):
    """Independent ordinary Eratosthenes; 2 is handled by parity separately."""
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\0\0"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = b"\0" * ((limit - p * p) // p + 1)
    return [p for p in range(3, limit + 1, 2) if flags[p]]


def project_valuations(exponent, width, primes):
    """Lift an entire zero progression from p to p², p³, ... at once.

    N_j = 3*2**exponent + 1 - 2*j. For an odd modulus m its zero indices
    form one class j0 modulo m. Every terminal prime-power residue is kept;
    it certifies that the previous exponents are exact, not lower bounds.
    """
    valuations = [{} for _ in range(width)]
    histories = {}
    pow_calls, hits, active = 0, 0, 0
    for p in primes:
        modulus, exponent_p = p, 1
        residue = pow(2, exponent, modulus)
        pow_calls += 1
        j0 = (3 * residue + 1) * ((modulus + 1) // 2) % modulus
        if j0 >= width:
            continue
        active += 1
        history = []
        while True:
            history.append((modulus, residue))
            if j0 >= width:
                break
            for j in range(j0, width, modulus):
                valuations[j][p] = exponent_p
                hits += 1
            modulus *= p
            exponent_p += 1
            residue = pow(2, exponent, modulus)
            pow_calls += 1
            j0 = (3 * residue + 1) * ((modulus + 1) // 2) % modulus
        histories[p] = history
    return valuations, histories, {
        "odd_primes_examined": len(primes), "active_primes": active,
        "modular_pow_calls_in_projection": pow_calls,
        "prime_power_hit_events": hits,
        "prime_address_pairs": sum(len(row) for row in valuations),
        "maximum_valuation": max((v for row in valuations for v in row.values()), default=0),
    }


def finite_reference_check():
    """Compare symbolic lifting with direct division on small actual integers."""
    cases = positions = fully_smooth = 0
    for exponent in (5, 11, 17):
        for limit in (7, 31, 101):
            primes = odd_primes(limit)
            values, _, _ = project_valuations(exponent, 31, primes)
            for j, symbolic in enumerate(values):
                n = 3 * (1 << exponent) + 1 - 2 * j  # small reference only
                remaining, direct = n, {}
                for p in primes:
                    v = 0
                    while remaining % p == 0:
                        remaining //= p
                        v += 1
                    if v:
                        direct[p] = v
                if direct != symbolic:
                    raise AssertionError((exponent, limit, j, direct, symbolic))
                divisor = prod(p ** v for p, v in symbolic.items())
                assert divisor * remaining == n
                fully_smooth += remaining == 1
                positions += 1
            cases += 1
    assert fully_smooth > 0  # ensure D=N cases do not imply a nontrivial residual
    return {"status": "PASS", "cases": cases, "positions": positions,
            "exponents": [5, 11, 17], "limits": [7, 31, 101],
            "fully_smooth_reference_positions": fully_smooth}


def address(offset):
    return "3P" if offset == 0 else f"3P{offset:+d}"


def build_certificate():
    started = perf_counter()
    check = finite_reference_check()
    checked_at = perf_counter()
    primes = odd_primes(LIMIT)
    basis_at = perf_counter()
    valuations, histories, counters = project_valuations(EXPONENT, WIDTH, primes)
    projection_at = perf_counter()
    rows = []
    independent_pow_checks = 0
    for j, values in enumerate(valuations):
        factor_records = []
        for p, v in values.items():
            modulus_v, residue_v = histories[p][v - 1]
            modulus_next, residue_next = histories[p][v]
            zero = (3 * residue_v + 1 - 2 * j) % modulus_v
            nonzero = (3 * residue_next + 1 - 2 * j) % modulus_next
            assert modulus_v == p ** v and modulus_next == p ** (v + 1)
            assert zero == 0 and nonzero != 0
            # A separate computation verifies both ends of each valuation.
            assert (3 * pow(2, EXPONENT, modulus_v) + 1 - 2 * j) % modulus_v == 0
            assert (3 * pow(2, EXPONENT, modulus_next) + 1 - 2 * j) % modulus_next == nonzero
            independent_pow_checks += 2
            factor_records.append({"p": p, "valuation": v, "p_to_v": modulus_v,
                                   "N_mod_p_to_v": 0, "p_to_v_plus_1": modulus_next,
                                   "N_mod_p_to_v_plus_1": nonzero})
        divisor = prod(p ** v for p, v in values.items())
        remainder = (3 * pow(2, EXPONENT, divisor) + 1 - 2 * j) % divisor
        independent_pow_checks += 1
        assert remainder == 0
        bits = divisor.bit_length()
        assert bits < EXPONENT
        covered = divisor > 1
        rows.append({
            "j": j, "offset_from_3P": 4 - 2 * j, "address": address(4 - 2 * j),
            "status": "COMPOSITE" if covered else "UNKNOWN",
            "small_factorization": factor_records, "D_decimal": str(divisor),
            "D_bit_length": bits, "N_mod_D": remainder,
            "residual_is_integer": True, "residual_greater_than_one": True,
            "residual_has_no_prime_divisor_at_most_Y": True,
            "residual_gt_power_of_two_exponent": EXPONENT - bits,
            "prime_divisor_q_above_Y_exists": True,
            "admissible_late_axis_in_world_P_certified": covered,
            "q_value": None,
        })
    verified_at = perf_counter()
    composite_rows = [row for row in rows if row["status"] == "COMPOSITE"]
    unknown = [row["j"] for row in rows if row["status"] == "UNKNOWN"]
    largest = max(rows, key=lambda row: int(row["D_decimal"]))
    max_divisor = int(largest["D_decimal"])
    square_bits = (max_divisor * max_divisor).bit_length()
    max_subtraction = max(0, 2 * (WIDTH - 1) - 1)
    # 2**(E+1) > max_subtraction, hence every N_j > 2**E.
    lower_bound_verified = EXPONENT + 1 >= max_subtraction.bit_length()
    square_bound_verified = square_bits <= EXPONENT
    assert lower_bound_verified and square_bound_verified
    assert len(primes) == 78497 and counters["active_primes"] == 1161
    assert len(composite_rows) == 1381 and len(unknown) == 119 and unknown[0] == 43
    assert largest["j"] == 17 and max_divisor == 1152208172826291812625387
    assert largest["D_bit_length"] == 80 and counters["maximum_valuation"] == 6
    assert counters["modular_pow_calls_in_projection"] == 79689
    with localcontext() as context:
        context.prec = 60
        coefficient = Decimal(3) / Decimal(max_divisor)
        coefficient_decimal = str(coefficient)
        assert coefficient < Decimal("2.603697e-24")
    # Compare against the earlier bounded experiment when it is supplied.
    previous_file = ROOT / "data/record_original.json"
    previous_comparison = "not supplied"
    if previous_file.exists():
        previous = json.loads(previous_file.read_text(encoding="utf-8"))
        old = previous["extended_window"]["factors"]
        assert len(old) == WIDTH
        for row, factor in zip(rows, old):
            assert (row["status"] == "UNKNOWN") == (factor is None)
            if factor is not None:
                assert int(row["D_decimal"]) % factor == 0
        previous_comparison = "PASS: all 1500 classifications and retained old factors agree"
    finished = perf_counter()
    return {
        "status": "PASS", "classification": "exact_symbolic_smooth_part_certificate_not_a_benchmark",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version.split()[0], "platform": platform.platform(),
        "input": {"P": f"2^{EXPONENT}-1", "exponent": EXPONENT, "Y": LIMIT,
                  "width": WIDTH, "N_j": "3P+4-2*j = 3*2^E+1-2*j",
                  "record_integer_materialized": False},
        "basis": {"all_primes_including_two": len(primes) + 1,
                  "odd_primes": len(primes), "last_prime": primes[-1],
                  "prime_two": "v_2(N_j)=0 because every address is odd",
                  "odd_prime_sequence_sha256": hashlib.sha256(
                      ("\n".join(map(str, primes)) + "\n").encode("ascii")).hexdigest()},
        "finite_reference_check": check, "previous_bounded_experiment": previous_comparison,
        "counts": {**counters, "composite": len(composite_rows), "UNKNOWN": len(unknown),
                   "first_UNKNOWN_j": unknown[0], "first_UNKNOWN_address": "3P-82",
                   "max_D_j": largest["j"], "max_D_decimal": str(max_divisor),
                   "max_D_bit_length": largest["D_bit_length"],
                   "independent_modular_verification_calls": independent_pow_checks},
        "exact_certificate": {
            "D_definition": "D_j = product_{prime p<=Y} p^v_p(N_j), with exact valuations",
            "window_lower_bound": {"statement": "N_j >= 3*2^E-2997 > 2^E",
                                   "maximum_subtraction": max_subtraction,
                                   "maximum_subtraction_bit_length": max_subtraction.bit_length(),
                                   "two_to_E_plus_1_exceeds_subtraction": lower_bound_verified},
            "smooth_part_upper_bound": "D_j <= D_max < 2^80 < 2^E < N_j",
            "uniform_residual_lower_bound": f"N_j/D_j > 2^{EXPONENT - 80} > 1",
            "residual_roughness": "No prime <=Y divides N_j/D_j: every such valuation was removed in full",
            "late_axis_for_covered_positions": (
                "If D_j>1, choose any prime q dividing N_j/D_j. Then q>Y and m=N_j/q>=D_j>=3. "
                "Both q and m are odd. Since N_j<=3P+4, either q>P or m>P would imply "
                "N_j>=3(P+2)>3P+4. Thus Y<q<=P and 3<=m<=P: a valid later axis in S_P."),
            "absorption": "C_{p<=Y}(I) is a subset of C_{Y<p<=P}(I) on this fixed window",
            "conditional_UNKNOWN_statement": (
                "For D_j=1 no compositeness is established. If N_j is composite, all its prime "
                "factors exceed Y and at least one is an admissible later axis in S_P."),
            "scope": "Only the stated window; q values are not produced; no new prime is certified",
        },
        "a_star_bounds": {
            "definition": "a_star(I)=min_{n composite in I} P_plus(n), where P_plus is the largest prime divisor",
            "lower_bound_strict": LIMIT,
            "upper_bound_witness_j": largest["j"], "upper_bound_numerator": "3P-30",
            "upper_bound_denominator_decimal": str(max_divisor),
            "upper_bound_exact": f"a_star(I) <= (3P-30)/{max_divisor}",
            "square_certificate": {"D_max_squared_bit_length": square_bits,
                                   "E_at_least_square_bit_length": square_bound_verified,
                                   "statement": "D_max^2 < 2^E < N_j for every address"},
            "upper_bound_proof": (
                "N_17 is composite. Every prime dividing N_17 divides either D_17 or N_17/D_17. "
                "Since N_17>D_17^2, both kinds of factors are <=N_17/D_17. "
                "The minimum over all composite window addresses cannot exceed this bound."),
            "strict_coefficient_of_P_exact": {"numerator": 3, "denominator_decimal": str(max_divisor)},
            "strict_coefficient_of_P_decimal": coefficient_decimal,
            "conservative_strict_upper_bound": "a_star(I) < 2.603697e-24 * P",
        },
        "timing_seconds": {
            "finite_reference_check": checked_at - started, "basis": basis_at - checked_at,
            "symbolic_projection": projection_at - basis_at,
            "row_certificates_and_independent_modular_checks": verified_at - projection_at,
            "bounds_and_previous_comparison": finished - verified_at,
            "total_before_serialization": finished - started,
            "interpretation": "single diagnostic run; not a paired speed comparison"},
        "rows": rows,
    }


def write_outputs(result, json_path):
    json_path = json_path.resolve()
    json_path.parent.mkdir(parents=True, exist_ok=True)
    csv_path = json_path.with_suffix(".csv")
    json_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    with csv_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["j", "offset_from_3P", "address", "status", "D_decimal", "D_bit_length",
                         "factorization", "valuation_certificates_json", "late_axis_certified", "q_value"])
        for row in result["rows"]:
            factorization = " * ".join(f"{f['p']}^{f['valuation']}" for f in row["small_factorization"]) or "1"
            writer.writerow([row["j"], row["offset_from_3P"], row["address"], row["status"],
                             row["D_decimal"], row["D_bit_length"], factorization,
                             json.dumps(row["small_factorization"], separators=(",", ":")),
                             row["admissible_late_axis_in_world_P_certified"], ""])
    return json_path, csv_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "data/ripple_smooth_certificate.json",
                        help="JSON path; the same basename with .csv is also written")
    args = parser.parse_args()
    if args.output.suffix.lower() != ".json":
        parser.error("--output must name a .json file")
    result = build_certificate()
    json_path, csv_path = write_outputs(result, args.output)
    print(json.dumps({"status": result["status"], "json": str(json_path), "csv": str(csv_path),
                      "counts": result["counts"], "timing_seconds": result["timing_seconds"],
                      "a_star_upper_bound": result["a_star_bounds"]["upper_bound_exact"]},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
