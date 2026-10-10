"""Exact pilot of the oldest necessary axis in a suffix of prime axes.

This is an ex-post analysis using complete factorization of small test windows.
It is not an efficient algorithm for finding the cutoff at the record prime.
Run from any directory; the default output is data/ripple_depth.json.
Existing output files are not overwritten. Python standard library only.
"""
from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from datetime import datetime, timezone
from decimal import Decimal, localcontext
import csv
import json
from math import isqrt, prod
from pathlib import Path
import sys
from time import perf_counter


SRC = Path(__file__).resolve().parent
DATA = SRC.parent / "data"
FLASH_LIMIT = 10_000_000
PRIME_LIMIT = 5000
WIDTH = 15
WATCHED_AXES = (5, 7, 13)


def prime_sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if flags[prime]:
            flags[prime*prime:limit+1:prime] = b"\x00" * ((limit-prime*prime)//prime + 1)
    return [prime for prime in range(2, limit + 1) if flags[prime]]


class CompleteFactorizer:
    def __init__(self, primes):
        self.primes = primes
        self.saved = {}
        self.requests = self.cache_hits = self.modulus_tests = 0
        self.seconds = 0.0

    def factor(self, number):
        self.requests += 1
        if number in self.saved:
            self.cache_hits += 1
            return self.saved[number]
        started = perf_counter()
        remaining = number
        factors = []
        for prime in self.primes:
            if prime * prime > remaining:
                break
            self.modulus_tests += 1
            if remaining % prime:
                continue
            power = 0
            while remaining % prime == 0:
                self.modulus_tests += 1
                remaining //= prime
                power += 1
            factors.append((prime, power))
        if remaining > 1:
            factors.append((remaining, 1))
        assert prod(prime ** power for prime, power in factors) == number
        self.saved[number] = factors
        self.seconds += perf_counter() - started
        return factors


def analyze_window(world_bound, primes, factorizer):
    right = min(world_bound * world_bound, 3 * world_bound + 4)
    left = max(3, right - 2 * (WIDTH - 1))
    composites, holes = [], []
    for number in range(left, right + 1, 2):
        factors = factorizer.factor(number)
        if factors == [(number, 1)]:
            holes.append(number)
            continue
        axes = [prime for prime, _ in factors
                if prime <= world_bound and 3 <= number // prime <= world_bound]
        assert axes, (world_bound, number, factors)
        assert axes == [prime for prime, _ in factors], (world_bound, number, axes)
        composites.append(dict(n=number, factorization=[list(pair) for pair in factors],
                               admissible_prime_axes=axes, latest_witness=max(axes)))
    latest_axes = sorted({row["latest_witness"] for row in composites})
    cutoff = min(latest_axes) if latest_axes else None
    rank_bound = bisect_right(primes, world_bound)
    full_suffix_count = rank_bound - bisect_left(primes, cutoff) if cutoff else 0
    critical = next((row for row in composites if row["latest_witness"] == cutoff), None)
    local_axes = sorted({prime for row in composites for prime in row["admissible_prime_axes"]})
    for prime in local_axes:
        shadow = {row["n"] for row in composites if prime in row["admissible_prime_axes"]}
        later_union = {row["n"] for row in composites
                       if any(later > prime for later in row["admissible_prime_axes"])}
        largest_factor_layer = {row["n"] for row in composites
                                if row["factorization"][-1][0] == prime}
        assert shadow - later_union == largest_factor_layer
    activity = {}
    for prime in WATCHED_AXES:
        shadow = [row["n"] for row in composites if prime in row["admissible_prime_axes"]]
        fresh = [row["n"] for row in composites if row["latest_witness"] == prime]
        state = ("not_yet_an_axis" if prime > world_bound else "active" if fresh else
                 "absorbed_by_larger_axes" if shadow else "no_shadow_in_window")
        later = [dict(n=row["n"], later_axis=row["latest_witness"])
                 for row in composites
                 if prime in row["admissible_prime_axes"] and row["latest_witness"] > prime]
        activity[str(prime)] = dict(state=state, active=bool(fresh),
                                   shadow_addresses=shadow, exclusive_to_later_axes_addresses=fresh,
                                   later_witnesses=later)
    return dict(B=world_bound, L=left, R=right, odd_positions=(right-left)//2+1,
                composite_count=len(composites), holes=holes, a_star=cutoff,
                a_star_over_B=(cutoff/world_bound if cutoff else None),
                a_star_over_B_exact=(str(cutoff)+"/"+str(world_bound) if cutoff else None),
                prime_index_of_B=rank_bound, full_prime_suffix_count=full_suffix_count,
                latest_witness_sparse_axes=latest_axes,
                latest_witness_sparse_axes_count=len(latest_axes),
                pancake_identity_axes_checked=len(local_axes),
                cutoff_maximality_witness=critical, composites=composites,
                watched_axis_activity=activity,
                empty_composite_case=("No cutoff is forced; all axes can be removed."
                                      if cutoff is None else None))


def find_reactivations(windows):
    events = []
    for prime in WATCHED_AXES:
        previous_active = None
        inactive_windows = []
        for window in windows:
            activity = window["watched_axis_activity"][str(prime)]
            if activity["active"]:
                if previous_active is not None and inactive_windows:
                    before = previous_active["watched_axis_activity"][str(prime)]
                    events.append(dict(
                        prime=prime, active_before_B=previous_active["B"],
                        active_before_witnesses=before["exclusive_to_later_axes_addresses"],
                        inactive_B_values=[w["B"] for w in inactive_windows],
                        inactive_states=[w["watched_axis_activity"][str(prime)]["state"]
                                         for w in inactive_windows],
                        reactivated_B=window["B"],
                        reactivated_witnesses=activity["exclusive_to_later_axes_addresses"]))
                previous_active = window
                inactive_windows = []
            elif previous_active is not None:
                inactive_windows.append(window)
    return sorted(events, key=lambda row: (row["reactivated_B"], row["prime"]))


def record_cutoff_bounds():
    record = json.loads((DATA / "record_original.json").read_text(encoding="utf-8"))
    exponent = record["input"]["exponent"]
    examples = []
    for prefix_width, index, divisor in ((15, 0, 53), (15, 13, 139291), (43, 25, 483167)):
        assert record["extended_window"]["factors"][index] == divisor
        constant = 1 - 2 * index  # N_j = 3*2^E + constant.
        assert (3 * pow(2, exponent, divisor) + constant) % divisor == 0
        # A small exact inequality proves N_j > divisor^2 without building P.
        assert exponent >= 40 and 3 * (1 << 40) + constant > divisor * divisor
        offset_from_3P = 4 - 2 * index
        numerator = "3P" + ("+" if offset_from_3P >= 0 else "") + str(offset_from_3P)
        with localcontext() as context:
            context.prec = 50
            ratio = str(Decimal(3) / Decimal(divisor))
        examples.append(dict(
            known_closed_prefix_width=prefix_width, index=index, n_expression=numerator,
            known_divisor=divisor, exact_modular_witness_verified=True,
            n_greater_than_divisor_squared_verified=True,
            prime_axis_suffix_cutoff_upper_bound="a* <= ("+numerator+")/"+str(divisor),
            normalized_bound_exact="a*/P <= (3" + ("+" if offset_from_3P >= 0 else "") +
                                   str(offset_from_3P)+"/P)/"+str(divisor),
            limiting_ratio_3_over_divisor_decimal=ratio,
            strict_constant_upper_bound=("a*/P < 3/"+str(divisor)
                                         if offset_from_3P < 0 else None)))
    return dict(
        classification="Analytic upper bounds for suffixes of literal prime axes, on known composite positions only.",
        P="2^136279841-1", record_integer_constructed=False,
        argument="If d divides n and n>d^2, each prime divisor q of n is at most n/d: q divides d and is at most d<n/d, or q divides n/d. Therefore min_n max D_B(n) is at most n/d for any exhibited n.",
        examples=examples,
        positive_absorption_example=dict(
            n="3P", old_axis=3, new_axis="P", new_cofactor=3,
            identity="3*P=P*3", assumption="P is the declared known prime.",
            scope="The new axis P covers this particular address formerly covered by axis 3; no whole-window absorption claim is made."),
        next_unresolved=dict(index=43, n="3P-82", status="UNKNOWN",
                             primality="not established", complete_factorization_available=False),
        limitations=[
            "These are upper bounds, not the exact record-window cutoff.",
            "They do not count the depth or size of arbitrary saved refinement rules.",
            "They do not prove a lower bound on the running time of every possible method.",
            "The plus-four example approaches 3/53 from above; 3/53 alone is not its strict upper bound."
        ])


def run():
    started = perf_counter()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(SRC / "candidate_work"))
    from flash_candidates import FlashRunner, make_backend
    runner = FlashRunner(make_backend("candidate_prime", profile=False))
    route_bounds = []
    while runner.B < FLASH_LIMIT:
        route_bounds.append(runner.B)
        runner.run(1)
    route_seconds = perf_counter() - started
    sieve_started = perf_counter()
    rank_limit = max(PRIME_LIMIT, max(route_bounds))
    primes = prime_sieve(rank_limit)
    sieve_seconds = perf_counter() - sieve_started
    factorizer = CompleteFactorizer(primes)
    analysis_started = perf_counter()
    route_windows = [analyze_window(bound, primes, factorizer) for bound in route_bounds]
    prime_windows = [analyze_window(bound, primes, factorizer)
                     for bound in primes[1:bisect_right(primes, PRIME_LIMIT)]]
    windows_by_bound = {window["B"]: window for window in prime_windows}
    old, new = windows_by_bound[71], windows_by_bound[211]
    next_flash = primes[bisect_right(primes, old["R"])-1]
    assert next_flash == 211
    assert old["watched_axis_activity"]["5"]["state"] == "absorbed_by_larger_axes"
    assert 625 in new["watched_axis_activity"]["5"]["exclusive_to_later_axes_addresses"]
    valid_transition = dict(
        scope="Valid flash from starting world 71; not part of the canonical route starting at 3.",
        old_B=71, next_B=211, old_window=[old["L"], old["R"]],
        new_window=[new["L"], new["R"]],
        closed_suffix_to_next_flash=[row for row in old["composites"] if row["n"] > next_flash],
        old_axis_5=old["watched_axis_activity"]["5"],
        new_axis_5=new["watched_axis_activity"]["5"],
        reactivation_witness=next(row for row in new["composites"] if row["n"] == 625))
    analysis_seconds = perf_counter() - analysis_started
    result = dict(
        status="PASS", generated_at_utc=datetime.now(timezone.utc).isoformat(),
        classification="Exact small-window pilot with complete ex-post factorization; not a speed benchmark.",
        input=dict(flash_B_upper_exclusive=FLASH_LIMIT, general_prime_B_upper_inclusive=PRIME_LIMIT,
                   requested_odd_window_width=WIDTH, watched_prime_axes=list(WATCHED_AXES)),
        definition=dict(world="S_B={p*m: p odd prime<=B, m odd, 3<=m<=B}",
                        window="I=[max(3,G(B)-28),G(B)] restricted to odd addresses; G(B)=min(B^2,3B+4)",
                        allowed_axes="D_B(n)={prime p dividing n: p<=B, 3<=n/p<=B}",
                        latest_witness="max D_B(n)",
                        suffix_cutoff="a*=min over composite n in I of latest_witness(n)",
                        full_suffix_count="pi(B)-pi(a*-1)",
                        sparse_count="Number of distinct latest_witness values; a specific covering set, not a proven minimum-cardinality cover.",
                        active="T_p(I) minus the union of T_q(I) for all q>p is nonempty; equivalent to latest_witness(n)=p for some n."),
        worlds=dict(canonical_flash_route=route_windows, all_prime_B_sequence=prime_windows),
        reactivations=dict(canonical_flash_route=find_reactivations(route_windows),
                           all_prime_B_sequence=find_reactivations(prime_windows)),
        additional_valid_flash_transition=valid_transition,
        pancake_identity=dict(
            formula="(T_p(I) minus union_{q>p} T_q(I)) = {composite n in I: P_plus(n)=p} = union_{k>=1} p^k H_<p restricted to composite n in I.",
            meaning="Every residual address has a power of p times a factor built only from smaller odd primes; H_<p includes 1.",
            equality_asserted_for_every_local_axis=True,
            local_axis_checks=sum(window["pancake_identity_axes_checked"]
                                  for window in route_windows + prime_windows),
            axis_5_examples=[dict(B=31, n=75, p=5, power=2, lower_prime_part=3,
                                  identity="75=5^2*3"),
                             dict(B=211, n=625, p=5, power=4, lower_prime_part=1,
                                  identity="625=5^4*1")]),
        record_prime_axis_suffix_upper_bounds=record_cutoff_bounds(),
        factorization_work=dict(requests=factorizer.requests, unique_numbers_fully_factored=len(factorizer.saved),
                                saved_factorization_hits=factorizer.cache_hits,
                                successful_or_initial_modulus_tests=factorizer.modulus_tests,
                                rank_sieve_limit=rank_limit, rank_sieve_primes=len(primes)),
        timing_seconds=dict(canonical_route=route_seconds, rank_sieve=sieve_seconds,
                            all_window_analysis_including_factorization=analysis_seconds,
                            uncached_factorization_inside_window_analysis=factorizer.seconds,
                            total_computation_excluding_serialization=perf_counter()-started),
        limitations=[
            "a* is computed after complete factorization of every small pilot address; this cost and rank-sieve construction are included in pilot timings.",
            "This does not supply an efficient way to obtain a* or a sufficient exact world at the record P.",
            "A minimum-length full suffix of prime axes differs from a minimum-cardinality sparse cover and from saved composite refinement rules.",
            "Activity is local to the current window. No-shadow and absorption-by-later-axes are recorded separately.",
            "Absence of a reactivation in the finite canonical sample would not prove permanent inactivity.",
            "Historical speed benchmarks are not rerun or changed by this pilot."
        ])
    return result


def save(result, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    csv_target = target.with_suffix(".csv")
    activity_target = target.with_name(target.stem + "_activity.csv")
    if any(path.exists() for path in (target, csv_target, activity_target)):
        raise FileExistsError("Choose a new --output name; existing pilot files are preserved")
    with target.open("x", encoding="utf-8") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    fields = ("B", "L", "R", "odd_positions", "composite_count", "a_star", "a_star_over_B",
              "prime_index_of_B", "full_prime_suffix_count", "latest_witness_sparse_axes_count")
    with csv_target.open("x", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["sequence", "index", *fields, "cutoff_witness_n"])
        writer.writeheader()
        for sequence, windows in result["worlds"].items():
            for index, window in enumerate(windows):
                row = {key: window[key] for key in fields}
                witness = window["cutoff_maximality_witness"]
                row.update(sequence=sequence, index=index, cutoff_witness_n=witness["n"] if witness else None)
                writer.writerow(row)
    with activity_target.open("x", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["sequence", "B", "prime", "state", "shadow_addresses", "fresh_addresses"])
        writer.writeheader()
        for sequence, windows in result["worlds"].items():
            for window in windows:
                for prime, activity in window["watched_axis_activity"].items():
                    writer.writerow(dict(sequence=sequence, B=window["B"], prime=prime,
                                         state=activity["state"],
                                         shadow_addresses=" ".join(map(str, activity["shadow_addresses"])),
                                         fresh_addresses=" ".join(map(str, activity["exclusive_to_later_axes_addresses"]))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DATA / "ripple_depth.json")
    args = parser.parse_args()
    result = run()
    save(result, args.output)
    print(json.dumps(dict(output=str(args.output.resolve()), status=result["status"],
                          windows={key: len(value) for key, value in result["worlds"].items()},
                          reactivation_counts={key: len(value) for key, value in result["reactivations"].items()},
                          timing_seconds=result["timing_seconds"]), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
