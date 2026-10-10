#!/usr/bin/env python3
"""Finite, exact checks of the mathematical statements in this package.

This is a reproducible audit on explicitly bounded inputs, not a proof of the
corresponding general theorems and not a performance comparison.  It requires
only the Python standard library.  Run without arguments to regenerate
data/mathematics_checks.json, or choose a separate destination with --output.

Two different objects are deliberately kept separate:
  S_B: the finite union of odd-prime multiplication shadows with m <= B;
  exponent worlds: products of a fixed finite prime basis, including 1.
The latter illustrate coordinates, slices and projections of the geometric
interpretation; they do not silently replace the definition of S_B.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
import platform
import sys
from time import perf_counter


def require(condition: bool, message: str) -> None:
    """Checks remain enabled even if Python is launched with -O."""
    if not condition:
        raise AssertionError(message)


def trial_primes(limit: int) -> list[int]:
    """Prime supply for the literal construction, independent of the sieve."""
    answer = []
    for n in range(2, limit + 1):
        if all(n % d for d in range(2, isqrt(n) + 1)):
            answer.append(n)
    return answer


def reference_sieve(limit: int) -> bytearray:
    """Independent Eratosthenes reference: one means prime."""
    flags = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        flags[0] = 0
    if limit >= 1:
        flags[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            count = (limit - p * p) // p + 1
            flags[p * p : limit + 1 : p] = b"\x00" * count
    return flags


def frontier(b: int) -> int:
    return min(b * b, 3 * b + 4)


def exact_factorization(n: int) -> tuple[tuple[int, int], ...]:
    """Elementary independent trial division, valid also for n=1."""
    factors = []
    remaining = n
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor += 1
    if remaining > 1:
        factors.append((remaining, 1))
    return tuple(factors)


def odd_window_points(left: int, right: int) -> set[int]:
    return set(range(left, right + 1, 2))


def check_finite_worlds(max_b: int, primes: list[int]) -> dict:
    reference = reference_sieve(frontier(max_b))
    counters = {
        "worlds": 0,
        "odd_coordinates_compared": 0,
        "literal_product_pairs": 0,
        "windows": 0,
        "nonempty_shadow_traces": 0,
        "retained_shadow_traces": 0,
        "discarded_redundant_shadow_traces": 0,
        "saved_factor_witnesses": 0,
        "safe_cut_equalities": 0,
        "unsafe_cut_counterchecks": 0,
    }
    digest = hashlib.sha256()
    for b in range(3, max_b + 1, 2):
        odd_primes = [p for p in primes if 3 <= p <= b]
        # Literal definition, including the part above the safe frontier.
        shadows = {p: {p * m for m in range(3, b + 1, 2)}
                   for p in odd_primes}
        world = set().union(*shadows.values())
        right = frontier(b)
        expected = {n for n in range(3, right + 1, 2) if not reference[n]}
        covered = {n for n in world if 3 <= n <= right}
        require(covered == expected, f"S_B frontier mismatch at B={b}")
        counters["worlds"] += 1
        counters["odd_coordinates_compared"] += (right - 1) // 2
        counters["literal_product_pairs"] += len(odd_primes) * ((b - 1) // 2)
        digest.update(f"{b}:".encode("ascii"))
        digest.update(",".join(map(str, sorted(covered))).encode("ascii"))
        digest.update(b"\n")

        center = 3 + 2 * (((right - 1) // 2) // 2)
        windows = sorted({(3, right), (max(3, right - 28), right),
                          (max(3, center - 14), min(right, center + 14))})
        for left, end in windows:
            coordinates = odd_window_points(left, end)
            traces = [(p, shadow & coordinates) for p, shadow in shadows.items()]
            full = covered & coordinates
            retained_union: set[int] = set()
            first_witness: dict[int, int] = {}
            c: set[int] = set()
            u: set[int] = set()
            for index, (p, trace) in enumerate(traces):
                (c if index % 2 == 0 else u).update(trace)
                if not trace:
                    continue
                counters["nonempty_shadow_traces"] += 1
                novel = trace - retained_union
                if not novel:
                    counters["discarded_redundant_shadow_traces"] += 1
                    continue
                counters["retained_shadow_traces"] += 1
                retained_union.update(trace)
                for n in novel:
                    first_witness[n] = p

            require(retained_union == full, f"Shadow pruning lost coverage: {b,left,end}")
            require(set(first_witness) == full, "Witness addresses differ from coverage")
            for n, p in first_witness.items():
                m, remainder = divmod(n, p)
                require(remainder == 0 and 3 <= m <= b and m % 2 == 1,
                        f"Invalid finite-world factor witness: {n,p,b}")

            # Remove exactly the part of C also covered by U.
            reduced_c = c - u
            require(reduced_c | u == c | u == full, "Safe cut changed the union")
            counters["safe_cut_equalities"] += 1
            if reduced_c:
                private = min(reduced_c)
                require((reduced_c - {private}) | u != full,
                        "Removing a private address should change coverage")
                counters["unsafe_cut_counterchecks"] += 1
            counters["windows"] += 1
            counters["saved_factor_witnesses"] += len(first_witness)

    # Pointwise necessary-and-sufficient condition, all admissible Boolean cases.
    boolean_cases = 0
    for c in (0, 1):
        for reduced_c in (0, 1):
            if reduced_c > c:
                continue
            for u in (0, 1):
                require(((reduced_c | u) == (c | u)) ==
                        ((c - reduced_c) * (1 - u) == 0), "Boolean cut identity failed")
                boolean_cases += 1

    return {
        "status": "PASS",
        "scope": "Every odd B from 3 through max_B; literal S_B versus independent Eratosthenes.",
        "max_B": max_b,
        "safe_frontier": "G(B)=min(B^2,3B+4)",
        "window_scope": "Full safe odd interval, final 15 odd addresses, central up-to-15 odd addresses; duplicate windows removed.",
        "cut_identity": "For c_prime<=c: (c_prime OR u)=(c OR u) iff (c-c_prime)*(1-u)=0.",
        "boolean_cases": boolean_cases,
        "coverage_sha256": digest.hexdigest(),
        **counters,
    }


def check_prime_squares(primes: list[int]) -> dict:
    earlier: list[int] = []
    covered_earlier_multiples = 0
    for p in primes:
        require(all((p * p) % q for q in earlier), f"Earlier shadow covers {p}^2")
        # Multiples p*k with 2<=k<p precede p^2 in A_p={2p,3p,...}.
        for multiplier in range(2, p):
            n = p * multiplier
            require(any(n % q == 0 for q in earlier),
                    f"Earlier multiple lacks a smaller-prime shadow: {p,multiplier}")
            covered_earlier_multiples += 1
        earlier.append(p)
    return {
        "status": "PASS",
        "scope": "Every prime p through the requested world bound; shadows A_q={2q,3q,...}.",
        "primes": len(primes),
        "largest_prime": primes[-1],
        "earlier_multiples_checked": covered_earlier_multiples,
        "claim_checked": "p^2 is the first address of A_p not covered by smaller-prime shadows.",
    }


def exponent_world(basis: tuple[int, ...], bound: int) -> dict[int, tuple[int, ...]]:
    points: dict[int, tuple[int, ...]] = {}

    def visit(axis: int, value: int, vector: tuple[int, ...]) -> None:
        if axis == len(basis):
            require(value not in points, "Two exponent vectors projected to the same integer")
            points[value] = vector
            return
        exponent = 0
        while value <= bound:
            visit(axis + 1, value, vector + (exponent,))
            value *= basis[axis]
            exponent += 1

    if bound >= 1:
        visit(0, 1, ())
    return points


def check_factorization_and_layers(factor_limit: int) -> dict:
    prime_flags = reference_sieve(factor_limit)
    factorizations = {}
    seen_vectors = {}
    for n in range(1, factor_limit + 1):
        vector = exact_factorization(n)
        require(all(prime_flags[p] and exponent >= 1 for p, exponent in vector),
                f"Factorization contains a non-prime coordinate: {n,vector}")
        require(prod(p ** exponent for p, exponent in vector) == n,
                f"Factorization reconstruction failed: {n}")
        require(vector not in seen_vectors, "Factor vectors are not injective")
        factorizations[n] = vector
        seen_vectors[vector] = n

    basis_all = (2, 3, 5, 7, 11, 13)
    bounds = (1, 2, 3, 10, 31, 100, 301, 1000)
    world_cases = 0
    layer_cases = 0
    projected_points = 0
    for size in range(1, len(basis_all) + 1):
        basis = basis_all[:size]
        q = basis[-1]
        for bound in bounds:
            world = exponent_world(basis, bound)
            expected = {n for n in range(1, bound + 1)
                        if all(p in basis for p, _ in factorizations[n])}
            require(set(world) == expected, f"Exponent world mismatch: {basis,bound}")
            world_cases += 1
            q_power = 1
            exponent = 0
            combined = set()
            while q_power <= bound:
                layer = {n: v for n, v in world.items() if v[-1] == exponent}
                smaller = exponent_world(basis[:-1], bound // q_power)
                projected = {n // q_power: v[:-1] for n, v in layer.items()}
                require(all(n % q_power == 0 for n in layer), "Non-integral layer projection")
                require(projected == smaller, f"Layer projection failed: {basis,bound,exponent}")
                require(not combined.intersection(layer), "Fixed-exponent layers overlap")
                combined.update(layer)
                layer_cases += 1
                projected_points += len(layer)
                q_power *= q
                exponent += 1
            require(combined == set(world), "Layers do not partition the exponent world")

    return {
        "status": "PASS",
        "factorization_scope": f"All integers n from 1 through {factor_limit}; factors are checked against an independent sieve.",
        "factorizations": factor_limit,
        "geometric_model": "Finite nonnegative exponent vectors over a fixed prime basis; 1 is the all-zero vector.",
        "bases": [list(basis_all[:size]) for size in range(1, len(basis_all) + 1)],
        "bounds": list(bounds),
        "world_cases": world_cases,
        "layer_cases": layer_cases,
        "projected_points": projected_points,
        "layer_identity": "For last basis prime q and k>=0: {n/q^k: n is in the fixed-basis world up to X, exponent_q(n)=k} equals the smaller-basis world with bound floor(X/q^k).",
        "interpretation_scope": "Exact illustration of slices and projections; this exponent world is distinct from S_B.",
    }


def strong_mr_round(n: int, base: int) -> tuple[bool, list[int]]:
    require(n >= 3 and n % 2 == 1, "This demonstration requires an odd n>=3")
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(base, d, n)
    residues = [x]
    if x in (1, n - 1):
        return True, residues
    for _ in range(s - 1):
        x = x * x % n
        residues.append(x)
        if x == n - 1:
            return True, residues
    return False, residues


def check_2047() -> dict:
    n = 2047
    passes, residues = strong_mr_round(n, 2)
    factors = exact_factorization(n)
    require(n == 23 * 89, "Incorrect example factorization")
    require(passes and residues[0] == 1, "2047 did not pass base 2")
    require(factors == ((23, 1), (89, 1)), "Exact factor test failed")
    return {
        "status": "PASS",
        "n": n,
        "factorization": [[23, 1], [89, 1]],
        "mr_base": 2,
        "n_minus_one": "2*1023",
        "mr_residues": residues,
        "passes_single_mr_round": passes,
        "exact_composite_certificate": "2047=23*89",
        "scope": "A single-base strong pseudoprime example; this does not show failure of every multi-base or bounded deterministic Miller-Rabin variant.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-world", type=int, default=501)
    parser.add_argument("--factor-limit", type=int, default=10000)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "mathematics_checks.json")
    args = parser.parse_args()
    require(args.max_world >= 3 and args.max_world % 2 == 1,
            "--max-world must be an odd integer >=3")
    require(args.factor_limit >= 1000, "--factor-limit must be >=1000 for the layer cases")
    started = perf_counter()
    primes = trial_primes(args.max_world)
    results = {
        "schema_version": 1,
        "status": "PASS",
        "classification": "Exact finite mathematical verification; neither a general proof nor a speed benchmark.",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "finite_worlds_and_cuts": check_finite_worlds(args.max_world, primes),
        "first_private_prime_square": check_prime_squares(primes),
        "factorizations_and_layers": check_factorization_and_layers(args.factor_limit),
        "strong_pseudoprime_2047": check_2047(),
    }
    results["verification_wall_seconds"] = perf_counter() - started
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {results['finite_worlds_and_cuts']['worlds']} finite worlds, "
          f"{results['finite_worlds_and_cuts']['windows']} windows, "
          f"{results['factorizations_and_layers']['layer_cases']} layers; "
          f"{results['verification_wall_seconds']:.3f} s")
    print(args.output.resolve())
    return 0


if __name__ == "__main__":
    sys.exit(main())
