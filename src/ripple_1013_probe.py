"""Three exact constructed windows showing local absorption and return of 1013.

These increasing prime worlds are not claimed to be consecutive flashes.
Only the trace of axis 1013 is classified; all its addresses are fully factored.
    python src/ripple_1013_probe.py
    python src/ripple_1013_probe.py --output data/ripple_1013_rerun.json
Python standard library only. Existing output files are never overwritten.
"""
from datetime import datetime, timezone
from math import isqrt, prod
from pathlib import Path
from time import perf_counter
import argparse
import json


def is_prime_exact(number):
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    return all(number % divisor for divisor in range(3, isqrt(number) + 1, 2))


def factor_exact(number):
    remaining = number
    divisor = 3
    factors = []
    assert number % 2 == 1
    while divisor * divisor <= remaining:
        power = 0
        while remaining % divisor == 0:
            remaining //= divisor
            power += 1
        if power:
            factors.append((divisor, power))
        divisor += 2
    if remaining > 1:
        factors.append((remaining, 1))
    assert prod(prime ** power for prime, power in factors) == number
    assert all(is_prime_exact(prime) for prime, _ in factors)
    return factors


def window_example(world_bound, prime=1013):
    assert is_prime_exact(world_bound) and is_prime_exact(prime)
    right = min(world_bound * world_bound, 3 * world_bound + 4)
    left = max(3, right - 28)
    traces = []
    for number in range(left, right + 1, 2):
        if number % prime or not (prime <= world_bound and 3 <= number // prime <= world_bound):
            continue
        factors = factor_exact(number)
        axes = [axis for axis, _ in factors
                if axis <= world_bound and 3 <= number // axis <= world_bound]
        assert axes == [axis for axis, _ in factors]
        later = [axis for axis in axes if axis > prime]
        traces.append(dict(n=number, factorization=[list(pair) for pair in factors],
                           admissible_axes=axes, larger_covering_axes=later,
                           remains_after_all_larger_axes=not later))
    residual = [row["n"] for row in traces if row["remains_after_all_larger_axes"]]
    state = "active" if residual else "absorbed_by_larger_axes" if traces else "no_shadow_in_window"
    assert right-left < 2*prime and len(traces) <= 1
    return dict(B=world_bound, B_primality_verified=True, L=left, R=right,
                prime_axis=prime, state=state, shadow_nonempty=bool(traces),
                traces=traces, residual_addresses=residual)


def run():
    started = perf_counter()
    examples = [window_example(bound) for bound in (1013, 344083, 1710287)]
    assert [row["state"] for row in examples] == ["active", "absorbed_by_larger_axes", "active"]
    assert examples[0]["residual_addresses"] == [3039]
    assert examples[1]["traces"][0]["factorization"] == [[1013, 1], [1019, 1]]
    assert examples[2]["residual_addresses"] == [5130845]
    assert examples[2]["traces"][0]["factorization"] == [[5, 1], [1013, 2]]
    return dict(
        status="PASS", generated_at_utc=datetime.now(timezone.utc).isoformat(),
        classification="Constructed exact examples, not a statistical sample or speed benchmark.",
        examples=examples,
        identity="The residual of T_1013 after all larger prime axes is precisely the composite addresses with largest prime factor 1013 in the safe window.",
        consequence="Absorption of a nonempty trace in one window does not justify permanently deleting the old prime axis from every later world.",
        limitations=[
            "The three selected prime worlds are not claimed to form consecutive flashes or the canonical route starting at 3.",
            "Every address in T_1013 is factored exactly; the other window addresses are not classified by this demonstration.",
            "These examples do not provide an efficient search algorithm for residual addresses near the record prime.",
            "No-shadow-in-window and absorption-of-a-nonempty-shadow are separate states."
        ],
        total_computation_seconds_excluding_serialization=perf_counter()-started)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    contents = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as stream:
            stream.write(contents)
        print(json.dumps(dict(output=str(args.output.resolve()), status=result["status"],
                              seconds=result["total_computation_seconds_excluding_serialization"])))
    else:
        print(contents, end="")


if __name__ == "__main__":
    main()
