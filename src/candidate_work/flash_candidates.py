"""Candidate-first flash route: rightmost address and a closed suffix only.

The hot route retains explicit addresses, factor witnesses and earned basis
state.  It never asks for the number of holes to the left of its maximum.
The working candidate engines use exact integer division, not the independent
Miller--Rabin validator.  No article or formal proof is part of this module.

Examples:
    python flash_candidates.py --mode candidate_wheel --flashes 28
    python flash_candidates.py --mode candidate_prime --flashes 28 --profile

The legacy_periods adapter is an optional ablation and requires the adjacent
frozen direct_access_work directory.  All other modes need only this file and
candidate_sieves.py.  A FlashRunner can continue with its resident backend;
its answers, addresses and small basis remain available without reconstruction.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from itertools import islice
import json
from math import isqrt
from pathlib import Path
import sys
import time

from candidate_sieves import (
    SmallPrimeBasis, CandidateSegmentedSieve, CandidateFullSieve,
    CandidateIncrementalSieve, _answer, _check_window,
)


def gate(B):
    return min(B * B, 3 * B + 4)


class CandidateBase:
    """Address-first search; completed facts are retained as native values."""
    name = "candidate_base"
    period_family = "unspecified"

    def __init__(self, profile=False):
        self.profile = profile
        self.facts = {}  # n -> first factor, or None for a certified hole.
        self.queries = self.candidates = self.rejected = self.accepted = 0
        self.address_cache_hits = self.modulus_tests = 0
        self.basis_seconds = 0.0
        self.maximum_trial_limit = 0

    def search(self, B, L, R):
        _check_window(B, L, R)
        self.queries += 1
        witnesses = []
        address = None
        max_cert = None
        for n in range(R, L - 1, -2):
            self.candidates += 1
            limit = isqrt(n)
            if n in self.facts:
                self.address_cache_hits += 1
                factor = self.facts[n]
                cached = True
            else:
                factor = self._test(n, limit)
                self.facts[n] = factor
                self.maximum_trial_limit = max(self.maximum_trial_limit, limit)
                cached = False
            if factor is not None:
                self.rejected += 1
                witnesses.append(dict(n=n, d=factor, m=n // factor,
                                      saved_fact_reused=cached))
                continue
            self.accepted += 1
            address = n
            max_cert = dict(method="trial_division", trial_limit=limit,
                            period_family=self.period_family,
                            saved_fact_reused=cached)
            break
        result = _answer(address, B, L, R,
                         "one retained factor witness for each rejected address")
        result.update(witnesses=witnesses, max_cert=max_cert)
        return result

    def snapshot(self):
        result = dict(
            engine=self.name, diagnostics_enabled=self.profile,
            queries=self.queries, candidates_visited=self.candidates,
            composite_candidates=self.rejected, accepted_candidates=self.accepted,
            retained_address_facts=len(self.facts),
            retained_shadow_periods=len({d for d in self.facts.values() if d is not None}),
            address_cache_hits=self.address_cache_hits,
            full_window_hole_counts=0, hole_address_reconstructions=0,
            AP_unions=0, CRT_intersections=0, moments=0,
            maximum_trial_limit=self.maximum_trial_limit,
            modulus_tests=self.modulus_tests if self.profile else None,
            basis_seconds=self.basis_seconds if self.profile else None,
            working_external_primality_test_calls=0,
        )
        if hasattr(self, "base"):
            result["base"] = self.base.snapshot()
        return result


class CandidateOdd(CandidateBase):
    name = "candidate_odd_division"
    period_family = "all odd divisors through isqrt(n), first shadow stops"

    def _test(self, n, limit):
        factor = None
        for d in range(3, limit + 1, 2):
            if n % d == 0:
                factor = d
                break
        if self.profile:
            self.modulus_tests += max(0, ((factor or limit) - 1) // 2)
        return factor


WHEEL_RESIDUES = (7, 11, 13, 17, 19, 23, 29, 31)


class CandidateWheel(CandidateBase):
    name = "candidate_wheel30_division"
    period_family = "3,5 then residues coprime to30 through isqrt(n)"

    def _test(self, n, limit):
        small_tests = 0
        for p in (3, 5):
            if p > limit:
                if self.profile:
                    self.modulus_tests += small_tests
                return None
            small_tests += 1
            if n % p == 0:
                if self.profile:
                    self.modulus_tests += small_tests
                return p
        d, factor = 7, None
        # Unrolled ordered residues avoid a Python generator per divisor.
        while d + 24 <= limit:
            if n % d == 0:
                factor = d
                break
            if n % (d + 4) == 0:
                factor = d + 4
                break
            if n % (d + 6) == 0:
                factor = d + 6
                break
            if n % (d + 10) == 0:
                factor = d + 10
                break
            if n % (d + 12) == 0:
                factor = d + 12
                break
            if n % (d + 16) == 0:
                factor = d + 16
                break
            if n % (d + 22) == 0:
                factor = d + 22
                break
            if n % (d + 24) == 0:
                factor = d + 24
                break
            d += 30
        if factor is None:
            for offset in (0, 4, 6, 10, 12, 16, 22, 24):
                p = d + offset
                if p > limit:
                    break
                if n % p == 0:
                    factor = p
                    break
        if self.profile:
            end = factor or limit
            self.modulus_tests += small_tests + sum(
                max(0, (end - r) // 30 + 1) for r in WHEEL_RESIDUES)
        return factor


class CandidatePrime(CandidateBase):
    name = "candidate_retained_prime_basis"
    period_family = "3,5 then complete retained odd-prime basis through isqrt(n)"

    def __init__(self, profile=False):
        super().__init__(profile)
        self.base = SmallPrimeBasis(diagnostics=profile)

    def _test(self, n, limit):
        small_tests = 0
        for p in (3, 5):
            if p > limit:
                if self.profile:
                    self.modulus_tests += small_tests
                return None
            small_tests += 1
            if n % p == 0:
                if self.profile:
                    self.modulus_tests += small_tests
                return p
        # Only a surviving candidate requests basis expansion.  The same
        # SmallPrimeBasis implementation is used and paid for by segmentation.
        if self.profile:
            t0 = time.perf_counter()
        primes, stop = self.base.prepare(limit)
        if self.profile:
            self.basis_seconds += time.perf_counter() - t0
        start = bisect_right(primes, 5, 0, stop)
        factor = None
        for p in islice(primes, start, stop):
            if n % p == 0:
                factor = p
                break
        if self.profile:
            end = stop if factor is None else bisect_right(primes, factor, start, stop)
            self.modulus_tests += small_tests + end - start
        return factor


class LegacyPeriods:
    """Frozen coverage-first producer under the new caller, for ablation."""
    name = "legacy_full_AP_period_coverage"

    def __init__(self, profile=False):
        frozen = Path(__file__).resolve().parent.parent / "direct_access_work"
        if not frozen.is_dir():
            raise RuntimeError("legacy_periods requires adjacent direct_access_work")
        sys.path.insert(0, str(frozen))
        from flash_active_periods import prepare_fresh_window
        from flash_exact import ExactAPCounter
        self.prepare = prepare_fresh_window
        self.counter_class = ExactAPCounter
        self.work = {}
        self.queries = 0

    def search(self, B, L, R):
        _check_window(B, L, R)
        prepared = self.prepare(B, L, R)
        self.queries += 1
        for key, value in prepared["producer_work"].items():
            self.work[key] = self.work.get(key, 0) + value
        counter = self.counter_class(prepared["hole_terms"], L, R, world_B=B)
        selected = counter.rightmost()
        return dict(address=selected["address"],
                    closed_suffix=selected["closed_suffix"])

    def snapshot(self):
        return dict(engine=self.name, queries=self.queries, producer_activity=self.work,
                    full_window_hole_counts=self.queries,
                    legacy_internal_operation_counters_always_enabled=True)


MODES = ("candidate_odd", "candidate_wheel", "candidate_prime", "segmented",
         "full", "incremental", "legacy_periods")


def make_backend(mode, profile=False):
    if mode == "candidate_odd":
        return CandidateOdd(profile)
    if mode == "candidate_wheel":
        return CandidateWheel(profile)
    if mode == "candidate_prime":
        return CandidatePrime(profile)
    if mode == "segmented":
        return CandidateSegmentedSieve(diagnostics=profile)
    if mode == "full":
        return CandidateFullSieve(diagnostics=profile)
    if mode == "incremental":
        return CandidateIncrementalSieve(diagnostics=profile)
    if mode == "legacy_periods":
        return LegacyPeriods(profile)
    raise ValueError("Unknown mode: " + str(mode))


class FlashRunner:
    """Small resident state with direct facts; no universal query/counter layer."""

    def __init__(self, backend):
        self.backend = backend
        self.B = 3
        self.previous_R = None
        self.anchors = [3]
        self.windows = []
        self.steps = []
        self.answers = {}
        self.exact_answer_cache_hits = 0

    def run(self, flashes):
        if type(flashes) is not int or flashes < 0:
            raise ValueError("flashes must be a nonnegative integer")
        for _ in range(flashes):
            B, previous_R = self.B, self.previous_R
            upper = gate(B)
            lower = max(B + 2, previous_R + 2 if previous_R is not None else B + 2)
            right = upper
            suffix_parts = []
            indices = []
            while right >= lower:
                left = max(lower, right - 28)
                key = B, left, right
                answer = self.answers.get(key)
                if answer is None:
                    answer = self.backend.search(B, left, right)
                    self.answers[key] = answer
                else:
                    self.exact_answer_cache_hits += 1
                idx = len(self.windows)
                self.windows.append(dict(B=B, L=left, R=right,
                                         flash_index=len(self.steps) + 1, **answer))
                indices.append(idx)
                suffix_parts.append(answer["closed_suffix"])
                address = answer["address"]
                if address is not None:
                    break
                right = left - 2
            else:
                raise ArithmeticError("No advancing hole within the search frontier")
            if not B < address <= upper:
                raise ArithmeticError("Non-advancing flash result")
            closed = dict(L=address + 2, R=upper, world_B=B,
                          exact_hole_mass=0, empty_interval=address + 2 > upper,
                          witness="retained candidate or sieve suffix certificates",
                          parts=list(reversed(suffix_parts)))
            self.steps.append(dict(B=B, R=upper, last_hole=address,
                                   flash_index=len(self.steps) + 1,
                                   search_lower_bound=lower, previous_closed_R=previous_R,
                                   window_indices=indices, closed_suffix=closed))
            self.B, self.previous_R = address, upper
            self.anchors.append(address)
        return self.result()

    def result(self):
        return dict(status="PASS", contract="maximum_and_closed_suffix_only",
                    completed_flashes=len(self.steps), anchors=list(self.anchors),
                    windows=list(self.windows), steps=list(self.steps),
                    final_state=dict(B=self.B, previous_R=self.previous_R),
                    direct_facts=dict(retained_answers=len(self.answers),
                                      exact_answer_cache_hits=self.exact_answer_cache_hits),
                    full_window_count_required=False,
                    independent_validator_used_by_working_algorithm=False)


def run_route(backend, flashes=12):
    return FlashRunner(backend).run(flashes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=MODES, default="candidate_wheel")
    parser.add_argument("--flashes", type=int, default=20)
    parser.add_argument("--profile", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    t0 = time.perf_counter()
    backend = make_backend(args.mode, profile=args.profile)
    result = run_route(backend, args.flashes)
    elapsed = time.perf_counter() - t0
    result.update(mode=args.mode, elapsed_seconds=elapsed, backend=backend.snapshot())
    # Validation is a separate, optional import after completion and timer stop.
    from candidate_validation import validate_route
    result["validation"] = validate_route(result)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
        print(json.dumps(dict(status=result["status"], mode=args.mode,
                              flashes=args.flashes, anchor=result["anchors"][-1],
                              elapsed_seconds=elapsed, output=str(args.output)),
                         ensure_ascii=False))
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
