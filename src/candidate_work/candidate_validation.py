"""Independent validation of candidate-first maximum / zero-suffix answers.

This module is for post-timer verification and small correctness checks only.
The working backends must not import it or receive its oracle answers.  Its
bounded primality oracle is self-contained; no sieve bitmap, AP producer,
working trial loop, or backend state is trusted.

Required search answer::

    {"address": int | None,
     "closed_suffix": {"L": int, "R": int, "world_B": int,
                       "exact_hole_mass": 0, "empty_interval": bool}}

The total number of holes in the original window is OPTIONAL.  If ``exact_h``
is supplied as an integer, it is checked against the *whole* original window;
one returned maximum is never interpreted as a full-window count of one.

Optional factor witnesses use ``{"n": n, "d": d, "m": m}`` in ``witnesses``.
This is a complete suffix ledger unless suffix_witnesses_complete is False.
Optional ``max_cert`` describes the selected address.  A ``trial_limit`` claim
must reach floor(sqrt(address)); the independent primality check establishes
the mathematical result, not that an untrusted execution trace actually ran.
"""
from __future__ import annotations

from collections.abc import Mapping
from math import isqrt
import random
from typing import Any


DEFAULT_MAX_UNIQUE_TESTS = 100_000
DEFAULT_MAX_INTERVAL_ODD = 4_096
BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
U64_LIMIT = 1 << 64
ORACLE_SOURCE = "https://arxiv.org/pdf/1509.00864 (Sorenson & Webster, Theorem 1.1)"


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def _integer(value: Any, name: str) -> int:
    _require(type(value) is int, name + " must be an integer, not a boolean")
    return value


def _gate(B: int) -> int:
    return min(B * B, 3 * B + 4)


def prime_u64(n: int) -> bool:
    """Independent deterministic Miller--Rabin on 0 <= n < 2**64.

    Sorenson & Webster, Theorem 1.1, identify the least strong pseudoprime to
    these twelve bases as 318665857834031151167461, which exceeds 2**64.
    We intentionally reject the larger domain despite that published bound.
    Source: https://arxiv.org/pdf/1509.00864
    """
    if type(n) is not int:
        raise TypeError("Primality input must be an integer")
    if n >= U64_LIMIT:
        raise ValueError("Deterministic oracle requires n < 2**64")
    if n < 2:
        return False
    for p in BASES:
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for base in BASES:
        value = pow(base, d, n)
        if value in (1, n - 1):
            continue
        for _ in range(s - 1):
            value = value * value % n
            if value == n - 1:
                break
        else:
            return False
    return True


class _IndependentOracle:
    def __init__(self, max_interval_odd: int, max_unique_tests: int):
        self.max_interval_odd = max_interval_odd
        self.max_unique_tests = max_unique_tests
        self.values: dict[int, bool] = {}
        self.cache_hits = 0
        self.intervals = 0
        self.requested_odd_cells = 0

    def is_prime(self, n: int) -> bool:
        if n in self.values:
            self.cache_hits += 1
            return self.values[n]
        _require(len(self.values) < self.max_unique_tests, "Oracle unique-test budget exceeded")
        answer = prime_u64(n)
        self.values[n] = answer
        return answer

    def holes(self, L: int, R: int) -> list[int]:
        _require(type(L) is int and type(R) is int and L >= 3 and L % 2 and R % 2,
                 "Oracle expects odd interval endpoints >= 3")
        _require(R < U64_LIMIT, "Oracle interval is outside uint64")
        if L > R:
            return []
        cells = (R - L) // 2 + 1
        _require(cells <= self.max_interval_odd, "Oracle interval budget exceeded")
        self.intervals += 1
        self.requested_odd_cells += cells
        return [n for n in range(L, R + 1, 2) if self.is_prime(n)]

    def snapshot(self) -> dict:
        return dict(method="deterministic Miller-Rabin; first 12 prime bases",
                    bases=list(BASES), proven_domain="n < 2**64", source=ORACLE_SOURCE,
                    unique_primality_tests=len(self.values), cache_hits=self.cache_hits,
                    checked_intervals=self.intervals, requested_odd_cells=self.requested_odd_cells,
                    maximum_tested=max(self.values, default=0),
                    allocated_prefix_bitmap=False, complete_prime_prefix_built=False,
                    max_interval_odd=self.max_interval_odd, max_unique_tests=self.max_unique_tests)


class _Validation:
    def __init__(self, *, max_interval_odd: int = DEFAULT_MAX_INTERVAL_ODD,
                 max_unique_tests: int = DEFAULT_MAX_UNIQUE_TESTS):
        _require(type(max_interval_odd) is int and max_interval_odd >= 1,
                 "Positive oracle interval budget required")
        _require(type(max_unique_tests) is int and max_unique_tests >= 1,
                 "Positive oracle unique-test budget required")
        self.oracle = _IndependentOracle(max_interval_odd, max_unique_tests)
        self.checked_windows = 0
        self.windows_without_holes = 0
        self.full_count_claims_checked = 0
        self.factor_witnesses_checked = 0
        self.maximum_certificates_checked = 0
        self.trial_limit_claims_checked = 0

    def _holes(self, L: int, R: int) -> list[int]:
        # Chunking permits a suffix assembled from many short windows without
        # relaxing the oracle's per-interval or total unique-coordinate budget.
        if L > R:
            return []
        result = []
        width = 2 * self.oracle.max_interval_odd
        for left in range(L, R + 1, width):
            result.extend(self.oracle.holes(left, min(R, left + width - 2)))
        return result

    def _suffix(self, B: int, expected_L: int, expected_R: int,
                suffix: Any, *, check_parts: bool = True) -> None:
        _require(isinstance(suffix, Mapping), "Missing structured closed suffix")
        for key, value in (("L", expected_L), ("R", expected_R), ("world_B", B),
                           ("exact_hole_mass", 0)):
            _integer(suffix.get(key), "closed_suffix." + key)
            _require(suffix[key] == value, "Incorrect closed_suffix." + key)
        _require(type(suffix.get("empty_interval")) is bool,
                 "closed_suffix.empty_interval must be a boolean")
        _require(suffix["empty_interval"] == (expected_L > expected_R),
                 "Incorrect closed_suffix.empty_interval")
        _require(not self._holes(expected_L, expected_R),
                 "A claimed zero-hole suffix contains a prime")
        if check_parts and "parts" in suffix:
            parts = suffix["parts"]
            _require(isinstance(parts, list), "Suffix parts must be a list")
            cursor = expected_L
            for part in parts:
                _require(isinstance(part, Mapping), "Malformed suffix part")
                left = _integer(part.get("L"), "suffix part L")
                right = _integer(part.get("R"), "suffix part R")
                _require(left >= 3 and left % 2 and right >= 1 and right % 2,
                         "Suffix part endpoints must be odd")
                self._suffix(B, left, right, part, check_parts=False)
                if left > right:
                    _require(left == right + 2 and expected_L <= left <= expected_R + 2,
                             "Empty suffix part lies outside the certificate")
                    continue
                _require(left == cursor and right <= expected_R,
                         "Suffix parts have a gap, overlap, or excessive endpoint")
                cursor = right + 2
            _require(cursor == expected_R + 2,
                     "Suffix parts do not cover the entire closed suffix")

    def _factors(self, B: int, L: int, R: int, address: int | None,
                 answer: Mapping) -> None:
        witnesses = answer.get("witnesses")
        if witnesses is None:
            return
        _require(isinstance(witnesses, list), "Factor witnesses must be a list")
        seen = set()
        for witness in witnesses:
            _require(isinstance(witness, Mapping), "Factor witness must be a mapping")
            n = _integer(witness.get("n"), "witness n")
            d = _integer(witness.get("d"), "witness d")
            m = _integer(witness.get("m"), "witness m")
            _require(L <= n <= R and n % 2, "Witness address lies outside its odd window")
            _require(3 <= d <= B and 3 <= m <= B and d % 2 and m % 2,
                     "Witness factors do not belong to the finite world")
            _require(d * m == n, "Incorrect factor-pair multiplication")
            _require(n != address, "A composite witness contradicts the selected hole")
            _require(not self.oracle.is_prime(n), "Composite witness names an oracle prime")
            seen.add(n)
            self.factor_witnesses_checked += 1
        # Presence of this list means a suffix certificate in the candidate
        # API.  Partial diagnostic witness lists must say so explicitly.
        complete = answer.get("suffix_witnesses_complete", True)
        _require(type(complete) is bool, "suffix_witnesses_complete must be a boolean")
        if complete:
            suffix_L = L if address is None else address + 2
            _require(seen == set(range(suffix_L, R + 1, 2)),
                     "Claimed complete suffix factor ledger is incomplete or has extra points")

    def _maximum_certificate(self, address: int | None, answer: Mapping) -> None:
        cert = answer.get("max_cert")
        if cert is None:
            return
        _require(address is not None and isinstance(cert, Mapping),
                 "Maximum certificate requires a selected address")
        for key in ("n", "address"):
            if key in cert:
                _integer(cert[key], "max_cert." + key)
                _require(cert[key] == address, "Maximum certificate names a different address")
        if cert.get("method") == "trial_division":
            _require("trial_limit" in cert, "Trial-division certificate is missing trial_limit")
        if "trial_limit" in cert:
            limit = _integer(cert["trial_limit"], "max_cert.trial_limit")
            _require(limit >= isqrt(address),
                     "Claimed trial certificate stops before floor(sqrt(address))")
            self.trial_limit_claims_checked += 1
        self.maximum_certificates_checked += 1

    def search(self, B: int, L: int, R: int, answer: Any) -> None:
        B, L, R = (_integer(B, "B"), _integer(L, "L"), _integer(R, "R"))
        _require(B >= 3 and B % 2 and 3 <= L <= R and L % 2 and R % 2,
                 "Expected odd B >= 3 and odd endpoints 3 <= L <= R")
        _require(R <= _gate(B), "Window leaves the stable finite-world frontier")
        _require(R < U64_LIMIT, "Window exceeds the independent oracle's domain")
        _require(isinstance(answer, Mapping) and "address" in answer,
                 "Search answer must contain address (including explicit None)")
        address = answer["address"]
        _require(address is None or type(address) is int,
                 "Address must be an integer or explicit None")
        expected = self._holes(L, R)
        _require(address == (expected[-1] if expected else None),
                 "Search answer is not the true rightmost hole")
        # A present exact count is a claim about [L,R], never just [address,R].
        for key in ("exact_h", "exact_hole_count"):
            if key in answer and answer[key] is not None:
                _integer(answer[key], key)
                _require(answer[key] == len(expected),
                         key + " is not the full original-window count")
                self.full_count_claims_checked += 1
        suffix_L = L if address is None else address + 2
        self._suffix(B, suffix_L, R, answer.get("closed_suffix"))
        self._factors(B, L, R, address, answer)
        self._maximum_certificate(address, answer)
        self.checked_windows += 1
        self.windows_without_holes += address is None

    def snapshot(self) -> dict:
        return {
            "status": "PASS",
            "contract": "rightmost hole and exact zero-hole suffix; full-window count optional",
            "oracle_role": "independent validation only; never a working search input",
            "checked_windows": self.checked_windows,
            "windows_without_holes": self.windows_without_holes,
            "full_window_count_claims_checked": self.full_count_claims_checked,
            "factor_witnesses_checked": self.factor_witnesses_checked,
            "maximum_certificates_checked": self.maximum_certificates_checked,
            "trial_limit_claims_checked": self.trial_limit_claims_checked,
            "execution_trace_attested": False,
            "oracle": self.oracle.snapshot(),
        }


def validate_search(B: int, L: int, R: int, answer: Mapping, **limits) -> dict:
    """Check one completed search without exposing expected addresses."""
    validation = _Validation(**limits)
    validation.search(B, L, R, answer)
    return validation.snapshot()


def validate_route(result: Mapping, flashes: int | None = None, **limits) -> dict:
    """Validate a cold online route and every answer, after its timer stops.

    Required result keys are anchors, windows and steps.  Required step keys:
    B, R, last_hole, search_lower_bound, previous_closed_R and closed_suffix.
    Windows are flat records with B, L, R and the search-answer fields.
    """
    _require(isinstance(result, Mapping), "Route result must be a mapping")
    if "status" in result:
        _require(result["status"] == "PASS", "Measured route did not finish successfully")
    anchors, windows, steps = (result.get("anchors"), result.get("windows"), result.get("steps"))
    _require(isinstance(anchors, list) and isinstance(windows, list) and isinstance(steps, list),
             "Route must contain anchors, windows and steps lists")
    if flashes is not None:
        _require(type(flashes) is int and flashes >= 0 and len(steps) == flashes,
                 "Unexpected completed flash count")
    validation = _Validation(**limits)
    B, previous_R, cursor = 3, None, 0
    expected_anchors = [B]
    for index, step in enumerate(steps, 1):
        _require(isinstance(step, Mapping), "Malformed step record")
        upper = _gate(B)
        lower = max(B + 2, previous_R + 2 if previous_R is not None else B + 2)
        expected_step = {"B": B, "R": upper, "search_lower_bound": lower,
                         "previous_closed_R": previous_R}
        for key, value in expected_step.items():
            _require(key in step and step[key] == value, "Incorrect online step field: " + key)
        if "flash_index" in step:
            _require(step["flash_index"] == index, "Wrong flash index")
        right, found, indices = upper, None, []
        while right >= lower:
            _require(cursor < len(windows), "Missing search window before an advancing hole")
            window = windows[cursor]
            _require(isinstance(window, Mapping), "Malformed window record")
            expected_window = {"B": B, "L": max(lower, right - 28), "R": right}
            for key, value in expected_window.items():
                _require(window.get(key) == value, "Incorrect online window policy: " + key)
            if "flash_index" in window:
                _require(window["flash_index"] == index, "Wrong window flash index")
            validation.search(B, window["L"], window["R"], window)
            indices.append(cursor)
            cursor += 1
            found = window["address"]
            if found is not None:
                break
            right = window["L"] - 2
        _require(found is not None and found > B, "Flash has no certified advancing maximum")
        _require(step.get("last_hole") == found, "Step maximum differs from its query")
        if "next_B" in step:
            _require(step["next_B"] == found, "Incorrect next anchor")
        if "main_windows" in step:
            _require(step["main_windows"] == len(indices), "Incorrect step window count")
        if "main_query_indices" in step:
            _require(step["main_query_indices"] == indices, "Incorrect ordered window ledger")
        if "window_indices" in step:
            _require(step["window_indices"] == indices, "Incorrect ordered window ledger")
        validation._suffix(B, found + 2, upper, step.get("closed_suffix"))
        expected_anchors.append(found)
        previous_R, B = upper, found
    _require(cursor == len(windows), "Extra, unassigned, or post-maximum windows remain")
    _require(all(type(n) is int for n in anchors) and anchors == expected_anchors,
             "Anchor sequence differs from the independently validated route")
    for key in ("requested_flashes", "completed_flashes"):
        if key in result:
            _require(result[key] == len(steps), "Incorrect route field: " + key)
    if "initial_B" in result:
        _require(result["initial_B"] == 3, "Cold route did not start at seed 3")
    if "final_state" in result:
        for key, value in (("B", B), ("previous_R", previous_R)):
            _require(result["final_state"].get(key) == value, "Incorrect final state: " + key)
    if "full_window_count_required" in result:
        _require(result["full_window_count_required"] is False,
                 "Route still requires the obsolete full-window count contract")
    if "independent_validator_used_by_working_algorithm" in result:
        _require(result["independent_validator_used_by_working_algorithm"] is False,
                 "Working algorithm admits using the independent validator")
    return {**validation.snapshot(), "checked_flashes": len(steps),
            "checked_anchor_count": len(anchors), "final_anchor": B,
            "maximum_queried_coordinate": max((w["R"] for w in windows), default=3)}


def normalized_contract(result: Mapping) -> dict:
    """Comparable output only: no optional full counts or method diagnostics."""
    suffix_keys = ("L", "R", "world_B", "exact_hole_mass", "empty_interval")
    return {
        "anchors": list(result["anchors"]),
        "windows": [
            {**{key: row[key] for key in ("B", "L", "R", "address")},
             "closed_suffix": {key: row["closed_suffix"][key] for key in suffix_keys}}
            for row in result["windows"]
        ],
        "steps": [
            {**{key: row[key] for key in ("B", "R", "last_hole", "search_lower_bound",
                                         "previous_closed_R")},
             "closed_suffix": {key: row["closed_suffix"][key] for key in suffix_keys}}
            for row in result["steps"]
        ],
    }


def boundary_cases(*, random_cases: int = 64, seed: int = 20261010) -> list[tuple[int, int, int]]:
    """Small deterministic API cases: no-hole runs, squares, frontiers, reuse.

    Composite odd B values are deliberate: the stable finite-world identity
    needs an odd boundary, while only the online anchor sequence needs prime B.
    All windows have at most 15 odd cells.  This does not benchmark an engine.
    """
    _require(type(random_cases) is int and 0 <= random_cases <= 10_000,
             "Invalid small-check case budget")
    cases = [
        (3, 3, 3), (3, 5, 9), (3, 7, 7), (3, 9, 9),
        (5, 3, 19), (5, 15, 15), (5, 19, 19),
        (7, 9, 25), (7, 25, 25), (9, 27, 31),
        (11, 33, 37), (13, 39, 39), (13, 39, 43),
        (17, 49, 49), (31, 89, 97), (31, 91, 95),
        (35, 105, 109), (39, 115, 121), (39, 121, 121),
        (77, 225, 231), (113, 341, 341), (187, 561, 561),
        (369, 1105, 1105), (3815, 11449, 11449),
    ]
    rng = random.Random(seed)
    for _ in range(random_cases):
        B = rng.randrange(3, 1002, 2)
        upper = _gate(B)
        right = 3 + 2 * rng.randrange((upper - 3) // 2 + 1)
        length = rng.randint(1, min(15, (right - 3) // 2 + 1))
        cases.append((B, right - 2 * (length - 1), right))
    return cases


def run_backend_checks(backend_or_factory: Any, *, random_cases: int = 64,
                       seed: int = 20261010, **limits) -> dict:
    """Exercise a separate untimed instance, including repeated/decreasing inputs.

    Pass a zero-argument factory for clean isolation.  Passing an existing
    backend is allowed but changes its state, so never pass a timed instance.
    A created backend is closed on exit if it exposes close().
    """
    created = isinstance(backend_or_factory, type) or not hasattr(backend_or_factory, "search")
    backend = backend_or_factory() if created else backend_or_factory
    _require(callable(getattr(backend, "search", None)), "Backend needs search(B,L,R)")
    validation = _Validation(**limits)
    cases = boundary_cases(random_cases=random_cases, seed=seed)
    replay = list(reversed(cases[:12]))
    try:
        for B, L, R in cases + replay:
            answer = backend.search(B, L, R)
            validation.search(B, L, R, answer)
    finally:
        if created and callable(getattr(backend, "close", None)):
            backend.close()
    return {**validation.snapshot(), "test_kind": "small untimed backend API checks",
            "directed_cases": 24, "random_cases": random_cases,
            "repeated_decreasing_cases": len(replay), "random_seed": seed,
            "largest_tested_B": max(B for B, _, _ in cases),
            "largest_tested_R": max(R for _, _, R in cases)}


__all__ = ["validate_search", "validate_route", "normalized_contract",
           "boundary_cases", "run_backend_checks"]
