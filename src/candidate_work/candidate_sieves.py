"""Exact sieve baselines for a rightmost-hole / closed-suffix contract.

No engine counts all holes or materializes all window prime addresses.  The
finite-world caller supplies B and an odd window inside min(B*B, 3*B+4), where
odd-prime positions are exactly the world's holes.  Every cold instance pays
for its own required prime basis, beginning with the seed 3.

SmallPrimeBasis.prepare(limit) returns (owned_list, stop_index).  Callers must
not mutate that list; itertools.islice(list, stop_index) visits only the needed
prefix without copying a potentially large list of prime addresses.  Basis
extension is distinct from searching a distant window and reuses all existing
flags and prime addresses.

Diagnostic operation counters are optional.  Production loops contain no
per-divisor dictionary updates and choose instrumented or plain loops once.
Payload counters describe bytearrays, not total process RSS.
"""
from __future__ import annotations

from bisect import bisect_right
from itertools import islice
from math import isqrt


DEFAULT_MAX_BITMAP_BYTES = 256 * 1024 * 1024


def _odd_floor(limit: int) -> int:
    return limit - (limit % 2 == 0)


def _check_window(B: int, L: int, R: int) -> None:
    if not (isinstance(B, int) and isinstance(L, int) and isinstance(R, int)
            and B >= 3 and B % 2 and 3 <= L <= R and L % 2 and R % 2):
        raise ValueError("Expected odd B >= 3 and odd endpoints 3 <= L <= R")
    if R > min(B * B, 3 * B + 4):
        raise ValueError("Window exceeds the exact finite-world frontier")


def _answer(address: int | None, B: int, L: int, R: int, witness: str) -> dict:
    suffix_left = L if address is None else address + 2
    return {
        "address": address,
        "closed_suffix": {
            "L": suffix_left, "R": R, "world_B": B,
            "exact_hole_mass": 0, "empty_interval": suffix_left > R,
            "witness": witness,
        },
    }


def append_prime_addresses_scan(primes: list[int], flags: bytearray,
                                previous_limit: int, limit: int) -> None:
    """Materialize a new certified prefix by inspecting each odd bitmap cell."""
    primes.extend([p for p in range(previous_limit + 2, limit + 1, 2)
                   if flags[(p - 3) // 2]])


def append_prime_addresses_find(primes: list[int], flags: bytearray,
                                previous_limit: int, limit: int) -> None:
    """Append only positions of set bits; scan intervening zeroes inside C.

    The owned bitmap and previously retained address list are never sliced or
    copied.  In particular, this variant needs no temporary list of new primes.
    The endpoints must be odd and flags must already be certified through limit.
    """
    find = flags.find
    append = primes.append
    stop = (limit - 3) // 2 + 1
    index = find(b"\x01", (previous_limit - 3) // 2 + 1, stop)
    while index >= 0:
        append(2 * index + 3)
        index = find(b"\x01", index + 1, stop)


class SmallPrimeBasis:
    """Incrementally certified odd bitmap and lazily materialized prime list.

    ensure(limit) pays only for the bitmap and the smaller marking basis.
    prepare(limit) also materializes prime addresses through the needed limit.
    Neither method copies previously retained flags or prime addresses.
    """

    def __init__(self, diagnostics: bool = False,
                 max_bitmap_bytes: int | None = DEFAULT_MAX_BITMAP_BYTES,
                 materialization: str = "find"):
        if materialization not in ("scan", "find"):
            raise ValueError("materialization must be 'scan' or 'find'")
        self.diagnostics = diagnostics
        self.max_bitmap_bytes = max_bitmap_bytes
        self.materialization = materialization
        self.limit = 3
        self.flags = bytearray(b"\x01")
        self.primes = [3]
        self.prime_list_limit = 3
        self.extensions = 0
        self.prime_materializations = 0
        self.base_flag_positions_inspected = 0
        self.base_flag_positions_considered = 0
        self.base_flag_find_calls = 0
        self.period_checks = 0
        self.composite_slot_writes = 0
        self.marking_progressions = 0

    def prepare(self, limit: int) -> tuple[list[int], int]:
        limit = _odd_floor(limit)
        self.ensure(limit)
        if limit > self.prime_list_limit:
            flags = self.flags
            old_list_limit = self.prime_list_limit
            old_count = len(self.primes)
            if self.materialization == "scan":
                append_prime_addresses_scan(self.primes, flags, old_list_limit, limit)
            else:
                append_prime_addresses_find(self.primes, flags, old_list_limit, limit)
            self.prime_list_limit = limit
            self.prime_materializations += 1
            if self.diagnostics:
                positions = (limit - old_list_limit) // 2
                self.base_flag_positions_considered += positions
                if self.materialization == "scan":
                    self.base_flag_positions_inspected += positions
                else:
                    self.base_flag_find_calls += len(self.primes) - old_count + 1
        stop = (len(self.primes) if limit >= self.prime_list_limit
                else bisect_right(self.primes, limit))
        return self.primes, stop

    def ensure(self, limit: int) -> None:
        limit = _odd_floor(limit)
        if limit <= self.limit:
            return
        size = (limit - 1) // 2
        if self.max_bitmap_bytes is not None and size > self.max_bitmap_bytes:
            raise MemoryError(f"Requested odd bitmap {size} bytes exceeds cap "
                              f"{self.max_bitmap_bytes}")
        primes, stop = self.prepare(isqrt(limit))
        old_limit = self.limit  # Recursive preparation may extend the prefix.
        flags = self.flags
        flags.extend(b"\x01" * ((limit - old_limit) // 2))
        if self.diagnostics:
            writes = progressions = 0
            for p in islice(primes, stop):
                first = max(p * p, ((old_limit + 2 + p - 1) // p) * p)
                if first % 2 == 0:
                    first += p
                if first > limit:
                    continue
                count = (limit - first) // (2 * p) + 1
                flags[(first - 3) // 2::p] = b"\x00" * count
                writes += count
                progressions += 1
            self.period_checks += stop
            self.composite_slot_writes += writes
            self.marking_progressions += progressions
        else:
            for p in islice(primes, stop):
                first = max(p * p, ((old_limit + 2 + p - 1) // p) * p)
                if first % 2 == 0:
                    first += p
                if first > limit:
                    continue
                count = (limit - first) // (2 * p) + 1
                flags[(first - 3) // 2::p] = b"\x00" * count
        self.limit = limit
        self.extensions += 1

    def snapshot(self) -> dict:
        return {
            "bitmap_certified_through": self.limit,
            "prime_list_certified_through": self.prime_list_limit,
            "retained_base_prime_addresses": len(self.primes),
            "retained_sieve_payload_bytes": len(self.flags),
            "base_sieve_builds": self.extensions,
            "prime_materializations": self.prime_materializations,
            "materialization_strategy": self.materialization,
            "diagnostics_enabled": self.diagnostics,
            "base_flag_positions_inspected": (
                self.base_flag_positions_inspected
                if self.diagnostics and self.materialization == "scan" else None),
            "base_flag_positions_considered": (
                self.base_flag_positions_considered if self.diagnostics else None),
            "base_flag_find_calls": (
                self.base_flag_find_calls if self.diagnostics else None),
            "base_period_checks": self.period_checks if self.diagnostics else None,
            "base_composite_slot_writes": (
                self.composite_slot_writes if self.diagnostics else None),
            "base_marking_progressions": (
                self.marking_progressions if self.diagnostics else None),
            "prime_list_copies": 0,
        }


class CandidateSegmentedSieve:
    """Short segmented Eratosthenes, with its own incremental small basis."""

    name = "candidate_segmented_odd"

    def __init__(self, diagnostics: bool = False,
                 max_bitmap_bytes: int | None = DEFAULT_MAX_BITMAP_BYTES):
        self.diagnostics = diagnostics
        self.base = SmallPrimeBasis(diagnostics, max_bitmap_bytes)
        self.queries = 0
        self.queried_odd_cells = 0
        self.segment_builds = 0
        self.prefix_queries = 0
        self.segment_period_checks = 0
        self.segment_composite_slot_writes = 0
        self.segment_marking_progressions = 0
        self.peak_sieve_payload_bytes = 1

    def search(self, B: int, L: int, R: int) -> dict:
        _check_window(B, L, R)
        self.queries += 1
        size = (R - L) // 2 + 1
        self.queried_odd_cells += size
        if L <= self.base.limit + 2:
            # Contiguous requested positions can become retained basis facts.
            self.base.ensure(R)
            self.prefix_queries += 1
            idx = self.base.flags.rfind(b"\x01", (L - 3) // 2, (R - 3) // 2 + 1)
            address = None if idx < 0 else 2 * idx + 3
            self.peak_sieve_payload_bytes = max(
                self.peak_sieve_payload_bytes, len(self.base.flags))
        else:
            primes, stop = self.base.prepare(isqrt(R))
            if R <= self.base.limit:
                self.prefix_queries += 1
                idx = self.base.flags.rfind(b"\x01", (L - 3) // 2, (R - 3) // 2 + 1)
                address = None if idx < 0 else 2 * idx + 3
            else:
                window = bytearray(b"\x01") * size
                self.segment_builds += 1
                self.peak_sieve_payload_bytes = max(
                    self.peak_sieve_payload_bytes, len(self.base.flags) + size)
                if self.diagnostics:
                    writes = progressions = 0
                    for p in islice(primes, stop):
                        first = max(p * p, ((L + p - 1) // p) * p)
                        if first % 2 == 0:
                            first += p
                        if first > R:
                            continue
                        count = (R - first) // (2 * p) + 1
                        window[(first - L) // 2::p] = b"\x00" * count
                        writes += count
                        progressions += 1
                    self.segment_period_checks += stop
                    self.segment_composite_slot_writes += writes
                    self.segment_marking_progressions += progressions
                else:
                    for p in islice(primes, stop):
                        first = max(p * p, ((L + p - 1) // p) * p)
                        if first % 2 == 0:
                            first += p
                        if first > R:
                            continue
                        count = (R - first) // (2 * p) + 1
                        window[(first - L) // 2::p] = b"\x00" * count
                idx = window.rfind(b"\x01")
                address = None if idx < 0 else L + 2 * idx
        return _answer(address, B, L, R,
                       "complete segmented odd-prime bitmap in the finite-world frontier")

    def snapshot(self) -> dict:
        return {
            "engine": self.name, "queries": self.queries,
            "queried_odd_cells": self.queried_odd_cells,
            "segment_builds": self.segment_builds,
            "prefix_queries": self.prefix_queries,
            "full_window_hole_counts": 0,
            "all_window_addresses_materialized": 0,
            "peak_sieve_payload_bytes": self.peak_sieve_payload_bytes,
            "segment_period_checks": (
                self.segment_period_checks if self.diagnostics else None),
            "segment_composite_slot_writes": (
                self.segment_composite_slot_writes if self.diagnostics else None),
            "segment_marking_progressions": (
                self.segment_marking_progressions if self.diagnostics else None),
            "base": self.base.snapshot(),
        }


class CandidateFullSieve:
    """Rebuild a full odd bitmap when its upper bound increases; retain it."""

    name = "candidate_full_odd"

    def __init__(self, diagnostics: bool = False,
                 max_bitmap_bytes: int | None = DEFAULT_MAX_BITMAP_BYTES):
        self.diagnostics = diagnostics
        self.max_bitmap_bytes = max_bitmap_bytes
        self.limit = 3
        self.flags = bytearray(b"\x01")
        self.queries = 0
        self.queried_odd_cells = 0
        self.sieve_builds = 0
        self.composite_slot_writes = 0
        self.marking_progressions = 0
        self.peak_sieve_payload_bytes = 1

    def ensure(self, limit: int) -> None:
        limit = _odd_floor(limit)
        if limit <= self.limit:
            return
        size = (limit - 1) // 2
        if self.max_bitmap_bytes is not None and size > self.max_bitmap_bytes:
            raise MemoryError(f"Requested odd bitmap {size} bytes exceeds cap "
                              f"{self.max_bitmap_bytes}")
        flags = bytearray(b"\x01") * size
        if self.diagnostics:
            writes = progressions = 0
            for p in range(3, isqrt(limit) + 1, 2):
                if flags[(p - 3) // 2]:
                    first = (p * p - 3) // 2
                    count = (size - 1 - first) // p + 1
                    flags[first::p] = b"\x00" * count
                    writes += count
                    progressions += 1
            self.composite_slot_writes += writes
            self.marking_progressions += progressions
        else:
            for p in range(3, isqrt(limit) + 1, 2):
                if flags[(p - 3) // 2]:
                    first = (p * p - 3) // 2
                    count = (size - 1 - first) // p + 1
                    flags[first::p] = b"\x00" * count
        self.peak_sieve_payload_bytes = max(
            self.peak_sieve_payload_bytes, len(self.flags) + size)
        self.flags = flags
        self.limit = limit
        self.sieve_builds += 1

    def search(self, B: int, L: int, R: int) -> dict:
        _check_window(B, L, R)
        self.ensure(R)
        self.queries += 1
        self.queried_odd_cells += (R - L) // 2 + 1
        idx = self.flags.rfind(b"\x01", (L - 3) // 2, (R - 3) // 2 + 1)
        address = None if idx < 0 else 2 * idx + 3
        return _answer(address, B, L, R,
                       "complete full odd-prime bitmap in the finite-world frontier")

    def snapshot(self) -> dict:
        return {
            "engine": self.name, "queries": self.queries,
            "queried_odd_cells": self.queried_odd_cells,
            "bitmap_certified_through": self.limit,
            "retained_sieve_payload_bytes": len(self.flags),
            "peak_sieve_payload_bytes": self.peak_sieve_payload_bytes,
            "sieve_builds": self.sieve_builds,
            "full_window_hole_counts": 0,
            "all_window_addresses_materialized": 0,
            "diagnostics_enabled": self.diagnostics,
            "composite_slot_writes": (
                self.composite_slot_writes if self.diagnostics else None),
            "marking_progressions": (
                self.marking_progressions if self.diagnostics else None),
        }


class CandidateIncrementalSieve:
    """Extend a full odd bitmap; answer by direct reverse bitmap lookup."""

    name = "candidate_incremental_odd"

    def __init__(self, diagnostics: bool = False,
                 max_bitmap_bytes: int | None = DEFAULT_MAX_BITMAP_BYTES):
        self.base = SmallPrimeBasis(diagnostics, max_bitmap_bytes)
        self.queries = 0
        self.queried_odd_cells = 0

    def search(self, B: int, L: int, R: int) -> dict:
        _check_window(B, L, R)
        self.base.ensure(R)
        self.queries += 1
        self.queried_odd_cells += (R - L) // 2 + 1
        idx = self.base.flags.rfind(b"\x01", (L - 3) // 2, (R - 3) // 2 + 1)
        address = None if idx < 0 else 2 * idx + 3
        return _answer(address, B, L, R,
                       "complete incremental odd-prime bitmap in the finite-world frontier")

    def snapshot(self) -> dict:
        return {
            "engine": self.name, "queries": self.queries,
            "queried_odd_cells": self.queried_odd_cells,
            "full_window_hole_counts": 0,
            "all_window_addresses_materialized": 0,
            "peak_sieve_payload_bytes": len(self.base.flags),
            "base": self.base.snapshot(),
        }
