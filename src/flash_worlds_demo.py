#!/usr/bin/env python3
"""Учебный пример миров вспышек; Python 3.10+, без внешних зависимостей.

python flash_worlds_demo.py flashes --count 15
python flash_worlds_demo.py record-probe
python flash_worlds_demo.py self-check
python flash_worlds_demo.py benchmark --count 20 --rounds 6

Точная ветвь ищет справа налево, хранит адреса и делители и расширяет
малый базис только до isqrt(n). Урезанная проверка record-probe НЕ
объявляет оставшиеся адреса простыми. Это самостоятельный учебный код,
а не замена реализации, на которой получены прежние времена проекта.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from itertools import islice
import json
from math import isqrt
from random import Random
from statistics import median
from time import perf_counter


class SmallBasis:
    """Сохраняет простые адреса и достраивает только новый нечётный участок."""

    def __init__(self):
        self.limit = 1
        self.primes = []
        self.flags = bytearray()  # индекс k соответствует числу 2*k + 3

    def through(self, limit):
        limit -= (limit % 2 == 0)
        if limit > self.limit:
            if (limit - 1) // 2 > 128 * 1024 * 1024:
                raise MemoryError("Превышен лимит базиса; ответ о простоте не получен")
            _, stop = self.through(isqrt(limit))
            old = self.limit  # рекурсивное достроение уже могло изменить предел
            self.flags.extend(b"\x01" * ((limit - old) // 2))
            for p in islice(self.primes, stop):
                first = max(p * p, ((old + 2 + p - 1) // p) * p)
                if first % 2 == 0:
                    first += p
                if first <= limit:
                    self.flags[(first - 3) // 2::p] = b"\0" * (
                        (limit - first) // (2 * p) + 1)
            i = self.flags.find(b"\x01", (old - 1) // 2)
            while i >= 0:
                self.primes.append(2 * i + 3)
                i = self.flags.find(b"\x01", i + 1)
            self.limit = limit
        return self.primes, bisect_right(self.primes, limit)


class ExactCandidates:
    """None означает доказанное простое; целый делитель — составное."""

    def __init__(self):
        self.base = SmallBasis()
        self.facts = {}  # сохраняем адрес -> делитель либо None

    def factor(self, n):
        if n < 2:
            raise ValueError("Требуется n >= 2")
        if n in self.facts:
            return self.facts[n]
        limit = isqrt(n)
        divisor = None
        for p in (2, 3, 5):
            if p > limit:
                break
            if n % p == 0:
                divisor = p
                break
        if divisor is None and limit >= 7:
            primes, stop = self.base.through(limit)
            for p in islice(primes, bisect_right(primes, 5), stop):
                if n % p == 0:
                    divisor = p
                    break
        self.facts[n] = divisor
        return divisor

    def search(self, left, right):
        witnesses = []
        for n in range(right, left - 1, -2):
            divisor = self.factor(n)
            if divisor is None:
                return n, witnesses
            witnesses.append((n, divisor))
        return None, witnesses


class Segmented:
    """Собственное простое сегментное решето на тех же коротких окнах."""

    def __init__(self):
        self.base = SmallBasis()

    def search(self, left, right):
        flags = bytearray(b"\x01") * ((right - left) // 2 + 1)
        primes, stop = self.base.through(isqrt(right))
        for p in islice(primes, stop):
            first = max(p * p, ((left + p - 1) // p) * p)
            if first % 2 == 0:
                first += p
            if first <= right:
                flags[(first - left) // 2::p] = b"\0" * (
                    (right - first) // (2 * p) + 1)
        i = flags.rfind(b"\x01")
        address = None if i < 0 else left + 2 * i
        start = left if address is None else address + 2
        # Здесь свидетельство составности — полное покрытие решетом.
        return address, [(n, "sieve") for n in range(right, start - 1, -2)]


MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def strong_probable_prime(n, base):
    """Один раунд Миллера — Рабина; True сам по себе не доказывает простоту."""
    if n < 3 or n % 2 == 0:
        return n == 2
    base %= n
    if base == 0:
        return True
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(base, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


def mr64(n):
    """Точный результат только при n < 2**64; выше запрещено применять.

    12 первых простых оснований достаточны в этом диапазоне:
    Sorenson & Webster, Strong pseudoprimes to twelve prime bases,
    https://arxiv.org/abs/1509.00864 .
    """
    if n >= 1 << 64:
        raise ValueError("MR64 разрешён только при n < 2**64")
    if n < 2:
        return False
    for p in MR_BASES:
        if n % p == 0:
            return n == p
    return all(strong_probable_prime(n, a) for a in MR_BASES)


class MillerRabin64:
    def __init__(self):
        self.facts = {}

    def search(self, left, right):
        witnesses = []
        for n in range(right, left - 1, -2):
            if n not in self.facts:
                self.facts[n] = mr64(n)
            if self.facts[n]:
                return n, witnesses
            witnesses.append((n, "MR64 composite"))
        return None, witnesses


ENGINES = {"exact": ExactCandidates, "segmented": Segmented, "mr64": MillerRabin64}


def run_flashes(engine, count):
    """Общий контракт: крайнее простое и закрытый нечётный суффикс."""
    if count < 0:
        raise ValueError("Число вспышек должно быть неотрицательным")
    b, previous_right = 3, 1
    anchors, steps = [b], []
    for _ in range(count):
        upper = min(b * b, 3 * b + 4)
        lower = max(b + 2, previous_right + 2)
        right, witnesses, windows = upper, [], 0
        while right >= lower:
            left = max(lower, right - 28)  # не более 15 нечётных адресов
            address, part = engine.search(left, right)
            witnesses.extend(part)
            windows += 1
            if address is not None:
                break
            right = left - 2
        else:
            raise ArithmeticError("В пределах границы не найден следующий шаг")
        steps.append({"B": b, "R": upper, "prime": address, "windows": windows,
                      "closed_suffix": {"odd_from": address + 2, "odd_to": upper,
                                        "composite_witnesses": witnesses}})
        b, previous_right = address, upper
        anchors.append(b)
    return {"contract": "rightmost_prime_and_closed_suffix",
            "anchors": anchors, "steps": steps}


def record_probe(limit=1_000_000, width=1500):
    """Только ограниченное покрытие у R=3P+4, P=2**136279841-1."""
    if limit < 3 or not 1 <= width <= 10_000_000:
        raise ValueError("Нужны limit >= 3 и 1 <= width <= 10000000")
    exponent = 136_279_841
    basis = SmallBasis()
    primes, stop = basis.through(limit)
    factors = [None] * width
    for p in islice(primes, stop):
        # N_j = 3*2**exponent + 1 - 2*j; его нули идут через p позиций.
        residue = (3 * pow(2, exponent, p) + 1) % p
        first = residue * ((p + 1) // 2) % p  # точное деление на 2 modulo p
        for j in range(first, width, p):
            if factors[j] is None:
                factors[j] = p  # первый делитель уже достаточен
    first_unknown = next((j for j, p in enumerate(factors) if p is None), None)
    candidate = None if first_unknown is None else {
        "index": first_unknown, "address": f"3P{4 - 2 * first_unknown:+d}",
        "expanded": f"3*2^{exponent}{1 - 2 * first_unknown:+d}", "status": "UNKNOWN"}
    return {"classification": "exact_bounded_filter_only", "exponent": exponent,
            "P": f"2^{exponent}-1", "addresses": "N_j=3P+4-2*j",
            "small_prime_limit": limit, "odd_primes_examined": stop,
            "positions": width, "composite": sum(p is not None for p in factors),
            "unknown": sum(p is None for p in factors),
            "consecutive_closed_top_positions": (
                width if first_unknown is None else first_unknown),
            "first_unknown": candidate, "factor_by_index": factors}


def ordinary_sieve(limit):
    """Независимое полное решето только для проверки умеренных диапазонов."""
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\0\0"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = b"\0" * ((limit - p * p) // p + 1)
    return flags


def self_check():
    truth, exact = ordinary_sieve(1_000_000), ExactCandidates()
    for n in range(2, 50_001):
        factor = exact.factor(n)
        assert (factor is None) == bool(truth[n]) == mr64(n), n
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
    routes = [run_flashes(factory(), 10) for factory in ENGINES.values()]
    assert routes[0]["anchors"] == routes[1]["anchors"] == routes[2]["anchors"]
    for route in routes:
        for step in route["steps"]:
            assert truth[step["prime"]]
            assert all(not truth[n] for n in range(step["prime"] + 2, step["R"] + 1, 2))
    pseudoprimes = [(2047, (2,)), (1373653, (2, 3)),
                   (25326001, (2, 3, 5)), (3215031751, (2, 3, 5, 7))]
    witnesses = []
    for n, bases in pseudoprimes:
        assert all(strong_probable_prime(n, a) for a in bases)
        factor = exact.factor(n)
        assert factor is not None and 1 < factor < n and n % factor == 0
        assert not mr64(n)
        witnesses.append({"n": n, "passes_bases": bases, "exact_factor": factor})
    try:
        mr64(1 << 64)
    except ValueError:
        pass
    else:
        raise AssertionError("Отсутствует обязательная граница MR64")
    probe = record_probe()
    assert (probe["composite"], probe["unknown"]) == (1381, 119)
    assert probe["consecutive_closed_top_positions"] == 43
    assert probe["first_unknown"]["address"] == "3P-82"
    for j, p in enumerate(probe["factor_by_index"]):
        if p is not None:
            assert (3 * pow(2, probe["exponent"], p) + 1 - 2 * j) % p == 0
    return {"status": "PASS", "exhaustive_range": [2, 50000],
            "flash_routes": 3, "flashes_per_route": 10,
            "strong_pseudoprime_witnesses": witnesses,
            "record_probe": "1381 composite; 119 UNKNOWN; first UNKNOWN = 3P-82"}


def benchmark(count, rounds):
    if rounds < 1:
        raise ValueError("Нужен хотя бы один парный повтор")
    rng, samples, reference = Random(20261010), [], None
    for factory in ENGINES.values():
        run_flashes(factory(), min(count, 8))  # прогрев интерпретатора вне замера
    for _ in range(rounds):
        order, row = list(ENGINES), {}
        rng.shuffle(order)
        for name in order:
            started = perf_counter()
            route = run_flashes(ENGINES[name](), count)  # новый базис оплачивается
            row[name] = perf_counter() - started
            signature = (route["anchors"], [(s["R"], s["windows"]) for s in route["steps"]])
            if reference is None:
                reference = signature
            assert signature == reference, "Разные результаты сравниваемых движков"
        samples.append(row)
    return {"note": "Учебные реализации Python; это не сравнение с primesieve",
            "contract": "rightmost_prime_and_closed_suffix", "flashes": count,
            "rounds": rounds, "state": "fresh engine in every timed run",
            "final_anchor": reference[0][-1], "seconds_by_round": samples,
            "median_seconds": {name: median(r[name] for r in samples) for name in ENGINES},
            "median_paired_exact_over_segmented": median(r["exact"] / r["segmented"] for r in samples),
            "median_paired_exact_over_mr64": median(r["exact"] / r["mr64"] for r in samples)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    flash = commands.add_parser("flashes", help="точные вспышки от B=3")
    flash.add_argument("--count", type=int, default=15)
    probe = commands.add_parser("record-probe", help="ограниченные тени около 3P+4")
    probe.add_argument("--limit", type=int, default=1_000_000)
    probe.add_argument("--width", type=int, default=1500)
    commands.add_parser("self-check", help="независимая проверка корректности")
    bench = commands.add_parser("benchmark", help="парное сравнение трёх реализаций")
    bench.add_argument("--count", type=int, default=20)
    bench.add_argument("--rounds", type=int, default=6)
    args = parser.parse_args()
    if args.command == "flashes":
        result = run_flashes(ExactCandidates(), args.count)
    elif args.command == "record-probe":
        result = record_probe(args.limit, args.width)
    elif args.command == "self-check":
        result = self_check()
    else:
        result = benchmark(args.count, args.rounds)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
