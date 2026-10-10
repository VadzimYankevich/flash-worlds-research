"""Exact bounded probe of shadow coverage near the current record prime.

This experiment constructs no record-sized integer and proves no new prime.
Run with Python 3.10+; no third-party packages. Results include this exact source.
"""
from datetime import datetime, timezone
from math import gcd, isqrt, lcm
from pathlib import Path
from time import perf_counter
import json
import platform

EXPONENT = 136279841
SMALL_LIMIT = 1_000_000
FIRST_WIDTH = 15
EXTENDED_WIDTH = 1500

def small_primes(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p:limit+1:p] = b"\x00" * ((limit-p*p)//p+1)
    return [p for p in range(3, limit+1, 2) if flags[p]]

def project(primes, width, early_stop):
    factors = [None] * width
    missing = width
    retained = []
    active = examined = 0
    for p in primes:
        examined += 1
        r = pow(2, EXPONENT, p)
        j0 = ((3*r+1)*((p+1)//2)) % p
        if j0 >= width:
            continue
        active += 1
        fresh = []
        for j in range(j0, width, p):
            if factors[j] is None:
                factors[j] = p
                missing -= 1
                fresh.append(j)
        if fresh:
            retained.append(dict(p=p, j0=j0, pow2_mod_p=r, newly_covered_j=fresh))
        if early_stop and missing == 0:
            break
    return dict(width=width, primes_examined=examined,
                last_prime_examined=p, active_periods=active,
                retained_periods=retained, factors=factors,
                unresolved_j=[j for j,p in enumerate(factors) if p is None])

def distinct_factors(n):
    result = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            result.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        result.append(n)
    return result

def order_two(p):
    order = p-1
    for q in distinct_factors(order):
        while order % q == 0 and pow(2, order//q, p) == 1:
            order //= q
    assert pow(2, order, p) == 1
    return order

def run():
    started = perf_counter()
    primes = small_primes(SMALL_LIMIT)
    small_sieve_seconds = perf_counter()-started
    t = perf_counter()
    first = project(primes, FIRST_WIDTH, True)
    first_seconds = perf_counter()-t
    t = perf_counter()
    extended = project(primes, EXTENDED_WIDTH, False)
    extended_seconds = perf_counter()-t
    expected = [53,5,3,7,89,3,5,2749,3,11,7,3,17,139291,3]
    assert first["factors"] == expected
    for data in (first, extended):
        for j,p in enumerate(data["factors"]):
            if p is not None:
                assert (3*pow(2, EXPONENT, p)+1-2*j) % p == 0
    # Reuse the first window's nine period rules across 1500 positions.
    keep = [row["p"] for row in first["retained_periods"]]
    inherited = project(keep, EXTENDED_WIDTH, False)
    assert len(keep) == 9
    assert EXTENDED_WIDTH-len(inherited["unresolved_j"]) == 936
    assert EXTENDED_WIDTH-len(extended["unresolved_j"]) == 1381
    assert extended["unresolved_j"][0] == 43

    # Minimum number of ordinary prime-period rules for the first 15 points.
    # Any common odd divisor of N_j and N_k divides abs(j-k) <= 14.
    isolated = [0,4,7,9,12,13]
    for j in isolated:
        for k in range(FIRST_WIDTH):
            if j != k:
                d = abs(j-k)
                assert gcd((3*pow(2, EXPONENT, d)+1-2*j) % d, d) == 1
    small_hits = {str(p):[j for j in range(FIRST_WIDTH)
                         if (3*pow(2, EXPONENT, p)+1-2*j) % p == 0]
                  for p in (3,5,7,11,13)}
    # Six isolated points need six different rules. Two further primes cover
    # at most 5+3 < 9 other points; every prime >=17 hits at most one point.
    assert sorted([len(v) for v in small_hits.values()], reverse=True)[:2] == [5,3]
    minimality = dict(minimum_periods=9, isolated_indices=isolated,
                      small_period_hits=small_hits,
                      proof="6 isolated points + at least 3 periods for the remaining 9; the exhibited cover attains 9",
                      scope="number of rules of the form multiples of one prime; not search time or arbitrary rule languages")

    orders = [order_two(p) for p in keep]
    exponent_period = lcm(*orders)
    period_rule = dict(primes=keep, multiplicative_orders_of_two=orders,
                       exponent_modulus=exponent_period,
                       exponent_residue=EXPONENT % exponent_period,
                       meaning="The same first-15 composite certificate applies to exponents congruent to this residue, for sufficiently large exponents.")
    result = dict(
        status="PASS", generated_at_utc=datetime.now(timezone.utc).isoformat(),
        python=platform.python_version(), platform=platform.platform(),
        classification="exact bounded symbolic coverage experiment; not a speed comparison and not a new prime discovery",
        input=dict(P="2^136279841-1", exponent=EXPONENT,
                   record_reference="https://www.mersenne.org/primes/",
                   world_boundary="R=3P+4=3*2^E+1",
                   addresses="N_j=R-2*j", small_prime_limit=SMALL_LIMIT),
        protocol=dict(record_integer_constructed=False, full_root_basis_constructed=False,
                      full_primality_tests=0,
                      arithmetic="exact Python integers, small-modulus powers and congruences",
                      each_project_call_starts_from_empty_window=True),
        first_window=first,
        extended_window=extended,
        reuse=dict(first_nine_primes=keep, examined_odd_positions=EXTENDED_WIDTH,
                   covered_by_first_nine=EXTENDED_WIDTH-len(inherited["unresolved_j"]),
                   covered_by_all_primes_through_limit=EXTENDED_WIDTH-len(extended["unresolved_j"]),
                   remaining_unknown=len(extended["unresolved_j"]),
                   consecutive_closed_top_positions=extended["unresolved_j"][0],
                   next_unresolved="3P-82=3*2^E-85",
                   next_unresolved_is_prime="not established"),
        minimum_first_window_certificate=minimality,
        reusable_exponent_rule=period_rule,
        timing_seconds=dict(small_sieve=small_sieve_seconds,
                            first_window_projection=first_seconds,
                            extended_window_projection=extended_seconds,
                            total_including_assertions=perf_counter()-started,
                            note="single diagnostic run, not paired benchmarking"),
        limitations=[
            "No factor up to 1000000 means unresolved, not prime.",
            "No universal left cutoff for subsequent windows has been proved.",
            "The first nine factors were discovered by examining 12943 odd primes, not guessed.",
            "No performance superiority over an equivalent symbolic segmented sieve is claimed."
        ],
        reproduction="Write embedded_source to record_boundary_probe.py and run python record_boundary_probe.py. Only the Python standard library is needed.",
        embedded_source=Path(__file__).read_text(encoding="utf-8")
    )
    out = Path(__file__).with_name("record_window_boundary_probe_2026-10-10.json")
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(dict(output=str(out.resolve()),status=result["status"],
                          kept_periods=len(keep),covered_first_window=FIRST_WIDTH,
                          covered_extended=1381,unresolved_extended=119,
                          closed_prefix=43,minimum_periods=9,
                          exponent_period=exponent_period,
                          timings=result["timing_seconds"]),ensure_ascii=False))

if __name__ == "__main__":
    run()

