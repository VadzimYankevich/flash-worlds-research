"""Record the exposed computation resources and estimate full-basis scale.

Python 3.11+ standard library only. No record-sized integer is constructed.
    python src/resource_audit.py
    python src/resource_audit.py --output data/resources_rerun.json

Without --output, prints JSON. An existing output file is never overwritten.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from decimal import Decimal, ROUND_FLOOR, localcontext
import glob
import json
import os
from pathlib import Path
import platform


EXPONENT = 136279841


def read_text(path):
    try:
        return Path(path).read_text(encoding="utf-8").strip()
    except (FileNotFoundError, PermissionError, OSError):
        return None


def limit_value(raw):
    if raw is None or raw == "max":
        return None
    return int(raw)


def scientific_from_log10(logarithm):
    exponent = int(logarithm.to_integral_value(rounding=ROUND_FLOOR))
    coefficient = Decimal(10) ** (logarithm - Decimal(exponent))
    return format(coefficient, ".8f") + "e+" + str(exponent)


def collect():
    cpuinfo = read_text("/proc/cpuinfo") or ""
    models = sorted({line.split(":", 1)[1].strip()
                     for line in cpuinfo.splitlines()
                     if line.startswith("model name") and ":" in line})
    affinity = (sorted(os.sched_getaffinity(0))
                if hasattr(os, "sched_getaffinity") else None)
    cgroup_membership = read_text("/proc/self/cgroup")
    cgroup_path = Path("/sys/fs/cgroup")
    if cgroup_membership:
        for line in cgroup_membership.splitlines():
            if line.startswith("0::"):
                member = cgroup_path / line[3:].lstrip("/")
                if (member / "cpu.max").exists():
                    cgroup_path = member
    raw = {name: read_text(cgroup_path / name) for name in
           ("cpu.max", "memory.max", "memory.current", "memory.swap.max",
            "memory.swap.current")}
    quota_us = period_us = None
    if raw["cpu.max"]:
        quota, period = raw["cpu.max"].split()
        quota_us, period_us = limit_value(quota), int(period)
    quota_equivalents = (quota_us / period_us
                        if quota_us is not None else None)
    meminfo = read_text("/proc/meminfo") or ""
    swap_total_kib = None
    for line in meminfo.splitlines():
        if line.startswith("SwapTotal:"):
            swap_total_kib = int(line.split()[1])
    swap_lines = read_text("/proc/swaps")
    swap_devices = (swap_lines.splitlines()[1:]
                    if swap_lines is not None else None)
    device_paths = sorted(set(glob.glob("/dev/nvidia*") +
                              glob.glob("/dev/dri") + glob.glob("/dev/dri/*")))
    devices = [dict(path=path, readable=os.access(path, os.R_OK),
                    writable=os.access(path, os.W_OK)) for path in device_paths]
    observed = dict(
        python_version=platform.python_version(), platform=platform.platform(),
        cpu=dict(model_names=models, model_source="/proc/cpuinfo",
                 os_cpu_count=os.cpu_count(), affinity_cpu_ids=affinity,
                 affinity_cpu_count=len(affinity) if affinity is not None else None),
        cgroup=dict(path=str(cgroup_path), membership=cgroup_membership,
                    raw=raw, cpu_quota_us=quota_us, cpu_period_us=period_us,
                    cpu_quota_equivalent_cpus=quota_equivalents,
                    memory_limit_bytes=limit_value(raw["memory.max"]),
                    memory_current_bytes=limit_value(raw["memory.current"]),
                    memory_swap_limit_bytes=limit_value(raw["memory.swap.max"]),
                    memory_swap_current_bytes=limit_value(raw["memory.swap.current"])),
        swap=dict(proc_swaps_rows=swap_devices, proc_meminfo_swap_total_kib=swap_total_kib),
        gpu_device_exposure=dict(paths=devices, device_paths_found=bool(devices)))
    with localcontext() as context:
        context.prec = 50
        log10_p = Decimal(EXPONENT) * Decimal(2).log10()
        log10_r = log10_p + Decimal(3).log10()
        log10_root = log10_r / 2
        ln_root = log10_root * Decimal(10).ln()
        log10_basis_count = log10_root - ln_root.log10()
        seconds_per_year = Decimal("365.25") * 24 * 60 * 60
        log10_years = log10_basis_count - 12 - seconds_per_year.log10()
        payload_bytes = (EXPONENT + 7) // 8
        exact = dict(exponent=EXPONENT,
                     P="2^136279841-1", R="3P+4=3*2^136279841+1",
                     P_binary_digits=EXPONENT,
                     P_packed_binary_payload_bytes=payload_bytes,
                     P_packed_binary_payload_MiB=str(Decimal(payload_bytes) / 2**20),
                     P_integer_constructed=False)
        estimates = dict(
            decimal_precision_digits=50,
            model="Prime number theorem: pi(x) ~ x/ln(x), x=sqrt(R).",
            classification="Asymptotic scale estimates, not measurements or rigorous lower bounds.",
            approximation="log10(P) approximated by E*log10(2), log10(R) by E*log10(2)+log10(3); the +/-1 terms are neglected.",
            log10_P_approx=str(log10_p), log10_R_approx=str(log10_r),
            log10_sqrt_R_approx=str(log10_root),
            log10_full_root_prime_basis_count_approx=str(log10_basis_count),
            full_root_prime_basis_count_scientific_approx=scientific_from_log10(log10_basis_count),
            hypothetical_full_scan=dict(
                classification="Optimistic toy scenario for enumerating every member of the full basis; not a benchmark and not a limit for other algorithms.",
                checks_per_second_assumed=10**12,
                seconds_per_year_assumed=str(seconds_per_year),
                cost_model="One check per basis prime; generating, storing and accessing the basis are assigned zero cost.",
                formula="log10(years) = log10(estimated basis count) - 12 - log10(seconds per year)",
                log10_years_approx=str(log10_years),
                years_scientific_approx=scientific_from_log10(log10_years)))
    return dict(
        schema_version=1, generated_at_utc=datetime.now(timezone.utc).isoformat(),
        observed_resources=observed, computed_exact=exact, scale_estimates=estimates,
        interpretation=[
            "Visible logical CPUs, the affinity set and the cgroup CPU quota are different quantities.",
            "The cgroup memory limit is the relevant local limit; host physical RAM is not substituted for it.",
            "memory.swap.max='max' means no limit in the observed cgroup file, not that swap is available; actual swap observations are reported separately.",
            "Absence of exposed GPU device paths says nothing about GPUs elsewhere on the host or remote resources.",
            "The packed P payload omits Python object overhead and arithmetic work buffers.",
            "The scale estimate concerns the current complete-root-basis approach, not every possible exact shadow method or primality algorithm.",
            "The bounded record experiment leaves 3P-82 unresolved; no new prime is established."
        ])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Save JSON to a new file; existing files are not overwritten")
    args = parser.parse_args()
    result = collect()
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as stream:
            stream.write(text)
        print(json.dumps(dict(output=str(args.output.resolve()),
                              generated_at_utc=result["generated_at_utc"]),
                         ensure_ascii=False))
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
