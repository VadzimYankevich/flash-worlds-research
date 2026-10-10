"""Reproduce this research package; computation needs Python's standard library.

Default: verify frozen evidence, rerun the record probe, mathematical checks,
and the independent teaching implementation. Optional flags rebuild timed
benchmarks, figures/video, and the article. Historical *_original files remain
unchanged. Machine-dependent data is written to separate *_rerun files.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def run(name, arguments, output_json=None):
    print("Running: " + name, flush=True)
    start = time.perf_counter()
    process = subprocess.run([sys.executable, *arguments], cwd=ROOT,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             encoding="utf-8", errors="replace")
    if process.returncode:
        raise RuntimeError(name + " failed:\n" + process.stdout + "\n" + process.stderr)
    entry = {"name": name, "status": "PASS",
             "wall_seconds": time.perf_counter() - start}
    if output_json is not None:
        payload = json.loads(process.stdout)
        (ROOT / output_json).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                                        encoding="utf-8")
        entry["output"] = output_json
    else:
        entry["stdout"] = process.stdout.strip()
    return entry


def run_probe(name, script, stem):
    """Keep first-run evidence, while allowing repeated package verification."""
    with tempfile.TemporaryDirectory(prefix="flash_worlds_probe_") as work:
        destination = Path(work) / (stem + "_rerun.json")
        entry = run(name, [script, "--output", str(destination)])
        entry.pop("stdout", None)
        outputs = []
        for source in sorted(Path(work).iterdir()):
            if source.is_file():
                shutil.copyfile(source, DATA / source.name)
                outputs.append("data/" + source.name)
        if not destination.exists():
            raise RuntimeError(name + " did not write its result")
        payload = json.loads(destination.read_text(encoding="utf-8"))
        if payload.get("status") != "PASS":
            raise RuntimeError(name + " did not report PASS")
        entry["outputs"] = outputs
        return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true", help="Rerun the 36 canonical timed observations; Linux/WSL")
    parser.add_argument("--media", action="store_true", help="Rebuild figures and MP4; matplotlib and ffmpeg")
    parser.add_argument("--paper", action="store_true", help="Rebuild paper/article.pdf with XeLaTeX")
    args = parser.parse_args()
    report = {"schema_version": 1, "status": "PASS",
              "generated_at_utc": datetime.now(timezone.utc).isoformat(),
              "classification": "Package reproduction; stage times are not competing prime-search timings.",
              "stages": []}
    DATA.mkdir(exist_ok=True)
    commands = ["src/reproduce.py", "--record"]
    if args.benchmark:
        commands.append("--benchmark")
    report["stages"].append(run("canonical evidence and record", commands,
                               "data/reproduction_rerun.json"))
    report["stages"].append(run("mathematical identities", ["src/verify_mathematics.py", "--output", "data/mathematics_rerun.json"]))
    report["stages"].append(run("independent teaching implementation", ["src/flash_worlds_demo.py", "self-check"],
                               "data/demo_selfcheck.json"))
    report["stages"].append(run_probe("ripple depth and residual layers", "src/ripple_depth_probe.py", "ripple_depth"))
    report["stages"].append(run_probe("absorption and return of axis 1013", "src/ripple_1013_probe.py", "ripple_1013"))
    report["stages"].append(run_probe("record-window old-shadow absorption certificate", "src/ripple_smooth_certificate.py", "ripple_smooth_certificate"))
    report["stages"].append(run("resource snapshot and scale estimates", ["src/resource_audit.py"],
                               "data/resources_rerun.json"))
    if args.media:
        report["stages"].append(run("figures and video", ["src/make_figures.py", "--video"]))
        report["stages"].append(run("ripple absorption figure", ["src/make_ripple_figure.py"]))
    if args.paper:
        report["stages"].append(run("LaTeX article", ["src/build_paper.py"]))
    path = DATA / "package_verification.json"
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("PASS: all requested stages completed. Report: data/package_verification.json")


if __name__ == "__main__":
    main()
