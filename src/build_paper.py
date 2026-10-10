"""Build the supplied LaTeX article into paper/article.pdf (XeLaTeX)."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    engine = shutil.which("xelatex")
    if not engine:
        raise SystemExit("XeLaTeX not found. Install TeX Live or MiKTeX with fontspec, polyglossia and DejaVu fonts.")
    for name in ("prime_space_projection.pdf", "benchmark_times.pdf", "record_window.pdf"):
        if not (ROOT / "figures" / name).is_file():
            raise SystemExit("Missing figures. Run: python src/make_figures.py")
    paper = ROOT / "paper"
    with tempfile.TemporaryDirectory(prefix="flash-paper-") as temp:
        command = [engine, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                   "-output-directory", temp, "article.tex"]
        for _ in range(2):
            result = subprocess.run(command, cwd=paper, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
            if result.returncode:
                raise SystemExit(result.stdout)
        log = (Path(temp) / "article.log").read_text(encoding="utf-8", errors="replace")
        warnings = [line for line in log.splitlines()
                    if "Overfull" in line or "undefined" in line or "Missing character" in line]
        if warnings:
            raise SystemExit("Review LaTeX layout/references before delivery:\n" + "\n".join(warnings))
        shutil.copyfile(Path(temp) / "article.pdf", paper / "article.pdf")
    print("Built paper/article.pdf")


if __name__ == "__main__":
    main()
