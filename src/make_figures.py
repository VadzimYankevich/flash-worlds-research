#!/usr/bin/env python3
"""Воспроизводимые научные рисунки и короткое видео к исследованию.

Python 3.10+ и matplotlib (со стандартными зависимостями).
Для --video дополнительно нужен ffmpeg в PATH с кодеком libx264.

    python src/make_figures.py
    python src/make_figures.py --video

Команды работают из любого каталога. Читают data/*_original.json,
сохраняют явные исходные данные рисунков в data/figure_inputs.json,
затем создают PNG/PDF и, по запросу, MP4 в figures/. Времена эксперимента
читаются из сохранённого JSON; генерация иллюстраций не входит в замеры.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
from statistics import median
import subprocess
import tempfile

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch, Rectangle
from matplotlib.ticker import ScalarFormatter
from mpl_toolkits.mplot3d.art3d import Poly3DCollection


TEXT = "#1d2c3e"
MUTED = "#58677b"
BLUE = "#28659b"
SLATE = "#65788c"
TEAL = "#007f73"
ORANGE = "#b66b17"
COVER = "#e6f0f8"
COVER_EDGE = "#8cacc6"
UNKNOWN = "#fff9ed"
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 12, "text.color": TEXT,
    "axes.labelcolor": TEXT, "axes.edgecolor": "#8290a0",
    "xtick.color": MUTED, "ytick.color": MUTED,
    "figure.facecolor": "white", "axes.facecolor": "white",
    "savefig.facecolor": "white", "pdf.fonttype": 42, "ps.fonttype": 42,
    "axes.unicode_minus": True,
})


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def smooth_points(bound):
    """Только целочисленные степени: 1 соответствует (0,0,0)."""
    result = []
    a, power2 = 0, 1
    while power2 <= bound:
        b, power3 = 0, 1
        while power2 * power3 <= bound:
            c, power5 = 0, 1
            while power2 * power3 * power5 <= bound:
                result.append({"a": a, "b": b, "c": c,
                               "n": power2 * power3 * power5})
                c, power5 = c + 1, power5 * 5
            b, power3 = b + 1, power3 * 3
        a, power2 = a + 1, power2 * 2
    return result


def build_inputs(root):
    benchmark_file = root / "data/benchmark_original.json"
    record_file = root / "data/record_original.json"
    benchmark, record = read_json(benchmark_file), read_json(record_file)
    points = smooth_points(120)
    plane = [{"a": p["a"], "b": p["b"], "n": p["n"] // 5,
              "original_n": p["n"]} for p in points if p["c"] == 1]
    observations = [dict(row, milliseconds=row["seconds"] * 1000)
                    for row in benchmark["observations_raw"]]
    modes = ["candidate_prime", "segmented", "mr12_candidates"]
    medians = {name: median(r["milliseconds"] for r in observations if r["mode"] == name)
               for name in modes}
    assert all(sum(r["mode"] == mode for r in observations) == 12 for mode in modes)
    exponent = record["input"]["exponent"]
    factors = record["extended_window"]["factors"][:44]
    assert len(factors) == 44 and all(factors[:43]) and factors[43] is None
    for j, factor in enumerate(factors):
        if factor is not None:
            assert (3 * pow(2, exponent, factor) + 1 - 2 * j) % factor == 0
    cells = [{"j": j, "offset_from_3P": 4 - 2 * j, "factor": p,
              "status": "COMPOSITE" if p is not None else "UNKNOWN"}
             for j, p in enumerate(factors)]
    stages = []
    for limit in (0, 3, 5, 7, 53, 139291, 1000000):
        closed = [cell["j"] for cell in cells
                  if cell["factor"] is not None and cell["factor"] <= limit]
        stages.append({"small_prime_limit": limit, "closed_indices": closed,
                       "unknown_indices": [j for j in range(44) if j not in closed],
                       "duration_seconds": 2.5})
    inputs = {
        "sources": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in (benchmark_file, record_file)},
        "prime_space": {
            "model": "H_3(120)={2^a*3^b*5^c<=120: a,b,c nonnegative integers}",
            "bound": 120, "slice_c": 1, "projected_bound": 24,
            "one_included": True, "points": points, "projected_slice": plane,
            "interpretation": "separate exponent-coordinate model, not a proof of speedup"},
        "benchmark": {
            "modes": modes, "flashes": benchmark["flashes"],
            "distinct_windows": benchmark["distinct_windows"],
            "rounds": benchmark["rounds"], "observations": observations,
            "median_milliseconds": medians, "original_contract": benchmark["contract"],
            "interpretation": "saved Python experiment; MR is deterministic below 2^64"},
        "record_window": {
            "P": record["input"]["P"], "exponent": exponent,
            "address_formula": "N_j=3P+4-2*j", "small_prime_limit": 1000000,
            "cells": cells, "closed_top_positions": 43,
            "candidate": "3P-82", "candidate_status": "UNKNOWN",
            "video_stages": stages, "final_frame_seconds": 3.5,
            "video_total_seconds": sum(s["duration_seconds"] for s in stages) + 3.5},
    }
    output = root / "data/figure_inputs.json"
    output.write_text(json.dumps(inputs, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return inputs


def save_figure(fig, output_dir, name, dpi):
    for extension in ("png", "pdf"):
        fig.savefig(output_dir / f"{name}.{extension}", dpi=dpi)
    plt.close(fig)


def prime_space_figure(data):
    fig = plt.figure(figsize=(13.6, 7.4))
    fig.suptitle("Многомерные координаты и проекция слоя", fontsize=22,
                 fontweight="bold", y=0.975)
    fig.text(0.5, 0.91,
             "Отдельная координатная модель: число задаётся показателями простых множителей",
             ha="center", fontsize=12.5, color=MUTED)
    ax = fig.add_axes([0.025, 0.17, 0.48, 0.68], projection="3d")
    other = [p for p in data["points"] if p["c"] != 1]
    layer = [p for p in data["points"] if p["c"] == 1]
    ax.scatter([p["a"] for p in other], [p["b"] for p in other],
               [p["c"] for p in other], s=32, color=BLUE, alpha=0.7, depthshade=False)
    plane = Poly3DCollection([[(0, 0, 1), (6, 0, 1), (6, 4, 1), (0, 4, 1)]],
                             alpha=0.07, facecolor=ORANGE, edgecolor=ORANGE, linewidth=1)
    ax.add_collection3d(plane)
    ax.scatter([p["a"] for p in layer], [p["b"] for p in layer],
               [p["c"] for p in layer], s=70, color=ORANGE, edgecolor="white",
               linewidth=0.6, depthshade=False)
    ax.text(0, 0, -0.15, "1", fontsize=12, color=TEXT)
    ax.set(xlim=(-0.15, 6.5), ylim=(-0.15, 4.4), zlim=(-0.15, 2.4),
           xticks=range(7), yticks=range(5), zticks=range(3))
    ax.set_xlabel("a — степень 2", labelpad=10)
    ax.set_ylabel("b — степень 3", labelpad=10)
    ax.set_zlabel("c — степень 5", labelpad=9)
    ax.set_title(r"$H_3(120)$: " + f"{len(data['points'])} точек", fontsize=16, pad=6)
    ax.view_init(elev=23, azim=-52)
    ax.tick_params(labelsize=10)
    ax.set_box_aspect((1.3, 1, 0.75))
    ax2 = fig.add_axes([0.61, 0.245, 0.33, 0.53])
    projected = data["projected_slice"]
    ax2.scatter([p["a"] for p in projected], [p["b"] for p in projected],
                s=76, color=ORANGE, zorder=3, edgecolor="white", linewidth=0.6)
    for p in projected:
        ax2.annotate(str(p["n"]), (p["a"], p["b"]), xytext=(6, 7),
                     textcoords="offset points", fontsize=12, color=TEXT)
    ax2.set(xlim=(-0.35, 4.65), ylim=(-0.3, 2.65), xticks=range(5), yticks=range(3))
    ax2.set_xlabel("a — степень 2", labelpad=10)
    ax2.set_ylabel("b — степень 3", labelpad=10)
    ax2.set_title(r"Срез $c=1$ → $H_2(24)$", fontsize=16, pad=24)
    ax2.grid(color="#dfe5ec", linewidth=0.8)
    ax2.set_axisbelow(True)
    ax2.set_aspect("equal")
    fig.text(0.76, 0.19, r"$2^a3^b5\;\mapsto\;2^a3^b,\qquad 120/5=24$",
             ha="center", fontsize=16)
    fig.legend(handles=[Line2D([], [], color=BLUE, marker="o", linestyle="", label="Остальные слои"),
                        Line2D([], [], color=ORANGE, marker="o", linestyle="", label="Слой c = 1")],
               loc="lower left", bbox_to_anchor=(0.035, 0.075), frameon=False, ncol=2, fontsize=11)
    fig.text(0.5, 0.04,
             "Включена единица: (0, 0, 0) ↔ 1. В проекции подписи показывают 2ᵃ3ᵇ; это не список простых.",
             ha="center", fontsize=11.5, color=MUTED)
    return fig


def benchmark_figure(data):
    fig, ax = plt.subplots(figsize=(12.8, 7.8))
    fig.subplots_adjust(left=0.10, right=0.96, top=0.80, bottom=0.25)
    fig.suptitle("Время полного маршрута вспышек", fontsize=22,
                 fontweight="bold", y=0.965)
    fig.text(0.5, 0.91,
             f"{data['flashes']} вспышек · {data['distinct_windows']} окно · "
             f"{data['rounds']} парных повторов · 36 измерений",
             ha="center", fontsize=14, color=MUTED)
    colors = [BLUE, SLATE, TEAL]
    labels = ["Точный кандидатный\nметод вспышек", "Сегментное решето\nсобственная Python-версия",
              "Миллер — Рабин\n12 оснований, n < 2⁶⁴"]
    for x, (mode, color) in enumerate(zip(data["modes"], colors)):
        rows = sorted((r for r in data["observations"] if r["mode"] == mode),
                      key=lambda r: r["round"])
        offsets = [-0.21 + 0.42 * i / 11 for i in range(12)]
        ax.scatter([x + o for o in offsets], [r["milliseconds"] for r in rows],
                   color=color, s=52, edgecolor="white", linewidth=0.7, zorder=4)
        med = data["median_milliseconds"][mode]
        ax.plot([x - 0.28, x + 0.28], [med, med], color=TEXT, linewidth=2.4,
                solid_capstyle="round", zorder=3)
        fig.text(0.245 + x * 0.286, 0.835,
                 f"Медиана {med:.2f} мс".replace(".", ","),
                 ha="center", fontsize=13.5, color=color, fontweight="bold")
    ax.set_yscale("log")
    ax.set(xlim=(-0.5, 2.5), ylim=(0.75, 1350), xticks=range(3), yticks=[1, 10, 100, 1000])
    ax.yaxis.set_major_formatter(ScalarFormatter())
    ax.set_xticklabels(labels, fontsize=12.5, linespacing=1.5)
    ax.set_ylabel("Время, мс · логарифмическая шкала", fontsize=13.5)
    ax.grid(axis="y", which="major", color="#dfe5ec", linewidth=0.9)
    ax.spines[["top", "right"]].set_visible(False)
    ax.tick_params(axis="x", length=0, pad=14)
    fig.text(0.10, 0.135,
             "Кружки — 12 отдельных запусков каждого движка; горизонтальная линия — медиана.",
             fontsize=12, color=MUTED)
    fig.text(0.10, 0.09,
             "Одинаковый результат: крайнее простое и закрытый суффикс. Новый базис включён во время.",
             fontsize=11.5, color=MUTED)
    fig.text(0.10, 0.045,
             "Сохранённый эксперимент 10.10.2026. С primesieve не сравнивали; MR здесь детерминированный.",
             fontsize=11.5, color=MUTED)
    return fig


def address_label(offset):
    return "3P" if offset == 0 else f"3P{'+' if offset > 0 else '−'}{abs(offset)}"


def record_figure(data, limit=1000000, video=False, stage_index=None):
    fig = plt.figure(figsize=(16, 9 if video else 8))
    fig.suptitle("Тени закрывают позиции у границы мира", fontsize=24,
                 fontweight="bold", y=0.965)
    fig.text(0.5, 0.875, r"$N_j=3P+4-2j,\quad P=2^{136\,279\,841}-1$",
             fontsize=19, ha="center")
    fig.text(0.5, 0.813, "Читаем слева направо, затем следующую строку: адреса уменьшаются на 2",
             fontsize=13, ha="center", color=MUTED)
    ax = fig.add_axes([0.035, 0.23, 0.93, 0.54])
    ax.set(xlim=(-0.05, 11.05), ylim=(-0.03, 4.04))
    ax.axis("off")
    closed_count = 0
    for cell in data["cells"]:
        j, factor = cell["j"], cell["factor"]
        covered = factor is not None and factor <= limit
        closed_count += covered
        x, y = j % 11, 3 - j // 11
        ax.add_patch(Rectangle((x + 0.035, y + 0.045), 0.93, 0.91,
                               facecolor=COVER if covered else UNKNOWN,
                               edgecolor=COVER_EDGE if covered else ORANGE,
                               linewidth=1.0 if covered else 1.5))
        ax.text(x + 0.5, y + 0.76, f"j = {j}", fontsize=11, color=MUTED, ha="center")
        ax.text(x + 0.5, y + 0.48, address_label(cell["offset_from_3P"]),
                fontsize=14, fontweight="bold", ha="center")
        ax.text(x + 0.5, y + 0.20, f"d = {factor}" if covered else "UNKNOWN",
                fontsize=11.5, color=BLUE if covered else ORANGE, ha="center")
    lim = f"{limit:,}".replace(",", " ")
    stage = f"Этап {stage_index + 1}/7  ·  " if stage_index is not None else ""
    fig.text(0.045, 0.19, f"{stage}Предел простых: {lim}  ·  Закрыто: {closed_count}/44  ·  "
             f"UNKNOWN: {44 - closed_count}", fontsize=15, fontweight="bold")
    fig.legend(handles=[Patch(facecolor=COVER, edgecolor=COVER_EDGE, label="Составное: сохранён делитель d"),
                        Patch(facecolor=UNKNOWN, edgecolor=ORANGE, label="UNKNOWN: статус простоты не установлен")],
               loc="lower left", bbox_to_anchor=(0.035, 0.103), frameon=False,
               ncol=2, fontsize=12.5, columnspacing=3)
    if limit == 1000000:
        foot = "43 позиции закрыты; следующий адрес: 3P + 4 − 2 × 43 = 3P − 82. Его простота не установлена."
    elif limit == 0:
        foot = "Начальное окно: тени ещё не наложены. Все 44 позиции имеют статус UNKNOWN."
    else:
        foot = "Найденный делитель закрывает позицию. Без делителя позиция остаётся UNKNOWN."
    fig.text(0.045, 0.055, foot, fontsize=13, color=MUTED)
    return fig


def final_video_frame():
    fig = plt.figure(figsize=(16, 9))
    fig.text(0.08, 0.86, "Результат ограниченной проверки", fontsize=30, fontweight="bold")
    fig.text(0.08, 0.70, "43 нечётные позиции подряд закрыты точными делителями.",
             fontsize=24, color=BLUE)
    fig.text(0.5, 0.48, r"$3P+4-2\times43=3P-82$", ha="center", fontsize=43)
    fig.text(0.5, 0.31, "UNKNOWN", ha="center", fontsize=30, color=ORANGE,
             bbox={"boxstyle": "round,pad=0.45", "facecolor": UNKNOWN, "edgecolor": ORANGE})
    fig.text(0.5, 0.17, "Делитель до 1 000 000 не найден. Простота кандидата не установлена.",
             ha="center", fontsize=20, color=MUTED)
    fig.text(0.5, 0.075, r"$P=2^{136\,279\,841}-1$", ha="center", fontsize=21, color=MUTED)
    return fig


def make_video(data, output_dir):
    ffmpeg = shutil.which("ffmpeg")
    if ffmpeg is None:
        raise RuntimeError("Для --video установите ffmpeg с поддержкой libx264")
    with tempfile.TemporaryDirectory(prefix="flash-worlds-frames-") as directory:
        frames_dir = Path(directory)
        entries = []
        for i, stage in enumerate(data["video_stages"]):
            frame = frames_dir / f"frame_{i:02d}.png"
            fig = record_figure(data, limit=stage["small_prime_limit"], video=True, stage_index=i)
            fig.savefig(frame, dpi=100)
            plt.close(fig)
            entries.extend([f"file '{frame.name}'", f"duration {stage['duration_seconds']}"])
        last = frames_dir / "frame_07.png"
        fig = final_video_frame()
        fig.savefig(last, dpi=100)
        plt.close(fig)
        entries.extend([f"file '{last.name}'", f"duration {data['final_frame_seconds']}",
                        f"file '{last.name}'"])
        sequence = frames_dir / "sequence.txt"
        sequence.write_text("\n".join(entries) + "\n", encoding="utf-8")
        command = [ffmpeg, "-hide_banner", "-loglevel", "error", "-y", "-f", "concat",
                   "-safe", "0", "-i", str(sequence), "-vf", "fps=25,format=yuv420p",
                   "-c:v", "libx264", "-crf", "20", "-preset", "medium", "-threads", "2",
                   "-an", "-movflags", "+faststart", "-t", str(data["video_total_seconds"]),
                   str(output_dir / "shadows_and_flash.mp4")]
        subprocess.run(command, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--video", action="store_true", help="также создать MP4 длительностью 21 с")
    parser.add_argument("--dpi", type=int, default=180, help="разрешение PNG (PDF остаётся векторным)")
    args = parser.parse_args()
    if not 72 <= args.dpi <= 600:
        parser.error("--dpi должен быть между 72 и 600")
    root = Path(__file__).resolve().parent.parent
    output_dir = root / "figures"
    output_dir.mkdir(exist_ok=True)
    inputs = build_inputs(root)
    save_figure(prime_space_figure(inputs["prime_space"]), output_dir, "prime_space_projection", args.dpi)
    save_figure(benchmark_figure(inputs["benchmark"]), output_dir, "benchmark_times", args.dpi)
    save_figure(record_figure(inputs["record_window"]), output_dir, "record_window", args.dpi)
    if args.video:
        make_video(inputs["record_window"], output_dir)
    names = [str(p.relative_to(root)) for p in sorted(output_dir.iterdir()) if p.is_file()]
    print(json.dumps({"status": "PASS", "matplotlib": matplotlib.__version__,
                      "inputs": "data/figure_inputs.json", "figures": names},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
