"""Render the verified 71 -> 211 absorption example from saved pilot data.

Requires matplotlib only; no computations or historical data are changed.
    python src/make_ripple_figure.py
Outputs figures/ripple_absorption.png (1600 x 700) and a vector PDF.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D


ROOT = Path(__file__).resolve().parent.parent
NEUTRAL = "#A5ACB7"
INK = "#243140"
MUTED = "#576675"
ABSORBED = "#C66C16"
RESIDUAL = "#007F70"


def draw_window(axis, bounds, activity):
    left, right = bounds
    addresses = list(range(left, right + 1, 2))
    assert len(addresses) == 15
    positions = {number: index for index, number in enumerate(addresses)}
    shadow = set(activity["shadow_addresses"])
    residual = set(activity["exclusive_to_later_axes_addresses"])
    larger = {row["n"]: row["later_axis"] for row in activity["later_witnesses"]}
    assert shadow <= set(addresses) and residual <= shadow

    axis.set_xlim(-0.6, 14.6)
    axis.set_ylim(-0.48, 1.22)
    axis.axis("off")
    axis.plot([0, 14], [0, 0], color="#D9DEE5", linewidth=1.5, zorder=1)
    axis.scatter(range(15), [0] * 15, s=68, color=NEUTRAL,
                 edgecolor="white", linewidth=1.0, zorder=2)
    for number in addresses:
        position = positions[number]
        color = RESIDUAL if number in residual else ABSORBED if number in shadow else MUTED
        axis.text(position, -0.20, str(number), ha="center", va="top",
                  color=color, fontsize=15 if number in residual else 12.5,
                  fontweight="bold" if number in shadow else "normal")
        if number not in shadow:
            continue
        axis.scatter([position], [0], s=225 if number in residual else 170,
                     color=color, edgecolor="white", linewidth=1.3, zorder=4)
        if number in residual:
            assert number == 625
            axis.scatter([position], [0], s=680, color=RESIDUAL, alpha=0.13, zorder=3)
            label = "Непоглощённый остаток\n" + r"$625=5^4$"
            axis.annotate(label, xy=(position, 0.08), xytext=(position, 0.90),
                          ha="center", va="center", fontsize=13.5, color=RESIDUAL,
                          fontweight="bold", linespacing=1.7,
                          bbox=dict(boxstyle="round,pad=0.55", facecolor="#EDF8F5",
                                    edgecolor="#91C8BE", linewidth=1.0),
                          arrowprops=dict(arrowstyle="-", color=RESIDUAL, linewidth=1.3))
            axis.text(position, 0.34, "большей оси нет", ha="center", va="center",
                      color=RESIDUAL, fontsize=10.5,
                      bbox=dict(facecolor="white", edgecolor="none", pad=1.5))
        else:
            later = larger[number]
            assert later > 5 and number % later == 0
            label = "Заменяющая ось " + str(later) + "\n" + str(number) + " = " + str(later) + " · " + str(number // later)
            axis.annotate(label, xy=(position, 0.08), xytext=(position, 0.81),
                          ha="center", va="center", fontsize=12, color=color,
                          linespacing=1.6,
                          arrowprops=dict(arrowstyle="-", color=color, linewidth=1.2))


def render(data_path, output_dir):
    data = json.loads(data_path.read_text(encoding="utf-8"))
    example = data["additional_valid_flash_transition"]
    assert (example["old_B"], example["next_B"]) == (71, 211)
    assert example["old_axis_5"]["state"] == "absorbed_by_larger_axes"
    assert example["new_axis_5"]["exclusive_to_later_axes_addresses"] == [625]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 12,
                         "pdf.fonttype": 42, "ps.fonttype": 42,
                         "axes.unicode_minus": False})
    figure = plt.figure(figsize=(16, 7), dpi=100, facecolor="white")
    figure.text(0.04, 0.952, "Ось 5: поглощение и возврат в следующей вспышке",
                ha="left", va="top", color=INK, fontsize=21, fontweight="bold")
    figure.text(0.04, 0.895,
                "Точный переход 71 → 211. В каждом окне показаны 15 нечётных адресов.",
                ha="left", va="top", color=MUTED, fontsize=12)

    figure.text(0.04, 0.822, "Мир B = 71   ·   I = [189, 217]",
                color=INK, fontsize=14, fontweight="bold")
    figure.text(0.365, 0.822, "Весь след 5 закрыт более крупными простыми осями",
                color=MUTED, fontsize=12)
    top_axis = figure.add_axes([0.04, 0.535, 0.925, 0.25])
    draw_window(top_axis, example["old_window"], example["old_axis_5"])

    figure.add_artist(Line2D([0.04, 0.965], [0.495, 0.495],
                             transform=figure.transFigure, color="#E6E9ED", linewidth=1.0))
    figure.text(0.04, 0.468, "Мир B = 211   ·   I = [609, 637]",
                color=INK, fontsize=14, fontweight="bold")
    figure.text(0.365, 0.468, "625 возвращает ось 5 в непоглощённый слой",
                color=MUTED, fontsize=12)
    bottom_axis = figure.add_axes([0.04, 0.18, 0.925, 0.25])
    draw_window(bottom_axis, example["new_window"], example["new_axis_5"])

    legend = [Line2D([], [], marker="o", linestyle="none", markersize=8,
                      color=NEUTRAL, label="Остальные адреса окна"),
              Line2D([], [], marker="o", linestyle="none", markersize=9,
                      color=ABSORBED, label="След 5: покрыт большей осью"),
              Line2D([], [], marker="o", linestyle="none", markersize=10,
                      color=RESIDUAL, label="След 5: непоглощённый остаток")]
    figure.legend(handles=legend, loc="lower left", bbox_to_anchor=(0.04, 0.073),
                  ncol=3, frameon=False, fontsize=11.5,
                  handletextpad=0.55, columnspacing=2.5, borderaxespad=0)
    figure.text(0.04, 0.032,
                "Остаток после больших осей состоит из чисел с наибольшим простым делителем 5. Источник: data/ripple_depth.json.",
                color=MUTED, fontsize=10.5)
    output_dir.mkdir(parents=True, exist_ok=True)
    png_path = output_dir / "ripple_absorption.png"
    pdf_path = output_dir / "ripple_absorption.pdf"
    figure.savefig(png_path, dpi=100, facecolor="white")
    figure.savefig(pdf_path, facecolor="white", metadata={
        "Title": "Ось 5: поглощение и возврат в следующей вспышке",
        "Subject": "Exact saved example from data/ripple_depth.json",
        "CreationDate": None, "ModDate": None})
    plt.close(figure)
    return png_path, pdf_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=ROOT / "data/ripple_depth.json")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "figures")
    args = parser.parse_args()
    png_path, pdf_path = render(args.data, args.output_dir)
    print(json.dumps(dict(png=str(png_path.resolve()), pdf=str(pdf_path.resolve()),
                          pixels=[1600, 700]), ensure_ascii=False))


if __name__ == "__main__":
    main()
