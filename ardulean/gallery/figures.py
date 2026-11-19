#!/usr/bin/env python3
"""Draws the two structure figures of the gallery (matplotlib only, its bundled DejaVu Sans font).

    python gallery/figures.py [OUT_DIR]      (default: this file's folder)
"""
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
INK, MUTED, LINE = "#1f2933", "#52606d", "#9aa5b1"
BLUE, BLUE_F = "#1d4ed8", "#e8efff"      # Lean code
GREEN, GREEN_F = "#15803d", "#e7f6ec"    # simulator / plant
AMBER, AMBER_F = "#b45309", "#fdf1dc"    # proofs
GREY_F = "#f3f4f6"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 12})


def box(ax, x, y, w, h, title, lines=(), edge=INK, face="white", dashed=False, title_size=13):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.12", linewidth=1.6,
                                edgecolor=edge, facecolor=face, linestyle=(0, (5, 3)) if dashed else "solid"))
    n = len(lines)
    top = y + h / 2 + 0.17 * n
    ax.text(x + w / 2, top, title, ha="center", va="center", fontsize=title_size, fontweight="bold", color=INK)
    for i, s in enumerate(lines):
        ax.text(x + w / 2, top - 0.36 * (i + 1), s, ha="center", va="center", fontsize=10.5, color=MUTED)


def arrow(ax, p, q, label=None, color=INK, both=False, dy=0.16, dashed=False, lw=1.6, ha="center"):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="<|-|>" if both else "-|>", mutation_scale=14, linewidth=lw,
                                 color=color, shrinkA=2, shrinkB=2, linestyle=(0, (5, 3)) if dashed else "solid"))
    if label:
        ax.text((p[0] + q[0]) / 2, (p[1] + q[1]) / 2 + dy, label, ha=ha, va="center", fontsize=10, color=MUTED)


def canvas(w, h):
    fig, ax = plt.subplots(figsize=(w, h), dpi=160)
    ax.set_xlim(0, w)
    ax.set_ylim(0, h)
    ax.axis("off")
    fig.subplots_adjust(0, 0, 1, 1)
    return fig, ax


def architecture():
    fig, ax = canvas(12, 5.6)
    ax.text(0.3, 5.25, "From ArduCopter to a flight in the simulator", fontsize=15, fontweight="bold", color=INK)
    # build row
    ax.text(0.3, 4.72, "BUILD", fontsize=9.5, color=MUTED, fontweight="bold")
    box(ax, 0.3, 3.3, 2.6, 1.2, "ArduCopter", ("C++ source", "(ArduPilot)"), face=GREY_F)
    box(ax, 4.0, 3.3, 3.6, 1.2, "Flight code in Lean 4", ("vehicle: modes, navigation, control,", "MAVLink  ·  estimator: EKF3"),
        edge=BLUE, face=BLUE_F)
    box(ax, 8.9, 3.3, 2.8, 1.2, "ardulean", ("one native executable",), edge=BLUE, face=BLUE_F)
    arrow(ax, (2.9, 3.9), (4.0, 3.9), "translate")
    arrow(ax, (7.6, 3.9), (8.9, 3.9), "lake build")
    # run row
    ax.plot([0.3, 11.7], [2.75, 2.75], color=LINE, linewidth=0.8)
    ax.text(0.3, 2.42, "FLY", fontsize=9.5, color=MUTED, fontweight="bold")
    box(ax, 0.3, 0.5, 3.4, 1.6, "Simulator", ("PyBullet physics", "the gorge, one or two X500s"), edge=GREEN, face=GREEN_F)
    box(ax, 4.9, 0.5, 2.6, 1.6, "ardulean", ("one process", "per vehicle"), edge=BLUE, face=BLUE_F)
    box(ax, 8.7, 0.5, 3.0, 1.6, "QGroundControl", ("plan, upload, arm,", "start the mission"), face=GREY_F)
    arrow(ax, (3.7, 1.62), (4.9, 1.62), "sensors", dy=0.2)
    arrow(ax, (4.9, 0.98), (3.7, 0.98), "motors", dy=-0.22)
    arrow(ax, (7.5, 1.3), (8.7, 1.3), "MAVLink", both=True, dy=0.2)
    ax.text(8.1, 0.92, "UDP 14550", ha="center", va="center", fontsize=9, color=MUTED)
    arrow(ax, (10.3, 3.3), (6.6, 2.1), color=LINE, dashed=True, lw=1.2)
    ax.text(10.45, 3.0, "the same file", ha="left", va="center", fontsize=9, color=MUTED)
    fig.savefig(OUT / "architecture.png", facecolor="white")
    plt.close(fig)


def proofs():
    fig, ax = canvas(12, 7.0)
    ax.text(0.3, 6.65, "How the proofs are layered", fontsize=15, fontweight="bold", color=INK)
    ax.text(0.3, 6.25, "The definitions at the bottom are never edited for a proof. Each layer uses only the layers below it.",
            fontsize=10.5, color=MUTED)
    # definitions
    box(ax, 0.6, 0.4, 5.0, 1.1, "Flight code in Lean", ("the definitions: what the vehicle executes",), edge=BLUE, face=BLUE_F)
    box(ax, 6.4, 0.4, 5.0, 1.1, "Plant", ("the X500's equations of motion, over the reals",), edge=GREEN, face=GREEN_F)
    # low level
    box(ax, 0.6, 2.0, 5.0, 1.2, "Code corpus", ("theorems about each function: cases, ranges,", "effects on memory, invariants, meaning"),
        edge=AMBER, face=AMBER_F)
    box(ax, 6.4, 2.0, 5.0, 1.2, "Plant library", ("theorems about the motion: bounds, invariants,", "sensitivity to commands, exact solutions"),
        edge=AMBER, face=AMBER_F)
    # mid, high
    box(ax, 2.2, 3.7, 7.6, 0.95, "Mid level  (planned)", ("one contract per control loop, code and plant together",),
        edge=AMBER, face="white", dashed=True)
    box(ax, 2.2, 5.05, 7.6, 0.95, "Goal  (planned)", ("with bounded sensor noise, the vehicle stays in a tube around its planned path",),
        edge=INK, face="white", dashed=True)
    for x in (3.1, 8.9):
        arrow(ax, (x, 1.5), (x, 2.0))
    arrow(ax, (4.2, 3.2), (5.0, 3.7))
    arrow(ax, (7.8, 3.2), (7.0, 3.7))
    arrow(ax, (6.0, 4.65), (6.0, 5.05))
    fig.savefig(OUT / "proof-structure.png", facecolor="white")
    plt.close(fig)


architecture()
proofs()
print("wrote", OUT / "architecture.png", OUT / "proof-structure.png")
