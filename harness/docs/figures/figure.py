#!/usr/bin/env python3
"""Draws decomposition.png: ArduCopter cut into modules, each a C++ executable inside a Lean wrapper (matplotlib only)."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

OUT = Path(__file__).resolve().parent
INK, MUTED, LINE = "#1f2933", "#52606d", "#9aa5b1"
BLUE, BLUE_F = "#1d4ed8", "#e8efff"
GREEN, GREEN_F = "#15803d", "#e7f6ec"
AMBER, AMBER_F = "#b45309", "#fdf1dc"
GREY_F = "#eceff2"
plt.rcParams.update({"font.family": "DejaVu Sans"})

fig, ax = plt.subplots(figsize=(14, 7.4), dpi=160)
ax.set_xlim(0, 14); ax.set_ylim(0, 7.4); ax.axis("off"); fig.subplots_adjust(0, 0, 1, 1)

def rbox(x, y, w, h, edge, face, lw=1.6, dashed=False, r=0.12):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle=f"round,pad=0,rounding_size={r}", linewidth=lw, edgecolor=edge,
                                facecolor=face, linestyle=(0, (5, 3)) if dashed else "solid"))
def arrow(p, q, color=INK, lw=1.6, dashed=False):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=13, linewidth=lw, color=color, shrinkA=1, shrinkB=1,
                                 linestyle=(0, (5, 3)) if dashed else "solid"))
def text(x, y, s, size=10, color=INK, bold=False, ha="center", va="center"):
    ax.text(x, y, s, fontsize=size, color=color, fontweight="bold" if bold else "normal", ha=ha, va=va)

text(0.35, 7.05, "ArduCopter as modules, each inside a Lean wrapper", 15, bold=True, ha="left")

# proof bar
rbox(0.35, 5.75, 13.3, 0.8, AMBER, AMBER_F)
text(7.0, 6.28, "Composition proof (Lean):  the module contracts  +  the plant's contract   ⟹   the system contract", 11.5, bold=True)
text(7.0, 5.97, "no code appears in this proof; each module contract is a named hypothesis with its evidence attached", 9.5, MUTED)

# modules
mods = [("Estimator", "EKF3, AHRS"), ("Guidance", "modes, WPNav"), ("Position\ncontrol", "AC_PosControl"),
        ("Attitude\ncontrol", "AC_AttitudeControl"), ("Rate\ncontrol", "AC_PID"), ("Mixer", "AP_Motors")]
flows = ["state\nestimate", "targets", "angles,\nthrust", "rate\ntargets", "torques"]
W, H, GAP, X0, Y0 = 1.58, 2.25, 0.72, 0.46, 2.55
xs = [X0 + i * (W + GAP) for i in range(6)]
for i, ((name, src), x) in enumerate(zip(mods, xs)):
    rbox(x, Y0, W, H, BLUE, BLUE_F, lw=1.8)                               # Lean wrapper
    text(x + W / 2, Y0 + H - 0.2, "Lean wrapper", 8.5, BLUE, bold=True)
    rbox(x + 0.16, Y0 + 0.72, W - 0.32, 1.12, INK, GREY_F, lw=1.3, r=0.08)     # the C++ executable
    text(x + W / 2, Y0 + 1.47, name, 10.5, bold=True)
    text(x + W / 2, Y0 + 0.93, src, 7.2, MUTED)
    text(x + W / 2, Y0 + 0.5, "contract · monitor", 8.2, BLUE)
    text(x + W / 2, Y0 + 0.24, "evidence record", 8.2, BLUE)
    arrow((x + W / 2, Y0 + H), (x + W / 2, 5.75), AMBER, 1.1, dashed=True)
for i in range(5):
    xa, xb = xs[i] + W, xs[i + 1]
    arrow((xa, Y0 + 1.28), (xb, Y0 + 1.28))
    text((xa + xb) / 2, Y0 + 1.28 + (0.34 if "\n" in flows[i] else 0.2), flows[i], 7.4, MUTED)

# supervisor
sx = xs[1]
rbox(sx - 0.25, 4.98, W + 0.5, 0.5, BLUE, BLUE_F, lw=1.4); text(sx + W / 2, 5.23, "Supervisor: mode, arming", 8.4, bold=True)
# (drawn inside the band between modules and proof bar: shift modules' dashed arrow for Guidance is hidden behind it)
arrow((sx + W / 2, 4.98), (sx + W / 2, Y0 + H), INK, 1.3)

# plant
rbox(3.0, 0.55, 8.0, 1.05, GREEN, GREEN_F, lw=1.8)
text(7.0, 1.25, "Plant", 11, bold=True)
text(7.0, 0.9, "the X500 in the simulator;  in Lean: its equations of motion and their theorems", 9, MUTED)
xm = xs[5] + W / 2; xe = xs[0] + W / 2
ax.plot([xm, xm], [Y0, 1.08], color=INK, lw=1.6); arrow((xm, 1.08), (11.0, 1.08))
text(xm + 0.12, 1.95, "motor\ncommands", 8, MUTED, ha="left")
ax.plot([3.0, xe], [1.08, 1.08], color=INK, lw=1.6); arrow((xe, 1.08), (xe, Y0))
text(xe - 0.12, 1.95, "sensor\nsamples", 8, MUTED, ha="right")

# legend
rbox(0.35, 0.12, 0.34, 0.22, INK, GREY_F, lw=1.1, r=0.04); text(0.8, 0.23, "real ArduPilot C++, compiled as its own executable", 8.6, MUTED, ha="left")
rbox(5.6, 0.12, 0.34, 0.22, BLUE, BLUE_F, lw=1.3, r=0.04); text(6.05, 0.23, "Lean: runs the executable in lock-step, checks its contract every tick, keeps its evidence", 8.6, MUTED, ha="left")
fig.savefig(OUT / "decomposition.png", facecolor="white"); print("wrote", OUT / "decomposition.png")
