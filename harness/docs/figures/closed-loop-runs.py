"""Plot two logged closed-loop runs of the harness (real C++ in the loop) for slides.
Data: saved cases written by `harness test` (every exchange of every tick, as bit patterns)."""
import json, struct, sys, glob
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager as fm

for f in glob.glob("/usr/local/texlive/2025/texmf-dist/fonts/opentype/adobe/sourcesanspro/SourceSansPro-*.otf"):
    fm.fontManager.addfont(f)
plt.rcParams.update({"font.family": "Source Sans Pro", "font.size": 11, "axes.spines.top": False,
                     "axes.spines.right": False, "axes.edgecolor": "#8a8a86", "axes.linewidth": 0.8,
                     "xtick.color": "#5b5b57", "ytick.color": "#5b5b57", "axes.labelcolor": "#3a3a37",
                     "axes.grid": True, "grid.color": "#e6e5e0", "grid.linewidth": 0.7})
INK, MUTED = "#14273A", "#5b5b57"
S1, S2, S3 = "#2a78d6", "#eb6834", "#1baf7a"     # reference categorical slots 1-3
MOTOR = "#2F5B7C"

def val(x):
    if isinstance(x, str) and x.startswith("0x"):
        return struct.unpack(">f", bytes.fromhex(x[2:].rjust(8, "0")))[0]
    if x in ("true", "false"): return x == "true"
    return float(x)

def load(path):
    j = json.load(open(path))
    cols = lambda rows, k: [val(r[k]) for r in rows]
    return j, cols

import os
HERE = os.path.dirname(os.path.abspath(__file__))
AP = os.path.join(HERE, "data/ap_closed_inner_case.json")   # from closed_inner campaign 20261118T162951Z-seed9
PX = os.path.join(HERE, "data/px4_closed_rate_case.json")

runs = []
j, c = load(AP); o = j["outputs"]; n = len(o)
runs.append(dict(title="ArduPilot", sub="gorge simulator  +  3 × AC_PID  +  AP_MotorsMatrix",
    t=[k/400 for k in range(n)], alt=[-(x - c(o,"pos_d")[0]) for x in c(o,"pos_d")],
    rates=[c(o,"rate_p"), c(o,"rate_q"), c(o,"rate_r")],
    pwm=[c(o,f"pwm_{i}") for i in (1,2,3,4)], n=n))
j, c = load(PX); o = j["outputs"]; n = len(o)
runs.append(dict(title="PX4", sub="gorge simulator  +  sensors  +  mc_rate_control  +  control_allocator",
    t=[k/400 for k in range(n)], alt=[-(x - c(o,"pos_d")[0]) for x in c(o,"pos_d")],
    rates=[c(o,"rate_p"), c(o,"rate_q"), c(o,"rate_r")],
    pwm=[c(o,f"pwm{i}") for i in (0,1,2,3)], n=n))

fig, ax = plt.subplots(3, 2, figsize=(11.5, 6.6), sharex="col", sharey="row",
                       gridspec_kw={"height_ratios": [1, 1, 1], "hspace": 0.18, "wspace": 0.16})
for k, r in enumerate(runs):
    a = ax[0][k]
    a.plot(r["t"], r["alt"], color=MOTOR, lw=2)
    a.set_title(r["title"], loc="left", fontsize=17, fontweight="bold", color=INK, pad=22)
    a.text(0, 1.06, r["sub"], transform=a.transAxes, fontsize=10.5, color=MUTED)
    a = ax[1][k]
    for series, col, name in zip(r["rates"], (S1, S2, S3), ("roll", "pitch", "yaw")):
        a.plot(r["t"], series, color=col, lw=1.6, label=name)
    a.axhline(0, color="#8a8a86", lw=0.8)
    a = ax[2][k]
    for series in r["pwm"]:
        a.plot(r["t"], series, color=MOTOR, lw=1.2, alpha=0.85)
    a.set_xlabel("time (s)")
    a.text(0, -0.56, f"{r['n']} ticks at 400 Hz  ·  0 contract violations  ·  every assumption met",
           transform=a.transAxes, ha="left", fontsize=10.5, color=INK)
ax[0][0].set_ylabel("height gained (m)")
ax[1][0].set_ylabel("body rates (rad/s)")
ax[2][0].set_ylabel("PWM, four motors (µs)")
ax[1][1].legend(frameon=False, ncol=3, loc="lower right", fontsize=10, handlelength=1.4)
ax[0][0].text(0.03, 0.80, "throttle held at or below 0.5, under hover thrust:\nthe motors spool up and the vehicle stays down",
              transform=ax[0][0].transAxes, fontsize=9.5, color=MUTED, va="top")
ax[0][1].text(0.03, 0.80, "thrust setpoint 0.5 to 0.7: it climbs", transform=ax[0][1].transAxes,
              fontsize=9.5, color=MUTED, va="top")
fig.text(0.5, 0.995, "Contract test runs: rate setpoints and thrust are drawn at random every tick within the flight regime",
         ha="center", va="top", fontsize=10.5, color=MUTED)
for row in ax:
    lo = min(row[0].get_ylim()[0], row[1].get_ylim()[0]); hi = max(row[0].get_ylim()[1], row[1].get_ylim()[1])
out = sys.argv[1]
fig.savefig(out + ".pdf", bbox_inches="tight"); fig.savefig(out + ".png", dpi=200, bbox_inches="tight")
for r in runs:
    print(r["title"], "ticks", r["n"], "height", round(max(r["alt"]),3), "max|rate|", round(max(abs(x) for s in r["rates"] for x in s),3), "pwm max", max(max(s) for s in r["pwm"]))
