"""ArduPilot on the gorge simulator: a GUIDED flight commanded over MAVLink, flown by the composed
harness ap_full (plant_sim, truth_est, rate_c, mixer, supervisor, guidance, position, attitude).
Data: data/ardupilot_guided_flight.csv, every fourth tick of the run
`python3 -I modules/supervisor/dev/fly.py guided --steps 12000` (no sensor noise; the estimator
stage is truth_est, which passes the simulator's true state under the estimator's names).
Run from this folder: python ardupilot-guided-flight.py"""
import csv, glob, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager as fm

for f in glob.glob("/usr/local/texlive/2025/texmf-dist/fonts/opentype/adobe/sourcesanspro/SourceSansPro-*.otf"):
    fm.fontManager.addfont(f)
plt.rcParams.update({"font.family": "Source Sans Pro", "font.size": 11.5, "axes.spines.top": False,
                     "axes.spines.right": False, "axes.edgecolor": "#8a8a86", "axes.linewidth": 0.8,
                     "xtick.color": "#5b5b57", "ytick.color": "#5b5b57", "axes.labelcolor": "#3a3a37",
                     "axes.grid": True, "grid.color": "#e6e5e0", "grid.linewidth": 0.7})
INK, MUTED, NAVY = "#14273A", "#5b5b57", "#2F5B7C"

here = os.path.dirname(os.path.abspath(__file__))
rows = list(csv.DictReader(open(os.path.join(here, "data", "ardupilot_guided_flight.csv"))))
t = [float(r["t"]) for r in rows]
height = [-(float(r["pos_d"]) - float(rows[0]["pos_d"])) for r in rows]
north = [float(r["pos_n"]) for r in rows]

def first(pred):
    return next(tt for tt, r in zip(t, rows) if pred(r))
t_guided = first(lambda r: r["mode"] == "4")
t_arm = first(lambda r: r["armed"] == "1")
t_land = first(lambda r: r["mode"] == "9")
t_disarm = 17.34                      # the driver stops at the disarm; its printed time
t_target = 7.77                       # the driver's printed time of the position target
events = [(t_arm, "arm", 0.95), (4.0, "take off to 2 m", 0.95), (t_target, "go 10 m north", 0.95),
          (t_land, "LAND", 0.95), (t_disarm, "disarmed", 0.95)]

fig, ax = plt.subplots(2, 1, figsize=(9.6, 6.1), sharex=True, gridspec_kw={"hspace": 0.14})
for a in ax:
    for x, _, _ in events:
        a.axvline(x, color="#b9b8b2", lw=0.9, ls=(0, (3, 3)), zorder=0)
for x, name, y in events:
    right = name == "disarmed"
    ax[0].text(x - 0.12 if right else x + 0.12, y, name, transform=ax[0].get_xaxis_transform(),
               fontsize=10, color=MUTED, va="top", ha="right" if right else "left")

ax[0].plot([4.0, t_land], [2, 2], color="#9a9993", lw=1.1, ls=(0, (1, 2)))
ax[0].plot(t, height, color=NAVY, lw=2.2)
ax[0].set_ylabel("height above start (m)")
ax[0].set_ylim(-0.1, 3.0)
ax[0].text(4.15, 1.93, "commanded", fontsize=10, color=MUTED, va="top")
ax[0].annotate("lands on the gorge floor,\n0.4 m higher here", xy=(16.6, 0.42),
               xytext=(17.2, 1.6), fontsize=10, color=MUTED, va="top", ha="right",
               arrowprops={"arrowstyle": "-", "color": "#9a9993", "lw": 0.8})

ax[1].plot([t_target, t[-1]], [10, 10], color="#9a9993", lw=1.1, ls=(0, (1, 2)))
ax[1].plot(t, north, color=NAVY, lw=2.2)
ax[1].set_ylabel("distance north (m)")
ax[1].set_ylim(-0.5, 11.5)
ax[1].set_yticks([0, 5, 10])
ax[1].text(t_target + 0.15, 10.25, "commanded", fontsize=10, color=MUTED)
ax[1].set_xlabel("time (s)")
ax[1].set_xlim(0, 18)

fig.suptitle("ArduPilot flies a commanded flight, composed from eight harnesses", x=0.125,
             y=0.985, ha="left", fontsize=17, fontweight="bold", color=INK)
fig.text(0.125, 0.90, "unmodified ArduCopter:  flight modes  ·  AC_WPNav  ·  AC_PosControl  ·  "
         "AC_AttitudeControl  ·  AC_PID  ·  AP_MotorsMatrix",
         fontsize=10.5, color=MUTED)
fig.text(0.125, 0.058, "commands sent as MAVLink messages  ·  0 guarantee violations in any harness"
         "  ·  1 assumption missed, at touchdown", fontsize=10.5, color=INK)
fig.text(0.125, 0.02, "the estimator stage here passes the simulator's true state; the EKF3 "
         "harness is verified separately and not yet in this loop", fontsize=9.5, color=MUTED)
fig.subplots_adjust(top=0.855, bottom=0.2)
out = os.path.join(here, "ardupilot-guided-flight")
fig.savefig(out + ".pdf"); fig.savefig(out + ".png", dpi=200)
print("arm", t_arm, "land", t_land, "disarm", t_disarm, "max height", round(max(height), 2),
      "final height", round(height[-1], 2), "max north", round(max(north), 2))
