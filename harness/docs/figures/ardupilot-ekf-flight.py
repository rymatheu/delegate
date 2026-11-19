"""ArduPilot on the gorge simulator, flying on its own EKF3: a GUIDED flight commanded over MAVLink,
flown by the composed harness ap_full_ekf (plant_sim, estimator, rate_c, mixer, supervisor,
guidance, position, attitude) with sensor noise on (noise seed 37), IMU full scale 16 g.
Data: data/ardupilot_ekf_flight.csv, every fourth tick from 43 s of the run
`python3 -I modules/supervisor/dev/fly.py guided --node ap_full_ekf --noise --steps 32000 --csv ...`
Run from this folder: python ardupilot-ekf-flight.py"""
import csv, glob, math, os
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
INK, MUTED = "#14273A", "#5b5b57"
S1, S2 = "#2a78d6", "#eb6834"          # reference categorical slots 1 and 2

here = os.path.dirname(os.path.abspath(__file__))
rows = list(csv.DictReader(open(os.path.join(here, "data", "ardupilot_ekf_flight.csv"))))
T0 = 45.0                              # the EKF starts using GPS; the script starts
t = [float(r["t_s"]) - T0 for r in rows]
d0 = float(rows[0]["pos_d"])
h_true = [-(float(r["pos_d"]) - d0) for r in rows]
h_est = [-float(r["est_pos_d"]) for r in rows]
n_true = [float(r["pos_n"]) for r in rows]
n_est = [float(r["est_pos_n"]) for r in rows]

def first(pred):
    return next(tt for tt, r in zip(t, rows) if pred(r))
t_arm = first(lambda r: r["armed"] == "1")
t_land = first(lambda r: r["mode"] == "9")
t_target, t_disarm = 53.60 - T0, 65.08 - T0      # the driver's printed times
events = [(t_arm, "arm"), (4.0, "take off to 2 m"), (t_target, "go 10 m north"), (t_land, "LAND"),
          (t_disarm, "disarmed")]

fig, ax = plt.subplots(2, 1, figsize=(9.6, 6.1), sharex=True, gridspec_kw={"hspace": 0.14})
for a in ax:
    for x, _ in events:
        a.axvline(x, color="#b9b8b2", lw=0.9, ls=(0, (3, 3)), zorder=0)
for x, name in events:
    right = name == "disarmed"
    ax[0].text(x - 0.12 if right else x + 0.12, 0.95, name, transform=ax[0].get_xaxis_transform(),
               fontsize=10, color=MUTED, va="top", ha="right" if right else "left")

ax[0].plot([4.0, t_land], [2, 2], color="#9a9993", lw=1.1, ls=(0, (1, 2)))
ax[0].plot(t, h_true, color=S1, lw=2.0, label="true")
ax[0].plot(t, h_est, color=S2, lw=1.4, label="EKF3 estimate")
ax[0].set_ylabel("height above start (m)")
ax[0].set_ylim(-0.25, 3.0)
ax[0].text(4.15, 2.07, "commanded", fontsize=10, color=MUTED)
ax[0].legend(frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.42), fontsize=10.5,
             handlelength=1.5)

ax[1].plot([t_target, t[-1]], [10, 10], color="#9a9993", lw=1.1, ls=(0, (1, 2)))
ax[1].plot(t, n_true, color=S1, lw=2.0)
ax[1].plot(t, n_est, color=S2, lw=1.4)
ax[1].set_ylabel("distance north (m)")
ax[1].set_ylim(-0.6, 11.8)
ax[1].set_yticks([0, 5, 10])
ax[1].text(t_target + 0.15, 10.3, "commanded", fontsize=10, color=MUTED)
ax[1].set_xlabel("time since the EKF had a GPS position (s)")
ax[1].set_xlim(-2, 21)

fig.suptitle("ArduPilot flies on its own EKF, composed from eight harnesses", x=0.125, y=0.985,
             ha="left", fontsize=17, fontweight="bold", color=INK)
fig.text(0.125, 0.905, "unmodified ArduCopter:  EKF3  ·  flight modes  ·  AC_WPNav  ·  AC_PosControl"
         "  ·  AC_AttitudeControl  ·  AC_PID  ·  AP_MotorsMatrix", fontsize=10, color=MUTED)
fig.text(0.125, 0.058, "commands sent as MAVLink messages  ·  sensor noise on  ·  0 contract "
         "violations in any harness", fontsize=10.5, color=INK)
fig.text(0.125, 0.02, "26,033 ticks at 400 Hz  ·  every harness's assumption met at every tick  ·  "
         "recorded in the evidence ledger", fontsize=9.5, color=MUTED)
fig.subplots_adjust(top=0.855, bottom=0.2)
out = os.path.join(here, "ardupilot-ekf-flight")
fig.savefig(out + ".pdf"); fig.savefig(out + ".png", dpi=200)
fl = [(a, b, c, d) for a, b, c, d, r in zip(h_true, h_est, n_true, n_est, rows)
      if r["armed"] == "1" and r["land_complete"] == "0"]
print("arm", t_arm, "land", t_land, "max height", round(max(h_true), 2),
      "max |north est - true| in flight", round(max(abs(d - c) for _, _, c, d in fl), 2),
      "max |height est - true| in flight", round(max(abs(b - a) for a, b, _, _ in fl), 2))
