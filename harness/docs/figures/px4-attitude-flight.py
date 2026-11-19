"""PX4 on the gorge simulator: take-off and level hold with the real EKF2 in the loop.
Data: data/px4_att_loop_noise.csv, every fourth tick of a 20 s run of the composed harness
px4_att_loop (plant_sim, sensors, EKF2, attitude, rate, allocator; sensor noise on).
Run from this folder: python px4-attitude-flight.py"""
import csv, math, glob, os
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
S1, S2 = "#2a78d6", "#eb6834"          # reference categorical slots 1 and 2

here = os.path.dirname(os.path.abspath(__file__))
rows = list(csv.DictReader(open(os.path.join(here, "data", "px4_att_loop_noise.csv"))))
t = [float(r["t_us"]) / 1e6 for r in rows]
height = [-(float(r["pos_d"]) - float(rows[0]["pos_d"])) for r in rows]

def tilt(x, y):                       # angle between body z and world z, degrees
    return math.degrees(math.acos(max(-1.0, min(1.0, 1 - 2 * (x * x + y * y)))))

true_tilt = [tilt(float(r["q2"]), float(r["q3"])) for r in rows]
est = [(tt, tilt(float(r["vehicle_attitude_q_1"]), float(r["vehicle_attitude_q_2"])))
       for tt, r in zip(t, rows) if float(r["vehicle_attitude_q_0"]) != 0.0 and tt >= 10.5]
motors = [[float(r[f"actuator_motors_control_{i}"]) for r in rows] for i in range(4)]

fig, ax = plt.subplots(3, 1, figsize=(9.6, 6.6), sharex=True,
                       gridspec_kw={"height_ratios": [1.15, 1, 1], "hspace": 0.16})
events = [(2.0, "armed"), (10.5, "EKF valid"), (12.0, "take-off")]
for a in ax:
    for x, _ in events:
        a.axvline(x, color="#b9b8b2", lw=0.9, ls=(0, (3, 3)), zorder=0)
for (x, name), y in zip(events, (0.93, 0.93, 0.78)):
    ax[0].text(x + 0.12, y, name, transform=ax[0].get_xaxis_transform(), fontsize=10, color=MUTED,
               va="top")

ax[0].plot(t, height, color=NAVY, lw=2.2)
ax[0].set_ylabel("height (m)")
ax[1].plot(t, true_tilt, color=S1, lw=1.7, label="true tilt")
ax[1].plot([p[0] for p in est], [p[1] for p in est], color=S2, lw=1.3, label="EKF2 estimate, once valid")
ax[1].set_ylabel("tilt from level (deg)")
ax[1].set_ylim(0, 2.0)
ax[1].legend(frameon=False, ncol=2, loc="upper left", fontsize=10.5, handlelength=1.5)
for m in motors:
    ax[2].plot(t, m, color=NAVY, lw=1.0, alpha=0.85)
ax[2].set_ylabel("motor commands (0 to 1)")
ax[2].set_ylim(0, 1)
ax[2].set_xlabel("time (s)")
ax[2].set_xlim(0, 20)
ax[2].text(0.012, 0.86, "four motors", transform=ax[2].transAxes, fontsize=10, color=MUTED)

fig.suptitle("PX4 flies the X500 in the gorge simulator, under the harness", x=0.125, y=0.985,
             ha="left", fontsize=17, fontweight="bold", color=INK)
fig.text(0.125, 0.905, "real, unmodified PX4 v1.17.0:  sensors  ·  EKF2  ·  mc_att_control  ·  "
         "mc_rate_control  ·  control_allocator", fontsize=10.5, color=MUTED)
fig.text(0.125, 0.018, "8,000 ticks at 400 Hz, sensor noise on  ·  0 contract violations  ·  "
         "every harness's assumption met at every tick", fontsize=10.5, color=INK)
fig.subplots_adjust(top=0.865, bottom=0.135)
out = os.path.join(here, "px4-attitude-flight")
fig.savefig(out + ".pdf"); fig.savefig(out + ".png", dpi=200)
after = [x for tt, x in zip(t, true_tilt) if tt > 13.4]
print("height max", round(max(height), 1), "tilt after liftoff max", round(max(after), 2),
      "rms", round((sum(x * x for x in after) / len(after)) ** 0.5, 2), "est points", len(est))
