"""PX4 on the gorge simulator, armed through its real commander: take-off, hold and a 10 m step,
flown by the composed harness px4_cmd_loop (plant_sim, test driver, sim bridges, sensors, rate,
allocator, EKF2, attitude, flight mode manager, position, land detector, commander), noise on.
Data: data/px4_cmd_loop_noise.csv, every fourth tick of the recorded campaign case (seed 1) of
`harness test px4_cmd_loop --cases 1 --steps 14000 --seed 1 --regime x500_cmd_step_noise`.
Run from this folder: python px4-position-flight.py"""
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
rows = list(csv.DictReader(open(os.path.join(here, "data", "px4_cmd_loop_noise.csv"))))
num = lambda r, k: float(r[k]) if r[k] not in ("", "nan", "NaN") else math.nan
t = [num(r, "time_s") for r in rows]
T_EKF, T_ARM, T_STEP = 10.48, 12.0, 25.0      # from the run's event summary
i_arm = min(range(len(t)), key=lambda i: abs(t[i] - T_ARM))
z_home = num(rows[i_arm], "vehicle_local_position_z")   # commander takes home at arming
d0 = num(rows[0], "pos_d")
h_true = [-(num(r, "pos_d") - d0) for r in rows]
valid = [tt >= T_EKF for tt in t]
h_est = [-(num(r, "vehicle_local_position_z") - z_home) if v else math.nan for r, v in zip(rows, valid)]
h_sp = [-(num(r, "trajectory_setpoint_position_2") - z_home) if tt >= T_ARM else math.nan
        for r, tt in zip(rows, t)]
n_true = [num(r, "pos_n") for r in rows]
n_est = [num(r, "vehicle_local_position_x") if v else math.nan for r, v in zip(rows, valid)]
n_sp = [num(r, "trajectory_setpoint_position_0") if tt >= T_ARM else math.nan for r, tt in zip(rows, t)]

events = [(T_EKF, "EKF2 valid", "right"), (T_ARM, "armed by commander", "left"),
          (T_STEP, "10 m step", "left")]
fig, ax = plt.subplots(2, 1, figsize=(9.6, 6.1), sharex=True, gridspec_kw={"hspace": 0.14})
for a in ax:
    for x, _, _ in events:
        a.axvline(x, color="#b9b8b2", lw=0.9, ls=(0, (3, 3)), zorder=0)
for x, name, side in events:
    ax[0].text(x - 0.15 if side == "right" else x + 0.15, 0.95, name,
               transform=ax[0].get_xaxis_transform(), fontsize=10, color=MUTED, va="top", ha=side)

SP = {"color": "#9a9993", "lw": 1.3, "ls": (0, (1, 2))}
ax[0].plot(t, h_sp, **SP, label="setpoint from the flight mode manager")
ax[0].plot(t, h_true, color=S1, lw=2.0, label="true")
ax[0].plot(t, h_est, color=S2, lw=1.4, label="EKF2 estimate")
ax[0].set_ylabel("height above start (m)")
ax[0].set_ylim(-0.3, 3.0)
handles, labels = ax[0].get_legend_handles_labels()
ax[0].legend([handles[1], handles[2], handles[0]], [labels[1], labels[2], labels[0]], frameon=False,
             loc="lower right", bbox_to_anchor=(1.0, 0.05), fontsize=10.5, handlelength=1.6)

ax[1].plot(t, n_sp, **SP)
ax[1].plot(t, n_true, color=S1, lw=2.0)
ax[1].plot(t, n_est, color=S2, lw=1.4)
ax[1].set_ylabel("distance north (m)")
ax[1].set_ylim(-0.8, 11.8)
ax[1].set_yticks([0, 5, 10])
ax[1].set_xlabel("time since boot (s)")
ax[1].set_xlim(8, 35)

fig.suptitle("PX4 holds position and flies a 10 m step, composed from harnesses", x=0.125,
             y=0.985, ha="left", fontsize=17, fontweight="bold", color=INK)
fig.text(0.125, 0.905, "unmodified PX4 v1.17.0:  commander  ·  EKF2  ·  sensors  ·  flight mode manager"
         "  ·  land detector  ·  position  ·  attitude  ·  rate  ·  allocator", fontsize=10,
         color=MUTED)
fig.text(0.125, 0.058, "14,000 ticks at 400 Hz, sensor noise on  ·  0 contract violations  ·  every "
         "harness's assumption met at every tick", fontsize=10.5, color=INK)
fig.text(0.125, 0.02, "the navigator is not in this loop yet: a test driver sends the arm command "
         "and the hold position", fontsize=9.5, color=MUTED)
fig.subplots_adjust(top=0.855, bottom=0.2)
out = os.path.join(here, "px4-position-flight")
fig.savefig(out + ".pdf"); fig.savefig(out + ".png", dpi=200)
hold = [(a, b) for a, b, tt in zip(h_true, h_est, t) if 22 <= tt <= 25]
print("z_home", round(z_home, 3), "hold true height", round(sum(a for a, _ in hold) / len(hold), 2),
      "hold EKF height", round(sum(b for _, b in hold) / len(hold), 2), "final north",
      round(n_true[-1], 2))
