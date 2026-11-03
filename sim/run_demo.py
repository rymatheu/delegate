#!/usr/bin/env python3
"""Closed-loop demo: the Lean 4 flight controller flying a CF2X Crazyflie in gym-pybullet-drones.

The controller runs as a separate process (one of three backends) and talks to this script over
pipes, one line per control tick in lock-step: this script writes the vehicle state (NED, 13
numbers), the controller answers with four motor commands in [0, 1], and the commands are turned
into propeller RPMs for the simulator. No controller bundled with gym-pybullet-drones is used.

Run `.venv/bin/python run_demo.py --help` from the sim directory for the options; see README.md.
"""

from __future__ import annotations

import argparse
import csv
import math
import os
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
PKG_DIR = (SIM_DIR / "..").resolve()
# The flown mission: the CF2X gains of cf2x.txt with the figure-eight course of cf2x-course.txt.
DEFAULT_PARAMS = [SIM_DIR / "params" / "cf2x.txt", SIM_DIR / "params" / "cf2x-course.txt"]
DEFAULT_BIN = SIM_DIR / "build" / "flight-c"

CTRL_HZ = 120
PYB_HZ = 240
DT = 1.0 / CTRL_HZ

# Fixed change of basis from the simulator's world frame (ENU: x east, y north, z up) to the
# controller's world frame (NED: x north, y east, z down). It is a proper rotation (det +1), a half
# turn about the horizontal axis halfway between north and east, so it maps vectors and angular
# velocities alike.
ENU_TO_NED = np.array([[0.0, 1.0, 0.0],
                       [1.0, 0.0, 0.0],
                       [0.0, 0.0, -1.0]])
# Fixed change of basis between the URDF body frame (FLU: forward, left, up) and the controller's
# body frame (FRD: forward, right, down); also a proper rotation (half turn about forward), and its
# own inverse.
FRD_TO_FLU = np.diag([1.0, -1.0, -1.0])

# Controller motor i+1 (Flight/Types.lean) drives simulator propeller CTRL_TO_SIM[i] (cf2x.urdf).
#   m1 front-right CCW -> prop0 at (+x, -y) FLU, CCW (its drag torque enters z_torque with a minus sign)
#   m2 rear-left   CCW -> prop2 at (-x, +y) FLU, CCW
#   m3 front-left  CW  -> prop3 at (+x, +y) FLU, CW
#   m4 rear-right  CW  -> prop1 at (-x, -y) FLU, CW
CTRL_TO_SIM = [0, 2, 3, 1]


def quat_to_matrix(q):
    """Rotation matrix of a unit quaternion given as (x, y, z, w), PyBullet's order."""
    x, y, z, w = q
    return np.array([
        [1 - 2 * (y * y + z * z), 2 * (x * y - z * w), 2 * (x * z + y * w)],
        [2 * (x * y + z * w), 1 - 2 * (x * x + z * z), 2 * (y * z - x * w)],
        [2 * (x * z - y * w), 2 * (y * z + x * w), 1 - 2 * (x * x + y * y)],
    ])


def zyx_euler(R):
    """ZYX Euler angles (roll, pitch, yaw) of a rotation matrix R = Rz(yaw) Ry(pitch) Rx(roll)."""
    roll = math.atan2(R[2, 1], R[2, 2])
    pitch = math.asin(max(-1.0, min(1.0, -R[2, 0])))
    yaw = math.atan2(R[1, 0], R[0, 0])
    return roll, pitch, yaw


def enu_state_to_ned(pos, quat, vel, ang_vel_world):
    """Convert one PyBullet state (ENU world, FLU body) to the controller's NED/FRD quantities.

    Returns position and velocity (NED), ZYX Euler angles of the FRD body in NED, and body rates
    (p, q, r) about the FRD axes.
    """
    R_enu_flu = quat_to_matrix(quat)                      # FLU body -> ENU world
    R_ned_frd = ENU_TO_NED @ R_enu_flu @ FRD_TO_FLU       # FRD body -> NED world
    pos_ned = ENU_TO_NED @ np.asarray(pos)
    vel_ned = ENU_TO_NED @ np.asarray(vel)
    omega_ned = ENU_TO_NED @ np.asarray(ang_vel_world)    # PyBullet reports world-frame angular velocity
    rates_frd = R_ned_frd.T @ omega_ned                   # body rates are its body-frame components
    return pos_ned, vel_ned, zyx_euler(R_ned_frd), rates_frd


def fmt(x: float) -> str:
    """Shortest round-trip decimal of a double, which the Lean parser reads (no inf or nan)."""
    return repr(float(x))


# --------------------------------------------------------------------------------------------
# Controller process


def backend_command(backend: str, bin_path: Path, ctrl_args: list[str]) -> tuple[list[str], Path]:
    if backend == "lake":
        return ["lake", "exe", "flight", *ctrl_args], PKG_DIR
    if backend == "bin":
        return [str(bin_path), *ctrl_args], SIM_DIR
    if backend == "interp":
        return ["lake", "env", "lean", "--run", "Flight/Main.lean", *ctrl_args], PKG_DIR
    raise ValueError(backend)


class Controller:
    """A controller process in lock-step: one state line in, one motor line out."""

    def __init__(self, cmd: list[str], cwd: Path):
        self.proc = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1)

    def step(self, line: str) -> tuple[str, float]:
        t0 = time.perf_counter()
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        out = self.proc.stdout.readline()
        elapsed = time.perf_counter() - t0
        if not out:
            raise RuntimeError(f"controller exited (code {self.proc.poll()})")
        return out.strip(), elapsed

    def close(self):
        try:
            self.proc.stdin.close()
        except BrokenPipeError:
            pass
        self.proc.wait(timeout=30)


def effective_params(cmd_prefix: list[str], cwd: Path) -> dict:
    """Ask the controller itself for its effective waypoints and navigator parameters."""
    out = subprocess.run([*cmd_prefix, "--print-params"], cwd=cwd, check=True, capture_output=True,
                         text=True).stdout
    wps, nav = [], {}
    for line in out.splitlines():
        ws = line.split()
        if ws and ws[0] == "waypoint":
            wps.append(tuple(float(v) for v in ws[1:5]))
        elif ws and ws[0].startswith("nav."):
            nav[ws[0][4:]] = float(ws[1])
    return {"waypoints": wps, "accept_radius": nav.get("acceptRadius"), "nav": nav, "text": out}


# --------------------------------------------------------------------------------------------
# Simulator


def make_env(gui: bool, init_ned=(0.0, 0.0, None), init_euler_deg=(0.0, 0.0, 0.0)):
    import contextlib
    import io
    import warnings
    warnings.filterwarnings("ignore", module="gymnasium")
    from gym_pybullet_drones.envs.CtrlAviary import CtrlAviary
    from gym_pybullet_drones.utils.enums import DroneModel, Physics

    with contextlib.redirect_stdout(io.StringIO()):   # the environment prints its URDF constants
        env = CtrlAviary(drone_model=DroneModel.CF2X, num_drones=1, physics=Physics.PYB,
                         pyb_freq=PYB_HZ, ctrl_freq=CTRL_HZ, gui=gui, record=False, obstacles=False,
                         user_debug_gui=False, output_folder=str(SIM_DIR / "out" / "pyb"))
    # Start at rest on the ground at the origin, base at half the collision cylinder's height, facing
    # north: PyBullet's yaw is measured counter-clockwise from east, so north is yaw pi/2 (NED yaw 0).
    # Optional initial position (NED; None for the ground) and attitude (NED ZYX Euler, degrees),
    # converted to PyBullet's ENU position and its (roll, pitch, yaw) of the FLU body.
    n, e, d = init_ned
    ground = env.COLLISION_H / 2 - env.COLLISION_Z_OFFSET
    env.INIT_XYZS = np.array([[e, n, ground if d is None else -d]])
    r, pt, y = (math.radians(v) for v in init_euler_deg)
    c = np.cos; sn = np.sin
    R_ned_frd = (np.array([[c(y), -sn(y), 0], [sn(y), c(y), 0], [0, 0, 1]])
                 @ np.array([[c(pt), 0, sn(pt)], [0, 1, 0], [-sn(pt), 0, c(pt)]])
                 @ np.array([[1, 0, 0], [0, c(r), -sn(r)], [0, sn(r), c(r)]]))
    R_enu_flu = ENU_TO_NED.T @ R_ned_frd @ FRD_TO_FLU
    import pybullet as pb
    from scipy.spatial.transform import Rotation
    q = Rotation.from_matrix(R_enu_flu).as_quat()  # (x, y, z, w)
    env.INIT_RPYS = np.array([pb.getEulerFromQuaternion(q)])
    return env


def motors_to_rpm(env, m: list[float]) -> np.ndarray:
    """Thrust-linear map: per-motor thrust m * T_max with T_max = kf * MAX_RPM^2, so rpm = sqrt(m T_max / kf)."""
    t_max = env.KF * env.MAX_RPM ** 2
    rpm = np.zeros(4)
    for i, mi in enumerate(m):
        rpm[CTRL_TO_SIM[i]] = math.sqrt(max(0.0, min(1.0, mi)) * t_max / env.KF)
    return np.clip(rpm, 0.0, env.MAX_RPM)


# --------------------------------------------------------------------------------------------
# Run


@dataclass
class Run:
    rows: list = field(default_factory=list)
    inputs: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    tick_s: list = field(default_factory=list)
    reached: dict = field(default_factory=dict)      # waypoint index -> time first inside tolerance
    became_target: dict = field(default_factory=dict)
    closest: dict = field(default_factory=dict)      # waypoint index -> (distance, time) of closest approach
    passed: int = 0                                  # waypoints passed in order (within pass_tol)
    hold_start: float | None = None
    end_reason: str = ""


def fly(args, cmd, cwd, mission) -> Run:
    wps, radius = mission["waypoints"], mission["accept_radius"]
    env = make_env(args.gui, (args.init_ned[0], args.init_ned[1], args.init_ned[2] if args.init_ned[2] != 0 else None)
                   if args.init_ned else (0.0, 0.0, None), args.init_euler or (0.0, 0.0, 0.0))
    obs, _ = env.reset()
    ctrl = Controller(cmd, cwd)
    run = Run()
    n_ticks = int(round(args.duration * CTRL_HZ))
    try:
        for k in range(n_ticks):
            t = k * DT
            s = obs[0]
            pos, vel, att, rates = enu_state_to_ned(s[0:3], s[3:7], s[10:13], s[13:16])
            # Waypoints passed in order, for the end of the run only; the navigator's own target is
            # logged afterwards by replaying the inputs with --trace (see `attach_trace`).
            if wps and run.passed < len(wps) and math.dist(pos, wps[run.passed][:3]) <= args.pass_tol:
                run.passed += 1
            line = " ".join(fmt(v) for v in (*pos, *vel, *att, *rates, DT))
            out, el = ctrl.step(line)
            m = [float(v) for v in out.split()]
            if len(m) != 4:
                raise RuntimeError(f"bad controller line at t={t}: {out!r}")
            run.inputs.append(line)
            run.outputs.append(out)
            run.tick_s.append(el)
            err = math.dist(pos, wps[-1][:3]) if wps else 0.0
            run.rows.append([t, *pos, *vel, *att, *rates, *m, el * 1e6])
            # Termination: crash, or last waypoint held within tolerance for `hold` seconds.
            if abs(att[0]) > math.radians(80) or abs(att[1]) > math.radians(80):
                run.end_reason = f"crash: attitude beyond 80 deg at t={t:.3f}"
                break
            if t > 1.0 and -pos[2] < 0.03 and abs(vel[2]) < 0.05:
                run.end_reason = f"on the ground at t={t:.3f}"
                break
            if wps and run.passed == len(wps) and err <= args.tol:
                if run.hold_start is None:
                    run.hold_start = t
                if t - run.hold_start >= args.hold:
                    run.end_reason = f"last waypoint held {args.hold:g} s within {args.tol:g} m"
                    break
            else:
                run.hold_start = None
            obs, *_ = env.step(motors_to_rpm(env, m).reshape(1, 4))
            if args.gui:
                time.sleep(max(0.0, DT - el))
        else:
            run.end_reason = f"time limit {args.duration:g} s"
    finally:
        ctrl.close()
        env.close()
    return run


def attach_trace(run: Run, cmd, cwd, mission, args):
    """Replay the recorded inputs with --trace, check that the motor commands are the flown ones, and
    add the navigator's output (index, position setpoint, velocity and acceleration feed-forward,
    heading setpoint) to
    every row; then derive, per waypoint, when it became the target and the closest approach."""
    lines = replay([*cmd, "--trace"], cwd, run.inputs)
    if len(lines) != len(run.outputs):
        raise RuntimeError(f"trace replay gave {len(lines)} lines for {len(run.outputs)} inputs")
    for i, (ln, out) in enumerate(zip(lines, run.outputs)):
        ws = ln.split()
        if " ".join(ws[:4]) != out:
            raise RuntimeError(f"trace replay motor line {i + 1} differs from the flight: {ln!r} vs {out!r}")
        sp, vsp, asp, ysp, idx = ws[4:7], ws[7:10], ws[10:13], ws[13], int(ws[14])
        row = run.rows[i]
        run.rows[i] = row[:17] + [idx, *map(float, sp), *map(float, vsp), *map(float, asp), float(ysp)] + row[17:]
    wps = mission["waypoints"]
    a = np.array(run.rows)
    t, nidx = a[:, 0], a[:, 17].astype(int)
    for i, wp in enumerate(wps):
        sel = np.nonzero(nidx >= i)[0]
        if len(sel):
            run.became_target[i] = t[sel[0]]
        # Closest approach while the waypoint is targeted or just passed (its corner blend
        # continues on the next leg); for the last waypoint, any time once targeted.
        win = (nidx >= i) if i == len(wps) - 1 else ((nidx == i) | (nidx == i + 1))
        d = np.linalg.norm(a[:, 1:4] - np.array(wp[:3]), axis=1)
        if win.any():
            j = int(np.argmin(np.where(win, d, np.inf)))
            run.closest[i] = (float(d[j]), float(t[j]))
        inside = np.nonzero(win & (d <= args.tol))[0]
        if len(inside):
            run.reached[i] = float(t[inside[0]])


# --------------------------------------------------------------------------------------------
# Output

FIELDS = ["t", "x_n", "y_e", "z_d", "vx_n", "vy_e", "vz_d", "roll", "pitch", "yaw", "p", "q", "r",
          "m1", "m2", "m3", "m4", "nav_index", "sp_n", "sp_e", "sp_d", "vsp_n", "vsp_e", "vsp_d",
          "asp_n", "asp_e", "asp_d", "sp_yaw",
          "tick_us"]


def write_outputs(out_dir: Path, run: Run):
    out_dir.mkdir(parents=True, exist_ok=True)
    with open(out_dir / "flight.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(FIELDS)
        w.writerows(run.rows)
    (out_dir / "inputs.txt").write_text("\n".join(run.inputs) + "\n")
    (out_dir / "motors.txt").write_text("\n".join(run.outputs) + "\n")


def summarize(run: Run, mission, args) -> list[str]:
    a = np.array(run.rows)
    wps = mission["waypoints"]
    last = wps[-1] if wps else None
    lines = [f"end: {run.end_reason}; {len(run.rows)} ticks, {a[-1, 0]:.3f} s simulated"]
    if last is not None:
        final_err = math.dist(a[-1, 1:4], last[:3])
        lines.append(f"final position error to last waypoint: {final_err * 100:.2f} cm "
                     f"(pos NED {a[-1, 1]:.4f} {a[-1, 2]:.4f} {a[-1, 3]:.4f}, yaw {math.degrees(a[-1, 9]):.2f} deg "
                     f"vs {math.degrees(last[3]):.2f})")
    tilt = np.degrees(np.arccos(np.clip(np.cos(a[:, 7]) * np.cos(a[:, 8]), -1, 1)))
    lines.append(f"max |roll| {math.degrees(np.max(np.abs(a[:, 7]))):.2f} deg, "
                 f"max |pitch| {math.degrees(np.max(np.abs(a[:, 8]))):.2f} deg, "
                 f"max tilt {np.max(tilt):.2f} deg")
    # Tracking: distance from the navigator's position setpoint once the path has started.
    on_path = a[:, 17] >= 1
    if on_path.any():
        e = np.linalg.norm(a[on_path, 1:4] - a[on_path, 18:21], axis=1)
        vs = np.linalg.norm(a[on_path, 4:7], axis=1)
        lines.append(f"on the path (nav index >= 1, {on_path.sum()} ticks): distance to the position setpoint "
                     f"max {e.max() * 100:.2f} cm, rms {np.sqrt(np.mean(e ** 2)) * 100:.2f} cm; "
                     f"max speed {vs.max():.3f} m/s")
    for i, wp in enumerate(wps):
        t0 = run.became_target.get(i)
        tr = run.reached.get(i)
        cl = run.closest.get(i)
        cl_s = f", closest {cl[0] * 100:.2f} cm at {cl[1]:.3f} s" if cl else ""
        if t0 is None:
            lines.append(f"waypoint {i} {wp[:3]}: never targeted")
        elif tr is None:
            lines.append(f"waypoint {i} {wp[:3]}: targeted at {t0:.3f} s, never within {args.tol:g} m{cl_s}")
        else:
            lines.append(f"waypoint {i} {wp[:3]}: targeted at {t0:.3f} s, within {args.tol:g} m at "
                         f"{tr:.3f} s{cl_s}")
    # Excursion after the final waypoint was first reached: max distance from it.
    if last is not None and (len(wps) - 1) in run.reached:
        after = a[a[:, 0] >= run.reached[len(wps) - 1]]
        dmax = max(math.dist(r[1:4], last[:3]) for r in after)
        lines.append(f"max distance from last waypoint after reaching it: {dmax * 100:.2f} cm")
    # The first tick includes process start-up (for lake, its build check), so it is reported apart.
    us = np.array(run.tick_s[1:]) * 1e6
    lines.append(f"controller round trip per tick (write state line, read motor line; ticks 2..): "
                 f"median {np.median(us):.1f} us, mean {us.mean():.1f} us, p99 {np.percentile(us, 99):.1f} us, "
                 f"max {us.max():.1f} us; first tick incl. start-up {run.tick_s[0] * 1e3:.1f} ms")
    return lines


def plot(out_dir: Path, run: Run, mission, title: str):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    series = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100"]
    ink, muted, grid = "#0b0b0b", "#52514e", "#e4e3df"
    plt.rcParams.update({"axes.edgecolor": muted, "axes.labelcolor": ink, "xtick.color": muted,
                         "ytick.color": muted, "axes.grid": True, "grid.color": grid,
                         "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
                         "lines.linewidth": 1.6, "font.size": 9, "legend.frameon": False})
    a = np.array(run.rows)
    t = a[:, 0]
    fig, ax = plt.subplots(4, 1, figsize=(9, 10), sharex=True, constrained_layout=True)
    for j, (name, col) in enumerate([("north x", 1), ("east y", 2), ("down z", 3)]):
        ax[0].plot(t, a[:, col], color=series[j], label=f"{name}")
        ax[0].plot(t, a[:, 18 + j], color=series[j], linestyle="--", linewidth=1.0,
                   label=f"{name} setpoint")
    ax[0].set_ylabel("position NED (m)")
    ax[0].legend(ncol=3, loc="upper left", fontsize=8)
    ax[0].set_title(title, color=ink, loc="left")
    for j, (name, col) in enumerate([("roll", 7), ("pitch", 8)]):
        ax[1].plot(t, np.degrees(a[:, col]), color=series[j], label=name)
    ax[1].axhline(30, color=muted, linewidth=0.8, linestyle=":")
    ax[1].axhline(-30, color=muted, linewidth=0.8, linestyle=":")
    ax[1].set_ylabel("roll, pitch (deg)")
    ax[1].legend(loc="upper right")
    ax[2].plot(t, np.degrees(a[:, 9]), color=series[2], label="yaw")
    ax[2].plot(t, np.degrees(a[:, 27]), color=series[2], linestyle="--", linewidth=1.0, label="yaw setpoint")
    ax[2].set_ylabel("yaw (deg)")
    ax[2].legend(loc="upper left")
    for j in range(4):
        ax[3].plot(t, a[:, 13 + j], color=series[j], linewidth=1.0, label=f"m{j + 1}")
    ax[3].set_ylabel("motor command")
    ax[3].set_xlabel("time (s)")
    ax[3].legend(ncol=4, loc="upper right")
    fig.savefig(out_dir / "timeseries.png", dpi=130)
    plt.close(fig)

    wps = mission["waypoints"]
    fig, ax = plt.subplots(1, 2, figsize=(10, 4.6), constrained_layout=True)
    ax[0].plot(a[:, 19], a[:, 18], color=series[1], linestyle="--", linewidth=1.0, label="setpoint")
    ax[0].plot(a[:, 2], a[:, 1], color=series[0], label="path")
    for i, w in enumerate(wps):
        ax[0].plot(w[1], w[0], marker="o", markersize=8, color=series[1], linestyle="none",
                   label="waypoints" if i == 0 else None)
        ax[0].annotate(f"wp{i}", (w[1], w[0]), textcoords="offset points", xytext=(6, 6), color=ink)
    ax[0].set_xlabel("east (m)")
    ax[0].set_ylabel("north (m)")
    ax[0].set_aspect("equal", adjustable="datalim")
    ax[0].set_title("top-down path", color=ink, loc="left")
    ax[0].legend(loc="lower right")
    horiz = np.hypot(a[:, 1], a[:, 2])
    ax[1].plot(t, -a[:, 3], color=series[0], label="altitude")
    ax[1].plot(t, -a[:, 20], color=series[0], linestyle="--", linewidth=1.0, label="altitude setpoint")
    ax[1].plot(t, horiz, color=series[2], label="horizontal distance from origin")
    ax[1].set_xlabel("time (s)")
    ax[1].set_ylabel("m")
    ax[1].set_title("altitude and horizontal range", color=ink, loc="left")
    ax[1].legend(loc="lower right")
    fig.savefig(out_dir / "path.png", dpi=130)
    plt.close(fig)


# --------------------------------------------------------------------------------------------
# Determinism


def replay(cmd, cwd, inputs: list[str]) -> list[str]:
    """Feed a recorded state stream to a backend in one go and return its motor lines."""
    res = subprocess.run(cmd, cwd=cwd, input="\n".join(inputs) + "\n", capture_output=True,
                         text=True, check=True)
    return res.stdout.splitlines()


def replay_cost(cmd, cwd, inputs: list[str], copies: int = 20) -> float:
    """Seconds per line when a backend processes the recorded stream (repeated) in one batch, start-up
    subtracted via a one-line run; this is the controller's own cost without the lock-step pipe latency."""
    def timed(lines):
        t0 = time.perf_counter()
        subprocess.run(cmd, cwd=cwd, input="\n".join(lines) + "\n", capture_output=True, text=True, check=True)
        return time.perf_counter() - t0
    big = inputs * copies
    return max(0.0, timed(big) - timed(inputs[:1])) / len(big)


def diff_count(a: list[str], b: list[str]) -> tuple[int, int | None]:
    n = max(len(a), len(b))
    d = [i for i in range(n) if i >= len(a) or i >= len(b) or a[i] != b[i]]
    return len(d), (d[0] if d else None)


def max_abs_diff(a: list[str], b: list[str]) -> float:
    m = 0.0
    for la, lb in zip(a, b):
        for x, y in zip(la.split(), lb.split()):
            m = max(m, abs(float(x) - float(y)))
    return m


def fly_backend(args, backend: str, ctrl_args: list[str], out_dir: Path | None = None) -> Run:
    """Fly the mission with one backend, write CSV, raw streams, summary and plots, and print the summary."""
    cmd, cwd = backend_command(backend, Path(args.bin), ctrl_args)
    mission = effective_params(cmd, cwd)
    run = fly(args, cmd, cwd, mission)
    attach_trace(run, cmd, cwd, mission, args)
    out_dir = out_dir or SIM_DIR / "out" / backend
    write_outputs(out_dir, run)
    lines = [f"backend {backend}: {' '.join(cmd)} (cwd {cwd})"] + summarize(run, mission, args)
    (out_dir / "summary.txt").write_text("\n".join(lines) + "\n")
    if not args.no_plots:
        plot(out_dir, run, mission, f"Lean flight controller, CF2X in gym-pybullet-drones ({backend} backend)")
    print("\n".join(lines), flush=True)
    return run


def determinism(args, ctrl_args):
    backends = ["lake", "bin", "interp"]
    runs = {}
    for b in backends:
        runs[b] = fly_backend(args, b, ctrl_args)
    report = []
    ref = runs["lake"]
    for b in ["bin", "interp"]:
        n, first = diff_count(ref.outputs, runs[b].outputs)
        report.append(f"closed loop lake vs {b}: {len(ref.outputs)} vs {len(runs[b].outputs)} motor lines, "
                      f"{n} differ" + (f" (first at line {first + 1}, max |diff| "
                                        f"{max_abs_diff(ref.outputs, runs[b].outputs):.3e})" if n else ""))
    # Open-loop replay of the lake run's recorded inputs through every backend.
    outs = {}
    for b in backends:
        cmd, cwd = backend_command(b, Path(args.bin), ctrl_args)
        outs[b] = replay(cmd, cwd, ref.inputs)
    for b in ["bin", "interp"]:
        n, first = diff_count(outs["lake"], outs[b])
        report.append(f"replay of lake inputs, lake vs {b}: {len(outs['lake'])} lines, {n} differ"
                      + (f" (first at line {first + 1})" if n else ""))
    n, _ = diff_count(outs["lake"], ref.outputs)
    report.append(f"replay vs live lake run: {n} lines differ")
    for b in backends:
        cmd, cwd = backend_command(b, Path(args.bin), ctrl_args)
        report.append(f"batch cost per tick ({b}, parse + step + exact print, no pipe round trip): "
                      f"{replay_cost(cmd, cwd, ref.inputs) * 1e6:.1f} us")
    text = "\n".join(report)
    (SIM_DIR / "out" / "determinism.txt").write_text(text + "\n")
    print(text)


# --------------------------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--backend", choices=["lake", "bin", "interp"], default="lake",
                    help="lake: `lake exe flight`; bin: the binary compiled from Lean's C; interp: `lean --run`")
    ap.add_argument("--bin", default=str(DEFAULT_BIN), help="path of the C-route binary (bin backend)")
    ap.add_argument("--params", action="append", default=None, metavar="FILE",
                    help="parameter file passed to the controller (repeatable, read in order; default "
                         "params/cf2x.txt then params/cf2x-course.txt)")
    ap.add_argument("--set", action="append", default=[], metavar="'KEY VALUE...'",
                    help="extra parameter override passed to the controller (repeatable)")
    ap.add_argument("--duration", type=float, default=30.0, help="simulated seconds (default 30)")
    ap.add_argument("--hold", type=float, default=3.0, help="stop after the last waypoint is held this long (s)")
    ap.add_argument("--tol", type=float, default=0.1, help="waypoint tolerance sphere radius (m)")
    ap.add_argument("--pass-tol", type=float, default=0.2,
                    help="a waypoint counts as passed (for ending the run) within this distance (m)")
    ap.add_argument("--init-ned", type=float, nargs=3, metavar=("N", "E", "D"),
                    help="initial position in NED meters (D = 0 means resting on the ground)")
    ap.add_argument("--init-euler", type=float, nargs=3, metavar=("ROLL", "PITCH", "YAW"),
                    help="initial attitude, NED ZYX Euler angles in degrees (default level, facing north)")
    ap.add_argument("--gui", action="store_true", help="show the PyBullet GUI (paced to real time)")
    ap.add_argument("--out", default=None, help="output directory (default out/<backend>)")
    ap.add_argument("--no-plots", action="store_true")
    ap.add_argument("--determinism", action="store_true",
                    help="fly all three backends and compare their motor command streams")
    args = ap.parse_args()

    ctrl_args = ["--exact"]
    for f in args.params or [str(f) for f in DEFAULT_PARAMS]:
        ctrl_args += ["--params", str(Path(f).resolve())]
    for s in args.set:
        ctrl_args += ["--set", s]

    if args.determinism:
        determinism(args, ctrl_args)
        return

    fly_backend(args, args.backend, ctrl_args, Path(args.out) if args.out else None)

if __name__ == "__main__":
    main()
