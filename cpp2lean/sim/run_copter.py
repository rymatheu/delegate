#!/usr/bin/env python3
"""Closed-loop flight of a copter vehicle speaking sim/PROTOCOL.md on a CF2X in gym-pybullet-drones.

The vehicles are lean/.lake/build/bin/copter_lean (the Lean translations of ArduPilot's classes) and
build/vehicle/copter_ref (ArduPilot's classes compiled unmodified), built by ardupilot/vehicle/build.sh.
The controller runs as a separate process (`--backend bin --bin PATH`) in lock-step with this script, one
line per 400 Hz control tick: this script writes the vehicle state as ArduPilot's AHRS reports it
(NED position and velocity, the earth-frame specific force of `AP_AHRS::get_accel_ef`, the body-to-NED
attitude quaternion, the body rates and dt, 17 numbers), and the controller answers with the four
actuator outputs of the quad X motor slots 0..3, which are turned into propeller RPMs. No controller
bundled with gym-pybullet-drones is used.

`--check-frames` runs the conversion and motor-map checks against the simulator with a stub
controller (`--stub-controller`, built into this script); see README.md, "The copter driver".

Run `.venv/bin/python run_copter.py --help` from the sim directory for the options.
"""

from __future__ import annotations

import argparse
import contextlib
import csv
import io
import math
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
PKG_DIR = (SIM_DIR / ".." / "lean").resolve()

# Fixed change of basis from the simulator's world frame (ENU: x east, y north, z up) to the
# controller's world frame (NED: x north, y east, z down); a proper rotation (det +1), so it maps
# vectors and angular velocities alike.
ENU_TO_NED = np.array([[0.0, 1.0, 0.0],
                       [1.0, 0.0, 0.0],
                       [0.0, 0.0, -1.0]])
# Fixed change of basis between the URDF body frame (FLU: forward, left, up) and the controller's
# body frame (FRD: forward, right, down); also a proper rotation, and its own inverse.
FRD_TO_FLU = np.diag([1.0, -1.0, -1.0])


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
    """One PyBullet state (ENU world, FLU body) as the controller's NED/FRD quantities: position and
    velocity (NED), ZYX Euler angles of the FRD body in NED, and body rates (p, q, r) about FRD."""
    R_enu_flu = quat_to_matrix(quat)                      # FLU body -> ENU world
    R_ned_frd = ENU_TO_NED @ R_enu_flu @ FRD_TO_FLU       # FRD body -> NED world
    pos_ned = ENU_TO_NED @ np.asarray(pos)
    vel_ned = ENU_TO_NED @ np.asarray(vel)
    omega_ned = ENU_TO_NED @ np.asarray(ang_vel_world)    # PyBullet reports world-frame angular velocity
    rates_frd = R_ned_frd.T @ omega_ned                   # body rates are its body-frame components
    return pos_ned, vel_ned, zyx_euler(R_ned_frd), rates_frd


def fmt(x: float) -> str:
    """Shortest round-trip decimal of a double (no inf or nan)."""
    return repr(float(x))


DEFAULT_PARAMS = [SIM_DIR / "params" / "copter-cf2x.txt"]
DEFAULT_BIN = PKG_DIR / ".lake" / "build" / "bin" / "copter_lean"

CTRL_HZ = 400
# ArduPilot's GRAVITY_MSS (AP_Math/definitions.h). The simulator's gravity is set to it (see make_env),
# so that the specific force at rest is exactly (0, 0, -GRAVITY_MSS) and zero in free fall.
GRAVITY_MSS = 9.80665

# ArduPilot quad X motor slot i (AP_MotorsMatrix::setup_quad_matrix, MOTOR_FRAME_TYPE_X) drives
# simulator propeller SLOT_TO_SIM[i] (cf2x.urdf, FLU positions); angles from the nose, clockwise
# positive seen from above:
#   slot 0   45 deg front-right CCW -> prop0 at (+x, -y), CCW (its drag torque enters z_torque with -)
#   slot 1 -135 deg rear-left   CCW -> prop2 at (-x, +y), CCW
#   slot 2  -45 deg front-left  CW  -> prop3 at (+x, +y), CW
#   slot 3  135 deg rear-right  CW  -> prop1 at (-x, -y), CW
SLOT_TO_SIM = [0, 2, 3, 1]
SLOT_ANGLE_DEG = [45.0, -135.0, -45.0, 135.0]
SLOT_YAW = [1.0, 1.0, -1.0, -1.0]   # AP_MOTORS_MATRIX_YAW_FACTOR_CCW = 1, _CW = -1

# Quaternions are (w, x, y, z), w scalar, as ArduPilot's (q1, q2, q3, q4).
# ENU_TO_NED is the half turn about (1, 1, 0)/sqrt2, FRD_TO_FLU the half turn about x.
Q_ENU_TO_NED = (0.0, math.sqrt(0.5), math.sqrt(0.5), 0.0)
Q_FRD_TO_FLU = (0.0, 1.0, 0.0, 0.0)


def qmul(a, b):
    """Hamilton product a * b of (w, x, y, z) quaternions; the rotation of a * b is R(a) R(b)."""
    aw, ax, ay, az = a
    bw, bx, by, bz = b
    return (aw * bw - ax * bx - ay * by - az * bz,
            aw * bx + ax * bw + ay * bz - az * by,
            aw * by - ax * bz + ay * bw + az * bx,
            aw * bz + ax * by - ay * bx + az * bw)


def quat_ned_frd(q_pyb):
    """Body (FRD) to NED attitude quaternion (q1 scalar) from PyBullet's (x, y, z, w) FLU-to-ENU one:
    q = q(ENU_TO_NED) * q_enu_flu * q(FRD_TO_FLU), the quaternion form of R_ned_frd = T R_enu_flu D
    used by enu_state_to_ned. Normalized, sign chosen with q1 >= 0."""
    x, y, z, w = q_pyb
    q = qmul(qmul(Q_ENU_TO_NED, (w, x, y, z)), Q_FRD_TO_FLU)
    n = math.sqrt(sum(c * c for c in q))
    s = (1.0 if q[0] >= 0 else -1.0) / n
    return tuple(c * s for c in q)


def ap_quat_to_euler(q):
    """ArduPilot's Quaternion::to_euler (roll, pitch, yaw) of (q1, q2, q3, q4)."""
    q1, q2, q3, q4 = q
    roll = math.atan2(2.0 * (q1 * q2 + q3 * q4), 1.0 - 2.0 * (q2 * q2 + q3 * q3))
    pitch = math.asin(max(-1.0, min(1.0, 2.0 * (q1 * q3 - q4 * q2))))
    yaw = math.atan2(2.0 * (q1 * q4 + q2 * q3), 1.0 - 2.0 * (q3 * q3 + q4 * q4))
    return roll, pitch, yaw


def ap_quat_to_matrix(q):
    """ArduPilot's Quaternion::rotation_matrix (body to earth) of (q1, q2, q3, q4)."""
    w, x, y, z = q
    return quat_to_matrix((x, y, z, w))


class SpecificForce:
    """Earth-frame specific force in NED, as AP_AHRS::get_accel_ef: the vehicle's true NED acceleration
    minus the gravity vector (0, 0, +g). The acceleration is the backward difference of the NED
    velocity over the last control period, which equals the mean of the accelerations of its physics
    substeps (the differences telescope). Before the first tick there is no previous velocity; the
    vehicle starts at rest with no thrust applied yet, so the first value is (0, 0, -g) on the ground
    (held by the contact) and (0, 0, 0) in the air (free fall). An in-air start placed with
    first_accel "hover" (place) reads (0, 0, -g) instead, the specific force of a vehicle held at rest
    by its thrust: the controllers take over hovering at MOT_THST_HOVER (sim/PROTOCOL.md, run.start_hover)
    and their first actuators apply that thrust from the first physics step on."""

    def __init__(self, g: float, dt: float):
        self.g, self.dt, self.v_prev = g, dt, None

    def update(self, vel_ned, on_ground_at_start: bool):
        v = np.asarray(vel_ned, dtype=float)
        if self.v_prev is None:
            acc = np.zeros(3) if on_ground_at_start else np.array([0.0, 0.0, self.g])
        else:
            acc = (v - self.v_prev) / self.dt
        self.v_prev = v
        return acc - np.array([0.0, 0.0, self.g])


# --------------------------------------------------------------------------------------------
# Controller process


def backend_command(backend: str, bin_path: Path, ctrl_args: list[str]) -> tuple[list[str], Path]:
    if backend == "lake":
        return ["lake", "exe", "copter_lean", *ctrl_args], PKG_DIR
    if backend == "bin":
        return [str(bin_path), *ctrl_args], SIM_DIR
    if backend == "interp":
        return ["lake", "env", "lean", "--run", "VehicleMain.lean", *ctrl_args], PKG_DIR
    if backend == "stub":
        return [sys.executable, str(Path(__file__).resolve()), "--stub-controller", *ctrl_args], SIM_DIR
    raise ValueError(backend)


class Controller:
    """A controller process in lock-step: one state line in, one actuator line out."""

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
        try:
            self.proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            self.proc.kill()


def read_param_files(files: list[str], sets: list[str]) -> dict:
    """The waypoints (`waypoint N E D`, NED meters, appended in file order) and the ArduPilot parameter
    values (`NAME value`, later lines override) of the parameter files, read the way the controller
    reads them; used for the run's end condition and the summary."""
    wps, params = [], {}
    lines = []
    for f in files:
        lines += Path(f).read_text().splitlines()
    lines += sets
    for line in lines:
        ws = line.split("#", 1)[0].split()
        if not ws:
            continue
        if ws[0] == "waypoint":
            wps.append(tuple(float(v) for v in ws[1:4]))
        elif ws[0] == "mission.clear":
            wps = []
        elif len(ws) >= 2:
            params[ws[0]] = ws[1]
    return {"waypoints": wps, "params": params}


def effective_params(cmd_prefix: list[str], cwd: Path, files: list[str], sets: list[str]) -> dict:
    """The mission: from the controller's `--print-params` when it supports it (lines `waypoint N E D`),
    else from the parameter files."""
    mission = read_param_files(files, sets)
    mission["source"] = "parameter files"
    try:
        res = subprocess.run([*cmd_prefix, "--print-params"], cwd=cwd, capture_output=True, text=True,
                             input="", timeout=600)
    except subprocess.TimeoutExpired:
        return mission
    if res.returncode == 0:
        wps = [tuple(float(v) for v in ln.split()[1:4]) for ln in res.stdout.splitlines()
               if ln.split()[:1] == ["waypoint"]]
        if wps:
            mission["waypoints"] = wps
            mission["source"] = "--print-params"
            mission["text"] = res.stdout
    return mission


# --------------------------------------------------------------------------------------------
# Simulator


def make_env(gui: bool, pyb_hz: int, init_ned=(0.0, 0.0, None), init_euler_deg=(0.0, 0.0, 0.0),
             first_accel: str = "freefall"):
    import warnings
    warnings.filterwarnings("ignore", module="gymnasium")
    from gym_pybullet_drones.envs.CtrlAviary import CtrlAviary
    from gym_pybullet_drones.utils.enums import DroneModel, Physics

    with contextlib.redirect_stdout(io.StringIO()):   # the environment prints its URDF constants
        env = CtrlAviary(drone_model=DroneModel.CF2X, num_drones=1, physics=Physics.PYB,
                         pyb_freq=pyb_hz, ctrl_freq=CTRL_HZ, gui=gui, record=False, obstacles=False,
                         user_debug_gui=False, output_folder=str(SIM_DIR / "out" / "pyb"))
    # Gravity: ArduPilot's GRAVITY_MSS instead of the environment's 9.8. G is applied by
    # p.setGravity in reset(); the derived constants are recomputed as BaseAviary.__init__ does, so
    # the thrust-to-weight ratio stays 2.25 and hover is the thrust fraction 1/2.25.
    env.G = GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    place(env, init_ned, init_euler_deg, first_accel)
    return env


def place(env, init_ned=(0.0, 0.0, None), init_euler_deg=(0.0, 0.0, 0.0), first_accel: str = "freefall"):
    """Set the initial state used by the next reset: at rest at NED position init_ned with the NED ZYX
    Euler angles init_euler_deg (default level, facing north: PyBullet yaw pi/2, measured
    counter-clockwise from east). On the ground (base at half the collision cylinder's height, then
    settled by reset_env) when the down coordinate is None, and also when the requested altitude is
    below the altitude at which the vehicle rests on the ground (ground_rest_altitude, about 0.0135 m):
    there the collision cylinder would overlap the ground plane, so the vehicle starts resting on the
    ground at the requested north and east instead. Otherwise it starts in the air, at rest; its first
    specific force (SpecificForce) is free fall with first_accel "freefall" (no thrust before the first
    tick) and (0, 0, -g) with "hover" (held at rest by the hover thrust the controllers take over with)."""
    n, e, d = init_ned
    if d is not None and -d < ground_rest_altitude(env):
        d = None
    ground = env.COLLISION_H / 2 - env.COLLISION_Z_OFFSET
    env.INIT_XYZS = np.array([[e, n, ground if d is None else -d]])
    r, pt, y = (math.radians(v) for v in init_euler_deg)
    c, sn = np.cos, np.sin
    R_ned_frd = (np.array([[c(y), -sn(y), 0], [sn(y), c(y), 0], [0, 0, 1]])
                 @ np.array([[c(pt), 0, sn(pt)], [0, 1, 0], [-sn(pt), 0, c(pt)]])
                 @ np.array([[1, 0, 0], [0, c(r), -sn(r)], [0, sn(r), c(r)]]))
    R_enu_flu = ENU_TO_NED.T @ R_ned_frd @ FRD_TO_FLU
    import pybullet as pb
    from scipy.spatial.transform import Rotation
    q = Rotation.from_matrix(R_enu_flu).as_quat()  # (x, y, z, w)
    env.INIT_RPYS = np.array([pb.getEulerFromQuaternion(q)])
    env.on_ground_at_start = d is None
    env.hover_at_start = d is not None and first_accel == "hover"


def ground_rest_altitude(env) -> float:
    """Altitude of the vehicle's position when it rests on the ground, level, after reset_env's settling
    (measured once per environment at the origin and cached; about 0.0135 m for the CF2X)."""
    if getattr(env, "rest_alt", None) is None:
        env.rest_alt = 0.0                     # no recursion: place() below starts on the ground
        place(env, (0.0, 0.0, None))
        obs = reset_env(env)
        env.rest_alt = float(obs[0][2])
    return env.rest_alt


SETTLE_S = 0.25


def reset_env(env):
    """Reset the environment, remove PyBullet's default velocity damping, and let a vehicle that
    starts on the ground settle on its contact before the first control tick.

    PyBullet damps every body's linear and angular velocity by default (factor (1 - 0.04)^dt each
    step), a drag-like term that the URDF does not ask for; with it the specific force in free fall
    is -0.04 v instead of zero. Damping is set to zero, so the simulated vehicle is the rigid body of
    the thrust and drag-torque model only (no drag, ground effect or downwash, as Physics.PYB).
    The URDF puts the base on the ground plane with a slight overlap; the contact pushes it out over
    the first 20 or so control ticks (specific force transients up to 40 m/s^2). The vehicle is
    therefore stepped with the motors off for SETTLE_S seconds first; afterwards it rests with a
    contact jitter of about 0.01 m/s^2 in the specific force. The run's clock starts after that."""
    import pybullet as pb
    obs, _ = env.reset()
    pb.changeDynamics(env.DRONE_IDS[0], -1, linearDamping=0.0, angularDamping=0.0,
                      physicsClientId=env.CLIENT)
    if env.on_ground_at_start:
        for _ in range(int(SETTLE_S * CTRL_HZ)):
            obs, *_ = env.step(np.zeros((1, 4)))
    return obs


def actuators_to_rpm(env, a: list[float]) -> np.ndarray:
    """Actuator a of slot i -> thrust fraction a of the maximum per-motor thrust T_max = kf MAX_RPM^2
    (identity: the vehicles run with MOT_THST_EXPO 0, MOT_SPIN_MIN 0, MOT_SPIN_MAX 1), so the
    propeller speed is MAX_RPM sqrt(a), clipped to [0, MAX_RPM]."""
    rpm = np.zeros(4)
    for i, ai in enumerate(a):
        rpm[SLOT_TO_SIM[i]] = env.MAX_RPM * math.sqrt(max(0.0, min(1.0, ai)))
    return rpm


def sim_state(env, obs, sf: SpecificForce):
    """The controller's input quantities from one observation."""
    s = obs[0]
    pos, vel, att, rates = enu_state_to_ned(s[0:3], s[3:7], s[10:13], s[13:16])
    quat = quat_ned_frd(s[3:7])
    acc = sf.update(vel, env.on_ground_at_start or getattr(env, "hover_at_start", False))
    return pos, vel, acc, quat, att, rates


# --------------------------------------------------------------------------------------------
# Run


@dataclass
class Run:
    rows: list = field(default_factory=list)
    inputs: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    trace: list = field(default_factory=list)
    tick_s: list = field(default_factory=list)
    sim_s: float = 0.0
    wall_s: float = 0.0
    passed: int = 0
    hold_start: float | None = None
    end_reason: str = ""
    crashed: bool = False


def fly(args, cmd, cwd, mission) -> Run:
    wps = mission["waypoints"]
    init_ned = ((args.init_ned[0], args.init_ned[1], args.init_ned[2] if args.init_ned[2] != 0 else None)
                if args.init_ned else (0.0, 0.0, None))
    env = make_env(args.gui, args.pyb_hz, init_ned, args.init_euler or (0.0, 0.0, 0.0),
                   getattr(args, "init_accel", "hover"))
    obs = reset_env(env)
    dt = 1.0 / CTRL_HZ
    sf = SpecificForce(env.G, dt)
    ctrl = Controller(cmd, cwd)
    run = Run()
    n_ticks = int(round(args.duration * CTRL_HZ))
    w0 = time.perf_counter()
    try:
        for k in range(n_ticks):
            t = k * dt
            pos, vel, acc, quat, att, rates = sim_state(env, obs, sf)
            if wps and run.passed < len(wps) and math.dist(pos, wps[run.passed]) <= args.pass_tol:
                run.passed += 1
            line = " ".join(fmt(v) for v in (*pos, *vel, *acc, *quat, *rates, dt))
            out, el = ctrl.step(line)
            ws = out.split()
            try:
                m = [float(v) for v in ws[:4]]
            except ValueError:
                m = []
            if len(m) != 4:
                raise RuntimeError(f"bad controller line at tick {k} (t={t}): {out!r}")
            run.inputs.append(line)
            run.outputs.append(" ".join(ws[:4]))
            run.tick_s.append(el)
            run.rows.append([t, *pos, *vel, *acc, *quat, *att, *rates, *m, el * 1e6])
            err = math.dist(pos, wps[-1]) if wps else 0.0
            if abs(att[0]) > math.radians(80) or abs(att[1]) > math.radians(80):
                run.end_reason, run.crashed = f"crash: attitude beyond 80 deg at t={t:.4f}", True
                break
            if t > args.ground_timeout and -pos[2] < 0.03 and abs(vel[2]) < 0.05:
                run.end_reason = f"on the ground at t={t:.4f} (after {args.ground_timeout:g} s)"
                run.crashed = True
                break
            if wps and run.passed == len(wps) and err <= args.tol:
                if run.hold_start is None:
                    run.hold_start = t
                if t - run.hold_start >= args.hold:
                    run.end_reason = f"last waypoint held {args.hold:g} s within {args.tol:g} m"
                    break
            else:
                run.hold_start = None
            s0 = time.perf_counter()
            obs, *_ = env.step(actuators_to_rpm(env, m).reshape(1, 4))
            run.sim_s += time.perf_counter() - s0
            if args.gui:
                time.sleep(max(0.0, dt - el))
        else:
            run.end_reason = f"time limit {args.duration:g} s"
    finally:
        run.wall_s = time.perf_counter() - w0
        ctrl.close()
        env.close()
    return run


def attach_trace(run: Run, cmd, cwd):
    """Replay the recorded inputs with --trace and check that the first four numbers of every line are
    the flown actuator outputs; keep the rest of each line (the controller's trace fields)."""
    try:
        lines = replay([*cmd, "--trace"], cwd, run.inputs)
    except subprocess.CalledProcessError as e:
        print(f"trace replay failed (code {e.returncode}): {e.stderr.strip()[:500]}", flush=True)
        return
    if len(lines) != len(run.outputs):
        raise RuntimeError(f"trace replay gave {len(lines)} lines for {len(run.outputs)} inputs")
    for i, (ln, out) in enumerate(zip(lines, run.outputs)):
        ws = ln.split()
        if " ".join(ws[:4]) != out:
            raise RuntimeError(f"trace replay line {i + 1} differs from the flight: {ln!r} vs {out!r}")
        run.trace.append(ws[4:])


# --------------------------------------------------------------------------------------------
# Output

# The 18 trace fields of `--trace` (sim/PROTOCOL.md): AC_PosControl's position, velocity and
# acceleration targets after the tick (NED), the thrust vector, the attitude target Euler angles and
# the body-rate targets.
TRACE_FIELDS = ["sp_n", "sp_e", "sp_d", "vsp_n", "vsp_e", "vsp_d", "asp_n", "asp_e", "asp_d",
                "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
FIELDS = ["t", "x_n", "y_e", "z_d", "vx_n", "vy_e", "vz_d", "ax_n", "ay_e", "az_d",
          "q1", "q2", "q3", "q4", "roll", "pitch", "yaw", "p", "q", "r",
          "m1", "m2", "m3", "m4", "tick_us"]
C = {name: i for i, name in enumerate(FIELDS)}


def write_outputs(out_dir: Path, run: Run):
    out_dir.mkdir(parents=True, exist_ok=True)
    ntr = max((len(t) for t in run.trace), default=0)
    with open(out_dir / "flight.csv", "w", newline="") as f:
        w = csv.writer(f)
        names = TRACE_FIELDS if ntr == len(TRACE_FIELDS) else [f"trace{j}" for j in range(ntr)]
        w.writerow(FIELDS + names)
        for i, row in enumerate(run.rows):
            w.writerow(row + (run.trace[i] if i < len(run.trace) else []))
    (out_dir / "inputs.txt").write_text("\n".join(run.inputs) + "\n")
    (out_dir / "motors.txt").write_text("\n".join(run.outputs) + "\n")
    if run.trace:
        (out_dir / "trace.txt").write_text("\n".join(" ".join(t) for t in run.trace) + "\n")


def trace_array(run: Run):
    """The trace fields as an array (ticks x 18), or None if the trace is missing or of another shape."""
    if not run.trace or any(len(t) != len(TRACE_FIELDS) for t in run.trace):
        return None
    return np.array([[float(v) for v in t] for t in run.trace])


def summarize(run: Run, mission, args) -> list[str]:
    a = np.array(run.rows)
    wps = mission["waypoints"]
    t = a[:, C["t"]]
    pos = a[:, C["x_n"]:C["z_d"] + 1]
    sim_t = len(run.rows) / CTRL_HZ
    lines = [f"end: {run.end_reason}; {len(run.rows)} ticks, {sim_t:.4f} s simulated "
             f"(control {CTRL_HZ} Hz, physics {args.pyb_hz} Hz); mission from {mission['source']}"]
    if wps:
        last = wps[-1]
        lines.append(f"final position error to last waypoint: {math.dist(pos[-1], last) * 100:.2f} cm "
                     f"(pos NED {pos[-1, 0]:.4f} {pos[-1, 1]:.4f} {pos[-1, 2]:.4f}, "
                     f"yaw {math.degrees(a[-1, C['yaw']]):.2f} deg)")
    roll, pitch = a[:, C["roll"]], a[:, C["pitch"]]
    tilt = np.degrees(np.arccos(np.clip(np.cos(roll) * np.cos(pitch), -1, 1)))
    lines.append(f"max |roll| {math.degrees(np.max(np.abs(roll))):.2f} deg, "
                 f"max |pitch| {math.degrees(np.max(np.abs(pitch))):.2f} deg, max tilt {np.max(tilt):.2f} deg")
    vs = np.linalg.norm(a[:, C["vx_n"]:C["vz_d"] + 1], axis=1)
    lines.append(f"max speed {vs.max():.3f} m/s; max altitude {-pos[:, 2].min():.3f} m")
    lines.append(f"waypoints passed in order within {args.pass_tol:g} m: {run.passed} of {len(wps)}")
    # Closest approach to each waypoint in turn: waypoint i is searched from the closest approach to
    # waypoint i-1 up to the first tick that is more than halfway along the leg to waypoint i+1
    # (closer to i+1 than half the leg length); the last one up to the end.
    j0 = 0
    for i, wp in enumerate(wps):
        d = np.linalg.norm(pos - np.array(wp), axis=1)
        j1 = len(d)
        if i + 1 < len(wps):
            dn = np.linalg.norm(pos - np.array(wps[i + 1]), axis=1)
            half = 0.5 * math.dist(wp, wps[i + 1])
            past = np.nonzero(dn[j0:] < half)[0]
            if len(past):
                j1 = j0 + int(past[0]) + 1
        j = j0 + int(np.argmin(d[j0:j1]))
        inside = np.nonzero(d[j0:j1] <= args.tol)[0]
        reach = f", first within {args.tol:g} m at {t[j0 + inside[0]]:.3f} s" if len(inside) else \
            f", not within {args.tol:g} m"
        lines.append(f"waypoint {i} {wp}: closest {d[j] * 100:.2f} cm at {t[j]:.3f} s{reach}")
        j0 = j
    if wps:
        d = np.linalg.norm(pos - np.array(wps[-1]), axis=1)
        inside = np.nonzero(d[j0:] <= args.tol)[0] + j0
        if len(inside):
            lines.append(f"max distance from last waypoint after first reaching it: "
                         f"{d[inside[0]:].max() * 100:.2f} cm")
    tr = trace_array(run)
    if tr is not None:
        e = np.linalg.norm(pos - tr[:, 0:3], axis=1)
        vt = np.linalg.norm(tr[:, 3:6], axis=1)
        lines.append(f"max target speed {vt.max():.3f} m/s; max target acceleration "
                     f"{np.linalg.norm(tr[:, 6:9], axis=1).max():.3f} m/s^2")
        lines.append(f"distance to AC_PosControl's position target: max {e.max() * 100:.2f} cm, "
                     f"rms {np.sqrt(np.mean(e ** 2)) * 100:.2f} cm; max |roll - roll target| "
                     f"{math.degrees(np.abs(roll - tr[:, 12]).max()):.2f} deg, max |pitch - pitch target| "
                     f"{math.degrees(np.abs(pitch - tr[:, 13]).max()):.2f} deg")
    us = np.array(run.tick_s[1:]) * 1e6
    if len(us):
        lines.append(f"controller round trip per tick (write state line, read actuator line; ticks 2..): "
                     f"median {np.median(us):.1f} us, mean {us.mean():.1f} us, p99 {np.percentile(us, 99):.1f} us, "
                     f"max {us.max():.1f} us; first tick incl. start-up {run.tick_s[0] * 1e3:.1f} ms")
    lines.append(f"wall clock per simulated second: {run.wall_s / sim_t:.3f} s in all "
                 f"(physics {run.sim_s / sim_t:.3f} s, controller round trips {sum(run.tick_s[1:]) / sim_t:.3f} s)")
    lines.append(f"trace fields per line: {len(run.trace[0]) if run.trace else 'none'}")
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
    wps = mission["waypoints"]
    fig, ax = plt.subplots(5, 1, figsize=(9, 12), sharex=True, constrained_layout=True)
    tr = trace_array(run)
    for j, name in enumerate(["north x", "east y", "down z"]):
        ax[0].plot(t, a[:, C["x_n"] + j], color=series[j], label=name)
        if tr is not None:
            ax[0].plot(t, tr[:, j], color=series[j], linestyle="--", linewidth=1.0, label=f"{name} target")
    ax[0].set_ylabel("position NED (m)")
    ax[0].legend(ncol=3, loc="upper left", fontsize=8)
    ax[0].set_title(title, color=ink, loc="left")
    for j, name in enumerate(["roll", "pitch"]):
        ax[1].plot(t, np.degrees(a[:, C[name]]), color=series[j], label=name)
        if tr is not None:
            ax[1].plot(t, np.degrees(tr[:, 12 + j]), color=series[j], linestyle="--", linewidth=1.0,
                       label=f"{name} target")
    ax[1].set_ylabel("roll, pitch (deg)")
    ax[1].legend(loc="upper right")
    ax[2].plot(t, np.degrees(a[:, C["yaw"]]), color=series[2], label="yaw")
    if tr is not None:
        ax[2].plot(t, np.degrees(tr[:, 14]), color=series[2], linestyle="--", linewidth=1.0, label="yaw target")
    ax[2].set_ylabel("yaw (deg)")
    ax[2].legend(loc="upper left")
    for j, name in enumerate(["ax_n", "ay_e", "az_d"]):
        ax[3].plot(t, a[:, C[name]], color=series[j], linewidth=1.0, label=name)
    ax[3].set_ylabel("specific force NED (m/s^2)")
    ax[3].legend(ncol=3, loc="upper right")
    for j in range(4):
        ax[4].plot(t, a[:, C["m1"] + j], color=series[j], linewidth=1.0, label=f"slot {j}")
    ax[4].set_ylabel("actuator")
    ax[4].set_xlabel("time (s)")
    ax[4].legend(ncol=4, loc="upper right")
    fig.savefig(out_dir / "timeseries.png", dpi=130)
    plt.close(fig)

    fig, ax = plt.subplots(1, 2, figsize=(10, 4.6), constrained_layout=True)
    tr = trace_array(run)
    if tr is not None:
        ax[0].plot(tr[:, 1], tr[:, 0], color=series[1], linestyle="--", linewidth=1.0, label="position target")
    ax[0].plot(a[:, C["y_e"]], a[:, C["x_n"]], color=series[0], label="path")
    for i, w in enumerate(wps):
        ax[0].plot(w[1], w[0], marker="o", markersize=8, color=series[1], linestyle="none",
                   label="waypoints" if i == 0 else None)
        ax[0].annotate(f"wp{i}", (w[1], w[0]), textcoords="offset points", xytext=(6, 6), color=ink)
    ax[0].set_xlabel("east (m)")
    ax[0].set_ylabel("north (m)")
    ax[0].set_aspect("equal", adjustable="datalim")
    ax[0].set_title("top-down path", color=ink, loc="left")
    ax[0].legend(loc="lower right")
    ax[1].plot(t, -a[:, C["z_d"]], color=series[0], label="altitude")
    if tr is not None:
        ax[1].plot(t, -tr[:, 2], color=series[0], linestyle="--", linewidth=1.0, label="altitude target")
    ax[1].plot(t, np.hypot(a[:, C["x_n"]], a[:, C["y_e"]]), color=series[2],
               label="horizontal distance from origin")
    ax[1].set_xlabel("time (s)")
    ax[1].set_ylabel("m")
    ax[1].set_title("altitude and horizontal range", color=ink, loc="left")
    ax[1].legend(loc="lower right")
    fig.savefig(out_dir / "path.png", dpi=130)
    plt.close(fig)


# --------------------------------------------------------------------------------------------
# Determinism


def replay(cmd, cwd, inputs: list[str]) -> list[str]:
    """Feed a recorded state stream to a backend in one go and return its output lines."""
    res = subprocess.run(cmd, cwd=cwd, input="\n".join(inputs) + "\n", capture_output=True,
                         text=True, check=True)
    return res.stdout.splitlines()


def replay_cost(cmd, cwd, inputs: list[str], copies: int = 5) -> float:
    """Seconds per line for a batch run of the recorded stream (repeated), start-up subtracted."""
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


def fly_backend(args, backend: str, ctrl_args: list[str], files, out_dir: Path | None = None) -> Run:
    cmd, cwd = backend_command(backend, Path(args.bin), ctrl_args)
    mission = effective_params(cmd, cwd, files, args.set)
    run = fly(args, cmd, cwd, mission)
    out_dir = out_dir or SIM_DIR / "out" / f"copter-{backend}"
    label = f"{backend} backend" + (f", {Path(args.bin).name}" if backend == "bin" else "")
    if not args.no_trace:
        attach_trace(run, cmd, cwd)
    write_outputs(out_dir, run)
    lines = [f"{label}: {' '.join(cmd)} (cwd {cwd})"] + summarize(run, mission, args)
    if run.crashed:
        lines.append("first 20 ticks (input line -> actuator line):")
        lines += [f"  {i}: {run.inputs[i]} -> {run.outputs[i]}" for i in range(min(20, len(run.inputs)))]
    (out_dir / "summary.txt").write_text("\n".join(lines) + "\n")
    if not args.no_plots:
        plot(out_dir, run, mission, f"Copter vehicle, CF2X in gym-pybullet-drones ({label})")
    print("\n".join(lines), flush=True)
    return run


def determinism(args, ctrl_args, files):
    backends = ["lake", "bin", "interp"]
    base = Path(args.out) if args.out else SIM_DIR / "out"
    runs = {b: fly_backend(args, b, ctrl_args, files, base / f"copter-{b}") for b in backends}
    ref = runs["lake"]
    report = []
    for b in ["bin", "interp"]:
        n, first = diff_count(ref.outputs, runs[b].outputs)
        report.append(f"closed loop lake vs {b}: {len(ref.outputs)} vs {len(runs[b].outputs)} actuator lines, "
                      f"{n} differ" + (f" (first at line {first + 1})" if n else ""))
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
    (base / "copter-determinism.txt").write_text(text + "\n")
    print(text)


# --------------------------------------------------------------------------------------------
# Stub controller and frame checks


def stub_controller(argv: list[str]):
    """A stand-in for `copter`: reads protocol lines (17 numbers) and answers constant actuators,
    hover (MOT_THST_HOVER of the parameter files, default 0.4444) plus an optional open-loop
    roll/pitch/yaw/throttle offset through the quad X factors of AP_MotorsMatrix (`--rpyt R P Y T`,
    the offsets of the normalized roll, pitch, yaw and throttle inputs). With --trace it appends
    'stub'. Rejects malformed lines with exit code 2."""
    ap = argparse.ArgumentParser(prog="stub")
    ap.add_argument("--params", action="append", default=[])
    ap.add_argument("--set", action="append", default=[])
    ap.add_argument("--exact", action="store_true")
    ap.add_argument("--trace", action="store_true")
    ap.add_argument("--print-params", action="store_true")
    ap.add_argument("--rpyt", type=float, nargs=4, default=[0.0, 0.0, 0.0, 0.0])
    a = ap.parse_args(argv)
    m = read_param_files(a.params, a.set)
    if a.print_params:
        for w in m["waypoints"]:
            print("waypoint", *w)
        return
    hover = float(m["params"].get("MOT_THST_HOVER", 0.4444))
    r, p, y, t = a.rpyt
    out = []
    for ang, yf in zip(SLOT_ANGLE_DEG, SLOT_YAW):
        # add_motor(angle, yaw): roll factor cos(angle + 90), pitch factor cos(angle); normalized to 0.5
        rf = math.cos(math.radians(ang + 90.0)) / (2 * math.sqrt(0.5))
        pf = math.cos(math.radians(ang)) / (2 * math.sqrt(0.5))
        out.append(hover + t + r * rf + p * pf + y * yf * 0.5)
    ans = " ".join(repr(v) for v in out) + (" stub" if a.trace else "")
    for line in sys.stdin:
        ws = line.split()
        if len(ws) != 17:
            print(f"stub: expected 17 numbers, got {len(ws)}", file=sys.stderr)
            sys.exit(2)
        [float(v) for v in ws]
        print(ans, flush=True)


def check_frames(args):
    """Conversion and motor-map checks; prints a report (README, 'Validation')."""
    rep = []
    ok = True

    def check(name, cond, detail):
        nonlocal ok
        ok &= bool(cond)
        rep.append(f"[{'ok' if cond else 'FAIL'}] {name}: {detail}")

    # 1. Quaternion against the existing Euler conversion, for random PyBullet attitudes.
    import pybullet as pb
    rng = np.random.default_rng(1)
    worst_e = worst_r = 0.0
    for _ in range(20000):
        rpy = rng.uniform([-math.pi, -1.5, -math.pi], [math.pi, 1.5, math.pi])
        qp = pb.getQuaternionFromEuler(rpy.tolist())
        _, _, eul, _ = enu_state_to_ned([0, 0, 0], qp, [0, 0, 0], [0, 0, 0])
        q = quat_ned_frd(qp)
        e2 = ap_quat_to_euler(q)
        de = max(abs(math.remainder(x - y, 2 * math.pi)) for x, y in zip(eul, e2))
        R1 = ENU_TO_NED @ quat_to_matrix(qp) @ FRD_TO_FLU
        dr = np.abs(R1 - ap_quat_to_matrix(q)).max()
        worst_e, worst_r = max(worst_e, de), max(worst_r, dr)
    check("quaternion vs enu_state_to_ned Euler (20000 random attitudes, |pitch| < 1.5)",
          worst_e < 1e-9 and worst_r < 1e-12,
          f"max Euler difference {worst_e:.2e} rad, max matrix difference {worst_r:.2e}")
    qp = pb.getQuaternionFromEuler([0.1, 0.2, 0.3])
    q = quat_ned_frd(qp)
    e = ap_quat_to_euler(q)
    exp = (0.1, -0.2, math.pi / 2 - 0.3)
    check("known pose: PyBullet rpy (0.1, 0.2, 0.3)",
          max(abs(x - y) for x, y in zip(e, exp)) < 1e-12,
          f"q = ({', '.join(f'{c:.6f}' for c in q)}), to_euler = ({', '.join(f'{c:.6f}' for c in e)}), "
          f"expected (0.1, -0.2, pi/2 - 0.3)")
    qn = quat_ned_frd(pb.getQuaternionFromEuler([0, 0, math.pi / 2]))
    check("level, facing north (PyBullet yaw pi/2)", np.allclose(qn, (1, 0, 0, 0), atol=1e-15),
          f"q = {tuple(round(c, 15) for c in qn)}")
    qe = quat_ned_frd(pb.getQuaternionFromEuler([0, 0, 0]))
    check("level, facing east (PyBullet yaw 0)",
          np.allclose(qe, (math.sqrt(0.5), 0, 0, math.sqrt(0.5)), atol=1e-15),
          f"q = {tuple(round(c, 15) for c in qe)} (90 deg about down)")

    # 2. Simulated checks with the physics.
    def sim(init_ned, init_euler, actuators, seconds):
        env = make_env(False, args.pyb_hz, init_ned, init_euler)
        obs = reset_env(env)
        sf = SpecificForce(env.G, 1.0 / CTRL_HZ)
        hist = []
        for _ in range(int(seconds * CTRL_HZ)):
            pos, vel, acc, quat, att, rates = sim_state(env, obs, sf)
            hist.append((pos, vel, acc, quat, att, rates))
            obs, *_ = env.step(actuators_to_rpm(env, actuators).reshape(1, 4))
        env.close()
        return hist

    h = sim((0, 0, None), (0, 0, 0), [0, 0, 0, 0], 1.0)
    accs = np.array([x[2] for x in h])
    dev = np.abs(accs - [0, 0, -GRAVITY_MSS])
    check("at rest on the ground (after settling), motors off, 1 s",
          tuple(accs[0]) == (0.0, 0.0, -GRAVITY_MSS) and dev.max() < 0.05,
          f"first tick {' '.join(fmt(v) for v in accs[0])}; ticks 2.. contact jitter: max |f - (0, 0, -9.80665)| "
          f"{dev[1:].max():.2e}, mean f ({accs[1:, 0].mean():.2e}, {accs[1:, 1].mean():.2e}, {accs[1:, 2].mean():.6f})")
    h = sim((0, 0, -3), (0, 0, 0), [0, 0, 0, 0], 0.5)
    accs = np.array([x[2] for x in h])
    vz = h[-1][1][2]
    check("free fall from 3 m, motors off, 0.5 s", np.abs(accs).max() < 1e-9,
          f"max |f| {np.abs(accs).max():.2e} m/s^2; vz after 0.5 s {vz:.6f} (g t = {GRAVITY_MSS * (len(h) - 1) / CTRL_HZ:.6f})")
    hv = 1 / 2.25
    h = sim((0, 0, -1), (0, 0, 0), [hv] * 4, 1.0)
    accs = np.array([x[2] for x in h])
    pz = np.array([x[0][2] for x in h])
    check("hover actuators 1/2.25 at 1 m", np.abs(accs[1:] - [0, 0, -GRAVITY_MSS]).max() < 1e-6
          and abs(pz[-1] + 1) < 1e-6,
          f"max |f - (0, 0, -g)| (ticks 2..) {np.abs(accs[1:] - [0, 0, -GRAVITY_MSS]).max():.2e}, "
          f"z after 1 s {pz[-1]:.9f}")
    # Tilted hover thrust: f must be R_ned_frd (0, 0, -T/m) with T = 4 * hover thrust = m g.
    h = sim((0, 0, -2), (20, -10, 30), [hv] * 4, 0.1)
    errs = []
    for pos, vel, acc, quat, att, rates in h[1:]:
        R = ap_quat_to_matrix(quat)
        errs.append(np.abs(acc - R @ np.array([0, 0, -GRAVITY_MSS])).max())
    check("tilted start (roll 20, pitch -10, yaw 30 deg), hover actuators: f = R (0, 0, -g)",
          max(errs) < 0.05 * GRAVITY_MSS,
          f"max |f - R (0,0,-T/m)| {max(errs):.3e} m/s^2 over 0.1 s (no torque, so the "
          f"attitude is constant; f is the tick mean, R the tick end)")

    # Lift-off from the ground with all actuators at hover + 0.05: from the second tick on the vehicle
    # is off the contact and f = (0, 0, -4 a T_max / m) = (0, 0, -a 2.25 g).
    a_lift = hv + 0.05
    h = sim((0, 0, None), (0, 0, 0), [a_lift] * 4, 0.5)
    accs = np.array([x[2] for x in h])
    exp = -a_lift * 2.25 * GRAVITY_MSS
    dev = np.abs(accs[1:, 2] - exp).max()
    check(f"lift-off from the ground, actuators {a_lift:.4f}, 0.5 s", dev < 1e-5 and h[-1][0][2] < -0.1,
          f"f_z first tick {accs[0, 2]:.5f} (resting), then max |f_z - ({exp:.6f})| {dev:.2e}; "
          f"altitude after 0.5 s {-h[-1][0][2]:.4f} m")

    # 3. Motor map, open loop: small roll, pitch, yaw inputs through the quad X factors.
    for name, rpyt, axis in [("roll", [0.02, 0, 0, 0], 0), ("pitch", [0, 0.02, 0, 0], 1),
                             ("yaw", [0, 0, 0.05, 0], 2)]:
        acts = []
        for ang, yf in zip(SLOT_ANGLE_DEG, SLOT_YAW):
            rf = math.cos(math.radians(ang + 90.0)) / (2 * math.sqrt(0.5))
            pf = math.cos(math.radians(ang)) / (2 * math.sqrt(0.5))
            acts.append(hv + rpyt[0] * rf + rpyt[1] * pf + rpyt[2] * yf * 0.5)
        h = sim((0, 0, -2), (0, 0, 0), acts, 0.1)
        rates = np.array(h[-1][5])
        att = np.array(h[-1][4])
        others = [i for i in range(3) if i != axis]
        cond = rates[axis] > 0 and att[axis] > 0 and all(abs(rates[i]) < 1e-6 * max(1, abs(rates[axis])) + 1e-9
                                                       for i in others)
        check(f"open-loop {name} input +{max(rpyt):g} (actuators {', '.join(f'{v:.4f}' for v in acts)})", cond,
              f"after 0.1 s: (p, q, r) = ({rates[0]:.4f}, {rates[1]:.4f}, {rates[2]:.4f}) rad/s, "
              f"(roll, pitch, yaw) = ({math.degrees(att[0]):.3f}, {math.degrees(att[1]):.3f}, "
              f"{math.degrees(att[2]):.3f}) deg")

    rep.append(f"physics {args.pyb_hz} Hz, control {CTRL_HZ} Hz")
    text = "\n".join(rep)
    out = SIM_DIR / "out" / "copter-frames.txt"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text + "\n")
    print(text)
    return ok


# --------------------------------------------------------------------------------------------


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--stub-controller":
        stub_controller(sys.argv[2:])
        return
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--backend", choices=["lake", "bin", "interp", "stub"], default="lake",
                    help="lake: `lake exe copter_lean`; bin: a vehicle binary (--bin); "
                         "interp: `lean --run VehicleMain.lean`; stub: the built-in hover stub")
    ap.add_argument("--bin", default=str(DEFAULT_BIN), help="path of the vehicle binary (bin backend; copter_lean or copter_ref)")
    ap.add_argument("--params", action="append", default=None, metavar="FILE",
                    help="parameter file passed to the controller (repeatable; default params/copter-cf2x.txt)")
    ap.add_argument("--set", action="append", default=[], metavar="'NAME VALUE'",
                    help="extra parameter line passed to the controller (repeatable)")
    ap.add_argument("--stub-rpyt", type=float, nargs=4, metavar=("R", "P", "Y", "T"),
                    help="stub backend: open-loop roll, pitch, yaw, throttle offsets")
    ap.add_argument("--pyb-hz", type=int, default=1200, choices=[800, 1200, 2400],
                    help="physics rate (a multiple of the 400 Hz control rate; default 1200)")
    ap.add_argument("--duration", type=float, default=30.0, help="simulated seconds (default 30)")
    ap.add_argument("--hold", type=float, default=3.0, help="stop after the last waypoint is held this long (s)")
    ap.add_argument("--tol", type=float, default=0.1, help="waypoint tolerance sphere radius (m)")
    ap.add_argument("--pass-tol", type=float, default=0.2,
                    help="a waypoint counts as passed (for ending the run) within this distance (m)")
    ap.add_argument("--ground-timeout", type=float, default=3.0,
                    help="end the run if still (or again) on the ground after this many seconds")
    ap.add_argument("--init-ned", "--init", type=float, nargs=3, metavar=("N", "E", "D"),
                    help="initial position in NED meters, at rest (D = 0, or an altitude below the "
                         "resting height of about 0.0135 m, means resting on the ground at N, E)")
    ap.add_argument("--init-accel", choices=["hover", "freefall"], default="hover",
                    help="first specific force of an in-air start: hover (0, 0, -g), held at rest by the "
                         "hover thrust the controller takes over with (default), or freefall (0, 0, 0)")
    ap.add_argument("--init-euler", type=float, nargs=3, metavar=("ROLL", "PITCH", "YAW"),
                    help="initial attitude, NED ZYX Euler angles in degrees (default level, facing north)")
    ap.add_argument("--gui", action="store_true", help="show the PyBullet GUI (paced to real time)")
    ap.add_argument("--out", default=None, help="output directory (default out/copter-<backend>)")
    ap.add_argument("--no-plots", action="store_true")
    ap.add_argument("--no-trace", action="store_true", help="skip the --trace replay")
    ap.add_argument("--no-exact", action="store_true", help="do not pass --exact to the controller")
    ap.add_argument("--determinism", action="store_true",
                    help="fly the lake, bin and interp backends and compare their actuator streams")
    ap.add_argument("--check-frames", action="store_true",
                    help="run the conversion and motor-map checks (no controller) and exit")
    args = ap.parse_args()

    if args.check_frames:
        sys.exit(0 if check_frames(args) else 1)

    files = [str(Path(f).resolve()) for f in (args.params or [str(f) for f in DEFAULT_PARAMS])]
    ctrl_args = [] if args.no_exact else ["--exact"]
    for f in files:
        ctrl_args += ["--params", f]
    for s in args.set:
        ctrl_args += ["--set", s]
    if args.backend == "stub" and args.stub_rpyt:
        ctrl_args += ["--rpyt", *map(str, args.stub_rpyt)]

    if args.determinism:
        determinism(args, ctrl_args, files)
        return
    run = fly_backend(args, args.backend, ctrl_args, files, Path(args.out) if args.out else None)
    sys.exit(1 if run.crashed else 0)


if __name__ == "__main__":
    main()
