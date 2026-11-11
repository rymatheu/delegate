#!/usr/bin/env python3
"""Fly the leanfc mission in gym-pybullet-drones with the Lean controller in the loop.

Configuration: the controller and this harness read the same parameter files (params/*.params, format
in README.md). `--vehicle V` is shorthand for `--params params/V.params`; `--noise none` appends
params/mocap.params (100 Hz fixes, mocap navigation gains). From the files the harness takes the
control period `dt`, the fix period `dtFix` (a fix every dtFix/dt ticks), the start point, the
waypoints and their leg kinds (written to the run's JSON sidecar for analyze.py) and `SIM_VEHICLE`, which picks the
simulated airframe below.

Physics: gym-pybullet-drones `CtrlAviary` with `Physics.PYB` (PyBullet rigid body, no drag, ground
effect or downwash), 1200 Hz physics under a 400 Hz control step (3 substeps), gravity 9.80665, set
up as the cpp2lean harness does: the initial placement, the reset (no PyBullet velocity damping), the
actuator -> RPM map (RPM = MAX_RPM sqrt(m), slot map SLOT_TO_SIM) and the state extraction are
imported from sim/run_copter.py, an unmodified copy of the cpp2lean project's harness helpers (`place`, `reset_env`,
`actuators_to_rpm`, `sim_state`, `SpecificForce`, `enu_state_to_ned`, `quat_ned_frd`); `make_env`
below repeats its `make_env` with our aviary class.

Airframes (`SIM_VEHICLE`):
- cf2x: the package's assets/cf2x.urdf.
- x500: sim/assets/x500.urdf (Holybro X500 V2 from PX4's Gazebo model; sources in the URDF). The
  package has no X500 and loads its URDFs from its own assets directory, so `LeanfcAviary` overrides
  `_parseURDFParameters` to point `self.URDF` at our file before the package parses it; the package
  joins `files('gym_pybullet_drones') / 'assets' / self.URDF`, a pathlib join, so an absolute
  `self.URDF` is used as is, by the parser and by `_housekeeping`'s `loadURDF` alike. Nothing in
  the installed package or in cpp2lean is modified. The URDF keeps cf2x.urdf's propeller-link order
  (prop0 front right CCW, prop1 rear right CW, prop2 rear left CCW, prop3 front left CW, which is
  what the package's yaw-torque sum -t0 + t1 - t2 + t3 assumes), so cpp2lean's SLOT_TO_SIM sends
  motors 1..4 (front right CCW, rear left CCW, front left CW, rear right CW) to the right
  propellers; `--motor-test` checks it.

Motor lag (`--motor-lag on`, default on for the x500, off for the cf2x; no time constants are known
for the cf2x): each propeller's thrust follows its commanded thrust through a first-order lag with
time constant 0.0125 s when rising and 0.025 s when falling (PX4 gz `timeConstantUp` and
`timeConstantDown`). It is applied in `LeanfcAviary._physics`, i.e. once per 1200 Hz physics substep
(the command is held over the 3 substeps of a control step), as the exact step response of the lag
over one substep, to the thrust kf rpm^2 before it is turned back into the RPM the package applies.
The lag starts at the hover thrust (the vehicle takes over a hover). Gazebo's motor model lags the
rotor speed instead of the thrust; linearized around a speed the two time constants are the same.

Sensors: on top of the true state PyBullet returns each tick (NED position and velocity, earth-frame
specific force, body-FRD-to-NED quaternion, body rates): gyro = rates + bias + white noise; accel =
R(q)^T specific force + bias + white noise; on fix ticks heading (cos, sin of the true yaw plus
noise), position (sigma north/east, sigma down) and velocity. Per-run constant bias directions and
all noise from `numpy.random.default_rng(seed)`.

Controller: `.lake/build/bin/leanfc --params ... --calibrate 400 --trace --bits`, a separate process
in lock step, one line per tick (protocol in Main.lean): 16 sensor numbers in (17 during a dropout),
motors + trace out. The trace ends with the controller's heading setpoint (cos psi, sin psi), which goes
into the last two CSV columns, `hsp_c` and `hsp_s` (a binary without it gives a CSV without them).

Estimator and stress tests: `--estimator fixed|ekf` appends params/fixed.params or params/ekf.params
(the vehicle file's `estimator` line otherwise). `--no-calibration` draws the 400 at-rest samples as
usual (so the random sequence is unchanged) but sends none (`--calibrate 0`). `--dropout T0 T1`
withholds the position and velocity fixes for T0 <= t < T1 (the 17th number, position-fix presence,
is 0 and vfix is 0); the heading fixes continue. `--trace-ekf` asks the controller for the diagonal of
P and the two bias estimates (Main.lean) and adds them to the CSV, with the true position, velocity
and attitude at the start of the tick (the instant the estimate refers to); the true biases go into the
JSON sidecar. `--record FILE` writes every line sent to the controller (calibration samples first),
for sim/ekf_parity.py.
The vehicle starts at rest, level, heading 0 at the file's start point with the first specific force
(0, 0, -g) (`first_accel="hover"`: the controller takes over a hover); 400 at-rest gyro samples for
the calibration before the first physics step. One CSV row per tick in the format of analyze.py,
and a JSON sidecar (same name, .json) with the run's configuration and waypoints.

Ground start (`--ground`): the vehicle rests on gym-pybullet-drones' ground plane (`plane.urdf`, which
BaseAviary always loads) at the file's start north and east, level, nose north, settled on its contact
by cpp2lean's `reset_env`, motors off and the motor lag starting at zero thrust; the controller gets
`--ground` and no calibration lines: it calibrates its gyros itself from its first second of lines, as a
vehicle does at boot, and starts its estimator at the first fixes. `--realtime SPEED` paces the ticks to
the wall clock (SPEED 1: real time, 2: twice as fast); `--mav` gives the controller its MAVLink link
(`--mav-port`, default 14550, QGroundControl's; `--mav-log FILE`; `--origin LAT LON ALT`), so a ground
station can fly it. `--trace-vehicle` adds the vehicle layer's mode, armed, landed state and mission item
to every row (columns `mode armed landed item`). SIGTERM or Ctrl-C ends the run and writes the CSV.

Run: sim/.venv/bin/python sim/run_leanfc.py --vehicle x500 --noise field --seed 0 --out sim/out/run/x500-field0.csv
     sim/.venv/bin/python sim/run_leanfc.py --vehicle x500 --motor-test
"""
import argparse
import contextlib
import io
import json
import math
import signal
import struct
import subprocess
import sys
import time
import warnings
from dataclasses import dataclass
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "sim"))   # run_copter.py, copied from the cpp2lean project
from run_copter import (place, reset_env, actuators_to_rpm, sim_state, SpecificForce,  # noqa: E402
                        enu_state_to_ned, quat_ned_frd, GRAVITY_MSS, SIM_DIR, SLOT_TO_SIM)
warnings.filterwarnings("ignore", module="gymnasium")
from gym_pybullet_drones.envs.CtrlAviary import CtrlAviary  # noqa: E402
from gym_pybullet_drones.utils.enums import DroneModel, Physics  # noqa: E402

CTRL_HZ, PYB_HZ, CAL_SAMPLES = 400, 1200, 400
COLS = ("t p_n p_e p_d v_n v_e v_d q_w q_x q_y q_z ph_n ph_e ph_d vh_n vh_e vh_d qh_w qh_x qh_y qh_z "
        "sp_n sp_e sp_d leg m1 m2 m3 m4").split()
# last (when the controller prints it): the heading setpoint (cos psi, sin psi)
HSP_COLS = ["hsp_c", "hsp_s"]
# with --trace-ekf: diag P, bias estimates (body; the fixed nav filter's acceleration bias is NED), and
# the true position, velocity and attitude at the start of the tick
EKF_COLS = ([f"P{i}" for i in range(15)]
            + "bg_x bg_y bg_z ba_x ba_y ba_z pt_n pt_e pt_d vt_n vt_e vt_d qt_w qt_x qt_y qt_z".split())
# with --trace-vehicle, last: the vehicle layer's mode number, armed, landed state (MAV_LANDED_STATE) and item
VEH_COLS = ["mode", "armed", "landed", "item"]

# Simulated airframes: URDF (None = the package's cf2x.urdf), motor time constants (up, down) in s
# (None: unknown), and the default run length (s).
AIRFRAMES = {
    "cf2x": dict(urdf=None, lag=None, seconds=20.0),
    "x500": dict(urdf=ROOT / "sim/assets/x500.urdf", lag=(0.0125, 0.025), seconds=30.0),
}


# ------------------------------------------------------------------------------------------
# Parameter files


def read_params(paths):
    """Values, waypoints and SIM_VEHICLE of the files, merged as the controller merges them (later
    files override names; a file with WAYPOINT or SPLINE lines replaces the list). vals["legs"] is the
    kind of each leg ("WAYPOINT" or "SPLINE", with " stop" if marked). The controller validates the
    files; this reader takes only what the harness needs."""
    vals, wps, kinds, sim_vehicle = {}, [], [], None
    for p in paths:
        file_wps, file_kinds = [], []
        for line in Path(p).read_text().splitlines():
            ws = line.split("#", 1)[0].split()
            if not ws:
                continue
            if ws[0] == "SIM_VEHICLE":
                sim_vehicle = ws[1]
            elif ws[0] == "estimator":
                vals["estimator"] = ws[1]
            elif ws[0] in ("WAYPOINT", "SPLINE"):
                file_wps.append([float(v) for v in ws[1:4]])
                file_kinds.append(ws[0] + (" stop" if ws[4:5] == ["stop"] else ""))
            else:
                vals[ws[0]] = float(ws[1])
        if file_wps:
            wps, kinds = file_wps, file_kinds
    vals["legs"] = kinds
    return vals, wps, sim_vehicle


# ------------------------------------------------------------------------------------------
# Simulator


class LeanfcAviary(CtrlAviary):
    """CtrlAviary with a URDF from outside the package and an optional first-order motor lag."""

    def __init__(self, urdf=None, lag=None, **kw):
        self.urdf_path, self.lag = urdf, lag
        self.lag_thrust = None
        super().__init__(**kw)

    def _parseURDFParameters(self):
        if self.urdf_path is not None:
            self.URDF = str(self.urdf_path)   # absolute: files(...) / 'assets' / URDF is this path
        return super()._parseURDFParameters()

    def reset(self, *a, **kw):
        self.lag_thrust = None
        return super().reset(*a, **kw)

    def _physics(self, rpm, nth_drone):
        if self.lag is not None:
            cmd = self.KF * np.asarray(rpm, dtype=float) ** 2          # commanded thrust per propeller
            if self.lag_thrust is None:
                self.lag_thrust = (np.full(4, self.GRAVITY / 4) if getattr(self, "hover_at_start", False)
                                   else cmd.copy())
            up, down = self.lag
            tau = np.where(cmd > self.lag_thrust, up, down)
            self.lag_thrust = self.lag_thrust + (cmd - self.lag_thrust) * (1 - np.exp(-self.PYB_TIMESTEP / tau))
            rpm = np.sqrt(self.lag_thrust / self.KF)
        super()._physics(rpm, nth_drone)


def make_env(airframe, lag, init_ned, first_accel="hover"):
    """cpp2lean run_copter.make_env with LeanfcAviary: Physics.PYB, 1200 Hz physics, 400 Hz control,
    gravity 9.80665 with the derived constants recomputed as BaseAviary.__init__ does (so hover is
    the thrust fraction 1/thrust2weight), then `place`."""
    with contextlib.redirect_stdout(io.StringIO()):   # the environment prints its URDF constants
        env = LeanfcAviary(urdf=AIRFRAMES[airframe]["urdf"], lag=lag,
                           drone_model=DroneModel.CF2X, num_drones=1, physics=Physics.PYB,
                           pyb_freq=PYB_HZ, ctrl_freq=CTRL_HZ, gui=False, record=False, obstacles=False,
                           user_debug_gui=False, output_folder=str(SIM_DIR / "out" / "pyb"))
    env.G = GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    place(env, init_ned, (0.0, 0.0, 0.0), first_accel)
    return env


# ------------------------------------------------------------------------------------------
# Sensors


@dataclass
class Noise:
    """1 sigma white noise per sample and per-run bias magnitudes; the defaults are pyfc `plant.Noise`'s
    (/Users/ryan/Research/delegate/staging/pyfc/pyfc/plant.py), the field suite. velocity None: no
    velocity fix."""
    gyro: float = 0.003          # rad/s
    accel: float = 0.03          # m/s^2
    gyro_bias: float = 0.0175    # rad/s (1 deg/s)
    accel_bias: float = 0.05     # m/s^2
    position_ne: float = 0.5     # m, GPS horizontal
    position_d: float = 0.1      # m, barometer
    velocity: float = 0.1        # m/s, GPS Doppler
    heading: float = 0.035       # rad, magnetometer (2 deg)


def rot(q, v):
    """R(q) v for a (w, x, y, z) body-to-world quaternion."""
    w, x, y, z = q
    R = np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                  [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                  [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])
    return R @ np.asarray(v)


class Sensors:
    def __init__(self, noise: Noise, seed: int):
        self.n, self.rng = noise, np.random.default_rng(seed)
        def unit():
            v = self.rng.normal(size=3)
            return v / np.linalg.norm(v)
        self.gyro_bias, self.accel_bias = noise.gyro_bias * unit(), noise.accel_bias * unit()

    def sample(self, pos, vel, acc_ef, q, rates, with_fix):
        """16 numbers: gyro, accel, fix, hc, hs, position, velocity, velocity-fix presence."""
        n, rng = self.n, self.rng
        gyro = np.asarray(rates) + self.gyro_bias + rng.normal(0, n.gyro, 3)
        w, x, y, z = q
        accel = rot((w, -x, -y, -z), acc_ef) + self.accel_bias + rng.normal(0, n.accel, 3)
        if not with_fix:
            return [*gyro, *accel, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
        yaw = math.atan2(2 * (w * z + x * y), 1 - 2 * (y * y + z * z)) + n.heading * rng.normal()
        position = np.asarray(pos) + rng.normal(0, [n.position_ne, n.position_ne, n.position_d])
        if n.velocity is None:
            return [*gyro, *accel, 1.0, math.cos(yaw), math.sin(yaw), *position, 0.0, 0.0, 0.0, 0.0]
        velocity = np.asarray(vel) + rng.normal(0, n.velocity, 3)
        return [*gyro, *accel, 1.0, math.cos(yaw), math.sin(yaw), *position, *velocity, 1.0]


# ------------------------------------------------------------------------------------------
# Controller protocol


def line_of(xs):
    return " ".join(repr(float(x)) for x in xs) + "\n"


def f32bits(x):
    return struct.unpack("<I", struct.pack("<f", np.float32(x)))[0]


def parse_reply(line, n_ekf=0, n_veh=0):
    """17 binary32 numbers, the leg, n_ekf more binary32 numbers (--trace-ekf: 21) and the heading
    setpoint (2; absent from binaries older than the heading setpoint, which are still accepted), then
    n_veh integers (--trace-vehicle: 4); checks that each printed decimal round-trips to its hex word."""
    text, _, hexes = line.partition(" |")
    vals = text.split()
    if len(vals) not in (18 + n_ekf + n_veh, 20 + n_ekf + n_veh):
        raise RuntimeError(f"bad controller line: {line!r}")
    veh = [int(v) for v in vals[len(vals) - n_veh:]]
    vals = vals[:len(vals) - n_veh]
    nums = [float(v) for v in vals[:17]] + [int(vals[17])] + [float(v) for v in vals[18:]] + veh
    floats = nums[:17] + nums[18:]
    for x, h in zip(floats, hexes.split()):
        if f32bits(x) != int(h, 16) and not (x == 0 and int(h, 16) in (0, 0x80000000)):
            raise RuntimeError(f"decimal {x!r} does not round-trip to {h}")
    return nums


def param_args(files):
    return [a for f in files for a in ("--params", str(f))]


# ------------------------------------------------------------------------------------------
# Motor-sign test


def motor_test(binary, files, airframe, lags):
    """Each motor alone 0.05 above hover for 20 ms from a hover at 1 m: the signs of the measured
    body angular accelerations (FRD) must be those of the motor's column of the Lean allocation
    matrix A (`leanfc --print-params`, rows roll -y_i, pitch x_i, yaw s_i km/kf), and the specific
    force must grow upward. Returns True if every sign matches."""
    out = subprocess.run([binary, *param_args(files), "--print-params"], capture_output=True, text=True, check=True)
    A = np.zeros((4, 4))
    for ln in out.stdout.splitlines():
        ws = ln.split()
        if ws[:2] == ["#", "alloc"]:
            A[int(ws[2])] = [float(v) for v in ws[3:7]]
    ok, ticks, dm = True, 8, 0.05
    for lag in lags:
        env = make_env(airframe, lag, (0.0, 0.0, -1.0))
        h = env.GRAVITY / env.MAX_THRUST                        # hover thrust fraction
        J = np.diag(env.J)
        print(f"{airframe}, motor lag {'off' if lag is None else f'{lag[0]} s up / {lag[1]} s down'}: "
              f"hover command {h:.6f}, step +{dm} on one motor for {ticks} ticks ({ticks / CTRL_HZ * 1000:.0f} ms)")
        print("  motor  Lean A column (roll pitch yaw)   measured mean angular accel (rad/s^2)   "
              "open-loop prediction        specific force z change   signs")
        for i in range(4):
            obs = reset_env(env)
            sf = SpecificForce(env.G, 1.0 / CTRL_HZ)
            _, _, acc0, _, _, r0 = sim_state(env, obs, sf)
            cmd = [h] * 4
            cmd[i] = h + dm
            for _ in range(ticks):
                obs, *_ = env.step(actuators_to_rpm(env, cmd).reshape(1, 4))
                _, _, acc, _, _, r1 = sim_state(env, obs, sf)
            alpha = (np.asarray(r1) - np.asarray(r0)) / (ticks / CTRL_HZ)
            dT = dm * env.MAX_THRUST / 4
            pred = A[1:, i] * dT / J
            match = all(np.sign(alpha[k]) == np.sign(A[1 + k, i]) for k in range(3)) and acc[2] < acc0[2]
            ok &= match
            print(f"  {i + 1}      ({A[1, i]:+.4f} {A[2, i]:+.4f} {A[3, i]:+.4f})    "
                  f"({alpha[0]:+9.4f} {alpha[1]:+9.4f} {alpha[2]:+9.4f})          "
                  f"({pred[0]:+8.3f} {pred[1]:+8.3f} {pred[2]:+7.3f})   {acc[2] - acc0[2]:+.4f} m/s^2         "
                  f"{'ok' if match else 'MISMATCH'}")
        env.close()
    print("motor-sign test:", "PASS" if ok else "FAIL")
    return ok


# ------------------------------------------------------------------------------------------
# Run


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--vehicle", choices=sorted(AIRFRAMES), default="x500",
                    help="shorthand for --params params/VEHICLE.params (default x500)")
    ap.add_argument("--params", action="append", help="parameter file (repeatable; replaces --vehicle)")
    ap.add_argument("--noise", choices=("none", "field"), default="none")
    ap.add_argument("--motor-lag", choices=("on", "off"), default=None,
                    help="first-order motor lag (default: on if the airframe has time constants)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--seconds", type=float, default=None, help="default: 20 (cf2x), 30 (x500)")
    ap.add_argument("--out", default="sim/out/run.csv")
    ap.add_argument("--bin", default=str(ROOT / ".lake/build/bin/leanfc"))
    ap.add_argument("--motor-test", action="store_true", help="run the motor-sign test and exit")
    ap.add_argument("--estimator", choices=("fixed", "ekf"), default=None,
                    help="append params/ESTIMATOR.params (default: the vehicle file's `estimator` line)")
    ap.add_argument("--no-calibration", action="store_true",
                    help="draw the at-rest samples but send none (the random sequence is unchanged)")
    ap.add_argument("--dropout", type=float, nargs=2, metavar=("T0", "T1"),
                    help="no position or velocity fixes for T0 <= t < T1 (heading continues)")
    ap.add_argument("--trace-ekf", action="store_true",
                    help="log diag P, the bias estimates and the true start-of-tick state (extra CSV columns)")
    ap.add_argument("--record", default=None, help="write the lines sent to the controller to this file")
    ap.add_argument("--ground", action="store_true",
                    help="start resting on the ground, disarmed; the controller calibrates at boot (--ground)")
    ap.add_argument("--realtime", type=float, default=None, metavar="SPEED",
                    help="pace the ticks to the wall clock, SPEED times real time")
    ap.add_argument("--mav", action="store_true", help="give the controller its MAVLink link (--mav)")
    ap.add_argument("--mav-port", type=int, default=14550, help="the ground station's UDP port")
    ap.add_argument("--mav-log", default=None, help="the controller's MAVLink frame log")
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"),
                    help="geodetic origin for the ground station (default: the files' ORIGIN line)")
    ap.add_argument("--trace-vehicle", action="store_true",
                    help="log the vehicle layer's mode, armed, landed state and mission item")
    ap.add_argument("--ctl-arg", action="append", default=[], help="extra argument for the controller")
    a = ap.parse_args()

    files = [Path(p).resolve() for p in (a.params or [ROOT / "params" / f"{a.vehicle}.params"])]
    if a.noise == "none":
        files.append(ROOT / "params" / "mocap.params")
    if a.estimator is not None:
        files.append(ROOT / "params" / f"{a.estimator}.params")
    vals, wps, airframe = read_params(files)
    if airframe not in AIRFRAMES:
        sys.exit(f"SIM_VEHICLE {airframe!r} in {', '.join(map(str, files))}: expected one of {sorted(AIRFRAMES)}")
    tau = AIRFRAMES[airframe]["lag"]
    lag_on = (tau is not None) if a.motor_lag is None else a.motor_lag == "on"
    if lag_on and tau is None:
        sys.exit(f"--motor-lag on: no motor time constants for {airframe}")
    lag = tau if lag_on else None

    if a.motor_test:
        sys.exit(0 if motor_test(a.bin, files, airframe, [None] + ([tau] if tau else [])) else 1)

    dt, dt_fix = vals["dt"], vals["dtFix"]
    if abs(dt - 1.0 / CTRL_HZ) > 1e-12:
        sys.exit(f"dt {dt} in the parameter file; this harness steps the controller at {CTRL_HZ} Hz")
    fix_every = int(round(dt_fix / dt))
    p0 = (vals["start.x"], vals["start.y"], vals["start.z"])
    seconds = a.seconds if a.seconds is not None else AIRFRAMES[airframe]["seconds"]
    noise = Noise(0, 0, 0, 0, 0, 0, 0, 0) if a.noise == "none" else Noise()

    env = make_env(airframe, lag, (p0[0], p0[1], None) if a.ground else p0)
    obs = reset_env(env)
    sf = SpecificForce(env.G, 1.0 / CTRL_HZ)
    sens = Sensors(noise, a.seed)
    n_cal = 0 if (a.no_calibration or a.ground) else CAL_SAMPLES
    n_ekf = 21 if a.trace_ekf else 0
    n_veh = 4 if a.trace_vehicle else 0
    mav = (["--mav", "--port", str(a.mav_port)] + (["--log", a.mav_log] if a.mav_log else [])
           + (["--origin", *a.origin] if a.origin else [])) if a.mav else []
    proc = subprocess.Popen([a.bin, *param_args(files), "--calibrate", str(n_cal), "--trace", "--bits",
                             *(["--trace-ekf"] if a.trace_ekf else []), *(["--ground"] if a.ground else []),
                             *(["--trace-vehicle"] if a.trace_vehicle else []), *mav, *a.ctl_arg],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    record = open(a.record, "w") if a.record else None

    def send(line):
        proc.stdin.write(line)
        if record:
            record.write(line)

    t0 = time.time()

    # calibration: at rest before the first physics step (true rates 0, specific force (0, 0, -g));
    # the samples are drawn even with --no-calibration, so the noise that follows is the same
    pos, vel, _, _ = enu_state_to_ned(obs[0][0:3], obs[0][3:7], obs[0][10:13], obs[0][13:16])
    q0 = quat_ned_frd(obs[0][3:7])
    if not a.ground:
        for _ in range(CAL_SAMPLES):
            line = line_of(sens.sample(pos, vel, (0.0, 0.0, -env.G), q0, np.zeros(3), False))
            if n_cal:
                send(line)
    proc.stdin.flush()
    if n_cal and proc.stdout.readline().strip() != "calibrated":
        raise RuntimeError("controller did not acknowledge the calibration")

    def stop(*_):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop)
    n = int(round(seconds * CTRL_HZ))
    rows, leg = [], 0
    t_pace = time.monotonic()
    try:
        for k in range(n):
            pos, vel, acc, quat, _, rates = sim_state(env, obs, sf)
            s = sens.sample(pos, vel, acc, quat, rates, k % fix_every == 0)
            if a.dropout and a.dropout[0] <= k / CTRL_HZ < a.dropout[1] and s[6]:
                s = [*s[:15], 0.0, 0.0]          # vfix 0, position-fix presence 0; heading stays
            if a.realtime:
                late = t_pace + k / (CTRL_HZ * a.realtime) - time.monotonic()
                if late > 0:
                    time.sleep(late)
            send(line_of(s))
            proc.stdin.flush()
            r = parse_reply(proc.stdout.readline(), n_ekf, n_veh)
            obs, *_ = env.step(actuators_to_rpm(env, r[:4]).reshape(1, 4))
            p1, v1, _, _ = enu_state_to_ned(obs[0][0:3], obs[0][3:7], obs[0][10:13], obs[0][13:16])
            q1 = quat_ned_frd(obs[0][3:7])
            # state after the tick's physics, as pyfc mission.py logs it; leg at the start of the tick
            veh = r[len(r) - n_veh:] if n_veh else []
            hsp = r[18 + n_ekf:len(r) - n_veh]       # [] from a binary without the heading setpoint
            rows.append([k / CTRL_HZ, *p1, *v1, *q1, *r[4:17], leg, *r[:4]] +
                        ([*r[18:18 + n_ekf], *pos, *vel, *quat] if a.trace_ekf else []) + hsp + veh)
            leg = r[17]
    except KeyboardInterrupt:
        print(f"stopped after {len(rows)} ticks", file=sys.stderr)
    n = len(rows)
    proc.stdin.close()
    proc.wait()
    if record:
        record.close()
    env.close()
    wall = time.time() - t0

    out = Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        with_hsp = bool(rows) and len(rows[0]) == len(COLS) + (len(EKF_COLS) if a.trace_ekf else 0) + 2 + n_veh
        f.write(",".join(COLS + (EKF_COLS if a.trace_ekf else []) + (HSP_COLS if with_hsp else [])
                         + (VEH_COLS if n_veh else [])) + "\n")
        for row in rows:
            m = len(row) - n_veh
            f.write(",".join(str(int(x)) if (i == 24 or i >= m) else repr(float(x)) for i, x in enumerate(row)) + "\n")
    meta = dict(vehicle=airframe, params=[str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p) for p in files],
                noise=a.noise, seed=a.seed, fix_hz=1.0 / dt_fix, motor_lag=list(lag) if lag else None,
                seconds=n / CTRL_HZ, start=list(p0), waypoints=wps, legs=vals["legs"], radius=vals["nav.radius"],
                wall_s=round(wall, 2),
                estimator=vals.get("estimator"), calibration=n_cal, dropout=a.dropout, trace_ekf=a.trace_ekf,
                ground=a.ground, realtime=a.realtime, mav=a.mav, trace_vehicle=a.trace_vehicle,
                gyro_bias=list(sens.gyro_bias), accel_bias=list(sens.accel_bias))
    out.with_suffix(".json").write_text(json.dumps(meta, indent=1) + "\n")
    print(f"{out}: gym-pybullet-drones {airframe}, estimator {vals.get('estimator')}, noise {a.noise}, seed {a.seed}, "
          f"fix {1 / dt_fix:g} Hz, motor lag {'on' if lag else 'off'}, calibration {n_cal}, dropout {a.dropout}, "
          f"{n} ticks, {n / CTRL_HZ:.2f} s simulated, wall {wall:.1f} s")


if __name__ == "__main__":
    main()
