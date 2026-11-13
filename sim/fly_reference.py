#!/usr/bin/env python3
"""Fly the reference vehicle (build/reference/copter_ref, reference/REFERENCE.md) in gym-pybullet-drones
in lock step, one 400 Hz step per protocol line (sim/lockstep_proto.py).

The simulator is CtrlAviary with the CF2X model, as sim/run_copter.py (the same environment set-up,
frame conversions and motor map, imported from it). The sensor layer turns the simulator's state into
the raw samples of the protocol: IMU (body-frame specific force and rates, every step), barometer
(ArduPilot's 1976 atmosphere, 100 Hz), compass (ArduPilot's earth field at the home location rotated
into the body frame, minus SITL's sensor offsets, 100 Hz), GPS (position and NED velocity, 5 Hz), RC
(neutral sticks, throttle low, 50 Hz) and the battery; with --seed, Gaussian noise from a seeded
generator is added (deterministic for a given seed).

Ground station, one of:
  --script image    boot from blank storage, download the parameters, set the overrides of --params,
                    write the storage image (--storage-out); the image is the boot input of the flights
  --script flight   boot from --storage, download the parameters, upload and download a mission, GUIDED,
                    arm, take off, AUTO through the mission (waypoint, spline waypoint, land), until the
                    vehicle disarms on the ground
  --udp             no script: bridge SERIAL0 to UDP for a real ground station (QGroundControl), in real
                    time (the datagrams received before a step go into that step's line)

Every run records inputs.txt (the lines sent) and outputs.txt (the lines received) in --out; replaying
inputs.txt through the binary with the same --storage must reproduce outputs.txt byte for byte
(--replay-check does it after the run).
"""
from __future__ import annotations

import argparse
import math
import os
import socket
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
sys.path.insert(0, str(SIM_DIR))

import run_copter as rc  # noqa: E402  (environment, frames, motor map)
from lockstep_proto import encode_input, decode_output  # noqa: E402
import lockstep_gcs  # noqa: E402

REF_BIN = ROOT / "build" / "reference" / "copter_ref"
STEP_US = 2500
G = rc.GRAVITY_MSS

# home: SITL's default location (CMAC), alt AMSL
HOME_LAT, HOME_LON, HOME_ALT = -35.363261, 149.165230, 584.0
# ArduPilot's earth field at HOME (AP_Declination tables; build/reference/magfield -35.363261 149.165230):
# intensity 0.580028713 G, declination 12.7974262 deg, inclination -65.7653046 deg; NED as SITL builds it
# (Matrix3f::from_euler(0, -inclination, declination) applied to (intensity, 0, 0))
_I, _D, _INC = 580.028713, math.radians(12.7974262), math.radians(-65.7653046)
MAG_NED = np.array([_I * math.cos(_INC) * math.cos(_D), _I * math.cos(_INC) * math.sin(_D), _I * math.sin(_INC)])
MAG_OFS = np.array([5.0, 13.0, -18.0])      # SITL's SIM_MAG1_OFS, set as COMPASS_OFS by the stand-in
LOCATION_SCALING_FACTOR_INV = 89.83204953368922   # AP_Math/location.h, 1e-7 deg per meter

RC_NEUTRAL = [1500, 1500, 1000, 1500, 1000, 1000, 1000, 1000] + [1500] * 8

NOISE = dict(accel=0.05, gyro=0.002, baro_pa=1.0, mag=2.0, gps_pos=0.1, gps_vel=0.05)


def pressure_temperature(alt_amsl: float):
    """ArduPilot's 1976 standard atmosphere, troposphere (AP_Baro::get_pressure_temperature_for_alt_amsl)."""
    r = 6356766.0
    h = r * alt_amsl / (r + alt_amsl)            # geopotential altitude
    T = 288.15 - 0.0065 * h
    P = 101325.0 * (T / 288.15) ** (G / (0.0065 * 287.05287))
    return P, T - 273.15


class Sensors:
    """The sensor layer. IMU samples are taken after every physics substep (1200 Hz, three per step);
    barometer and compass every 4th step (100 Hz), GPS every 80th (5 Hz), RC every 8th (50 Hz)."""

    def __init__(self, seed, substep_s: float):
        self.rng = np.random.default_rng(seed) if seed is not None else None
        self.sf = rc.SpecificForce(G, substep_s)

    def n(self, sigma, size=None):
        if self.rng is None:
            return np.zeros(size) if size else 0.0
        return self.rng.normal(0.0, sigma, size)

    @staticmethod
    def state(obs):
        s = obs[0]
        pos, vel, att, rates = rc.enu_state_to_ned(s[0:3], s[3:7], s[10:13], s[13:16])
        R = rc.ap_quat_to_matrix(rc.quat_ned_frd(s[3:7]))     # FRD body -> NED
        return pos, vel, att, rates, R

    def imu(self, obs):
        pos, vel, att, rates, R = self.state(obs)
        f_ned = self.sf.update(vel, True)                      # earth-frame specific force
        accel = R.T @ f_ned + self.n(NOISE["accel"], 3)
        gyro = np.asarray(rates) + self.n(NOISE["gyro"], 3)
        return tuple(accel), tuple(gyro)

    def slow(self, k: int, obs):
        pos, vel, att, rates, R = self.state(obs)
        out = dict(pos=pos, vel=vel, att=att)
        if k % 4 == 0:
            P, T = pressure_temperature(HOME_ALT - pos[2])
            out["baro"] = (P + self.n(NOISE["baro_pa"]), T)
            out["mag"] = tuple(R.T @ MAG_NED - MAG_OFS + self.n(NOISE["mag"], 3))
        if k % 80 == 0:
            pn = pos + self.n(NOISE["gps_pos"], 3)
            vn = np.asarray(vel) + self.n(NOISE["gps_vel"], 3)
            lat = HOME_LAT + pn[0] * 1e-7 * LOCATION_SCALING_FACTOR_INV
            lon = HOME_LON + pn[1] * 1e-7 * LOCATION_SCALING_FACTOR_INV / math.cos(math.radians(HOME_LAT))
            out["gps"] = (lat, lon, HOME_ALT - pn[2], vn[0], vn[1], vn[2])
        if k % 8 == 0:
            out["rc"] = RC_NEUTRAL
        return out


def pwm_to_rpm(env, pwm):
    a = [min(1.0, max(0.0, (pwm[i] - 1000) / 1000.0)) for i in range(4)]
    return rc.actuators_to_rpm(env, a), a


def mission_items(m):
    """The scripted mission, NED meters from home converted to lat/lon, relative altitudes."""
    def ll(n, e):
        return (HOME_LAT + n * 1e-7 * LOCATION_SCALING_FACTOR_INV,
                HOME_LON + e * 1e-7 * LOCATION_SCALING_FACTOR_INV / math.cos(math.radians(HOME_LAT)))
    F, FR = m.MAV_FRAME_GLOBAL, m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT
    items = [(m.MAV_CMD_NAV_WAYPOINT, F, (0, 0, 0, 0), HOME_LAT, HOME_LON, HOME_ALT)]   # seq 0: home
    items.append((m.MAV_CMD_NAV_TAKEOFF, FR, (0, 0, 0, 0), *ll(0, 0), 5.0))
    items.append((m.MAV_CMD_NAV_WAYPOINT, FR, (0, 0, 0, 0), *ll(10, 0), 5.0))
    items.append((m.MAV_CMD_NAV_WAYPOINT, FR, (0, 0, 0, 0), *ll(10, 10), 6.0))
    items.append((m.MAV_CMD_NAV_SPLINE_WAYPOINT, FR, (0, 0, 0, 0), *ll(0, 10), 5.0))
    items.append((m.MAV_CMD_NAV_LAND, FR, (0, 0, 0, 0), *ll(0, 0), 0.0))
    return items


def script_image(g: lockstep_gcs.GCS, params: dict):
    yield from g.wait_until(lambda: "HEARTBEAT" in g.latest, 60, "first heartbeat")
    g.event("heartbeat")
    yield from g.wait_s(2.0)
    yield from g.download_params()
    for name, value in params.items():
        yield from g.set_param(name, value)
    g.event(f"{len(params)} parameters set")
    yield from g.wait_s(3.0)     # AP_Param saves in the IO process


def script_flight(g: lockstep_gcs.GCS, m):
    yield from g.wait_until(lambda: "HEARTBEAT" in g.latest, 60, "first heartbeat")
    g.event("heartbeat")
    g.request_streams(4)
    yield from g.download_params()
    for name, want in (("FRAME_CLASS", 1), ("GPS1_TYPE", 100), ("BATT_MONITOR", 4)):
        if name not in g.params or g.params[name][0] != want:
            raise lockstep_gcs.GCSError(f"parameter {name} is {g.params.get(name)}, expected {want}")
    yield from g.wait_until(lambda: any("is using GPS" in x[2] for x in g.texts), 120, "EKF3 using GPS")
    g.event("EKF3 using GPS")
    items = mission_items(m)
    yield from g.upload_mission(items)
    back = yield from g.download_mission()
    if len(back) != len(items) or any(b.command != it[0] for b, it in zip(back, items)):
        raise lockstep_gcs.GCSError("downloaded mission differs from the uploaded one")
    yield from g.set_mode("GUIDED")
    t0 = g.t
    while not g.armed:
        r = yield from g.command(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        if r == m.MAV_RESULT_ACCEPTED:
            yield from g.wait_until(lambda: g.armed, 3, "armed heartbeat")
            break
        if g.t - t0 > 60:
            raise lockstep_gcs.GCSError("arming refused for 60 s")
        yield from g.wait_s(2.0)
    g.event("armed")
    r = yield from g.command(m.MAV_CMD_NAV_TAKEOFF, p7=5.0)
    if r != m.MAV_RESULT_ACCEPTED:
        raise lockstep_gcs.GCSError(f"takeoff refused ({r})")
    yield from g.wait_until(lambda: "GLOBAL_POSITION_INT" in g.latest and
                            g.latest["GLOBAL_POSITION_INT"].relative_alt > 4500, 30, "4.5 m")
    g.event("reached 4.5 m in GUIDED")
    yield from g.set_mode("AUTO")
    yield from g.wait_until(lambda: not g.armed, 240, "disarm after the mission")
    g.event("disarmed")
    yield from g.wait_s(2.0)


# ---------------------------------------------------------------------------------------------------------------
# (Phase 5d) the scenario suite: short sessions that reach code the mission flight does not (README.md "Phase 5d
# summary"). Each boots from the same storage image as the flight, waits for EKF3 to use GPS (about 42 s), and then
# exercises one part of the vehicle. Ground-station and sensor-layer actions only; no vehicle logic here.

def ll_of(n, e):
    return (HOME_LAT + n * 1e-7 * LOCATION_SCALING_FACTOR_INV,
            HOME_LON + e * 1e-7 * LOCATION_SCALING_FACTOR_INV / math.cos(math.radians(HOME_LAT)))


def rc_frame(roll=1500, pitch=1500, thr=1000, yaw=1500):
    f = list(RC_NEUTRAL)
    f[0], f[1], f[2], f[3] = roll, pitch, thr, yaw
    return f


def boot_ready(g: lockstep_gcs.GCS, params=()):
    yield from g.wait_until(lambda: "HEARTBEAT" in g.latest, 60, "first heartbeat")
    g.event("heartbeat")
    g.request_streams(4)
    for name, value in params:
        yield from g.set_param(name, value)
    if params:
        g.event("parameters set: " + ", ".join(f"{n}={v:g}" for n, v in params))


def wait_gps(g):
    yield from g.wait_until(lambda: any("is using GPS" in x[2] for x in g.texts), 120, "EKF3 using GPS")
    g.event("EKF3 using GPS")


def arm_takeoff(g, m, alt):
    yield from g.set_mode("GUIDED")
    t0 = g.t
    while not g.armed:
        r = yield from g.command(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        if r == m.MAV_RESULT_ACCEPTED:
            yield from g.wait_until(lambda: g.armed, 3, "armed heartbeat")
            break
        if g.t - t0 > 30:
            raise lockstep_gcs.GCSError("arming refused for 30 s")
        yield from g.wait_s(2.0)
    g.event("armed")
    r = yield from g.command(m.MAV_CMD_NAV_TAKEOFF, p7=alt)
    if r != m.MAV_RESULT_ACCEPTED:
        raise lockstep_gcs.GCSError(f"takeoff refused ({r})")
    yield from rel_alt_above(g, alt - 0.3, 20)
    g.event(f"reached {alt - 0.3:g} m in GUIDED")


def rel_alt_above(g, alt, timeout):
    yield from g.wait_until(lambda: "GLOBAL_POSITION_INT" in g.latest and
                            g.latest["GLOBAL_POSITION_INT"].relative_alt > alt * 1000, timeout, f"{alt:g} m")


def wait_disarm(g, timeout=40):
    yield from g.wait_until(lambda: not g.armed, timeout, "disarm")
    g.event("disarmed")
    yield from g.wait_s(1.0)


def wait_mode(g, name, timeout):
    yield from g.wait_until(lambda: g.mode == lockstep_gcs.MODES[name], timeout, f"mode {name}")
    g.event(f"mode {name} (vehicle)")


def script_loiter(g, m):
    """(a) LOITER with stick input, then LAND."""
    yield from boot_ready(g)
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    g.rc = rc_frame(thr=1500)
    yield from g.wait_s(0.5)
    yield from g.set_mode("LOITER")
    for what, frame, s in (("roll right", rc_frame(roll=1650, thr=1500), 2.0), ("sticks centered", rc_frame(thr=1500), 1.0),
                           ("pitch forward", rc_frame(pitch=1350, thr=1500), 2.0), ("yaw right", rc_frame(yaw=1600, thr=1500), 1.0),
                           ("climb", rc_frame(thr=1700), 1.0), ("sticks centered", rc_frame(thr=1500), 2.0)):
        g.rc = frame
        g.event("sticks: " + what)
        yield from g.wait_s(s)
    yield from g.set_mode("LAND")
    yield from wait_disarm(g)


def script_brake(g, m):
    """(b) GUIDED toward a point, BRAKE while moving, ALT_HOLD with sticks, LAND."""
    yield from boot_ready(g)
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    g.mav.set_position_target_local_ned_send(0, *g.target, m.MAV_FRAME_LOCAL_NED, 0b110111111000, 8.0, 0.0, -3.0,
                                             0, 0, 0, 0, 0, 0, 0, 0)
    g.event("position target 8 m north")
    yield from g.wait_s(2.5)
    yield from g.set_mode("BRAKE")
    yield from g.wait_s(2.0)
    g.rc = rc_frame(thr=1500)
    yield from g.set_mode("ALT_HOLD")
    for what, frame, s in (("roll left", rc_frame(roll=1400, thr=1500), 1.0), ("sticks centered", rc_frame(thr=1500), 1.5),
                           ("climb", rc_frame(thr=1750), 1.0), ("sticks centered", rc_frame(thr=1500), 1.0)):
        g.rc = frame
        g.event("sticks: " + what)
        yield from g.wait_s(s)
    yield from g.set_mode("LAND")
    yield from wait_disarm(g)


def script_rtl(g, m):
    """(c) RTL from 12 m away (RTL_ALT_M 4, RTL_LOIT_TIME 1 s)."""
    yield from boot_ready(g, (("RTL_ALT_M", 4.0), ("RTL_LOIT_TIME", 1000.0)))
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    lat, lon = ll_of(12.0, 0.0)
    g.mav.set_position_target_global_int_send(0, *g.target, m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT, 0b110111111000,
                                              int(round(lat * 1e7)), int(round(lon * 1e7)), 3.0, 0, 0, 0, 0, 0, 0, 0, 0)
    g.event("position target 12 m north")
    yield from g.wait_until(lambda: "LOCAL_POSITION_NED" in g.latest and g.latest["LOCAL_POSITION_NED"].x > 11.0, 20, "12 m north")
    g.event("12 m north")
    yield from g.set_mode("RTL")
    yield from wait_disarm(g, 60)


def script_guided(g, m):
    """(d) GCS-commanded GUIDED: DO_REPOSITION, CONDITION_YAW, DO_CHANGE_SPEED, a velocity target, then LAND."""
    yield from boot_ready(g)
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    lat, lon = ll_of(0.0, 6.0)
    r = yield from g.command_int(m.MAV_CMD_DO_REPOSITION, m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT, -1, 0, 0, math.nan,
                                 int(round(lat * 1e7)), int(round(lon * 1e7)), 4.0)
    g.event(f"DO_REPOSITION 6 m east, 4 m: result {r}")
    yield from g.wait_s(4.0)
    r = yield from g.command(m.MAV_CMD_CONDITION_YAW, 90, 30, 1, 0)
    g.event(f"CONDITION_YAW 90: result {r}")
    yield from g.wait_s(3.0)
    r = yield from g.command(m.MAV_CMD_DO_CHANGE_SPEED, 1, 1.0, -1, 0)
    g.event(f"DO_CHANGE_SPEED 1 m/s: result {r}")
    g.mav.set_position_target_local_ned_send(0, *g.target, m.MAV_FRAME_LOCAL_NED, 0b110111000111, 0, 0, 0,
                                             -1.0, 0.0, 0.0, 0, 0, 0, 0, 0)
    g.event("velocity target 1 m/s south")
    yield from g.wait_s(2.0)
    r = yield from g.command(m.MAV_CMD_NAV_LAND)
    g.event(f"NAV_LAND: result {r}")
    yield from wait_disarm(g)


def script_battery(g, m):
    """(e) battery failsafe: the voltage drops below BATT_LOW_VOLT in flight; BATT_FS_LOW_ACT 1 (LAND)."""
    yield from boot_ready(g, (("BATT_FS_LOW_ACT", 1.0), ("BATT_LOW_TIMER", 2.0)))
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    yield from g.wait_s(1.0)
    g.bat = (10.2, 6.0)
    g.event("battery 10.2 V")
    yield from wait_mode(g, "LAND", 10)
    yield from wait_disarm(g)


def script_prearm(g, m):
    """(f) arming refused with its PreArm text (before the EKF has a position, and again later), then the radio
    failsafe in flight (the receiver goes silent; FS_THR_ENABLE 3: LAND)."""
    yield from boot_ready(g, (("FS_THR_ENABLE", 3.0),))
    yield from g.wait_s(2.0)
    for when in ("early", "after origin"):
        if when == "after origin":
            yield from g.wait_until(lambda: any("origin set" in x[2] for x in g.texts), 60, "origin set")
            yield from g.wait_s(1.0)
        r = yield from g.command(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        yield from g.wait_s(0.5)
        g.event(f"arm ({when}): result {r}; texts {[x[2] for x in g.texts if x[2].startswith('PreArm') or x[2].startswith('Arm')][-3:]}")
    yield from wait_gps(g)
    yield from arm_takeoff(g, m, 3.0)
    yield from g.wait_s(1.0)
    g.rc_off = True
    g.event("receiver silent")
    yield from wait_mode(g, "LAND", 5)
    yield from wait_disarm(g)


SCENARIOS = {"loiter": script_loiter, "brake": script_brake, "rtl": script_rtl, "guided": script_guided,
             "battery": script_battery, "prearm": script_prearm}


def read_params(files):
    out = {}
    for f in files:
        for line in Path(f).read_text().splitlines():
            line = line.split("#")[0].strip().replace(",", " ")
            if not line:
                continue
            k, v = line.split()[:2]
            out[k] = float(v)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=str(REF_BIN))
    ap.add_argument("--out", required=True)
    ap.add_argument("--script", choices=["image", "flight"] + sorted(SCENARIOS))
    ap.add_argument("--udp", action="store_true", help="real-time UDP bridge for a ground station")
    ap.add_argument("--udp-port", type=int, default=14550, help="ground station port on 127.0.0.1")
    ap.add_argument("--storage", help="storage image the vehicle boots from")
    ap.add_argument("--storage-out", help="storage image written at the end")
    ap.add_argument("--params", action="append", default=[], help="parameter overrides (image script)")
    ap.add_argument("--seed", type=int, help="sensor noise seed (default: no noise)")
    ap.add_argument("--duration", type=float, default=400.0, help="limit, simulated seconds")
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--replay-check", action="store_true")
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    logf = open(out / "log.txt", "w")

    def log(s):
        logf.write(s + "\n")
        logf.flush()
        if not args.udp or "==" in s:
            print(s, flush=True)

    from pymavlink.dialects.v20 import ardupilotmega as m
    if args.storage:
        # the boot image is an input of the run: keep a copy next to the trace
        (out / "storage_in.bin").write_bytes(Path(args.storage).read_bytes())
    cmd = [args.bin, "--timing-file", str(out / "timing.txt")]
    if args.storage:
        cmd += ["--storage", args.storage]
    if args.storage_out:
        cmd += ["--storage-out", args.storage_out]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    # the environment of run_copter.py stepped at the physics rate (control frequency = physics
    # frequency), so that every physics substep yields an IMU sample; the vehicle's PWM is held for
    # the SUBSTEPS substeps of one 400 Hz step
    rc.CTRL_HZ = args.pyb_hz
    substeps = args.pyb_hz // 400
    env = rc.make_env(False, args.pyb_hz, (0.0, 0.0, None), (0.0, 0.0, 0.0), "freefall")
    obs = rc.reset_env(env)
    sensors = Sensors(args.seed, 1.0 / args.pyb_hz)
    imu_buf = [sensors.imu(obs)] * substeps
    gcs = None
    sock = None
    if args.udp:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind(("127.0.0.1", 0))
        sock.setblocking(False)
        gcs_addr = ("127.0.0.1", args.udp_port)
        log(f"UDP bridge: vehicle at {sock.getsockname()}, ground station at {gcs_addr}")
    else:
        gcs = lockstep_gcs.GCS(m, log)
        gcs.script = (script_image(gcs, read_params(args.params)) if args.script == "image"
                      else SCENARIOS[args.script](gcs, m) if args.script in SCENARIOS
                      else script_flight(gcs, m))

    fin = open(out / "inputs.txt", "w")
    fout = open(out / "outputs.txt", "w")
    track = open(out / "track.csv", "w")
    track.write("t,n,e,d,vn,ve,vd,roll,pitch,yaw,m1,m2,m3,m4\n")
    up = b""
    n_ticks = int(args.duration * 1e6 / STEP_US)
    w0 = time.perf_counter()
    sim_s = 0.0
    k = 0
    end = "time limit"
    try:
        for k in range(n_ticks):
            t_us = STEP_US * (k + 1)
            s = sensors.slow(k, obs)
            rc_line = s.get("rc")
            bat = (12.6, 0.5)
            if gcs is not None:
                # (Phase 5d) a scenario's RC frame or silent receiver, and its battery reading
                if rc_line is not None and gcs.rc_off:
                    rc_line = None
                elif rc_line is not None and gcs.rc is not None:
                    rc_line = gcs.rc
                if gcs.bat is not None:
                    bat = gcs.bat
            line = encode_input(t_us, imu=imu_buf, baro=s.get("baro"), mag=s.get("mag"), gps=s.get("gps"),
                                rc=rc_line, bat=bat, up=up)
            proc.stdin.write(line + "\n")
            reply = proc.stdout.readline()
            if not reply:
                end = f"vehicle exited (code {proc.wait()})"
                break
            fin.write(line + "\n")
            fout.write(reply)
            t_out, pwm, down = decode_output(reply)
            rpm, act = pwm_to_rpm(env, pwm)
            if k % 40 == 0:
                p, v, a = s["pos"], s["vel"], s["att"]
                track.write(f"{t_us*1e-6:.4f},{p[0]:.4f},{p[1]:.4f},{p[2]:.4f},{v[0]:.4f},{v[1]:.4f},{v[2]:.4f},"
                            f"{math.degrees(a[0]):.2f},{math.degrees(a[1]):.2f},{math.degrees(a[2]):.2f},"
                            + ",".join(f"{x:.4f}" for x in act) + "\n")
            if gcs is not None:
                up = gcs.step(t_us * 1e-6, down)
                if gcs.done:
                    end = "script failed: " + gcs.error if gcs.error else "script finished"
                    break
            else:
                if down:
                    sock.sendto(down, gcs_addr)
                target = w0 + (k + 1) * STEP_US * 1e-6
                while True:
                    now = time.perf_counter()
                    if now >= target:
                        break
                    time.sleep(min(0.002, target - now))
                chunks = []
                while True:
                    try:
                        data, addr = sock.recvfrom(65536)
                    except BlockingIOError:
                        break
                    chunks.append(data)
                up = b"".join(chunks)
            s0 = time.perf_counter()
            imu_buf = []
            for _ in range(substeps):
                obs, *_ = env.step(rpm.reshape(1, 4))
                imu_buf.append(sensors.imu(obs))
            sim_s += time.perf_counter() - s0
    except KeyboardInterrupt:
        end = "interrupted"
    finally:
        wall = time.perf_counter() - w0
        proc.stdin.close()
        tail = proc.stdout.read()     # the output line of the last input line, if not yet read
        code = proc.wait()
        fin.close()
        fout.close()
        track.close()
        env.close()
    steps = k + 1
    summary = [f"end: {end}", f"steps: {steps} ({steps * STEP_US * 1e-6:.2f} s simulated), wall {wall:.2f} s "
               f"({steps * STEP_US * 1e-6 / wall:.1f}x real time), simulator {sim_s:.2f} s",
               f"vehicle exit code {code}" + (f", unread output {len(tail)} bytes" if tail else "")]
    tf = out / "timing.txt"
    if tf.exists():
        summary.append(tf.read_text().splitlines()[0])
    if gcs is not None:
        summary.append("events: " + "; ".join(f"{t:.2f} {w}" for t, w in gcs.events))
        summary.append("messages received: " + ", ".join(f"{k}:{v}" for k, v in sorted(gcs.counts.items())))
    for line in summary:
        log(line)
    if args.replay_check:
        replay_check(args, out, log)
    (out / "summary.txt").write_text("\n".join(summary) + "\n")
    if gcs is not None and gcs.error:
        sys.exit(1)


def replay_check(args, out: Path, log):
    """Feed inputs.txt back to the binary (no simulator) and compare its output with outputs.txt."""
    cmd = [args.bin, "--timing-file", str(out / "timing_replay.txt")]
    if args.storage:
        cmd += ["--storage", args.storage]
    t0 = time.perf_counter()
    with open(out / "inputs.txt") as fi, open(out / "replay.txt", "w") as fo:
        subprocess.run(cmd, stdin=fi, stdout=fo, check=False)
    wall = time.perf_counter() - t0
    a = (out / "outputs.txt").read_bytes()
    b = (out / "replay.txt").read_bytes()
    la, lb = a.count(b"\n"), b.count(b"\n")
    if a == b:
        log(f"replay: {lb} output lines, identical to outputs.txt byte for byte ({wall:.2f} s wall)")
    else:
        al, bl = a.split(b"\n"), b.split(b"\n")
        first = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
        log(f"replay: DIFFERS from outputs.txt ({la} vs {lb} lines), first difference at line {first + 1}")


if __name__ == "__main__":
    main()
