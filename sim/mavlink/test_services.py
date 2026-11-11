#!/usr/bin/env python3
"""Services test: a scripted ground station replaying QGroundControl 5.1.5's sequences against the REAL
controller (`leanfc`: services, vehicle layer, flight law) flying in PyBullet from the ground, over UDP.

    sim/mavlink/.venv/bin/python sim/mavlink/test_services.py [--vehicle x500] [--noise none|field]
        [--seed 0] [--speed 2] [--port 14570] [--out sim/mavlink/out/services-x500-none]

Starts the simulator harness `sim/run_leanfc.py --ground --mav --realtime SPEED --trace-vehicle` (the
vehicle resting on the ground plane, disarmed, the controller calibrating its gyros at boot), listens on
127.0.0.1:PORT as QGroundControl listens on 14550, and replies to the vehicle's source address.
pymavlink's generated dialect (sim/mavlink/.gen/apm2.py, made by test_codec.py) is the test oracle (LGPL,
private, not shipped). Every timeout is in simulated seconds: the clock is the largest time_boot_ms the
vehicle has sent (and a wall-clock bound of 4 x timeout / SPEED + 2 s, which also covers the start).

Each step mirrors what QGroundControl 5.1.5 does (file and function in sim/mavlink/QGC-REQUIREMENTS.md) with
QGroundControl's own timeouts and acceptance checks, and reports PASS or FAIL:

  boot      an arm request before the gyro calibration and the estimator are done: refused with a PreArm text
  connect   GCS HEARTBEAT 1 Hz; REQUEST_MESSAGE AUTOPILOT_VERSION; AVAILABLE_MODES, COMPONENT_METADATA,
            COMPONENT_INFORMATION refused; MAVLink FTP NAKed; APM stream requests
  params    PARAM_REQUEST_LIST with values dropped on purpose and recovered by index; every leanfc parameter
            equal to the files' value (binary32 bits)
  mission   initial download (home + the file's waypoints); fence and rally empty
  rates     QGroundControl's stream rates measured; SET_MESSAGE_INTERVAL / REQUEST_DATA_STREAM changes
  set       PARAM_SET with echo; read back; a rejected value; an unknown name; WP_SPD set for the mission
  upload    plan: takeoff, two waypoints, two spline waypoints, RTL (one request dropped, retried); download
  arming    arm in AUTO refused ("Arm: Auto mode not armable"); PREARM_CHECK healthy
  auto      Start Mission from the ground as QGroundControl does it (GUIDED, arm, MISSION_START): takeoff,
            MISSION_CURRENT / MISSION_ITEM_REACHED in order, ground speed within the WP_SPD that was set,
            pause (BRAKE) holds, continue (AUTO), RTL item lands and disarms (landed_state ON_GROUND)
  guided    QGroundControl's takeoff (GUIDED, arm, NAV_TAKEOFF), go to location (DO_REPOSITION and the
            MISSION_ITEM current=2 fallback), change altitude (SET_POSITION_TARGET_LOCAL_NED offset),
            disarm in flight refused, RTL mode climbs to RTL_ALT_M, returns, lands, disarms
  land      takeoff, LAND, touchdown and the automatic disarm
  mission2  a plan with a waypoint hold time and a NAV_LAND item at a location, started from the ground;
            DO_CHANGE_SPEED and DO_SET_MISSION_CURRENT in flight
  failsafe  FS_GCS_ENABLE 5, FS_GCS_TIMEOUT 3; takeoff; the ground station falls silent: "GCS Failsafe",
            mode LAND, landing, disarm; heartbeats again: "GCS Failsafe Cleared"
  ekf       takeoff; LFC_FS_EKF_POS set below the estimator's position 1 sigma: "EKF Failsafe: changed to
            Land Mode", landing, disarm; arming refused ("PreArm: EKF position variance"); restored:
            "EKF Failsafe Cleared"
  misc      DO_SET_HOME; unsupported command; unsupported mode; TIMESYNC; PING; an unanswered upload
            abandoned after 8 s

Outputs in --out: flight.csv (+ .json, the harness's CSV with the vehicle columns), vehicle.log (every
frame the controller received and sent), steps.json (the steps' simulated times, for
sim/mavlink/flight_metrics.py).
"""

import argparse
import json
import math
import os
import queue
import socket
import struct
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HERE, ".gen"))
import apm2  # noqa: E402

M = apm2
RESULTS = []
SIM_PY = os.environ.get("LEANFC_PY") or str(__import__("pathlib").Path(__file__).resolve().parents[2] / "sim" / ".venv" / "bin" / "python")


def report(name, ok, detail=""):
    RESULTS.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}{'  ' + detail if detail else ''}", flush=True)


def f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


class Link:
    """A UDP ground station: system 255, component 190 (QGroundControl's ids), with a simulated clock."""

    def __init__(self, port, speed):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.sock.settimeout(0.2)
        self.speed = speed
        self.peer = None
        self.mav = M.MAVLink(self, srcSystem=255, srcComponent=190)
        self.mav.robust_parsing = True
        self.q = queue.Queue()
        self.log = []          # (time, msg) of everything received
        self.drop = None       # predicate: drop an incoming message (simulated loss)
        self.running = True
        self.heartbeat = True  # False: the ground station falls silent (link-loss failsafe)
        self.sim_ms = None     # largest time_boot_ms received
        self.lock = threading.Lock()
        threading.Thread(target=self._rx, daemon=True).start()
        threading.Thread(target=self._hb, daemon=True).start()

    def write(self, buf):
        if self.peer:
            self.sock.sendto(buf, self.peer)

    def now(self):
        """Simulated seconds (None before the vehicle's first timestamped message)."""
        return None if self.sim_ms is None else self.sim_ms / 1000.0

    def _rx(self):
        while self.running:
            try:
                data, addr = self.sock.recvfrom(65536)
            except socket.timeout:
                continue
            except OSError:
                return
            self.peer = addr
            for m in self.mav.parse_buffer(data) or []:
                if m.get_srcSystem() != 1:
                    continue
                tb = getattr(m, "time_boot_ms", None)
                if tb is not None and (self.sim_ms is None or tb > self.sim_ms):
                    self.sim_ms = tb
                t = time.time()
                with self.lock:
                    self.log.append((t, m))
                if self.drop and self.drop(m):
                    continue
                self.q.put((t, m))

    def _hb(self):
        last = None
        while self.running:
            if self.peer and self.heartbeat:
                now = self.now()
                if now is None or last is None or now - last >= 1.0 or now < last:
                    self.mav.heartbeat_send(6, 8, 192, 0, 4)  # GCS, INVALID, MANUAL_ARMED, ACTIVE
                    last = now
            time.sleep(0.05 / self.speed)

    def flush(self):
        while not self.q.empty():
            self.q.get_nowait()

    def expired(self, start_sim, start_wall, timeout):
        now = self.now()
        if now is not None and start_sim is not None and now >= start_sim + timeout:
            return True
        return time.time() >= start_wall + 4 * timeout / self.speed + 2

    def wait(self, types, cond=lambda m: True, timeout=2.0):
        if isinstance(types, str):
            types = [types]
        s0, w0 = self.now(), time.time()
        while not self.expired(s0, w0, timeout):
            try:
                _, m = self.q.get(timeout=0.02)
            except queue.Empty:
                continue
            if m.get_type() in types and cond(m):
                return m
        return None

    def collect(self, seconds):
        s0, w0 = self.now(), time.time()
        out = []
        while not self.expired(s0, w0, seconds):
            try:
                _, m = self.q.get(timeout=0.02)
                out.append(m)
            except queue.Empty:
                pass
        return out

    def sleep(self, seconds):
        self.collect(seconds)

    def last(self, typ):
        with self.lock:
            for _, m in reversed(self.log):
                if m.get_type() == typ:
                    return m
        return None

    # QGroundControl's command and mode helpers ---------------------------------------------
    def command_long(self, cmd, *p, timeout=1.5):
        p = list(p) + [0] * (7 - len(p))
        self.mav.command_long_send(1, 1, cmd, 0, *p)
        return self.wait("COMMAND_ACK", lambda m: m.command == cmd, timeout)

    def command_int(self, cmd, frame, p1, p2, p3, p4, x, y, z, timeout=1.5):
        self.mav.command_int_send(1, 1, frame, cmd, 0, 0, p1, p2, p3, p4, x, y, z)
        return self.wait("COMMAND_ACK", lambda m: m.command == cmd, timeout)

    def set_mode_validated(self, mode):
        """FirmwarePlugin::_setFlightModeAndValidate: DO_SET_MODE, HEARTBEAT shows the mode within 1.3 s,
        up to 3 attempts."""
        ack = None
        for _ in range(3):
            ack = self.command_long(176, 1, mode)
            if ack is None or ack.result != 0:
                return False, ack
            if self.wait("HEARTBEAT", lambda m: m.custom_mode == mode, 1.3):
                return True, ack
        return False, ack

    def arm_validated(self, arm=True, force=False):
        """FirmwarePlugin::_armVehicleAndValidate: one ARM_DISARM, HEARTBEAT armed flag within 1.5 s."""
        ack = self.command_long(400, 1 if arm else 0, 21196 if force else 0)
        ok = ack is not None and ack.result == 0 and self.wait(
            "HEARTBEAT", lambda m: bool(m.base_mode & 0x80) == arm, 1.5) is not None
        return ok, ack

    def takeoff(self, alt):
        """APMFirmwarePlugin::guidedModeTakeoff: GUIDED (validated), arm (validated), NAV_TAKEOFF alt."""
        ok1, _ = self.set_mode_validated(4)
        ok2, _ = self.arm_validated(True)
        ack = self.command_long(22, 0, 0, 0, 0, 0, 0, alt)
        return ok1 and ok2 and ack is not None and ack.result == 0

    def rel_alt(self):
        m = self.wait("GLOBAL_POSITION_INT", timeout=1.0)
        return None if m is None else m.relative_alt / 1000.0

    def wait_alt(self, lo, hi, timeout):
        """Wait until the relative altitude is within [lo, hi]; the last altitude seen."""
        s0, w0 = self.now(), time.time()
        alt = None
        while not self.expired(s0, w0, timeout):
            a = self.rel_alt()
            if a is not None:
                alt = a
                if lo <= a <= hi:
                    return True, alt
        return False, alt

    def wait_disarmed(self, timeout):
        return self.wait("HEARTBEAT", lambda m: not (m.base_mode & 0x80), timeout)


def load_file_params(paths):
    vals = {}
    for path in paths:
        for line in open(path):
            t = line.split("#")[0].split()
            if len(t) == 2 and t[0] not in ("estimator", "SIM_VEHICLE"):
                vals[t[0]] = t[1]
    return vals


def parse_table():
    """(MAVLink name, file name) of every leanfc parameter, from Leanfc/Mavlink/ParamTable.lean."""
    src = open(os.path.join(ROOT, "Leanfc", "Mavlink", "ParamTable.lean")).read()
    out = []
    for line in src.splitlines():
        line = line.strip()
        if line.startswith("mk \"") or line.startswith("{ name := \""):
            parts = line.split("\"")
            out.append((parts[1], parts[3]))
    return out


STEPS = []


def step(name, link):
    STEPS.append({"step": name, "t": link.now()})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--vehicle", default="x500")
    ap.add_argument("--noise", default="none")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--speed", type=float, default=2.0, help="simulated seconds per wall second")
    ap.add_argument("--port", type=int, default=14570)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    out = a.out or os.path.join(HERE, "out", f"services-{a.vehicle}-{a.noise}{'' if a.noise == 'none' else a.seed}")
    os.makedirs(out, exist_ok=True)
    files = [os.path.join(ROOT, "params", f"{a.vehicle}.params"), os.path.join(ROOT, "params", "ground.params")]
    params = files + ([os.path.join(ROOT, "params", "mocap.params")] if a.noise == "none" else [])
    link = Link(a.port, a.speed)
    veh = subprocess.Popen(
        [SIM_PY, os.path.join(ROOT, "sim", "run_leanfc.py"), "--params", files[0], "--params", files[1],
         "--noise", a.noise, "--seed", str(a.seed), "--ground", "--mav", "--mav-port", str(a.port),
         "--mav-log", os.path.join(out, "vehicle.log"), "--realtime", str(a.speed), "--trace-vehicle",
         "--seconds", "3600", "--out", os.path.join(out, "flight.csv")],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    t0 = time.time()
    try:
        run(link, a, params)
    except Exception as e:  # report and stop the vehicle
        report(f"exception {type(e).__name__}: {e}", False)
    finally:
        step("end", link)
        link.running = False
        veh.terminate()
        try:
            o, _ = veh.communicate(timeout=300)
            print(o.strip().splitlines()[-1] if o.strip() else "", flush=True)
        except subprocess.TimeoutExpired:
            veh.kill()
        json.dump({"steps": STEPS, "vehicle": a.vehicle, "noise": a.noise, "seed": a.seed, "speed": a.speed},
                  open(os.path.join(out, "steps.json"), "w"), indent=1)
    n_ok = sum(1 for _, ok in RESULTS if ok)
    print(f"\n{n_ok}/{len(RESULTS)} steps passed ({time.time() - t0:.0f} s wall, {link.now() or 0:.0f} s simulated)")
    return 0 if n_ok == len(RESULTS) else 1


def run(link, a, files):
    # ---------------------------------------------------------------- boot
    hb = link.wait("HEARTBEAT", timeout=20)
    report("connect: HEARTBEAT (QUADROTOR, ARDUPILOTMEGA, custom mode STABILIZE, standby, disarmed)",
           hb is not None and hb.type == 2 and hb.autopilot == 3 and hb.base_mode & 1 and hb.system_status == 3
           and hb.custom_mode == 0 and not hb.base_mode & 0x80, str(hb))
    step("boot", link)
    ack = link.command_long(400, 1, 0)
    txt = link.wait("STATUSTEXT", lambda m: m.text.startswith("PreArm"), 1.0)
    report("boot: arm right after boot (calibration or estimator not done) refused (FAILED + PreArm text)",
           ack is not None and ack.result == 4 and txt is not None, txt.text if txt else "")
    # ---------------------------------------------------------------- connect
    t0 = time.time()
    link.mav.command_long_send(1, 1, 512, 0, 148, 0, 0, 0, 0, 0, 0)
    ack = link.wait("COMMAND_ACK", lambda m: m.command == 512, 1.2)
    av = link.wait("AUTOPILOT_VERSION", timeout=1.0)
    report("connect: REQUEST_MESSAGE AUTOPILOT_VERSION -> ACK ACCEPTED, then the message within 1 s",
           ack is not None and ack.result == 0 and av is not None,
           f"caps={av.capabilities if av else None} sw={hex(av.flight_sw_version) if av else None} "
           f"in {time.time() - t0:.3f} s wall")
    for mid, p2 in ((435, 1), (397, 0), (395, 0)):
        link.mav.command_long_send(1, 1, 512, 0, mid, p2, 0, 0, 0, 0, 0)
        ack = link.wait("COMMAND_ACK", lambda m: m.command == 512, 1.2)
        report(f"connect: REQUEST_MESSAGE {mid} refused at once (UNSUPPORTED)", ack is not None and ack.result == 3)
    path = b"@PARAM/param.pck?withdefaults=1"
    hdr = struct.pack("<HBBBBBBI", 1, 0, 4, len(path), 0, 0, 0, 0) + path
    link.mav.file_transfer_protocol_send(0, 1, 1, list(hdr + bytes(251 - len(hdr))))
    ftp = link.wait("FILE_TRANSFER_PROTOCOL", timeout=1.0)
    ok = False
    if ftp:
        p = bytes(ftp.payload)
        seq, sess, op, size, req = struct.unpack("<HBBBB", p[:6])
        ok = seq == 2 and op == 129 and size == 1 and req == 4 and p[12] == 10 and ftp.target_system == 255
    report("connect: FTP OpenFileRO -> NAK FileNotFound (seq+1, size 1, req_opcode 4)", ok)
    rates = [(1, 2), (2, 2), (3, 2), (6, 3), (10, 10), (11, 10), (12, 3)]
    for _ in range(5):
        for sid, hz in rates:
            link.mav.request_data_stream_send(1, 1, sid, hz, 1)
    a1 = link.command_long(511, 242, 1000000)
    a2 = link.command_long(511, 245, 1000000)
    report("connect: SET_MESSAGE_INTERVAL HOME_POSITION, EXTENDED_SYS_STATE 1 Hz accepted",
           a1 is not None and a1.result == 0 and a2 is not None and a2.result == 0)

    # ---------------------------------------------------------------- params
    step("params", link)
    link.flush()
    dropped = {3, 17, 40, 64, 99, 140}
    link.drop = lambda m: m.get_type() == "PARAM_VALUE" and m.param_index in dropped and m.param_index != 65535
    link.mav.param_request_list_send(1, 0)
    got, count, last = {}, None, time.time()
    while time.time() - last < 3.0:      # ParameterManager: 3 s of silence before re-requests
        m = link.wait("PARAM_VALUE", timeout=0.2)
        if m:
            got[m.param_index] = m
            count = m.param_count
            last = time.time()
    link.drop = None
    missing = sorted(set(range(count or 0)) - set(got))
    rounds = 0
    while missing and rounds < 5:
        rounds += 1
        for i in missing[:11]:
            link.mav.param_request_read_send(1, 1, b"", i)
        s0 = time.time()
        while time.time() - s0 < 1.0:
            m = link.wait("PARAM_VALUE", timeout=0.1)
            if m and m.param_index != 65535:
                got[m.param_index] = m
        missing = sorted(set(range(count)) - set(got))
    report(f"params: list of {count}, {len(dropped)} dropped on purpose, recovered by PARAM_REQUEST_READ "
           f"by index in {rounds} round(s)", count is not None and not missing and len(got) == count)
    filep = load_file_params(files)
    names = {m.param_id: m for m in got.values()}
    table = parse_table()
    bad = []
    for mav, fname in table:
        if mav not in names:
            bad.append(f"{mav} missing")
            continue
        if struct.pack("<f", names[mav].param_value) != struct.pack("<f", f32(float(filep[fname]))):
            bad.append(f"{mav}={names[mav].param_value} file {filep[fname]}")
    report(f"params: all {len(table)} leanfc parameters equal the files' values (binary32 bits)", not bad,
           "; ".join(bad[:5]))
    types_ok = all(names[n].param_type in (2, 4, 6, 9) for n in names)
    report(f"params: {(count or 0) - len(table)} compatibility parameters present; ArduPilot types "
           f"(FS_GCS_ENABLE INT8, RTL_LOIT_TIME INT32)", types_ok and "FRAME_CLASS" in names
           and names.get("FS_GCS_ENABLE") is not None and names["FS_GCS_ENABLE"].param_type == 2
           and names.get("RTL_LOIT_TIME") is not None and names["RTL_LOIT_TIME"].param_type == 6)

    # ---------------------------------------------------------------- initial mission download
    def download(mission_type=0):
        link.flush()
        link.mav.mission_request_list_send(1, 1, mission_type)
        c = link.wait("MISSION_COUNT", lambda m: m.mission_type == mission_type, 1.5)
        if c is None:
            return None
        items = []
        for s in range(c.count):
            it = None
            for _ in range(6):
                link.mav.mission_request_int_send(1, 1, s, mission_type)
                it = link.wait("MISSION_ITEM_INT", lambda m: m.seq == s, 0.25)
                if it:
                    break
            if it is None:
                return None
            items.append(it)
        link.mav.mission_ack_send(1, 1, 0, mission_type, 0)
        return items

    items = download()
    report("mission: initial download (home + the file's 4 waypoints as NAV_WAYPOINT)",
           items is not None and len(items) == 5 and items[0].frame == 0 and all(i.command == 16 for i in items),
           f"{[(i.seq, i.command, i.frame, i.x, i.y, round(i.z, 2)) for i in items] if items else None}")
    for mt, name in ((1, "fence"), (2, "rally")):
        link.mav.mission_request_list_send(1, 1, mt)
        c = link.wait("MISSION_COUNT", lambda m: m.mission_type == mt, 1.5)
        report(f"mission: {name} list is empty (MISSION_COUNT 0)", c is not None and c.count == 0)

    # ---------------------------------------------------------------- rates (simulated time)
    link.sleep(1.0)
    link.flush()
    s0 = link.now()
    msgs = link.collect(5.0)
    span = (link.now() - s0) if s0 is not None else 5.0
    cnt = {}
    for m in msgs:
        cnt[m.get_type()] = cnt.get(m.get_type(), 0) + 1
    expect = {"HEARTBEAT": 1, "SYS_STATUS": 2, "GPS_RAW_INT": 2, "MISSION_CURRENT": 2, "NAV_CONTROLLER_OUTPUT": 2,
              "GLOBAL_POSITION_INT": 3, "LOCAL_POSITION_NED": 3, "ATTITUDE": 10, "VFR_HUD": 10,
              "SYSTEM_TIME": 3, "BATTERY_STATUS": 3, "HOME_POSITION": 1, "EXTENDED_SYS_STATE": 1}
    measured = {k: cnt.get(k, 0) / span for k in expect}
    report("rates: QGroundControl's APM stream rates (Hz of simulated time, over 5 s)",
           all(abs(measured[k] - v) <= max(0.25 * v, 0.45) for k, v in expect.items()),
           ", ".join(f"{k} {measured[k]:.1f}/{v}" for k, v in expect.items()))
    a1 = link.command_long(511, 30, 50000)        # ATTITUDE at 20 Hz
    link.mav.request_data_stream_send(1, 1, 11, 0, 0)   # stop EXTRA2 (VFR_HUD)
    a2 = link.command_long(511, 31, 200000)       # ATTITUDE_QUATERNION 5 Hz
    link.sleep(0.5)
    link.flush()
    s0 = link.now()
    msgs = link.collect(4.0)
    span = (link.now() - s0) if s0 is not None else 4.0
    c2 = {}
    for m in msgs:
        c2[m.get_type()] = c2.get(m.get_type(), 0) + 1
    att, vfr, aq = c2.get("ATTITUDE", 0) / span, c2.get("VFR_HUD", 0) / span, c2.get("ATTITUDE_QUATERNION", 0) / span
    report("rates: SET_MESSAGE_INTERVAL ATTITUDE 20 Hz, ATTITUDE_QUATERNION 5 Hz; REQUEST_DATA_STREAM stop EXTRA2",
           a1 and a1.result == 0 and a2 and a2.result == 0 and abs(att - 20) <= 2.5 and vfr == 0 and abs(aq - 5) <= 1,
           f"ATTITUDE {att:.1f} Hz, VFR_HUD {vfr:.1f} Hz, ATTITUDE_QUATERNION {aq:.1f} Hz")
    link.mav.command_long_send(1, 1, 510, 0, 30, 0, 0, 0, 0, 0, 0)
    mi = link.wait("MESSAGE_INTERVAL", timeout=1.0)
    report("rates: GET_MESSAGE_INTERVAL ATTITUDE -> MESSAGE_INTERVAL 50000 us",
           mi is not None and mi.message_id == 30 and mi.interval_us == 50000)
    link.command_long(511, 30, 0)
    link.command_long(511, 31, -1)
    link.mav.request_data_stream_send(1, 1, 11, 10, 1)

    # ---------------------------------------------------------------- param set
    step("set", link)
    link.flush()
    wp_spd = round(0.75 * float(load_file_params(files)["nav.vMax"]), 3)   # X500 1.5, CF2X 0.75 m/s
    link.mav.param_set_send(1, 1, b"WP_SPD", wp_spd, 9)
    echo = link.wait("PARAM_VALUE", lambda m: m.param_id == "WP_SPD", 1.0)
    report(f"set: PARAM_SET WP_SPD {wp_spd} -> PARAM_VALUE echo within 1 s",
           echo is not None and echo.param_value == wp_spd)
    link.mav.param_request_read_send(1, 1, b"WP_SPD", -1)
    rb = link.wait("PARAM_VALUE", lambda m: m.param_id == "WP_SPD", 1.0)
    report("set: read back by name", rb is not None and rb.param_value == wp_spd)
    link.mav.param_set_send(1, 1, b"LFC_DT", -1.0, 9)
    echo = link.wait("PARAM_VALUE", lambda m: m.param_id == "LFC_DT", 1.0)
    txt = link.wait("STATUSTEXT", lambda m: "denied" in m.text, 1.0)
    report("set: a value the loader rejects (LFC_DT -1) keeps the old value and says why",
           echo is not None and abs(echo.param_value - 0.0025) < 1e-9 and txt is not None, txt.text if txt else "")
    link.mav.param_set_send(1, 1, b"NO_SUCH_PARAM", 1.0, 9)
    err = link.wait("PARAM_ERROR", timeout=1.0)
    report("set: unknown name -> PARAM_ERROR DOES_NOT_EXIST", err is not None and err.error == 1)

    # ---------------------------------------------------------------- upload
    hm = link.last("HOME_POSITION")
    lat0, lon0 = hm.latitude, hm.longitude
    home_amsl = hm.altitude / 1000.0
    m_lat = 0.011131884502145034
    m_lon = m_lat * math.cos(math.radians(lat0 / 1e7))
    dlat, dlon = 12.0 / m_lat, 12.0 / m_lon
    plan = [  # (command, frame, p1, x, y, z): what QGroundControl's Plan view sends for ArduPilot
        (16, 0, 0, lat0, lon0, home_amsl),                               # 0: planned home, absolute
        (22, 3, 0, 0, 0, 5.0),                                           # takeoff to 5 m
        (16, 3, 0, int(lat0 + dlat), lon0, 5.0),                         # waypoint 12 m north
        (16, 3, 0, int(lat0 + dlat), int(lon0 + dlon), 6.0),             # waypoint 12 m north-east
        (82, 3, 0, int(lat0 + 2 * dlat), int(lon0 + 2 * dlon), 6.0),     # spline waypoint
        (82, 3, 0, lat0, int(lon0 + 2 * dlon), 5.0),                     # spline waypoint
        (20, 2, 0, 0, 0, 0.0),                                           # RTL
    ]

    def upload(plan, drop_seq=None):
        link.flush()
        link.mav.mission_count_send(1, 1, len(plan), 0)
        dropped_once, requests, t_drop, t_retry = False, [], None, None
        s0, w0 = link.now(), time.time()
        while not link.expired(s0, w0, 15):
            m = link.wait(["MISSION_REQUEST_INT", "MISSION_REQUEST", "MISSION_ACK"], timeout=2.0)
            if m is None:
                return None, requests, None
            if m.get_type() == "MISSION_ACK":
                return m, requests, (t_retry - t_drop if t_drop is not None and t_retry is not None else None)
            requests.append(m.seq)
            if m.seq == drop_seq and not dropped_once:
                dropped_once, t_drop = True, link.now()
                continue
            if m.seq == drop_seq and t_retry is None:
                t_retry = link.now()
            c, fr, p1, x, y, z = plan[m.seq]
            link.mav.mission_item_int_send(1, 1, m.seq, fr, c, 1 if m.seq == 0 else 0, 1, p1, 0, 0,
                                           float("nan") if c in (16, 82) else 0, x, y, z, 0)
        return None, requests, None

    step("upload", link)
    ack, reqs, retry = upload(plan, drop_seq=2)
    report("upload: 7 items, request for item 2 dropped, re-requested, MISSION_ACK ACCEPTED",
           ack is not None and ack.type == 0 and reqs.count(2) == 2,
           f"requests {reqs}, retry after {retry:.2f} s" if retry else f"requests {reqs}")
    items = download()
    ok = items is not None and len(items) == len(plan)
    if ok:
        for it, (c, fr, p1, x, y, z) in zip(items[1:], plan[1:]):
            exp_fr = fr if c != 20 else 2
            if it.command != c or it.frame != exp_fr or (c != 20 and (it.x != x or it.y != y or it.z != f32(z))):
                ok = False
    report("upload: download equals the plan (commands, frames, lat/lon integers, altitudes)", ok)

    # ---------------------------------------------------------------- arming refusal
    ok, _ = link.set_mode_validated(3)
    link.flush()
    ack = link.command_long(400, 1, 0)
    txt = link.wait("STATUSTEXT", lambda m: "not armable" in m.text, 1.0)
    report("arming: arm in AUTO refused (FAILED, 'Arm: Auto mode not armable')", ok and ack is not None
           and ack.result == 4 and txt is not None, txt.text if txt else "")
    sys_status = link.wait("SYS_STATUS", timeout=1.0)
    report("arming: SYS_STATUS PREARM_CHECK healthy once calibrated and settled (QGroundControl: Ready To Fly)",
           sys_status is not None and sys_status.onboard_control_sensors_health & 0x10000000,
           hex(sys_status.onboard_control_sensors_health) if sys_status else "")

    # ---------------------------------------------------------------- AUTO mission from the ground
    step("auto", link)
    ok1, _ = link.set_mode_validated(4)
    ok2, _ = link.arm_validated(True)
    ack = link.command_long(300, 0, 0)
    hb = link.wait("HEARTBEAT", lambda m: m.custom_mode == 3, 1.3)
    report("auto: Start Mission from the ground (GUIDED, arm, MISSION_START): AUTO",
           ok1 and ok2 and ack is not None and ack.result == 0 and hb is not None)
    st = link.wait("EXTENDED_SYS_STATE", lambda m: m.landed_state == 3, 10)
    report("auto: liftoff (landed_state TAKEOFF)", st is not None)
    reached, currents, gs = [], [], []
    s0, w0 = link.now(), time.time()
    while not link.expired(s0, w0, 120):
        m = link.wait(["MISSION_ITEM_REACHED", "MISSION_CURRENT", "VFR_HUD"], timeout=1.0)
        if m is None:
            continue
        if m.get_type() == "MISSION_ITEM_REACHED":
            reached.append(m.seq)
            if m.seq == 4:
                break
        elif m.get_type() == "MISSION_CURRENT":
            if not currents or currents[-1] != m.seq:
                currents.append(m.seq)
        elif m.get_type() == "VFR_HUD":
            gs.append(m.groundspeed)
    report("auto: MISSION_CURRENT 1,2,3,4 and MISSION_ITEM_REACHED 1,2,3,4 in order",
           reached[:4] == [1, 2, 3, 4] and currents[:4] == [1, 2, 3, 4], f"current {currents}, reached {reached}")
    cruise = sorted(v for v in gs if v > 0.5 * wp_spd)
    med = cruise[len(cruise) // 2] if cruise else 0
    report(f"auto: the WP_SPD that was set (PARAM_SET {wp_spd} m/s) is the cruise speed (median ground speed "
           f"above half of it within 5%)", cruise and abs(med - wp_spd) <= 0.05 * wp_spd,
           f"median {med:.3f} m/s, max {max(gs) if gs else 0:.2f} m/s (the velocity loop's overshoot when an "
           f"acceleration ends)")
    # pause (Brake) on the leg to spline waypoint 5, then continue
    link.sleep(2.0)
    step("pause", link)
    ok, _ = link.set_mode_validated(17)
    link.sleep(3.0)
    link.flush()
    p1 = link.wait("LOCAL_POSITION_NED", timeout=1.0)
    link.sleep(3.0)
    link.flush()
    p2 = link.wait("LOCAL_POSITION_NED", timeout=1.0)
    moved = math.dist((p1.x, p1.y, p1.z), (p2.x, p2.y, p2.z)) if p1 and p2 else None
    report("auto: pause (BRAKE) stops and holds the position (moved < 0.3 m over 3 s)",
           ok and moved is not None and moved < 0.3, f"moved {moved:.3f} m" if moved is not None else "")
    step("resume", link)
    ok, _ = link.set_mode_validated(3)
    m = link.wait("MISSION_ITEM_REACHED", lambda m: m.seq == 5, 40)
    report("auto: continue (AUTO): spline waypoint 5 reached", ok and m is not None)
    hb = link.wait_disarmed(150)
    link.flush()
    g = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
    st = link.wait("EXTENDED_SYS_STATE", timeout=1.5)
    mc = link.wait("MISSION_CURRENT", timeout=1.5)
    dh = math.hypot((g.lat - lat0) * m_lat, (g.lon - lon0) * m_lon) if g else None
    report("auto: RTL item: returns, lands, disarms (landed_state ON_GROUND, within 1 m of home, mission complete)",
           hb is not None and g is not None and st is not None and st.landed_state == 1 and dh < 1.0
           and abs(g.relative_alt) < 300 and mc is not None and mc.mission_state == 5,
           f"{dh:.2f} m from home, rel_alt {g.relative_alt} mm, mission_state {mc.mission_state if mc else None}"
           if g else "")

    # ---------------------------------------------------------------- GUIDED
    step("guided", link)
    link.sleep(1.0)
    ok = link.takeoff(5.0)
    st = link.wait("EXTENDED_SYS_STATE", lambda m: m.landed_state in (2, 3), 10)
    hb = link.wait("HEARTBEAT", lambda m: m.system_status == 4 and m.base_mode & 0x80, 10)
    report("guided: takeoff as QGroundControl does it (GUIDED + HEARTBEAT, arm + HEARTBEAT, NAV_TAKEOFF 5 m); "
           "underway (TAKEOFF/IN_AIR, ACTIVE)", ok and st is not None and hb is not None)
    ok, alt = link.wait_alt(4.8, 5.3, 30)
    st = link.wait("EXTENDED_SYS_STATE", lambda m: m.landed_state == 2, 10)
    report("guided: climbed to 5 m (GLOBAL_POSITION_INT relative_alt), landed_state IN_AIR", ok and st is not None,
           f"{alt} m")
    link.sleep(2.0)
    step("goto", link)
    gp = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
    # a target whose degrees are binary32 numbers, so that DO_REPOSITION (integers) and the MISSION_ITEM
    # fallback (binary32 degrees) name the same point
    tlat = round(f32((gp.lat + int(10 / m_lat)) / 1e7) * 1e7)
    tlon = round(f32((gp.lon + int(5 / m_lon)) / 1e7) * 1e7)
    ack = link.command_int(192, 0, -1, 1, 0, float("nan"), tlat, tlon, gp.alt / 1000.0)
    link.mav.mission_item_send(1, 1, 0, 3, 16, 2, 1, 0, 0, 0, 0, tlat / 1e7, tlon / 1e7, gp.relative_alt / 1000.0, 0)
    mack = link.wait("MISSION_ACK", timeout=1.5)
    s0, w0 = link.now(), time.time()
    dist = None
    while not link.expired(s0, w0, 30):
        g = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
        if g:
            dist = math.hypot((g.lat - tlat) * m_lat, (g.lon - tlon) * m_lon)
            if dist < 0.2:
                break
    report("guided: go to location (DO_REPOSITION ACCEPTED, MISSION_ITEM current=2 -> MISSION_ACK ACCEPTED), "
           "arrived within 0.2 m", ack is not None and ack.result == 0
           and mack is not None and mack.type == 0 and dist is not None and dist < 0.2,
           f"distance {dist:.3f} m" if dist is not None else "")
    link.sleep(2.0)
    step("altitude", link)
    a0 = link.rel_alt()
    link.mav.set_position_target_local_ned_send(0, 1, 1, 7, 0xFFF8, 0, 0, -3.0, 0, 0, 0, 0, 0, 0, 0, 0)
    ok, a1 = link.wait_alt(a0 + 2.8, a0 + 3.3, 20)
    report("guided: change altitude +3 m (SET_POSITION_TARGET_LOCAL_NED offset)", ok, f"{a0} -> {a1} m")
    ack = link.command_long(400, 0, 0)
    report("guided: disarm in flight refused (FAILED)", ack is not None and ack.result == 4)
    link.sleep(2.0)
    step("rtl", link)
    hm = link.last("HOME_POSITION")      # home was set again at this flight's arming
    lat0, lon0 = hm.latitude, hm.longitude
    a_start = link.rel_alt()
    ok, _ = link.set_mode_validated(6)
    rtl_alt = float(load_file_params(files)["RTL_ALT_M"])
    expect = max(rtl_alt, a_start or 0)
    # over home (within 0.5 m horizontally) the vehicle waits RTL_LOIT_TIME at its return altitude
    s0, w0 = link.now(), time.time()
    over = None
    while not link.expired(s0, w0, 60):
        g = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
        if g and math.hypot((g.lat - lat0) * m_lat, (g.lon - lon0) * m_lon) < 0.5:
            over = g.relative_alt / 1000.0
            break
    hb = link.wait_disarmed(120)
    link.flush()
    g = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
    st = link.wait("EXTENDED_SYS_STATE", timeout=1.5)
    dh = math.hypot((g.lat - lat0) * m_lat, (g.lon - lon0) * m_lon) if g else None
    report(f"guided: RTL returns at max(RTL_ALT_M {rtl_alt:g} m, current {a_start} m) = {expect:.2f} m, lands, "
           f"disarms (ON_GROUND, within 1 m of home)",
           ok and over is not None and abs(over - expect) < 0.3 and hb is not None and g is not None
           and st is not None and st.landed_state == 1 and dh < 1.0,
           f"over home at {over} m; landed {dh:.2f} m from home" if g else "")

    # ---------------------------------------------------------------- LAND
    step("land", link)
    link.sleep(1.0)
    ok = link.takeoff(4.0)
    ok_alt, alt = link.wait_alt(3.8, 4.3, 30)
    link.sleep(2.0)
    step("land-descent", link)
    ok2, _ = link.set_mode_validated(9)
    st = link.wait("EXTENDED_SYS_STATE", lambda m: m.landed_state == 4, 5)
    hb = link.wait_disarmed(60)
    report("land: takeoff to 4 m, LAND descends (landed_state LANDING), touches down and disarms by itself",
           ok and ok_alt and ok2 and st is not None and hb is not None)

    # ---------------------------------------------------------------- mission 2: hold, speed, set current, land item
    step("mission2", link)
    hm = link.last("HOME_POSITION")
    h_lat, h_lon = hm.latitude, hm.longitude
    d8lat, d8lon = int(8.0 / m_lat), int(8.0 / m_lon)
    plan2 = [
        (16, 0, 0, h_lat, h_lon, home_amsl),                             # 0: home
        (22, 3, 0, 0, 0, 4.0),                                           # takeoff to 4 m
        (16, 3, 3.0, h_lat + d8lat, h_lon, 4.0),                         # waypoint 8 m north, hold 3 s
        (16, 3, 0, h_lat + d8lat, h_lon + d8lon, 4.0),                   # waypoint 8 m north-east
        (21, 3, 0, h_lat, h_lon + d8lon, 0.0),                           # NAV_LAND 8 m east
    ]
    ack, _, _ = upload(plan2)
    ok1, _ = link.set_mode_validated(4)
    ok2, _ = link.arm_validated(True)
    ack2 = link.command_long(300, 0, 0)
    report("mission2: plan (takeoff, waypoint with a 3 s hold, waypoint, NAV_LAND at a location) uploaded and "
           "started from the ground", ack is not None and ack.type == 0 and ok1 and ok2 and ack2 is not None
           and ack2.result == 0)
    m = link.wait("MISSION_ITEM_REACHED", lambda m: m.seq == 2, 40)
    t_reached = link.now()
    c3 = link.wait("MISSION_CURRENT", lambda m: m.seq == 3, 15)
    held = (link.now() - t_reached) if (m and c3 and t_reached is not None) else None
    report("mission2: hold time honored (MISSION_CURRENT 3 at least 3 s after item 2 was reached)",
           held is not None and 2.8 <= held < 4.0, f"{held:.2f} s (simulated clock of 0.1 s resolution)" if held is not None else "")
    link.sleep(1.5)
    step("mission2-speed", link)
    ack = link.command_long(178, 1, 0.8, -1)
    link.sleep(3.0)
    link.flush()
    gs = [m.groundspeed for m in link.collect(3.0) if m.get_type() == "VFR_HUD"]
    med = sorted(gs)[len(gs) // 2] if gs else 0
    report("mission2: DO_CHANGE_SPEED 0.8 m/s in flight accepted; the leg continues at 0.8 m/s",
           ack is not None and ack.result == 0 and abs(med - 0.8) < 0.08, f"median ground speed {med:.3f} m/s")
    step("mission2-setcurrent", link)
    ack = link.command_long(224, 2)
    m = link.wait("MISSION_CURRENT", lambda m: m.seq == 2, 5)
    r2 = link.wait("MISSION_ITEM_REACHED", lambda m: m.seq == 2, 40)
    report("mission2: DO_SET_MISSION_CURRENT 2 in flight: back to item 2, reached again",
           ack is not None and ack.result == 0 and m is not None and r2 is not None)
    st = link.wait("EXTENDED_SYS_STATE", lambda m: m.landed_state == 4, 60)
    hb = link.wait_disarmed(60)
    link.flush()
    g = link.wait("GLOBAL_POSITION_INT", timeout=1.0)
    mc = link.wait("MISSION_CURRENT", timeout=1.5)
    dl = math.hypot((g.lat - h_lat) * m_lat, (g.lon - (h_lon + d8lon)) * m_lon) if g else None
    report("mission2: NAV_LAND item flies to its location, descends (LANDING), lands within 0.5 m of it, "
           "disarms, mission complete", st is not None and hb is not None and dl is not None and dl < 0.5
           and mc is not None and mc.mission_state == 5, f"{dl:.2f} m from the land point" if dl is not None else "")

    # ---------------------------------------------------------------- link-loss failsafe
    step("failsafe", link)
    for name, val, ty in ((b"FS_GCS_ENABLE", 5.0, 2), (b"FS_GCS_TIMEOUT", 3.0, 9)):
        link.mav.param_set_send(1, 1, name, val, ty)
        link.wait("PARAM_VALUE", lambda m, n=name.decode(): m.param_id == n, 1.0)
    link.sleep(1.0)
    ok = link.takeoff(4.0)
    ok_alt, _ = link.wait_alt(3.8, 4.3, 30)
    link.sleep(1.0)
    step("failsafe-silent", link)
    link.heartbeat = False
    txt = link.wait("STATUSTEXT", lambda m: "GCS Failsafe" in m.text, 8)
    hb = link.wait("HEARTBEAT", lambda m: m.custom_mode == 9 and m.system_status == 5, 3)
    report("failsafe: FS_GCS_ENABLE 5, ground station silent for FS_GCS_TIMEOUT 3 s: 'GCS Failsafe', LAND, "
           "HEARTBEAT CRITICAL", ok and ok_alt and txt is not None and hb is not None, txt.text if txt else "")
    hb = link.wait_disarmed(60)
    report("failsafe: the LAND (4 s pause, then the descent) touches down and disarms", hb is not None)
    link.heartbeat = True
    txt = link.wait("STATUSTEXT", lambda m: "Cleared" in m.text, 5)
    report("failsafe: heartbeats again: 'GCS Failsafe Cleared'", txt is not None, txt.text if txt else "")
    link.mav.param_set_send(1, 1, b"FS_GCS_ENABLE", 1.0, 2)
    link.wait("PARAM_VALUE", lambda m: m.param_id == "FS_GCS_ENABLE", 1.0)

    # ---------------------------------------------------------------- estimator failsafe
    # LFC_FS_EKF_POS (copter.ekfPosMax) set below the EKF's position 1 sigma makes the estimator unhealthy
    step("ekf-failsafe", link)
    link.sleep(1.0)
    ok = link.takeoff(4.0)
    ok_alt, _ = link.wait_alt(3.8, 4.3, 30)
    link.sleep(1.0)
    step("ekf-unhealthy", link)
    link.mav.param_set_send(1, 1, b"LFC_FS_EKF_POS", 1e-6, 9)
    link.wait("PARAM_VALUE", lambda m: m.param_id == "LFC_FS_EKF_POS", 1.0)
    txt = link.wait("STATUSTEXT", lambda m: "EKF Failsafe" in m.text, 4)
    hb = link.wait("HEARTBEAT", lambda m: m.custom_mode == 9 and m.system_status == 5, 3)
    report("ekf failsafe: estimator unhealthy for 1 s (LFC_FS_EKF_POS below its position 1 sigma): "
           "'EKF Failsafe: changed to Land Mode', LAND, CRITICAL", ok and ok_alt and txt is not None
           and hb is not None, txt.text if txt else "")
    hb = link.wait_disarmed(60)
    report("ekf failsafe: lands (4 s pause, descent) and disarms", hb is not None)
    link.sleep(1.0)
    ok1, _ = link.set_mode_validated(4)
    link.flush()
    ack = link.command_long(400, 1, 0)
    txt = link.wait("STATUSTEXT", lambda m: m.text.startswith("PreArm"), 1.0)
    report("ekf failsafe: arming refused while the estimator is unhealthy ('PreArm: EKF position variance')",
           ok1 and ack is not None and ack.result == 4 and txt is not None and "variance" in txt.text,
           txt.text if txt else "")
    link.mav.param_set_send(1, 1, b"LFC_FS_EKF_POS", 2.0, 9)
    link.wait("PARAM_VALUE", lambda m: m.param_id == "LFC_FS_EKF_POS", 1.0)
    txt = link.wait("STATUSTEXT", lambda m: "EKF Failsafe Cleared" in m.text, 3)
    report("ekf failsafe: healthy again: 'EKF Failsafe Cleared'", txt is not None)

    # ---------------------------------------------------------------- misc
    step("misc", link)
    ack = link.command_long(179, 0, 0, 0, float("nan"), (lat0 + 1000) / 1e7, lon0 / 1e7, home_amsl)
    h = link.wait("HOME_POSITION", lambda m: abs(m.latitude - (lat0 + 1000)) < 20, 3)
    report("misc: DO_SET_HOME (COMMAND_LONG, location) accepted, HOME_POSITION moved", ack is not None
           and ack.result == 0 and h is not None, f"{h.latitude if h else None}")
    ack = link.command_long(115, 90, 0, 1, 1)
    report("misc: unsupported command (CONDITION_YAW) -> UNSUPPORTED", ack is not None and ack.result == 3)
    ok, ack = link.set_mode_validated(2)
    txt = link.wait("STATUSTEXT", lambda m: "No such mode" in m.text, 1.0)
    report("misc: an unsupported mode (ALT_HOLD) -> FAILED, 'No such mode 2'", not ok and ack is not None
           and ack.result == 4 and txt is not None, txt.text if txt else "")
    link.mav.timesync_send(0, 123456789, 0, 0)
    ts = link.wait("TIMESYNC", lambda m: m.ts1 == 123456789, 1.0)
    report("misc: TIMESYNC answered (tc1 = vehicle ns, ts1 echoed)", ts is not None and ts.tc1 > 0)
    link.mav.ping_send(42, 7, 0, 0)
    pg = link.wait("PING", lambda m: m.seq == 7, 1.0)
    report("misc: PING answered", pg is not None and pg.target_system == 255 and pg.time_usec == 42)
    link.flush()
    link.mav.mission_count_send(1, 1, 3, 0)
    s0 = link.now()
    req = link.wait("MISSION_REQUEST_INT", timeout=1.0)
    ack = link.wait("MISSION_ACK", timeout=12)
    dt = link.now() - s0
    report("misc: unanswered upload abandoned with OPERATION_CANCELLED after about 8 s (simulated)",
           req is not None and ack is not None and ack.type == 15 and 7.5 < dt < 9.5, f"after {dt:.2f} s")


if __name__ == "__main__":
    sys.exit(main())
