"""A scripted MAVLink ground station for the lock-step reference vehicle (sim/fly_reference.py).

It runs inside the lock-step loop: after every step it reads the vehicle's downlink bytes and returns the
uplink bytes for the next input line, so a scripted session is as deterministic as the vehicle (no
sockets, no wall clock). The script is a generator: each `yield` waits one step. Messages use
ArduPilot's own MAVLink dialect (pymavlink built from the pinned ArduPilot submodule, see
reference/REFERENCE.md); the GCS is system 255, component 190, as MAVProxy and QGroundControl.
"""
from __future__ import annotations

import math


class Sink:
    def __init__(self):
        self.buf = bytearray()

    def write(self, b):
        self.buf += b


class GCSError(Exception):
    pass


# ArduCopter custom modes (ArduCopter/mode.h, Mode::Number)
MODES = {"STABILIZE": 0, "ALT_HOLD": 2, "AUTO": 3, "GUIDED": 4, "LOITER": 5, "RTL": 6, "CIRCLE": 7,
         "LAND": 9, "BRAKE": 17}


class GCS:
    def __init__(self, mavmod, log):
        self.m = mavmod
        self.sink = Sink()
        self.mav = mavmod.MAVLink(self.sink, srcSystem=255, srcComponent=190)
        self.mav.robust_parsing = True
        self.parser = mavmod.MAVLink(None)
        self.parser.robust_parsing = True
        self.log = log
        self.t = 0.0
        self.msgs = []          # messages received in the last step
        self.latest = {}        # latest message by type
        self.texts = []         # (t, severity, text)
        self.params = {}        # name -> (value, type, index)
        self.param_count = None
        self.target = (1, 1)
        self.last_hb_sent = -10.0
        self.counts = {}
        self.events = []        # (t, what) milestones for the summary
        self.script = None
        self.done = False
        self.error = None
        # (Phase 5d) the scenario scripts' inputs to the sensor layer of sim/fly_reference.py: the RC frame sent every
        # 8th step (None: the sensor layer's neutral frame; `rc_off`: no RC frame at all, the receiver silent) and the
        # battery's (voltage, current) of every line
        self.rc = None
        self.rc_off = False
        self.bat = None

    # ------------------------------------------------------------------ step interface
    def step(self, t: float, down: bytes) -> bytes:
        """Feed the downlink bytes of one step (time t, s); return the uplink bytes of the next line."""
        self.t = t
        self.msgs = []
        if down:
            for msg in self.parser.parse_buffer(down) or []:
                self._receive(msg)
        if self.t - self.last_hb_sent >= 1.0:
            self.last_hb_sent = self.t
            self.mav.heartbeat_send(self.m.MAV_TYPE_GCS, self.m.MAV_AUTOPILOT_INVALID, 0, 0,
                                    self.m.MAV_STATE_ACTIVE)
        if self.script is not None and not self.done:
            try:
                next(self.script)
            except StopIteration:
                self.done = True
            except GCSError as e:
                self.error = str(e)
                self.event(f"FAILED: {e}")
                self.done = True
        out = bytes(self.sink.buf)
        self.sink.buf.clear()
        return out

    def _receive(self, msg):
        typ = msg.get_type()
        if typ == "BAD_DATA":
            self.counts["BAD_DATA"] = self.counts.get("BAD_DATA", 0) + 1
            return
        self.counts[typ] = self.counts.get(typ, 0) + 1
        self.msgs.append(msg)
        self.latest[typ] = msg
        if typ == "HEARTBEAT" and msg.get_srcComponent() == 1:
            self.target = (msg.get_srcSystem(), msg.get_srcComponent())
        elif typ == "STATUSTEXT":
            self.texts.append((self.t, msg.severity, msg.text))
            self.log(f"{self.t:9.3f}  text[{msg.severity}] {msg.text}")
        elif typ == "PARAM_VALUE":
            self.params[msg.param_id] = (msg.param_value, msg.param_type, msg.param_index)
            self.param_count = msg.param_count

    def event(self, what: str):
        self.events.append((self.t, what))
        self.log(f"{self.t:9.3f}  == {what}")

    # ------------------------------------------------------------------ helpers (generators)
    def wait_until(self, pred, timeout_s: float, what: str):
        t0 = self.t
        while not pred():
            if self.t - t0 > timeout_s:
                raise GCSError(f"timeout ({timeout_s:g} s) waiting for {what}")
            yield

    def wait_s(self, s: float):
        t0 = self.t
        while self.t - t0 < s:
            yield

    def got(self, typ, cond=lambda m: True):
        return next((m for m in self.msgs if m.get_type() == typ and cond(m)), None)

    @property
    def armed(self) -> bool:
        hb = self.latest.get("HEARTBEAT")
        return bool(hb and hb.base_mode & self.m.MAV_MODE_FLAG_SAFETY_ARMED)

    @property
    def mode(self):
        hb = self.latest.get("HEARTBEAT")
        return hb.custom_mode if hb else None

    def command(self, cmd, p1=0, p2=0, p3=0, p4=0, p5=0, p6=0, p7=0, timeout_s=2.0):
        """COMMAND_LONG; returns the COMMAND_ACK result (None on timeout)."""
        self.mav.command_long_send(*self.target, cmd, 0, p1, p2, p3, p4, p5, p6, p7)
        t0 = self.t
        while self.t - t0 < timeout_s:
            yield
            a = self.got("COMMAND_ACK", lambda m: m.command == cmd)
            if a is not None:
                return a.result
        return None

    def command_int(self, cmd, frame, p1=0, p2=0, p3=0, p4=0, x=0, y=0, z=0.0, timeout_s=2.0):
        """COMMAND_INT; returns the COMMAND_ACK result (None on timeout)."""
        self.mav.command_int_send(*self.target, frame, cmd, 0, 0, p1, p2, p3, p4, x, y, z)
        t0 = self.t
        while self.t - t0 < timeout_s:
            yield
            a = self.got("COMMAND_ACK", lambda m: m.command == cmd)
            if a is not None:
                return a.result
        return None

    def set_mode(self, name: str):
        r = yield from self.command(self.m.MAV_CMD_DO_SET_MODE, self.m.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED,
                                    MODES[name])
        if r != self.m.MAV_RESULT_ACCEPTED:
            raise GCSError(f"mode {name} refused (result {r})")
        yield from self.wait_until(lambda: self.mode == MODES[name], 3, f"heartbeat in {name}")
        self.event(f"mode {name}")

    def request_streams(self, rate_hz=4):
        self.mav.request_data_stream_send(*self.target, self.m.MAV_DATA_STREAM_ALL, rate_hz, 1)

    def download_params(self, timeout_s=60.0):
        """PARAM_REQUEST_LIST, then PARAM_REQUEST_READ for every index missing after a quiet second
        (QGroundControl's procedure)."""
        self.params.clear()
        self.param_count = None
        self.mav.param_request_list_send(*self.target)
        t0, last_rx = self.t, self.t
        while True:
            yield
            if any(m.get_type() == "PARAM_VALUE" for m in self.msgs):
                last_rx = self.t
            if self.param_count is not None:
                have = {v[2] for v in self.params.values()}
                if len(have) >= self.param_count:
                    break
                if self.t - last_rx > 1.0:
                    missing = [i for i in range(self.param_count) if i not in have]
                    for i in missing[:20]:
                        self.mav.param_request_read_send(*self.target, b"", i)
                    last_rx = self.t
            if self.t - t0 > timeout_s:
                raise GCSError(f"parameter download incomplete: {len(self.params)} of {self.param_count}")
        self.event(f"parameters downloaded: {self.param_count} in {self.t - t0:.2f} s")

    def set_param(self, name: str, value: float, retries=3):
        for _ in range(retries):
            ptype = self.params.get(name, (0, self.m.MAV_PARAM_TYPE_REAL32, 0))[1]
            self.mav.param_set_send(*self.target, name.encode(), float(value), ptype)
            t0 = self.t
            while self.t - t0 < 1.0:
                yield
                pv = self.got("PARAM_VALUE", lambda m: m.param_id == name)
                if pv is not None:
                    if not math.isclose(pv.param_value, float(value), rel_tol=1e-6, abs_tol=1e-6):
                        raise GCSError(f"PARAM_SET {name}={value} answered with {pv.param_value}")
                    return
        raise GCSError(f"no PARAM_VALUE for {name}")

    def upload_mission(self, items):
        """items: list of (command, frame, params(4), lat_deg, lon_deg, alt_m); seq 0 is home."""
        n = len(items)
        self.mav.mission_count_send(*self.target, n, self.m.MAV_MISSION_TYPE_MISSION)
        t0 = self.t
        while True:
            yield
            for msg in self.msgs:
                if msg.get_type() in ("MISSION_REQUEST_INT", "MISSION_REQUEST"):
                    s = msg.seq
                    cmd, frame, p, lat, lon, alt = items[s]
                    self.mav.mission_item_int_send(*self.target, s, frame, cmd, 0, 1, *p,
                                                   int(round(lat * 1e7)), int(round(lon * 1e7)), alt,
                                                   self.m.MAV_MISSION_TYPE_MISSION)
                elif msg.get_type() == "MISSION_ACK":
                    if msg.type != self.m.MAV_MISSION_ACCEPTED:
                        raise GCSError(f"mission upload refused: {msg.type}")
                    self.event(f"mission uploaded: {n} items")
                    return
            if self.t - t0 > 10:
                raise GCSError("mission upload timed out")

    def download_mission(self):
        self.mav.mission_request_list_send(*self.target, self.m.MAV_MISSION_TYPE_MISSION)
        yield from self.wait_until(lambda: self.got("MISSION_COUNT") is not None, 3, "MISSION_COUNT")
        n = self.got("MISSION_COUNT").count
        got = []
        for s in range(n):
            self.mav.mission_request_int_send(*self.target, s, self.m.MAV_MISSION_TYPE_MISSION)
            yield from self.wait_until(lambda: self.got("MISSION_ITEM_INT", lambda m: m.seq == s) is not None,
                                       3, f"MISSION_ITEM_INT {s}")
            got.append(self.got("MISSION_ITEM_INT", lambda m: m.seq == s))
        self.mav.mission_ack_send(*self.target, self.m.MAV_MISSION_ACCEPTED, self.m.MAV_MISSION_TYPE_MISSION)
        self.event(f"mission downloaded: {n} items")
        return got
