#!/usr/bin/env python3
"""Check a QGroundControl session without QGroundControl: a QGroundControl-like pymavlink client on one UDP port for the
real-time gorge sessions of any stack's fly_qgc.sh. Per vehicle (told apart by MAVLink system id and source address; only the
autopilot's component 1, as QGroundControl creates vehicles; the cameras' component 100 is ignored):
heartbeat, parameter download start, mission upload of a .plan's items as QGroundControl sends them (MISSION_ITEM_INT,
frame as in the plan, x/y = int(deg * 1e7)), download back and compare, GUIDED, arm, takeoff, AUTO, then MISSION_CURRENT
past the first spline waypoint. Prints `RESULT PASS` (exit 0) or `RESULT FAIL` (exit 1).

    sim/.venv/bin/python sim/checks/qgc_session_check.py PORT TIMEOUT_S SYSID=PLAN [SYSID=PLAN ...]

For example, in one terminal `./fly_qgc.sh abreast --udp-port 14560 --video-port 5700` (a stack's launcher), in another
`sim/.venv/bin/python sim/checks/qgc_session_check.py 14560 400 1=sim/plans/formation-abreast-v1.plan
2=sim/plans/formation-abreast-v2.plan`, then stop the session (Ctrl-C). The modes it sets are ArduCopter's (GUIDED 4,
AUTO 3), so it fits stacks that speak ArduPilot's MAVLink dialect.
"""
import json
import struct
import socket
import sys
import time

from pymavlink.dialects.v20 import ardupilotmega as m

port, timeout = int(sys.argv[1]), float(sys.argv[2])
plans = {int(a.split("=")[0]): json.load(open(a.split("=")[1])) for a in sys.argv[3:]}
sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.bind(("127.0.0.1", port))
sock.setblocking(False)
mav = m.MAVLink(None, srcSystem=255, srcComponent=190)
T0 = time.time()
f32 = lambda v: struct.unpack('<f', struct.pack('<f', float(v)))[0]   # MAVLink params are float32


def log(s):
    print(f"{time.time() - T0:7.2f}  {s}", flush=True)


class V:
    def __init__(self, sysid, plan):
        self.sysid, self.plan = sysid, plan
        self.addr = None
        self.parser = m.MAVLink(None)
        self.parser.robust_parsing = True
        self.msgs, self.latest, self.texts = [], {}, []
        self.params = 0
        self.ok = {}
        self.script = self.run()
        self.done = False

    def send(self, msg):
        sock.sendto(msg.pack(mav), self.addr)

    def got(self, typ, cond=lambda x: True):
        return next((x for x in self.msgs if x.get_type() == typ and cond(x)), None)

    def wait(self, pred, s, what):
        t0 = time.time()
        while not pred():
            if time.time() - t0 > s:
                raise RuntimeError(f"sysid {self.sysid}: timeout waiting for {what}")
            yield

    def cmd(self, c, *p):
        p = list(p) + [0] * (7 - len(p))
        for _ in range(10):
            self.send(m.MAVLink_command_long_message(self.sysid, 1, c, 0, *p))
            t0 = time.time()
            while time.time() - t0 < 1.0:
                yield
                a = self.got("COMMAND_ACK", lambda x: x.command == c)
                if a is not None:
                    if a.result == 0:
                        return 0
                    break
            yield from self.sleep(1.0)
        return -1

    def sleep(self, s):
        t0 = time.time()
        while time.time() - t0 < s:
            yield

    def run(self):
        L = lambda s: log(f"[sysid {self.sysid}] {s}")
        L(f"heartbeat from {self.addr}")
        self.send(m.MAVLink_request_data_stream_message(self.sysid, 1, m.MAV_DATA_STREAM_ALL, 4, 1))
        self.send(m.MAVLink_param_request_list_message(self.sysid, 1))
        yield from self.wait(lambda: self.params >= 20, 30, "PARAM_VALUEs")
        L(f"parameter download started: {self.params} PARAM_VALUE so far (param_count {self.latest['PARAM_VALUE'].param_count})")
        self.ok["params"] = True
        yield from self.wait(lambda: any("is using GPS" in t for t in self.texts), 180, "EKF3 using GPS")
        L("EKF3 using GPS")
        P = self.plan["mission"]
        home = P["plannedHomePosition"]
        items = [(0, 16, 0, 0, 0, 0, home[0], home[1], home[2])] + [
            (q["frame"], q["command"], *q["params"]) for q in P["items"]]
        self.send(m.MAVLink_mission_count_message(self.sysid, 1, len(items), 0))
        sent = set()
        t0 = time.time()
        while True:
            yield
            if time.time() - t0 > 20:
                raise RuntimeError("upload timeout")
            for x in self.msgs:
                if x.get_type() in ("MISSION_REQUEST_INT", "MISSION_REQUEST"):
                    s = x.seq
                    fr, c, p1, p2, p3, p4, la, lo, al = items[s]
                    X = la if fr == 2 else int(la * 1e7)
                    Y = lo if fr == 2 else int(lo * 1e7)
                    self.send(m.MAVLink_mission_item_int_message(self.sysid, 1, s, fr, c, int(s == 0), 1,
                                                                 p1, p2, p3, p4, int(X), int(Y), al, 0))
                    sent.add(s)
            a = self.got("MISSION_ACK")
            if a is not None:
                break
        L(f"upload of {len(items)} items: MISSION_ACK type {a.type} ({'accepted' if a.type == 0 else 'REFUSED'})")
        if a.type != 0:
            raise RuntimeError("mission refused")
        self.send(m.MAVLink_mission_request_list_message(self.sysid, 1, 0))
        yield from self.wait(lambda: self.got("MISSION_COUNT") is not None, 5, "MISSION_COUNT")
        n = self.got("MISSION_COUNT").count
        back = []
        for s in range(n):
            self.send(m.MAVLink_mission_request_int_message(self.sysid, 1, s, 0))
            yield from self.wait(lambda: self.got("MISSION_ITEM_INT", lambda x, s=s: x.seq == s) is not None, 3, f"item {s}")
            back.append(self.got("MISSION_ITEM_INT", lambda x, s=s: x.seq == s))
        self.send(m.MAVLink_mission_ack_message(self.sysid, 1, 0, 0))
        diff = [s for s, (b, it) in enumerate(zip(back, items)) if s > 0 and (
            b.command != it[1] or [b.param1, b.param2, b.param3, b.param4] != [f32(v) for v in it[2:5]] + [
                (-1.0 if it[5] < 0 else 1.0) if it[1] == 21 else float(it[5])]     # AP_Mission: NAV_LAND param4 = yaw direction +-1
            or (it[0] != 2 and (b.x != int(it[6] * 1e7) or b.y != int(it[7] * 1e7)))
            or abs(b.z - it[8]) > 0.01)]                     # AP_Mission keeps altitudes in cm
        dz = max(abs(b.z - it[8]) for b, it in zip(back[1:], items[1:]))
        L(f"download back: {n} items, differences at seq {diff or 'none'} (command, params 1-4, x, y exact; "
          f"altitude max |difference| {dz:.4f} m, AP_Mission stores cm)")
        for s in diff:
            L(f"  seq {s}: sent {items[s]}, back {back[s]}")
        self.ok["mission"] = n == len(items) and not diff
        yield from self.sleep(1.0)
        r = yield from self.cmd(m.MAV_CMD_DO_SET_MODE, 1, 4)
        L(f"GUIDED: {r}")
        t0 = time.time()
        while True:
            r = yield from self.cmd(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
            if r == 0:
                break
            if time.time() - t0 > 90:
                raise RuntimeError("arming refused")
            L("arm refused, retrying")
            yield from self.sleep(2.0)
        L("armed")
        self.ok["armed"] = True
        alt = P["items"][0]["params"][6]
        r = yield from self.cmd(m.MAV_CMD_NAV_TAKEOFF, 0, 0, 0, 0, 0, 0, alt)
        L(f"takeoff to {alt} m: {r}")
        yield from self.wait(lambda: "GLOBAL_POSITION_INT" in self.latest and
                             self.latest["GLOBAL_POSITION_INT"].relative_alt > (alt - 0.3) * 1000, 60, "takeoff altitude")
        L(f"at {self.latest['GLOBAL_POSITION_INT'].relative_alt / 1000:.2f} m")
        self.ok["takeoff"] = True
        r = yield from self.cmd(m.MAV_CMD_DO_SET_MODE, 1, 3)
        L(f"AUTO: {r}")
        first_spl = next(i for i, q in enumerate(P["items"], start=1) if q["command"] == 82)
        yield from self.wait(lambda: "MISSION_CURRENT" in self.latest and self.latest["MISSION_CURRENT"].seq > first_spl,
                             120, "MISSION_CURRENT past the first spline waypoint")
        L(f"MISSION_CURRENT {self.latest['MISSION_CURRENT'].seq} (first spline waypoint was seq {first_spl})")
        self.ok["auto"] = True


vs = {s: V(s, p) for s, p in plans.items()}
last_hb = 0
cur = {}
parsers = {}
others = set()
while time.time() - T0 < timeout and not all(v.done for v in vs.values()):
    for v in vs.values():
        v.msgs = []
    while True:
        try:
            data, addr = sock.recvfrom(65536)
        except BlockingIOError:
            break
        if addr not in parsers:
            parsers[addr] = m.MAVLink(None)
            parsers[addr].robust_parsing = True
        for msg in parsers[addr].parse_buffer(data) or []:
            if msg.get_type() == "BAD_DATA":
                continue
            sid = msg.get_srcSystem()
            if msg.get_srcComponent() != 1:          # another component of the system (its camera): not the vehicle
                if msg.get_type() == "HEARTBEAT" and (sid, msg.get_srcComponent()) not in others:
                    others.add((sid, msg.get_srcComponent()))
                    log(f"component {sid}/{msg.get_srcComponent()} (type {msg.type}) at {addr}: not the vehicle, ignored")
                continue
            if sid not in vs:
                if msg.get_type() == "HEARTBEAT":
                    log(f"unexpected system id {sid} from {addr}")
                continue
            v = vs[sid]
            if v.addr is None:
                v.addr = addr
                log(f"system id {sid} at {addr}")
            elif v.addr != addr:
                log(f"system id {sid} now from {addr} (was {v.addr})")
            t = msg.get_type()
            v.msgs.append(msg)
            v.latest[t] = msg
            if t == "PARAM_VALUE":
                v.params += 1
            elif t == "STATUSTEXT":
                v.texts.append(msg.text)
            elif t == "MISSION_CURRENT" and cur.get(sid) != msg.seq:
                cur[sid] = msg.seq
                log(f"[sysid {sid}] MISSION_CURRENT {msg.seq}")
    if time.time() - last_hb > 1.0:
        last_hb = time.time()
        for v in vs.values():
            if v.addr:
                v.send(m.MAVLink_heartbeat_message(m.MAV_TYPE_GCS, m.MAV_AUTOPILOT_INVALID, 0, 0, m.MAV_STATE_ACTIVE, 3))
    for v in vs.values():
        if v.addr is not None and not v.done:
            try:
                next(v.script)
            except StopIteration:
                v.done = True
            except RuntimeError as e:
                log(f"FAILED: {e}")
                v.done = True
    time.sleep(0.005)
for v in vs.values():
    log(f"sysid {v.sysid}: {v.ok}")
ok = all(len(v.ok) == 5 and all(v.ok.values()) for v in vs.values())
log("RESULT " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
