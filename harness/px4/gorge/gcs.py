#!/usr/bin/env python3
"""A scripted ground station for the PX4 gorge flights: what a QGroundControl user does, on one UDP
port, for one or two vehicles (pymavlink's codec generated from PX4's message definitions).

  build/px4venv/bin/python -I px4/gorge/gcs.py --port P --vehicle 1=px4/plans/gorge.plan
          [--vehicle 2=PLAN] [--camera] [--log DIR] [--timeout S]

It binds UDP 127.0.0.1:P and waits for the vehicles, which send first (relay.py --gcs, as PX4 SITL
reaches QGroundControl on 14550; 14550 and 14560 are refused here). Vehicles are told apart by
their MAVLink system id (component 1 is the autopilot); replies go to the address each vehicle's
datagrams come from. For every vehicle, as QGroundControl does: heartbeats at 1 Hz, the parameter
list, the plan uploaded with the mission protocol (MISSION_COUNT, then MISSION_ITEM_INT for each
MISSION_REQUEST_INT: x, y = int(deg * 1e7), the plan's frame and params, null as NaN), then once
every vehicle has its mission and its home: arm (MAV_CMD_COMPONENT_ARM_DISARM, again every 3 s of
vehicle time while PX4 refuses), MAV_CMD_MISSION_START, and it watches the mission to the landing
and PX4's own disarm. With two vehicles both are armed and started together.

--camera: each vehicle's camera (component 100 of its system id, sim/world/camera_component.py)
must send heartbeats and answer REQUEST_MESSAGE for CAMERA_INFORMATION and
VIDEO_STREAM_INFORMATION; the streams' names and URIs are printed.

Every stage prints PASS or FAIL per vehicle. --log DIR writes vN.gpi.csv (each GLOBAL_POSITION_INT)
and vN.events.txt. Exit 0 when every stage of every vehicle passed. Commands sent to a vehicle:
at most one per vehicle second (navigator's assumption is at most 4 per 400 ticks)."""
import argparse
import json
import math
import os
import socket
import struct
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HARNESS, 'build/gen/px4_mavlink/pymav'))
import development as mav  # noqa: E402

CAMERA = 100


def stage(v, name, ok, detail=''):
    print('gcs: V%d %-36s %s %s' % (v.sysid, name, 'PASS' if ok else 'FAIL', detail), flush=True)
    v.stages.append((name, ok))
    return ok


class Vehicle:
    def __init__(self, sysid, plan_path):
        self.sysid = sysid
        self.plan_path = plan_path
        plan = json.load(open(plan_path))
        self.items = plan['mission']['items']
        self.addr = None
        self.parser = mav.MAVLink(None)
        self.parser.robust_parsing = True
        self.boot_ms = 0
        self.armed = None
        self.custom_mode = None
        self.landed_state = None
        self.params, self.param_count = {}, None
        self.home = None
        self.mission_ack = None
        self.mission_total = None
        self.reached = []
        self.current = None
        self.events = []
        self.gpi = []
        self.stages = []
        self.acks = []
        self.cam_hb = 0
        self.cam_info = None
        self.streams = {}
        self.cmds = []           # vehicle ms of every command sent
        self.ever_armed = False
        self.disarmed_after_flight = False
        self.texts = []

    def note(self, what):
        self.events.append((self.boot_ms, what))
        print('gcs:   V%d t %8.3f s  %s' % (self.sysid, self.boot_ms / 1000, what), flush=True)


class Station:
    def __init__(self, port, vehicles):
        self.s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4 << 20)
        self.s.bind(('127.0.0.1', port))
        self.s.settimeout(0.02)
        self.m = mav.MAVLink(None, srcSystem=255, srcComponent=190)
        self.v = {x.sysid: x for x in vehicles}
        self.cam_addr = {}
        self.cam_parser = {}
        self.last_hb = 0.0

    def send(self, v, msg, to_camera=False):
        addr = self.cam_addr.get(v.sysid) if to_camera else v.addr
        if addr is not None:
            self.s.sendto(msg.pack(self.m), addr)

    def command(self, v, cmd, *p):
        v.cmds.append(v.boot_ms)
        self.send(v, self.m.command_long_encode(v.sysid, 1, cmd, 0, *(list(p) + [0] * (7 - len(p)))))

    def poll(self):
        if time.monotonic() - self.last_hb > 1.0:
            for v in self.v.values():
                self.send(v, self.m.heartbeat_encode(mav.MAV_TYPE_GCS, mav.MAV_AUTOPILOT_INVALID, 0, 0,
                                                     mav.MAV_STATE_ACTIVE))
            self.last_hb = time.monotonic()
        try:
            data, addr = self.s.recvfrom(65536)
        except socket.timeout:
            return
        # who sent it: parse with a parser per source address
        p = self.cam_parser.setdefault(addr, mav.MAVLink(None))
        p.robust_parsing = True
        for x in p.parse_buffer(data) or []:
            if x.get_type() == 'BAD_DATA':
                continue
            v = self.v.get(x.get_srcSystem())
            if v is None:
                continue
            if x.get_srcComponent() == CAMERA:
                self.cam_addr[v.sysid] = addr
                self.on_camera(v, x)
            elif x.get_srcComponent() == 1:
                if v.addr is None:
                    v.addr = addr
                    print('gcs:   V%d first datagram from %s:%d' % ((v.sysid,) + addr), flush=True)
                self.on_vehicle(v, x)

    def on_camera(self, v, x):
        t = x.get_type()
        if t == 'HEARTBEAT':
            v.cam_hb += 1
        elif t == 'CAMERA_INFORMATION':
            v.cam_info = x
        elif t == 'VIDEO_STREAM_INFORMATION':
            v.streams[x.stream_id] = (x.name, x.uri, x.resolution_h, x.resolution_v, x.framerate)

    def on_vehicle(self, v, x):
        t = x.get_type()
        if hasattr(x, 'time_boot_ms'):
            v.boot_ms = max(v.boot_ms, x.time_boot_ms)
        if t == 'HEARTBEAT':
            armed = bool(x.base_mode & mav.MAV_MODE_FLAG_SAFETY_ARMED)
            if armed != v.armed:
                v.note('armed' if armed else 'disarmed')
                if armed:
                    v.ever_armed = True
                elif v.ever_armed:
                    v.disarmed_after_flight = True
            if x.custom_mode != v.custom_mode:
                v.note('mode main %d sub %d' % ((x.custom_mode >> 16) & 0xff, (x.custom_mode >> 24) & 0xff))
            v.armed, v.custom_mode = armed, x.custom_mode
        elif t == 'PARAM_VALUE':
            v.param_count = x.param_count
            if x.param_index < x.param_count:      # 65535: a value sent on its own, not by index
                v.params[x.param_index] = (x.param_id, x.param_value, x.param_type)
        elif t == 'HOME_POSITION':
            if v.home is None:
                v.note('home lat %d lon %d alt %d mm' % (x.latitude, x.longitude, x.altitude))
            v.home = x
        elif t == 'GLOBAL_POSITION_INT':
            v.gpi.append((x.time_boot_ms, x.lat, x.lon, x.alt, x.relative_alt, x.hdg))
        elif t == 'EXTENDED_SYS_STATE':
            if x.landed_state != v.landed_state:
                v.note('landed_state %d' % x.landed_state)
            v.landed_state = x.landed_state
        elif t == 'MISSION_ITEM_REACHED':
            if not v.reached or v.reached[-1] != x.seq:
                v.reached.append(x.seq)
                v.note('mission item %d reached' % x.seq)
        elif t == 'MISSION_CURRENT':
            v.mission_total = x.total
            if x.seq != v.current:
                v.current = x.seq
        elif t in ('MISSION_REQUEST_INT', 'MISSION_REQUEST') and x.target_system == 255:
            self.send_item(v, x.seq)
        elif t == 'MISSION_ACK' and x.target_system == 255:
            v.mission_ack = x.type
            v.note('MISSION_ACK type %d' % x.type)
        elif t == 'COMMAND_ACK':
            v.acks.append((x.command, x.result))
            v.note('COMMAND_ACK %d result %d' % (x.command, x.result))
        elif t == 'STATUSTEXT':
            v.texts.append(x.text)
            v.note('STATUSTEXT %s' % x.text)

    def send_item(self, v, seq):
        if seq >= len(v.items):
            return
        it = v.items[seq]
        p = [float('nan') if q is None else float(q) for q in it['params']]
        if it['frame'] == mav.MAV_FRAME_MISSION:
            x, y = int(p[4]), int(p[5])
        else:
            x, y = int(p[4] * 1e7), int(p[5] * 1e7)
        self.send(v, self.m.mission_item_int_encode(v.sysid, 1, seq, it['frame'], it['command'], 0,
                                                    1 if it['autoContinue'] else 0, p[0], p[1], p[2], p[3],
                                                    x, y, p[6], mav.MAV_MISSION_TYPE_MISSION))

    def until(self, pred, timeout):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            self.poll()
            if pred():
                return True
        return False


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--port', type=int, required=True)
    ap.add_argument('--vehicle', action='append', required=True, help='SYSID=PLAN')
    ap.add_argument('--camera', action='store_true')
    ap.add_argument('--log', default=None)
    ap.add_argument('--timeout', type=float, default=900.0, help='wall-clock seconds for the whole flight')
    a = ap.parse_args()
    if a.port in (14550, 14560):
        raise SystemExit('gcs: not on 14550 (the ground station\'s) or 14560')
    vs = [Vehicle(int(s.split('=', 1)[0]), s.split('=', 1)[1]) for s in a.vehicle]
    G = Station(a.port, vs)
    t_end = time.monotonic() + a.timeout
    left = lambda: max(1.0, t_end - time.monotonic())
    every = list(G.v.values())

    # 1. heartbeats
    ok = G.until(lambda: all(v.addr is not None and v.armed is not None for v in every), min(300, left()))
    for v in every:
        stage(v, 'vehicle heartbeat', v.addr is not None and v.armed is not None)
    if not ok:
        return finish(G, a)
    # 2. the parameter list (QGroundControl's first request), then the missing ones by index
    for v in every:
        G.send(v, G.m.param_request_list_encode(v.sysid, 1))
    G.until(lambda: all(v.param_count is not None and len(v.params) >= v.param_count for v in every),
            min(600, left()))
    for _ in range(3):
        for v in every:
            if v.param_count is not None:
                for i in [i for i in range(v.param_count) if i not in v.params][:200]:
                    G.send(v, G.m.param_request_read_encode(v.sysid, 1, b'', i))
        G.until(lambda: all(v.param_count is not None and len(v.params) >= v.param_count for v in every), 20)
    for v in every:
        stage(v, 'parameter download', v.param_count is not None and len(v.params) == v.param_count,
              '%d of %s (vehicle t %.1f s)' % (len(v.params), v.param_count, v.boot_ms / 1000))
        # PX4 sends an integer parameter's bytes in the float field (MAV_PARAM_TYPE_INT32)
        sid = [struct.unpack('<i', struct.pack('<f', val))[0] if typ == mav.MAV_PARAM_TYPE_INT32 else val
               for (pid, val, typ) in v.params.values() if pid == 'MAV_SYS_ID']
        stage(v, 'MAV_SYS_ID', sid == [v.sysid], 'parameter %s' % sid)
    # 3. the mission upload
    for v in every:
        G.send(v, G.m.mission_count_encode(v.sysid, 1, len(v.items), mav.MAV_MISSION_TYPE_MISSION, 0))
    G.until(lambda: all(v.mission_ack is not None for v in every), min(300, left()))
    for v in every:
        stage(v, 'mission upload (%d items)' % len(v.items), v.mission_ack == mav.MAV_MISSION_ACCEPTED,
              'ack type %s, %s' % (v.mission_ack, os.path.basename(v.plan_path)))
    G.until(lambda: all(v.mission_total == len(v.items) for v in every), min(120, left()))
    for v in every:
        stage(v, 'vehicle reports the mission', v.mission_total == len(v.items), 'total %s' % v.mission_total)
    # 4. home (EKF2's origin and position)
    G.until(lambda: all(v.home is not None for v in every), min(600, left()))
    for v in every:
        stage(v, 'home position', v.home is not None, 'vehicle t %.1f s' % (v.boot_ms / 1000))
    if any(v.home is None or v.mission_ack != mav.MAV_MISSION_ACCEPTED for v in every):
        return finish(G, a)
    if a.camera:
        # the camera announces itself by heartbeat (it starts with the session; its render workers load the
        # world first), then answers REQUEST_MESSAGE; asked again every 2 s until it has answered
        G.until(lambda: all(v.sysid in G.cam_addr for v in every), 180)

        def ask():
            for v in every:
                if v.cam_info is None or len(v.streams) < 2:
                    for msg_id in (mav.MAVLINK_MSG_ID_CAMERA_INFORMATION, mav.MAVLINK_MSG_ID_VIDEO_STREAM_INFORMATION):
                        G.send(v, G.m.command_long_encode(v.sysid, CAMERA, mav.MAV_CMD_REQUEST_MESSAGE, 0,
                                                          msg_id, 0, 0, 0, 0, 0, 0), to_camera=True)
        for _ in range(15):
            ask()
            if G.until(lambda: all(v.cam_info is not None and len(v.streams) >= 2 for v in every), 2):
                break
        for v in every:
            stage(v, 'camera heartbeat and information', v.cam_hb > 0 and v.cam_info is not None,
                  '%d heartbeats' % v.cam_hb)
            stage(v, 'video streams announced', len(v.streams) >= 2, '; '.join(
                '%d %s %s %dx%d@%.1f' % ((k,) + tuple(s)) for k, s in sorted(v.streams.items())))
    # 5. arm, all vehicles together, again while PX4 refuses
    armed_ok = {v.sysid: False for v in every}
    for attempt in range(40):
        for v in every:
            if not armed_ok[v.sysid]:
                v.acks = []
                G.command(v, mav.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        G.until(lambda: all(armed_ok[v.sysid] or any(c == 400 for c, _ in v.acks) for v in every), 30)
        for v in every:
            if any(c == 400 and r == mav.MAV_RESULT_ACCEPTED for c, r in v.acks):
                armed_ok[v.sysid] = True
        if all(armed_ok.values()):
            break
        t0 = {v.sysid: v.boot_ms for v in every}
        G.until(lambda: all(v.boot_ms > t0[v.sysid] + 3000 for v in every), 60)
    for v in every:
        stage(v, 'arm accepted', armed_ok[v.sysid], 'attempt %d (vehicle t %.1f s)' % (attempt + 1, v.boot_ms / 1000))
    # 6. mission start
    for v in every:
        v.acks = []
        G.command(v, mav.MAV_CMD_MISSION_START, 0, 0)
    G.until(lambda: all(any(c == 300 for c, _ in v.acks) for v in every), 30)
    for v in every:
        r = [r for c, r in v.acks if c == 300]
        stage(v, 'MISSION_START accepted', r[:1] == [mav.MAV_RESULT_ACCEPTED], 'result %s' % r)
    # 7. the mission to PX4's own disarm
    G.until(lambda: all(v.disarmed_after_flight and v.landed_state == mav.MAV_LANDED_STATE_ON_GROUND
                        for v in every), left())
    for v in every:
        # PX4 reports the last item reached per update: the takeoff and the speed change can share one
        want = [i for i, it in enumerate(v.items) if it['command'] in (16, 21)]
        stage(v, 'every waypoint and the landing reached', set(want) <= set(v.reached),
              'reached %s' % v.reached)
        stage(v, 'landed and disarmed by PX4', v.disarmed_after_flight and
              v.landed_state == mav.MAV_LANDED_STATE_ON_GROUND, 'vehicle t %.1f s' % (v.boot_ms / 1000))
    return finish(G, a)


def finish(G, a):
    G.s.close()
    ok = True
    for v in G.v.values():
        ok &= all(o for _, o in v.stages) and bool(v.stages)
        if a.log:
            os.makedirs(a.log, exist_ok=True)
            with open(os.path.join(a.log, 'v%d.gpi.csv' % v.sysid), 'w') as f:
                f.write('time_boot_ms,lat,lon,alt_mm,relative_alt_mm,hdg_cdeg\n')
                for g in v.gpi:
                    f.write(','.join(map(str, g)) + '\n')
            with open(os.path.join(a.log, 'v%d.events.txt' % v.sysid), 'w') as f:
                for t, e in v.events:
                    f.write('%.3f %s\n' % (t / 1000, e))
        # commands per vehicle second, for navigator's window (4 per 400 ticks)
        c = sorted(v.cmds)
        worst = max((sum(1 for y in c if x <= y < x + 1000) for x in c), default=0)
        print('gcs: V%d %d commands sent, at most %d in any vehicle second' % (v.sysid, len(c), worst))
    print('gcs: %s' % ('PASS' if ok else 'FAIL'), flush=True)
    return 0 if ok else 1


sys.exit(main())
