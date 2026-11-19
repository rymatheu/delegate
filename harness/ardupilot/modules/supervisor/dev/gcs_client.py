#!/usr/bin/env python3
"""A scripted ground station for dev/udp_bridge.py (headless test; no QGroundControl).

  python3 -I ardupilot/modules/supervisor/dev/gcs_client.py [--port 14560] [--timeout 150] [--listen]

--listen: bind 127.0.0.1:PORT and wait for the vehicle to send first (as QGroundControl's default
UDP link does; the bridge runs with --gcs 127.0.0.1:PORT); otherwise send to a listening vehicle.
Before arming it waits (up to 120 s) for the EKF: EKF_STATUS_REPORT with an absolute horizontal
position (EKF_POS_HORIZ_ABS) and GPS_RAW_INT with a 3D fix.

MAVLink 2 over UDP to 127.0.0.1:PORT, with the ardupilotmega dialect pymavlink's mavgen wrote
(build/gen/supervisor/py/apm.py, dev/gen_pymavlink.sh). In order: heartbeat (1 Hz throughout),
all data streams at 4 Hz, the whole parameter list (PARAM_REQUEST_LIST until param_count values,
re-requesting missing indices once), a 5-item mission upload, GUIDED, arm, takeoff to 2 m, LAND
at 1.8 m, wait for the disarm. Prints each step's result and the messages received.
"""
import math
import os
import socket
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(HARNESS, 'deps', 'mavlink'))
sys.path.insert(0, os.path.join(HARNESS, 'build', 'gen', 'supervisor', 'py'))
os.environ.setdefault('MAVLINK20', '1')
import apm as mav  # noqa: E402

PORT = int(sys.argv[sys.argv.index('--port') + 1]) if '--port' in sys.argv else 14560
TIMEOUT = float(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 150
ORIGIN = [473977420, 85455940]


LISTEN = '--listen' in sys.argv


class Link:
    def __init__(self):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.settimeout(0.05)
        self.peer = ('127.0.0.1', PORT)
        if LISTEN:
            if PORT == 14550:
                raise SystemExit('gcs_client: 14550 is not used here')
            self.sock.bind(('127.0.0.1', PORT))
            self.peer = None   # learned from the vehicle's first datagram
        self.m = mav.MAVLink(None, srcSystem=255, srcComponent=190)
        self.rx = mav.MAVLink(None)
        self.rx.robust_parsing = True
        self.counts = {}
        self.nan = {}
        self.last_hb = 0
        self.state = {}

    def send(self, msg):
        if self.peer is not None:
            self.sock.sendto(msg.pack(self.m), self.peer)

    def poll(self):
        now = time.monotonic()
        if now - self.last_hb > 1:
            self.send(self.m.heartbeat_encode(mav.MAV_TYPE_GCS, mav.MAV_AUTOPILOT_INVALID, 0, 0,
                                              0))
            self.last_hb = now
        msgs = []
        try:
            data, addr = self.sock.recvfrom(65536)
            if self.peer is None:
                self.peer = addr
                print('vehicle at %s:%d' % addr)
            msgs = self.rx.parse_buffer(data) or []
        except socket.timeout:
            pass
        for msg in msgs:
            t = msg.get_type()
            for fld in msg.get_fieldnames():
                v = getattr(msg, fld)
                if isinstance(v, float) and math.isnan(v):
                    self.nan['%s.%s' % (t, fld)] = self.nan.get('%s.%s' % (t, fld), 0) + 1
            self.counts[t] = self.counts.get(t, 0) + 1
            self.state[t] = msg
            if t == 'STATUSTEXT':
                print('  STATUSTEXT', msg.text)
        return msgs

    def wait(self, pred, timeout):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            for msg in self.poll():
                if pred(msg):
                    return msg
        return None


def item(m, seq, cmd, n, e, alt, frame=mav.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT):
    lat = ORIGIN[0] + int(round(n / 111319.49079327357 * 1e7))
    lon = ORIGIN[1] + int(round(e / (111319.49079327357 * math.cos(math.radians(ORIGIN[0] * 1e-7)))
                                * 1e7))
    return m.mission_item_int_encode(1, 1, seq, frame, cmd, 0, 1, 0, 0, 0, 0, lat, lon, alt)


def main():
    t0 = time.monotonic()
    L = Link()
    hb = L.wait(lambda x: x.get_type() == 'HEARTBEAT', 20)
    print('heartbeat:', 'type %d autopilot %d mode %d' % (hb.type, hb.autopilot, hb.custom_mode)
          if hb else 'NONE')
    if hb is None:
        return 1
    L.send(L.m.request_data_stream_encode(1, 1, mav.MAV_DATA_STREAM_ALL, 4, 1))
    # parameters
    L.send(L.m.param_request_list_encode(1, 1))
    got, count = {}, None
    end = time.monotonic() + 60
    retried = False
    while time.monotonic() < end and (count is None or len(got) < count):
        for msg in L.poll():
            if msg.get_type() == 'PARAM_VALUE':
                count = msg.param_count
                if msg.param_index != 65535:
                    got[msg.param_index] = msg.param_id
        if count and not retried and time.monotonic() > end - 20:
            for i in range(count):
                if i not in got:
                    L.send(L.m.param_request_read_encode(1, 1, b'', i))
            retried = True
    print('parameters: %d of %s in %.1f s' % (len(got), count, time.monotonic() - t0))
    # wait for the EKF (real estimator) before arming
    ekf = L.wait(lambda x: x.get_type() == 'EKF_STATUS_REPORT' and (x.flags & 16) and
                 not (x.flags & 128) and L.state.get('GPS_RAW_INT') is not None and
                 L.state['GPS_RAW_INT'].fix_type >= 3, 120)
    print('EKF ready:', 'flags 0x%x at %.1f s' % (ekf.flags, time.monotonic() - t0) if ekf
          else 'NO (last %s)' % L.state.get('EKF_STATUS_REPORT'))
    # mission, relative to the EKF origin the vehicle reports (GPS_GLOBAL_ORIGIN)
    go = L.state.get('GPS_GLOBAL_ORIGIN') or L.wait(
        lambda x: x.get_type() == 'GPS_GLOBAL_ORIGIN', 10)
    if go is not None:
        ORIGIN[0], ORIGIN[1] = go.latitude, go.longitude
    print('origin:', ORIGIN)
    mission = [item(L.m, 0, mav.MAV_CMD_NAV_WAYPOINT, 0, 0, 0, mav.MAV_FRAME_GLOBAL),
               item(L.m, 1, mav.MAV_CMD_NAV_TAKEOFF, 0, 0, 2),
               item(L.m, 2, mav.MAV_CMD_NAV_WAYPOINT, 10, 0, 2),
               item(L.m, 3, mav.MAV_CMD_NAV_WAYPOINT, 20, 0, 2),
               item(L.m, 4, mav.MAV_CMD_NAV_LAND, 20, 0, 0)]
    L.send(L.m.mission_count_encode(1, 1, len(mission), 0))
    ack = None
    end = time.monotonic() + 20
    while time.monotonic() < end and ack is None:
        for msg in L.poll():
            if msg.get_type() in ('MISSION_REQUEST_INT', 'MISSION_REQUEST'):
                L.send(mission[msg.seq])
            elif msg.get_type() == 'MISSION_ACK':
                ack = msg
    print('mission upload:', 'MISSION_ACK type %d' % ack.type if ack else 'NO ACK')
    # GUIDED, arm, takeoff
    L.send(L.m.set_mode_encode(1, mav.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED, 4))
    hb = L.wait(lambda x: x.get_type() == 'HEARTBEAT' and x.custom_mode == 4, 10)
    print('GUIDED:', 'yes' if hb else 'NO')
    L.send(L.m.command_long_encode(1, 1, mav.MAV_CMD_COMPONENT_ARM_DISARM, 0, 1, 0, 0, 0, 0, 0, 0))
    a = L.wait(lambda x: x.get_type() == 'COMMAND_ACK' and x.command == 400, 10)
    print('arm:', 'result %d' % a.result if a else 'NO ACK')
    L.send(L.m.command_long_encode(1, 1, mav.MAV_CMD_NAV_TAKEOFF, 0, 0, 0, 0, 0, 0, 0, 2))
    a = L.wait(lambda x: x.get_type() == 'COMMAND_ACK' and x.command == 22, 10)
    print('takeoff:', 'result %d' % a.result if a else 'NO ACK')
    top = L.wait(lambda x: x.get_type() == 'GLOBAL_POSITION_INT' and x.relative_alt > 1800, 30)
    print('altitude 1.8 m:', ('relative_alt %d mm at %.1f s' % (top.relative_alt,
                                                                time.monotonic() - t0))
          if top else 'NOT REACHED (last %s)' % L.state.get('GLOBAL_POSITION_INT'))
    L.send(L.m.set_mode_encode(1, mav.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED, 9))
    d = L.wait(lambda x: x.get_type() == 'HEARTBEAT' and not (x.base_mode &
                                                              mav.MAV_MODE_FLAG_SAFETY_ARMED), 40)
    print('landed and disarmed:', 'yes at %.1f s' % (time.monotonic() - t0) if d else 'NO')
    print('messages:', dict(sorted(L.counts.items())))
    print('telemetry fields that carried NaN:', L.nan or 'none')
    L.sock.close()
    return 0


sys.exit(main())
