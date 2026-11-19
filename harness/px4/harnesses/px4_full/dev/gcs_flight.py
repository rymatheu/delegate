#!/usr/bin/env python3
"""A headless ground-station flight against px4/harnesses/px4_full/dev/relay.py (scripted, with
pymavlink's codec generated from PX4's message definitions; no QGroundControl):

  build/px4venv/bin/python px4/harnesses/px4_full/dev/gcs_flight.py (mission | commands)
          [--port 14570] [--listen] [--truth FILE.csv] [--log FILE.csv]

Talks to the vehicle on UDP 127.0.0.1:PORT (default 14570; never 14550 or 14560) as QGroundControl
does: heartbeats at 1 Hz, the whole parameter list, then

  mission:  waits for the vehicle's home, uploads a mission (NAV_TAKEOFF 2.5 m above home,
            NAV_WAYPOINT 10 m north of home at 2.5 m, NAV_LAND there), arms, sets AUTO MISSION,
            and watches the mission to PX4's own landing and auto-disarm;
  compare:  (after a flight, with --log and --truth) each GLOBAL_POSITION_INT against the truth;
  commands: waits for home, arms, MAV_CMD_NAV_TAKEOFF (PX4's default altitude), then
            MAV_CMD_DO_REPOSITION to 10 m north of home at the same altitude (COMMAND_INT), then
            MAV_CMD_NAV_LAND, and watches to the auto-disarm.

Without --listen the vehicle listens on PORT (relay.py --port) and this sends first, from an
ephemeral port. With --listen this binds 127.0.0.1:PORT and waits for the vehicle, which sends
first (relay.py --gcs, px4/fly_qgc.sh): QGroundControl's side of PX4 SITL's link, on a test port;
it answers to the address the vehicle's datagrams come from.

Every stage prints PASS or FAIL. --log writes the vehicle's GLOBAL_POSITION_INT reports; the
`compare` mode reads them with the relay's --truth CSV and compares each with the simulator's
position at the same vehicle time (time_boot_ms is PX4's clock, the simulator's t_us / 1000):
PASS when every report is within --hbound m (default 1.0, EKF2's horizontal bound in px4_nav_loop's
truth clauses) horizontally and --vbound m (default 1.5, its height bound after the land command)
in altitude.
The vehicle's clock runs at the harness's speed, so the timeouts here are generous wall-clock
ones. Exit 0 when every stage passed. Closes its socket."""
import csv
import math
import os
import socket
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(HERE))))
sys.path.insert(0, os.path.join(HARNESS, 'build/gen/px4_mavlink/pymav'))
import development as mav  # noqa: E402

MODE = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else 'mission'
PORT = int(sys.argv[sys.argv.index('--port') + 1]) if '--port' in sys.argv else 14570
if PORT in (14550, 14560):
    raise SystemExit('gcs_flight: not on 14550 (the ground station\'s) or 14560')
TRUTH = sys.argv[sys.argv.index('--truth') + 1] if '--truth' in sys.argv else None
LOG = sys.argv[sys.argv.index('--log') + 1] if '--log' in sys.argv else None
LISTEN = '--listen' in sys.argv
HBOUND = float(sys.argv[sys.argv.index('--hbound') + 1]) if '--hbound' in sys.argv else 1.0
VBOUND = float(sys.argv[sys.argv.index('--vbound') + 1]) if '--vbound' in sys.argv else 1.5
# the simulator's start (its noise-free GPS at rest), PX4's earth radius
LAT0, LON0, ALT0 = 38.84055560937258, -105.04416668582736, 4302.00005
R = 6371000.0
KN = R * math.pi / 180
KE = KN * math.cos(math.radians(LAT0))
NORTH = 10.0
ALT_REL = 2.5


class Link:
    def __init__(self):
        self.s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4 << 20)
        self.s.bind(('127.0.0.1', PORT if LISTEN else 0))
        # where the vehicle is: its port, or (listening) the address its first datagram came from
        self.peer = None if LISTEN else ('127.0.0.1', PORT)
        self.s.settimeout(0.05)
        self.m = mav.MAVLink(None, srcSystem=255, srcComponent=190)
        self.m.robust_parsing = True
        self.last_hb = 0.0
        self.seen = {}
        self.gpi = []          # (time_boot_ms, lat, lon, alt mm, relative_alt mm)
        self.boot_ms = 0
        self.armed = None
        self.custom_mode = None
        self.landed_state = None
        self.events = []
        self.last_report = time.monotonic()
        self.period = {}

    def send(self, msg):
        if self.peer is None:
            return      # listening, and the vehicle has not sent yet
        self.s.sendto(msg.pack(self.m), self.peer)

    def note(self, what):
        self.events.append((self.boot_ms, what))
        print('gcs_flight:   vehicle t %8.3f s  %s' % (self.boot_ms / 1000, what), flush=True)

    def poll(self):
        if time.monotonic() - self.last_hb > 1.0:
            self.send(self.m.heartbeat_encode(mav.MAV_TYPE_GCS, mav.MAV_AUTOPILOT_INVALID, 0, 0,
                                              mav.MAV_STATE_ACTIVE))
            self.last_hb = time.monotonic()
        try:
            data, addr = self.s.recvfrom(65536)
        except socket.timeout:
            return []
        if LISTEN and self.peer is None:
            self.peer = addr
            print('gcs_flight:   first datagram from the vehicle at %s:%d' % addr, flush=True)
        msgs = [x for x in (self.m.parse_buffer(data) or []) if x.get_type() != 'BAD_DATA']
        if time.monotonic() - self.last_report > 20:
            print('gcs_flight:   (vehicle t %.1f s; last 20 s: %s)' % (self.boot_ms / 1000, ', '.join(
                '%s %d' % kv for kv in sorted(self.period.items()))), flush=True)
            self.period, self.last_report = {}, time.monotonic()
        for x in msgs:
            t = x.get_type()
            self.seen[t] = self.seen.get(t, 0) + 1
            self.period[t] = self.period.get(t, 0) + 1
            if hasattr(x, 'time_boot_ms'):
                self.boot_ms = max(self.boot_ms, x.time_boot_ms)
            if t == 'GLOBAL_POSITION_INT':
                self.gpi.append((x.time_boot_ms, x.lat, x.lon, x.alt, x.relative_alt))
            elif t == 'HEARTBEAT' and x.get_srcSystem() == 1 and x.get_srcComponent() == 1:
                armed = bool(x.base_mode & mav.MAV_MODE_FLAG_SAFETY_ARMED)
                if armed != self.armed:
                    self.note('armed' if armed else 'disarmed')
                if x.custom_mode != self.custom_mode:
                    self.note('custom_mode main %d sub %d' % ((x.custom_mode >> 16) & 0xff,
                                                             (x.custom_mode >> 24) & 0xff))
                self.armed, self.custom_mode = armed, x.custom_mode
            elif t == 'EXTENDED_SYS_STATE':
                if x.landed_state != self.landed_state:
                    self.note('landed_state %d' % x.landed_state)
                self.landed_state = x.landed_state
            elif t == 'MISSION_ITEM_REACHED':
                self.note('mission item %d reached' % x.seq)
            elif t == 'COMMAND_ACK':
                self.note('COMMAND_ACK %d result %d' % (x.command, x.result))
            elif t == 'STATUSTEXT':
                self.note('STATUSTEXT %s' % x.text)
        return msgs

    def wait(self, pred, timeout, resend=None, every=2.0):
        end, last = time.monotonic() + timeout, None
        while time.monotonic() < end:
            if resend and (last is None or time.monotonic() - last > every):
                resend()
                last = time.monotonic()
            for x in self.poll():
                if pred(x):
                    return x
        return None


def stage(name, ok, detail=''):
    print('gcs_flight: %-38s %s %s' % (name, 'PASS' if ok else 'FAIL', detail), flush=True)
    return ok


def compare(gpi):
    """Each GLOBAL_POSITION_INT against the simulator's truth at the same vehicle time."""
    rows = list(csv.DictReader(open(TRUTH)))
    by_t = {int(r['t_us']) // 1000: r for r in rows}
    hmax, vmax, n = 0.0, 0.0, 0
    worst = None
    for tb, lat, lon, alt, rel in gpi:
        r = by_t.get(tb)
        if r is None:
            continue
        tn, te, td = float(r['pos_n']), float(r['pos_e']), float(r['pos_d'])
        en = (lat * 1e-7 - LAT0) * KN - tn
        ee = (lon * 1e-7 - LON0) * KE - te
        ea = alt * 1e-3 - (ALT0 - td)
        h = math.hypot(en, ee)
        n += 1
        if h > hmax:
            hmax, worst = h, (tb, en, ee)
        vmax = max(vmax, abs(ea))
    return n, hmax, vmax, worst


def arm(L, tries=60):
    """Arm as a ground-station user does: again every few seconds while PX4 refuses (its
    pre-flight checks pass once EKF2 has a position and the sensors are calibrated)."""
    r = None
    for k in range(tries):
        r = command(L, mav.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        if r == mav.MAV_RESULT_ACCEPTED:
            return r, k + 1
        t = L.boot_ms
        L.wait(lambda x: L.boot_ms > t + 2000, 600)
    return r, tries


def command(L, cmd, *p, use_int=False, x=0, y=0, z=0.0):
    if use_int:
        msg = lambda: L.send(L.m.command_int_encode(1, 1, mav.MAV_FRAME_GLOBAL, cmd, 0, 0, *p, x, y, z))
    else:
        msg = lambda: L.send(L.m.command_long_encode(1, 1, cmd, 0, *(list(p) + [0] * (7 - len(p)))))
    msg()
    a = L.wait(lambda m: m.get_type() == 'COMMAND_ACK' and m.command == cmd, 600)
    return a.result if a else None


def main():
    L = Link()
    ok = True
    hb = L.wait(lambda x: x.get_type() == 'HEARTBEAT' and x.get_srcSystem() == 1, 300)
    ok &= stage('vehicle heartbeat', hb is not None)
    params, count = {}, [None]

    def on_param(x):
        if x.get_type() == 'PARAM_VALUE':
            count[0] = x.param_count
            params[x.param_index] = (x.param_id, x.param_value)
            return count[0] is not None and len(params) >= count[0]
        return False
    L.wait(on_param, 3600, resend=lambda: L.send(L.m.param_request_list_encode(1, 1)), every=1e9)
    for _ in range(3):
        if count[0] is None or len(params) >= count[0]:
            break
        for i in [i for i in range(count[0]) if i not in params]:
            L.send(L.m.param_request_read_encode(1, 1, b'', i))
        L.wait(on_param, 600)
    ok &= stage('parameter download', count[0] is not None and len(params) == count[0],
                '%d of %s (vehicle t %.1f s)' % (len(params), count[0], L.boot_ms / 1000))
    home = L.wait(lambda x: x.get_type() == 'HOME_POSITION', 7200,
                  resend=lambda: L.send(L.m.command_long_encode(
                      1, 1, mav.MAV_CMD_REQUEST_MESSAGE, 0, mav.MAVLINK_MSG_ID_HOME_POSITION,
                      0, 0, 0, 0, 0, 0)), every=20)
    ok &= stage('home position', home is not None, home and 'lat %d lon %d alt %d mm (vehicle t %.1f s)'
                % (home.latitude, home.longitude, home.altitude, L.boot_ms / 1000) or '')
    if home is None:
        return 1
    hlat, hlon = home.latitude, home.longitude
    tlat = hlat + int(round(NORTH / KN * 1e7))
    if MODE == 'mission':
        items = [(mav.MAV_CMD_NAV_TAKEOFF, hlat, hlon, ALT_REL),
                 (mav.MAV_CMD_NAV_WAYPOINT, tlat, hlon, ALT_REL),
                 (mav.MAV_CMD_NAV_LAND, tlat, hlon, 0.0)]
        acked = [None]

        def on_mission(x):
            t = x.get_type()
            if t in ('MISSION_REQUEST_INT', 'MISSION_REQUEST') and x.seq < len(items):
                c, la, lo, al = items[x.seq]
                L.send(L.m.mission_item_int_encode(1, 1, x.seq, mav.MAV_FRAME_GLOBAL_RELATIVE_ALT,
                                                   c, 0, 1, 0, 0, 0, float('nan'), la, lo, al, 0))
            if t == 'MISSION_ACK':
                acked[0] = x.type
                return True
            return False
        L.wait(on_mission, 1200, resend=lambda: L.send(L.m.mission_count_encode(1, 1, len(items), 0)),
               every=1e9)
        ok &= stage('mission upload', acked[0] == mav.MAV_MISSION_ACCEPTED, 'ack type %s' % acked[0])
        cur = L.wait(lambda x: x.get_type() == 'MISSION_CURRENT' and x.total == len(items), 1200)
        ok &= stage('vehicle reports the mission', cur is not None)
        r, n = arm(L)
        ok &= stage('arm accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s at attempt %d '
                    '(vehicle t %.1f s)' % (r, n, L.boot_ms / 1000))
        r = command(L, mav.MAV_CMD_DO_SET_MODE, 1, 4, 4)
        ok &= stage('AUTO MISSION accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s' % r)
        last = L.wait(lambda x: x.get_type() == 'MISSION_ITEM_REACHED' and x.seq == 1, 7200)
        ok &= stage('waypoint 10 m north reached', last is not None,
                    'vehicle t %.1f s' % (L.boot_ms / 1000))
    else:
        r, n = arm(L)
        ok &= stage('arm accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s at attempt %d '
                    '(vehicle t %.1f s)' % (r, n, L.boot_ms / 1000))
        r = command(L, mav.MAV_CMD_NAV_TAKEOFF, 0, 0, 0, float('nan'), float('nan'), float('nan'),
                    float('nan'))
        ok &= stage('takeoff accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s (vehicle t %.1f s)'
                    % (r, L.boot_ms / 1000))
        LOITER = (4 << 16) | (3 << 24)
        hold = L.wait(lambda x: x.get_type() == 'HEARTBEAT' and x.get_srcSystem() == 1 and
                      x.custom_mode == LOITER and L.landed_state == mav.MAV_LANDED_STATE_IN_AIR, 7200)
        ok &= stage('takeoff done, holding', hold is not None, 'vehicle t %.1f s' % (L.boot_ms / 1000))
        r = command(L, mav.MAV_CMD_DO_REPOSITION, -1, mav.MAV_DO_REPOSITION_FLAGS_CHANGE_MODE, 0,
                    float('nan'), use_int=True, x=tlat, y=hlon, z=float('nan'))
        ok &= stage('reposition accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s (vehicle t %.1f s)'
                    % (r, L.boot_ms / 1000))
        t_rep = L.boot_ms
        L.wait(lambda x: L.boot_ms > t_rep + 12000, 7200)
        r = command(L, mav.MAV_CMD_NAV_LAND, 0, 0, 0, float('nan'), float('nan'), float('nan'),
                    float('nan'))
        ok &= stage('land accepted', r == mav.MAV_RESULT_ACCEPTED, 'result %s (vehicle t %.1f s)'
                    % (r, L.boot_ms / 1000))
    landed = L.wait(lambda x: L.landed_state == mav.MAV_LANDED_STATE_ON_GROUND and L.armed is False
                    and L.boot_ms > 20000, 7200)
    ok &= stage('landed and disarmed by PX4', landed is not None, 'vehicle t %.1f s' % (L.boot_ms / 1000))
    print('gcs_flight: messages seen: %s' % ', '.join('%s %d' % kv for kv in sorted(L.seen.items())))
    L.s.close()
    if LOG:
        with open(LOG, 'w') as f:
            f.write('time_boot_ms,lat,lon,alt_mm,relative_alt_mm\n')
            for g in L.gpi:
                f.write(','.join(map(str, g)) + '\n')
    return 0 if ok else 1


def main_compare():
    gpi = [tuple(int(v) for v in r) for r in list(csv.reader(open(LOG)))[1:]]
    n, hmax, vmax, worst = compare(gpi)
    ok = stage('GLOBAL_POSITION_INT vs truth', n > 0 and hmax <= HBOUND and vmax <= VBOUND,
               '%d reports: horizontal error max %.3f m (at %s), altitude (AMSL) error max %.3f m '
               '(bounds %.2f m, %.2f m)'
               % (n, hmax, worst and '%.2f s' % (worst[0] / 1000), vmax, HBOUND, VBOUND))
    return 0 if ok else 1


sys.exit(main_compare() if MODE == 'compare' else main())
