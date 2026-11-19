"""The three gorge scenarios on the ArduPilot harness stack: which served node flies them, its parameters, the
mission of each vehicle (the plan files of the repository's sim/plans), and the session (`harness serve`).

    single     one X500 through the gorge: node ap_full_ekf, plan sim/plans/gorge.plan
    abreast    two X500s side by side: node ap_formation (formation 1), formation-abreast-v1/-v2.plan
    staggered  two X500s staggered, vehicle 2 rear and nose-backward: ap_formation (formation 2),
               formation-staggered-v1/-v2.plan (vehicle 2: a CONDITION_YAW before each spline waypoint, and
               WP_YAW_BEHAVIOR 0 so that ArduCopter keeps that yaw on the spline legs)

Used by ardupilot/fly_gorge.py (headless, a scripted ground station per vehicle in the loop) and
ardupilot/qgc_bridge.py (real time, QGroundControl over UDP). Vehicle i's fields of the formation are its stack's
fields prefixed `v{i}_` (`inst` in ardupilot/harnesses/ap_formation); the clock (`dt`, `now_us`, `now_ms`) is shared.
"""
import json
import os
import sys
sys.dont_write_bytecode = True     # no __pycache__ in the tree

import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(HERE)
REPO = os.path.dirname(HARNESS)
SIM = os.path.join(REPO, 'sim')
PLANS = os.path.join(SIM, 'plans')
HB = os.path.join(HARNESS, '.lake', 'build', 'bin', 'harness')
sys.path.insert(0, os.path.join(HARNESS, 'py'))
import module_protocol as mp  # noqa: E402

SCENARIOS = {
    'single': dict(node='ap_full_ekf', vehicles=1, formation=0, plans=['gorge.plan'], yaw_behavior=[2]),
    'abreast': dict(node='ap_formation', vehicles=2, formation=1,
                    plans=['formation-abreast-v1.plan', 'formation-abreast-v2.plan'], yaw_behavior=[2, 2]),
    'staggered': dict(node='ap_formation', vehicles=2, formation=2,
                      plans=['formation-staggered-v1.plan', 'formation-staggered-v2.plan'], yaw_behavior=[2, 0]),
}
CLOCK = ('dt', 'now_us', 'now_ms')
GCS_WORDS = 64


def prefix(sc, i):
    """The field prefix of vehicle i (0-based) in the scenario's node."""
    return '' if sc['vehicles'] == 1 else 'v%d_' % (i + 1)


class Served:
    """`harness serve NODE`: the composite behind the module protocol, its monitors inside (verdicts in the log
    $HARNESS_SERVE_LOG names, default build/serve/NODE.log; a ledger record at the end of the session only with
    HARNESS_RECORD=1)."""

    def __init__(self, node):
        self.node = node
        # its own session: a Ctrl-C at the terminal reaches the driver, which ends the session cleanly
        self.p = subprocess.Popen([HB, 'serve', node], cwd=HARNESS, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  start_new_session=True)
        self.p.stdin.write(b'D')
        self.p.stdin.flush()
        if self.p.stdout.read(1) != b'K':
            raise SystemExit('harness serve %s did not answer describe' % node)
        n = struct.unpack('<I', self.p.stdout.read(4))[0]
        self.schema = json.loads(self.p.stdout.read(n))
        self.nout = mp.record_bytes(self.schema['output'])

    def req(self, b, nout=0):
        self.p.stdin.write(b)
        self.p.stdin.flush()
        k = self.p.stdout.read(1)
        if k != b'K':
            raise SystemExit('reply %r, exit %s' % (k, self.p.poll()))
        return self.p.stdout.read(nout) if nout else b''

    def init(self, params):
        self.req(b'I' + mp.pack(self.schema['params'], params))

    def step(self, inp):
        return mp.unpack(self.schema['output'], self.req(b'S' + mp.pack(self.schema['input'], inp), self.nout))

    def quit(self):
        """End the session: the served harness writes its summary and its ledger record, then exits."""
        try:
            self.req(b'Q')
        except (SystemExit, Exception):
            pass
        try:
            self.p.wait(timeout=60)
        except subprocess.TimeoutExpired:
            self.p.kill()


def stock_params():
    """Every `name = value` of the stages' stock regimes (`harness contract`), as dev/fly.py."""
    vals = {}
    for node, regs in (('rate_c', ['stock_flight']), ('mixer', ['stock_flight']),
                       ('position', ['stock_flight']), ('attitude', ['stock_flight']),
                       ('guidance', ['stock_leg']), ('estimator', ['plant_like']),
                       ('loiter', ['stock_flight'])):
        txt = subprocess.run([HB, 'contract', node], cwd=HARNESS, capture_output=True, text=True).stdout
        for line in txt.splitlines():
            m = re.match(r'regime (\w+):(.*)', line)
            if m and m.group(1) in regs:
                for k, v in re.findall(r'(\w+) = (true|false|-?[0-9][0-9.e+-]*)\b', m.group(2)):
                    vals[k] = {'true': True, 'false': False}.get(v, v)
    return vals


def params(schema, sc, noise, seed):
    """The parameter record of the scenario's node: the stock regimes for every stage of every vehicle, the
    supervisor's settings of dev/fly.py (no RC: no throttle failsafe, arming checks skipped), each vehicle's
    MAVLink system id (1, 2) and WP_YAW_BEHAVIOR, and the simulator's noise and formation."""
    stock = stock_params()
    per = dict(fltmode1=0, initial_mode=0, arming_skipchk=-1, fs_thr_enable=0, fs_gcs_enable=0, rc_options=32,
               auto_options=2, gps1_type=1)
    vals = {}
    for i in range(sc['vehicles']):
        pre = prefix(sc, i)
        for k, v in stock.items():
            vals[pre + k] = v
        for k, v in per.items():
            vals[pre + k] = v
        vals[pre + 'mav_sysid'] = i + 1
        vals[pre + 'wp_yaw_behavior'] = sc['yaw_behavior'][i]
    vals.update(noise_on=noise, noise_seed=seed if noise else 0, formation=sc['formation'])
    out = {}
    for f in schema['params']:
        n, t = f['name'], f['type']
        v = vals.get(n, False if t == 'bool' else 0)
        out[n] = bool(v) if t == 'bool' else (float(v) if t == 'f32' else int(float(v)))
    return out


def blank_input(schema, t_us):
    inp = {f['name']: (False if f['type'] == 'bool' else 0) for f in schema['input']}
    inp.update(dt=0.0025, now_us=t_us, now_ms=t_us // 1000)
    return inp


def put_bytes(inp, pre, data):
    """At most 4 * GCS_WORDS bytes from the ground station into vehicle `pre`'s input."""
    assert len(data) <= 4 * GCS_WORDS
    inp[pre + 'gcs_rx_len'] = len(data)
    padded = data + b'\0' * (4 * GCS_WORDS - len(data))
    for w in range(GCS_WORDS):
        inp[pre + 'gcs_rx_w%02d' % w] = struct.unpack('<I', padded[4 * w:4 * w + 4])[0]


def get_bytes(out, pre):
    raw = b''.join(struct.pack('<I', out[pre + 'gcs_tx_w%02d' % w]) for w in range(GCS_WORDS))
    return raw[:out[pre + 'gcs_tx_len']]


def plan_items(name):
    """The mission of a QGroundControl plan file as QGroundControl uploads it: item 0 the planned home, then the
    plan's items; each (command, frame, (p1..p4), lat deg, lon deg, alt m)."""
    j = json.load(open(os.path.join(PLANS, name)))
    m = j['mission']
    h = m['plannedHomePosition']
    items = [(16, 0, (0.0, 0.0, 0.0, 0.0), h[0], h[1], h[2])]
    for it in m['items']:
        p = [0.0 if x is None else float(x) for x in it['params']]
        items.append((it['command'], it['frame'], tuple(p[:4]), p[4], p[5], p[6]))
    return items


def ne_of(lat, lon):
    """North and east (m) of a latitude and longitude from the gorge origin (sim/world/origin.params, the home of
    sim/plans/gorge.plan), flat earth: what the plant's pos_n, pos_e are about."""
    import math
    o = plan_items('gorge.plan')[0]
    r = 6378137.0
    return (math.radians(lat - o[3]) * r, math.radians(lon - o[4]) * r * math.cos(math.radians(o[3])))


def quat_enu_flu(q):
    """PyBullet's (x, y, z, w) FLU-to-ENU quaternion of a body (FRD) to NED one (q1 scalar): the inverse of the
    simulator's quat_ned_frd (sim/gorgesim/simulator.py), for the camera poses."""
    import math
    h = math.sqrt(0.5)
    # NED = R_x(pi) R_z(pi/2) ENU as quaternions: Q_ENU_TO_NED = (0, h, h, 0); FRD = R_x(pi) FLU: (0, 1, 0, 0)
    def mul(a, b):
        aw, ax, ay, az = a
        bw, bx, by, bz = b
        return (aw * bw - ax * bx - ay * by - az * bz, aw * bx + ax * bw + ay * bz - az * by,
                aw * by - ax * bz + ay * bw + az * bx, aw * bz + ax * by - ay * bx + az * bw)
    conj_t = (0.0, -h, -h, 0.0)          # inverse of Q_ENU_TO_NED
    conj_d = (0.0, -1.0, 0.0, 0.0)       # inverse of Q_FRD_TO_FLU
    w, x, y, z = mul(mul(conj_t, q), conj_d)
    return (x, y, z, w)
