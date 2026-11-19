#!/usr/bin/env python3
"""Relay between px4_full's MAVLink byte ports and UDP, in real time (or as fast as it runs).

  python3 -I px4/harnesses/px4_full/dev/relay.py [--regime x500_full_noise] [--set NAME=VALUE ...]
          [--seconds S] [--fast] [--truth FILE.csv] [--every N] (--port P | --gcs HOST:PORT)

Starts `.lake/build/bin/harness serve px4_full` (the monitors run inside; their verdicts go to
$HARNESS_SERVE_LOG, default build/serve/NODE.log; a ledger record only with HARNESS_RECORD=1) and initializes it with the regime's parameters (py/regime_case.py:
PX4's defaults with the SITL and X500 values; `--set noise_seed=S` picks the simulator's noise).
A parameter the regime leaves free (a range only) gets PX4's default. Every input other than the
link is the regime's: the healthy constants of the topics nothing in
the stack makes, their timestamps advancing with the clock. The vehicle, its sensors, estimator,
controllers, commander, navigator and MAVLink are the real modules; nothing here moves it.

It steps one 400 Hz tick per 2.5 ms of wall clock, or as fast as it can (--fast, or whenever it
cannot keep up: the ticks it falls behind are counted and printed every second of simulated
time, with the tick rate achieved).

  --port P        the vehicle listens on UDP 127.0.0.1:P (default 14570, PX4's test port); replies
                  go to the last client that sent. 14550 and 14560 are refused.
  --gcs HOST:PORT the vehicle sends from the first tick (heartbeats included), from an ephemeral
                  local port, to HOST:PORT, and accepts what HOST:PORT sends back: how PX4 SITL
                  reaches a ground station that listens (QGroundControl listens on 14550).

Bytes from the ground station are queued and fed at most 512 per tick into mavlink_rx_* (the
port's capacity); the vehicle's mavlink_tx_* bytes go out as one datagram per tick. --truth
writes one CSV row every --every ticks (default 1): the clock, the simulator's position (NED from
its start) and velocity, EKF2's local position and reference, the reported state. The socket is
closed and the served harness stopped at --seconds of simulated time, Ctrl-C or SIGTERM.

  --pose-port N   every 4th tick (100 Hz) the simulator's true pose goes to UDP 127.0.0.1:N as one
                  datagram for the vehicle's camera (sim/world/camera_component.py, POSE_FMT: sequence,
                  simulated time, wall time, position in the world frame (ENU, m), PyBullet quaternion
                  x, y, z, w of the FLU body): what the camera draws. Sending never blocks and nothing
                  comes back, so the flight is the same with or without a camera.
  --node NAME     the served system (default px4_full); px4_formation: two vehicles, v1_ and v2_,
                  each given px4_full's regime under its prefix and MAV_SYS_ID 1 and 2 (--set
                  formation=1 abreast, 2 staggered; --set noise_seed=S), each with its own UDP socket
                  to the same --gcs address (in --port mode vehicle k listens on P + 2 (k - 1)), its own
                  camera pose port (--pose-port N: vehicle k on N + 2 (k - 1)) and its own truth file
                  (--truth F.csv: F-v1.csv, F-v2.csv, px4_full's column names).
  --exit-on-disarm S  stop by itself S seconds of simulated time after PX4 disarms following a
                  flight (every vehicle was armed and in the air, then disarmed)."""
import json
import os
import select
import signal
import socket
import struct
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(HERE))))
sys.path.insert(0, os.path.join(HARNESS, 'py'))
from regime_case import RegimeCase  # noqa: E402

WORDS = 128
NODE = 'px4_full'
TRUTH = ['t_us', 'pos_n', 'pos_e', 'pos_d', 'vel_n', 'vel_e', 'vel_d',
         'vehicle_local_position_x', 'vehicle_local_position_y', 'vehicle_local_position_z',
         'vehicle_local_position_xy_valid', 'vehicle_local_position_z_valid',
         'vehicle_local_position_xy_global', 'vehicle_local_position_z_global',
         'vehicle_local_position_ref_lat', 'vehicle_local_position_ref_lat_lo',
         'vehicle_local_position_ref_lon', 'vehicle_local_position_ref_lon_lo',
         'vehicle_local_position_ref_alt',
         'vehicle_global_position_lat', 'vehicle_global_position_lat_lo',
         'vehicle_global_position_lon', 'vehicle_global_position_lon_lo',
         'vehicle_global_position_alt',
         'trajectory_setpoint_position_0', 'trajectory_setpoint_position_1',
         'trajectory_setpoint_position_2', 'vehicle_status_nav_state', 'vehicle_status_arming_state',
         'vehicle_land_detected_landed', 'mission_result_seq_current', 'mission_result_finished',
         'home_position_alt', 'mavlink_tx_len', 'mavlink_rx_dropped',
         'vehicle_command_count', 'vehicle_status_updated', 'dataman_request_mirror_count',
         'dataman_request_mirror_lost', 'mission_updated', 'q1', 'q2', 'q3', 'q4',
         'actuator_armed_armed', 'wall_clear']
POSE_FMT = struct.Struct('<Idd3d4d')     # sim/harness/udp_bridge.POSE_FMT (camera_component.py)


def pyb_pose(n, e, d, q1, q2, q3, q4):
    """The simulator's world pose from the plant's NED position and FRD-to-NED quaternion (q1 the
    scalar): ENU position (e, n, -d), and the FLU-to-ENU quaternion conj(Q_ENU_TO_NED) * q *
    conj(Q_FRD_TO_FLU) as PyBullet's (x, y, z, w) (the inverse of simulator.quat_ned_frd)."""
    def qmul(a, b):
        aw, ax, ay, az = a
        bw, bx, by, bz = b
        return (aw * bw - ax * bx - ay * by - az * bz, aw * bx + ax * bw + ay * bz - az * by,
                aw * by - ax * bz + ay * bw + az * bx, aw * bz + ax * by - ay * bx + az * bw)
    h = 0.7071067811865476
    w, x, y, z = qmul(qmul((0.0, -h, -h, 0.0), (q1, q2, q3, q4)), (0.0, -1.0, 0.0, 0.0))
    return (e, n, -d), (x, y, z, w)


def arg(name, default):
    return type(default)(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


class Stop(Exception):
    pass


def on_signal(signum, frame):
    raise Stop()


def layout(fields):
    """Byte offset and struct format of each field of a record (cpp/module_protocol.h)."""
    off, o = {}, 0
    for f in fields:
        t = f['type']
        off[f['name']] = (o, {'bool': '<?', 'f32': '<f', 'u32': '<I', 'i32': '<i'}[t], t)
        o += 1 if t == 'bool' else 4
    return off, o


def word_bytes(t, w):
    if t == 'bool':
        return b'\x01' if w == 'true' else b'\x00'
    if t == 'f32':
        return struct.pack('<I', int(w, 16))
    return struct.pack('<I', int(w) & 0xffffffff) if t == 'u32' else struct.pack('<i', int(w))


class Served:
    def __init__(self):
        self.p = subprocess.Popen([os.path.join(HARNESS, '.lake/build/bin/harness'), 'serve', NODE],
                                  cwd=HARNESS, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.p.stdin.write(b'D')
        self.p.stdin.flush()
        assert self.p.stdout.read(1) == b'K'
        n = struct.unpack('<I', self.p.stdout.read(4))[0]
        self.schema = json.loads(self.p.stdout.read(n))
        self.inoff, self.insize = layout(self.schema['input'])
        self.outoff, self.outsize = layout(self.schema['output'])

    def req(self, b, nout=0):
        self.p.stdin.write(b)
        self.p.stdin.flush()
        k = self.p.stdout.read(1)
        if k != b'K':
            raise SystemExit('relay: reply %r, exit %s' % (k, self.p.poll()))
        return self.p.stdout.read(nout) if nout else b''

    def record(self, fields, words):
        return b''.join(word_bytes(f['type'], words[f['name']]) for f in fields)

    def out(self, raw, name):
        o, fmt, t = self.outoff[name]
        return struct.unpack_from(fmt, raw, o)[0]


def word_of(t, v):
    """A protocol word (the text form RegimeCase uses) of value v for a field of type t."""
    if t == 'bool':
        return 'true' if v in (True, 'true', '1', 1) else 'false'
    if t == 'f32':
        return '0x%08x' % struct.unpack('<I', struct.pack('<f', float(v)))[0]
    return str(int(float(v)))


def main():
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    global NODE
    NODE = arg('--node', NODE)
    regime = arg('--regime', 'x500_full_noise')
    sets = [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == '--set']
    seconds = arg('--seconds', 0.0)
    fast = '--fast' in sys.argv
    every = arg('--every', 1)
    gcs_addr = None
    if '--gcs' in sys.argv:
        host, p = arg('--gcs', '127.0.0.1:14550').rsplit(':', 1)
        gcs_addr = (host, int(p))
        bind = ('127.0.0.1', 0)
    else:
        port = arg('--port', 14570)
        if port in (14550, 14560):
            raise SystemExit('relay: not binding 14550 (the ground station\'s; use --gcs '
                             '127.0.0.1:14550 to send to a listening one) or 14560')
        bind = ('127.0.0.1', port)
    s = Served()
    ptypes = {f['name']: f['type'] for f in s.schema['params']}
    itypes = {f['name']: f['type'] for f in s.schema['input']}
    # the vehicles: px4_full has one, unprefixed; a formation (px4_formation) has v1_, v2_, ...
    pre = sorted({n.split('_', 1)[0] + '_' for n in itypes if n.endswith('mavlink_rx_len') and n != 'mavlink_rx_len'})
    pre = pre or ['']
    if pre == ['']:
        rc = RegimeCase(NODE, regime, sets, px4_defaults=True)
        params, first, hints = rc.params, rc.first, rc.hints
    else:
        # a formation: every vehicle gets px4_full's regime (PX4's defaults with the SITL and X500
        # values), its fields prefixed; vehicle N is MAVLink system N; the plant's parameters are shared
        rc = RegimeCase('px4_full', regime, [], px4_defaults=True)
        params, first, hints = {}, {}, {}
        for n in ptypes:
            q = next((x for x in pre if n.startswith(x)), None)
            base = n[len(q):] if q else n
            if base in rc.params:
                params[n] = rc.params[base]
            elif n not in ('formation',):
                raise SystemExit('relay: no value for parameter %s' % n)
        for k, q in enumerate(pre):
            params[q + 'MAV_SYS_ID'] = str(k + 1)
        params.setdefault('formation', '1')
        for n in itypes:
            q = next((x for x in pre if n.startswith(x)), '')
            base = n[len(q):]
            first[n] = rc.first.get(base, word_of(itypes[n], 0))
            if base in rc.hints:
                hints[n] = rc.hints[base]
        for st in sets:
            n, v = st.split('=', 1)
            if n.startswith('in:'):
                first[n[3:]] = word_of(itypes[n[3:]], v)
            else:
                params[n] = word_of(ptypes[n], v)
    s.req(b'I' + s.record(s.schema['params'], params))
    buf = bytearray(s.record(s.schema['input'], first))
    hinted = [(s.inoff[n][0], s.inoff[n][2], a, b) for n, (a, b) in hints.items() if n in s.inoff]
    V = []
    multi = len(pre) > 1
    truth_path = arg('--truth', '') if '--truth' in sys.argv else None
    pose_base = arg('--pose-port', 0) if '--pose-port' in sys.argv else None
    for k, q in enumerate(pre):
        v = dict(pre=q, sysid=k + 1)
        v['rx_off'] = [s.inoff[q + 'mavlink_rx_%d' % w][0] for w in range(WORDS)]
        v['rx_len'] = s.inoff[q + 'mavlink_rx_len'][0]
        v['tx_off'] = [s.outoff[q + 'mavlink_tx_%d' % w][0] for w in range(WORDS)]
        v['tx_len'] = q + 'mavlink_tx_len'
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind(bind if k == 0 or gcs_addr else ('127.0.0.1', bind[1] + 2 * k))
        sock.setblocking(False)
        v['sock'], v['client'], v['pending'], v['rx'], v['tx'] = sock, gcs_addr, b'', 0, 0
        v['pose'] = None
        if pose_base is not None:
            ps = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            ps.setblocking(False)
            v['pose'], v['pose_addr'], v['pose_seq'] = ps, ('127.0.0.1', pose_base + 2 * k), 0
        # truth columns: px4_full's names (the vehicle's own fields, the plant's under its prefix)
        v['cols'] = [(c, c if c == 't_us' else q + c) for c in TRUTH if (c if c == 't_us' else q + c) in s.outoff]
        v['truth'] = None
        if truth_path:
            tp = truth_path if not multi else truth_path.replace('.csv', '-v%d.csv' % (k + 1))
            v['truth'] = open(tp, 'w')
            v['truth'].write(','.join(c for c, _ in v['cols']) + '\n')
        v['flew'] = False
        V.append(v)
    exit_after = arg('--exit-on-disarm', -1.0)
    t_disarm = None
    sockets = {v['sock']: v for v in V}
    for v in V:
        where = 'sending to %s:%d' % gcs_addr if gcs_addr else 'listening'
        print('relay: %s, regime %s %s; vehicle %d (MAVLink system %d) on udp %s:%d %s'
              % (NODE, regime, ' '.join(sets), v['sysid'], v['sysid'], v['sock'].getsockname()[0],
                 v['sock'].getsockname()[1], where), flush=True)
    k, late = 0, 0
    start = time.monotonic()
    t_step = 0.0
    last_print = (start, 0)
    o = lambda raw, v, n: s.out(raw, v['pre'] + n)
    try:
        while seconds <= 0 or k * 0.0025 < seconds:
            while True:
                r, _, _ = select.select(list(sockets), [], [], 0)
                if not r:
                    break
                for sk in r:
                    v = sockets[sk]
                    try:
                        data, addr = sk.recvfrom(65536)
                    except OSError:
                        continue
                    if gcs_addr is not None and addr != gcs_addr:
                        continue
                    v['client'] = addr
                    v['pending'] += data
                    v['rx'] += len(data)
            if k > 0:
                for off, t, a, b in hinted:
                    struct.pack_into('<I' if t == 'u32' else '<i', buf, off, int(a + b * k))
            for v in V:
                chunk, v['pending'] = v['pending'][:4 * WORDS], v['pending'][4 * WORDS:]
                struct.pack_into('<I', buf, v['rx_len'], len(chunk))
                padded = chunk + bytes(4 * WORDS - len(chunk))
                for w in range(WORDS):
                    buf[v['rx_off'][w]:v['rx_off'][w] + 4] = padded[4 * w:4 * w + 4]
            t0 = time.monotonic()
            raw = s.req(b'S' + bytes(buf), s.outsize)
            t_step += time.monotonic() - t0
            for v in V:
                n = s.out(raw, v['tx_len'])
                if n and v['client'] is not None:
                    data = b''.join(raw[x:x + 4] for x in v['tx_off'])[:n]
                    try:
                        v['sock'].sendto(data, v['client'])
                        v['tx'] += n
                    except OSError:
                        pass
                if v['pose'] is not None and k % 4 == 0:
                    pos, quat = pyb_pose(*(o(raw, v, c) for c in ('pos_n', 'pos_e', 'pos_d', 'q1', 'q2', 'q3', 'q4')))
                    v['pose_seq'] += 1
                    try:
                        v['pose'].sendto(POSE_FMT.pack(v['pose_seq'], (k + 1) * 0.0025, time.time(), *pos, *quat),
                                         v['pose_addr'])
                    except OSError:
                        pass
                if v['truth'] and k % every == 0:
                    v['truth'].write(','.join(repr(s.out(raw, f)) for _, f in v['cols']) + '\n')
                if o(raw, v, 'actuator_armed_armed') and not o(raw, v, 'vehicle_land_detected_landed'):
                    v['flew'] = True
            if exit_after >= 0:
                done = all(v['flew'] and not o(raw, v, 'actuator_armed_armed') for v in V)
                if done and t_disarm is None:
                    t_disarm = k
                if t_disarm is not None and (k - t_disarm) * 0.0025 >= exit_after:
                    print('relay: every vehicle disarmed after its flight; stopping', flush=True)
                    break
            k += 1
            if k % 400 == 0:
                now = time.monotonic()
                rate = (k - last_print[1]) / max(now - last_print[0], 1e-9)
                last_print = (now, k)
                print('relay: t %.1f s  %.0f ticks/s (step %.1f ms)  behind %d ticks  %s'
                      % (k * 0.0025, rate, 1000 * t_step / k, late, ' | '.join(
                          'V%d armed %d nav_state %d landed %d N %.2f E %.2f D %.2f rx %d B tx %d B'
                          % (v['sysid'], o(raw, v, 'actuator_armed_armed'), o(raw, v, 'vehicle_status_nav_state'),
                             o(raw, v, 'vehicle_land_detected_landed'), o(raw, v, 'pos_n'), o(raw, v, 'pos_e'),
                             o(raw, v, 'pos_d'), v['rx'], v['tx']) for v in V)), flush=True)
            if not fast:
                wait = start + k * 0.0025 - time.monotonic()
                if wait > 0:
                    time.sleep(wait)
                else:
                    late = max(late, int(-wait / 0.0025))
            else:
                late = max(late, int((time.monotonic() - start) / 0.0025) - k)
    except Stop:
        pass
    finally:
        for v in V:
            v['sock'].close()
            if v['pose'] is not None:
                v['pose'].close()
            if v['truth']:
                v['truth'].close()
        try:
            s.req(b'Q')
        except (SystemExit, Exception):
            pass
        s.p.wait(timeout=60)
        el = time.monotonic() - start
        print('relay: socket closed after %d ticks (%.1f s simulated) in %.1f s: %.1f ticks/s, '
              'step round trip %.2f ms, %d ticks behind real time at most'
              % (k, k * 0.0025, el, k / max(el, 1e-9), 1000 * t_step / max(k, 1), late), flush=True)


try:
    main()
except Stop:
    # stopped while starting (before the stepping loop): the served harness, if started, ends
    # when its stdin closes with this process
    print('relay: stopped while starting', flush=True)
