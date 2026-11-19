#!/usr/bin/env python3
"""Relay between the full stack's ground-station byte ports and UDP, in real time.

  python3 -I ardupilot/modules/supervisor/dev/udp_bridge.py [--node ap_full|ap_full_ekf] [--noise]
          [--seed N] [--seconds S] (--port P | --gcs HOST:PORT)

Starts `.lake/build/bin/harness serve NODE` (monitors inside, verdicts in build/serve/NODE.log)
and steps it one 400 Hz tick per 2.5 ms of wall clock.

  --port P        the vehicle listens on UDP 127.0.0.1:P; replies go to the last client that
                  sent (a ground station that connects out to a listening vehicle)
  --gcs HOST:PORT the vehicle sends its stream to HOST:PORT from the first tick (heartbeats
                  included), from an ephemeral local port, and accepts what HOST:PORT sends back:
                  how ArduPilot SITL reaches a ground station that listens (QGroundControl's
                  default UDP link)

Bytes from the ground station are queued and fed at most 256 per tick into gcs_rx_*; the
vehicle's gcs_tx_* bytes are sent as they come. Parameters as dev/fly.py (the stages' stock
regimes; no RC). The bridge never binds port 14550. It stops at --seconds (default: no limit),
at Ctrl-C or SIGTERM, closes its socket and stops the served harness.
"""
import os
import select
import signal
import socket
import struct
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, 'fly.py')).read().replace('\nmain()\n', '\n')
fly = {'__file__': os.path.join(HERE, 'fly.py'), '__name__': 'flylib'}
exec(compile(src, 'fly.py', 'exec'), fly)


def arg(name, default):
    return type(default)(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


class Stop(Exception):
    pass


def on_signal(signum, frame):
    raise Stop()


def main():
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    node = arg('--node', 'ap_full')
    noise = '--noise' in sys.argv
    seed = arg('--seed', 1)
    seconds = arg('--seconds', 0.0)
    gcs_addr = None
    if '--gcs' in sys.argv:
        host, p = arg('--gcs', '127.0.0.1:14550').rsplit(':', 1)
        gcs_addr = (host, int(p))
        bind = ('127.0.0.1', 0)
    else:
        port = arg('--port', 14560)
        if port == 14550:
            raise SystemExit('udp_bridge: binding port 14550 is not done here (it is the ground '
                             'station\'s); use --gcs 127.0.0.1:14550 to send to a listening one')
        bind = ('127.0.0.1', port)
    s = fly['Served'](node)
    stock = fly['stock_params']()
    params = {}
    for f in s.schema['params']:
        n, t = f['name'], f['type']
        v = stock.get(n, False if t == 'bool' else 0)
        params[n] = v if t == 'bool' else (float(v) if t == 'f32' else int(float(v)))
    o = fly['ORIGIN']
    params.update(mav_sysid=1, fltmode1=0, initial_mode=0, arming_skipchk=-1, fs_thr_enable=0,
                  fs_gcs_enable=0, rc_options=32, auto_options=2, gps1_type=1, noise_on=noise,
                  noise_seed=seed if noise else 0, origin_lat_e7=o[0], origin_lon_e7=o[1],
                  origin_alt_cm=o[2])
    params = {k: v for k, v in params.items() if k in {f['name'] for f in s.schema['params']}}
    s.init(params)
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(bind)
    sock.setblocking(False)
    client = gcs_addr
    if gcs_addr:
        print('udp_bridge: %s; vehicle on udp %s:%d sending to %s:%d' %
              ((node,) + sock.getsockname() + gcs_addr), flush=True)
    else:
        print('udp_bridge: %s; vehicle listening on udp %s:%d' % ((node,) + bind), flush=True)
    pending = b''
    t_us, k, late = 0, 0, 0
    stats = {'rx': 0, 'tx': 0}
    start = time.monotonic()
    try:
        while seconds <= 0 or t_us < seconds * 1e6:
            while True:
                r, _, _ = select.select([sock], [], [], 0)
                if not r:
                    break
                try:
                    data, addr = sock.recvfrom(65536)
                except OSError:   # e.g. ICMP port unreachable while nobody listens yet
                    break
                if gcs_addr is not None and addr != gcs_addr:
                    continue
                client = addr
                pending += data
                stats['rx'] += len(data)
            t_us += 2500
            k += 1
            inp = {f['name']: (False if f['type'] == 'bool' else 0) for f in s.schema['input']}
            inp.update(dt=0.0025, now_us=t_us, now_ms=t_us // 1000)
            chunk, pending = pending[:256], pending[256:]
            inp['gcs_rx_len'] = len(chunk)
            padded = chunk + b'\0' * (256 - len(chunk))
            for w in range(64):
                inp['gcs_rx_w%02d' % w] = struct.unpack('<I', padded[4 * w:4 * w + 4])[0]
            out = s.step(inp)
            n = out['gcs_tx_len']
            if n and client is not None:
                raw = b''.join(struct.pack('<I', out['gcs_tx_w%02d' % w]) for w in range(64))
                try:
                    sock.sendto(raw[:n], client)
                    stats['tx'] += n
                except OSError:
                    pass   # nobody listening yet
            if k % 4000 == 0:
                print('udp_bridge: t %.0f s  mode %d armed %d alt %.2f  rx %d B tx %d B  late %d'
                      % (t_us * 1e-6, out['mode'], out['armed'], -out['pos_d'], stats['rx'],
                         stats['tx'], late), flush=True)
            wait = start + t_us * 1e-6 - time.monotonic()
            if wait > 0:
                time.sleep(wait)
            else:
                late += 1
    except Stop:
        pass
    finally:
        sock.close()
        try:
            s.req(b'Q')
        except (SystemExit, Exception):
            pass
        print('udp_bridge: socket closed after %d ticks (%d behind real time)' % (k, late),
              flush=True)


main()
