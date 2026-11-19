#!/usr/bin/env python3
"""A gorge scenario on the ArduPilot harness stack in real time, for QGroundControl: ardupilot/fly_qgc.sh starts this.

    python3 -I ardupilot/qgc_bridge.py [single|abreast|staggered] [--udp-port 14550] [--pose-port 14601]
                                       [--seed 1] [--seconds S]

The scenario's node is served (`harness serve`: every clause of every instance monitored at every tick, verdicts in
build/serve/NODE.log, a ledger record when the session ends) and stepped one 400 Hz tick per 2.5 ms of wall clock
(the shared simulator's gorgesim.udp_bridge.Pacer: a late tick is never dropped, the next ones run without waiting
until the loop has caught up). Each vehicle has its own UDP socket on 127.0.0.1 (gorgesim.udp_bridge.UdpBridge) and
sends its MAVLink stream, as system 1 or 2, to the ground station at 127.0.0.1:--udp-port from the first tick, as
ArduPilot SITL reaches a listening QGroundControl; QGroundControl answers each vehicle at the address its datagrams
come from, so both share its one port. What a vehicle's socket receives goes into that vehicle's ground-station
input, at most 256 bytes per tick (the rest waits for the next ticks). Nothing binds the ground station's port.

Cameras: every 4th tick each vehicle's true pose (the served node's plant outputs, as ENU position and PyBullet
quaternion) goes to UDP 127.0.0.1:--pose-port + 2 (i - 1) (gorgesim.udp_bridge.PoseSender, never blocking), where
the camera process of sim/cameras.sh listens; it reads only outputs the session already has, so the flight is the
same with or without video. The mission is not onboard: QGroundControl uploads it from the plan files of sim/plans.

Stops at --seconds (default: no limit), Ctrl-C or SIGTERM: closes the sockets, ends the served session (its summary
and ledger record) and prints the real-time line.
"""
import argparse
import math
import os
import signal
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import scenario as S  # noqa: E402

sys.path.insert(0, S.SIM)
from gorgesim.udp_bridge import Pacer, PoseSender, UdpBridge  # noqa: E402


STOP = []


def on_signal(signum, frame):
    STOP.append(signum)       # the loop ends after the current tick, so the session's protocol stays whole


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scenario', nargs='?', default='single', choices=sorted(S.SCENARIOS))
    ap.add_argument('--udp-port', type=int, default=14550)
    ap.add_argument('--pose-port', type=int, default=0, help='0: no camera poses')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--seconds', type=float, default=0.0)
    a = ap.parse_args()
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    sc = S.SCENARIOS[a.scenario]
    nv = sc['vehicles']
    s = S.Served(sc['node'])
    s.init(S.params(s.schema, sc, True, a.seed))
    links = [UdpBridge(a.udp_port) for _ in range(nv)]
    poses = [PoseSender(a.pose_port + 2 * i) for i in range(nv)] if a.pose_port else []
    for i, br in enumerate(links):
        print('qgc_bridge: %s, vehicle %d (MAVLink system %d) on udp %s:%d sending to 127.0.0.1:%d' %
              (sc['node'], i + 1, i + 1, br.addr[0], br.addr[1], a.udp_port), flush=True)
    pending = [b''] * nv
    pre = [S.prefix(sc, i) for i in range(nv)]
    pacer = Pacer(0.0025)
    t_us, k = 0, 0
    try:
        while not STOP and (a.seconds <= 0 or t_us < a.seconds * 1e6):
            t_us += 2500
            inp = S.blank_input(s.schema, t_us)
            for i, br in enumerate(links):
                pending[i] += br.receive()
                chunk, pending[i] = pending[i][:256], pending[i][256:]
                S.put_bytes(inp, pre[i], chunk)
            out = s.step(inp)
            for i, br in enumerate(links):
                br.send(S.get_bytes(out, pre[i]))
            if poses and k % 4 == 0:
                for i, ps in enumerate(poses):
                    p = pre[i]
                    pos = (out[p + 'pos_e'], out[p + 'pos_n'], -out[p + 'pos_d'])
                    q = S.quat_enu_flu((out[p + 'q1'], out[p + 'q2'], out[p + 'q3'], out[p + 'q4']))
                    ps.send(t_us * 1e-6, pos, q)
            if k % 4000 == 0:
                print('qgc_bridge: t %.0f s  ' % (t_us * 1e-6) + '  '.join(
                    'v%d mode %d armed %d alt %.2f' % (i + 1, out[pre[i] + 'mode'], out[pre[i] + 'armed'],
                                                     -out[pre[i] + 'pos_d']) for i in range(nv)) +
                    '  late %d' % pacer.late_steps, flush=True)
            pacer.wait(k)
            k += 1
    finally:
        for br in links:
            br.close()
        for ps in poses:
            ps.close()
        s.quit()
        print('qgc_bridge: %s' % pacer.summary(k), flush=True)


if __name__ == '__main__':
    main()
