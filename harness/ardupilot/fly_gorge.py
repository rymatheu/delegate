#!/usr/bin/env python3
"""A gorge scenario on the ArduPilot harness stack with no ground station: ardupilot/fly_gorge.sh [single|abreast|staggered].

The scenario's node is served (`harness serve`, every clause of every instance monitored at every tick) and stepped
as fast as it goes, in lock-step with one scripted MAVLink ground station per vehicle (the shared simulator's
gorgesim.ground_station.GCS, system 255): wait for the heartbeat and for EKF3 using GPS, upload the vehicle's plan
file of sim/plans through the mission protocol and download it back, GUIDED, arm, take off to the first item's
altitude, AUTO through the spline waypoints, land, disarm. With two vehicles every phase waits for both, so they
take off and switch to AUTO at the same tick. It ends by itself and prints a PASS/FAIL summary. Nothing is kept by
default (the run writes into a temporary directory, --tmp, which fly_gorge.sh removes). With --record [DIR] (default
ardupilot/out/SCENARIO): the record gorge-SCENARIO.csv (every 4th tick: time, per vehicle true position, yaw, mode,
armed, wall clearance; the separation), the summary gorge-SCENARIO.json, the ground stations' log gorge-SCENARIO.log,
the monitors' verdicts serve.log, and the served session's ledger record.

PASS: every vehicle reached every mission item and disarmed on the ground; the session's monitors saw no guarantee
violation and no discharge failure; with two vehicles, the separation stayed at least SEP_MIN and every vehicle's
wall clearance at least CLEAR_MIN (also clauses of the formation's contract, monitored by the harness).
"""
import argparse
import json
import sys
sys.dont_write_bytecode = True     # no __pycache__ in the tree

import math
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import scenario as S  # noqa: E402

sys.path.insert(0, os.path.join(S.HARNESS, 'deps', 'mavlink'))
sys.path.insert(0, os.path.join(S.HARNESS, 'build', 'gen', 'supervisor', 'py'))
sys.path.insert(0, S.SIM)
os.environ.setdefault('MAVLINK20', '1')
import apm as mav  # noqa: E402
from gorgesim.ground_station import GCS, GCSError  # noqa: E402

SEP_MIN = 1.5        # m, the formation contract's min_separation
CLEAR_MIN = 0.5      # m, its wall_clearance


def script(g, m, items, rec, sync, i):
    """One vehicle's flight from the ground (gorgesim.ground_station.script_gorge without its parameter checks, which
    are another controller's); `sync(name)` waits until every vehicle has reached the same point."""
    yield from g.wait_until(lambda: "HEARTBEAT" in g.latest, 60, "first heartbeat")
    g.event("heartbeat")
    g.request_streams(4)
    yield from g.wait_until(lambda: any("is using GPS" in x[2] for x in g.texts), 150, "EKF3 using GPS")
    g.event("EKF3 using GPS")
    yield from g.upload_mission(items)
    back = yield from g.download_mission()
    if len(back) != len(items) or any(b.command != it[0] or (s > 0 and it[0] != m.MAV_CMD_CONDITION_YAW and
                                                             (b.x != int(round(it[3] * 1e7)) or
                                                              b.y != int(round(it[4] * 1e7))))
                                      for s, (b, it) in enumerate(zip(back, items))):
        raise GCSError("downloaded mission differs from the uploaded one")
    yield from sync('uploaded')
    yield from g.set_mode("GUIDED")
    t0 = g.t
    while not g.armed:
        r = yield from g.command(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        if r == m.MAV_RESULT_ACCEPTED:
            yield from g.wait_until(lambda: g.armed, 3, "armed heartbeat")
            break
        if g.t - t0 > 60:
            raise GCSError("arming refused for 60 s")
        yield from g.wait_s(2.0)
    g.event("armed")
    rec["t_arm"] = g.t
    yield from sync('armed')
    alt = items[1][5]
    r = yield from g.command(m.MAV_CMD_NAV_TAKEOFF, p7=alt)
    if r != m.MAV_RESULT_ACCEPTED:
        raise GCSError(f"takeoff refused ({r})")
    yield from g.wait_until(lambda: "GLOBAL_POSITION_INT" in g.latest and
                            g.latest["GLOBAL_POSITION_INT"].relative_alt > (alt - 0.3) * 1000, 30, f"{alt - 0.3:.2f} m")
    g.event(f"reached {alt - 0.3:.2f} m in GUIDED")
    yield from sync('climbed')
    yield from g.set_mode("AUTO")
    rec["t_auto"] = g.t
    t0 = g.t
    while g.armed:
        for msg in g.msgs:
            typ = msg.get_type()
            if typ == "MISSION_ITEM_REACHED" and (not rec["reached"] or rec["reached"][-1][1] != msg.seq):
                rec["reached"].append((g.t, msg.seq))
                g.event(f"MISSION_ITEM_REACHED {msg.seq}")
            elif typ == "MISSION_CURRENT" and (not rec["current"] or rec["current"][-1][1] != msg.seq):
                rec["current"].append((g.t, msg.seq))
                g.event(f"MISSION_CURRENT {msg.seq}")
        if g.t - t0 > 400:
            raise GCSError("timeout (400 s) waiting for the disarm after the mission")
        yield
    rec["t_disarm"] = g.t
    g.event("disarmed")
    yield from g.wait_s(2.0)


def serve_summary(node):
    """The served session's verdicts from its log ($HARNESS_SERVE_LOG): guarantee violations and discharge failures."""
    log = open(os.environ['HARNESS_SERVE_LOG']).read()
    tail = log[log.rfind('summary:'):]
    viol, disch = [], []
    for line in tail.splitlines():
        m = re.match(r'\s+(\S+): assumption failed in (\d+) cases; guarantee violations: (.*)$', line)
        if m:
            if m.group(2) != '0':
                disch.append(m.group(1))
            if m.group(3).strip() != 'none':
                viol.append('%s: %s' % (m.group(1), m.group(3).strip()))
    rec = re.search(r'ledger: session recorded, (\S+)', tail)
    return viol, disch, rec.group(1) if rec else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scenario', nargs='?', default='single', choices=sorted(S.SCENARIOS))
    ap.add_argument('--seed', type=int, default=1, help='sensor noise seed (vehicle 2: seed + 100)')
    ap.add_argument('--no-noise', action='store_true')
    ap.add_argument('--minutes', type=float, default=8.0, help='simulated time limit')
    ap.add_argument('--record', nargs='?', const='', default=None, metavar='DIR',
                    help='keep the record, the summary and the session (default DIR: ardupilot/out/SCENARIO)')
    ap.add_argument('--out', default=None, help='the same as --record DIR')
    ap.add_argument('--tmp', default=None, help='where a run that records nothing writes while it runs')
    a = ap.parse_args()
    if a.out is not None:
        a.record = a.out
    recording = a.record is not None
    if recording:
        a.out = a.record or os.path.join(HERE, 'out', a.scenario)
        os.environ['HARNESS_RECORD'] = '1'
        os.environ['HARNESS_SERVE_LOG'] = os.path.join(a.out, 'serve.log')
    else:
        import tempfile
        a.out = a.tmp or tempfile.mkdtemp(prefix='fly_gorge.')
        os.environ.pop('HARNESS_RECORD', None)
        os.environ['HARNESS_SERVE_LOG'] = os.path.join(a.out, 'serve.log')
    sc = S.SCENARIOS[a.scenario]
    nv = sc['vehicles']
    os.makedirs(a.out, exist_ok=True)
    logf = open(os.path.join(a.out, 'gorge-%s.log' % a.scenario), 'w')

    def log(i):
        return lambda s: logf.write('v%d %s\n' % (i + 1, s))

    s = S.Served(sc['node'])
    prm = S.params(s.schema, sc, not a.no_noise, a.seed)
    s.init(prm)
    gcs, recs, pending, scripts = [], [], [], []
    at = {}

    def sync(name):
        at[name] = at.get(name, 0) + 1
        while at[name] < nv:
            yield

    for i in range(nv):
        g = GCS(mav, log(i))
        rec = dict(reached=[], current=[], t_arm=None, t_auto=None, t_disarm=None)
        items = S.plan_items(sc['plans'][i])
        g.script = script(g, mav, items, rec, sync, i)
        gcs.append(g)
        recs.append(rec)
        pending.append(b'')
    csv = open(os.path.join(a.out, 'gorge-%s.csv' % a.scenario), 'w')
    cols = ['t_s']
    for i in range(nv):
        cols += ['v%d_%s' % (i + 1, c) for c in ('pos_n', 'pos_e', 'pos_d', 'yaw_deg', 'mode', 'armed',
                                                 'wall_clear')]
    if nv == 2:
        cols += ['separation']
    csv.write(','.join(cols) + '\n')
    sep_min, sep_at = math.inf, None
    clear_min = [math.inf] * nv
    clear_at = [None] * nv
    t_us, k = 0, 0
    end = [(math.nan,) * 3] * nv
    w0 = time.perf_counter()
    nmax = int(a.minutes * 60 * 400)
    try:
        while k < nmax and not all(g.done for g in gcs):
            t_us += 2500
            k += 1
            inp = S.blank_input(s.schema, t_us)
            for i in range(nv):
                chunk, pending[i] = pending[i][:256], pending[i][256:]
                S.put_bytes(inp, S.prefix(sc, i), chunk)
            out = s.step(inp)
            for i, g in enumerate(gcs):
                pending[i] += g.step(t_us * 1e-6, S.get_bytes(out, S.prefix(sc, i)))
            pos = []
            for i in range(nv):
                pre = S.prefix(sc, i)
                pos.append((out[pre + 'pos_n'], out[pre + 'pos_e'], out[pre + 'pos_d']))
                end[i] = pos[i]
                airborne = out[pre + 'armed'] and not out[pre + 'land_complete']
                if airborne and out[pre + 'wall_clear'] < clear_min[i]:
                    clear_min[i], clear_at[i] = out[pre + 'wall_clear'], (t_us * 1e-6,) + pos[i]
            if nv == 2:
                sep = math.dist(pos[0], pos[1])
                if sep < sep_min:
                    sep_min, sep_at = sep, t_us * 1e-6
            if k % 4 == 0:
                row = [round(t_us * 1e-6, 4)]
                for i in range(nv):
                    pre = S.prefix(sc, i)
                    q1, q2, q3, q4 = (out[pre + c] for c in ('q1', 'q2', 'q3', 'q4'))
                    yaw = math.degrees(math.atan2(2 * (q1 * q4 + q2 * q3), 1 - 2 * (q3 * q3 + q4 * q4)))
                    row += [round(x, 4) for x in pos[i]] + [round(yaw, 2), out[pre + 'mode'],
                                                            int(out[pre + 'armed']), round(out[pre + 'wall_clear'], 3)]
                if nv == 2:
                    row.append(round(sep, 4))
                csv.write(','.join(str(x) for x in row) + '\n')
    finally:
        wall = time.perf_counter() - w0
        s.quit()
        csv.close()
        logf.close()
    viol, disch, ledger = serve_summary(sc['node'])
    sim_s = k * 0.0025
    res = dict(scenario=a.scenario, node=sc['node'], seed=a.seed, noise=not a.no_noise, steps=k, simulated_s=sim_s,
               wall_s=round(wall, 2), real_time_factor=round(sim_s / wall, 3), guarantee_violations=viol,
               discharge_failures=disch, served_record=ledger, vehicles=[])
    ok = not viol and not disch
    for i, (g, rec) in enumerate(zip(gcs, recs)):
        items = S.plan_items(sc['plans'][i])
        last = len(items) - 1
        reached = [sq for _, sq in rec['reached']]
        v = dict(system=i + 1, plan=sc['plans'][i], error=g.error, armed_s=rec['t_arm'], auto_s=rec['t_auto'],
                 disarmed_s=rec['t_disarm'], items_reached=reached, last_item=last,
                 wall_clearance_min_in_air_m=None if clear_at[i] is None else round(clear_min[i], 3),
                 wall_clearance_min_at=clear_at[i] and [round(x, 2) for x in clear_at[i]])
        # the land item gets no MISSION_ITEM_REACHED: it is done when the vehicle lands and disarms
        cur = [sq for _, sq in rec['current']]
        v['ok'] = (g.error is None and rec['t_disarm'] is not None and last in cur and
                   all(sq in reached for sq in range(1, last) if items[sq][0] != mav.MAV_CMD_CONDITION_YAW))
        ln, le = S.ne_of(items[last][3], items[last][4])
        v['landing_error_m'] = round(math.hypot(end[i][0] - ln, end[i][1] - le), 3)
        ok = ok and v['ok']
        if nv == 2:
            ok = ok and clear_min[i] >= CLEAR_MIN
        res['vehicles'].append(v)
    if nv == 2:
        res['separation_min_m'] = round(sep_min, 3)
        res['separation_min_at_s'] = sep_at
        ok = ok and sep_min >= SEP_MIN
    res['result'] = 'PASS' if ok else 'FAIL'
    json.dump(res, open(os.path.join(a.out, 'gorge-%s.json' % a.scenario), 'w'), indent=1)
    print('%s: %s, %d vehicle(s), %.1f s simulated in %.1f s wall (real-time factor %.2f)' %
          (a.scenario, sc['node'], nv, sim_s, wall, sim_s / wall))
    for v in res['vehicles']:
        print('  vehicle %d (%s): %s; armed %s s, AUTO %s s, disarmed %s s; items reached %s of %d (then LAND); '
              'min wall clearance in the air %s m' % (v['system'], v['plan'], 'ok' if v['ok'] else
              'NOT OK (%s)' % (v['error'] or 'mission not completed'), v['armed_s'], v['auto_s'], v['disarmed_s'],
              len(set(v['items_reached'])), v['last_item'] - 1, v['wall_clearance_min_in_air_m']) +
              '; landed %.2f m from the plan\'s land point' % v['landing_error_m'])
    if nv == 2:
        print('  min separation %.2f m at %.1f s' % (sep_min, sep_at or 0))
    print('  monitors: %d guarantee violations, %d discharge failures%s' %
          (len(viol), len(disch), (': ' + '; '.join(viol + disch)) if viol or disch else ''))
    if recording:
        print('  recorded: %s (gorge-%s.csv, .json, .log, serve.log) and the session\'s ledger record %s' %
              (a.out, a.scenario, ledger))
    else:
        print('  nothing recorded (--record keeps the record and the session)')
    print('RESULT %s' % res['result'])
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
