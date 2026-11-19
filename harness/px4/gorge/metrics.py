#!/usr/bin/env python3
"""Wall clearance and separation of a PX4 gorge flight, from the relay's truth CSV (the simulator's
pose of each vehicle), measured in the simulator's own world.

  SIM_PYTHON px4/gorge/metrics.py --sim SIMDIR TRUTH.csv [TRUTH2.csv] [--every 4] [--json OUT.json]

SIMDIR is the shared simulator's folder (sim/ at the repository root: gorgesim, world); its plant
(gorgesim.plant.Plant, FormationPlant) holds the gorge and measures. A truth file has the
columns t_us, pos_n, pos_e, pos_d (NED from the world origin), q1..q4 (FRD to NED, scalar first) and
vehicle_land_detected_landed; two files are the two vehicles of a formation, row by row at the same
times. For every --every-th row (100 Hz at --every 4 of a 400 Hz log) each vehicle's X500 collision
body is put at its pose in a PyBullet client holding the gorge, and:

  clearance   the closest distance from the vehicle's collision body to every body of the gorge
              (getClosestPoints, up to 4 m), the simulator's own measure (sim/harness/record.py);
  separation  the distance between the two vehicles' centers, and between their collision bodies.

"In the air" is, per vehicle, from the end of its takeoff item to the start of its land item (the
mission's current item past the first and before the last, armed), as the simulator's own flight
record counts it (sim/gorgesim/record.py): clearance and heading are each vehicle's in its own
window; the separation is taken while either vehicle is in the air.
Prints the minima in the air (with where they happen) and writes them as JSON."""
import argparse
import csv
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CLEAR_MAX = 4.0


def pyb_pose(n, e, d, q1, q2, q3, q4):
    def qmul(a, b):
        aw, ax, ay, az = a
        bw, bx, by, bz = b
        return (aw * bw - ax * bx - ay * by - az * bz, aw * bx + ax * bw + ay * bz - az * by,
                aw * by - ax * bz + ay * bw + az * bx, aw * bz + ax * by - ay * bx + az * bw)
    h = 0.7071067811865476
    w, x, y, z = qmul(qmul((0.0, -h, -h, 0.0), (q1, q2, q3, q4)), (0.0, -1.0, 0.0, 0.0))
    return [e, n, -d], [x, y, z, w]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sim', required=True)
    ap.add_argument('truth', nargs='+')
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--json', default=None)
    a = ap.parse_args()
    sys.dont_write_bytecode = True
    sim = Path(a.sim).resolve()
    sys.path.insert(0, str(sim))
    import pybullet as pb                              # noqa: E402
    from gorgesim.plant import Plant, FormationPlant   # noqa: E402  (puts sim/world on sys.path)
    n = len(a.truth)
    p = Plant() if n == 1 else FormationPlant([[0.0, 3.0 * k] for k in range(n)])
    p.reset()
    client, drones = p.env.CLIENT, list(p.env.DRONE_IDS)
    data = [list(csv.DictReader(open(f))) for f in a.truth]
    rows = min(len(d) for d in data)
    def flying(d, k):
        return d[k]['actuator_armed_armed'] == 'True' and 1 <= int(d[k]['mission_result_seq_current']) < last[id(d)]
    last = {id(d): max(int(r['mission_result_seq_current']) for r in d) for d in data}
    air = [k for k in range(rows) if any(flying(d, k) for d in data)]
    if not air:
        print('metrics: never in the air')
        return 1
    k0, k1 = air[0], air[-1]
    best = {'clearance': [(CLEAR_MAX, None)] * n, 'center': (math.inf, None), 'gap': (math.inf, None)}
    for k in range(k0, k1 + 1, a.every):
        poses = []
        for i, d in enumerate(data):
            r = d[k]
            pos, q = pyb_pose(*(float(r[c]) for c in ('pos_n', 'pos_e', 'pos_d', 'q1', 'q2', 'q3', 'q4')))
            pb.resetBasePositionAndOrientation(drones[i], pos, q, physicsClientId=client)
            poses.append((float(r['t_us']) * 1e-6, float(r['pos_n']), float(r['pos_e']), -float(r['pos_d'])))
        for i in range(n):
            if not flying(data[i], k):          # each vehicle's clearance in its own air window
                continue
            c = p.clearance(i, CLEAR_MAX)
            if c < best['clearance'][i][0]:
                best['clearance'][i] = (c, poses[i])
        if n == 2:
            t, n1, e1, u1 = poses[0]
            _, n2, e2, u2 = poses[1]
            c = math.sqrt((n1 - n2) ** 2 + (e1 - e2) ** 2 + (u1 - u2) ** 2)
            if c < best['center'][0]:
                best['center'] = (c, (t, n1, e1, n2, e2))
            gp = pb.getClosestPoints(drones[0], drones[1], 10.0, physicsClientId=client)
            gap = min(q[8] for q in gp) if gp else 10.0
            if gap < best['gap'][0]:
                best['gap'] = (gap, (t, n1, e1, n2, e2))
    # heading against the direction of travel, wherever a vehicle moves faster than 1 m/s horizontally;
    # also after the first leg (the turn from the takeoff heading happens on the first leg)
    for i, d in enumerate(data):
        offs = []
        for k in range(k0, k1 + 1, a.every):
            if not flying(d, k):
                continue
            r = d[k]
            vn, ve = float(r['vel_n']), float(r['vel_e'])
            if math.hypot(vn, ve) < 1.0:
                continue
            q1, q2, q3, q4 = (float(r[c]) for c in ('q1', 'q2', 'q3', 'q4'))
            yaw = math.degrees(math.atan2(2 * (q1 * q4 + q2 * q3), 1 - 2 * (q3 * q3 + q4 * q4)))
            offs.append((int(r['mission_result_seq_current']),
                         ((yaw - math.degrees(math.atan2(ve, vn)) + 180) % 360) - 180))
        if offs:
            first = min(s_ for s_, _ in offs)
            for tag, sel in (('', [o for _, o in offs]), ('_after_first_leg', [o for s_, o in offs if s_ > first])):
                sel = sorted(sel)
                med = sel[len(sel) // 2]
                devs = sorted(abs(((o - med + 180) % 360) - 180) for o in sel)
                best[f'heading{i}{tag}'] = (med, devs[int(0.95 * (len(devs) - 1))], devs[-1], len(sel))
    # the plant's own measure, if it has one: wall_clear (side surfaces only, capped at 2 m; plant_sim)
    for i, d in enumerate(data):
        if 'wall_clear' in d[0]:
            w = min((float(d[k]['wall_clear']), k) for k in range(k0, k1 + 1) if flying(d, k))
            best[f'wall{i}'] = (w[0], float(d[w[1]]['t_us']) * 1e-6)
    out = {'air_s': [float(data[0][k0]['t_us']) * 1e-6, float(data[0][k1]['t_us']) * 1e-6]}
    for i in range(n):
        c, p = best['clearance'][i]
        out[f'v{i + 1}_clearance_min_m'] = round(c, 3)
        out[f'v{i + 1}_clearance_min_at'] = p and dict(t=round(p[0], 2), north=round(p[1], 2), east=round(p[2], 2), up=round(p[3], 2))
        print('metrics: V%d wall clearance min %.3f m in the air (%.1f to %.1f s), at t %.2f s, N %.2f E %.2f'
              % (i + 1, c, out['air_s'][0], out['air_s'][1], p[0], p[1], p[2]))
        if f'wall{i}' in best:
            w, t = best[f'wall{i}']
            out[f'v{i + 1}_plant_wall_clear_min_m'] = round(w, 3)
            print('metrics: V%d the plant\'s wall_clear (side walls only, at most 2 m) min %.3f m in the air, at t %.2f s'
                  % (i + 1, w, t))
        for tag, what in (('', 'the whole route'), ('_after_first_leg', 'after the first leg')):
            if f'heading{i}{tag}' not in best:
                continue
            med, p95, mx, cnt = best[f'heading{i}{tag}']
            out[f'v{i + 1}_heading_vs_travel{tag}_median_deg'] = round(med, 1)
            out[f'v{i + 1}_heading_vs_travel{tag}_p95_dev_deg'] = round(p95, 1)
            out[f'v{i + 1}_heading_vs_travel{tag}_max_dev_deg'] = round(mx, 1)
            print('metrics: V%d heading minus direction of travel, %s (moving > 1 m/s, %d samples at 100 Hz): '
                  'median %.1f deg; 95 %% of samples within %.1f deg of it, all within %.1f deg'
                  % (i + 1, what, cnt, med, p95, mx))
    if n == 2:
        out['separation_center_min_m'] = round(best['center'][0], 3)
        out['separation_body_gap_min_m'] = round(best['gap'][0], 3)
        out['separation_min_at_s'] = round(best['center'][1][0], 2)
        print('metrics: separation min %.3f m between centers (t %.2f s), %.3f m between collision bodies'
              % (best['center'][0], best['center'][1][0], best['gap'][0]))
    if a.json:
        Path(a.json).write_text(json.dumps(out, indent=1) + '\n')
    return 0


sys.exit(main())
