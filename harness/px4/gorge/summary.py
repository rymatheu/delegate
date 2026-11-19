#!/usr/bin/env python3
"""summary.py OUT RC: the short PASS/FAIL summary of a PX4 gorge flight (px4/fly_gorge.sh) from
the files in OUT: the ground station's stages (gcs.log), the monitors' verdicts of every served
session (serve*.log: guarantee violations and discharge failures, i.e. assumption failures, per
instance), the real-time factor (relay*.log) and the wall clearance and separation (metrics.json).
PASS when RC is 0, every stage passed, no clause was violated, no assumption failed, and no vehicle
touched the gorge in the air (clearance above 0)."""
import glob
import json
import os
import re
import sys

out, rc = sys.argv[1], int(sys.argv[2])
ok = rc == 0
lines = []
gcs = open(os.path.join(out, 'gcs.log')).read().splitlines() if os.path.exists(os.path.join(out, 'gcs.log')) else []
stages = [l for l in gcs if re.match(r'gcs: V\d .* (PASS|FAIL)', l)]
fails = [l for l in stages if ' FAIL' in l]
ok &= bool(stages) and not fails
lines.append('ground station: %d stages, %d failed%s' % (len(stages), len(fails),
             ''.join('\n  ' + l for l in fails)))
lines += ['  ' + l[5:] for l in gcs if re.match(r'gcs: V\d (every item|landed|arm accepted|mission upload)', l)]
lines += ['  ' + l[5:] for l in gcs if 'commands sent' in l]
for f in sorted(glob.glob(os.path.join(out, 'serve*.log'))):
    s = open(f).read().splitlines()
    summ = [l for l in s if l.startswith('summary:')]
    inst = [l.strip() for l in s if re.match(r'\s+\S+: assumption failed in', l)]
    bad = [l for l in inst if not re.search(r'assumption failed in 0 cases; guarantee violations: none', l)]
    first = [l for l in s if 'violated' in l or 'discharge failure' in l][:8]
    ok &= bool(summ) and not bad
    lines.append('%s: %s; %d instances monitored, %d with a violation or a discharge failure'
                 % (os.path.basename(f), summ[0][9:] if summ else 'no summary (session not ended)', len(inst), len(bad)))
    lines += ['  ' + l for l in bad] + ['  first: ' + l for l in first]
for f in sorted(glob.glob(os.path.join(out, 'relay*.log'))):
    end = [l for l in open(f).read().splitlines() if 'socket closed after' in l]
    if end:
        m = re.search(r'after (\d+) ticks \(([\d.]+) s simulated\) in ([\d.]+) s: ([\d.]+) ticks/s, step round trip ([\d.]+) ms', end[-1])
        if m:
            sim_s, wall_s = float(m.group(2)), float(m.group(3))
            lines.append('%s: %.1f s simulated in %.1f s wall: real-time factor %.2f (%s ticks/s of 400; step %s ms of 2.5)'
                         % (os.path.basename(f), sim_s, wall_s, sim_s / max(wall_s, 1e-9), m.group(4), m.group(5)))
    else:
        lines.append('%s: no end line' % os.path.basename(f))
mj = os.path.join(out, 'metrics.json')
if os.path.exists(mj):
    m = json.load(open(mj))
    for k in sorted(m):
        if k.endswith('clearance_min_m'):
            at = m.get(k.replace('_m', '_at'))
            lines.append('%s wall clearance min %.3f m in the air%s' % (k[:2].upper(), m[k],
                         at and ' (t %.1f s, N %.1f m)' % (at['t'], at['north']) or ''))
            ok &= m[k] > 0
            w = m.get(k[:2] + '_plant_wall_clear_min_m')
            if w is not None:
                lines[-1] += "; plant_sim's wall_clear (side walls, capped at 2 m) min %s" % ('%.3f m' % w if w < 2 else 'at the cap')
    for k in sorted(m):
        if k.endswith('heading_vs_travel_median_deg'):
            v = k[:2]
            a = v + '_heading_vs_travel_after_first_leg_'
            lines.append('%s heading minus direction of travel: median %.1f deg (95 %% within %.1f deg of it); after '
                         'the first leg median %.1f deg, 95 %% within %.1f deg, all within %.1f deg'
                         % (v.upper(), m[k], m[v + '_heading_vs_travel_p95_dev_deg'], m[a + 'median_deg'],
                            m[a + 'p95_dev_deg'], m[a + 'max_dev_deg']))
    if 'separation_center_min_m' in m:
        lines.append('separation min %.3f m between centers, %.3f m between collision bodies (t %.1f s)'
                     % (m['separation_center_min_m'], m['separation_body_gap_min_m'], m['separation_min_at_s']))
        ok &= m['separation_body_gap_min_m'] > 0
else:
    ok = False
    lines.append('metrics: none (metrics.log)')
print('\n'.join(lines))
print('RESULT %s' % ('PASS' if ok else 'FAIL'))
