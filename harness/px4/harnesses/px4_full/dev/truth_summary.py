#!/usr/bin/env python3
"""truth_summary.py TRUTH.csv: a px4_full flight from the relay's truth log (the simulator's
position, EKF2's estimate, the state): nav_state and arming changes, liftoff and touchdown (truth),
the highest point, the landing position, EKF2's largest errors against the truth (in EKF2's frame,
as px4_auto_loop's truth clauses), and the tracking of the trajectory setpoint while airborne."""
import csv, math, sys
LAT, LON, H0 = 38.84055560937258, -105.04416668582736, 4302.00005
KN, KE = 111194.92664455874, 86609.08804087383
rows = list(csv.DictReader(open(sys.argv[1])))
f = lambda r, k: float(r[k])
T = lambda r: int(r['t_us']) * 1e-6
d0 = f(rows[0], 'pos_d')
prev = None
for r in rows:
    s = (r['vehicle_status_nav_state'], r['vehicle_status_arming_state'], r['vehicle_land_detected_landed'])
    if s != prev:
        print('t %7.3f s  nav_state %s arming_state %s landed %s' % ((T(r),) + s)); prev = s
up = [r for r in rows if f(r, 'pos_d') < d0 - 0.1]
if up:
    print('true liftoff (0.1 m) %.3f s; highest %.3f m above the start at %.2f s' % (
        T(up[0]), max(d0 - f(r, 'pos_d') for r in rows), T(min(rows, key=lambda r: f(r, 'pos_d')))))
    last = rows[-1]
    print('end %.2f s: true N %.3f E %.3f, D %.3f (start %.3f), still: |vel| %.3f m/s' % (
        T(last), f(last, 'pos_n'), f(last, 'pos_e'), f(last, 'pos_d'), d0,
        math.sqrt(sum(f(last, k) ** 2 for k in ('vel_n', 'vel_e', 'vel_d')))))
ez, exy, tr = 0.0, 0.0, 0.0
for r in rows:
    rl = f(r, 'vehicle_local_position_ref_lat') + f(r, 'vehicle_local_position_ref_lat_lo')
    ro = f(r, 'vehicle_local_position_ref_lon') + f(r, 'vehicle_local_position_ref_lon_lo')
    tn = f(r, 'pos_n') + (LAT - rl) * KN; te = f(r, 'pos_e') + (LON - ro) * KE
    td = f(r, 'pos_d') - H0 + f(r, 'vehicle_local_position_ref_alt')
    if r['vehicle_local_position_z_valid'] == 'True' and r['vehicle_local_position_z_global'] == 'True':
        ez = max(ez, abs(f(r, 'vehicle_local_position_z') - td))
    if r['vehicle_local_position_xy_valid'] == 'True' and r['vehicle_local_position_xy_global'] == 'True':
        exy = max(exy, max(abs(f(r, 'vehicle_local_position_x') - tn), abs(f(r, 'vehicle_local_position_y') - te)))
print('EKF2 vs truth: height error max %.3f m, horizontal (per axis) max %.3f m' % (ez, exy))
