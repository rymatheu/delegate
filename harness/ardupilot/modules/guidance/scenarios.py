# scenarios.py: the guidance module's saved cases, written as replayable case files.
#
#   python3 -I ardupilot/modules/guidance/scenarios.py      (from the harness directory, after the build)
#
# Each case runs the module executable through the module protocol and records its outputs, so
# `harness replay FILE` reproduces it bit for bit; the case's note says what it shows. The two
# small cases are kept in the module folder; the closed-loop one is long (about 1000 ticks, 5 MB)
# and is written to build/guidance/ on demand.
#
#   arc-radius-case.json          1 tick: an ARC_WAYPOINT leg whose horizontal chord is between
#                                 FLT_EPSILON and 2 FLT_EPSILON raises an internal error
#   spline-reached-case.json      3 ticks: a spline leg reports reached while its target is
#                                 still at the origin, after a jump of the desired velocity
#   build/guidance/speed-overshoot-case.json
#                                 closed loop with an ideal position stage: pause, resume, then a
#                                 speed reduction drive the target speed above WP_SPD
import json
import os
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
EXE = os.path.join(HARNESS, 'build/modules/guidance/guidance')
FMT = {'f32': '<f', 'i32': '<i', 'u32': '<I'}
C = 'cmd_guidance_'


def f32(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


class Module:
    def __init__(self):
        self.p = subprocess.Popen([EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL)
        self.p.stdin.write(b'D')
        self.p.stdin.flush()
        assert self.p.stdout.read(1) == b'K'
        n = struct.unpack('<I', self.p.stdout.read(4))[0]
        m = json.loads(self.p.stdout.read(n))
        self.code_hash = m['code_hash']
        self.schema = {k: m[k] for k in ('params', 'input', 'output')}

    def pack(self, schema, d):
        b = b''
        for fd in schema:
            v = d.get(fd['name'], 0)
            b += bytes([1 if v else 0]) if fd['type'] == 'bool' else struct.pack(FMT[fd['type']], v)
        return b

    def init(self, p):
        self.p.stdin.write(b'I' + self.pack(self.schema['params'], p))
        self.p.stdin.flush()
        assert self.p.stdout.read(1) == b'K'

    def step(self, i):
        self.p.stdin.write(b'S' + self.pack(self.schema['input'], i))
        self.p.stdin.flush()
        assert self.p.stdout.read(1) == b'K'
        out = {}
        for fd in self.schema['output']:
            if fd['type'] == 'bool':
                out[fd['name']] = self.p.stdout.read(1)[0] == 1
            else:
                out[fd['name']] = struct.unpack(FMT[fd['type']], self.p.stdout.read(4))[0]
        return out

    def record(self, kind, d):
        r = {}
        for fd in self.schema[kind]:
            v = d.get(fd['name'], 0)
            if fd['type'] == 'bool':
                r[fd['name']] = 'true' if v else 'false'
            elif fd['type'] == 'f32':
                r[fd['name']] = '0x%08x' % struct.unpack('<I', struct.pack('<f', v))[0]
            else:
                r[fd['name']] = str(int(v))
        return r

    def write(self, path, clause, note, params, ins, outs):
        case = dict(module='guidance', code_hash=self.code_hash, campaign='none', kind='scenario',
                    clause=clause, case=0, step=len(ins) - 1, note=note,
                    params=self.record('params', params),
                    inputs=[self.record('input', i) for i in ins],
                    outputs=[self.record('output', o) for o in outs])
        with open(path, 'w') as fh:
            json.dump(case, fh, indent=1)
        print(f'wrote {os.path.relpath(path, HARNESS)} ({len(ins)} ticks)')


# ArduCopter's default parameters (Module.lean, stockParams)
STOCK = dict(wp_spd=10.0, wp_radius_m=2.0, wp_spd_up=2.5, wp_spd_dn=1.5, wp_acc=2.5, wp_acc_z=1.0,
             wp_acc_cnr=0.0, wp_jerk=1.0, wp_ter_margin=10.0, atc_rate_r_max=0.0,
             atc_rate_p_max=0.0, atc_input_tc=0.1, atc_acc_r_max=1100.0, atc_acc_p_max=1100.0,
             psc_ne_pos_p=1.0, psc_ne_jerk=5.0)


def limits(p):
    return dict(pc_ne_max_speed=p['wp_spd'], pc_ne_max_accel=p['wp_acc'],
                pc_max_speed_up=p['wp_spd_up'], pc_max_speed_down=p['wp_spd_dn'],
                pc_d_max_accel=p['wp_acc_z'])


def arc_radius_case():
    m = Module()
    m.init(STOCK)
    i = dict(dt=0.0025, now_ms=1000, est_pos_d=-10.0, pc_pos_target_d=-10.0,
             pc_stopping_point_d=-10.0, **limits(STOCK))
    i.update({C + 'wp_and_spline_init_m': True, C + 'set_wp_destination_NED_m': True,
              C + 'set_wp_destination_NED_m_destination_e': 2e-7,
              C + 'set_wp_destination_NED_m_destination_d': -20.0,
              C + 'set_wp_destination_NED_m_arc_rad': 2.48, C + 'update_wpnav': True})
    o = m.step(i)
    assert o['wp_internal_errors'] == 1 and o['wp_internal_errors_uninit'] == 0
    m.write(os.path.join(HERE, 'arc-radius-case.json'), 'no_internal_error_initialized',
            'An ARC_WAYPOINT leg from (0, 0, -10) to (0, 2e-7, -20) with arc angle 2.48 rad: a '
            'climb of 10 m (so the leg is not zero length, SCurve.cpp:80) with a horizontal chord of '
            '2e-7 m. SCurve::calculate_track (SCurve.cpp:88) takes the arc branch because the chord length '
            '2e-7 is_positive (>= FLT_EPSILON, 1.19e-7), and its comment says the radius is then '
            'positive; the radius chord / (2 |sin(1.24)|) = 1.06e-7 is below FLT_EPSILON, so '
            'project_scurve_onto_track (SCurve.cpp:678) finds !is_positive(arc.radius_ne), raises '
            'invalid_arg_or_result and clears the leg. The two guards disagree. A mission item cannot '
            'produce this chord (Location resolution 1e-7 deg, about 1.1 cm); the assumption now '
            'excludes arc legs (arc_rad = 0).', STOCK, [i], [o])


def spline_reached_case():
    m = Module()
    p = dict(STOCK)
    m.init(p)
    base = dict(est_pos_d=-10.0, pc_pos_target_d=-10.0, pc_stopping_point_d=-300.0,
                **limits(p))
    i0 = dict(base, dt=0.0001, now_ms=1000)
    i0.update({C + 'wp_and_spline_init_m': True, C + 'set_spline_destination_NED_m': True,
               C + 'set_spline_destination_NED_m_destination_d': -10.0,
               C + 'set_spline_destination_NED_m_next_destination_e': 1e-6,
               C + 'set_spline_destination_NED_m_next_destination_d': -10.0,
               C + 'update_wpnav': True, C + 'wp_and_spline_init_m_stopping_point_d': -300.0})
    o0 = m.step(i0)
    i1 = dict(base, dt=0.0001, now_ms=1001, pc_vel_desired_d=1e-6)
    i1[C + 'update_wpnav'] = True
    o1 = m.step(i1)
    i2 = dict(base, dt=0.0025, now_ms=1003, pc_vel_desired_d=30.0)
    i2[C + 'update_wpnav'] = True
    o2 = m.step(i2)
    assert not o1['wp_reached'] and o2['wp_reached'] and abs(o2['tgt_pos_d'] - (-10.0)) > 1.0
    m.write(os.path.join(HERE, 'spline-reached-case.json'), 'reached_holds (spline legs)',
            'A spline leg from the stopping point (0, 0, -300) to (0, 0, -10), leaving towards '
            '(0, 1e-6, -10): its origin velocity is 0 and its destination velocity tiny but not '
            'zero, so it is a fast waypoint. Tick 0 starts it (the initialization zeroes the desired '
            'velocity, so the spline time stays 0). Tick 1 (dt 1e-4, desired velocity 1e-6 m/s) '
            'advances the spline time to about 3e-7 (the zero-velocity branch of '
            'SplineCurve::calc_dt_speed_max, spline_dt = sqrt(2 d / |a|)). Tick 2: the position stage '
            'reports a desired velocity of 30 m/s; the spline velocity at that time is about 6e-4, so '
            'spline_dt = d / |v| is over 100 and SplineCurve::advance_target_along_track sets the '
            'time to 1 and reached; the '
            'target of that tick is still computed at the old time (the origin), 290 m from the '
            'destination, and AC_WPNav reports the leg finished (s_finished, fast waypoint). In '
            'ArduCopter the desired velocity is the target velocity of the previous tick, so the '
            'jump needs a position stage that does not follow the target; reached_holds is stated '
            'for S-curve legs only.', p, [i0, i1, i2], [o0, o1, o2])


def speed_overshoot_case():
    p = dict(STOCK, wp_jerk=20.0, wp_spd=5.0)
    m = Module()
    m.init(p)
    start, dest, dt = (0.0, 0.0, -10.0), (200.0, 0.0, -10.0), 0.0025
    est, vel, lim = list(start), [0.0, 0.0, 0.0], limits(p)
    events = {700: {C + 'set_pause': True}, 800: {C + 'set_resume': True},
              950: {C + 'set_speed_NE_ms': True, C + 'set_speed_NE_ms_speed_ms': 0.1}}
    ins, outs = [], []
    for k in range(1000):
        i = dict(dt=dt, now_ms=1000 + int(k * 2.5), est_pos_n=est[0], est_pos_e=est[1],
                 est_pos_d=est[2], est_vel_n=vel[0], est_vel_e=vel[1], est_vel_d=vel[2],
                 pc_vel_desired_n=vel[0], pc_vel_desired_e=vel[1], pc_vel_desired_d=vel[2],
                 pc_pos_target_d=est[2], pc_stopping_point_n=start[0],
                 pc_stopping_point_e=start[1], pc_stopping_point_d=start[2], **lim)
        i[C + 'update_wpnav'] = True
        if k == 0:
            i.update({C + 'wp_and_spline_init_m': True, C + 'set_wp_destination_NED_m': True})
            for c, x in zip('ned', dest):
                i[C + 'set_wp_destination_NED_m_destination_' + c] = x
        i.update(events.get(k, {}))
        o = m.step(i)
        ins.append(i)
        outs.append(o)
        # an ideal position stage: the vehicle is where the target was, with its velocity, and
        # the position controller holds the limits it was handed
        est = [o['tgt_pos_n'], o['tgt_pos_e'], o['tgt_pos_d']]
        vel = [o['tgt_vel_n'], o['tgt_vel_e'], o['tgt_vel_d']]
        lim = dict(pc_ne_max_speed=o['tgt_ne_max_speed'], pc_ne_max_accel=o['tgt_ne_max_accel'],
                   pc_max_speed_up=o['tgt_max_speed_up'],
                   pc_max_speed_down=o['tgt_max_speed_down'], pc_d_max_accel=o['tgt_d_max_accel'])
    peak = max(range(len(outs)), key=lambda k: outs[k]['tgt_vel_n'])
    o = outs[peak]
    assert o['tgt_vel_n'] > 1.2 * p['wp_spd']
    os.makedirs(os.path.join(HARNESS, 'build/guidance'), exist_ok=True)
    m.write(os.path.join(HARNESS, 'build/guidance/speed-overshoot-case.json'),
            'speed_within_limits_as_first_stated',
            f'Stock parameters except WP_SPD 5 and WP_JERK 20, a 200 m leg north, an ideal '
            f'position stage (the estimate is the previous target, the desired velocity the '
            f'previous target velocity, the limits those handed over). set_pause at tick 700, '
            f'set_resume at 800, set_speed_NE_ms(0.1) at 950. At tick {peak} the target speed is '
            f'{o["tgt_vel_n"]:.4f} m/s with WP_SPD 5 and a speed limit of 0.1: set_speed_NE_ms scales '
            f'_offset_vel_ms by the speed ratio (AC_WPNav.cpp:283) but keeps _offset_accel_mss, the '
            f'resume acceleration; the jerk-limited shaper (shape_vel_accel, PSC_NE_JERK) carries '
            f'the offset to {o["wp_offset_vel"]:.4f} > 0.1, and the target velocity is the S-curve '
            f'velocity (still near 5 m/s: the replanned leg keeps its committed speed, '
            f'SCurve::set_speed_max) times _offset_vel_ms / _wp_desired_speed_ne_ms '
            f'(AC_WPNav.cpp:599, 631). With all stock parameters (WP_SPD 10), pause at 3000, resume '
            f'at 3800 and the change at 4100 the target reaches 20.8 m/s.',
            p, ins[:peak + 1], outs[:peak + 1])


if __name__ == '__main__':
    which = sys.argv[1:] or ['arc', 'spline', 'speed']
    if 'arc' in which:
        arc_radius_case()
    if 'spline' in which:
        spline_reached_case()
    if 'speed' in which:
        speed_overshoot_case()
