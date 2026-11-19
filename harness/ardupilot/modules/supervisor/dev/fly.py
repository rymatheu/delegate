#!/usr/bin/env python3
"""Fly the full stack (ardupilot/harnesses/ap_full) from a scripted ground station, over `harness serve`.

  python3 -I ardupilot/modules/supervisor/dev/fly.py guided [--steps N] [--log FILE]
  python3 -I ardupilot/modules/supervisor/dev/fly.py auto   [--steps N] [--log FILE]

The composite is served by `.lake/build/bin/harness serve ap_full` (monitors inside, verdicts in
build/serve/ap_full.log; with --record also a ledger record of the session, none by default). This client is the ground station and the clock: each step it sends
now_us/now_ms/dt for one 400 Hz tick, no RC (all channels 0, FS_THR_ENABLE 0), and up to 256 bytes
of MAVLink from a script:
  guided  GUIDED, arm, takeoff to 2 m, at 2 m a position target 10 m north (SET_POSITION_TARGET_
          LOCAL_NED), when there LAND
Options: --node NAME (ap_full, default, with truth_est; ap_full_ekf with the real estimator),
  --noise (the simulator's sensor noise; --seed N, default 1), --csv FILE (per tick: time,
  true and estimated position, guidance target, mode, armed; from h-apctl). With the estimator
  the script waits, disarmed on the ground, until the EKF uses GPS and has an origin.
  rtl     GUIDED takeoff to 2 m, a position target 10 m north, then RTL (RTL_ALT default 15 m)
          back to home, landing and disarm
  althold pilot sticks over RC (channels 1-4 at 1500, throttle 1000, channel 5 low: FLTMODE1 =
          ALT_HOLD): rudder arming (yaw stick right, throttle low), throttle up to climb, mid to
          hold, pitch forward, throttle low to descend and land, rudder disarm
  auto10  the same mission ending with LAND at 10 m north (WP 20 m north left out)
  loiter  pilot sticks over RC as althold, FLTMODE1 = LOITER: rudder arming, throttle up to climb
          to 2.5 m, mid to hold; hands off for 8 s (the hold), a pitch-forward nudge for 1.5 s
          (north), release and hold for 6 s, throttle low to descend and land, rudder disarm.
          Prints the hold drift against the simulator's truth and the nudge response
  auto    upload a mission (home, takeoff 2 m, waypoint 10 m north at 2 m, waypoint 20 m north
          at 2 m, LAND there; the gorge runs north: 10 m east at 2 m is its wall), arm in GUIDED, switch to AUTO
Parameters: the stock regimes of the stages (`harness contract`: every `name = value` of rate_c's
stock_flight, mixer's stock_flight, position's and attitude's stock_flight, guidance's
stock_leg), the supervisor's from dev/drive.py, no sensor noise.
"""
import math
import os
import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(HARNESS, 'py'))
sys.path.insert(0, os.path.join(HARNESS, 'deps', 'mavlink'))
sys.path.insert(0, os.path.join(HARNESS, 'build', 'gen', 'supervisor', 'py'))
os.environ.setdefault('MAVLINK20', '1')
import module_protocol as mp  # noqa: E402
import apm as mav  # noqa: E402
import json  # noqa: E402

HB = os.path.join(HARNESS, '.lake', 'build', 'bin', 'harness')
ORIGIN = (473977420, 85455940, 48800)


def stock_params():
    vals = {}
    for node, regs in (('rate_c', ['stock_flight']), ('mixer', ['stock_flight']),
                       ('position', ['stock_flight']), ('attitude', ['stock_flight']),
                       ('guidance', ['stock_leg']), ('estimator', ['plant_like']),
                       ('loiter', ['stock_flight'])):
        txt = subprocess.run([HB, 'contract', node], cwd=HARNESS, capture_output=True,
                             text=True).stdout
        for line in txt.splitlines():
            m = re.match(r'regime (\w+):(.*)', line)
            if m and m.group(1) in regs:
                for k, v in re.findall(r'(\w+) = (true|false|-?[0-9][0-9.e+-]*)\b', m.group(2)):
                    vals[k] = {'true': True, 'false': False}.get(v, v)
    return vals


class Served:
    def __init__(self, node='ap_full'):
        # the session's ledger record only when asked (--record); its log in build/serve/NODE.log
        self.p = subprocess.Popen([HB, 'serve', node] + (['--record'] if '--record' in sys.argv else []),
                                  cwd=HARNESS, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE)
        self.p.stdin.write(b'D')
        self.p.stdin.flush()
        assert self.p.stdout.read(1) == b'K'
        n = struct.unpack('<I', self.p.stdout.read(4))[0]
        self.schema = json.loads(self.p.stdout.read(n))

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
        nout = mp.record_bytes(self.schema['output'])
        return mp.unpack(self.schema['output'],
                         self.req(b'S' + mp.pack(self.schema['input'], inp), nout))


def main():
    scen = sys.argv[1]
    nsteps = int(sys.argv[sys.argv.index('--steps') + 1]) if '--steps' in sys.argv else 12000
    log = open(sys.argv[sys.argv.index('--log') + 1], 'w') if '--log' in sys.argv else None
    node = sys.argv[sys.argv.index('--node') + 1] if '--node' in sys.argv else 'ap_full'
    noise = '--noise' in sys.argv
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    csv = open(sys.argv[sys.argv.index('--csv') + 1], 'w') if '--csv' in sys.argv else None
    s = Served(node)
    has_ekf = any(f['name'] == 'est_ekf_using_gps' for f in s.schema['output'])
    if csv:
        csv.write('t_s,mode,armed,land_complete,pos_n,pos_e,pos_d,est_pos_n,est_pos_e,est_pos_d,'
                  'tgt_valid,tgt_pos_n,tgt_pos_e,tgt_pos_d\n')
    stock = stock_params()
    params = {}
    for f in s.schema['params']:
        n, t = f['name'], f['type']
        if n in stock:
            v = stock[n]
            params[n] = v if t == 'bool' else (float(v) if t == 'f32' else int(float(v)))
        else:
            params[n] = False if t == 'bool' else 0
    params.update(mav_sysid=1, fltmode1={'althold': 2, 'loiter': 5}.get(scen, 0), initial_mode=0, arming_skipchk=-1, fs_thr_enable=0,
                  fs_gcs_enable=0, rc_options=32, auto_options=2, gps1_type=1, noise_on=noise,
                  noise_seed=seed if noise else 0,
                  origin_lat_e7=ORIGIN[0], origin_lon_e7=ORIGIN[1], origin_alt_cm=ORIGIN[2])
    missing = [f['name'] for f in s.schema['params'] if f['name'] not in stock and
               f['name'] not in ('mav_sysid', 'fltmode1', 'initial_mode', 'arming_skipchk',
                                 'fs_thr_enable', 'fs_gcs_enable', 'rc_options', 'auto_options', 'gps1_type', 'noise_on',
                                 'noise_seed', 'origin_lat_e7', 'origin_lon_e7', 'origin_alt_cm')]
    print('parameters not in a stock regime (0):', missing)
    s.init(params)
    gcs = mav.MAVLink(None, srcSystem=255, srcComponent=190)
    parser = mav.MAVLink(None)
    parser.robust_parsing = True
    pending = b''
    phase = 'boot'
    counts = {}
    mission = []
    if scen == 'auto10':
        scen = 'auto'
        short = True
    else:
        short = False
    ORIGIN_EKF = [ORIGIN[0], ORIGIN[1]]

    def item(seq, cmd, n, e, alt, frame=mav.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT):
        o = ORIGIN_EKF
        lat = o[0] + int(round(n / 111319.49079327357 * 1e7))
        lon = o[1] + int(round(e / (111319.49079327357 *
                                    math.cos(math.radians(o[0] * 1e-7))) * 1e7))
        return gcs.mission_item_int_encode(1, 1, seq, frame, cmd, 0, 1, 0, 0, 0, 0, lat, lon, alt)

    def build_mission():
        if scen != 'auto':
            return []
        mis = [item(0, mav.MAV_CMD_NAV_WAYPOINT, 0, 0, 0, mav.MAV_FRAME_GLOBAL),
               item(1, mav.MAV_CMD_NAV_TAKEOFF, 0, 0, 2),
               item(2, mav.MAV_CMD_NAV_WAYPOINT, 10, 0, 2),
               item(3, mav.MAV_CMD_NAV_WAYPOINT, 20, 0, 2),
               item(4, mav.MAV_CMD_NAV_LAND, 20, 0, 0)]
        if short:   # auto10: LAND at 10 m north, where the GUIDED flight landed on level floor
            mis = mis[:3] + [item(3, mav.MAV_CMD_NAV_LAND, 10, 0, 0)]
        return mis

    mission = build_mission()
    rc = [1500, 1500, 1000, 1500]   # roll, pitch, throttle, yaw (us)
    nan_fields = {}
    t_us = 0
    last = None
    upload_done = None
    ekf_ready = None if has_ekf else 0
    if scen == 'auto':
        phase = 'upload'
    lt = {}          # the loiter scenario's measurements
    t_phase = 0
    for k in range(nsteps):
        t_us += 2500
        inp = {f['name']: (False if f['type'] == 'bool' else 0) for f in s.schema['input']}
        inp.update(dt=0.0025, now_us=t_us, now_ms=t_us // 1000)
        if scen in ('althold', 'loiter'):
            inp.update(rc_1=rc[0], rc_2=rc[1], rc_3=rc[2], rc_4=rc[3], rc_5=1000, rc_6=1500,
                       rc_7=1000, rc_8=1000, rc_fresh=True)
        if k % 400 == 0:
            pending += gcs.heartbeat_encode(mav.MAV_TYPE_GCS, mav.MAV_AUTOPILOT_INVALID, 0, 0,
                                            0).pack(gcs)
        chunk, pending = pending[:256], pending[256:]
        inp['gcs_rx_len'] = len(chunk)
        padded = chunk + b'\0' * (256 - len(chunk))
        for w in range(64):
            inp['gcs_rx_w%02d' % w] = struct.unpack('<I', padded[4 * w:4 * w + 4])[0]
        out = s.step(inp)
        raw = b''.join(struct.pack('<I', out['gcs_tx_w%02d' % w]) for w in range(64))
        for m in parser.parse_buffer(raw[:out['gcs_tx_len']]) or []:
            nm = m.get_type()
            counts[nm] = counts.get(nm, 0) + 1
            for fld in m.get_fieldnames():   # the poison trap's view of the telemetry
                v = getattr(m, fld)
                if isinstance(v, float) and math.isnan(v):
                    key = '%s.%s' % (nm, fld)
                    if key not in nan_fields:
                        print('t %.2f s: NaN in telemetry %s' % (t_us * 1e-6, key))
                    nan_fields[key] = nan_fields.get(key, 0) + 1
            if nm in ('COMMAND_ACK', 'STATUSTEXT', 'MISSION_ACK', 'MISSION_ITEM_REACHED',
                      'MISSION_CURRENT') and (nm != 'MISSION_CURRENT' or counts[nm] < 3):
                print('t %.2f s <- %s' % (t_us * 1e-6, m))
            if nm in ('MISSION_REQUEST_INT', 'MISSION_REQUEST') and mission:
                pending += mission[m.seq].pack(gcs)
            if nm == 'MISSION_ACK' and m.type == 0 and phase == 'upload':
                phase = 'boot'
                upload_done = k
        alt = -out['pos_d']
        if ekf_ready is None and out['est_ekf_using_gps'] and out['est_origin_ok'] and \
                out['est_ekf_horiz_pos_abs']:
            ekf_ready = k
            print('t %.2f s: EKF using GPS with an origin; the script starts' % (t_us * 1e-6))
        if csv:
            csv.write(','.join(str(x) for x in [round(t_us * 1e-6, 4), out['mode'],
                int(out['armed']), int(out['land_complete']), out['pos_n'], out['pos_e'],
                out['pos_d'], out['est_pos_n'], out['est_pos_e'], out['est_pos_d'],
                int(out['tgt_valid']), out['tgt_pos_n'], out['tgt_pos_e'], out['tgt_pos_d']]) + '\n')
        if '--dump' in sys.argv and k + 1 == int(sys.argv[sys.argv.index('--dump') + 1]):
            for nm in sorted(out):
                pre = os.environ.get('DUMP', 'cmd_position,ac_,tgt_,est_,throttle_hover').split(',')
                if any(nm.startswith(p) for p in pre):
                    v = out[nm]
                    if v not in (0, False) or nm.endswith('_seq') is False:
                        print('   %s = %s' % (nm, v))
        # the script
        if ekf_ready is None:
            continue   # wait on the ground, disarmed, for the EKF (ap_full_ekf)
        t0 = ekf_ready if upload_done is None else upload_done
        if phase == 'upload' and k == ekf_ready + 400 and has_ekf:
            # the mission relative to the EKF origin the estimator chose (its first GPS fix),
            # not to the fixture's ORIGIN
            ORIGIN_EKF[0] = out['est_origin_lat_e7']
            ORIGIN_EKF[1] = out['est_origin_lon_e7']
            mission[:] = build_mission()
        if phase == 'upload' and k == ekf_ready + 400:
            pending += gcs.mission_count_encode(1, 1, len(mission), 0).pack(gcs)
            phase = 'upload'
            k_upload = k
        if scen == 'loiter':
            ts = (k - t0) * 0.0025
            tp = (k - t_phase) * 0.0025 if phase not in ('boot', 'arming') else 0.0
            pn, pe = out['pos_n'], out['pos_e']
            if phase in ('hold', 'nudge', 'release', 'hold2'):
                err = math.hypot(out['est_pos_n'] - pn, out['est_pos_e'] - pe)
                lt['est_err_max'] = max(lt.get('est_err_max', 0.0), err)
                lt['speed_max'] = max(lt.get('speed_max', 0.0), math.hypot(out['vel_n'], out['vel_e']))
            if phase == 'boot' and ts >= 1:
                rc[3] = 2000                       # rudder arming: yaw right, throttle low
                phase = 'arming'
            elif phase == 'arming' and out['armed']:
                rc[3] = 1500
                print('t %.2f s: armed by rudder in mode %d' % (t_us * 1e-6, out['mode']))
                phase = 'climb'
                t_phase = k
            elif phase == 'climb' and tp >= 2:
                rc[2] = 1700                       # above the mid deadzone: climb
                if alt > 2.5:
                    rc[2] = 1500                   # mid stick, sticks centered: hold
                    print('t %.2f s: at %.2f m, sticks centered (hold)' % (t_us * 1e-6, alt))
                    phase = 'hold'
                    t_phase = k
            elif phase == 'hold':
                if tp >= 1 and 'p0' not in lt:    # the hold's reference: 1 s after centering
                    lt['p0'] = (pn, pe)
                if 'p0' in lt:
                    d = math.hypot(pn - lt['p0'][0], pe - lt['p0'][1])
                    lt['hold_drift_max'] = max(lt.get('hold_drift_max', 0.0), d)
                if tp >= 8:
                    lt['hold_drift_end'] = math.hypot(pn - lt['p0'][0], pe - lt['p0'][1])
                    lt['p_nudge'] = (pn, pe)
                    rc[1] = 1400                   # pitch forward (channel 2 low = nose down)
                    print('t %.2f s: hold done at (%.2f, %.2f), nudge north' % (t_us * 1e-6, pn, pe))
                    phase = 'nudge'
                    t_phase = k
            elif phase == 'nudge':
                lt['nudge_vn_max'] = max(lt.get('nudge_vn_max', 0.0), out['vel_n'])
                if tp >= 1.5:
                    rc[1] = 1500                   # release
                    lt['p_release'] = (pn, pe)
                    print('t %.2f s: released at (%.2f, %.2f), vel_n %.2f m/s' % (
                        t_us * 1e-6, pn, pe, out['vel_n']))
                    phase = 'release'
                    t_phase = k
            elif phase == 'release':
                lt['nudge_vn_max'] = max(lt.get('nudge_vn_max', 0.0), out['vel_n'])
                if 'stop_t' not in lt and math.hypot(out['vel_n'], out['vel_e']) < 0.1:
                    lt['stop_t'] = tp
                    lt['p_stop'] = (pn, pe)
                if tp >= 6:
                    lt['p1'] = (pn, pe)
                    print('t %.2f s: after release at (%.2f, %.2f)' % (t_us * 1e-6, pn, pe))
                    phase = 'hold2'
                    t_phase = k
            elif phase == 'hold2':
                d = math.hypot(pn - lt['p1'][0], pe - lt['p1'][1])
                lt['hold2_drift_max'] = max(lt.get('hold2_drift_max', 0.0), d)
                if tp >= 4:
                    rc[2] = 1150                   # below the deadzone: descend
                    print('t %.2f s: descending at (%.2f, %.2f)' % (t_us * 1e-6, pn, pe))
                    lt['p_descend'] = (pn, pe)
                    phase = 'descend'
                    t_phase = k
            elif phase == 'descend' and out['land_complete']:
                lt['p_land'] = (pn, pe)
                rc[2] = 1000
                rc[3] = 1000                       # rudder disarm: yaw left, throttle low
                print('t %.2f s: landed at (%.2f, %.2f), rudder disarm' % (t_us * 1e-6, pn, pe))
                phase = 'land'
        elif scen == 'althold':
            ts = (k - t0) * 0.0025
            if phase == 'boot' and ts >= 1:
                rc[3] = 2000                       # rudder arming: yaw right, throttle low
                phase = 'arming'
            elif phase == 'arming' and out['armed']:
                rc[3] = 1500
                print('t %.2f s: armed by rudder' % (t_us * 1e-6))
                phase = 'climb'
                t_phase = k
            elif phase == 'climb' and (k - t_phase) * 0.0025 >= 2:
                rc[2] = 1700                       # above the mid deadzone: climb
                if alt > 2.5:
                    rc[2] = 1500                   # mid stick: hold altitude
                    print('t %.2f s: at %.2f m, throttle mid' % (t_us * 1e-6, alt))
                    phase = 'hold'
                    t_phase = k
            elif phase == 'hold' and (k - t_phase) * 0.0025 >= 3:
                rc[1] = 1400                       # pitch forward (channel 2 low = nose down)
                phase = 'forward'
                t_phase = k
            elif phase == 'forward' and (k - t_phase) * 0.0025 >= 2:
                rc[1] = 1500
                phase = 'brake'
                t_phase = k
            elif phase == 'brake' and (k - t_phase) * 0.0025 >= 3:
                rc[2] = 1150                       # below the deadzone: descend
                print('t %.2f s: descending at north %.2f m' % (t_us * 1e-6, out['pos_n']))
                phase = 'descend'
            elif phase == 'descend' and out['land_complete']:
                rc[2] = 1000
                rc[3] = 1000                       # rudder disarm: yaw left, throttle low
                print('t %.2f s: landed, rudder disarm' % (t_us * 1e-6))
                phase = 'land'
        elif phase == 'boot' and k == t0 + 400:
            pending += gcs.set_mode_encode(1, mav.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED, 4).pack(gcs)
            phase = 'guided'
        elif phase == 'guided' and k == t0 + 1200:
            pending += gcs.command_long_encode(1, 1, mav.MAV_CMD_COMPONENT_ARM_DISARM, 0, 1, 0,
                                               0, 0, 0, 0, 0).pack(gcs)
            phase = 'armed'
        elif phase == 'armed' and k == t0 + 1600:
            if scen in ('guided', 'rtl'):
                pending += gcs.command_long_encode(1, 1, mav.MAV_CMD_NAV_TAKEOFF, 0, 0, 0, 0, 0,
                                                   0, 0, 2).pack(gcs)
            else:
                pending += gcs.set_mode_encode(1, mav.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED,
                                               3).pack(gcs)
            phase = 'takeoff'
        elif phase == 'takeoff' and scen in ('guided', 'rtl') and alt > 1.9:
            pending += gcs.set_position_target_local_ned_encode(
                0, 1, 1, mav.MAV_FRAME_LOCAL_NED, 0b110111111000, 10, 0, -2, 0, 0, 0, 0, 0, 0, 0,
                0).pack(gcs)
            print('t %.2f s: at %.2f m, position target 10 m north sent' % (t_us * 1e-6, alt))
            phase = 'goto'
        elif phase == 'goto' and abs(out['pos_n'] - 10) < 0.5 and abs(out['vel_n']) < 0.3:
            m_end = 6 if scen == 'rtl' else 9
            pending += gcs.set_mode_encode(1, mav.MAV_MODE_FLAG_CUSTOM_MODE_ENABLED,
                                           m_end).pack(gcs)
            print('t %.2f s: at north %.2f m, %s sent' % (t_us * 1e-6, out['pos_n'],
                                                         'RTL' if m_end == 6 else 'LAND'))
            phase = 'land'
        state = (out['mode'], out['armed'], out['spool_state'], out['land_complete'])
        if state != last or k % 400 == 0:
            line = ('t %6.2f mode %d armed %d spool %d landed %d  pos %6.2f %6.2f %6.2f  vel %5.2f '
                    '%5.2f %5.2f  thr %.3f  unans %d unmapped %d conflicts %d errs %d/%d/%d/%d' % (
                        t_us * 1e-6, out['mode'], out['armed'], out['spool_state'],
                        out['land_complete'], out['pos_n'], out['pos_e'], out['pos_d'],
                        out['vel_n'], out['vel_e'], out['vel_d'], out['throttle_out'],
                        out['unanswered'], out['cmd_unmapped'], out['sup_cmd_conflicts'],
                        out['sup_internal_errors'], out['pc_internal_errors'],
                        out['ac_internal_errors'], out['wp_internal_errors']))
            print(line)
            last = state
        if log:
            log.write('%.4f %.4f %.4f %.4f %d %d\n' % (t_us * 1e-6, out['pos_n'], out['pos_e'],
                                                     out['pos_d'], out['mode'], out['armed']))
        if (phase == 'land' or (scen == 'auto' and phase == 'takeoff' and alt > 1)):
            if scen == 'auto' and phase == 'takeoff':
                phase = 'land'   # in the air: the end is AUTO's LAND and the auto-disarm
        if phase == 'land' and out['land_complete'] and not out['armed']:
            print('t %.2f s: landed and disarmed' % (t_us * 1e-6))
            break
        if math.isnan(out['pos_d']) or alt < -5 or abs(out['pos_n']) > 200:
            print('t %.2f s: STOP, vehicle state out of bounds' % (t_us * 1e-6))
            break
    if scen == 'loiter':
        def fmt(x):
            return '(%.3f, %.3f)' % x if isinstance(x, tuple) else ('%.3f' % x)
        print('LOITER summary (truth = the simulator\'s position):')
        for key, what in [('hold_drift_max', 'hold, 8 s hands off: largest horizontal drift from the position 1 s after centering, m'),
                          ('hold_drift_end', 'hold: drift at its end, m'),
                          ('p_nudge', 'position at the nudge'), ('p_release', 'position at release (1.5 s pitch forward)'),
                          ('nudge_vn_max', 'largest north speed during nudge and braking, m/s'),
                          ('stop_t', 'time from release to |v| < 0.1 m/s, s'), ('p_stop', 'position there'),
                          ('p1', 'position 6 s after release'),
                          ('hold2_drift_max', 'second hold, 4 s: largest drift, m'),
                          ('est_err_max', 'largest |estimate - truth| horizontal while holding and nudging, m'),
                          ('speed_max', 'largest horizontal speed in those phases, m/s'),
                          ('p_descend', 'position when the descent started'), ('p_land', 'position at touchdown')]:
            if key in lt:
                print('  %-16s %-14s %s' % (key, fmt(lt[key]), what))
    print('messages received:', dict(sorted(counts.items())))
    print('telemetry fields that carried NaN:', nan_fields or 'none')
    print('poisoned_reads (f32 outputs):', out['poisoned_reads'])
    s.req(b'Q')


main()
