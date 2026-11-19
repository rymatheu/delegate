#!/usr/bin/env python3
"""The loiter stage's hand-checked case, worked out from the code in binary32, operation by
operation, and written as hand-checked-case.json (replayed by `harness replay`).

  python3 -I ardupilot/modules/loiter/hand-checked-case.py [--write]

Two steps with ArduCopter's default parameters (LOIT_ANG_MAX 0, LOIT_SPEED_MS 12.5,
LOIT_ACC_MAX_M 5, LOIT_BRK_ACC_M 2.5, LOIT_BRK_JRK_M 5, LOIT_BRK_DELAY 1, LOIT_OPTIONS 0;
ATC_RATE_FF_ENAB 1, ATC_RATE_R/P_MAX 0, ATC_ACC_R/P_MAX 1100, ATC_INPUT_TC 0.1, ATC_ANGLE_MAX 30,
ATC_ANG_RLL/PIT_P 4.5; PSC_NE_VEL_P 2), fixed order (every `_seq` 0):
  step 0 (now_ms 1000): init_target (ModeLoiter::init, mode_loiter.cpp:19)
  step 1 (now_ms 1002): set_pilot_desired_acceleration_rad(0.1, 0) then update(false)
                        (ModeLoiter::run, mode_loiter.cpp:90, 160)
Every binary32 operation is one double operation rounded to binary32 (F), the double ones (postype_t, the double
constants of AP_Math/definitions.h) in Python floats; sinf, cosf, tanf and fmodf are the C
library's (ctypes), the ones the module links. The expected outputs are printed with the line
of AC_Loiter.cpp, AC_AttitudeControl.cpp, AP_Math/control.cpp or AC_PosControl.cpp they come
from, then compared with the module's outputs for the same inputs.
"""
import ctypes
import json
import math
import os
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
libm = ctypes.CDLL(None)
for fn in ('sinf', 'cosf', 'tanf', 'sqrtf'):
    getattr(libm, fn).restype = ctypes.c_float
    getattr(libm, fn).argtypes = [ctypes.c_float]
libm.fmodf.restype = ctypes.c_float
libm.fmodf.argtypes = [ctypes.c_float, ctypes.c_float]



def F(x):
    """Round to binary32. One +, -, *, / or sqrt of two binary32 values done in double and
    rounded once to binary32 is the binary32 operation (double has more than 2 x 24 + 2 bits), so
    F(a op b) is the C++ float operation."""
    return struct.unpack('<f', struct.pack('<f', float(x)))[0]


def sinf(x): return F(libm.sinf(float(x)))
def cosf(x): return F(libm.cosf(float(x)))
def tanf(x): return F(libm.tanf(float(x)))
def sqrtf(x): return F(libm.sqrtf(float(x)))
def fmodf(x, y): return F(libm.fmodf(float(x), float(y)))
def bits(x): return '0x%08x' % struct.unpack('<I', struct.pack('<f', float(F(x))))[0]


FLT_EPSILON = F(1.1920928955078125e-07)
M_PI = 3.141592653589793238462643383279502884          # double (AP_Math/definitions.h:11)
DEG_TO_RAD = M_PI / 180.0                              # (M_PI / 180.0f): double (definitions.h:33)
GRAVITY_MSS = F(9.80665)                               # 9.80665f (definitions.h:45)


def radians_f(deg):            # AP_Math.h:232: float overload, deg * DEG_TO_RAD in double, to float
    return F(float(F(deg)) * DEG_TO_RAD)


def is_positive(x): return F(x) >= FLT_EPSILON         # AP_Math.h:68
def is_negative(x): return F(x) <= -FLT_EPSILON
def is_zero(x): return abs(F(x)) < FLT_EPSILON
def constrain(x, lo, hi): return lo if x < lo else (hi if x > hi else x)


def wrap_PI(r):                # AP_Math.cpp:251-277 (float)
    res = fmodf(r, F(M_PI * 2))
    if res < 0:
        res = F(res + F(M_PI * 2))
    if res > F(M_PI):
        res = F(res - F(M_PI * 2))
    return res


def lean_angles_to_accel(roll, pitch, yaw):   # AC_PosControl.cpp:1200-1215
    sr, cr, sp, cp, sy, cy = sinf(roll), cosf(roll), sinf(pitch), cosf(pitch), sinf(yaw), cosf(yaw)
    den = max(F(cr * cp), F(0.1))
    x = F(F(GRAVITY_MSS * F(F(F(-cy) * sp) * cr - F(sy * sr))) / den)
    y = F(F(GRAVITY_MSS * F(F(F(F(-sy) * sp) * cr) + F(cy * sr))) / den)
    return x, y


def sqrt_controller(error, p, lim, dt):        # control.cpp sqrt_controller
    if is_negative(lim) or is_zero(lim):
        rate = F(error * p)
    elif is_zero(p):
        raise SystemExit('not on this path')
    else:
        ld = F(lim / F(p * p))
        assert -ld <= error <= ld, 'the case stays in the linear region'
        rate = F(error * p)
    if is_positive(dt):
        b = F(abs(error) / dt)
        return constrain(rate, F(-b), b)
    return rate


def shape_pos_vel_accel(pos_d, vel_d, acc_d, pos, vel, acc, vmin, vmax, amin, amax, jerk, dt):
    # control.cpp shape_pos_vel_accel (limit_total true), with sqrt_controller_accel and
    # shape_accel; pos_d and pos are postype_t (double)
    assert not (is_positive(vmin) or is_negative(vmax) or not is_negative(amin) or
                not is_positive(amax) or not is_positive(jerk))
    pos_error = F(pos_d - pos)
    if is_positive(pos_error):
        accel_lim = F(-amin)
    else:
        accel_lim = amax
    k_v = F(jerk / accel_lim)
    vel_corr = F(vel - vel_d)
    vcc = sqrt_controller(pos_error, k_v, accel_lim, dt)
    # sqrt_controller_accel: rate_cmd * rate_state = vcc * 0 is not positive: 0
    assert not is_positive(F(vcc * vel_corr))
    acc_corr = F(0.0)
    vcc = F(vcc + F(acc_corr / k_v))
    assert not is_negative(vmin) and not is_positive(vmax)      # rate limits 0: none applied
    vel_target = F(vel_d + vcc)
    at = F(F(vel_target - vel) * k_v)
    at = constrain(at, amin, amax)
    at = F(at + acc_d)
    at = constrain(at, amin, amax)
    # shape_accel
    delta = F(at - acc)
    delta = constrain(delta, F(-F(jerk * dt)), F(jerk * dt))
    return F(acc + delta), dict(pos_error=pos_error, k_v=k_v, vel_corr_cmd=vcc, accel_target=at)


def attitude_command_model(err, vel, acc, max_vel, accel_max, input_tc, dt):
    # AC_AttitudeControl.cpp:1107-1129
    assert is_positive(dt) and is_positive(accel_max) and is_positive(input_tc)
    angle_desired_wrapped = F(F(0.0) + wrap_PI(F(err - F(0.0))))   # shape_angle_vel_accel
    jerk = F(accel_max / input_tc)
    acc, w = shape_pos_vel_accel(float(angle_desired_wrapped), F(0.0), F(0.0), 0.0, vel, acc,
                                 F(-max_vel), max_vel, F(-accel_max), accel_max, jerk, dt)
    vel = F(vel + F(acc * dt))
    return vel, acc, dict(w, jerk=jerk)


def main():
    write = '--write' in sys.argv
    lines = []

    def say(s):
        lines.append(s)
        print(s)

    # parameters
    P = dict(loit_ang_max=0.0, loit_speed_ms=12.5, loit_acc_max_m=5.0, loit_brk_acc_m=2.5,
             loit_brk_jrk_m=5.0, loit_brk_delay=1.0, loit_options=0, atc_rate_ff_enab=True,
             atc_rate_r_max=0.0, atc_rate_p_max=0.0, atc_acc_r_max=1100.0, atc_acc_p_max=1100.0,
             atc_input_tc=0.1, atc_angle_max=30.0, atc_ang_rll_p=4.5, atc_ang_pit_p=4.5,
             psc_ne_vel_p=2.0)
    dt = F(0.0025)
    att_lean = radians_f(30.0)          # lean_angle_max_rad, AC_AttitudeControl.cpp:1419-1422
    pc_lean = att_lean                  # the position stage's get_lean_angle_max_rad (PSC_ANGLE_MAX 0)
    base_in = dict(dt=dt, now_ms=1000, est_yaw=F(0), est_gnd_spd_limit=F(400),
                   pc_vel_desired_n=F(0), pc_vel_desired_e=F(0), pc_pos_desired_n=F(1),
                   pc_pos_desired_e=F(2), pc_accel_target_n=F(0.5), pc_accel_target_e=F(-0.25),
                   pc_roll=F(0.02), pc_pitch=F(-0.01), pc_stopping_point_n=F(3),
                   pc_stopping_point_e=F(4), pc_lean_angle_max=pc_lean,
                   ac_att_target_roll=F(0.05), ac_att_target_pitch=F(-0.04))

    # ---- step 0: init_target (AC_Loiter.cpp:136-154)
    say('step 0: init_target')
    speed_max = F(max(12.5, 0.2))                                  # :306 MAX(_speed_max, 0.2)
    g_tan = F(GRAVITY_MSS * tanf(att_lean))
    accel_max = min(F(5.0), g_tan)                                 # :309
    say('  sanity_check_params: speed %s; accel MIN(5, g tanf(%r) = %r) = %r' % (
        speed_max, float(att_lean), float(g_tan), float(accel_max)))
    pred_acc = (base_in['pc_accel_target_n'], base_in['pc_accel_target_e'])   # :148 (previous tick)
    pred_ang = (base_in['ac_att_target_roll'], base_in['ac_att_target_pitch'])  # :149-150 after relax
    pred_rate = (F(0), F(0))
    pred_aacc = (F(0), F(0))
    brake = F(0)
    angle_max = F(min(att_lean, pc_lean) * F(F(2.0) / F(3.0)))    # :239
    say('  NE_set_correction_speed_accel_m(2, %r), NE_set_pos_error_max_m(2), '
        'NE_relax_velocity_controller (:141-145)' % float(accel_max))
    say('  predicted accel = previous acceleration target %s; predicted angles = the attitude '
        'target (relax post-condition) %s' % ([float(x) for x in pred_acc], [float(x) for x in pred_ang]))
    say('  get_angle_max_rad = MIN(%r, %r) * (2/3f) = %r' % (float(att_lean), float(pc_lean),
                                                            float(angle_max)))
    out0 = dict(lt_tgt_ne_init_stopping_point=False, lt_tgt_ne_set_correction_speed_accel=True,
                lt_tgt_ne_correction_speed=F(2), lt_tgt_ne_correction_accel=accel_max,
                lt_tgt_handover_seq=0, lt_cmd_position_NE_set_pos_error_max_m=True,
                lt_cmd_position_NE_set_pos_error_max_m_error_max=F(2),
                lt_cmd_position_NE_set_pos_error_max_m_seq=0,
                lt_cmd_position_set_pos_desired_NE_m=False,
                lt_cmd_position_set_pos_desired_NE_m_n=F(0),
                lt_cmd_position_set_pos_desired_NE_m_e=F(0),
                lt_cmd_position_set_pos_desired_NE_m_seq=0,
                lt_cmd_position_NE_relax_velocity_controller=True,
                lt_cmd_position_NE_relax_velocity_controller_seq=0,
                lt_cmd_position_NE_soften_for_landing=False,
                lt_cmd_position_NE_soften_for_landing_seq=0, lt_tgt_valid=False,
                lt_tgt_ne_update=False, lt_tgt_update_seq=0, lt_tgt_pos_n=F(0), lt_tgt_pos_e=F(0),
                lt_tgt_vel_n=F(0), lt_tgt_vel_e=F(0), lt_tgt_acc_n=F(0), lt_tgt_acc_e=F(0),
                lt_angle_max=angle_max, lt_att_lean_angle_max=att_lean,
                lt_desired_accel_n=F(0), lt_desired_accel_e=F(0),
                lt_predicted_accel_n=pred_acc[0], lt_predicted_accel_e=pred_acc[1],
                lt_predicted_roll=pred_ang[0], lt_predicted_pitch=pred_ang[1],
                lt_predicted_roll_rate=F(0), lt_predicted_pitch_rate=F(0),
                lt_predicted_roll_accel=F(0), lt_predicted_pitch_accel=F(0), lt_brake_accel=brake,
                lt_brake_timer_ms=0, lt_speed_max=speed_max, lt_accel_max=accel_max,
                lt_stopping_point_n=F(3), lt_stopping_point_e=F(4), lt_update_ran=False,
                lt_update_last=False, lt_pilot_set=False, lt_pilot_before_update=False,
                lt_internal_errors=0)

    # ---- step 1: set_pilot_desired_acceleration_rad(0.1, 0) (AC_Loiter.cpp:174-209)
    say('step 1: set_pilot_desired_acceleration_rad(0.1, 0), update(false)')
    roll_in, pitch_in, yaw = F(0.1), F(0.0), F(0.0)
    des = lean_angles_to_accel(roll_in, pitch_in, yaw)             # :179-180
    say('  desired accel = lean_angles_rad_to_accel_NED_mss(0.1, 0, 0).xy = (%r, %r): '
        'g sinf(0.1)/cosf(0.1) east, -0 north' % (float(des[0]), float(des[1])))
    brake_timer = 1002                                             # :183-185, not zero
    err = (wrap_PI(F(roll_in - pred_ang[0])), wrap_PI(F(pitch_in - pred_ang[1])))   # :188
    say('  angle error = (%r, %r)' % (float(err[0]), float(err[1])))
    acc_max_r = radians_f(1100.0)                                  # get_accel_roll_max_radss
    rate_max = radians_f(0.0)                                      # ATC_RATE_R/P_MAX 0
    vx, ax, wx = attitude_command_model(wrap_PI(err[0]), pred_rate[0], pred_aacc[0], rate_max,
                                        acc_max_r, F(0.1), dt)
    vy, ay, wy = attitude_command_model(wrap_PI(err[1]), pred_rate[1], pred_aacc[1], rate_max,
                                        acc_max_r, F(0.1), dt)
    for nm, w, v, a in (('roll', wx, vx, ax), ('pitch', wy, vy, ay)):
        say('  command model %s (AC_AttitudeControl.cpp:1137-1138, 1107-1129): accel_max '
            'radians(1100) = %r, jerk accel_max/0.1 = %r, k_v = jerk/accel_max = %r; '
            'sqrt_controller linear (|error| %r < accel_max/k_v^2): rate %r; accel target %r; '
            'shape_accel limits the step to jerk dt = %r: accel %r; rate += accel dt = %r' % (
                nm, float(acc_max_r), float(w['jerk']), float(w['k_v']), float(w['pos_error']),
                float(w['vel_corr_cmd']), float(w['accel_target']), float(F(w['jerk'] * dt)),
                float(a), float(v)))
    # ang_vel_limit with zero limits: unchanged (AC_AttitudeControl.cpp ang_vel_limit)
    pred_rate = (vx, vy)
    pred_aacc = (ax, ay)
    pred_ang = (F(pred_ang[0] + F(vx * dt)), F(pred_ang[1] + F(vy * dt)))   # :194
    pred_acc = lean_angles_to_accel(pred_ang[0], pred_ang[1], yaw)          # :197-200
    say('  predicted angles += rate dt = (%r, %r); predicted accel = (%r, %r)' % (
        float(pred_ang[0]), float(pred_ang[1]), float(pred_acc[0]), float(pred_acc[1])))
    # ---- update(false): calc_desired_velocity (AC_Loiter.cpp:320-400)
    gnd = F(max(float(min(speed_max, F(400))), 0.2))              # :329-330
    pilot_acc_max = F(F(gnd / speed_max) * F(GRAVITY_MSS * tanf(angle_max)))   # :333
    vel = (F(F(0) + F(pred_acc[0] * dt)), F(F(0) + F(pred_acc[1] * dt)))       # :341-344
    speed = sqrtf(F(F(vel[0] * vel[0]) + F(vel[1] * vel[1])))                 # :347
    assert not is_zero(speed)
    norm = (F(vel[0] / speed), F(vel[1] / speed))
    drag = F(F(pilot_acc_max * speed) / gnd)                      # :352
    # :356: millis - brake_timer = 0 is not > MAX(1, dt) * 1000: no brake target
    brake = F(brake + constrain(F(F(0) - brake), F(-F(F(5) * dt)), F(F(5) * dt)))   # :362
    brake_vec = (F(norm[0] * brake), F(norm[1] * brake))
    speed2 = max(F(speed - F(F(drag + brake) * dt)), F(0))        # :366
    vel = (F(norm[0] * speed2), F(norm[1] * speed2))              # :367
    des = (F(des[0] - brake_vec[0]), F(des[1] - brake_vec[1]))    # :371
    assert sqrtf(F(F(vel[0] * vel[0]) + F(vel[1] * vel[1]))) <= gnd   # :374-377 no limit
    pos = (1.0 + float(F(vel[0] * dt)), 2.0 + float(F(vel[1] * dt)))   # :393-396, double
    say('  calc_desired_velocity: ground-speed limit MAX(MIN(12.5, 400), 0.2) = %r; pilot accel '
        'max = g tanf(%r) = %r; desired velocity = predicted accel dt = (%r, %r), speed %r; drag '
        '%r m/s/s; brake 0 (stick moved this tick, brake delay 1 s); speed after drag %r; '
        'velocity (%r, %r); position (1, 2) + v dt = (%r, %r) (double), handed as binary32' % (
            float(gnd), float(angle_max), float(pilot_acc_max), float(F(pred_acc[0] * dt)),
            float(F(pred_acc[1] * dt)), float(speed), float(drag), float(speed2), float(vel[0]),
            float(vel[1]), pos[0], pos[1]))
    in1 = dict(base_in, now_ms=1002)
    out1 = dict(out0, lt_tgt_ne_set_correction_speed_accel=False, lt_tgt_ne_correction_speed=F(0),
                lt_tgt_ne_correction_accel=F(0), lt_cmd_position_NE_set_pos_error_max_m=False,
                lt_cmd_position_NE_set_pos_error_max_m_error_max=F(0),
                lt_cmd_position_NE_relax_velocity_controller=False, lt_tgt_valid=True,
                lt_tgt_ne_update=True, lt_tgt_pos_n=F(pos[0]), lt_tgt_pos_e=F(pos[1]),
                lt_tgt_vel_n=vel[0], lt_tgt_vel_e=vel[1], lt_tgt_acc_n=des[0],
                lt_tgt_acc_e=des[1], lt_desired_accel_n=des[0], lt_desired_accel_e=des[1],
                lt_predicted_accel_n=pred_acc[0], lt_predicted_accel_e=pred_acc[1],
                lt_predicted_roll=pred_ang[0], lt_predicted_pitch=pred_ang[1],
                lt_predicted_roll_rate=vx, lt_predicted_pitch_rate=vy,
                lt_predicted_roll_accel=ax, lt_predicted_pitch_accel=ay, lt_brake_accel=brake,
                lt_brake_timer_ms=brake_timer, lt_update_ran=True, lt_update_last=True,
                lt_pilot_set=True, lt_pilot_before_update=True)

    # the schema, from the module's describe (the build's records)
    desc = subprocess.run([os.path.join(HARNESS, '.lake', 'build', 'bin', 'harness'), 'describe',
                           'loiter'], cwd=HARNESS, capture_output=True, text=True).stdout
    schema = {}
    for ln in desc.splitlines():
        for port in ('params', 'input', 'output'):
            if ln.startswith(port + ' '):
                schema[port] = [x.strip().split(': ') for x in ln[len(port):].strip().split(', ')]

    def word(t, v):
        if t == 'bool':
            return 'true' if v else 'false'
        if t == 'f32':
            return bits(v)
        return str(int(v))

    def rec(port, vals, default_off=True):
        r = {}
        for n, t in schema[port]:
            if n in vals:
                r[n] = word(t, vals[n])
            elif default_off:
                r[n] = word(t, 0)
            else:
                raise SystemExit('no value for %s' % n)
        return r

    cmd0 = dict(cmd_loiter_init_target=True)
    cmd1 = dict(cmd_loiter_set_pilot_desired_acceleration_rad=True,
                cmd_loiter_set_pilot_desired_acceleration_rad_roll=roll_in,
                cmd_loiter_set_pilot_desired_acceleration_rad_pitch=pitch_in,
                cmd_loiter_update=True)
    case = {
        'module': 'loiter', 'code_hash': '(computed by hand)', 'campaign': 'none',
        'kind': 'hand-checked', 'clause': '', 'case': 0, 'step': 1,
        'note': 'Expected outputs worked out from AC_Loiter.cpp, AC_AttitudeControl.cpp '
                '(command_model_rate_predictor), AP_Math/control.cpp and AC_PosControl.cpp '
                '(lean_angles_rad_to_accel_NED_mss) in binary32, operation by operation (the '
                'working: ardupilot/modules/loiter/hand-checked-case.py, which prints it and '
                'writes this file; libm sinf/cosf/tanf/fmodf through ctypes). ' + ' '.join(lines),
        'params': rec('params', P, default_off=False),
        'inputs': [rec('input', dict(base_in, **cmd0)), rec('input', dict(in1, **cmd1))],
        'outputs': [rec('output', out0, default_off=False), rec('output', out1, default_off=False)]}

    # compare with the module: `harness replay` of the case written to a temporary file
    tmp = os.path.join(HERE, '.hand-checked-case.tmp.json')
    json.dump(case, open(tmp, 'w'), indent=2)
    r = subprocess.run([os.path.join(HARNESS, '.lake', 'build', 'bin', 'harness'), 'replay', tmp],
                       cwd=HARNESS, capture_output=True, text=True)
    print(r.stdout.strip() or r.stderr.strip())
    os.remove(tmp)
    if write and 'bit-identical' in r.stdout:
        path = os.path.join(HERE, 'hand-checked-case.json')
        json.dump(case, open(path, 'w'), indent=2)
        open(path, 'a').write('\n')
        print('written', path)


main()
