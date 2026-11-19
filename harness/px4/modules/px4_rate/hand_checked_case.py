#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_rate: three gyro ticks at 400 Hz worked out from
MulticopterRateControl::Run and RateControl::update / updateIntegral (rate_control.cpp:69-118),
every operation rounded to binary32 in the order the C++ performs it (f() below).

Parameters: PX4's defaults, except roll P = 0.5, I = 0.25, D = 0.0625 (K = 1, FF = 0 by default).
Step 0 (t = 1 s): vehicle_control_mode (armed, rates enabled), vehicle_status (rotary wing),
  vehicle_rates_setpoint roll 1 rad/s, thrust (0, 0, -0.5), gyro x = 0.5 rad/s, x-accel 2 rad/s^2.
  _landed starts true (MulticopterRateControl.hpp:115), so the integrator is frozen:
  torque_x = 0.5*(1-0.5) + 0 - 0.0625*2 + 0*1 = 0.125, exactly.
Step 1 (t = 1.0025 s): gyro x = 0.5, accel 0; vehicle_land_detected: not landed, not maybe landed.
  torque_x = 0.5*0.5 = 0.25 (the integrator is added before it is updated);
  dt = 2500 * 1e-6f; i_factor = 1 - (0.5 / radians(400))^2; I1 = 0 + i_factor*0.25*0.5*dt.
Step 2 (t = 1.005 s): the same gyro; torque_x = 0.25 + I1, I2 = I1 + i_factor*0.25*0.5*dt.
The yaw output filter sees 0 and stays 0; pitch and yaw torque 0. The thrust published is the rate
setpoint's (0, 0, -0.5). actuator_controls_status is published after 0.5 s only.
"""
import json, os, re, struct, math

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))


def f(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


def hx(x):
    return '0x%08x' % struct.unpack('<I', struct.pack('<f', x))[0]


def schema(label):
    txt = open(os.path.join(HERE, 'Ports.lean')).read()
    # the schema's rows, in either layout of px4/ports.py (one array, or chunks joined by ++)
    block = re.search(rf'def {label} : Schema :=(.*?)(?:\n(?:def |/--|end |set_option)|\Z)', txt,
                      re.S).group(1)
    return re.findall(r'name := "([^"]+)", type := \.(\w+)', block)


params_json = json.load(open(os.path.join(HARNESS, 'build/gen/px4_rate/parameters/parameters.json')))
defaults = {p['name']: p['default'] for p in params_json['parameters']}
defaults.update({'MC_ROLLRATE_P': 0.5, 'MC_ROLLRATE_I': 0.25, 'MC_ROLLRATE_D': 0.0625})


def word(t, v):
    if t == 'f32':
        return hx(v)
    if t == 'bool':
        return 'true' if v else 'false'
    return str(int(v))


P = {n: word(t, defaults[n]) for n, t in schema('params')}

# binary32 arithmetic of the code
radians400 = f(f(400.0) * f(f(math.pi) / f(180.0)))     # math::radians(400.f)
dt = f(f(2500.0) * f(1e-6))
err = f(f(1.0) - f(0.5))
i_factor = f(err / radians400)
i_factor = max(0.0, f(f(1.0) - f(i_factor * i_factor)))
inc = f(f(f(i_factor * f(0.25)) * err) * dt)
I1 = f(f(0.0) + inc)
I2 = f(I1 + inc)
assert f(f(0.5) * err) == 0.25 and f(f(f(f(0.5) * err) + 0.0) - f(f(0.0625) * f(2.0))) == 0.125

steps = [
    dict(t=1000000, land=None, accel=2.0, rsp=True, torque=0.125, integ=0.0),
    dict(t=1002500, land=False, accel=0.0, rsp=False, torque=f(f(f(0.5 * err) + 0.0) - 0.0), integ=I1),
    dict(t=1005000, land=None, accel=0.0, rsp=False, torque=f(f(f(0.5 * err) + I1) - 0.0), integ=I2),
]
inputs, outputs = [], []
for k, s in enumerate(steps):
    v = {n: (0.0 if t == 'f32' else (False if t == 'bool' else 0)) for n, t in schema('input')}
    v['t_us'] = s['t']
    v.update({'vehicle_angular_velocity_updated': True, 'vehicle_angular_velocity_timestamp': s['t'],
              'vehicle_angular_velocity_timestamp_sample': s['t'], 'vehicle_angular_velocity_xyz_0': 0.5,
              'vehicle_angular_velocity_xyz_derivative_0': s['accel']})
    if k == 0:
        v.update({'vehicle_control_mode_updated': True, 'vehicle_control_mode_timestamp': s['t'],
                  'vehicle_control_mode_flag_armed': True,
                  'vehicle_control_mode_flag_control_rates_enabled': True,
                  'vehicle_status_updated': True, 'vehicle_status_timestamp': s['t'],
                  'vehicle_status_vehicle_type': 1})
    if s['rsp']:
        v.update({'vehicle_rates_setpoint_updated': True, 'vehicle_rates_setpoint_timestamp': s['t'],
                  'vehicle_rates_setpoint_roll': 1.0, 'vehicle_rates_setpoint_thrust_body_2': -0.5})
    if s['land'] is not None:
        v.update({'vehicle_land_detected_updated': True, 'vehicle_land_detected_timestamp': s['t'],
                  'vehicle_land_detected_landed': s['land'], 'vehicle_land_detected_maybe_landed': s['land']})
    inputs.append({n: word(t, v[n]) for n, t in schema('input')})
    o = {n: (0.0 if t == 'f32' else (False if t == 'bool' else 0)) for n, t in schema('output')}
    o.update({'vehicle_torque_setpoint_updated': True, 'vehicle_torque_setpoint_timestamp': s['t'],
              'vehicle_torque_setpoint_timestamp_sample': s['t'], 'vehicle_torque_setpoint_xyz_0': s['torque'],
              'vehicle_thrust_setpoint_updated': True, 'vehicle_thrust_setpoint_timestamp': s['t'],
              'vehicle_thrust_setpoint_timestamp_sample': s['t'], 'vehicle_thrust_setpoint_xyz_2': -0.5,
              'rate_ctrl_status_updated': True, 'rate_ctrl_status_timestamp': s['t'],
              'rate_ctrl_status_rollspeed_integ': s['integ']})
    outputs.append({n: word(t, o[n]) for n, t in schema('output')})

case = {"module": "px4_rate", "code_hash": "(computed by hand)", "campaign": "none",
        "kind": "hand-checked", "clause": "", "case": 0, "step": 2,
        "note": __doc__.strip().replace('\n', ' '),
        "params": P, "inputs": inputs, "outputs": outputs}
json.dump(case, open(os.path.join(HERE, 'hand-checked-case.json'), 'w'), indent=2)
print('torque', [s['torque'] for s in steps], 'integrator', I1, I2)
