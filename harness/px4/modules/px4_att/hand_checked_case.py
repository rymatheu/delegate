#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_att: three attitude ticks at 400 Hz worked out from
MulticopterAttitudeControl::Run (mc_att_control_main.cpp:233-425) and AttitudeControl::update
(AttitudeControl.cpp:56-113), PX4's default parameters (MC_ROLL_P 4, MC_ROLLRATE_MAX 220,
MC_YAW_WEIGHT 0.4). The attitude is the identity quaternion at every tick.

Step 0 (t = 1 s): control mode armed, rates enabled, attitude NOT enabled; status rotary wing.
  run_att_ctrl is false (:291-292): nothing is published.
Step 1 (t = 1.0025 s): control mode with attitude enabled; attitude setpoint q_d = identity,
  thrust (0, 0, -0.6), yaw_sp_move_rate 0.5, stamped 1.0025 s (newer than 0: accepted, :318-329).
  e_z = e_z_d = (0, 0, 1): Quatf(e_z, e_z_d) has cross 0 and dot 1, so q0 = 1 + sqrt(1) = 2 and
  normalizes to the identity; qd_dyaw = identity, acos(1) = 0, so qd = identity; qe = identity, the
  attitude error eq = 0 and the rate setpoint is the yaw feed-forward q^-1.dcm_z * 0.5 =
  (0, 0, 0.5), inside the limits. The thrust is the setpoint's.
Step 2 (t = 1.005 s): setpoint q_d = (0, 1, 0, 0), a 180° roll, yaw_sp_move_rate NaN (no
  feed-forward). e_z_d = (0, 0, -1) is opposite to e_z: the corner case of Quatf(src, dst)
  (Quaternion.hpp:203-228) gives (0, -1, 0, 0), |qd_red(1)| > 1 - 1e-5, so qd_red = qd
  (AttitudeControl.cpp:66-71); qd_dyaw = qd_red^-1 qd = identity, so qd = (0, 1, 0, 0);
  qe = (0, 1, 0, 0), eq = 2 * (1, 0, 0), roll rate 2 * MC_ROLL_P = 8 rad/s, constrained to
  radians(220) = 220f * 0.0174532924f = 3.8397243 rad/s; pitch and yaw 0.
Signed zeros: the zero rate components are written +0; the replay confirms them bit for bit.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'px4_common'))
from hand_case import f, write

HERE = os.path.dirname(os.path.abspath(__file__))
NAN = float('nan')
limit = f(f(220.0) * f(0.0174532924))
assert f(8.0) > limit

common = lambda t: {'t_us': t, 'vehicle_attitude_updated': True, 'vehicle_attitude_timestamp': t,
                    'vehicle_attitude_timestamp_sample': t, 'vehicle_attitude_q_0': 1.0,
                    'vehicle_attitude_delta_q_reset_0': 1.0}
s0 = common(1000000)
s0.update({'vehicle_control_mode_updated': True, 'vehicle_control_mode_timestamp': 1000000,
           'vehicle_control_mode_flag_armed': True, 'vehicle_control_mode_flag_control_rates_enabled': True,
           'vehicle_status_updated': True, 'vehicle_status_timestamp': 1000000,
           'vehicle_status_vehicle_type': 1, 'vehicle_status_arming_state': 2})
s1 = common(1002500)
s1.update({'vehicle_control_mode_updated': True, 'vehicle_control_mode_timestamp': 1002500,
           'vehicle_control_mode_flag_armed': True, 'vehicle_control_mode_flag_control_rates_enabled': True,
           'vehicle_control_mode_flag_control_attitude_enabled': True,
           'vehicle_attitude_setpoint_updated': True, 'vehicle_attitude_setpoint_timestamp': 1002500,
           'vehicle_attitude_setpoint_q_d_0': 1.0, 'vehicle_attitude_setpoint_thrust_body_2': -0.6,
           'vehicle_attitude_setpoint_yaw_sp_move_rate': 0.5})
s2 = common(1005000)
s2.update({'vehicle_attitude_setpoint_updated': True, 'vehicle_attitude_setpoint_timestamp': 1005000,
           'vehicle_attitude_setpoint_q_d_1': 1.0, 'vehicle_attitude_setpoint_thrust_body_2': -0.6,
           'vehicle_attitude_setpoint_yaw_sp_move_rate': NAN})
o0 = {}
o1 = {'vehicle_rates_setpoint_updated': True, 'vehicle_rates_setpoint_timestamp': 1002500,
      'vehicle_rates_setpoint_yaw': 0.5, 'vehicle_rates_setpoint_thrust_body_2': -0.6}
o2 = {'vehicle_rates_setpoint_updated': True, 'vehicle_rates_setpoint_timestamp': 1005000,
      'vehicle_rates_setpoint_roll': limit, 'vehicle_rates_setpoint_thrust_body_2': -0.6}
write('px4_att', __doc__, {}, [s0, s1, s2], [o0, o1, o2], os.path.join(HERE, 'hand-checked-case.json'))
print('roll limit', limit)
