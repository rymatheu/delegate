#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_pos: two local position ticks worked out from
MulticopterPositionControl::Run (MulticopterPositionControl.cpp:376-623), PositionControl
(PositionControl.cpp) and ControlMath (ControlMath.cpp), PX4's default parameters except
COM_THROW_EN = 1 (takeoff skipped: armed means TakeoffState::flight, Takeoff.cpp:104-106).

Inputs at both ticks: a valid estimate at rest at the origin (heading 0, vxy_max = inf); control
mode armed with multicopter position control, stamped 1 s; airborne land detector; a trajectory
setpoint of zero velocity only (position, acceleration, yaw, yawspeed NaN), stamped 1 s.
Step 0 (t = 1 s): dt = constrain((1 s - 0) * 1e-6, 0.002, 0.04) = 0.04. Velocity error 0, integral
  0, derivative 0, so acc_sp = 0 (:161); body_z = (-0, -0, g) normalized = (0, 0, 1), no tilt;
  thrust_ned_z = 0 * (0.5 / g) - 0.5 = -0.5; collective = min(-0.5 / 1, -max(MPC_THR_MIN 0.12,
  1e-3)) = -0.5; thr_sp = (-0, -0, -0.5), inside every saturation. bodyzToAttitude((0, 0, 0.5),
  yaw = heading 0) is the identity; thrust_body[2] = -|thr_sp| = -0.5; yawspeed NaN -> 0 (:146).
  Local position setpoint: position NaN, velocity 0, acceleration 0, thrust (-0, -0, -0.5), yaw 0.
  Takeoff status: state 5 (flight), tilt limit slewed from 0 at 0.2 rad/s: 0.2f * 0.04f = 0.008.
Step 1 (t = 1.0025 s): dt = 0.0025; the same setpoints; tilt limit 0.008 + 0.2f * 0.0025f, which
  changed, so takeoff_status is published again.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'px4_common'))
from hand_case import f, write

HERE = os.path.dirname(os.path.abspath(__file__))
NAN, INF = float('nan'), float('inf')
tilt0 = f(f(0.2) * f(0.04))
tilt1 = f(tilt0 + f(f(0.2) * f(f(2500.0) * f(1e-6))))


def inp(t):
    d = {'t_us': t, 'vehicle_local_position_updated': True, 'vehicle_local_position_timestamp': t,
         'vehicle_local_position_timestamp_sample': t, 'vehicle_local_position_vxy_max': INF,
         'vehicle_control_mode_updated': True, 'vehicle_control_mode_timestamp': 1000000,
         'vehicle_control_mode_flag_armed': True,
         'vehicle_control_mode_flag_multicopter_position_control_enabled': True,
         'vehicle_land_detected_updated': True, 'vehicle_land_detected_timestamp': t,
         'trajectory_setpoint_updated': True, 'trajectory_setpoint_timestamp': 1000000,
         'trajectory_setpoint_yaw': NAN, 'trajectory_setpoint_yawspeed': NAN}
    for v in ('xy_valid', 'z_valid', 'v_xy_valid', 'v_z_valid', 'heading_good_for_control'):
        d[f'vehicle_local_position_{v}'] = True
    for i in range(3):
        d[f'trajectory_setpoint_position_{i}'] = NAN
        d[f'trajectory_setpoint_acceleration_{i}'] = NAN
    return d


def out(t, tilt):
    return {'vehicle_attitude_setpoint_updated': True, 'vehicle_attitude_setpoint_timestamp': t,
            'vehicle_attitude_setpoint_q_d_0': 1.0, 'vehicle_attitude_setpoint_thrust_body_2': -0.5,
            'vehicle_local_position_setpoint_updated': True,
            'vehicle_local_position_setpoint_timestamp': t,
            'vehicle_local_position_setpoint_x': NAN, 'vehicle_local_position_setpoint_y': NAN,
            'vehicle_local_position_setpoint_z': NAN,
            'vehicle_local_position_setpoint_thrust_0': -0.0,
            'vehicle_local_position_setpoint_thrust_1': -0.0,
            'vehicle_local_position_setpoint_thrust_2': -0.5,
            'takeoff_status_updated': True, 'takeoff_status_timestamp': t,
            'takeoff_status_takeoff_state': 5, 'takeoff_status_tilt_limit': tilt}


write('px4_pos', __doc__, {'COM_THROW_EN': 1}, [inp(1000000), inp(1002500)],
      [out(1000000, tilt0), out(1002500, tilt1)], os.path.join(HERE, 'hand-checked-case.json'))
print('tilt', tilt0, tilt1)
