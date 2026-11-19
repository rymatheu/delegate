#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_fmm: three local position ticks worked out from
FlightModeManager::Run / start_flight_task / generateTrajectorySetpoint (FlightModeManager.cpp:
75-372) and FlightTaskDescend (FlightTaskDescend.cpp:40-80), PX4's default parameters.

Inputs: armed in Descend (nav state 12) with commander's flags for it (auto, climb rate,
attitude, rates, allocation; control_mode.cpp:102-108), a valid estimate (vz 0.1 m/s, heading
0.25 rad), takeoff status flight (5).
Step 0 (t = 1 s): the first local position runs the module (interval 20 ms, :66); nav state 12
  starts Descend (:236-241). FlightTask::activate resets every setpoint to NaN; Descend::update:
  vz is finite, so velocity z = MPC_LAND_SPEED = 0.7 and acceleration z NaN; no stick nudging
  (MPC_LAND_RC_HELP 0), so acceleration xy = 0, yawspeed NaN, yaw = heading 0.25. Constraints:
  MPC_Z_VEL_MAX_UP 3, MPC_Z_VEL_MAX_DN 1.5, no takeoff (FlightTask.cpp:210-214). The gear is
  GEAR_DOWN (-1), which differs from the initial GEAR_KEEP, so landing_gear is published.
Step 1 (t = 1.0025 s): SubscriptionInterval keeps the average rate, not the spacing: after the
  run at 1 s its last update is constrain(0 + 20 ms, 1 s - 20 ms, 1 s) = 0.98 s
  (SubscriptionInterval.cpp:62-66), so 22.5 ms have elapsed and the module runs again: the same
  setpoint and constraints, stamped 1.0025 s; the gear is unchanged, so landing_gear is not
  published (its output keeps the last message, flag false). The last update becomes
  constrain(0.98 s + 20 ms, 0.9825 s, 1.0025 s) = 1 s.
Step 2 (t = 1.005 s): 5 ms since 1 s, inside the interval: the module does not run; nothing is
  published (the outputs keep the last messages, flags false).
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'px4_common'))
from hand_case import write

HERE = os.path.dirname(os.path.abspath(__file__))
NAN = float('nan')


def inp(t):
    d = {'t_us': t, 'vehicle_local_position_updated': True, 'vehicle_local_position_timestamp': t,
         'vehicle_local_position_timestamp_sample': t, 'vehicle_local_position_vz': 0.1,
         'vehicle_local_position_heading': 0.25,
         'vehicle_control_mode_updated': True, 'vehicle_control_mode_timestamp': t,
         'vehicle_status_updated': True, 'vehicle_status_timestamp': t,
         'vehicle_status_vehicle_type': 1, 'vehicle_status_arming_state': 2,
         'vehicle_status_nav_state': 12,
         'takeoff_status_updated': True, 'takeoff_status_timestamp': t,
         'takeoff_status_takeoff_state': 5}
    for v in ('xy_valid', 'z_valid', 'v_xy_valid', 'v_z_valid', 'heading_good_for_control'):
        d[f'vehicle_local_position_{v}'] = True
    for fl in ('armed', 'control_auto_enabled', 'control_climb_rate_enabled',
               'control_attitude_enabled', 'control_rates_enabled', 'control_allocation_enabled',
               'multicopter_position_control_enabled'):
        d[f'vehicle_control_mode_flag_{fl}'] = True
    return d


def out(t, sp_fresh, gear_fresh):
    d = {'trajectory_setpoint_updated': sp_fresh, 'trajectory_setpoint_timestamp': t,
         'trajectory_setpoint_velocity_2': 0.7, 'trajectory_setpoint_yaw': 0.25,
         'trajectory_setpoint_yawspeed': NAN,
         'vehicle_constraints_updated': sp_fresh, 'vehicle_constraints_timestamp': t,
         'vehicle_constraints_speed_up': 3.0, 'vehicle_constraints_speed_down': 1.5,
         'landing_gear_updated': gear_fresh, 'landing_gear_timestamp': 1000000,
         'landing_gear_landing_gear': -1}
    for i in range(3):
        d[f'trajectory_setpoint_position_{i}'] = NAN
        d[f'trajectory_setpoint_jerk_{i}'] = NAN
    for i in range(2):
        d[f'trajectory_setpoint_velocity_{i}'] = NAN
    d['trajectory_setpoint_acceleration_2'] = NAN
    return d


write('px4_fmm', __doc__, {}, [inp(1000000), inp(1002500), inp(1005000)],
      [out(1000000, True, True), out(1002500, True, False), out(1002500, False, False)],
      os.path.join(HERE, 'hand-checked-case.json'))
