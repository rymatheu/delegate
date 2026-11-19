#!/usr/bin/env python3
"""Hand-checked case of px4_commander: a healthy X500 on the ground (SITL parameters), an arm
command and a mode change, ticks worked out from Commander.cpp.

Schedule of the commander task. At init it runs one pass at t = 0 and sleeps 10 ms
(Commander.cpp:1979, COMMANDER_MONITORING_INTERVAL); a pass runs at the first step whose t_us is
past the deadline: step 0 (t = 1 s), then every 4th step (t = 1.01 s, 1.02 s, ...), since each pass
ends in a 10 ms sleep when no command is waiting (:1977-1980).
Step 0 (t = 1 s): pass; the 2 Hz rule (now >= vehicle_status.timestamp + 500 ms, :1932) publishes
  actuator_armed, vehicle_control_mode and vehicle_status: disarmed (arming_state 1), nav_state 4
  AUTO_LOITER (the initial user intention, UserModeIntention.hpp:100, kept without RC).
Step 2 (t = 1.005 s): COMPONENT_ARM_DISARM (400, param1 1) from the GCS (255/190). Commander sleeps.
Step 4 (t = 1.01 s): pass; the command is read (:1888-1898), Commander::arm runs the arming checks
  (:610) and sets arming_state ARMED (:622); handle_command returns true, so _status_changed and
  the block at :1932-1946 publishes actuator_armed.armed = true (:1918), vehicle_control_mode with
  flag_armed, vehicle_status with arming_state 2, all stamped 1010000; the ACCEPTED (0) ack goes to
  255/190 (answer_command, :1553). Steps 5-7: no pass, nothing published.
Step 9 (t = 1.0225 s): DO_SET_MODE (176, param1 1 = custom mode, param2 4 = AUTO, param3 2 =
  TAKEOFF). Step 12 (t = 1.03 s): pass; DO_SET_MODE (:800-930) maps it to AUTO_TAKEOFF (17) and
  _user_mode_intention.change accepts it (:915): ACCEPTED ack, status published (still nav_state 4:
  the published nav state is set in handleModeIntentionAndFailsafe, which ran before the command,
  :1866 and :2369-2373). Step 16 (t = 1.04 s): pass; handleModeIntentionAndFailsafe sets
  nav_state = nav_state_user_intention = 17 and nav_state_timestamp = 1040000, nav_state changed:
  status published; control mode for 17 = auto, position, velocity, altitude, climb rate,
  attitude, rates, allocation (control_mode.cpp, the AUTO group), as for 4, and
  multicopter_position_control on (rotary wing).
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'py'))
import px4_case  # noqa: E402

IMU, MAG, BARO, GPS = 1310988, 197388, 6620172, 11141384
LAT, LON, ALT = 47.397742, 8.545594, 488.0
SITL = {'CAL_ACC0_ID': IMU, 'CAL_GYRO0_ID': IMU, 'CAL_MAG0_ID': MAG, 'CAL_MAG0_PRIO': 50,
        'COM_CPU_MAX': -1.0, 'COM_RAM_MAX': -1.0, 'COM_RC_IN_MODE': 1, 'SYS_FAILURE_EN': 1,
        'COM_LOW_BAT_ACT': 3, 'MAV_TYPE': 2, 'NAV_DLL_ACT': 2, 'COM_MODE_ARM_CHK': 1, 'SDLOG_MODE': 1}
def T(k): return 1000000 + 2500 * k
def topic(prefix, t, **f):
    d = {f'{prefix}_updated': True, f'{prefix}_timestamp': t}
    d.update({f'{prefix}_{a}': b for a, b in f.items()})
    return d
def queued(prefix, t, **f):
    d = {f'{prefix}_count': 1, f'{prefix}_timestamp': t}
    d.update({f'{prefix}_{a}': b for a, b in f.items()})
    return d
def healthy(k):
    t = T(k)
    d = {'t_us': t}
    d.update(queued('sensor_accel', t, timestamp_sample=t, device_id=IMU, z=-9.80665, temperature=25.0, samples=1))
    d.update(queued('sensor_gyro', t, timestamp_sample=t, device_id=IMU, temperature=25.0, samples=1))
    d.update(queued('sensor_mag', t, timestamp_sample=t, device_id=MAG, x=0.21, y=0.0, z=0.43, temperature=25.0))
    d.update(queued('sensor_baro', t, timestamp_sample=t, device_id=BARO, pressure=95500.0, temperature=25.0))
    d.update(topic('sensor_selection', t, accel_device_id=IMU, gyro_device_id=IMU))
    d.update(topic('sensors_status_imu', t, accel_device_id_primary=IMU, accel_device_ids_0=IMU, accel_healthy_0=True,
                   accel_priority_0=50, gyro_device_id_primary=IMU, gyro_device_ids_0=IMU, gyro_healthy_0=True,
                   gyro_priority_0=50))
    d.update(topic('vehicle_imu_status', t, accel_device_id=IMU, gyro_device_id=IMU, accel_rate_hz=250.0,
                   gyro_rate_hz=250.0, accel_raw_rate_hz=250.0, gyro_raw_rate_hz=250.0, mean_accel_2=-9.80665,
                   temperature_accel=25.0, temperature_gyro=25.0))
    d.update(topic('vehicle_air_data', t, timestamp_sample=t, baro_device_id=BARO, baro_alt_meter=ALT,
                   baro_pressure_pa=95500.0, ambient_temperature=25.0, rho=1.15))
    d.update(topic('vehicle_attitude', t, timestamp_sample=t, q_0=1.0))
    d.update(topic('vehicle_angular_velocity', t, timestamp_sample=t))
    d.update(topic('vehicle_acceleration', t, timestamp_sample=t, xyz_2=-9.80665))
    d.update(topic('vehicle_local_position', t, timestamp_sample=t, xy_valid=True, z_valid=True, v_xy_valid=True,
                   v_z_valid=True, heading_good_for_control=True, xy_global=True, z_global=True, ref_timestamp=t,
                   ref_lat=LAT, ref_lon=LON, ref_alt=ALT, eph=0.5, epv=0.5, evh=0.1, evv=0.1,
                   vxy_max=float('inf'), vz_max=float('inf'), hagl_min=float('inf'), hagl_max_z=float('inf'),
                   hagl_max_xy=float('inf')))
    d.update(topic('vehicle_global_position', t, timestamp_sample=t, lat=LAT, lon=LON, alt=ALT, alt_ellipsoid=ALT,
                   lat_lon_valid=True, alt_valid=True, eph=0.5, epv=0.5))
    d.update(topic('vehicle_gps_position', t, timestamp_sample=t, device_id=GPS, latitude_deg=LAT, longitude_deg=LON,
                   altitude_msl_m=ALT, altitude_ellipsoid_m=ALT, s_variance_m_s=0.2, fix_type=3, eph=0.5, epv=0.8,
                   hdop=0.7, vdop=0.9, vel_ned_valid=True, satellites_used=10, heading=float('nan'),
                   heading_offset=float('nan'), heading_accuracy=float('nan')))
    d.update(topic('estimator_status', t, timestamp_sample=t, pos_horiz_accuracy=0.5, pos_vert_accuracy=0.5,
                   hdg_test_ratio=0.1, vel_test_ratio=0.1, pos_test_ratio=0.1, hgt_test_ratio=0.1,
                   accel_device_id=IMU, gyro_device_id=IMU, baro_device_id=BARO, mag_device_id=MAG,
                   mag_strength_gs=0.48, mag_strength_ref_gs=0.48, mag_inclination_deg=63.0, mag_inclination_ref_deg=63.0))
    d.update(topic('estimator_status_flags', t, timestamp_sample=t, cs_tilt_align=True, cs_yaw_align=True,
                   cs_gnss_pos=True, cs_mag_hdg=False, cs_mag_3d=True, cs_baro_hgt=True, cs_vehicle_at_rest=True,
                   cs_gnss_vel=True, cs_mag=True))
    d.update(topic('estimator_selector_status', t, primary_instance=0, instances_available=1, accel_device_id=IMU,
                   baro_device_id=BARO, gyro_device_id=IMU, mag_device_id=MAG, healthy_0=True))
    d.update(topic('estimator_sensor_bias', t, timestamp_sample=t, gyro_device_id=IMU, accel_device_id=IMU,
                   mag_device_id=MAG))
    d.update(topic('vehicle_land_detected', t, ground_contact=True, maybe_landed=True, landed=True, at_rest=True))
    d.update(topic('battery_status', t, connected=True, voltage_v=16.2, current_a=1.0, current_average_a=1.0,
                   remaining=0.9, scale=1.0, time_remaining_s=float('nan'), temperature=float('nan'), cell_count=4,
                   capacity=5000, state_of_health=100, id=1, voltage_cell_v_0=4.05, voltage_cell_v_1=4.05,
                   voltage_cell_v_2=4.05, voltage_cell_v_3=4.05, full_charge_capacity_wh=float('nan'),
                   remaining_capacity_wh=float('nan'), nominal_voltage=14.8))
    d.update(topic('system_power', t, voltage5v_v=5.0, brick_valid=1, usb_valid=0, servo_valid=1))
    d.update(topic('cpuload', t, load=0.2, ram_usage=0.3))
    d.update(topic('telemetry_status', t, type=1, mode=0, mavlink_v2=True, heartbeat_type_gcs=True))
    return d


def cmd(k, c, p1=0.0, p2=0.0, p3=0.0):
    return {'vehicle_command_count': 1, 'vehicle_command_timestamp': T(k), 'vehicle_command_command': c,
            'vehicle_command_param1': p1, 'vehicle_command_param2': p2, 'vehicle_command_param3': p3,
            'vehicle_command_target_system': 1, 'vehicle_command_target_component': 1,
            'vehicle_command_source_system': 255, 'vehicle_command_source_component': 190,
            'vehicle_command_from_external': True}


steps = [healthy(k) for k in range(20)]
steps[2].update(cmd(2, 400, 1.0))
steps[9].update(cmd(9, 176, 1.0, 4.0, 2.0))
params = px4_case.defaults('px4_commander')
params.update(SITL)

AUTO = {f'vehicle_control_mode_flag_control_{f}_enabled': True for f in
        ['auto', 'position', 'velocity', 'altitude', 'climb_rate', 'attitude', 'rates', 'allocation']}
AUTO.update({f'vehicle_control_mode_flag_control_{f}_enabled': False for f in
             ['manual', 'offboard', 'acceleration', 'termination']})
AUTO['vehicle_control_mode_flag_multicopter_position_control_enabled'] = True


def status(k, armed, nav, stamp):
    d = {'actuator_armed_updated': True, 'vehicle_status_updated': True, 'vehicle_control_mode_updated': True,
         'actuator_armed_armed': armed, 'vehicle_control_mode_flag_armed': armed,
         'vehicle_status_arming_state': 2 if armed else 1, 'vehicle_status_nav_state': nav,
         'vehicle_status_timestamp': stamp, 'actuator_armed_timestamp': stamp,
         'vehicle_control_mode_timestamp': stamp}
    d.update(AUTO)
    return d


quiet = {'actuator_armed_updated': False, 'vehicle_status_updated': False, 'vehicle_control_mode_updated': False}
ack = lambda c: {'vehicle_command_ack_by_px4_commander_count': 1, 'vehicle_command_ack_by_px4_commander_command': c, 'vehicle_command_ack_by_px4_commander_result': 0,
                 'vehicle_command_ack_by_px4_commander_target_system': 255, 'vehicle_command_ack_by_px4_commander_target_component': 190}
expect = {0: status(0, False, 4, T(0)), 1: dict(quiet), 2: dict(quiet, vehicle_command_ack_by_px4_commander_count=0),
          3: dict(quiet), 4: dict(status(4, True, 4, T(4)), **ack(400)), 5: dict(quiet), 6: dict(quiet),
          7: dict(quiet), 8: dict(quiet, vehicle_status_arming_state=2), 9: dict(quiet),
          12: dict(status(12, True, 4, T(12)), vehicle_status_nav_state_user_intention=4, **ack(176)),
          13: dict(quiet),
          16: dict(status(16, True, 17, T(16)), vehicle_status_nav_state_user_intention=17,
                   vehicle_status_nav_state_timestamp=T(16)),
          17: dict(quiet), 19: dict(quiet, vehicle_status_nav_state=17)}
px4_case.record('px4_commander', params, steps, expect, __doc__)
