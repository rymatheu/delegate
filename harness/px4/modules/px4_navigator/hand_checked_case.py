#!/usr/bin/env python3
"""Hand-checked case of px4_navigator: a two-waypoint mission stored in dataman as MAVLink's
mission manager stores it, then flown in AUTO_MISSION.

Inputs every tick: the vehicle airborne 10 m above the SITL home (local and global position
valid, not landed). Tick 0: vehicle_status (armed, rotary wing, AUTO_LOITER) and home_position.
Ticks 2-4: three DM_WRITE requests from client 200 on the mirror port (one each), as
MavlinkMissionManager::handle_mission_item / update_active_mission make them
(mavlink_mission.cpp:1123-1160, :155-188): item 7 (DM_KEY_WAYPOINTS_OFFBOARD_1, the storage not in
use, :972) index 0 and 1, each a 56-byte mission_item_s as parse_mavlink_mission_item makes it from
a MISSION_ITEM_INT with frame 3 (GLOBAL_RELATIVE_ALT), command 16 (NAV_WAYPOINT), x/y in 1e-7
degrees, z = 10 m, param4 NaN, autocontinue 1 (:1396-1531): lat = x * 1e-7, altitude 10,
altitude_is_relative 1, frame 3, nav_cmd 16, yaw = wrap_2pi(radians(NaN)) = NaN; then item 8
(DM_KEY_MISSION_STATE) index 0, the mission_s state (count 2, storage 7, current_seq 0, land
indices -1, mission_id 0x1234). Tick 5: the `mission` topic with the same content. Tick 40:
vehicle_status with nav_state AUTO_MISSION (3).

Worked out from dataman.cpp (task_main, _ram_write): each write is answered in its own step with
status 0 (STATUS_SUCCESS), the request's client id, type, item and index (ticks 2, 3, 4).
Worked out from the navigator: in AUTO_LOITER airborne (tick 0) the triplet is a loiter setpoint
(type 2) at the current position, alt = 488 + 10 = 498 (loiter.cpp set_loiter_position). Once the
mission runs, the current setpoint is waypoint 0 and the next is waypoint 1, both POSITION (0),
lat/lon the stored doubles as binary32 (the ports carry float64 as binary32), alt = home alt 488 +
10 (MissionBlock::get_absolute_altitude_for_item, relative altitude); the previous setpoint is the
loiter setpoint it replaces; mission_result: valid, 2 items, current 0, not finished.
Observed and explained, not derived: the step at which the mission starts (100). Navigator passes
come with its poll: local position at most every 50 ms (orb_set_interval(50),
SubscriptionInterval: ticks 0, 1, 20, 40, 60, 80, 100), vehicle_status and mission messages
(ticks 0, 5, 40). After the switch at 40 the mission waits for the feasibility check, which needs
the geofence loaded from dataman (MissionBase::canRunMissionFeasibility, mission_base.cpp:1451),
and for its items in the DatamanCache; both load through asynchronous dataman requests, one round
trip per pass, so the mission starts at the third pass after the switch.
"""
import os
import struct
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'py'))
import px4_case  # noqa: E402

LAT, LON, ALT = 47.397742, 8.545594, 488.0
def T(k): return 1000000 + 2500 * k
def item(lat_e7, lon_e7, alt_rel, seq):
    # mission_item_s as MavlinkMissionManager::parse_mavlink_mission_item makes it from a
    # MISSION_ITEM_INT, frame 3 (GLOBAL_RELATIVE_ALT), command 16 (NAV_WAYPOINT), param1-3 0,
    # param4 NaN (yaw unchanged), autocontinue 1
    lat = float(lat_e7) * 1e-7
    lon = float(lon_e7) * 1e-7
    nan = float('nan')
    floats = [0.0, 0.0, 0.0, nan, 0.0, 0.0, alt_rel]
    bits = 3 | (0 << 4) | (0 << 7) | (0 << 8) | (1 << 9) | (1 << 10)
    return struct.pack('<dd7fHhHHH2x', lat, lon, *floats, 16, 0, 0, 0, bits)
def mission_state(count, dm_id, seq, mid, t):
    return struct.pack('<QiiiIIIHBBB3x', t, seq, -1, -1, mid, 0, 0, count, dm_id, 0, 0)
def dm_write(k, item_id, index, data, client=200):
    d = {'dataman_request_updated': True, 'dataman_request_timestamp': T(k), 'dataman_request_client_id': client,
         'dataman_request_request_type': 1, 'dataman_request_item': item_id, 'dataman_request_index': index,
         'dataman_request_data_length': len(data)}
    for i, b in enumerate(data):
        d[f'dataman_request_data_{i}'] = b
    return d
def state(k, nav, armed=True, alt=10.0):
    t = T(k)
    d = {'t_us': t}
    d.update({'vehicle_local_position_updated': True, 'vehicle_local_position_timestamp': t,
              'vehicle_local_position_timestamp_sample': t, 'vehicle_local_position_xy_valid': True,
              'vehicle_local_position_z_valid': True, 'vehicle_local_position_v_xy_valid': True,
              'vehicle_local_position_v_z_valid': True, 'vehicle_local_position_z': -alt,
              'vehicle_local_position_xy_global': True, 'vehicle_local_position_z_global': True,
              'vehicle_local_position_ref_timestamp': 1000000, 'vehicle_local_position_ref_lat': LAT,
              'vehicle_local_position_ref_lon': LON, 'vehicle_local_position_ref_alt': ALT,
              'vehicle_local_position_heading_good_for_control': True,
              'vehicle_local_position_eph': 0.5, 'vehicle_local_position_epv': 0.5,
              'vehicle_local_position_vxy_max': float('inf'), 'vehicle_local_position_vz_max': float('inf'),
              'vehicle_local_position_hagl_min': float('inf'), 'vehicle_local_position_hagl_max_z': float('inf'),
              'vehicle_local_position_hagl_max_xy': float('inf')})
    d.update({'vehicle_global_position_updated': True, 'vehicle_global_position_timestamp': t,
              'vehicle_global_position_timestamp_sample': t, 'vehicle_global_position_lat': LAT,
              'vehicle_global_position_lon': LON, 'vehicle_global_position_alt': ALT + alt,
              'vehicle_global_position_alt_ellipsoid': ALT + alt, 'vehicle_global_position_lat_lon_valid': True,
              'vehicle_global_position_alt_valid': True, 'vehicle_global_position_eph': 0.5,
              'vehicle_global_position_epv': 0.5})
    d.update({'vehicle_land_detected_updated': True, 'vehicle_land_detected_timestamp': t,
              'vehicle_land_detected_landed': False})
    return d
def status(k, nav, armed=True):
    t = T(k)
    return {'vehicle_status_updated': True, 'vehicle_status_timestamp': t, 'vehicle_status_arming_state': 2 if armed else 1,
            'vehicle_status_nav_state': nav, 'vehicle_status_nav_state_user_intention': nav,
            'vehicle_status_nav_state_timestamp': t, 'vehicle_status_vehicle_type': 1,
            'vehicle_status_system_id': 1, 'vehicle_status_component_id': 1, 'vehicle_status_pre_flight_checks_pass': True,
            'vehicle_status_armed_time': 1000000, 'vehicle_status_takeoff_time': 1000000}
def home(k):
    t = T(k)
    return {'home_position_updated': True, 'home_position_timestamp': t, 'home_position_lat': LAT,
            'home_position_lon': LON, 'home_position_alt': ALT, 'home_position_valid_alt': True,
            'home_position_valid_hpos': True, 'home_position_valid_lpos': True, 'home_position_manual_home': False,
            'home_position_update_count': 1}


def mirrored(k, d):
    """A dataman_request as one message on the mirror port: the bytes of dataman_request_s
    (timestamp u64, index u32, data_length u32, client_id, request_type, item, data[56], 5 pad)
    in u32 words, as px4_mavlink's tap packs it."""
    raw = struct.pack('<QIIBBB56s5x', d['dataman_request_timestamp'], d['dataman_request_index'],
                      d['dataman_request_data_length'], d['dataman_request_client_id'],
                      d['dataman_request_request_type'], d['dataman_request_item'],
                      bytes(d.get(f'dataman_request_data_{i}', 0) for i in range(56)))
    out = {'dataman_request_mirror_count': 1}
    out.update({f'dataman_request_mirror_{i}': int.from_bytes(raw[4 * i:4 * i + 4], 'little')
                for i in range(len(raw) // 4)})
    return out


def f32(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


N = 120
steps = [state(k, 4) for k in range(N)]
steps[0].update(status(0, 4))
steps[0].update(home(0))
steps[2].update(mirrored(2, dm_write(2, 7, 0, item(473980000, 85456000, 10.0, 0))))
steps[3].update(mirrored(3, dm_write(3, 7, 1, item(473980000, 85470000, 10.0, 1))))
steps[4].update(mirrored(4, dm_write(4, 8, 0, mission_state(2, 7, 0, 0x1234, T(4)))))
steps[5].update({'mission_updated': True, 'mission_timestamp': T(5), 'mission_mission_dataman_id': 7,
                 'mission_count': 2, 'mission_current_seq': 0, 'mission_land_start_index': -1,
                 'mission_land_index': -1, 'mission_mission_id': 0x1234})
steps[40].update(status(40, 3))
params = px4_case.defaults('px4_navigator')
params.update({'NAV_ACC_RAD': 2.0, 'RTL_RETURN_ALT': 30.0, 'RTL_DESCEND_ALT': 10.0})


def ack(item_id, index):
    return {'dataman_response_updated': True, 'dataman_response_client_id': 200,
            'dataman_response_request_type': 1, 'dataman_response_item': item_id,
            'dataman_response_index': index, 'dataman_response_status': 0}


P = 'position_setpoint_triplet_'
loiter = {P + 'current_valid': True, P + 'current_type': 2, P + 'current_lat': f32(LAT),
          P + 'current_lon': f32(LON), P + 'current_alt': 498.0}
expect = {
    0: dict(loiter, **{P + 'updated': True, P + 'timestamp': T(0), P + 'next_valid': False}),
    2: ack(7, 0), 3: ack(7, 1), 4: ack(8, 0),
    100: {P + 'updated': True, P + 'timestamp': T(100),
          P + 'previous_valid': True, P + 'previous_type': 2, P + 'previous_lat': f32(LAT),
          P + 'previous_lon': f32(LON), P + 'previous_alt': 498.0,
          P + 'current_valid': True, P + 'current_type': 0, P + 'current_lat': f32(47.398),
          P + 'current_lon': f32(8.5456), P + 'current_alt': 498.0,
          P + 'next_valid': True, P + 'next_type': 0, P + 'next_lat': f32(47.398),
          P + 'next_lon': f32(8.547), P + 'next_alt': 498.0,
          'mission_result_valid': True, 'mission_result_seq_total': 2,
          'mission_result_seq_current': 0, 'mission_result_finished': False,
          'mission_result_mission_id': 0x1234, 'px4_navigator_errors': 0},
    119: {'px4_navigator_errors': 0, P + 'current_type': 0}}
px4_case.record('px4_navigator', params, steps, expect, __doc__)
