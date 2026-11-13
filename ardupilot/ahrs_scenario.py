"""Inputs for the AP_AHRS difftest (ardupilot/ahrs_difftest.py; README.md, "Phase 3: AP_AHRS translated"): the
NavEKF3 scenario of ardupilot/ekf3_scenario.py (the vehicle level at CMAC, armed at `still` - 0.5 s, then
accelerating, cruising and decelerating; IMU, baro, compass, GPS samples; with two IMUs a z bias on IMU0 from
two seconds after take-off), with the values AP_AHRS and its DCM backend read added, each derived from the same
samples (every input of the same getter has the same value: AP_DAL's `ins.get_delta_velocity(i, ...)`, DCM's,
AP_AHRS's), and the vehicle's calls on AP_AHRS: each line is `<ops> <arg> <inputs>`, ops a string of letters
run in order (`B` boot: create_view(ROTATION_NONE), init, set_vehicle_class(COPTER), reset, as
Copter::allocate_motors and startup_INS_ground; `U` update(true), as Copter::read_AHRS; `H` set_home to
get_location's location, as Copter::update_home_from_EKF; `L` lock_home; `O` set_origin(CMAC); `D`
resetHeightDatum; `T` set_terrain_hgt_stable(arg); `K` set_takeoff_expected(arg); `W` set_touchdown_expected(arg);
`Y` request_yaw_reset; `C` check_lane_switch; `E` the parameter AHRS_EKF_TYPE set to arg, as a GCS parameter
write: 10, SITL's SIM backend, and back to 3; 0 (DCM) would have no effect, Copter always uses an EKF). The run's
`events` place the letters other than U (every line updates); `glitch` [first, last, metres] moves the GPS position
north for those steps; `imu_nan` [step, imu] makes one delta velocity of that IMU NaN (an IMU fault)."""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ekf3_scenario  # noqa: E402

DT = ekf3_scenario.DT


def vlen_xy(v):
    return math.hypot(v["x"], v["y"])


def course_deg(v):
    c = math.degrees(math.atan2(v["y"], v["x"]))
    return c + 360.0 if c < 0 else c


def lines(run, steps, tokenize, consts):
    """The lines of a run: (ops, arg) per step and the inputs. consts: the values of the inline boundary getters
    that compute a constant (`AP::ins().get_gyro_drift_rate()`, AP_InertialSensor.h:257), from the C++ side."""
    events = {}
    for ev in run.get("events", []):
        events.setdefault(ev[0], []).append((ev[1], ev[2] if len(ev) > 2 else 0))
    glitch = run.get("glitch")
    imu_nan = run.get("imu_nan")
    k = [0]
    last_fix = [0]

    def tok(v):
        step = k[0]
        k[0] += 1
        if glitch and glitch[0] <= step <= glitch[1] and v["env_dal._gps.location_at"][0]:
            loc = dict(v["env_dal._gps.location_at"][0])
            loc["lat"] = loc["lat"] + int(round(glitch[2] / 111319.49079327357 * 1e7))
            v["env_dal._gps.location_at"] = [loc]
        if imu_nan and step == imu_nan[0]:
            # an IMU fault: one delta velocity of IMU `imu_nan[1]` is NaN (its EKF3 core's states become NaN, so its
            # filter faults are set: AP_AHRS falls back to DCM until NavEKF3 selects another lane)
            dvs = [dict(x) for x in v["env_dal._ins.get_delta_velocity_delta_velocity_at"]]
            dvs[imu_nan[1]]["x"] = float("nan")
            v["env_dal._ins.get_delta_velocity_delta_velocity_at"] = dvs
        ops = "B" if step == 0 else ""
        arg = 0
        for letter, a in events.get(step, []):
            ops += letter
            arg = a
        ops += "U"
        prim = v["env_dal._gps.primary_sensor"]
        gvel = v["env_dal._gps.velocity_at"][prim]
        status = v["env_dal._gps.status_at"][prim]
        if status >= 3:
            last_fix[0] = v["env_dal._gps.last_message_time_ms_at"][prim]
        fu_g = v["env_dal._ins.get_first_usable_gyro"]
        fu_a = v["env_dal._ins.get_first_usable_accel"]
        nimu = v["env_dal._ins.get_accel_count"]
        ok = v["env_dal._ins.use_accel_at"]
        dv = v["env_dal._ins.get_delta_velocity_delta_velocity_at"]
        da = v["env_dal._ins.get_delta_angle_delta_angle_at"]
        accel = [{"x": x["x"] / DT, "y": x["y"] / DT, "z": x["z"] / DT} for x in dv]
        gyro = [{"x": x["x"] / DT, "y": x["y"] / DT, "z": x["z"] / DT} for x in da]
        millis = v["env_dal.micros64"] // 1000
        cfu = v["env_dal._compass.get_first_usable"]
        bprim = v["env_dal._baro.get_primary"]
        common = {
            "millis": millis,
            "get_soft_armed": v["env_dal.get_soft_armed"],
            "status": status,
            "use_for_yaw": v["env_dal._compass.use_for_yaw_at"][cfu],
            "ground_speed": vlen_xy(gvel),
            "was_watchdog_reset": False,
            "persistent_data_home_lat": 0, "persistent_data_home_lon": 0, "persistent_data_home_alt_cm": 0,
            "persistent_data_roll_rad": 0.0, "persistent_data_pitch_rad": 0.0, "persistent_data_yaw_rad": 0.0,
            "get_origin_ret": {}, "get_origin": False,
            "get_EAS2TAS": v["env_dal.get_EAS2TAS"],
            "get_delta_velocity_delta_velocity_at": dv,
            "get_delta_velocity_delta_velocity_dt_at": v["env_dal._ins.get_delta_velocity_delta_velocity_dt_at"],
            "get_delta_velocity_at": v["env_dal._ins.get_delta_velocity_at"],
            "opticalflow_set": False,
            "loop_time_jitter_us": 0,
            "random": 0,
            "get_innovations_velInnov": {}, "get_innovations_posInnov": {}, "get_innovations_magInnov": {},
            "get_innovations_tasInnov": 0.0, "get_innovations_yawInnov": 0.0, "get_innovations": False,
            "get_altitude": v["env_dal._baro.get_altitude_at"][bprim],
            "location": v["env_dal._gps.location_at"][prim],
            # DCM
            "get_accel": accel[fu_a],
            "get_delta_time": DT,
            "get_delta_angle_delta_angle": da[fu_g],
            "get_delta_angle_delta_angle_dt": v["env_dal._ins.get_delta_angle_delta_angle_dt_at"][fu_g],
            "get_delta_angle": v["env_dal._ins.get_delta_angle_at"][fu_g],
            "get_gyro": gyro[fu_g],
            "ground_course": course_deg(gvel),
            "last_update_usec": v["env_dal._compass.last_update_usec_at"][cfu],
            "read": True,
            # the compass's heading from the DCM matrix (AP_AHRS_DCM.cpp:679, a site input): the field's heading
            "calculate_heading": ekf3_scenario.YAW,
            "get_field": v["env_dal._compass.get_field_at"][cfu],
            "get_declination": v["env_dal._compass.get_declination"],
            "last_fix_time_ms": last_fix[0],
            "get_accel_count": nimu,
            "use_accel_at": ok,
            "num_sats": v["env_dal._gps.num_sats_at"][prim],
            "velocity": gvel,
            "get_accel_health_at": ok,
            "healthy": True,
            "get_gyro_drift_rate": consts["get_gyro_drift_rate"],
            "last_message_time_ms": v["env_dal._gps.last_message_time_ms_at"][prim],
            "get_first_usable_gyro": fu_g,
            "get_first_usable_accel": fu_a,
            "AP_baro_healthy": v["env_dal._baro.healthy_at"][bprim],
            "get_climb_rate": -v["env_dal._gps.velocity_at"][prim]["z"],
            "get_lag_lag_sec": v["env_dal._gps.get_lag_lag_sec_at"][prim],
            "get_lag": v["env_dal._gps.get_lag_at"][prim],
            # AP_AHRS_NavEKF3
            "get_gyro_at": gyro,
            "get_accel_at": accel,
        }
        for root in ("env_ahrs", "env_ahrs.dcm", "env_ahrs.ekf3"):
            for key, val in common.items():
                v["%s.%s" % (root, key)] = val
        return [ops, str(arg)] + tokenize(v)

    out = []
    for l in ekf3_scenario.lines(run, steps, tok):
        out.append(l.split(" ", 1)[1])      # (ekf3_scenario's own op, `A`/`U`, replaced by the ops above)
    return out
