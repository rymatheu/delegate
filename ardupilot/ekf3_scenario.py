"""Physically plausible inputs for the NavEKF3 difftest (ardupilot/ekf3_difftest.py; README.md, "Phase 3: AP_DAL
and NavEKF3"): the front ends as AP_DAL reads them, step by step at the reference vehicle's loop rate (400 Hz).

The vehicle sits level at CMAC (yaw 30 degrees) for `still` seconds, is armed, then accelerates north-east and
climbs, cruises and decelerates (the attitude stays level: the EKF needs consistent inertial and aiding data,
not a flight dynamics model). The IMUs give delta angles and delta velocities each step (the body-frame
specific force and rates times the step, small seeded noise; with two IMUs, IMU0's gyro and accelerometer get the run's z biases
`fault`, `accel_fault` two seconds after take-off, so that the second core becomes the better one and the lanes switch); the
barometer reports at 50 Hz, the compass at 100 Hz (the CMAC field rotated into the body frame), the GPS at
5 Hz (a 3D fix from 2 s on, 15 satellites). The NavEKF3 front end is initialised after one second, as
AP_AHRS does after its start-up delay; every other step is an UpdateFilter. The source selection inputs
(AP_NavEKF_Source, --boundary-call) are those of ArduPilot's default source parameters (EK3_SRC1_*: GPS
position and velocity, baro height, compass yaw), which the C++ driver checks against AP_NavEKF_Source."""

import math
import random

DT = 0.0025
G = 9.80665
LAT0, LNG0, ALT0 = -35.363261, 149.165230, 584.0
YAW = math.radians(30.0)
# the earth field at CMAC (mGauss, NED): about 576 mG, inclination -66 deg, declination 12.4 deg
DECL = math.radians(12.4)
H = 576.0 * math.cos(math.radians(66.0))
EARTH = (H * math.cos(DECL), H * math.sin(DECL), -576.0 * math.sin(math.radians(66.0)))

# AP_NavEKF_Source with ArduPilot's default source parameters
GPS_XY, BARO_Z, GPS_Z, COMPASS_YAW = 3, 1, 3, 1


def body(v):
    """NED to body frame for the level attitude with yaw YAW."""
    c, s = math.cos(YAW), math.sin(YAW)
    return (c * v[0] + s * v[1], -s * v[0] + c * v[1], v[2])


def vec(x, y, z):
    return {"x": x, "y": y, "z": z}


def accel_ned(t, still):
    """The vehicle's acceleration (NED) at time t (seconds since the start)."""
    m = t - still
    if m < 0:
        return (0.0, 0.0, 0.0)
    if m < 3:
        return (0.6, 0.4, -0.2)
    if m < 6:
        return (0.0, 0.0, 0.0)
    if m < 9:
        return (-0.6, -0.4, 0.2)
    return (0.0, 0.0, 0.0)


def lines(run, steps, tokenize):
    rng = random.Random(run.get("seed", 20261111))
    still = run.get("still", 16.0)
    nimu = run.get("imus", 1)
    t0_us = 1_000_000
    pos, vel = [0.0, 0.0, 0.0], [0.0, 0.0, 0.0]
    baro_ms = mag_us = gps_ms = 0
    baro_alt, mag_field = 0.0, vec(0, 0, 0)
    gps = None
    armed_at = None
    out = []
    for k in range(steps):
        t = k * DT
        t_us = t0_us + int(round(k * DT * 1e6))
        a = accel_ned(t, still)
        for i in range(3):
            vel[i] += a[i] * DT
            pos[i] += vel[i] * DT
        armed = t >= still - 0.5
        if armed and armed_at is None:
            armed_at = t_us
        flying = armed and t >= still
        f = body((a[0], a[1], a[2] - G))
        dv, da, ok = [], [], []
        for i in range(3):
            if i < nimu:
                bias = (0.0, 0.0, 0.0) if i == 1 else (0.0, 0.0, 0.0) if nimu == 1 or t < still + 2 else (0.0, 0.0, run.get("fault", 0.0))
                ab = (0.0, 0.0, run.get("accel_fault", 0.0)) if i == 0 and nimu > 1 and t >= still + 2 else (0.0, 0.0, 0.0)
                dv.append(vec(*[(f[j] + ab[j] + rng.gauss(0, 0.05)) * DT for j in range(3)]))
                da.append(vec(*[(bias[j] + rng.gauss(0, 0.002)) * DT for j in range(3)]))
                ok.append(True)
            else:
                dv.append(vec(0, 0, 0))
                da.append(vec(0, 0, 0))
                ok.append(False)
        if k % 8 == 0:
            baro_ms = t_us // 1000
            baro_alt = -pos[2] + rng.gauss(0, 0.1)
        if k % 4 == 0:
            mag_us = t_us
            b = body(EARTH)
            mag_field = vec(*[b[j] + rng.gauss(0, 2.0) for j in range(3)])
        if k % 80 == 0 and t >= 2.0:
            gps_ms = t_us // 1000
            n, e, d = (pos[j] + rng.gauss(0, 0.1) for j in range(3))
            lat = LAT0 + n / 111319.49079327357
            lng = LNG0 + e / (111319.49079327357 * math.cos(math.radians(LAT0)))
            gps = {"lat": int(round(lat * 1e7)), "lng": int(round(lng * 1e7)), "alt": int(round((ALT0 - d) * 100))}
            gvel = vec(*[vel[j] + rng.gauss(0, 0.05) for j in range(3)])
        home = {"lat": int(round(LAT0 * 1e7)), "lng": int(round(LNG0 * 1e7)), "alt": int(round(ALT0 * 100))} if armed else {}
        v = {
            # AP_DAL: the vehicle, AP_AHRS, the HAL
            "env_dal.get_last_update_usec": t_us & 0xffffffff,
            "env_dal.get_time_flying_ms": (t_us - armed_at) // 1000 if flying else 0,
            "env_dal.micros64": t_us,
            "env_dal.micros": t_us & 0xffffffff,
            "env_dal.get_soft_armed": armed,
            "env_dal.get_home": home,
            "env_dal.get_EAS2TAS": 1.0,
            "env_dal.get_vehicle_class": 2,             # AP_AHRS::VehicleClass::COPTER
            "env_dal.get_fly_forward": False,
            "env_dal.get_takeoff_expected": False,
            "env_dal.get_touchdown_expected": False,
            "env_dal.available_memory": 1 << 20,
            "env_dal.get_trim": vec(0, 0, 0),
            "env_dal.nonnull": False,
            "env_dal.num_sensors": 0,
            "env_dal.configured_ekf_type": 3,
            "env_dal.get_rotation_vehicle_body_to_autopilot_body": {"a": vec(1, 0, 0), "b": vec(0, 1, 0), "c": vec(0, 0, 1)},
            "env_dal.get_loop_delta_t": DT,
            # AP_InertialSensor
            "env_dal._ins.get_loop_rate_hz": 400,
            "env_dal._ins.get_first_usable_gyro": 0,
            "env_dal._ins.get_loop_delta_t": DT,
            "env_dal._ins.get_first_usable_accel": 0,
            "env_dal._ins.get_accel_count": nimu,
            "env_dal._ins.get_gyro_count": nimu,
            "env_dal._ins.use_accel_at": ok,
            "env_dal._ins.get_delta_velocity_delta_velocity_at": dv,
            "env_dal._ins.get_delta_velocity_delta_velocity_dt_at": [DT if x else 0.0 for x in ok],
            "env_dal._ins.get_delta_velocity_at": ok,
            "env_dal._ins.use_gyro_at": ok,
            "env_dal._ins.get_delta_angle_delta_angle_at": da,
            "env_dal._ins.get_delta_angle_delta_angle_dt_at": [DT if x else 0.0 for x in ok],
            "env_dal._ins.get_delta_angle_at": ok,
            "env_dal._ins.get_gyro_bias_limit_rads_at": [0.5] * 3,
            "env_dal._ins.get_gyro_bias_init_dps_at": [2.5] * 3,
            "env_dal._ins.get_imu_pos_offset_at": [vec(0, 0, 0)] * 3,
            # AP_Baro
            "env_dal._baro.get_primary": 0,
            "env_dal._baro.num_instances": 1,
            "env_dal._baro.get_last_update_at": [baro_ms],
            "env_dal._baro.healthy_at": [True],
            "env_dal._baro.get_altitude_at": [baro_alt],
            # AP_GPS
            "env_dal._gps.primary_sensor": 0,
            "env_dal._gps.num_sensors": 1,
            "env_dal._gps.status_at": [3 if gps else 1],
            "env_dal._gps.get_antenna_offset_at": [vec(0, 0, 0)] * 3,
            "env_dal._gps.location_at": [gps or {}],
            "env_dal._gps.last_message_time_ms_at": [gps_ms],
            "env_dal._gps.have_vertical_velocity_at": [True],
            "env_dal._gps.horizontal_accuracy_hacc_at": [0.5],
            "env_dal._gps.horizontal_accuracy_at": [True],
            "env_dal._gps.vertical_accuracy_vacc_at": [0.8],
            "env_dal._gps.vertical_accuracy_at": [True],
            "env_dal._gps.get_hdop_at": [100],
            "env_dal._gps.num_sats_at": [15 if gps else 0],
            "env_dal._gps.get_lag_lag_sec_at": [0.2],
            "env_dal._gps.get_lag_at": [True],
            "env_dal._gps.velocity_at": [gvel if gps else vec(0, 0, 0)],
            "env_dal._gps.speed_accuracy_sacc_at": [0.2],
            "env_dal._gps.speed_accuracy_at": [True],
            "env_dal._gps.gps_yaw_deg_at": [False],
            "env_dal._gps.gps_yaw_deg_yaw_deg_at": [0.0],
            "env_dal._gps.gps_yaw_deg_accuracy_deg_at": [0.0],
            "env_dal._gps.gps_yaw_deg_time_ms_at": [0],
            # Compass
            "env_dal._compass.available": True,
            "env_dal._compass.get_count": 1,
            "env_dal._compass.auto_declination_enabled": True,
            "env_dal._compass.get_declination": DECL,
            "env_dal._compass.get_num_enabled": 1,
            "env_dal._compass.consistent": True,
            "env_dal._compass.get_first_usable": 0,
            "env_dal._compass.learn_offsets_enabled": False,
            "env_dal._compass.use_for_yaw_at": [True],
            "env_dal._compass.healthy_at": [True],
            "env_dal._compass.get_offsets_at": [vec(0, 0, 0)] * 3,
            "env_dal._compass.have_scale_factor_at": [False],
            "env_dal._compass.last_update_usec_at": [mag_us],
            "env_dal._compass.get_field_at": [mag_field],
        }
        # AP_NavEKF_Source (--boundary-call) with the default source parameters, for every core index
        for key, val in run_sources().items():
            v[key] = val
        op = "A" if k >= 400 else "U"      # AP_AHRS starts EKF3 after its start-up delay
        out.append(" ".join([op] + tokenize(v)))
    return out


def run_sources():
    return {
        "env_ekf3.getPosXYSource_at": [GPS_XY] * 3,
        "env_core.usingGPS_at": [True] * 3,
        "env_core.ext_nav_enabled": False,
        "env_core.wheel_encoder_enabled": False,
        "env_core.gps_yaw_enabled": False,
        "env_core.getVelXYSource_at": [GPS_XY] * 3,
        "env_core.getPosXYSource_at": [GPS_XY] * 3,
        "env_core.getYawSource_at": [COMPASS_YAW] * 3,
        "env_core.getPosZSource_at": [BARO_Z] * 3,
        # useVelXYSource(src, i) / useVelZSource(src, i): src is the configured source (FUSE_ALL_VELOCITIES off)
        "@useVelXYSource": lambda src: [src == GPS_XY] * 3,
        "@useVelZSource": lambda src: [src == GPS_Z] * 3,
    }
