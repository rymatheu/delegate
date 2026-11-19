"""The sensor layer: the simulator's state as the raw samples of the vehicle protocol (the flight controller's bridge encodes them).

IMU (body-frame specific force and rates, after every 1200 Hz physics substep, three samples per 400 Hz step), barometer
(ArduPilot's 1976 atmosphere, 100 Hz), compass (ArduPilot's earth field at the home location rotated into the body
frame, minus SITL's sensor offsets, 100 Hz), GPS (position and NED velocity, 5 Hz), RC (neutral sticks, throttle low,
50 Hz) and the battery. Home is the gorge's geographic origin (simulator.gorge_origin: 38.8405556, -105.0441667, 4302 m),
which is world ENU (0, 0, 0): GPS latitude, longitude and altitude, and the barometer's atmosphere, are taken about it.
With a seed, Gaussian noise from a seeded generator is added (deterministic for a given seed).
"""
import math

import numpy as np

from .simulator import GRAVITY_MSS, ap_quat_to_matrix, enu_state_to_ned, quat_ned_frd

# ArduPilot's earth field at the gorge's origin (AP_Declination tables: 0.508486092 G, declination 7.42202234 deg,
# inclination 65.1364594 deg), NED as SITL builds it (Matrix3f::from_euler(0, -inclination, declination) applied to
# (intensity, 0, 0)), in mGauss
_I, _D, _INC = 508.486092, math.radians(7.42202234), math.radians(65.1364594)
GORGE_MAG_NED = np.array([_I * math.cos(_INC) * math.cos(_D), _I * math.cos(_INC) * math.sin(_D), _I * math.sin(_INC)])
MAG_OFS = np.array([5.0, 13.0, -18.0])      # SITL's SIM_MAG1_OFS, the image's COMPASS_OFS
LOCATION_SCALING_FACTOR_INV = 89.83204953368922   # AP_Math/location.h, 1e-7 deg per meter

RC_NEUTRAL = [1500, 1500, 1000, 1500, 1000, 1000, 1000, 1000] + [1500] * 8
BATTERY = (16.0, 0.5)                        # the battery stand-in's (V, A): the X500's 4S

NOISE = dict(accel=0.05, gyro=0.002, baro_pa=1.0, mag=2.0, gps_pos=0.1, gps_vel=0.05)


def pressure_temperature(alt_amsl: float):
    """ArduPilot's 1976 standard atmosphere, troposphere (AP_Baro::get_pressure_temperature_for_alt_amsl)."""
    r = 6356766.0
    h = r * alt_amsl / (r + alt_amsl)            # geopotential altitude
    T = 288.15 - 0.0065 * h
    P = 101325.0 * (T / 288.15) ** (GRAVITY_MSS / (0.0065 * 287.05287))
    return P, T - 273.15


class SpecificForce:
    """Earth-frame specific force in NED, as AP_AHRS::get_accel_ef: the vehicle's true NED acceleration minus the
    gravity vector (0, 0, +g). The acceleration is the backward difference of the NED velocity over the last period,
    which equals the mean of the accelerations of its physics substeps (the differences telescope). Before the first
    sample there is no previous velocity; the vehicle starts at rest on the ground (held by the contact), so the first
    value is (0, 0, -g)."""

    def __init__(self, g: float, dt: float):
        self.g, self.dt, self.v_prev = g, dt, None

    def update(self, vel_ned):
        v = np.asarray(vel_ned, dtype=float)
        acc = np.zeros(3) if self.v_prev is None else (v - self.v_prev) / self.dt
        self.v_prev = v
        return acc - np.array([0.0, 0.0, self.g])


class Sensors:
    """The sensor layer of one vehicle. IMU samples are taken after every physics substep (1200 Hz, three per step);
    barometer and compass every 4th step (100 Hz), GPS every 80th (5 Hz), RC every 8th (50 Hz). home: (lat, lon, alt
    AMSL) of world ENU (0, 0, 0); mag_ned: the earth field there (mGauss, NED)."""

    def __init__(self, seed, substep_s: float, home, mag_ned=GORGE_MAG_NED):
        self.rng = np.random.default_rng(seed) if seed is not None else None
        self.sf = SpecificForce(GRAVITY_MSS, substep_s)
        self.home_lat, self.home_lon, self.home_alt = home
        self.mag_ned = mag_ned

    def n(self, sigma, size=None):
        if self.rng is None:
            return np.zeros(size) if size else 0.0
        return self.rng.normal(0.0, sigma, size)

    @staticmethod
    def state(obs):
        s = obs[0]
        pos, vel, att, rates = enu_state_to_ned(s[0:3], s[3:7], s[10:13], s[13:16])
        R = ap_quat_to_matrix(quat_ned_frd(s[3:7]))     # FRD body -> NED
        return pos, vel, att, rates, R

    def imu(self, obs):
        pos, vel, att, rates, R = self.state(obs)
        f_ned = self.sf.update(vel)                      # earth-frame specific force
        accel = R.T @ f_ned + self.n(NOISE["accel"], 3)
        gyro = np.asarray(rates) + self.n(NOISE["gyro"], 3)
        return tuple(accel), tuple(gyro)

    def slow(self, k: int, obs):
        pos, vel, att, rates, R = self.state(obs)
        out = dict(pos=pos, vel=vel, att=att)
        if k % 4 == 0:
            P, T = pressure_temperature(self.home_alt - pos[2])
            out["baro"] = (P + self.n(NOISE["baro_pa"]), T)
            out["mag"] = tuple(R.T @ self.mag_ned - MAG_OFS + self.n(NOISE["mag"], 3))
        if k % 80 == 0:
            pn = pos + self.n(NOISE["gps_pos"], 3)
            vn = np.asarray(vel) + self.n(NOISE["gps_vel"], 3)
            lat = self.home_lat + pn[0] * 1e-7 * LOCATION_SCALING_FACTOR_INV
            lon = self.home_lon + pn[1] * 1e-7 * LOCATION_SCALING_FACTOR_INV / math.cos(math.radians(self.home_lat))
            out["gps"] = (lat, lon, self.home_alt - pn[2], vn[0], vn[1], vn[2])
        if k % 8 == 0:
            out["rc"] = RC_NEUTRAL
        return out
