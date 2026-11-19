"""The simulator: gym-pybullet-drones with the gorge world and the X500, its constants, and the frame conversions.

Environment. `make_env` (one X500) and `make_formation_env` (several) build sim/world/gorge_aviary.GorgeAviary and
FormationAviary (Physics.PYB, the gorge's collision bodies in place of the ground plane, the X500 of
sim/world/x500/x500.urdf with the motor lag airframes.LAG), stepped at the physics rate (1200 Hz: control frequency =
physics frequency, so that every physics substep yields an IMU sample; the vehicle's PWM is held for the three substeps
of one 400 Hz step). Gravity is ArduPilot's GRAVITY_MSS instead of the package's 9.8, and the constants the package
derives from it are recomputed as BaseAviary.__init__ does, so that the specific force at rest is exactly
(0, 0, -GRAVITY_MSS) and zero in free fall. Each vehicle starts level, at rest, its base 5 mm above
gorge_plan.start_rest_z at its start; `reset_env` removes PyBullet's velocity damping and settles the vehicles on their
contact with the motors off for SETTLE_S, before the run's clock starts.

Frames. PyBullet's world is ENU (x east, y north, z up) and its body frame FLU (forward, left, up); ArduPilot's are NED
and FRD. ENU_TO_NED and FRD_TO_FLU are fixed proper rotations (det +1), so they map vectors and angular velocities alike.
Quaternions are (w, x, y, z), w scalar, as ArduPilot's (q1, q2, q3, q4), except PyBullet's (x, y, z, w).
"""
from __future__ import annotations

import contextlib
import io
import math

import numpy as np

from . import BUILD_DIR, WORLD_DIR

# ArduPilot's GRAVITY_MSS (AP_Math/definitions.h), written over the environment's gravity (_aviary)
GRAVITY_MSS = 9.80665
CTRL_HZ = 400                    # the vehicle's loop rate: one protocol line per step
STEP_US = 2500                   # the step, 1 / CTRL_HZ, in microseconds
SETTLE_S = 0.25                  # motors off on the contact before the first step
GORGE_SEED = 7                   # the gorge of sim/world/gorge.py that the missions are planned in

# Fixed change of basis from the simulator's world frame (ENU) to the vehicle's (NED).
ENU_TO_NED = np.array([[0.0, 1.0, 0.0],
                       [1.0, 0.0, 0.0],
                       [0.0, 0.0, -1.0]])
# Fixed change of basis between the URDF body frame (FLU) and the vehicle's (FRD); its own inverse.
FRD_TO_FLU = np.diag([1.0, -1.0, -1.0])
# ENU_TO_NED is the half turn about (1, 1, 0)/sqrt2, FRD_TO_FLU the half turn about x.
Q_ENU_TO_NED = (0.0, math.sqrt(0.5), math.sqrt(0.5), 0.0)
Q_FRD_TO_FLU = (0.0, 1.0, 0.0, 0.0)


def quat_to_matrix(q):
    """Rotation matrix of a unit quaternion given as (x, y, z, w), PyBullet's order."""
    x, y, z, w = q
    return np.array([
        [1 - 2 * (y * y + z * z), 2 * (x * y - z * w), 2 * (x * z + y * w)],
        [2 * (x * y + z * w), 1 - 2 * (x * x + z * z), 2 * (y * z - x * w)],
        [2 * (x * z - y * w), 2 * (y * z + x * w), 1 - 2 * (x * x + y * y)],
    ])


def zyx_euler(R):
    """ZYX Euler angles (roll, pitch, yaw) of a rotation matrix R = Rz(yaw) Ry(pitch) Rx(roll)."""
    roll = math.atan2(R[2, 1], R[2, 2])
    pitch = math.asin(max(-1.0, min(1.0, -R[2, 0])))
    yaw = math.atan2(R[1, 0], R[0, 0])
    return roll, pitch, yaw


def enu_state_to_ned(pos, quat, vel, ang_vel_world):
    """One PyBullet state (ENU world, FLU body) as the vehicle's NED/FRD quantities: position and velocity (NED), ZYX
    Euler angles of the FRD body in NED, and body rates (p, q, r) about FRD."""
    R_enu_flu = quat_to_matrix(quat)                      # FLU body -> ENU world
    R_ned_frd = ENU_TO_NED @ R_enu_flu @ FRD_TO_FLU       # FRD body -> NED world
    pos_ned = ENU_TO_NED @ np.asarray(pos)
    vel_ned = ENU_TO_NED @ np.asarray(vel)
    omega_ned = ENU_TO_NED @ np.asarray(ang_vel_world)    # PyBullet reports world-frame angular velocity
    rates_frd = R_ned_frd.T @ omega_ned                   # body rates are its body-frame components
    return pos_ned, vel_ned, zyx_euler(R_ned_frd), rates_frd


def qmul(a, b):
    """Hamilton product a * b of (w, x, y, z) quaternions; the rotation of a * b is R(a) R(b)."""
    aw, ax, ay, az = a
    bw, bx, by, bz = b
    return (aw * bw - ax * bx - ay * by - az * bz,
            aw * bx + ax * bw + ay * bz - az * by,
            aw * by - ax * bz + ay * bw + az * bx,
            aw * bz + ax * by - ay * bx + az * bw)


def quat_ned_frd(q_pyb):
    """Body (FRD) to NED attitude quaternion (q1 scalar) from PyBullet's (x, y, z, w) FLU-to-ENU one:
    q = q(ENU_TO_NED) * q_enu_flu * q(FRD_TO_FLU), the quaternion form of R_ned_frd = T R_enu_flu D
    used by enu_state_to_ned. Normalized, sign chosen with q1 >= 0."""
    x, y, z, w = q_pyb
    q = qmul(qmul(Q_ENU_TO_NED, (w, x, y, z)), Q_FRD_TO_FLU)
    n = math.sqrt(sum(c * c for c in q))
    s = (1.0 if q[0] >= 0 else -1.0) / n
    return tuple(c * s for c in q)


def ap_quat_to_matrix(q):
    """ArduPilot's Quaternion::rotation_matrix (body to earth) of (q1, q2, q3, q4)."""
    w, x, y, z = q
    return quat_to_matrix((x, y, z, w))


def gorge_origin():
    """The gorge's geographic origin (the ORIGIN line of sim/world/origin.params), world ENU (0, 0, 0)."""
    import geo
    return geo.Origin.from_params([WORLD_DIR / "origin.params"])


def start_rpy(yaw_deg=0.0):
    """PyBullet's roll, pitch, yaw of a vehicle standing level with NED heading yaw_deg (0: nose north, PyBullet yaw
    pi/2, measured counter-clockwise from east)."""
    import pybullet as pb
    from scipy.spatial.transform import Rotation
    r, pt, y = (math.radians(v) for v in (0.0, 0.0, yaw_deg))
    c, sn = np.cos, np.sin
    R_ned_frd = (np.array([[c(y), -sn(y), 0], [sn(y), c(y), 0], [0, 0, 1]])
                 @ np.array([[c(pt), 0, sn(pt)], [0, 1, 0], [-sn(pt), 0, c(pt)]])
                 @ np.array([[1, 0, 0], [0, c(r), -sn(r)], [0, sn(r), c(r)]]))
    R_enu_flu = ENU_TO_NED.T @ R_ned_frd @ FRD_TO_FLU
    q = Rotation.from_matrix(R_enu_flu).as_quat()  # (x, y, z, w)
    return pb.getEulerFromQuaternion(q)


def _aviary(cls, pyb_hz, **kw):
    """An aviary of X500s stepped at the physics rate, with ArduPilot's gravity."""
    import warnings
    warnings.filterwarnings("ignore", module="gymnasium")
    from gym_pybullet_drones.utils.enums import DroneModel, Physics
    import airframes
    with contextlib.redirect_stdout(io.StringIO()):   # the environment prints its URDF constants
        # gym-pybullet-drones requires a DroneModel member; the X500's URDF (urdf=) replaces the model it names
        env = cls(urdf=airframes.AIRFRAMES["x500"]["urdf"], lag=airframes.LAG, drone_model=DroneModel.CF2X,
                  physics=Physics.PYB, pyb_freq=pyb_hz, ctrl_freq=pyb_hz, gui=False, record=False, obstacles=False,
                  user_debug_gui=False, output_folder=str(BUILD_DIR / "pyb"), **kw)
    # gravity GRAVITY_MSS, and the constants derived from it as BaseAviary.__init__ computes them, so that the
    # thrust-to-weight ratio is the URDF's
    env.G = GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    return env


def make_env(g, pyb_hz, wind=None):
    """gorge_aviary.GorgeAviary with one X500 resting on the floor at the plan's start (g.path[0]), level, nose north.
    wind: wind.Wind or None."""
    import gorge_plan
    from gorge_aviary import GorgeAviary
    env = _aviary(GorgeAviary, pyb_hz, gorge=g, wind=wind, num_drones=1)
    start = g.path[0]                         # ENU
    env.INIT_XYZS = np.array([[float(start[0]), float(start[1]), gorge_plan.start_rest_z(g, np.array(start[:2])) + 0.005]])
    env.INIT_RPYS = np.array([start_rpy()])
    return env


def make_formation_env(g, pyb_hz, starts_xy, yaws_deg=None):
    """gorge_aviary.FormationAviary (per-vehicle motor lag, no wind) with one X500 per start: each level, nose north or
    at yaws_deg[i] (NED heading, deg), resting on the floor at starts_xy[i] (ENU)."""
    import gorge_plan
    from gorge_aviary import FormationAviary
    env = _aviary(FormationAviary, pyb_hz, gorge=g, winds=None, num_drones=len(starts_xy))
    xyz, rpy = [], []
    for i, xy in enumerate(starts_xy):
        yaw = 0.0 if yaws_deg is None else float(yaws_deg[i])
        xyz.append([float(xy[0]), float(xy[1]), gorge_plan.start_rest_z(g, np.asarray(xy, float)) + 0.005])
        rpy.append(start_rpy(yaw))
    env.INIT_XYZS, env.INIT_RPYS = np.array(xyz), np.array(rpy)
    return env


def reset_env(env):
    """Reset the environment, remove PyBullet's default velocity damping, and let the vehicles settle on their contact
    before the first step.

    PyBullet damps every body's linear and angular velocity by default (factor (1 - 0.04)^dt each step), a drag-like
    term that the URDF does not ask for; with it the specific force in free fall is -0.04 v instead of zero. Damping is
    set to zero, so the simulated vehicle is the rigid body of the thrust and drag-torque model only (no drag, ground
    effect or downwash, as Physics.PYB). The vehicles are then stepped with the motors off for SETTLE_S seconds, so that
    the contact's start-up transients are over; afterwards a vehicle rests with a contact jitter of about 0.01 m/s^2 in
    the specific force. The run's clock starts after that."""
    import pybullet as pb
    obs, _ = env.reset()
    for d in env.DRONE_IDS:
        pb.changeDynamics(d, -1, linearDamping=0.0, angularDamping=0.0, physicsClientId=env.CLIENT)
    for _ in range(int(SETTLE_S * env.PYB_FREQ)):
        obs, *_ = env.step(np.zeros((env.NUM_DRONES, 4)))
    return obs
