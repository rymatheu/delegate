"""The motor map: the vehicle's PWM outputs as the X500's propeller speeds.

ArduPilot's quad X motor slot i (AP_MotorsMatrix::setup_quad_matrix, MOTOR_FRAME_TYPE_X) drives simulator propeller
SLOT_TO_SIM[i] (sim/world/x500/x500.urdf, FLU positions; the URDF's propeller links are in the order and spin that
gym-pybullet-drones' yaw-torque sum -t0 + t1 - t2 + t3 assumes); angles from the nose, clockwise positive seen from above:
  slot 0   45 deg front-right CCW -> prop0 at (+x, -y), CCW (its drag torque enters z_torque with -)
  slot 1 -135 deg rear-left   CCW -> prop2 at (-x, +y), CCW
  slot 2  -45 deg front-left  CW  -> prop3 at (+x, +y), CW
  slot 3  135 deg rear-right  CW  -> prop1 at (-x, -y), CW
These are PX4's rotor_0..3 of the X500 model, in the same order and spins.
"""
import math

import numpy as np

SLOT_TO_SIM = [0, 2, 3, 1]


def actuators_to_rpm(env, a) -> np.ndarray:
    """Actuator a of slot i -> thrust fraction a of the maximum per-motor thrust T_max = kf MAX_RPM^2 (identity: the
    vehicle runs with MOT_THST_EXPO 0, MOT_SPIN_MIN 0, MOT_SPIN_MAX 1), so the propeller speed is MAX_RPM sqrt(a),
    clipped to [0, MAX_RPM]."""
    rpm = np.zeros(4)
    for i, ai in enumerate(a):
        rpm[SLOT_TO_SIM[i]] = env.MAX_RPM * math.sqrt(max(0.0, min(1.0, ai)))
    return rpm


def pwm_to_rpm(env, pwm):
    """The propeller speeds and the actuators a = (PWM - 1000) / 1000, clipped to [0, 1], of the first four PWM
    outputs (the motor slots 0..3)."""
    a = [min(1.0, max(0.0, (pwm[i] - 1000) / 1000.0)) for i in range(4)]
    return actuators_to_rpm(env, a), a
