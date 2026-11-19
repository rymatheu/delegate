"""Simulated airframes of the gorge world, and the gym-pybullet-drones aviary that flies them.

Airframes (`AIRFRAMES`): URDF and motor time constants (up, down) in s. The gorge has one airframe:
- x500: x500/x500.urdf (Holybro X500 V2 from PX4's Gazebo model; sources in the URDF), with the first-order motor lag
  LAG = (0.0125, 0.025) s (PX4 gz `timeConstantUp`, `timeConstantDown`). The URDF's propeller links are in the order
  the package's quadrotor URDFs use (prop0 front right CCW, prop1 rear right CW, prop2 rear left CCW, prop3 front left
  CW, which is what the package's yaw-torque sum -t0 + t1 - t2 + t3 assumes), so sim/gorgesim/motors.SLOT_TO_SIM sends
  motors 1..4 (front right CCW, rear left CCW, front left CW, rear right CW) to the right propellers. The package's own
  models are not used.

`AirframeAviary`: CtrlAviary with a URDF from outside the package and an optional first-order motor lag. The package has
no X500 and loads its URDFs from its own assets directory, so `_parseURDFParameters` points `self.URDF` at the file before
the package parses it; the package joins `files('gym_pybullet_drones') / 'assets' / self.URDF`, a pathlib join, so an
absolute `self.URDF` is used as is, by the parser and by `_housekeeping`'s `loadURDF` alike. Nothing in the installed
package is modified.

Motor lag: each propeller's thrust follows its commanded thrust through a first-order lag with time constant 0.0125 s
when rising and 0.025 s when falling. It is applied in `_physics`, i.e. once per physics substep, as the exact step
response of the lag over one substep, to the thrust kf rpm^2 before it is turned back into the RPM the package applies.
The lag starts at the hover thrust when the aviary has `hover_at_start` set, otherwise at the first command (a vehicle
resting on the ground: zero thrust). Gazebo's motor model lags the rotor speed instead of the thrust; linearized around a
speed the two time constants are the same.
"""
import warnings
from pathlib import Path

import numpy as np

warnings.filterwarnings("ignore", module="gymnasium")
from gym_pybullet_drones.envs.CtrlAviary import CtrlAviary  # noqa: E402

HERE = Path(__file__).resolve().parent
LAG = (0.0125, 0.025)

# the gorge's airframe: the URDF that AirframeAviary loads, and its motor lag
AIRFRAMES = {
    "x500": dict(urdf=HERE / "x500" / "x500.urdf", lag=LAG),
}


class AirframeAviary(CtrlAviary):
    """CtrlAviary with a URDF from outside the package and an optional first-order motor lag."""

    def __init__(self, urdf, lag=None, **kw):
        self.urdf_path, self.lag = urdf, lag
        self.lag_thrust = None
        super().__init__(**kw)

    def _parseURDFParameters(self):
        # absolute: files('gym_pybullet_drones') / 'assets' / URDF is this path
        self.URDF = str(self.urdf_path)
        return super()._parseURDFParameters()

    def reset(self, *a, **kw):
        self.lag_thrust = None
        return super().reset(*a, **kw)

    def _physics(self, rpm, nth_drone):
        if self.lag is not None:
            cmd = self.KF * np.asarray(rpm, dtype=float) ** 2          # commanded thrust per propeller
            if self.lag_thrust is None:
                self.lag_thrust = (np.full(4, self.GRAVITY / 4) if getattr(self, "hover_at_start", False)
                                   else cmd.copy())
            up, down = self.lag
            tau = np.where(cmd > self.lag_thrust, up, down)
            self.lag_thrust = self.lag_thrust + (cmd - self.lag_thrust) * (1 - np.exp(-self.PYB_TIMESTEP / tau))
            rpm = np.sqrt(self.lag_thrust / self.KF)
        super()._physics(rpm, nth_drone)
