"""The gym-pybullet-drones environments of the gorge: one vehicle (`GorgeAviary`) or several (`FormationAviary`).

`GorgeAviary`: wind.WindAviary (airframes.AirframeAviary: URDF from outside the package, first-order motor lag; and the
optional aerodynamic force of wind.Wind) in the gorge. BaseAviary._housekeeping, which loads pybullet_data's plane.urdf,
is replaced by the same housekeeping without the ground plane (counters, buffers, gravity, time step, the vehicles), then
the gorge's collision bodies are loaded (gorge.Gorge.load "physics": concave terrain trimesh, convex boulders, compounds
of convex hulls for rocks and vegetation); their body ids are in `self.world`.

`FormationAviary`: GorgeAviary with the motor lag and the wind kept per vehicle (AirframeAviary and WindAviary keep one
state for the whole aviary, which is right for one vehicle only); with one vehicle it is GorgeAviary bit for bit. One
PyBullet world holds the gorge and all vehicles, so contact between the vehicles and with the terrain is PyBullet's own.
Not modeled: any aerodynamic interaction between the vehicles. `Physics.PYB` applies thrust and drag torque only; the
package's downwash model (`Physics.PYB_DW`) is not used, and the X500 URDF has zero downwash coefficients. The vehicles
meet only through contact of their collision cylinders (radius 0.25 m, 0.22 m tall; the X500's rotor tips reach 0.386 m
from the centre, so the cylinders touch only at a centre distance below 0.5 m, rotor discs could touch below 0.77 m).

FCOLS: the columns of a two-vehicle record (time, centre distance, closest distance of the two collision bodies, contact
points vehicle-vehicle, vehicle 1-world and vehicle 2-world, each vehicle's clearance).
"""
import time
from importlib.resources import files

import numpy as np
import pybullet as p
from gym_pybullet_drones.envs.BaseAviary import BaseAviary

from wind import WindAviary, aero_force

FCOLS = "t dist gap contact_vv contact_v1 contact_v2 clear1 clear2".split()


class GorgeAviary(WindAviary):
    """WindAviary in the gorge: BaseAviary._housekeeping's counters, buffers, gravity, time step and
    vehicle, without the ground plane, then the gorge's collision bodies."""

    def __init__(self, gorge, **kw):
        self.gorge = gorge
        super().__init__(**kw)

    def _housekeeping(self):
        n = self.NUM_DRONES
        self.RESET_TIME, self.step_counter, self.first_render_call = time.time(), 0, True
        self.X_AX, self.Y_AX, self.Z_AX, self.GUI_INPUT_TEXT = (-1 * np.ones(n) for _ in range(4))
        self.USE_GUI_RPM, self.last_input_switch = False, 0
        self.last_clipped_action, self.gui_input = np.zeros((n, 4)), np.zeros(4)
        self.pos, self.quat, self.rpy = np.zeros((n, 3)), np.zeros((n, 4)), np.zeros((n, 3))
        self.vel, self.ang_v = np.zeros((n, 3)), np.zeros((n, 3))
        c = self.CLIENT
        p.setGravity(0, 0, -self.G, physicsClientId=c)
        p.setRealTimeSimulation(0, physicsClientId=c)
        p.setTimeStep(self.PYB_TIMESTEP, physicsClientId=c)
        self.PLANE_ID = None
        self.DRONE_IDS = np.array([p.loadURDF(str(files('gym_pybullet_drones') / 'assets' / self.URDF), self.INIT_XYZS[i, :],
                                              p.getQuaternionFromEuler(self.INIT_RPYS[i, :]),
                                              flags=p.URDF_USE_INERTIA_FROM_FILE, physicsClientId=c) for i in range(n)])
        self.world = self.gorge.load(c, "physics")


class FormationAviary(GorgeAviary):
    """GorgeAviary with the motor lag and the wind kept per vehicle."""

    def __init__(self, gorge, winds=None, **kw):
        self.winds = winds
        self.lag_thr = None
        self.wind_v, self.force_v = None, None
        super().__init__(gorge, wind=None, **kw)

    def reset(self, *a, **kw):
        self.lag_thr = [None] * self.NUM_DRONES
        self.wind_v, self.force_v = np.zeros((self.NUM_DRONES, 3)), np.zeros((self.NUM_DRONES, 3))
        return super().reset(*a, **kw)

    def _physics(self, rpm, i):
        if self.lag is not None:
            cmd = self.KF * np.asarray(rpm, dtype=float) ** 2
            if self.lag_thr[i] is None:
                self.lag_thr[i] = np.full(4, self.GRAVITY / 4) if getattr(self, "hover_at_start", False) else cmd.copy()
            up, down = self.lag
            tau = np.where(cmd > self.lag_thr[i], up, down)
            self.lag_thr[i] = self.lag_thr[i] + (cmd - self.lag_thr[i]) * (1 - np.exp(-self.PYB_TIMESTEP / tau))
            rpm = np.sqrt(self.lag_thr[i] / self.KF)
        BaseAviary._physics(self, rpm, i)
        if self.winds is None or self.winds[i] is None:
            return
        d, c = self.DRONE_IDS[i], self.CLIENT
        pos, orn = p.getBasePositionAndOrientation(d, physicsClientId=c)
        vel, _ = p.getBaseVelocity(d, physicsClientId=c)
        thrust = self.lag_thr[i] if self.lag is not None else self.KF * np.asarray(rpm, float) ** 2
        omega = np.sqrt(np.maximum(thrust, 0) / self.KF) * 2 * np.pi / 60
        z_body = np.array(p.getMatrixFromQuaternion(orn)).reshape(3, 3)[:, 2]
        w = self.winds[i].step(pos)
        f = aero_force(np.asarray(vel) - w, z_body, omega)
        p.applyExternalForce(d, -1, f.tolist(), list(pos), p.WORLD_FRAME, physicsClientId=c)
        self.wind_v[i], self.force_v[i] = w, f
