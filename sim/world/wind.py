"""Wind in the gorge and its aerodynamic force on the X500.

Mean flow (`Wind.mean_at`): along the local gorge axis, signed: MEAN > 0 blows up-gorge (north, a
daytime up-valley wind, a tailwind for a vehicle flying up the gorge), MEAN < 0 down-gorge. MEAN is
the speed at the reference height FLIGHT_H above the floor where the floor has the reference width
W_ref (the median floor width along the flight); elsewhere
  speed = |MEAN| * min(W_ref / W(y), CAP) * ln((h + Z0) / Z0) / ln((FLIGHT_H + Z0) / Z0),
continuity at constant depth (speed inversely proportional to the width, capped at CAP = 2) and a
logarithmic profile over the rough floor (roughness length Z0 = 0.1 m, boulders and shrubs; h the
height above the centerline floor, the profile factor capped at 1.6).

Turbulence (`Wind.step`): Dryden-style, three independent first-order shaping filters on white noise
(along the axis u, across v, vertical w), updated at the physics rate:
  g[k+1] = a g[k] + sigma sqrt(1 - a^2) n[k],  a = exp(-V dt / L),  n ~ N(0, 1) (seeded),
so each component is stationary with standard deviation sigma and correlation length L at the
advection speed V = max(local mean speed, 1 m/s) (frozen turbulence). Length scales: MIL-F-8785C low
altitude at h = 3.5 m (11.5 ft): L_u = h / (0.177 + 0.000823 h)^1.2 = 26 m, L_w = h = 3.5 m;
L_v = min(26 m, W(y)): the cross-gorge eddies are taken as no larger than the gorge (assumption).
Intensities: sigma_u = sigma_v = GUST, sigma_w = GUST / 1.96 (MIL-F-8785C: sigma_u / sigma_w =
1 / (0.177 + 0.000823 h)^0.4 = 1.96 at 11.5 ft).

Force (`aero_force`), from the air-relative velocity v_rel = v - w:
- rotor drag (PX4 gz MulticopterMotorModel, which the X500 model uses): each rotor adds
  -C_R |omega_i| v_rel_perp, v_rel_perp the component in the rotor plane, C_R = 8.06428e-05
  N/(m/s)/(rad/s) (rotorDragCoefficient of PX4-gazebo-models x500/model.sdf); at hover
  (omega = sqrt(m g / 4 / 8.54858e-06) = 769 rad/s) the lumped coefficient is 4 C_R omega =
  0.248 N/(m/s). The rotor speeds are those of the lagged thrust in the physics step;
- body drag: -1/2 rho CdA |v_rel| v_rel, rho = 1.16 kg/m^3 (dry air at 30 deg C, 1000 hPa),
  CdA = 0.04 m^2 (assumption: frontal area of the X500's plates, battery, arms, motors and legs about
  0.035 m^2 with Cd about 1.1), isotropic.
It acts at the center of mass (no moment; the rotor plane is 0.06 m above it).

`WindAviary` applies the force in `_physics` at 1200 Hz, after the motor lag and thrust of
run_leanfc.LeanfcAviary. With `wind=None` no force is applied at all and the physics is
LeanfcAviary's exactly: `python wind.py` checks this bit for bit by replaying a recorded command
sequence through both.
"""
import math
import sys
from pathlib import Path

import numpy as np
import pybullet as p

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from run_leanfc import LeanfcAviary  # noqa: E402

import gorge as G  # noqa: E402

C_R = 8.06428e-05          # N/(m/s)/(rad/s) per rotor
RHO, CDA = 1.16, 0.04      # kg/m^3, m^2
Z0, CAP, PROFILE_CAP = 0.1, 2.0, 1.6
L_U, L_W = 26.0, G.FLIGHT_H
SIGMA_W_RATIO = 1 / 1.96


def aero_force(v_rel, z_body, omega):
    """Aerodynamic force (world, N) for air-relative velocity v_rel (world), body z axis z_body
    (world) and rotor speeds omega (rad/s)."""
    v_rel = np.asarray(v_rel, float)
    perp = v_rel - (v_rel @ z_body) * z_body
    return -C_R * np.sum(np.abs(omega)) * perp - 0.5 * RHO * CDA * np.linalg.norm(v_rel) * v_rel


class Wind:
    def __init__(self, gorge, mean, gust, seed, dt=1 / 1200):
        self.g, self.mean, self.gust, self.dt = gorge, float(mean), float(gust), dt
        self.rng = np.random.default_rng(seed)
        ys = np.linspace(0, G.Y_END, 721)
        self.w_ref = float(np.median(gorge.width_at(ys)))
        self.state = np.zeros(3)
        self.norm = math.log((G.FLIGHT_H + Z0) / Z0)

    def mean_at(self, pos):
        x, y, z = pos
        h = max(z - self.g.floor_c(y), 0.0)
        prof = min(math.log((h + Z0) / Z0) / self.norm, PROFILE_CAP)
        speed = self.mean * min(self.w_ref / self.g.width_at(y), CAP) * prof
        return speed * self.g.axis_dir(y)

    def step(self, pos):
        """Wind vector (world, m/s) at pos, advancing the gust filters by dt."""
        m = self.mean_at(pos)
        y = pos[1]
        V = max(np.linalg.norm(m), 1.0)
        L = np.array([L_U, min(L_U, self.g.width_at(y)), L_W])
        sig = self.gust * np.array([1.0, 1.0, SIGMA_W_RATIO])
        a = np.exp(-V * self.dt / L)
        self.state = a * self.state + sig * np.sqrt(1 - a * a) * self.rng.normal(size=3)
        ax = self.g.axis_dir(y)
        across = np.array([ax[1], -ax[0], 0.0])
        return m + self.state[0] * ax + self.state[1] * across + self.state[2] * np.array([0, 0, 1.0])


class WindAviary(LeanfcAviary):
    """LeanfcAviary with the aerodynamic force of `wind` (None: none) applied every physics substep.
    Logs the last wind vector and force (world ENU) in self.wind_last, self.force_last."""

    def __init__(self, wind=None, **kw):
        self.wind = wind
        self.wind_last, self.force_last = np.zeros(3), np.zeros(3)
        super().__init__(**kw)

    def _physics(self, rpm, nth_drone):
        super()._physics(rpm, nth_drone)
        if self.wind is None:
            return
        d, c = self.DRONE_IDS[nth_drone], self.CLIENT
        pos, orn = p.getBasePositionAndOrientation(d, physicsClientId=c)
        vel, _ = p.getBaseVelocity(d, physicsClientId=c)
        thrust = self.lag_thrust if self.lag is not None else self.KF * np.asarray(rpm, float) ** 2
        omega = np.sqrt(np.maximum(thrust, 0) / self.KF) * 2 * np.pi / 60      # KF is N/RPM^2
        z_body = np.array(p.getMatrixFromQuaternion(orn)).reshape(3, 3)[:, 2]
        w = self.wind.step(pos)
        f = aero_force(np.asarray(vel) - w, z_body, omega)
        p.applyExternalForce(d, -1, f.tolist(), list(pos), p.WORLD_FRAME, physicsClientId=c)
        self.wind_last, self.force_last = w, f


def check_wind_off(csv):
    """Replay the motor commands of a recorded run through run_leanfc's LeanfcAviary (its make_env)
    and through fly_gorge's GorgeAviary with wind None: every state must be bitwise equal."""
    import run_leanfc as R
    import fly_gorge as FG
    from run_copter import reset_env, actuators_to_rpm
    d = np.genfromtxt(csv, delimiter=",", names=True)
    meta = __import__("json").loads(Path(csv).with_suffix(".json").read_text())
    p0 = meta["start"]
    m = np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]])
    envs = [R.make_env("x500", (0.0125, 0.025), p0), FG.make_env(G.Gorge(meta["gorge_seed"]), None, p0)]
    obs = [reset_env(e) for e in envs]
    worst = 0.0
    for k in range(len(m)):
        obs = [e.step(actuators_to_rpm(e, m[k]).reshape(1, 4))[0] for e in envs]
        worst = max(worst, float(np.abs(obs[0] - obs[1]).max()))
    for e in envs:
        e.close()
    print(f"wind off vs run_leanfc physics, {len(m)} ticks of {csv}: max |state difference| = {worst!r}")
    return worst == 0.0


if __name__ == "__main__":
    ok = check_wind_off(sys.argv[1] if len(sys.argv) > 1 else str(Path(__file__).parent / "out/runs/off/flight.csv"))
    sys.exit(0 if ok else 1)
