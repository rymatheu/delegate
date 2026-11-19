"""The plant: one X500 (`Plant`) or several (`FormationPlant`) in the gorge, stepped one 400 Hz tick at a time.

A tick takes the vehicle's motor commands (PWM in microseconds, ArduPilot's quad-X motor slots 0..3, which are PX4's
X500 rotor_0..3 in the same order and spins; or actuators in [0, 1]), holds them for the three 1200 Hz physics substeps
of the environment (gorge_aviary.GorgeAviary / FormationAviary: the X500 URDF with its first-order motor lag, the
gorge's collision bodies, ArduPilot's gravity), takes an IMU sample after each substep, then the slower sensors of the
new state (sensor_layer.Sensors: barometer and compass every 4th tick, GPS every 80th, RC every 8th). Nothing here is
specific to a flight controller; a controller's bridge encodes a `Sample` into its own input format.

Timing, the convention of the lock-step flight programs: `reset()` returns sample 0 (the vehicle resting on the floor:
one IMU sample repeated three times, the slow sensors of tick count 0); `tick(pwm)` with the controller's reply to
sample k returns sample k + 1 (the three IMU samples of the substeps just stepped, the slow sensors of tick count k + 1)
and the true state after the tick. The noise generator (seeded, or none) is drawn in exactly that order, so a flight is
deterministic for a given seed.

    from gorgesim.plant import Plant, FormationPlant
    p = Plant(seed=None)                         # loads (or builds, once) the gorge of seed 7
    s = p.reset()                                # Sample at t = 0
    s = p.tick([1500, 1500, 1500, 1500])         # one 400 Hz tick; s.t_us == 2500
    f = FormationPlant.for_plan("abreast")       # two vehicles at the plan's start sites
    s1, s2 = f.reset()
    s1, s2 = f.tick([pwm1, pwm2])

Poses for the cameras: `Plant(..., pose_ports=[P])` (FormationPlant: one port per vehicle) sends each vehicle's true
pose to its camera every 4th tick (udp_bridge.PoseSender, as sim/cameras.sh expects); it changes nothing the vehicles
see.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np

from . import simulator
from .motors import actuators_to_rpm, pwm_to_rpm
from .record import CLEAR_MAX, REC_EVERY
from .sensor_layer import BATTERY, Sensors
from .udp_bridge import PoseSender

PYB_HZ = 1200                          # physics rate: three substeps per tick
CTRL_HZ = simulator.CTRL_HZ            # 400 Hz ticks
STEP_US = simulator.STEP_US            # 2500 us per tick


@dataclass
class Sample:
    """What one vehicle's sensors give after a tick, and its true state (for records and cameras, not for the
    controller). Frames: NED world, FRD body; `pos_enu`, `quat_xyzw` are PyBullet's ENU world and FLU body."""
    t_us: int                          # simulated time at the end of the tick (0 at reset)
    imu: list                          # three ((ax, ay, az) m/s^2 specific force, (p, q, r) rad/s), FRD, one per substep
    baro: tuple | None                 # (pressure Pa, temperature degC), every 4th tick (100 Hz)
    mag: tuple | None                  # (x, y, z) mGauss, FRD body, minus the compass offsets, every 4th tick
    gps: tuple | None                  # (lat deg, lon deg, alt m AMSL, vn, ve, vd m/s), every 80th tick (5 Hz)
    rc: list | None                    # 16 RC channels (us; neutral sticks, throttle low), every 8th tick (50 Hz)
    battery: tuple                     # (volts, amps)
    pos_ned: np.ndarray                # true position, m, about the gorge origin (sim/world/origin.params)
    vel_ned: np.ndarray                # true velocity, m/s
    euler: tuple                       # true (roll, pitch, yaw), rad, ZYX of the FRD body in NED
    rates_frd: np.ndarray              # true body rates, rad/s
    quat_ned_frd: tuple                # true attitude (q1 scalar, q2, q3, q4), body FRD to NED
    pos_enu: np.ndarray = field(repr=False, default=None)     # PyBullet position (ENU)
    quat_xyzw: np.ndarray = field(repr=False, default=None)   # PyBullet quaternion (FLU body to ENU)
    actuators: list = field(default_factory=lambda: [0.0] * 4)  # the actuators applied in this tick, slot order


def _sample(t_us, imu, slow, state, obs_row, act):
    pos, vel, att, rates, _ = state
    return Sample(t_us=t_us, imu=list(imu), baro=slow.get("baro"), mag=slow.get("mag"), gps=slow.get("gps"),
                  rc=slow.get("rc"), battery=BATTERY, pos_ned=pos, vel_ned=np.asarray(vel), euler=att,
                  rates_frd=np.asarray(rates), quat_ned_frd=simulator.quat_ned_frd(obs_row[3:7]),
                  pos_enu=np.asarray(obs_row[0:3]), quat_xyzw=np.asarray(obs_row[3:7]), actuators=list(act))


def load_gorge(gorge=None):
    """The gorge of simulator.GORGE_SEED (built on first use, about 3 minutes, cached in sim/build/world-cache/)."""
    if gorge is not None:
        return gorge
    import gorge as G
    return G.Gorge(simulator.GORGE_SEED)


def home_of_origin():
    origin = simulator.gorge_origin()
    return (origin.lat_e7 / 1e7, origin.lon_e7 / 1e7, origin.alt_m)


class _Base:
    def _common(self, gorge, pyb_hz, pose_ports):
        if pyb_hz % CTRL_HZ:
            raise ValueError("pyb_hz must be a multiple of 400")
        self.g = load_gorge(gorge)
        self.pyb_hz = pyb_hz
        self.substeps = pyb_hz // CTRL_HZ
        self.home = home_of_origin()
        self.poses = [PoseSender(p) for p in pose_ports] if pose_ports else None
        self.k = 0
        self.obs = None

    # --- queries of the current state (record helpers, as the flight programs' track.csv) ---
    def clearance(self, i=0, reach=CLEAR_MAX):
        """Closest distance (m) from vehicle i's collision cylinder to every body of the gorge, up to `reach`."""
        import pybullet as pb
        d = self.env.DRONE_IDS[i]
        dist = [q[8] for b in self.env.world for q in pb.getClosestPoints(d, b, reach, physicsClientId=self.env.CLIENT)]
        return min(dist) if dist else reach

    def contacts(self, i=0, world_only=False):
        """Number of contact points of vehicle i (with the gorge only, if world_only)."""
        import pybullet as pb
        pts = pb.getContactPoints(bodyA=self.env.DRONE_IDS[i], physicsClientId=self.env.CLIENT)
        if world_only:
            ws = set(self.env.world)
            pts = [q for q in pts if q[2] in ws]
        return len(pts)

    def _send_poses(self, k):
        if self.poses is not None and k % REC_EVERY == 0:
            t = (k + 1) * STEP_US * 1e-6
            for i, ps in enumerate(self.poses):
                ps.send(t, self.obs[i][0:3], self.obs[i][3:7])

    def close(self):
        if self.env is not None:
            self.env.close()
            self.env = None
        for ps in self.poses or []:
            ps.close()


class Plant(_Base):
    """One X500 resting on the gorge floor at the gorge mission's start (Gorge.path[0], world ENU (0, 0)), level, nose
    north. seed: sensor noise seed (None: no noise). wind: (mean m/s, gust m/s) of wind.Wind (gust seed: seed or 0,
    plus 1000), or None. gorge: a loaded gorge.Gorge (default: load it). pose_ports: [port] for the camera."""

    def __init__(self, seed=None, wind=None, gorge=None, pyb_hz=PYB_HZ, pose_ports=None):
        self._common(gorge, pyb_hz, pose_ports)
        w = None
        if wind is not None:
            from wind import Wind
            w = Wind(self.g, wind[0], wind[1], (seed or 0) + 1000)
        self.seed, self.wind = seed, wind
        self.env = simulator.make_env(self.g, pyb_hz, w)
        self.sensors = None

    def reset(self) -> Sample:
        """Reset to rest on the floor (settled 0.25 s with the motors off); sample 0."""
        self.obs = simulator.reset_env(self.env)
        self.home_z = float(self.obs[0][2])
        self.sensors = Sensors(self.seed, 1.0 / self.pyb_hz, self.home)
        self.k = 0
        imu0 = self.sensors.imu(self.obs)
        slow = self.sensors.slow(0, self.obs)
        return _sample(0, [imu0] * self.substeps, slow, Sensors.state(self.obs), self.obs[0], [0.0] * 4)

    def tick(self, pwm=None, actuators=None) -> Sample:
        """One 400 Hz tick with the motor commands: pwm (at least four values, us; slot i -> (pwm - 1000) / 1000) or
        actuators (four values in [0, 1]). Returns the next sample."""
        if actuators is None:
            rpm, act = pwm_to_rpm(self.env, pwm)
        else:
            act = [min(1.0, max(0.0, float(a))) for a in actuators[:4]]
            rpm = actuators_to_rpm(self.env, act)
        imu = []
        for _ in range(self.substeps):
            self.obs, *_ = self.env.step(rpm.reshape(1, 4))
            imu.append(self.sensors.imu(self.obs))
        self._send_poses(self.k)
        self.k += 1
        slow = self.sensors.slow(self.k, self.obs)
        return _sample(self.k * STEP_US, imu, slow, Sensors.state(self.obs), self.obs[0], act)


class FormationPlant(_Base):
    """Several X500s in one gorge (gorge_aviary.FormationAviary: per-vehicle motor lag, no wind), each resting level on
    the floor at starts_xy[i] (ENU) with NED heading yaws_deg[i]. seeds: per-vehicle noise seed or None. Vehicles
    collide with the gorge and with each other."""

    def __init__(self, starts_xy, yaws_deg=None, seeds=None, gorge=None, pyb_hz=PYB_HZ, pose_ports=None):
        self._common(gorge, pyb_hz, pose_ports)
        self.n = len(starts_xy)
        self.seeds = list(seeds) if seeds is not None else [None] * self.n
        self.env = simulator.make_formation_env(self.g, pyb_hz, starts_xy, yaws_deg)
        self.sensors = None

    @classmethod
    def for_plan(cls, plan, reverse=None, seed=None, gorge=None, **kw):
        """Two vehicles at the start sites of formation plan `plan` ("abreast" or "staggered"; formation_plan.PLANS),
        a reversed vehicle (default: the plan's reverse flags; staggered: vehicle 2) facing against leg 1. seed: noise
        seed of vehicle 1, vehicle 2 gets seed + 100 (None: no noise). Also sets .routes, .lands, .offset, .reverse.
        Takes a few seconds (the level start sites are settled in PyBullet)."""
        import formation_plan as FP
        from .missions import leg_headings
        g = load_gorge(gorge)
        rev = tuple(int(x) for x in (FP.PLANS[plan]["reverse"] if reverse is None else reverse))
        c = FP.centre(g, plan)
        r1, r2, o, _ = FP.routes(g, plan, c)
        yaws = [float((leg_headings(r)[0] + 180.0) % 360.0) if rv else 0.0 for r, rv in zip((r1, r2), rev)]
        seeds = [None, None] if seed is None else [seed, seed + 100]
        self = cls([r1[0, :2], r2[0, :2]], yaws, seeds, gorge=g, **kw)
        self.routes, self.lands, self.offset, self.reverse = (r1, r2), FP.land_sites(g, r1, r2), np.asarray(o, float), rev
        return self

    def reset(self):
        """Reset all vehicles to rest; [sample 0 per vehicle]."""
        self.obs = simulator.reset_env(self.env)
        self.home_z = [float(self.obs[i][2]) for i in range(self.n)]
        self.sensors = [Sensors(s, 1.0 / self.pyb_hz, self.home) for s in self.seeds]
        self.k = 0
        out = []
        for i, S in enumerate(self.sensors):
            o = self.obs[i:i + 1]
            imu0 = S.imu(o)
            out.append((i, imu0))
        res = []
        for i, imu0 in out:
            o = self.obs[i:i + 1]
            slow = self.sensors[i].slow(0, o)
            res.append(_sample(0, [imu0] * self.substeps, slow, Sensors.state(o), self.obs[i], [0.0] * 4))
        return res

    def tick(self, pwms=None, actuators=None):
        """One 400 Hz tick of all vehicles: pwms[i] (us) or actuators[i] (in [0, 1]) per vehicle; [next sample]."""
        rpm = np.zeros((self.n, 4))
        acts = []
        for i in range(self.n):
            if actuators is None:
                r, a = pwm_to_rpm(self.env, pwms[i])
            else:
                a = [min(1.0, max(0.0, float(x))) for x in actuators[i][:4]]
                r = actuators_to_rpm(self.env, a)
            rpm[i] = r
            acts.append(a)
        imu = [[] for _ in range(self.n)]
        for _ in range(self.substeps):
            self.obs, *_ = self.env.step(rpm)
            for i, S in enumerate(self.sensors):
                imu[i].append(S.imu(self.obs[i:i + 1]))
        self._send_poses(self.k)
        self.k += 1
        res = []
        for i, S in enumerate(self.sensors):
            o = self.obs[i:i + 1]
            res.append(_sample(self.k * STEP_US, imu[i], S.slow(self.k, o), Sensors.state(o), self.obs[i], acts[i]))
        return res
