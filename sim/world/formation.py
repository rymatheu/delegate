"""Two X500s in one gorge world, each with its own leanfc controller: the formation flights.

    python formation.py --plan abreast|staggered [--noise field|none] [--seed N] [--wind MEAN GUST]
                        [--skew S] [--cameras on|off] [--out DIR]                        # batch (default)
    python formation.py --plan PLAN --session [--mav-port 14550] [--pose-ports 14601 14603]
                        [--realtime 1] [--noise field] [--seed N] [--wind MEAN GUST] [--out DIR]

One PyBullet world (gym-pybullet-drones, `Physics.PYB`, 1200 Hz under the 400 Hz control step) holds
the gorge's collision bodies and both vehicles, so contact between the vehicles and with the terrain
is PyBullet's own. Everything per vehicle is run_leanfc's (imported, unmodified): the sensor layer
(`Sensors`, `Noise`; vehicle 2 draws from seed + 100), the X500 URDF and its motor lag, the controller
protocol (one line per tick, `.lake/build/bin/leanfc`, the current build), and wind.py's aerodynamic
force (`--wind MEAN GUST`; each vehicle its own gust process, seeds seed + 1000 and seed + 1100: the
gusts at the two vehicles are uncorrelated, which overstates their relative motion and is the
conservative choice for the separation). `FormationAviary` keeps the motor lag and the wind per
vehicle (LeanfcAviary and WindAviary keep one state for the whole aviary, which is right for one
vehicle only); with one vehicle it is GorgeAviary bit for bit (`--self-check`).

Not modeled: any aerodynamic interaction between the vehicles. `Physics.PYB` applies thrust and
drag torque only; the package's downwash model (`Physics.PYB_DW`, `_downwash`) is not used, and the
X500 URDF has zero downwash coefficients. The vehicles meet only through contact of their collision
cylinders (radius 0.25 m, 0.22 m tall; the X500's rotor tips reach 0.386 m from the centre, so the
cylinders touch only at a centre distance below 0.5 m, rotor discs could touch below 0.77 m).

Plans and routes: formation_plan.py (vehicle 2's route = vehicle 1's + one offset vector).

Batch (default, no MAVLink, as fast as possible, deterministic): each vehicle starts in the air,
hovering at its route's first point, armed in AUTO (the controller's batch start, 400 calibration
samples), nose north, and flies its overlay `formation-PLAN-vN-air.params` after x500.params (and
mocap.params with `--noise none`). `--skew S`: vehicle 2 starts S s after vehicle 1 (S < 0: vehicle 1
starts |S| s after vehicle 2); until its start a vehicle is held at its start point (pose reset after
every physics step, hover thrust), and its controller and sensors start at its start, exactly as
they would at t = 0. The run ends 2 s after both navigators complete, at any contact (vehicle with
vehicle, terrain or boulder), or at the time limit (60 s + |S|).

Session (`--session`, real time, MAVLink): both vehicles rest on the gorge floor at their routes'
starts (formation-PLAN-vN-ground.params after x500.params and ground.params), disarmed; controller k
runs with `--ground --mav --sysid k` to the ground station's port; the true pose of vehicle k is sent
at 100 Hz to 127.0.0.1:POSE_PORT_k for its camera payload (camera_component.py). Ends on SIGINT or
SIGTERM or after --seconds; contacts do not end it.

Records every tick from the simulator's truth (OUT/formation.csv): centre distance, the closest
distance between the two collision bodies, contact points vehicle-vehicle and vehicle-world, each
vehicle's clearance (closest distance of its collision body to terrain and boulders, up to 4 m, as
fly_gorge.py measures it; every tick in batch, every 4th tick in the session, where the terrain query
costs 0.32 ms per vehicle: `--clear-every`, NaN in between); per vehicle OUT/vN.csv (run_leanfc's columns, the heading setpoint, with
--session the vehicle columns, then wind w_n w_e w_d, aerodynamic force f_n f_e f_d, clearance) with
a JSON sidecar; OUT/formation.json (configuration, outcome, the summary of `summarize`).
"""
import argparse
import contextlib
import io
import json
import math
import signal
import socket
import struct
import subprocess
import sys
import time
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent))
import run_leanfc as R  # noqa: E402
from run_copter import place, actuators_to_rpm, SpecificForce, enu_state_to_ned, quat_ned_frd, SETTLE_S  # noqa: E402
from gym_pybullet_drones.envs.BaseAviary import BaseAviary  # noqa: E402

import geo  # noqa: E402
import gorge as G  # noqa: E402
import gorge_plan  # noqa: E402
import formation_plan as FP  # noqa: E402
from fly_gorge import GorgeAviary  # noqa: E402
from wind import Wind, aero_force  # noqa: E402

LAG = (0.0125, 0.025)
CLEAR_MAX = 4.0
POSE_FMT = "<Idd3d4d"          # gorge_session.POSE_FMT
BIN = ROOT / ".lake/build/bin/leanfc"
FCOLS = "t dist gap contact_vv contact_v1 contact_v2 clear1 clear2".split()
TURN_DONE_DEG = 5.0          # the rear vehicle's initial turn is done when its heading error first falls below this


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


def make_env(g, winds, starts_ned, ground):
    """FormationAviary with len(starts_ned) X500s (run_leanfc's constants), placed as run_copter.place
    places one: level, nose north; in the air at rest (hover thrust held) or resting on the floor."""
    n = len(starts_ned)
    with contextlib.redirect_stdout(io.StringIO()):
        env = FormationAviary(g, winds=winds, urdf=R.AIRFRAMES["x500"]["urdf"], lag=LAG,
                              drone_model=R.DroneModel.CF2X, num_drones=n, physics=R.Physics.PYB,
                              pyb_freq=R.PYB_HZ, ctrl_freq=R.CTRL_HZ, gui=False, record=False, obstacles=False,
                              user_debug_gui=False, output_folder=str(HERE / "out" / "pyb"))
    env.G = R.GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    env.rest_alt = 0.0
    xyz, rpy = [], []
    for (nn, ee, dd) in starts_ned:
        place(env, (nn, ee, None if ground else dd), (0.0, 0.0, 0.0), "hover")
        xyz.append(env.INIT_XYZS[0].copy())
        if ground:
            xyz[-1][2] = gorge_plan.start_rest_z(g, np.array([ee, nn])) + 0.005
        rpy.append(env.INIT_RPYS[0].copy())
    env.INIT_XYZS, env.INIT_RPYS = np.array(xyz), np.array(rpy)
    return env


def reset(env):
    """run_copter.reset_env for every vehicle: no PyBullet velocity damping; settle on the ground."""
    obs, _ = env.reset()
    for d in env.DRONE_IDS:
        p.changeDynamics(d, -1, linearDamping=0.0, angularDamping=0.0, physicsClientId=env.CLIENT)
    if env.on_ground_at_start:
        for _ in range(int(SETTLE_S * R.CTRL_HZ)):
            obs, *_ = env.step(np.zeros((env.NUM_DRONES, 4)))
    return obs


def state_of(obs_i, sf, env):
    """run_copter.sim_state for one vehicle's row of the observation."""
    pos, vel, att, rates = enu_state_to_ned(obs_i[0:3], obs_i[3:7], obs_i[10:13], obs_i[13:16])
    quat = quat_ned_frd(obs_i[3:7])
    acc = sf.update(vel, env.on_ground_at_start or getattr(env, "hover_at_start", False))
    return pos, vel, acc, quat, att, rates


def enu_to_ned(v):
    return [v[1], v[0], -v[2]]


def param_files(plan, k, noise, session, plans_dir):
    files = [ROOT / "params/x500.params"]
    if session:
        files.append(ROOT / "params/ground.params")
    if noise == "none":
        files.append(ROOT / "params/mocap.params")
    files.append(Path(plans_dir) / f"formation-{plan}-v{k}-{'ground' if session else 'air'}.params")
    return files


def run(a):
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    plans_dir = out / "plans"
    files0 = [ROOT / "params/x500.params", ROOT / "params/ground.params"]     # the origin of the plan files
    origin = geo.Origin.from_params(files0, a.origin)
    info = FP.write_all(g, origin, plans_dir)[a.plan]
    nominal = float(np.linalg.norm(info["offset_enu"]))
    files = [param_files(a.plan, k, a.noise, a.session, plans_dir) for k in (1, 2)]
    vals = [R.read_params(f) for f in files]
    nlegs = [len(v[1]) for v in vals]
    fix_every = int(round(vals[0][0]["dtFix"] / vals[0][0]["dt"]))
    starts = [(v[0]["start.x"], v[0]["start.y"], v[0]["start.z"]) for v in vals]
    winds = [Wind(g, a.wind[0], a.wind[1], a.seed + 1000 + 100 * k) for k in range(2)] if a.wind else None
    env = make_env(g, winds, starts, a.session)
    obs = reset(env)
    drones = list(env.DRONE_IDS)
    world = dict(env.world)
    statics = list(world)
    noise = R.Noise(0, 0, 0, 0, 0, 0, 0, 0) if a.noise == "none" else R.Noise()
    sens = [R.Sensors(noise, a.seed + 100 * k) for k in range(2)]
    sfs = [SpecificForce(env.G, 1.0 / R.CTRL_HZ) for _ in range(2)]
    seconds = a.seconds if a.seconds is not None else (7200.0 if a.session else 60.0 + abs(a.skew))
    delay = [max(0.0, -a.skew), max(0.0, a.skew)] if not a.session else [0.0, 0.0]
    k_start = [int(round(d * R.CTRL_HZ)) for d in delay]
    hold = [p.getBasePositionAndOrientation(d, physicsClientId=env.CLIENT) for d in drones]
    n_veh = 4 if a.session else 0
    procs = []
    for k in range(2):
        cmd = [str(a.bin), *R.param_args(files[k]), "--trace", "--bits"]
        if a.session:
            cmd += ["--ground", "--trace-vehicle", "--calibrate", "0", "--mav", "--port", str(a.mav_port),
                    "--sysid", str(k + 1), "--log", str(out / f"vehicle{k + 1}.log")]
            if a.origin:
                cmd += ["--origin", *a.origin]
        else:
            cmd += ["--calibrate", str(R.CAL_SAMPLES)]
        # own session: a Ctrl-C to the launcher's process group stops this loop, which then closes the
        # controllers' input (they exit at its end) after writing the records
        procs.append(subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1,
                                      start_new_session=True))

    def calibrate(k):
        """The batch start's 400 at-rest samples (true rates 0, specific force (0, 0, -g))."""
        pos, vel, _, _ = enu_state_to_ned(obs[k][0:3], obs[k][3:7], obs[k][10:13], obs[k][13:16])
        q0 = quat_ned_frd(obs[k][3:7])
        for _ in range(R.CAL_SAMPLES):
            procs[k].stdin.write(R.line_of(sens[k].sample(pos, vel, (0.0, 0.0, -env.G), q0, np.zeros(3), False)))
        procs[k].stdin.flush()
        if procs[k].stdout.readline().strip() != "calibrated":
            raise RuntimeError(f"controller {k + 1} did not acknowledge the calibration")

    started = [False, False]
    pose_socks = None
    if a.session and a.pose_ports:
        pose_socks = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    wall = []
    stop = {"now": False}

    def on_signal(*_):
        stop["now"] = True
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    rows = [[], []]
    frows = []
    legs = [0, 0]
    done_at, outcome, contact = None, "time limit", None
    hover = np.full(4, env.HOVER_RPM)
    t0 = time.time()
    t_pace = time.monotonic()
    n = int(round(seconds * R.CTRL_HZ))
    replies = [None, None]
    try:
        for k in range(n):
            if stop["now"]:
                outcome = "stopped"
                break
            active = []
            for v in range(2):
                if not started[v] and k >= k_start[v]:
                    started[v] = True
                    if not a.session:
                        calibrate(v)
                if started[v]:
                    active.append(v)
            st = [None, None]
            for v in active:
                st[v] = state_of(obs[v], sfs[v], env)
            if a.realtime:
                late = t_pace + k / (R.CTRL_HZ * a.realtime) - time.monotonic()
                if late > 0:
                    time.sleep(late)
            for v in active:
                pos, vel, acc, quat, _, rates = st[v]
                procs[v].stdin.write(R.line_of(sens[v].sample(pos, vel, acc, quat, rates, (k - k_start[v]) % fix_every == 0)))
                procs[v].stdin.flush()
            rpm = np.tile(hover, (2, 1))
            lines_in = [(v, procs[v].stdout.readline()) for v in active]
            if any(not ln for _, ln in lines_in):
                outcome = "controller ended"
                break
            for v, ln in lines_in:
                replies[v] = R.parse_reply(ln, 0, n_veh)
                rpm[v] = actuators_to_rpm(env, replies[v][:4])
            obs, *_ = env.step(rpm)
            held = [v for v in range(2) if not started[v]]
            for v in held:
                p.resetBasePositionAndOrientation(drones[v], *hold[v], physicsClientId=env.CLIENT)
                p.resetBaseVelocity(drones[v], [0, 0, 0], [0, 0, 0], physicsClientId=env.CLIENT)
            if held:
                env._updateAndStoreKinematicInformation()
                obs = env._computeObs()
            tk = (k + 1) / R.CTRL_HZ
            c = env.CLIENT
            clear = [float("nan"), float("nan")]
            if (k + 1) % a.clear_every == 0:
                for v in range(2):
                    dist = [q[8] for b in statics for q in p.getClosestPoints(drones[v], b, CLEAR_MAX, physicsClientId=c)]
                    clear[v] = min(dist) if dist else CLEAR_MAX
            gap = p.getClosestPoints(drones[0], drones[1], 10.0, physicsClientId=c)
            gap = min(q[8] for q in gap) if gap else 10.0
            cvv = len(p.getContactPoints(bodyA=drones[0], bodyB=drones[1], physicsClientId=c))
            cw = [len([q for q in p.getContactPoints(bodyA=drones[v], physicsClientId=c) if q[2] in world]) for v in range(2)]
            pe = [np.array(obs[v][0:3]) for v in range(2)]
            frows.append([tk, float(np.linalg.norm(pe[1] - pe[0])), gap, cvv, cw[0], cw[1], clear[0], clear[1]])
            for v in active:
                r = replies[v]
                p1, v1, _, _ = enu_state_to_ned(obs[v][0:3], obs[v][3:7], obs[v][10:13], obs[v][13:16])
                q1 = quat_ned_frd(obs[v][3:7])
                veh = r[len(r) - n_veh:] if n_veh else []
                hsp = r[18:len(r) - n_veh]
                rows[v].append([tk - 1 / R.CTRL_HZ, *p1, *v1, *q1, *r[4:17], legs[v], *r[:4], *hsp, *veh,
                                *enu_to_ned(env.wind_v[v]), *enu_to_ned(env.force_v[v]), clear[v]])
                legs[v] = r[17]
            if pose_socks is not None and (k + 1) % 4 == 0:
                for v in range(2):
                    pos_, orn_ = p.getBasePositionAndOrientation(drones[v], physicsClientId=c)
                    pose_socks.sendto(struct.pack(POSE_FMT, k + 1, tk, time.time(), *pos_, *orn_), ("127.0.0.1", a.pose_ports[v]))
            if a.session and (k + 1) % 40 == 0:
                wall.append((k + 1, time.monotonic()))
            if not a.session:
                if cvv or cw[0] or cw[1]:
                    cp = p.getContactPoints(bodyA=drones[0], bodyB=drones[1], physicsClientId=c) or \
                        [q for v in range(2) for q in p.getContactPoints(bodyA=drones[v], physicsClientId=c)]
                    q = min(cp, key=lambda q: q[8])
                    contact = dict(t=tk, bodies=[int(q[1]), int(q[2])], kind="vehicle-vehicle" if cvv else
                                   f"vehicle {drones.index(q[1]) + 1}-{world.get(q[2], ('?', -1))[0]}",
                                   pos_enu=list(q[5]), depth=float(q[8]), normal_force=float(q[9]))
                    outcome = "contact"
                    break
                if all(started) and legs[0] >= nlegs[0] and legs[1] >= nlegs[1] and done_at is None:
                    done_at = tk
                if done_at is not None and tk >= done_at + 2.0:
                    outcome = "completed"
                    break
    finally:
        for pr in procs:
            try:
                pr.stdin.close()
            except Exception:
                pass
        for pr in procs:
            try:
                pr.wait(10)
            except subprocess.TimeoutExpired:
                pr.kill()
        env.close()
    wall_s = time.time() - t0

    base = R.COLS + R.HSP_COLS + (R.VEH_COLS if a.session else []) + "w_n w_e w_d f_n f_e f_d clearance".split()
    for v in range(2):
        with open(out / f"v{v + 1}.csv", "w") as f:
            f.write(",".join(base) + "\n")
            nint = {24} | (set(range(len(R.COLS) + 2, len(R.COLS) + 2 + n_veh)) if n_veh else set())
            for row in rows[v]:
                f.write(",".join(str(int(x)) if i in nint else repr(float(x)) for i, x in enumerate(row)) + "\n")
        meta = dict(vehicle="x500", sysid=v + 1, params=[str(x) for x in files[v]], noise=a.noise, seed=a.seed + 100 * v,
                    fix_hz=1.0 / vals[v][0]["dtFix"], motor_lag=list(LAG), start=list(starts[v]), start_delay_s=delay[v],
                    waypoints=vals[v][1], legs=vals[v][0]["legs"], radius=vals[v][0]["nav.radius"], gorge_seed=a.gorge_seed,
                    yaw_reverse=int(vals[v][0]["nav.yawReverse"]), session=a.session)
        (out / f"v{v + 1}.json").write_text(json.dumps(meta, indent=1) + "\n")
    with open(out / "formation.csv", "w") as f:
        f.write(",".join(FCOLS) + "\n")
        for r in frows:
            f.write(",".join(str(int(x)) if 3 <= i <= 5 else repr(float(x)) for i, x in enumerate(r)) + "\n")
    meta = dict(plan=a.plan, session=a.session, noise=a.noise, seed=a.seed, wind=a.wind, skew_s=a.skew, gorge_seed=a.gorge_seed,
                offset_enu=info["offset_enu"], nominal_distance=nominal, reverse=info["reverse"], outcome=outcome,
                completed_at=done_at, contact=contact, seconds=len(frows) / R.CTRL_HZ, wall_s=round(wall_s, 1),
                downwash_modeled=False)
    if a.session and len(wall) > 2:
        w = np.array(wall, float)
        w = w[w[:, 0] >= 2 * R.CTRL_HZ]
        sim = (w[:, 0] - w[0, 0]) / R.CTRL_HZ
        wl = w[:, 1] - w[0, 1]
        lag = (wl - sim) - (wl - sim).min()
        per_s = [(sim[j] - sim[i]) / (wl[j] - wl[i]) for i, j in zip(range(0, len(w) - 10, 10), range(10, len(w), 10))]
        meta["realtime"] = dict(simulated_s=float(sim[-1]), wall_s=float(wl[-1]), rtf=float(sim[-1] / wl[-1]),
                                lag_max_s=float(lag.max()), rtf_1s_min=float(min(per_s)) if per_s else None,
                                seconds_below_0_98=int(sum(r < 0.98 for r in per_s)), seconds=len(per_s))
    (out / "formation.json").write_text(json.dumps(meta, indent=1) + "\n")
    if not a.session:
        meta["summary"] = summarize(out)
        (out / "formation.json").write_text(json.dumps(meta, indent=1) + "\n")
    print(f"{out}: {a.plan}, {outcome} at t = {len(frows) / R.CTRL_HZ:.2f} s, noise {a.noise}, seed {a.seed}, wind {a.wind}, "
          f"skew {a.skew} s, wall {wall_s:.1f} s" + (f", contact {contact}" if contact else ""), flush=True)
    return meta


# --- metrics ------------------------------------------------------------------------------------------------

def heading_error(d, reverse, vmin=0.5):
    """Per tick: angle (deg) between the true heading (body x, horizontal) and the direction of travel
    (horizontal velocity; its opposite with `reverse`), NaN below vmin m/s horizontal."""
    yaw = np.arctan2(2 * (d["q_w"] * d["q_z"] + d["q_x"] * d["q_y"]), 1 - 2 * (d["q_y"] ** 2 + d["q_z"] ** 2))
    trav = np.arctan2(d["v_e"], d["v_n"]) + (math.pi if reverse else 0.0)
    e = np.degrees(np.abs((yaw - trav + math.pi) % (2 * math.pi) - math.pi))
    return np.where(np.hypot(d["v_n"], d["v_e"]) > vmin, e, np.nan)


def summarize(out, route_mask=None):
    """Separation, contacts, clearance, tracking and heading of a formation run directory. `route_mask`
    (per formation.csv row): the route phase; default (batch): both navigators started and neither done."""
    out = Path(out)
    fm = json.loads((out / "formation.json").read_text()) if (out / "formation.json").exists() else {}
    f = np.genfromtxt(out / "formation.csv", delimiter=",", names=True)
    ds = [np.genfromtxt(out / f"v{v}.csv", delimiter=",", names=True) for v in (1, 2)]
    ms = [json.loads((out / f"v{v}.json").read_text()) for v in (1, 2)]
    t = f["t"]
    res = {}
    if route_mask is None:
        on = []
        for d, m in zip(ds, ms):
            leg = np.zeros(len(t), int)
            tt = d["t"] + 1 / R.CTRL_HZ                         # vN.csv rows carry the start of the tick
            idx = np.searchsorted(t, tt - 1e-9)
            leg[:] = -1
            leg[idx] = d["leg"].astype(int)
            on.append((leg >= 0) & (leg < len(m["waypoints"])))
        route_mask = on[0] & on[1]
    nominal = float(np.linalg.norm(fm.get("offset_enu", [0, 0, 0]))) if fm else float("nan")
    dr = f["dist"][route_mask]
    res["nominal_m"] = nominal
    res["route_s"] = float(route_mask.sum() / R.CTRL_HZ)
    if len(dr):
        dev = np.abs(dr - nominal)
        res["dist_route"] = dict(min=float(dr.min()), mean=float(dr.mean()), max=float(dr.max()),
                                 dev_p95=float(np.percentile(dev, 95)), dev_max=float(dev.max()),
                                 t_min=float(t[route_mask][np.argmin(dr)]))
    res["dist_all"] = dict(min=float(f["dist"].min()), max=float(f["dist"].max()), t_min=float(t[np.argmin(f["dist"])]))
    res["gap_min"] = float(f["gap"].min())
    res["contacts"] = dict(vv=int((f["contact_vv"] > 0).sum()), v1=int((f["contact_v1"] > 0).sum()), v2=int((f["contact_v2"] > 0).sum()))
    for v, (d, m) in enumerate(zip(ds, ms), start=1):
        pos = np.column_stack([d["p_n"], d["p_e"], d["p_d"]])
        sp = np.column_stack([d["sp_n"], d["sp_e"], d["sp_d"]])
        trk = np.linalg.norm(pos - sp, axis=1)
        he = heading_error(d, m.get("yaw_reverse", 0))
        legs = d["leg"].astype(int)
        nl = len(m["waypoints"])
        rt = (legs >= 0) & (legs < nl)
        h_route = he[rt & np.isfinite(he)]
        h_after = None
        cl = np.where(np.isfinite(d["clearance"]), d["clearance"], np.inf)
        # the turn to the heading: first time after which the error stays below 10 deg while moving
        moving = np.isfinite(he)
        bad = moving & (he > 10.0)
        k_ok = (np.nonzero(bad)[0].max() + 1) if bad.any() else 0
        # after the initial turn: from the first time the error falls below TURN_DONE_DEG on
        k_in = int(np.argmax(moving & (he < TURN_DONE_DEG))) if (moving & (he < TURN_DONE_DEG)).any() else len(d) - 1
        sel = rt & moving & (np.arange(len(d)) >= k_in)
        h_after = he[sel]
        res[f"v{v}"] = dict(clear_min=float(cl.min()), clear_min_north=float(d["p_n"][np.argmin(cl)]),
                            track_max=float(trk.max()), track_rms=float(np.sqrt((trk ** 2).mean())),
                            heading_err_route=dict(max=float(h_route.max()) if len(h_route) else None,
                                                   p95=float(np.percentile(h_route, 95)) if len(h_route) else None,
                                                   rms=float(np.sqrt((h_route ** 2).mean())) if len(h_route) else None),
                            heading_err_after_turn=dict(from_t=float(d["t"][k_in]), from_north=float(d["p_n"][k_in]),
                                                        max=float(h_after.max()) if len(h_after) else None,
                                                        p95=float(np.percentile(h_after, 95)) if len(h_after) else None,
                                                        rms=float(np.sqrt((h_after ** 2).mean())) if len(h_after) else None),
                            heading_within_10deg_from=dict(t=float(d["t"][min(k_ok, len(d) - 1)]),
                                                           north=float(d["p_n"][min(k_ok, len(d) - 1)])),
                            legs_done=int(legs.max()), legs=nl,
                            tilt_max_deg=float(np.degrees(np.arccos(np.clip(1 - 2 * (d["q_x"] ** 2 + d["q_y"] ** 2), -1, 1))).max()),
                            sat_ticks=int(np.sum(np.any((np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]]) >= 0.999) |
                                                        (np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]]) <= 0.001), axis=1))))
    return res


def self_check(g):
    """FormationAviary with one vehicle against fly_gorge.GorgeAviary (and wind.py's WindAviary force):
    the same random motor commands, with wind 4 1 (same gust seed) and without: states bitwise equal."""
    import fly_gorge as FG
    from run_copter import reset_env
    rng = np.random.default_rng(1)
    m = 0.592 + 0.05 * rng.standard_normal((800, 4))
    worst = []
    for wind in (None, (4.0, 1.0)):
        e1 = FG.make_env(g, Wind(g, *wind, 1000) if wind else None, (2.0, 0.0, -4.0))
        e2 = make_env(g, [Wind(g, *wind, 1000)] if wind else None, [(2.0, 0.0, -4.0)], False)
        o1, o2 = reset_env(e1), reset(e2)
        w = 0.0
        for k in range(len(m)):
            o1 = e1.step(actuators_to_rpm(e1, m[k]).reshape(1, 4))[0]
            o2 = e2.step(actuators_to_rpm(e2, m[k]).reshape(1, 4))[0]
            w = max(w, float(np.abs(o1 - o2).max()))
        e1.close(); e2.close()
        worst.append(w)
        print(f"FormationAviary (1 vehicle) vs GorgeAviary, wind {wind}, {len(m)} ticks: max |state difference| = {w!r}")
    return all(w == 0.0 for w in worst)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--plan", choices=sorted(FP.PLANS), default="abreast")
    ap.add_argument("--noise", choices=("none", "field"), default="field")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--wind", type=float, nargs=2, metavar=("MEAN", "GUST"), default=None)
    ap.add_argument("--skew", type=float, default=0.0, help="batch: vehicle 2 starts SKEW s after vehicle 1 (negative: before)")
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--seconds", type=float, default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--bin", default=str(BIN))
    ap.add_argument("--session", action="store_true", help="ground start, MAVLink, real time (see the module comment)")
    ap.add_argument("--mav-port", type=int, default=14550)
    ap.add_argument("--pose-ports", type=int, nargs=2, default=None, metavar=("PORT1", "PORT2"))
    ap.add_argument("--realtime", type=float, default=None)
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"))
    ap.add_argument("--clear-every", type=int, default=None,
                    help="clearance every N ticks (default 1 in batch, 4 = 100 Hz in the session; NaN in between)")
    ap.add_argument("--self-check", action="store_true")
    a = ap.parse_args()
    if a.self_check:
        g = G.Gorge(a.gorge_seed)
        g.write_assets()
        sys.exit(0 if self_check(g) else 1)
    if a.session and a.realtime is None:
        a.realtime = 1.0
    if a.clear_every is None:
        a.clear_every = 4 if a.session else 1
    if a.out is None:
        a.out = str(HERE / "out" / "formation" / ("session" if a.session else f"{a.plan}-{a.noise}-s{a.seed}"))
    run(a)


if __name__ == "__main__":
    main()
