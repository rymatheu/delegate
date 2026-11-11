"""Fly the X500 with the frozen Lean controller up the gorge, with wind and onboard cameras.

The harness is sim/run_leanfc.py's (imported, unmodified): its parameter reader, sensor layer
(`Sensors`, `Noise`: `--noise none` zero noise with the 100 Hz mocap overlay, `field` the GPS-like
10 Hz profile), the controller protocol and the lock-step loop (one controller line per 400 Hz tick,
three 1200 Hz physics substeps, motor lag). What changes:
- the world: `GorgeAviary` loads the gorge's collision bodies (gorge.py: concave terrain trimesh,
  convex boulders) in place of the package's ground plane (BaseAviary._housekeeping, which loads
  pybullet_data's plane.urdf, is replaced by the same housekeeping without it);
- the wind (wind.py `WindAviary`, `--wind MEAN GUST`; default off: no aerodynamic force at all);
- the mission: a parameter overlay written to OUT/mission.params with the waypoints of
  `Gorge.flight_path` (3.5 m above the floor along the centerline, legs of at most 10 m with the
  centerline within 0.35 m of each chord), the start (hovering at the first waypoint) and the
  navigator settings, loaded after the snapshot's x500.params (and mocap.params for --noise none);
- contact: after every tick the vehicle's contacts with the world are read; any contact ends the
  run and is reported; the clearance (closest distance from the vehicle's collision cylinder to the
  terrain and the boulders, up to 4 m) is logged every tick;
- cameras (`--cameras on`): forward RGB and downward RGB at 10 Hz, forward thermal at 8.7 Hz, from
  the true pose after the tick's physics, rendered in separate PyBullet clients holding the visual
  and the thermal twin of the world; they do not feed the controller. Thermal detections are
  matched against the firebrands online.

Outputs in OUT: flight.csv (run_leanfc's columns, then wind w_n w_e w_d and aerodynamic force
f_n f_e f_d in NED, and the clearance), flight.json (configuration, waypoints, outcome, contact),
mission.params, cams_rgb_fwd.npz, cams_rgb_down.npz, cams_thermal.npz, detections.json and
detections.md.

Run: python fly_gorge.py [--wind MEAN GUST] [--seed N] [--noise none|field] [--cameras on|off] [--out DIR]
"""
import argparse
import json
import math
import subprocess
import sys
import time
from importlib.resources import files
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent))
import run_leanfc as R  # noqa: E402
from run_copter import place, reset_env, actuators_to_rpm, sim_state, SpecificForce, enu_state_to_ned, quat_ned_frd  # noqa: E402

import gorge as G  # noqa: E402
import sensors as S  # noqa: E402
from wind import Wind, WindAviary  # noqa: E402

SNAP = HERE / "snapshot"
LAG = (0.0125, 0.025)
CLEAR_MAX = 4.0


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


def make_env(gorge, wind, init_ned):
    """run_leanfc.make_env with GorgeAviary (X500 URDF, motor lag, 1200 Hz physics, 400 Hz control,
    gravity 9.80665 and the derived constants). The start is in the air, so place()'s ground probe is
    skipped (rest_alt 0)."""
    import contextlib, io
    with contextlib.redirect_stdout(io.StringIO()):
        env = GorgeAviary(gorge, wind=wind, urdf=R.AIRFRAMES["x500"]["urdf"], lag=LAG,
                          drone_model=R.DroneModel.CF2X, num_drones=1, physics=R.Physics.PYB,
                          pyb_freq=R.PYB_HZ, ctrl_freq=R.CTRL_HZ, gui=False, record=False, obstacles=False,
                          user_debug_gui=False, output_folder=str(HERE / "out" / "pyb"))
    env.G = R.GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    env.rest_alt = 0.0
    place(env, init_ned, (0.0, 0.0, 0.0), "hover")
    return env


def write_mission(gorge, path, kind="WAYPOINT"):
    wps = gorge.path
    lines = ["# gorge mission (fly_gorge.py): waypoints 3.5 m above the floor along the centerline, NED m",
             f"# gorge seed {gorge.seed}; start hovering at the first waypoint, heading north",
             f"start.x             {wps[0][1]:.4f}", f"start.y             {wps[0][0]:.4f}",
             f"start.z             {-wps[0][2]:.4f}",
             "nav.vMax            2.0", "nav.aMax            2.0", "nav.radius          0.2", "nav.lagMax          0.6"]
    lines += [f"{kind}  {w[1]:.4f}  {w[0]:.4f}  {-w[2]:.4f}" for w in wps[1:]]
    Path(path).write_text("\n".join(lines) + "\n")


def enu_to_ned(v):
    return np.array([v[1], v[0], -v[2]])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--wind", type=float, nargs=2, metavar=("MEAN", "GUST"), default=None,
                    help="mean speed (m/s, + up-gorge) and gust sigma (m/s); default: no wind and no aerodynamic force")
    ap.add_argument("--seed", type=int, default=0, help="sensor-noise, gust and thermal-noise seed")
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--noise", choices=("none", "field"), default="field")
    ap.add_argument("--cameras", choices=("on", "off"), default="on")
    ap.add_argument("--out", default=str(HERE / "out"))
    ap.add_argument("--legs", choices=("waypoint", "spline"), default="waypoint", help="mission lines WAYPOINT (default) or SPLINE")
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)

    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    write_mission(g, out / "mission.params", a.legs.upper())
    files_ = [SNAP / "params/x500.params"] + ([SNAP / "params/mocap.params"] if a.noise == "none" else []) + [out / "mission.params"]
    vals, wps, _ = R.read_params(files_)
    fix_every = int(round(vals["dtFix"] / vals["dt"]))
    p0 = (vals["start.x"], vals["start.y"], vals["start.z"])
    legs = np.linalg.norm(np.diff(g.path, axis=0), axis=1)
    seconds = float(np.sum(legs / 2.0 + 1.0) * 2.0 + 10.0)       # time limit: twice the nominal mission time + 10 s
    wind = Wind(g, a.wind[0], a.wind[1], a.seed + 1000) if a.wind else None
    env = make_env(g, wind, p0)
    obs = reset_env(env)
    drone = env.DRONE_IDS[0]
    world = {b: v for b, v in env.world.items()}
    sf = SpecificForce(env.G, 1.0 / R.CTRL_HZ)
    sens = R.Sensors(R.Noise(0, 0, 0, 0, 0, 0, 0, 0) if a.noise == "none" else R.Noise(), a.seed)

    cams = {}
    if a.cameras == "on":
        vis, th = p.connect(p.DIRECT), p.connect(p.DIRECT)
        bv, bt = g.load(vis, "visual"), g.load(th, "thermal")
        cams = {"rgb_fwd": S.RGBCamera(vis, bv, S.FORWARD, gorge=g), "rgb_down": S.RGBCamera(vis, bv, S.DOWN, gorge=g),
                "thermal": S.ThermalCamera(th, bt, S.FORWARD, seed=a.seed)}
    rec = {k: dict(t=[], img=[], cost=[]) for k in cams}
    fire_fill = {k: [] for k in range(len(g.firebrands))}       # per thermal frame: max ember fill, peak temp
    dets = []

    proc = subprocess.Popen([str(SNAP / "leanfc"), *R.param_args(files_), "--calibrate", str(R.CAL_SAMPLES), "--trace", "--bits"],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    t0 = time.time()
    pos, vel, _, _ = enu_state_to_ned(obs[0][0:3], obs[0][3:7], obs[0][10:13], obs[0][13:16])
    q0 = quat_ned_frd(obs[0][3:7])
    for _ in range(R.CAL_SAMPLES):
        proc.stdin.write(R.line_of(sens.sample(pos, vel, (0.0, 0.0, -env.G), q0, np.zeros(3), False)))
    proc.stdin.flush()
    if proc.stdout.readline().strip() != "calibrated":
        raise RuntimeError("controller did not acknowledge the calibration")

    statics = list(world)
    rows, leg, contact, done_at, outcome = [], 0, None, None, "time limit"
    n = int(round(seconds * R.CTRL_HZ))
    for k in range(n):
        pos, vel, acc, quat, _, rates = sim_state(env, obs, sf)
        s = sens.sample(pos, vel, acc, quat, rates, k % fix_every == 0)
        proc.stdin.write(R.line_of(s)); proc.stdin.flush()
        r = R.parse_reply(proc.stdout.readline())
        obs, *_ = env.step(actuators_to_rpm(env, r[:4]).reshape(1, 4))
        p1, v1, _, _ = enu_state_to_ned(obs[0][0:3], obs[0][3:7], obs[0][10:13], obs[0][13:16])
        q1 = quat_ned_frd(obs[0][3:7])
        dist = [c[8] for b in statics for c in p.getClosestPoints(drone, b, CLEAR_MAX, physicsClientId=env.CLIENT)]
        clear = min(dist) if dist else CLEAR_MAX
        rows.append([k / R.CTRL_HZ, *p1, *v1, *q1, *r[4:17], leg, *r[:4],
                     *enu_to_ned(env.wind_last), *enu_to_ned(env.force_last), clear])
        leg = r[17]
        tk = (k + 1) / R.CTRL_HZ
        if cams:
            pw, ow = p.getBasePositionAndOrientation(drone, physicsClientId=env.CLIENT)
            Rw = np.array(p.getMatrixFromQuaternion(ow)).reshape(3, 3)
            for name, cam in cams.items():
                if tk + 1e-9 >= len(rec[name]["t"]) / cam.rate:
                    c0 = time.perf_counter()
                    fr = cam.capture(Rw, np.array(pw))
                    rec[name]["cost"].append(time.perf_counter() - c0)
                    rec[name]["t"].append(tk)
                    if name == "thermal":
                        rec[name]["img"].append(fr["temp_c"].astype(np.float16))
                        for f in range(len(g.firebrands)):
                            fe, fa = fr["fill"].get(f, (None, None))
                            fire_fill[f].append((float(fe.max()), float(fa.max()), float(fr["temp_c"][fa > 0].max()))
                                                if fe is not None else (0.0, 0.0, float("nan")))
                        for d, m in zip(S.detect(fr), S.match(S.detect(fr), g.firebrands)):
                            dets.append(dict(t=tk, match=m, peak_c=d["peak_c"], n_pix=d["n_pix"], az_deg=d["az_deg"], el_deg=d["el_deg"],
                                             range=d["range"], pos=None if d["pos"] is None else list(map(float, d["pos"])),
                                             vehicle=list(map(float, pw))))
                    else:
                        rec[name]["img"].append(fr["rgb"])
        cp = p.getContactPoints(bodyA=drone, physicsClientId=env.CLIENT)
        if cp:
            c = min(cp, key=lambda c: c[8])
            contact = dict(t=tk, body=world.get(c[2], ("?", -1)), pos_enu=list(c[5]), normal_force=float(c[9]),
                           depth=float(c[8]), speed=float(np.linalg.norm(v1)))
            outcome = "contact"
            break
        if leg == len(wps) and done_at is None:
            done_at = tk
        if done_at is not None and tk >= done_at + 2.0:
            outcome = "completed"
            break
    proc.stdin.close(); proc.wait()
    env.close()
    wall = time.time() - t0

    cols = R.COLS + "w_n w_e w_d f_n f_e f_d clearance".split()
    with open(out / "flight.csv", "w") as f:
        f.write(",".join(cols) + "\n")
        for row in rows:
            f.write(",".join(str(int(x)) if i == 24 else repr(float(x)) for i, x in enumerate(row)) + "\n")
    meta = dict(vehicle="x500", params=[str(x) for x in files_], noise=a.noise, seed=a.seed, gorge_seed=a.gorge_seed,
                fix_hz=1.0 / vals["dtFix"], motor_lag=list(LAG), start=list(p0), waypoints=wps,
                wind=None if a.wind is None else dict(mean=a.wind[0], gust=a.wind[1], w_ref=wind.w_ref),
                outcome=outcome, completed_at=done_at, legs_done=int(leg), legs=len(wps), contact=contact, seconds=len(rows) / R.CTRL_HZ, wall_s=round(wall, 1),
                camera_cost_ms={k: dict(mean=1000 * float(np.mean(v["cost"])), max=1000 * float(np.max(v["cost"])), frames=len(v["t"]))
                                for k, v in rec.items() if v["t"]})
    (out / "flight.json").write_text(json.dumps(meta, indent=1) + "\n")
    for name, v in rec.items():
        np.savez_compressed(out / f"cams_{name}.npz", t=np.array(v["t"]), img=np.array(v["img"]))
    if cams:
        (out / "detections.json").write_text(json.dumps(dict(detections=dets, fill={k: v for k, v in fire_fill.items()},
                                                             t=rec["thermal"]["t"]), indent=0) + "\n")
        write_detections(g, out, dets, fire_fill, rec["thermal"]["t"], np.array(rows))
    print(f"{out}: {outcome} at t = {len(rows) / R.CTRL_HZ:.2f} s, wind {a.wind}, noise {a.noise}, seed {a.seed}, wall {wall:.1f} s"
          + (f", contact {contact}" if contact else ""))
    for k, v in meta["camera_cost_ms"].items():
        print(f"  {k}: {v['frames']} frames, {v['mean']:.1f} ms mean, {v['max']:.1f} ms max")


def write_detections(g, out, dets, fire_fill, tt, rows):
    """detections.md: per firebrand the first frame in which any part of it (embers or ash bed) is in
    the image, the first thermal detection (time, range from the vehicle) with the ember fill of the
    best pixel and the detection's apparent temperature at that frame, the number of frames with a
    detection, the peak apparent temperature over its pixels and the peak ember fill of a pixel;
    then the false positives (detections farther than MATCH_RADIUS_M from every firebrand)."""
    t = rows[:, 0]
    pos = np.column_stack([rows[:, 2], rows[:, 1], -rows[:, 3]])
    lines = [f"# Thermal detections, gorge seed {g.seed}", "",
             f"Forward thermal camera (Lepton 3.5 class, 160 x 120, 57 deg, {S.Lepton().rate_hz} Hz, 30 deg down). Hot pixel: "
             f"apparent temperature above the frame median + {S.DETECT_DELTA_K:g} K; a detection is a connected group of hot "
             f"pixels, placed in the world from its hottest pixel's bearing and the range of that pixel's hottest sample, and "
             f"matched to a firebrand within {S.MATCH_RADIUS_M} m. Ranges are from the vehicle to the firebrand center.", "",
             "| # | position (E, N, U) m | radius m | T C | placement | first in view: t s, range m | first detection: t s, range m "
             "| at first detection: ember fill, apparent T C | detected frames | peak apparent T C | peak ember fill |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for k, f in enumerate(g.firebrands):
        fe = np.array([q[0] for q in fire_fill[k]])
        fa = np.array([q[1] for q in fire_fill[k]])
        peak = np.array([q[2] for q in fire_fill[k]])
        rng_at = lambda tq: float(np.linalg.norm(pos[np.argmin(np.abs(t - tq))] - f.center))
        iv = np.nonzero(fa > 0)[0]
        view = f"{tt[iv[0]]:.2f}, {rng_at(tt[iv[0]]):.1f}" if len(iv) else "never"
        dk = [d for d in dets if d["match"] == k]
        first = f"{dk[0]['t']:.2f}, {rng_at(dk[0]['t']):.1f}" if dk else "not detected"
        at = (f"{fe[int(np.argmin(np.abs(np.array(tt) - dk[0]['t'])))]:.3f}, {dk[0]['peak_c']:.0f}") if dk else "-"
        place_ = f"hidden behind boulder {f.boulder}" if f.hidden else "open"
        pk = f"{np.nanmax(peak):.0f}" if np.isfinite(peak).any() else "-"
        lines.append(f"| {k} | ({f.center[0]:.1f}, {f.center[1]:.1f}, {f.center[2]:.2f}) | {f.radius:.2f} | {f.temp_c:.0f} | {place_} | "
                     f"{view} | {first} | {at} | {len({d['t'] for d in dk})} | {pk} | {fe.max():.3f} |")
    fp = [d for d in dets if d["match"] < 0]
    lines += ["", f"False positives: {len(fp)} detections in {len({d['t'] for d in fp})} of {len(tt)} frames."]
    for d in fp[:20]:
        lines.append(f"- t {d['t']:.2f} s: peak {d['peak_c']:.0f} C, {d['n_pix']} px, range {d['range']:.1f} m, "
                     f"position {None if d['pos'] is None else tuple(round(x, 1) for x in d['pos'])}")
    (out / "detections.md").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
