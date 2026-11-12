"""The gorge as a ground-start, real-time MAVLink session: sim/run_leanfc.py's loop with the gorge world.

    python gorge_session.py [--wind MEAN GUST] [--gorge-seed 7] [--pose-port 14601] [--session-out DIR]
                            RUN_LEANFC_OPTIONS...

Everything after the options above is passed to sim/run_leanfc.py's `main` unchanged (the parameter
files, `--ground --mav --realtime 1 --trace-vehicle`, `--noise`, `--seed`, `--origin`, `--out`, ...):
the harness, its sensors, the controller protocol, the pacing and the CSV are run_leanfc's own. This
script only replaces its `make_env` with the gorge (and appends one parameter overlay):

- the world: fly_gorge.GorgeAviary (the gorge's terrain trimesh and boulder hulls in place of the
  package's ground plane; wind.py's aerodynamic force with `--wind`, none without);
- the start: the X500 resting on the gorge floor at the mission start (`Gorge.path[0]`, north 0 on the
  centerline), level, nose north: its base is placed 5 mm above the highest ground point under its
  collision disc plus the rest height, and cpp2lean's reset_env lets it settle on its contact
  (0.25 s, motors off) before the clock starts; the motor lag starts at zero thrust;
- the overlay DIR/gorge.params (gorge_plan.write_overlay): that start and the complete gorge mission
  (TAKEOFF, the route as SPLINE lines, LAND), which the vehicle boots with onboard, so Start Mission
  works without an upload; DIR/gorge.plan is the same mission as a plan file for QGroundControl
  (gorge_plan.write_plan; uploading it is optional) for the run's origin (the files' ORIGIN line or
  --origin);
- the camera feed: after every 4th control step (100 Hz) the vehicle's true pose (ENU position,
  PyBullet quaternion), its simulated time and the wall-clock time are sent as one UDP datagram to
  127.0.0.1:POSE_PORT (camera_component.py renders from the latest one; 0 disables);
- the record: every 4th step the clearance (closest distance of the vehicle's collision cylinder to
  terrain and boulders, up to 4 m) and the number of contact points, and every 40th step the wall
  clock; written at the end to DIR/session.csv (t as in the run's CSV; negative during the settling)
  and DIR/session.json (real-time factor overall and per second, the largest lag behind the wall
  clock after the first 2 s, the time in the air, the smallest clearance and the contacts in the air).

Without wind the physics is run_leanfc's exactly (wind.py's check), only the ground is the gorge.
"""
import argparse
import contextlib
import io
import json
import socket
import struct
import sys
import time
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent))
import run_leanfc as R  # noqa: E402
from run_copter import place  # noqa: E402

import geo  # noqa: E402
import gorge as G  # noqa: E402
import gorge_plan  # noqa: E402
from fly_gorge import GorgeAviary  # noqa: E402
from wind import Wind  # noqa: E402

POSE_FMT = "<Idd3d4d"          # seq, simulated s, wall s (time.time), ENU position, PyBullet quaternion (x, y, z, w)
POSE_EVERY, WALL_EVERY = 4, 40
CLEAR_MAX = 4.0


class SessionAviary(GorgeAviary):
    """GorgeAviary that publishes the pose and records clearance, contacts and the wall clock."""

    def __init__(self, gorge, pose_addr=None, **kw):
        self.pose_addr, self.k = pose_addr, 0
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM) if pose_addr else None
        self.rec, self.wall = [], []
        super().__init__(gorge, **kw)

    def step(self, action):
        out = super().step(action)
        self.k += 1
        if self.k % POSE_EVERY == 0:
            d, c = self.DRONE_IDS[0], self.CLIENT
            pos, orn = p.getBasePositionAndOrientation(d, physicsClientId=c)
            if self.sock:
                self.sock.sendto(struct.pack(POSE_FMT, self.k, self.k / R.CTRL_HZ, time.time(), *pos, *orn), self.pose_addr)
            dist = [q[8] for b in self.world for q in p.getClosestPoints(d, b, CLEAR_MAX, physicsClientId=c)]
            self.rec.append((self.k, min(dist) if dist else CLEAR_MAX, len(p.getContactPoints(bodyA=d, physicsClientId=c))))
        if self.k % WALL_EVERY == 0:
            self.wall.append((self.k, time.monotonic()))
        return out


def make_env_factory(g, wind, pose_addr):
    def make_env(airframe, lag, init_ned, first_accel="hover"):
        """run_leanfc.make_env with SessionAviary, the vehicle resting on the gorge floor at (n, e)."""
        if airframe != "x500":
            sys.exit("the gorge session flies the x500 (SIM_VEHICLE x500)")
        with contextlib.redirect_stdout(io.StringIO()):
            env = SessionAviary(g, pose_addr=pose_addr, wind=wind, urdf=R.AIRFRAMES["x500"]["urdf"], lag=lag,
                                drone_model=R.DroneModel.CF2X, num_drones=1, physics=R.Physics.PYB,
                                pyb_freq=R.PYB_HZ, ctrl_freq=R.CTRL_HZ, gui=False, record=False, obstacles=False,
                                user_debug_gui=False, output_folder=str(HERE / "out" / "pyb"))
        env.G = R.GRAVITY_MSS
        env.GRAVITY = env.G * env.M
        env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
        env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
        env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
        env.rest_alt = 0.0
        n, e, d = init_ned
        if d is not None:
            sys.exit("the gorge session starts on the ground (--ground)")
        place(env, (n, e, None), (0.0, 0.0, 0.0), first_accel)
        env.INIT_XYZS[0, 2] = gorge_plan.start_rest_z(g, np.array([e, n])) + 0.005
        return env
    return make_env


def summary(env, csv, out):
    """session.csv (t, clearance, contacts) and session.json (real time, clearance in flight)."""
    rec = np.array(env.rec, float)
    with open(out / "session.csv", "w") as f:              # t as in flight.csv: step 101 + i is its row i (t = i / 400)
        f.write("t,clearance,contacts\n")
        for k, c, n in rec:
            f.write(f"{(int(k) - 101) / R.CTRL_HZ!r},{float(c)!r},{int(n)}\n")
    w = np.array(env.wall, float)
    k0 = 100 + 2 * R.CTRL_HZ                  # skip reset_env's 100 settling steps and the first 2 s (start-up catch-up)
    w = w[w[:, 0] >= k0]
    info = {}
    if len(w) > 2:
        sim = (w[:, 0] - w[0, 0]) / R.CTRL_HZ
        wall = w[:, 1] - w[0, 1]
        lag = (wall - sim) - (wall - sim).min()   # behind the best-aligned real-time schedule (run_leanfc never runs ahead)
        per_s = [(sim[j] - sim[i]) / (wall[j] - wall[i]) for i, j in zip(range(0, len(w) - 10, 10), range(10, len(w), 10))]
        info = dict(simulated_s=float(sim[-1]), wall_s=float(wall[-1]), rtf=float(sim[-1] / wall[-1]),
                    lag_max_s=float(lag.max()), rtf_1s_min=float(min(per_s)) if per_s else None,
                    seconds_below_0_98=int(sum(r < 0.98 for r in per_s)), seconds=len(per_s))
    if csv.exists():
        d = np.genfromtxt(csv, delimiter=",", names=True)
        if d.size and "landed" in d.dtype.names:
            t = d["t"]
            k = np.round(rec[:, 0] / R.CTRL_HZ * R.CTRL_HZ).astype(int) - 101    # session step -> CSV row
            ok = (k >= 0) & (k < len(t))
            landed = np.zeros(len(rec), int)
            landed[ok] = d["landed"][k[ok]].astype(int)
            air = landed == 2                                                   # MAV_LANDED_STATE_IN_AIR
            info.update(in_air_s=float(air.sum() * POSE_EVERY / R.CTRL_HZ),
                        clearance_min_in_air_m=float(rec[air, 1].min()) if air.any() else None,
                        contacts_in_air=int((rec[air, 2] > 0).sum()))
    (out / "session.json").write_text(json.dumps(info, indent=1) + "\n")
    print("session:", json.dumps(info), file=sys.stderr)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], add_help=False)
    ap.add_argument("--wind", type=float, nargs=2, metavar=("MEAN", "GUST"), default=None)
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--pose-port", type=int, default=14601)
    ap.add_argument("--session-out", default=str(HERE / "out" / "qgc"))
    a, rest = ap.parse_known_args()
    sub = argparse.ArgumentParser(add_help=False)
    sub.add_argument("--params", action="append", default=[])
    sub.add_argument("--origin", nargs=3, default=None)
    sub.add_argument("--seed", type=int, default=0)
    sub.add_argument("--out", default=None)
    s, _ = sub.parse_known_args(rest)
    out = Path(a.session_out)
    out.mkdir(parents=True, exist_ok=True)

    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    gorge_plan.write_overlay(g, out / "gorge.params")
    origin = geo.Origin.from_params(s.params, s.origin)
    gorge_plan.write_plan(g, origin, out / "gorge.plan")
    wind = Wind(g, a.wind[0], a.wind[1], s.seed + 1000) if a.wind else None
    holder = {}
    factory = make_env_factory(g, wind, ("127.0.0.1", a.pose_port) if a.pose_port else None)

    def make_env(*args, **kw):
        holder["env"] = factory(*args, **kw)
        return holder["env"]
    R.make_env = make_env
    sys.argv = ["run_leanfc.py", *rest, "--params", str(out / "gorge.params")]
    print(f"gorge session: seed {g.seed}, start on the floor at {g.path[0][:2].round(2).tolist()} (ENU), "
          f"wind {a.wind}, pose -> 127.0.0.1:{a.pose_port}, plan {out / 'gorge.plan'}", file=sys.stderr, flush=True)
    R.main()
    if "env" in holder:
        summary(holder["env"], Path(s.out) if s.out else Path("sim/out/run.csv"), out)


if __name__ == "__main__":
    main()
