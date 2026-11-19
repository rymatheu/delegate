"""The gorge simulator's X500 as a harness module: plant_sim (one vehicle) and plant_formation (two vehicles in one
gorge).

The simulator is the repository's shared one (sim/ at the repository root, `gorgesim.plant`: `Plant` and
`FormationPlant`), run with its own Python environment (sim/.venv, sim/setup.sh). Nothing of the physics or the
sensors is written here: one protocol step is one `tick` of the plant (the four PWM values of each vehicle held for
three 1200 Hz physics substeps, an IMU sample after each, then the slow sensors), and its outputs are the plant's
`Sample` fields under the module's names. What the harness adds: the IMU samples saturated at a full scale (a real
IMU saturates, the simulator's sensor layer does not), and the wall clearance.

Timing. `init` resets the plant (`reset()`: sample 0, the vehicles resting on the floor; it has no protocol reply to
travel in and is dropped). Step k (0-based, input = the PWM the vehicle wrote in reply to sample k) returns sample
k + 1: the state after the tick and the sensor samples the vehicle reads on its next tick.

Wall clearance (`wall_clear`): the closest distance, up to CLEAR_REACH, from the vehicle's collision body to the
gorge's side surfaces: PyBullet's closest points to every body of the gorge (as sim/gorgesim/plant.py `clearance`),
counting only points of the gorge no lower than WALL_BELOW under the vehicle's center, so the floor or a rock top
under the vehicle is not a wall (a wall or rock face beside it is). Measured every 4th tick (100 Hz, as the flight
records) and held between.

Usage (the launchers written by build.sh):
    python adapter.py --build DIR --sim SIM --schema FILE [--vehicles 2]        serve the protocol on stdin/stdout
    python adapter.py ... --code-inputs      one init and one step, then print (JSON) every file of sim/ it read, the
                                             package versions, and any write it attempted
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
HARNESS = HERE.parent.parent.parent
sys.path.insert(0, str(HARNESS / "py"))
import module_protocol as mp  # noqa: E402

sys.dont_write_bytecode = True        # never write __pycache__ into the simulator's tree

CLEAR_REACH = 2.0                     # m: a wall clearance beyond this is reported as this
CLEAR_EVERY = 4                       # ticks between clearance measurements (100 Hz)
WALL_BELOW = 0.05                     # m: gorge points lower than this below the vehicle's center are floor, not wall
FORMATIONS = {1: "abreast", 2: "staggered"}

PARAMS = ["noise_on", "noise_seed", "imu_acc_fs_g", "imu_gyro_fs_dps"]
INPUT = ["pwm0", "pwm1", "pwm2", "pwm3"]
IMU_FIELDS = [f"imu{s}_{c}" for s in range(3) for c in ("ax", "ay", "az", "gx", "gy", "gz")]
VEHICLE_OUT = (["pos_n", "pos_e", "pos_d", "vel_n", "vel_e", "vel_d", "q1", "q2", "q3", "q4",
                "rate_p", "rate_q", "rate_r", "thrust0", "thrust1", "thrust2", "thrust3"] + IMU_FIELDS +
               ["baro_fresh", "baro_pa", "baro_degc", "mag_fresh", "mag_x", "mag_y", "mag_z",
                "gps_fresh", "gps_lat_e7", "gps_lon_e7", "gps_alt", "gps_vn", "gps_ve", "gps_vd", "wall_clear"])


def names(nveh):
    """The module's parameter, input and output field names (one vehicle: unprefixed; two: v1_, v2_)."""
    if nveh == 1:
        return PARAMS, INPUT, ["t_us"] + VEHICLE_OUT
    pre = [f"v{i + 1}_" for i in range(nveh)]
    return (PARAMS + ["formation"], [p + f for p in pre for f in INPUT],
            ["t_us"] + [p + f for p in pre for f in VEHICLE_OUT])


def f32(x):
    """x rounded to binary32 (as the protocol sends it)."""
    return struct.unpack("<f", struct.pack("<f", x))[0]


def full_scale(fs, default, unit):
    """The IMU full-scale limit in output units, a binary32 value: f32(f32(fs) * f32(unit)), the product the
    contract's clause computes in binary32; fs = 0 is the default."""
    fs = f32(fs) if fs > 0 else f32(default)
    return f32(fs * f32(unit))


def load_gorge_readonly(seed):
    """gorge.Gorge(seed) from its cache in sim/build/world-cache, without writing: Gorge.__init__'s cached branch
    minus its `ASSETS.mkdir` and the lock file it opens for writing. Where Gorge.__init__ would build the world (no
    cache, key changed, files missing), this stops instead: run sim/setup.sh."""
    import pickle

    import gorge as G
    import pybullet as p
    cache = G.ASSETS / f"gorge_s{seed}.pkl"
    if not cache.exists():
        raise SystemExit(f"plant: no world cache {cache}; run sim/setup.sh")
    with open(cache, "rb") as fh:
        state = pickle.load(fh)
    if state.get("_key") != G.source_key(seed):
        raise SystemExit(f"plant: world cache {cache} is stale; run sim/setup.sh")
    missing = [f for f in state["files"].values() if not Path(f).exists()]
    if missing:
        raise SystemExit(f"plant: world cache files missing ({missing[:3]}); run sim/setup.sh")
    g = G.Gorge.__new__(G.Gorge)
    g.seed = seed
    for k in G.Gorge.PERSIST:
        setattr(g, k, state[k])
    g.cached = True
    g._client = p.connect(p.DIRECT)
    g._scratch_bodies()
    g._cache_file = cache
    return g


class Plant:
    def __init__(self, sim: Path, nveh: int):
        self.sim, self.nveh = sim, nveh
        self.g = None
        self.p = None
        self.key = None

    def _modules(self):
        sys.path.insert(0, str(self.sim))
        global plant_mod, simulator, motors, pb
        import gorgesim  # noqa: F401  (puts sim/world on sys.path)
        from gorgesim import motors, simulator
        from gorgesim import plant as plant_mod
        import pybullet as pb
        if self.g is None:
            self.g = load_gorge_readonly(simulator.GORGE_SEED)

    def init(self, prm):
        self._modules()
        seed = int(prm["noise_seed"]) if prm["noise_on"] else None
        key = (seed, int(prm.get("formation", 0)))
        if self.p is None or self.key != key:
            if self.p is not None:
                self.p.close()
            if self.nveh == 1:
                self.p = plant_mod.Plant(seed=seed, gorge=self.g)
            else:
                form = FORMATIONS.get(int(prm["formation"]))
                if form is None:
                    raise SystemExit(f"plant_formation: formation {prm['formation']} (1 abreast, 2 staggered)")
                self.p = plant_mod.FormationPlant.for_plan(form, seed=seed, gorge=self.g)
            self.key = key
        self.p.reset()
        self.fmax = self.p.env.KF * self.p.env.MAX_RPM ** 2         # per-motor maximum thrust, N
        self.acc_lim = full_scale(prm.get("imu_acc_fs_g", 0.0), 16.0, 9.80665)
        self.gyro_lim = full_scale(prm.get("imu_gyro_fs_dps", 0.0), 2000.0, 0.017453292)
        self.clear = [CLEAR_REACH] * self.nveh
        self.k = 0

    def wall_clear(self, i):
        env = self.p.env
        d = env.DRONE_IDS[i]
        zc = pb.getBasePositionAndOrientation(d, physicsClientId=env.CLIENT)[0][2]
        best = CLEAR_REACH
        for b in env.world:
            for q in pb.getClosestPoints(d, b, CLEAR_REACH, physicsClientId=env.CLIENT):
                if q[6][2] >= zc - WALL_BELOW and q[8] < best:
                    best = q[8]
        return max(0.0, best)

    def vehicle(self, s, lag, i):
        if self.k % CLEAR_EVERY == 0:
            self.clear[i] = self.wall_clear(i)
        out = dict(pos_n=s.pos_ned[0], pos_e=s.pos_ned[1], pos_d=s.pos_ned[2], vel_n=s.vel_ned[0],
                   vel_e=s.vel_ned[1], vel_d=s.vel_ned[2], q1=s.quat_ned_frd[0], q2=s.quat_ned_frd[1],
                   q3=s.quat_ned_frd[2], q4=s.quat_ned_frd[3], rate_p=s.rates_frd[0], rate_q=s.rates_frd[1],
                   rate_r=s.rates_frd[2], wall_clear=self.clear[i])
        for j in range(4):
            out[f"thrust{j}"] = lag[motors.SLOT_TO_SIM[j]] / self.fmax
        # the IMU samples saturated at the full scale (a value within range passes unchanged); truth is not
        clip = lambda v, lim: max(-lim, min(lim, float(v)))
        for si, (a, gy) in enumerate(s.imu):
            for c, v in zip(("ax", "ay", "az"), a):
                out[f"imu{si}_{c}"] = clip(v, self.acc_lim) if abs(float(v)) > self.acc_lim else v
            for c, v in zip(("gx", "gy", "gz"), gy):
                out[f"imu{si}_{c}"] = clip(v, self.gyro_lim) if abs(float(v)) > self.gyro_lim else v
        b, m, gp = s.baro, s.mag, s.gps
        out.update(baro_fresh=b is not None, baro_pa=b[0] if b else 0.0, baro_degc=b[1] if b else 0.0,
                   mag_fresh=m is not None, mag_x=m[0] if m else 0.0, mag_y=m[1] if m else 0.0,
                   mag_z=m[2] if m else 0.0, gps_fresh=gp is not None)
        if gp:
            # latitude and longitude: degrees (binary64) -> int32 in 1e-7 degrees, nearest
            out.update(gps_lat_e7=int(round(float(gp[0]) * 1e7)), gps_lon_e7=int(round(float(gp[1]) * 1e7)),
                       gps_alt=gp[2], gps_vn=gp[3], gps_ve=gp[4], gps_vd=gp[5])
        else:
            out.update(gps_lat_e7=0, gps_lon_e7=0, gps_alt=0.0, gps_vn=0.0, gps_ve=0.0, gps_vd=0.0)
        return out

    def step(self, inp):
        if self.nveh == 1:
            s = self.p.tick([inp[f"pwm{j}"] for j in range(4)])
            out = self.vehicle(s, self.p.env.lag_thrust, 0)
        else:
            ss = self.p.tick([[inp[f"v{i + 1}_pwm{j}"] for j in range(4)] for i in range(self.nveh)])
            out = {}
            for i, s in enumerate(ss):
                for k, v in self.vehicle(s, self.p.env.lag_thr[i], i).items():
                    out[f"v{i + 1}_{k}"] = v
        self.k += 1
        out["t_us"] = self.k * plant_mod.STEP_US
        return out


def versions():
    import importlib.metadata as md
    v = {"python": sys.version.split()[0]}
    for d in ("pybullet", "gym-pybullet-drones", "numpy", "scipy", "gymnasium", "pillow"):
        v[d] = md.version(d)
    return v


def code_inputs(plant: Plant, prm, inp):
    """Every file of sim/ this process read: the simulator's Python modules it imported, the data files Python opened
    (audit hook), and the files PyBullet loads from C (URDF, the world's collision meshes), which the audit hook
    cannot see. Also every write this process attempted anywhere."""
    opened, written = set(), []

    def hook(event, args):
        if event == "open" and args and isinstance(args[0], (str, bytes, os.PathLike)):
            path = os.fsdecode(args[0])
            mode = args[1] if len(args) > 1 and isinstance(args[1], str) else "r"
            flags = args[2] if len(args) > 2 and isinstance(args[2], int) else 0
            if any(c in mode for c in "wax+") or flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT):
                written.append(path)
            opened.add(os.path.realpath(path))
        elif event in ("os.mkdir", "os.rename", "os.replace", "os.remove", "os.rmdir", "os.truncate"):
            written.append(f"{event} {args[0]!r}")
    sys.addaudithook(hook)
    plant.init(prm)
    plant.step(inp)
    import airframes
    root = os.path.realpath(plant.sim)
    files = set()
    for mod in list(sys.modules.values()):
        f = getattr(mod, "__file__", None)
        if f and os.path.realpath(f).startswith(root + "/"):
            files.add(os.path.realpath(f))
    files |= {f for f in opened if f.startswith(root + "/") and os.path.isfile(f) and "/.venv" not in f}
    g = plant.g
    files.add(os.path.realpath(airframes.AIRFRAMES["x500"]["urdf"]))           # pybullet loadURDF
    files.add(os.path.realpath(g.files["terrain"]))                            # the world's collision bodies
    files |= {os.path.realpath(g.files[k]) for k in g.files if k.endswith("_hull")}
    files |= {os.path.realpath(g.asset_dir / f"boulder_s{g.seed}_{k:02d}_hull.obj") for k in range(len(g.boulders))}
    files = {f for f in files if "/.venv" not in f}
    return dict(files=sorted(files), versions=versions(), written=written)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", required=True, help="build/modules/NAME (manifest.json)")
    ap.add_argument("--sim", required=True, help="the repository's sim/ (read only)")
    ap.add_argument("--schema", required=True, help="build/gen/NAME/module_schema.json")
    ap.add_argument("--vehicles", type=int, default=1)
    ap.add_argument("--code-inputs", action="store_true")
    a = ap.parse_args()
    proto = mp.take_stdout()
    schema = mp.load_schema(a.schema)
    mp.check_fields(schema, *names(a.vehicles))
    plant = Plant(Path(a.sim), a.vehicles)
    if a.code_inputs:
        prm = {"noise_on": True, "noise_seed": 1, "imu_acc_fs_g": 0.0, "imu_gyro_fs_dps": 0.0, "formation": 1}
        inp = {n: 1500 for n in names(a.vehicles)[1]}
        proto.write((json.dumps(code_inputs(plant, prm, inp), indent=1) + "\n").encode())
        proto.flush()
        return 0
    man = json.loads(Path(a.build, "manifest.json").read_text())
    manifest = mp.manifest_json(schema, man["code_hash"], man["flags"], man["compiler"])
    return mp.serve(schema, manifest, plant.init, plant.step, proto)


if __name__ == "__main__":
    sys.exit(main())
