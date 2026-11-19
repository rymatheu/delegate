#!/usr/bin/env python3
"""Render a two-vehicle gorge flight of sim/fly_gorge_formation.py with the formation renderer
(sim/world/render_formation.py): one H.264 mp4 at 20 fps and real speed (chase view behind the pair, the two
X500s labelled V1 and V2; under it V1's forward RGB and thermal cameras and V2's forward RGB and thermal cameras), stills,
and every 20th frame as PNG.

    .venv/bin/python sim/render_gorge_formation.py --run build/runs/abreast
        --out build/render/abreast [--name formation-abreast] [--every 0.05] [--span T0 T1] [--overview-only]

Adapter code. What is sim/world/'s: render_formation.render_sharded (two worker processes, one PyBullet client each, about 4 GB each:
one renders the chase canvas and both RGB frames before exposure, the other both thermal cameras' optical signal; the main
process applies exposure, thermal detector and AGC in frame order), render_formation.Setup (frame times, the chase camera
5 m behind the pair's midpoint along the gorge axis, the V1 / V2 labels, the status line with the centre distance from
formation.csv, the panel titles; the run's formation.json gives plan, nominal distance, reverse flags [0, 0] and the
thermal seeds), render_formation.Pair (placing the X500s in the visual world: PX4's X500 meshes without propellers and
render_flight's propeller motion blur), the cameras of sensors.py, the fonts (DejaVu Sans from Matplotlib) and the H.264
encoder script (render_formation.MP4_ENCODER) run with .venv-video (as sim/render_gorge.py).

What this adapter supplies, by setting four names of render_formation before rendering (at import, so that the spawned
workers see the same): Pair reads each vehicle's track.csv (100 Hz: ENU position, PyBullet quaternion, actuators), its
propeller state at 100 Hz; Setup adds "ArduCopter in Lean x 2" at the right of the status line and a line at
the bottom of the chase view (each vehicle's mode, mission item and terrain clearance, from track.csv); Outputs writes the mp4, every 20th frame as PNG,
and stills (the chase frame where the pair's midpoint first passes north 12, 25, 45 and 65 m, and the frame of the later
touchdown). The frames run from 1 s before the first arming to 1 s after the last disarm (armed and disarmed heartbeats).
Writes OUT/NAME.mp4, OUT/NAME-N12.png ... OUT/NAME-landing.png, OUT/NAME-overview.png (top-down view, both flown tracks),
OUT/NAME-frames/, OUT/NAME-render.json.
"""
import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np

sys.dont_write_bytecode = True

import render_gorge as RG  # noqa: E402   (puts sim/world on sys.path; quat_R, Mp4, View, caption, VIDEO_PY)
import pybullet as p  # noqa: E402
from PIL import ImageDraw  # noqa: E402

RFM = RG.RFM                     # sim/world/render_formation.py
RW = RG.RW                       # sim/world/render_world.py
RF = RFM.RF                      # sim/world/render_flight.py
G, S = RG.G, RG.S

STILL_NORTH = (12.0, 25.0, 45.0, 65.0)
FRAME_EVERY = 20
MODE_NAMES = RG.MODE_NAMES
_Pair, _Setup = RFM.Pair, RFM.Setup


class TrackPair(_Pair):
    """render_formation.Pair over the two track.csv of a fly_gorge_formation.py run (ENU positions, PyBullet
    quaternions, actuators at 100 Hz); client=False loads the flight data only."""

    def __init__(self, g, run, client=True):
        self.g = g
        if client:
            self.c = p.connect(p.DIRECT)
            self.bodies = g.load(self.c, "visual")
            self.fires = S.FI.Fires(g, "still")
        self.runs = []
        for v in (1, 2):
            d = np.genfromtxt(Path(run) / f"v{v}" / "track.csv", delimiter=",", names=True)
            pos = np.column_stack([d["x"], d["y"], d["z"]])
            quat = np.column_stack([d["qx"], d["qy"], d["qz"], d["qw"]])
            ang, spd = RF.prop_state(d, hz=1.0 / (d["t"][1] - d["t"][0]))
            self.runs.append(dict(d=d, meta={}, pos=pos, quat=quat, angle=ang, speed=spd, t=d["t"], body=None))

    def pose(self, v, k):
        r = self.runs[v]
        return r["pos"][k], RG.quat_R(r["quat"][k]), r["angle"][k], r["speed"][k]


class TrackSetup(_Setup):
    """render_formation.Setup with a bottom line on the chase view: each vehicle's mode, item and clearance."""

    def chase(self, sc, t):
        canvas, north = super().chase(sc, t)
        dr = ImageDraw.Draw(canvas, "RGBA")
        parts = []
        for v in (0, 1):
            k = sc.at(v, t)
            if k is None:
                continue
            d = sc.runs[v]["d"]
            mode = MODE_NAMES.get(int(d["mode"][k]), str(int(d["mode"][k])))
            if not d["armed"][k]:
                mode += " disarmed"
            item = int(d["item"][k])
            parts.append(f"V{v + 1} {mode}" + (f" item {item}" if item >= 0 else "") + f", clearance {max(0.0, d['clearance'][k]):4.2f} m")
        f = RW.font(12, True)
        dr.text((self.W - 8, 5), "ArduCopter in Lean x 2", font=f, fill=(255, 255, 255), anchor="ra")
        dr.rectangle([0, self.H - 22, self.W, self.H], fill=(0, 0, 0, 130))
        if parts:
            dr.text((8, self.H - 18), parts[0], font=f, fill=(255, 255, 255))
        if len(parts) > 1:
            dr.text((self.W - 8, self.H - 18), parts[1], font=f, fill=(255, 255, 255), anchor="ra")
        return canvas, north


class Mp4Outputs:
    """render_formation.Outputs' interface: the mp4 (render_gorge.Mp4, .venv-video), every FRAME_EVERY-th frame as
    PNG, and the stills."""

    landing_t = None

    def __init__(self, out, name, every, n, mp4=True):
        self.out, self.name, self.every = Path(out), name, every
        self.ms = int(round(1000 * every))
        self.dir = self.out / f"{name}-frames"
        self.dir.mkdir(parents=True, exist_ok=True)
        for old in self.dir.glob("frame_*.png"):
            old.unlink()
        self.digits = max(4, len(str(n - 1)))
        self.v = None
        self.n = 0
        self.still_t = None
        self.stills = {}
        self.todo = list(STILL_NORTH)

    def add(self, i, t, canvas, north):
        if self.v is None:
            self.v = RG.Mp4(self.out / f"{self.name}.mp4", canvas.size, 1 / self.every)
        self.v.add(canvas)
        self.n += 1
        if i % FRAME_EVERY == 0:
            canvas.save(self.dir / f"frame_{i:0{self.digits}d}.png")
        while self.todo and north >= self.todo[0]:
            tag = f"N{self.todo.pop(0):g}"
            canvas.save(self.out / f"{self.name}-{tag}.png")
            self.stills[tag] = dict(t=float(t), north=float(north))
            if self.still_t is None:
                self.still_t = float(t)
        if self.landing_t is not None and "landing" not in self.stills and t >= self.landing_t:
            canvas.save(self.out / f"{self.name}-landing.png")
            self.stills["landing"] = dict(t=float(t), north=float(north))

    def close(self):
        self.v.close()
        return dict(mp4=round((self.out / f"{self.name}.mp4").stat().st_size / 1e6, 2))


def report(o, st, acc, n, workers, wall):
    sizes = o.close()
    info = dict(run=str(st.run), frames=n, every_s=st.every, fps=1 / st.every, workers=workers, render_wall_s=round(wall, 1),
                mp4_mb=sizes["mp4"], stills=o.stills, world=dict(seed=st.g.seed, key=G.source_key(st.g.seed)),
                other_vehicle_in_rgb_fov_fraction={k: v / max(acc["n"], 1) for k, v in acc.items() if k != "n"})
    (o.out / f"{o.name}-render.json").write_text(json.dumps(info, indent=1) + "\n")
    print(json.dumps(info), flush=True)
    return info


RFM.Pair, RFM.Setup, RFM.Outputs, RFM.report = TrackPair, TrackSetup, Mp4Outputs, report


def overview(g, run, path):
    """Top-down view of the gorge with both flown tracks (liftoff to touchdown; V1 red, V2 orange), the routes'
    waypoints and the land sites (render_gorge.overview's camera)."""
    fm = json.loads((run / "formation.json").read_text())
    v = RG.View(g)
    Wo, Ho = 2400, 960
    y0, y1 = -3.0, 80.0
    xm = float(np.mean(g.xc_fn(np.linspace(0, 72, 100))))
    ym = (y0 + y1) / 2
    alt = 400.0
    across = (y1 - y0) * Ho / Wo
    fov_v = 2 * math.degrees(math.atan(across / 2 / alt))
    img, px = v.shoot(Wo, Ho, (xm, ym, alt), (xm, ym, 0), (-1, 0, 0), fov_v, 300, 430, (), 1.0, bg=(46, 50, 56))
    dr = ImageDraw.Draw(img, "RGBA")
    colors = [(230, 50, 40, 235), (255, 170, 30, 235)]
    for k in (1, 2):
        fl = json.loads((run / f"v{k}" / "flight.json").read_text())
        ms = json.loads((run / f"v{k}" / "mission.json").read_text())
        d = np.genfromtxt(run / f"v{k}" / "track.csv", delimiter=",", names=True)
        met = fl["metrics"]
        sel = (d["t"] >= met["liftoff_t"]) & (d["t"] <= (met.get("touchdown_t") or d["t"][-1]))
        q, _ = px(np.column_stack([d["x"], d["y"], d["z"]])[sel][::5])
        dr.line([tuple(a) for a in q], fill=colors[k - 1], width=4)
        q, _ = px(np.array(ms["route_enu"]))
        for a in q:
            dr.ellipse([a[0] - 6, a[1] - 6, a[0] + 6, a[1] + 6], fill=(40, 110, 230, 235), outline=(255, 255, 255, 230))
        a, _ = px(np.array([ms["land_site_enu"]]))
        a = a[0]
        dr.ellipse([a[0] - 14, a[1] - 14, a[0] + 14, a[1] + 14], outline=(255, 255, 255, 240), width=3)
        c = met["clearance_min_at"]
        b, _ = px(np.array([[c["east"], c["north"], c["up"]]]))
        b = b[0]
        dr.ellipse([b[0] - 11, b[1] - 11, b[0] + 11, b[1] + 11], outline=(255, 226, 70, 255), width=4)
        RW.label(dr, (b[0] + 18, b[1] + (-40 if k == 1 else 60)), f"V{k} least clearance {met['clearance_min_in_air_m']:.2f} m", 22,
                 fill=(255, 236, 140))
    a, _ = px(np.array([[xm - 13.5, y0 + 2, 0], [xm - 13.5, y0 + 12, 0]]))
    dr.line([tuple(a[0]), tuple(a[1])], fill=(255, 255, 255, 255), width=6)
    dr.text((a[0][0], a[0][1] - 34), "10 m", font=RW.font(24, True), fill=(255, 255, 255))
    dr.line([(Wo - 140, 70), (Wo - 50, 70)], fill=(255, 255, 255), width=5)
    dr.polygon([(Wo - 50, 58), (Wo - 26, 70), (Wo - 50, 82)], fill=(255, 255, 255))
    dr.text((Wo - 128, 82), "north", font=RW.font(24, True), fill=(255, 255, 255))
    dr.rectangle([0, 0, Wo, 30], fill=(0, 0, 0, 120))
    dr.text((12, 3), f"Gorge seed {g.seed} from above: two X500s, each flown by its own ArduCopter in Lean (cpp2lean), formation "
            f"'{fm['plan']}'. Red: V1's track, orange: V2's (liftoff to touchdown); blue: the routes' takeoff and spline "
            f"waypoints; white rings: land sites", font=RW.font(20), fill=(255, 255, 255))
    img.save(path)
    p.disconnect(v.c)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--name", default=None, help="default formation-PLAN")
    ap.add_argument("--every", type=float, default=0.05, help="seconds of flight per frame (default 0.05: 20 fps at real speed)")
    ap.add_argument("--span", type=float, nargs=2, default=None, metavar=("T0", "T1"),
                    help="frames in [T0, T1) s (default: 1 s before the first arming to 1 s after the last disarm)")
    ap.add_argument("--workers", type=int, default=2, help="render_formation's worker processes (about 4 GB each; at most 2)")
    ap.add_argument("--overview-only", action="store_true", help="only OUT/NAME-overview.png")
    a = ap.parse_args()
    if not RG.VIDEO_PY.exists():
        sys.exit(f"render_gorge_formation: {RG.VIDEO_PY} not found (see sim/README.md, 'Rendering')")
    run, out = Path(a.run).resolve(), Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    fm = json.loads((run / "formation.json").read_text())
    name = a.name or f"formation-{fm['plan']}"
    if a.overview_only:
        overview(G.Gorge(fm["gorge_seed"]), run, out / f"{name}-overview.png")
        return
    fl = [json.loads((run / f"v{k}" / "flight.json").read_text()) for k in (1, 2)]
    span = a.span or (min(f["record"]["t_arm"] for f in fl) - 1.0, max(f["record"]["t_disarm"] for f in fl) + 1.0)
    tds = [f["metrics"].get("touchdown_t") for f in fl]
    Mp4Outputs.landing_t = max(tds) + 0.5 if all(x is not None for x in tds) else None
    info = RFM.render_sharded(run, out, name, a.every, 720, 400, max(2, min(a.workers, 2)), True, span)
    if a.span is None:
        overview(G.Gorge(fm["gorge_seed"]), run, out / f"{name}-overview.png")
        info["stills"]["overview"] = {}
        (out / f"{name}-render.json").write_text(json.dumps(dict(info, span=list(span)), indent=1) + "\n")


if __name__ == "__main__":
    main()
