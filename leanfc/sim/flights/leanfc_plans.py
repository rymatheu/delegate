"""leanfc's own mission files for the shared gorge world: the parameter overlays (the start and the onboard mission
as the controller's TAKEOFF / SPLINE / LAND lines), the plan files written next to them, and the formation-offset
study. The geometry itself (the gorge route, the level start and land sites, the two routes of a formation plan, the
rest height) is the shared simulator's (sim/world/gorge_plan.py, formation_plan.py); this module only adds what the
leanfc controller needs.

Gorge (one vehicle): `write_gorge_plan` (the plan file, the items of gorge_plan.plan_items) and `write_gorge_overlay`
(start resting on the floor at the first waypoint; TAKEOFF to its height, the route as SPLINE lines, LAND at the last
waypoint). The vehicle boots with that mission onboard, so Start Mission works without an upload; uploading the plan is
optional and replaces it with the same items.

Formation (two vehicles): `write_all` writes per plan and vehicle the plan file `formation-PLAN-vN.plan` (no
CONDITION_YAW items: leanfc turns vehicle 2 of `staggered` around with its parameter `nav.yawReverse`), the session
overlay `formation-PLAN-vN-ground.params` (start on the floor, `nav.yawReverse`, TAKEOFF, the route as SPLINE lines,
LAND at the level land site) and the batch overlay `formation-PLAN-vN-air.params` (start hovering at the route's first
point, the route only). `--sweep` prints the offsets study (clearance probe, re-centering, skew tolerance).

    ../sim/.venv/bin/python sim/flights/leanfc_plans.py [--gorge-seed 7] [--out DIR] [--sweep]     (from leanfc/)
    ../sim/.venv/bin/python -B sim/flights/leanfc_plans.py --plans          # rewrite leanfc/plans/*.plan
    ../sim/.venv/bin/python -B sim/flights/leanfc_plans.py --check-plans    # committed plans == what a session writes
"""
import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import shared  # noqa: E402
shared.use_world()
import geo  # noqa: E402                     (shared: sim/world/geo.py)
import gorge as G  # noqa: E402              (shared)
import gorge_plan  # noqa: E402              (shared)
import formation_plan as FPS  # noqa: E402   (shared)
from formation_plan import PLANS, frame, offset_vector, level_start, land_sites, settled_tilt  # noqa: E402

ROOT = shared.LEANFC
URDF = shared.X500_URDF
RECENTERED = False
RECENTER_SPAN = 1.5          # m: the pair's centre is searched within +-1.5 m of the centerline


# --- one vehicle ------------------------------------------------------------------------------------------

def site_check(g, xy, radius=0.6):
    """Ground relief (max - min of the ground height) within `radius` of xy: a boulder or step shows up."""
    ang = np.linspace(0, 2 * np.pi, 25)[:-1]
    pts = [xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.2, 0.4, radius) for a in ang]
    z = g.ground_z(np.array(pts))
    return float(z.max() - z.min())


def write_gorge_plan(g, origin, out):
    items, home_z = gorge_plan.plan_items(g, origin)
    lat, lon = origin.latlon_e7(g.path[0, 1], g.path[0, 0])
    plan = {"fileType": "Plan", "version": 1, "groundStation": "QGroundControl",
            "mission": {"version": 2, "firmwareType": 3, "vehicleType": 2,
                        "plannedHomePosition": [lat / 1e7, lon / 1e7, round(origin.alt_m + home_z, 3)],
                        "items": items},
            "geoFence": {"version": 2, "circles": [], "polygons": []},
            "rallyPoints": {"version": 2, "points": []}}
    Path(out).write_text(json.dumps(plan, indent=4) + "\n")
    return plan, home_z


def write_gorge_overlay(g, out):
    """The session's parameter overlay (NED: north = ENU y, east = x, down = -z)."""
    path = g.path
    lines = ["# gorge session overlay (leanfc/sim/flights/leanfc_plans.py): load after x500.params and ground.params",
             f"# gorge seed {g.seed}: start resting on the floor at the first waypoint; the onboard mission is",
             "# gorge.plan's items: TAKEOFF to the first waypoint's height, the gorge route (3.5 m above the floor",
             "# on the centerline) as SPLINE legs, LAND at the last waypoint",
             f"start.x             {path[0][1]:.4f}", f"start.y             {path[0][0]:.4f}",
             f"start.z             {-gorge_plan.start_rest_z(g, path[0, :2]):.4f}",
             f"TAKEOFF {-path[0][2]:.4f}"]
    lines += [f"SPLINE  {w[1]:.4f}  {w[0]:.4f}  {-w[2]:.4f}" for w in path[1:]]
    lines += [f"LAND    {path[-1][1]:.4f}  {path[-1][0]:.4f}"]
    Path(out).write_text("\n".join(lines) + "\n")



# --- two vehicles -----------------------------------------------------------------------------------------

class Probe:
    """A scratch PyBullet client with the gorge's collision bodies and the X500 (its collision cylinder):
    clearance as the sessions measure it (getClosestPoints of the vehicle body to terrain and boulders)."""

    def __init__(self, g):
        self.c = p.connect(p.DIRECT)
        self.statics = list(g.load(self.c, "physics"))
        self.body = p.loadURDF(str(URDF), [0, 0, 50], useFixedBase=True, physicsClientId=self.c)

    def clearance(self, pts, yaw=None, reach=6.0):
        out = []
        for k, q in enumerate(np.atleast_2d(pts)):
            orn = [0, 0, 0, 1] if yaw is None else p.getQuaternionFromEuler([0, 0, yaw[k]])
            p.resetBasePositionAndOrientation(self.body, q.tolist(), orn, physicsClientId=self.c)
            d = [c[8] for s in self.statics for c in p.getClosestPoints(self.body, s, reach, physicsClientId=self.c)]
            out.append(min(d) if d else reach)
        return np.array(out)

    def close(self):
        p.disconnect(self.c)


def recenter(g, probe, path, o):
    """Each waypoint moved across the gorge axis (within RECENTER_SPAN, 5 cm steps) to where
    min(clearance of w - o/2, clearance of w + o/2) is largest (the middle of the best ones)."""
    out = path.copy()
    us = np.linspace(-RECENTER_SPAN, RECENTER_SPAN, 61)
    for k, w in enumerate(path):
        ax = g.axis_dir(w[1])
        nrm = np.array([ax[1], -ax[0], 0.0])
        q = w + us[:, None] * nrm
        c = np.minimum(probe.clearance(q - o / 2), probe.clearance(q + o / 2))
        best = us[c >= c.max() - 0.01]
        out[k] = w + float(np.median(best)) * nrm
    return out


def centre(g, plan, probe=None, recentered=RECENTERED):
    """The route centre of a plan: Gorge.path with its first point at the level start site, re-centered
    for the pair (or not)."""
    c = g.path.copy()
    c[0] = level_start(g, offset_vector(g, plan))
    if not recentered:
        return c
    own = probe is None
    probe = probe or Probe(g)
    c = recenter(g, probe, c, offset_vector(g, plan))
    if own:
        probe.close()
    return c


def routes(g, plan, c=None, probe=None):
    """The two routes (ENU waypoints, the first is the takeoff point above the start) and the offset
    vector (vehicle 2 - vehicle 1), with the vertical component that equalizes the takeoff climbs."""
    c = centre(g, plan, probe) if c is None else c
    o = offset_vector(g, plan)
    r1, r2 = c - o / 2, c + o / 2
    z1 = gorge_plan.start_rest_z(g, r1[0, :2])
    z2 = gorge_plan.start_rest_z(g, r2[0, :2])
    r2 = r2 + [0, 0, z2 - z1]
    return r1, r2, r2[0] - r1[0], (z1, z2)


# --- the navigator's curves (Leanfc/Navigator.lean legsOf, all SPLINE legs, the last at rest) -----------

def hermite_points(start, wps, step=0.05):
    """Points along the target path of a mission of SPLINE legs from `start` through `wps` (Catmull-Rom
    tangents, the last leg ending at rest), sampled about every `step` m; and the unit tangents."""
    pts = [np.asarray(start, float)] + [np.asarray(w, float) for w in wps]
    n = len(wps)
    unit = lambda v: v / np.linalg.norm(v)
    end_dir = None
    P, T = [], []
    for k in range(n):
        o, d = pts[k], pts[k + 1]
        L = np.linalg.norm(d - o)
        c = unit(d - o)
        t0 = end_dir if k > 0 else c
        t1 = c if k == n - 1 else unit(pts[k + 2] - o)
        m0, m1 = L * t0, L * t1
        end_dir = t1
        tau = np.linspace(0, 1, max(3, int(L / step)))[:-1] if k < n - 1 else np.linspace(0, 1, max(3, int(L / step)))
        h00, h01 = 2 * tau ** 3 - 3 * tau ** 2 + 1, -2 * tau ** 3 + 3 * tau ** 2
        h10, h11 = tau ** 3 - 2 * tau ** 2 + tau, tau ** 3 - tau ** 2
        P.append(h00[:, None] * o + h01[:, None] * d + h10[:, None] * m0 + h11[:, None] * m1)
        dp = (6 * (tau - tau ** 2))[:, None] * (d - o) + (3 * tau ** 2 - 4 * tau + 1)[:, None] * m0 + (3 * tau ** 2 - 2 * tau)[:, None] * m1
        T.append(dp / np.linalg.norm(dp, axis=1, keepdims=True))
    return np.concatenate(P), np.concatenate(T)


def arclength(P):
    return np.concatenate([[0.0], np.cumsum(np.linalg.norm(np.diff(P, axis=0), axis=1))])


def skew_band(skews, dist, limit=1.0):
    """The interval of skews around 0 (contiguous) over which the distance stays at or above `limit`."""
    skews, dist = np.asarray(skews), np.asarray(dist)
    i0 = int(np.argmin(np.abs(skews)))
    lo = hi = i0
    while lo > 0 and dist[lo - 1] >= limit:
        lo -= 1
    while hi < len(skews) - 1 and dist[hi + 1] >= limit:
        hi += 1
    return float(skews[lo]), float(skews[hi])


def skew_distance(P1, P2, skews):
    """Centre distance when vehicle 2 is `s` m of path ahead of its nominal place (s < 0: behind) along its
    route: min over the route of |P2(arc + s) - P1(arc)| for each s (same arc-length parametrization)."""
    s1, s2 = arclength(P1), arclength(P2)
    out = []
    for s in skews:
        q = np.clip(s1 + s, 0, s2[-1])
        x2 = np.column_stack([np.interp(q, s2, P2[:, i]) for i in range(3)])
        out.append(float(np.linalg.norm(x2 - P1, axis=1).min()))
    return np.array(out)


def geometry(g, plan, probe, c=None):
    """Nominal numbers of a plan: clearance of each route's curve (vehicle level, nose along or against
    the tangent), centre distance along the routes, and the distance under a start-time skew."""
    r1, r2, o, (z1, z2) = routes(g, plan, c, probe)
    P1, T1 = hermite_points(r1[0], r1[1:])
    P2, _ = hermite_points(r2[0], r2[1:])
    yaw = np.arctan2(T1[:, 1], T1[:, 0])
    rev = PLANS[plan]["reverse"] if isinstance(plan, str) else plan["reverse"]
    c1 = probe.clearance(P1[::4], yaw[::4] + math.pi * rev[0])
    c2 = probe.clearance(P2[::4], yaw[::4] + math.pi * rev[1])
    dist = np.linalg.norm(P2 - P1, axis=1)
    skews = np.arange(-30.0, 30.01, 0.25)
    sd = skew_distance(P1, P2, skews)
    return dict(offset=o.tolist(), norm=float(np.linalg.norm(o)), rest_z=(z1, z2),
                clear1=(float(c1.min()), float(P1[::4][np.argmin(c1), 1])),
                clear2=(float(c2.min()), float(P2[::4][np.argmin(c2), 1])),
                dist=(float(dist.min()), float(dist.max())), skews=skews.tolist(), skew_dist=sd.tolist(),
                start_relief=(site_check(g, r1[0, :2]), site_check(g, r2[0, :2])),
                land_relief=(site_check(g, r1[-1, :2]), site_check(g, r2[-1, :2])))


# --- files ------------------------------------------------------------------------------------------------

write_plan = FPS.write_plan     # the shared plan file of one vehicle's route (no CONDITION_YAW items)


def write_overlay(g, route, reverse, out, ground, plan, vehicle, land=None):
    """Parameter overlay (NED: north = ENU y, east = x, down = -z) after x500.params (and ground.params for
    the session): the start (resting on the floor, or hovering at the first point) and the route; on the
    ground also the plan's takeoff and land items (`TAKEOFF`, `LAND` at `land`, default the last point),
    so that the onboard mission is write_plan's."""
    start_d = -gorge_plan.start_rest_z(g, route[0, :2]) if ground else -route[0, 2]
    lines = [f"# formation plan {plan}, vehicle {vehicle} (leanfc/sim/flights/leanfc_plans.py), gorge seed {g.seed}",
             "# start " + ("resting on the floor below the route's first point" if ground else "hovering at the route's first point"),
             f"start.x             {route[0][1]:.4f}", f"start.y             {route[0][0]:.4f}",
             f"start.z             {start_d:.4f}",
             f"nav.yawReverse      {reverse}"]
    if not ground:
        lines += ["nav.vMax            2.0", "nav.aMax            2.0", "nav.radius          0.2", "nav.lagMax          0.6"]
    if ground:
        lines += [f"TAKEOFF {-route[0][2]:.4f}"]
    lines += [f"SPLINE  {w[1]:.4f}  {w[0]:.4f}  {-w[2]:.4f}" for w in route[1:]]
    if ground:
        lp = route[-1] if land is None else land
        lines += [f"LAND    {lp[1]:.4f}  {lp[0]:.4f}"]
    Path(out).write_text("\n".join(lines) + "\n")


def write_all(g, origin, out, plans=PLANS):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    probe = Probe(g)
    info = {}
    for name in plans:
        c = centre(g, name, probe)
        r1, r2, o, rz = routes(g, name, c, probe)
        lands = land_sites(g, r1, r2)
        for v, (r, rev) in enumerate(zip((r1, r2), PLANS[name]["reverse"]), start=1):
            write_plan(g, origin, r, out / f"formation-{name}-v{v}.plan", lands[v - 1])
            write_overlay(g, r, rev, out / f"formation-{name}-v{v}-ground.params", True, name, v, lands[v - 1])
            write_overlay(g, r, rev, out / f"formation-{name}-v{v}-air.params", False, name, v)
        info[name] = dict(offset_enu=o.tolist(), rest_z=rz, reverse=PLANS[name]["reverse"],
                          start1=r1[0].tolist(), start2=r2[0].tolist(),
                          settled_tilt_deg=settled_tilt(g, [r1[0, :2], r2[0, :2]]),
                          land1=lands[0].tolist(), land2=lands[1].tolist(),
                          land_settled_tilt_deg=settled_tilt(g, [lands[0][:2], lands[1][:2]]))
    probe.close()
    (out / "formation-plans.json").write_text(json.dumps(info, indent=1) + "\n")
    return info


def sweep(g):
    """The offsets study: nominal clearance per route, separation, and the skew it tolerates."""
    probe = Probe(g)
    rows = []
    cands = [dict(lat=L, along=0.0, reverse=(0, 0)) for L in (1.5, 1.8, 2.0, 2.2)]
    cands += [dict(lat=L, along=A, reverse=(0, 1)) for L in (1.5, 1.8, 2.0) for A in (-1.5, -2.0)]
    for rec in (False, True):
        for pl in cands:
            c = centre(g, pl, probe, rec)
            m = geometry(g, pl, probe, c)
            sd = np.array(m["skew_dist"]); sk = np.array(m["skews"])
            band = skew_band(sk, sd)
            rows.append((rec, pl, m, band, sd.min()))
            print(f"recentered {rec!s:5} lat {pl['lat']:.1f} along {pl['along']:+.1f}: |o| {m['norm']:.2f} m, dz {m['offset'][2]:+.3f}; "
                  f"clearance v1 {m['clear1'][0]:.2f} (N {m['clear1'][1]:.1f}), v2 {m['clear2'][0]:.2f} (N {m['clear2'][1]:.1f}); "
                  f"distance {m['dist'][0]:.2f}..{m['dist'][1]:.2f}; min over skews -6..6 m: {sd[np.abs(sk) <= 6].min():.2f}, -30..30 m: {sd.min():.2f}, >= 1.0 m for skews {band[0]:+.2f}..{band[1]:+.2f} m; "
                  f"relief start {m['start_relief'][0]:.2f}/{m['start_relief'][1]:.2f}, land {m['land_relief'][0]:.2f}/{m['land_relief'][1]:.2f}",
                  flush=True)
    probe.close()
    return rows


PLAN_FILES = ["gorge.plan"] + [f"formation-{n}-v{v}.plan" for n in PLANS for v in (1, 2)]


def write_plan_files(g, origin, out):
    """The five plan files a person may upload (the ones every session writes): the gorge and both formations."""
    import shutil
    import tempfile
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    write_gorge_plan(g, origin, out / "gorge.plan")
    with tempfile.TemporaryDirectory(prefix="leanfc-plans.") as t:
        write_all(g, origin, t)
        for f in PLAN_FILES[1:]:
            shutil.copyfile(Path(t) / f, out / f)


def check_plan_files(g, origin, committed):
    """True when the committed plan files are byte for byte what a session writes now."""
    import filecmp
    import tempfile
    with tempfile.TemporaryDirectory(prefix="leanfc-plans.") as t:
        write_plan_files(g, origin, t)
        bad = [f for f in PLAN_FILES if not (Path(committed) / f).exists()
               or not filecmp.cmp(Path(t) / f, Path(committed) / f, shallow=False)]
    for f in PLAN_FILES:
        print(f"{'DIFFERS' if f in bad else 'same   '}  {Path(committed) / f}")
    return not bad


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--plans", nargs="?", const=str(ROOT / "plans"), default=None, metavar="DIR",
                    help="write only the five plan files into DIR (default leanfc/plans)")
    ap.add_argument("--check-plans", nargs="?", const=str(ROOT / "plans"), default=None, metavar="DIR",
                    help="check that the plan files in DIR (default leanfc/plans) are what a session writes")
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--params", action="append", default=None, help="parameter files with the ORIGIN line")
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"))
    ap.add_argument("--out", default=str(ROOT / "out" / "formation" / "plans"))
    ap.add_argument("--sweep", action="store_true")
    a = ap.parse_args()
    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    if a.sweep:
        sweep(g)
        return
    origin = geo.Origin.from_params(a.params or [ROOT / "params/x500.params", ROOT / "params/ground.params"], a.origin)
    if a.plans:
        write_plan_files(g, origin, a.plans)
        print("wrote " + ", ".join(PLAN_FILES) + f" in {a.plans}")
        return
    if a.check_plans:
        ok = check_plan_files(g, origin, a.check_plans)
        print("RESULT " + ("PASS" if ok else "FAIL"))
        sys.exit(0 if ok else 1)
    info = write_all(g, origin, a.out)
    probe = Probe(g)
    for name in PLANS:
        m = geometry(g, name, probe, centre(g, name, probe))
        info[name]["geometry"] = m
        sk, sd = np.array(m["skews"]), np.array(m["skew_dist"])
        band = skew_band(sk, sd)
        o = np.array(m["offset"])
        print(f"{name}: offset ENU ({o[0]:+.3f}, {o[1]:+.3f}, {o[2]:+.3f}) m, |o| {m['norm']:.3f} m; nominal clearance "
              f"v1 {m['clear1'][0]:.2f} m (N {m['clear1'][1]:.1f}), v2 {m['clear2'][0]:.2f} m (N {m['clear2'][1]:.1f}); "
              f"distance along the curves {m['dist'][0]:.3f}..{m['dist'][1]:.3f} m; with vehicle 2 s m of path ahead: "
              + ", ".join(f"{s:+g}: {np.interp(s, sk, sd):.2f}" for s in (-20, -10, -6, -4, -2, -1, 1, 2, 3, 4, 6, 10, 20))
              + f"; >= 1.0 m for s in {band[0]:+.2f}..{band[1]:+.2f} m; start relief {m['start_relief'][0]:.2f}/{m['start_relief'][1]:.2f} m, "
              f"landing relief {m['land_relief'][0]:.2f}/{m['land_relief'][1]:.2f} m")
    probe.close()
    (Path(a.out) / "formation-plans.json").write_text(json.dumps(info, indent=1) + "\n")


if __name__ == "__main__":
    main()
