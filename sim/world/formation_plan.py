"""Two X500s in the gorge on parallel routes: the two formation plans, their routes, plan files and
parameter overlays, and the nominal geometry (clearance of each route, separation, start-time skew).

There is no link between the vehicles. Each flies its own mission; vehicle 2's route is vehicle 1's
route plus one constant offset vector, so the two navigators produce the same speed profile (the
legs have the same lengths, curvatures and slopes) and the nominal offset stays constant.

Plans (`PLANS`). Offsets are given in the frame of the gorge's mean direction over the flight (the
chord from the first to the last waypoint, `frame`): `lat` to its right (east-ish), `along` forward
(up-gorge), `up`. The pair is centered on the route centre: vehicle 1 flies centre - offset/2,
vehicle 2 centre + offset/2.
  abreast    side by side, both noses along the direction of travel: lat 1.8 m, along 0
             (centre distance 1.80 m);
  staggered  vehicle 2 behind and to the side, its nose against the direction of travel
             (`nav.yawReverse 1`), its camera looking behind the formation: lat 2.2 m, along -1.8 m
             (centre distance 2.84 m).
Why these (`--sweep` prints the study): every candidate keeps the nominal clearance of both routes
above 1.5 m, so the clearance does not decide. The lateral component decides how close the two
curves come when one vehicle is ahead of its nominal place (a start-time skew): the minimum over
skews of -6..+6 m is 1.68 m for abreast 1.8 and 1.42 m for staggered (2.2, -1.8); with lat 1.5 and
along -2.0 it is 0.70 m (the axis turns by up to 22 deg, so the along-track component of a fixed
offset becomes partly cross-track in the bends). The first staggered choice, (2.0, -2.0), had 1.16 m,
and a noisy flight with vehicle 2 starting 1.25 s early came to 0.99 m (formation_study.py, skew
set), so the lateral component was raised at about the same centre distance.
The vertical component is the difference of the two start rest heights (a few cm; see below), not a
design choice.

Route centre (`centre`): the gorge route `Gorge.path` (3.5 m above the floor on the centerline),
not re-centered (RECENTERED False). Re-centering was tried (`--sweep`): each waypoint is moved across the axis (within RECENTER_SPAN) to where the
smaller of the two vehicles' clearances is largest (`recenter`), because the walls are not symmetric
about the floor centerline (hard and soft strata, benches) and the offset is fixed in direction while
the axis turns by up to 22 deg. It raises the smaller nominal clearance of abreast 1.8 from 1.57 to
1.63 m and lowers that of staggered (2.0, -2.0) from 1.56 to 1.30 m (the clearance between the
waypoints is not controlled), so the routes stay centered on the gorge route.

Level start sites (`level_start`). A vehicle starting on the ground calibrates and starts its estimator
level (Controller.initAt with levelQuat): a vehicle resting tilted starts with that tilt as an attitude
error, which pushes it sideways during the takeoff until the filter has corrected it. On the floor the
two offset start points are not level where the single vehicle's is (the centerline at north 0): at the
gorge route's first point abreast vehicle 2 rested at 4.4 deg (its estimate 2.1 deg at liftoff); it drifted
0.5 m east during the climb, and the takeoff item, which ends when the estimate is within nav.radius
(0.2 m) of its top, held it there 4.9 s longer than vehicle 1, so its route started 4.7 s late
(test_formation_flight.py, seeds 0 and 1). The first point of the route centre is therefore moved,
within 3 m back and 1 m across the axis, to where the larger of the two rest tilts is smallest: the
candidates are ranked by the plane fitted to the ground under each collision disc, and the best 12 are
settled in PyBullet (the X500 dropped 5 mm onto the floor, 0.5 s at 1200 Hz, motors off) and judged by
the settled tilt; the other waypoints are unchanged, so the offset stays constant.

Level land sites (`land_site`). The same holds at the end: at the route's last point the floor slopes
by 5 to 12 deg under the two vehicles (toward the channel between them in abreast), and in the first
scripted flights both slid on touchdown toward each other, by up to 0.45 m (abreast: the closest
approach of the whole flight, 1.10 to 1.24 m, came after touchdown). The plan's NAV_LAND item carries
its own location (the vehicle flies there at its altitude, then descends), so each vehicle's land point
is a level site found as above, up to 6 m ahead of its own last point along its last leg and at most
0.25 m to the side, so that the land leg continues the last leg and the heading does not turn (a first
version allowed 1 m to the side: the land leg then turned the heading by up to 90 deg, and with the
X500's weak yaw authority 46 to 70 ticks saturated at every landing); the pair is chosen with the two
land points at least the offset apart (`land_sites`); the route is unchanged.

Equal takeoff climbs. A QGroundControl plan gives altitudes relative to home, which each vehicle sets
from its own estimate at the start on the floor. The two start points are on different ground
(offset across the floor, which has a 0.3 m channel and noise), so the same route height would mean
different climbs, which the navigators fly at nav.vMaxZ: the vehicle with the longer climb would
start its route late. The offset's vertical component is therefore the difference of the two rest
heights, so that both takeoff items have the same relative altitude and both climbs the same length.

Files (`write_all`): per plan and vehicle, the QGroundControl plan `formation-PLAN-vN.plan`, the
session overlay `formation-PLAN-vN-ground.params` (start resting on the floor, the route as SPLINE
lines, `nav.yawReverse`) and the batch overlay `formation-PLAN-vN-air.params` (start hovering at the
route's first point, as fly_gorge.py starts).

    python formation_plan.py [--gorge-seed 7] [--out DIR] [--sweep]   # writes the files; --sweep: offsets study
"""
import argparse
import json
import math
from pathlib import Path

import numpy as np
import pybullet as p

import geo
import gorge as G
import gorge_plan

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
URDF = ROOT / "sim/assets/x500.urdf"

PLANS = {
    "abreast": dict(lat=1.8, along=0.0, reverse=(0, 0)),
    "staggered": dict(lat=2.2, along=-1.8, reverse=(0, 1)),
}
RECENTERED = False
RECENTER_SPAN = 1.5          # m: the pair's centre is searched within +-1.5 m of the centerline


def frame(g):
    """Unit vectors (ENU) of the mean direction over the flight: along, lat (right of it), up."""
    a = g.path[-1, :2] - g.path[0, :2]
    a = a / np.linalg.norm(a)
    return np.array([a[0], a[1], 0.0]), np.array([a[1], -a[0], 0.0]), np.array([0.0, 0.0, 1.0])


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


def rest_tilt(g, xy, radius=0.25):
    """Tilt (deg) of a vehicle resting at xy: the plane fitted to the ground under its collision disc;
    and the ground relief (max - min) there."""
    ang = np.linspace(0, 2 * np.pi, 17)[:-1]
    pts = np.array([xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.12, radius) for a in ang])
    z = g.ground_z(pts)
    A = np.column_stack([pts[:, 0] - xy[0], pts[:, 1] - xy[1], np.ones(len(pts))])
    c, *_ = np.linalg.lstsq(A, z, rcond=None)
    return math.degrees(math.atan(math.hypot(c[0], c[1]))), float(z.max() - z.min())


def settled_tilt(g, xys, client=None):
    """Tilt (deg) of the X500 settled on the floor at each xy: dropped from 5 mm above its rest height,
    level, motors off, 0.5 s of PyBullet at 1200 Hz without velocity damping (as the sessions settle it)."""
    c = client if client is not None else p.connect(p.DIRECT)
    if client is None or not hasattr(settled_tilt, "bodies"):
        g.load(c, "physics")
        p.setGravity(0, 0, -9.80665, physicsClientId=c)
        p.setTimeStep(1 / 1200, physicsClientId=c)
        settled_tilt.body = p.loadURDF(str(URDF), [0, 0, 50], flags=p.URDF_USE_INERTIA_FROM_FILE, physicsClientId=c)
        p.changeDynamics(settled_tilt.body, -1, linearDamping=0.0, angularDamping=0.0, physicsClientId=c)
        settled_tilt.bodies = True
    out = []
    for xy in xys:
        z = gorge_plan.start_rest_z(g, np.asarray(xy)) + 0.005
        p.resetBasePositionAndOrientation(settled_tilt.body, [xy[0], xy[1], z], [0, 0, 0, 1], physicsClientId=c)
        p.resetBaseVelocity(settled_tilt.body, [0, 0, 0], [0, 0, 0], physicsClientId=c)
        for _ in range(600):
            p.stepSimulation(physicsClientId=c)
        _, q = p.getBasePositionAndOrientation(settled_tilt.body, physicsClientId=c)
        out.append(math.degrees(math.acos(min(1.0, 1 - 2 * (q[0] ** 2 + q[1] ** 2)))))
    if client is None:
        p.disconnect(c)
        del settled_tilt.bodies
    return out


def level_site(g, o, c0, alongs, across=1.0, step=0.25, keep=12):
    """The point near c0 (along `alongs` (lo, hi) and -across..across of the axis, in `step`) where
    max(rest tilt of c - o/2, of c + o/2) is smallest: the `keep` best by the plane fit (`rest_tilt`), then
    by the settled tilt (`settled_tilt`; ties: the smallest move); FLIGHT_H above the floor."""
    ax = g.axis_dir(c0[1])
    nrm = np.array([ax[1], -ax[0], 0.0])
    cands = []
    for a in np.arange(alongs[0], alongs[1] + 1e-9, step):
        for b in np.arange(-across, across + 1e-9, step):
            c = c0 + a * ax + b * nrm
            t = max(rest_tilt(g, (c - o / 2)[:2])[0], rest_tilt(g, (c + o / 2)[:2])[0])
            cands.append((round(t, 2), abs(a) + abs(b), c))
    cands.sort(key=lambda r: (r[0], r[1]))
    best = None
    for _, move, c in cands[:keep]:
        t = max(settled_tilt(g, [(c - o / 2)[:2], (c + o / 2)[:2]]))
        if best is None or (round(t, 2), move) < best[0]:
            best = ((round(t, 2), move), c)
    c = best[1].copy()
    c[2] = float(g.floor_c(c[1])) + G.FLIGHT_H
    return c


def level_start(g, o):
    """The route's first point: the level site within 3 m back and 1 m across of Gorge.path[0]."""
    return level_site(g, o, g.path[0], (-3.0, 0.0))


def land_sites(g, r1, r2, ahead=6.0, across=0.25, step=0.25, keep=12):
    """The two land locations: for each vehicle the `keep` most level sites by the plane fit within `ahead`
    m ahead of its route's last point along its last leg's direction and `across` m to either side (so
    that the land leg continues the last leg and the heading turns by at most atan(across / step)),
    settled; then the pair with the smallest larger settled tilt whose distance is at least the routes'
    offset (ties: the smaller moves). The routes themselves are unchanged."""
    per = []
    for r in (r1, r2):
        ax = np.array([*(r[-1] - r[-2])[:2], 0.0])
        ax /= np.linalg.norm(ax)
        nrm = np.array([ax[1], -ax[0], 0.0])
        cands = []
        for a in np.arange(0.0, ahead + 1e-9, step):
            for b in np.arange(-across, across + 1e-9, step):
                c = r[-1] + a * ax + b * nrm
                cands.append((round(rest_tilt(g, c[:2])[0], 2), abs(a) + abs(b), c))
        cands.sort(key=lambda q: (q[0], q[1]))
        top = cands[:keep]
        tilts = settled_tilt(g, [c[:2] for _, _, c in top])
        per.append([(t, m, c) for t, (_, m, c) in zip(tilts, top)])
    dmin = float(np.linalg.norm(r2[-1] - r1[-1])) - 1e-6
    best = None
    for t1, m1, c1 in per[0]:
        for t2, m2, c2 in per[1]:
            if not (np.isfinite(t1) and np.isfinite(t2)):
                continue
            if np.linalg.norm((c2 - c1)[:2]) < dmin:
                continue
            key = (round(max(t1, t2), 2), m1 + m2)
            if best is None or key < best[0]:
                best = (key, c1, c2)
    return best[1], best[2]


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


def offset_vector(g, plan, dz=0.0):
    al, la, up = frame(g)
    pl = PLANS[plan] if isinstance(plan, str) else plan
    return pl["lat"] * la + pl["along"] * al + dz * up


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
                start_relief=(gorge_plan.site_check(g, r1[0, :2]), gorge_plan.site_check(g, r2[0, :2])),
                land_relief=(gorge_plan.site_check(g, r1[-1, :2]), gorge_plan.site_check(g, r2[-1, :2])))


# --- files ------------------------------------------------------------------------------------------------

def write_plan(g, origin, route, out, land=None):
    """gorge_plan.write_plan for one vehicle's route: takeoff at the start to the first point's height,
    spline waypoints, land at `land` (default the last point); altitudes relative to this vehicle's home
    (its rest height)."""
    home_z = gorge_plan.start_rest_z(g, route[0, :2])
    def item(cmd, w, rel, seq):
        lat, lon = origin.latlon_e7(w[1], w[0])
        return {"type": "SimpleItem", "command": cmd, "frame": 3, "autoContinue": True, "doJumpId": seq,
                "params": [0, 0, 0, None if cmd == 82 else 0, lat / 1e7, lon / 1e7, round(rel, 3)]}
    items = [item(22, route[0], route[0, 2] - home_z, 1)]
    items += [item(82, w, w[2] - home_z, k) for k, w in enumerate(route[1:], start=2)]
    items.append(item(21, route[-1] if land is None else land, 0.0, len(route) + 1))
    lat, lon = origin.latlon_e7(route[0, 1], route[0, 0])
    plan = {"fileType": "Plan", "version": 1, "groundStation": "QGroundControl",
            "mission": {"version": 2, "firmwareType": 3, "vehicleType": 2,
                        "plannedHomePosition": [lat / 1e7, lon / 1e7, round(origin.alt_m + home_z, 3)], "items": items},
            "geoFence": {"version": 2, "circles": [], "polygons": []},
            "rallyPoints": {"version": 2, "points": []}}
    Path(out).write_text(json.dumps(plan, indent=4) + "\n")
    return plan


def write_overlay(g, route, reverse, out, ground, plan, vehicle):
    """Parameter overlay (NED: north = ENU y, east = x, down = -z) after x500.params (and ground.params for
    the session): the start (resting on the floor, or hovering at the first point) and the route."""
    start_d = -gorge_plan.start_rest_z(g, route[0, :2]) if ground else -route[0, 2]
    lines = [f"# formation plan {plan}, vehicle {vehicle} (sim/world/formation_plan.py), gorge seed {g.seed}",
             "# start " + ("resting on the floor below the route's first point" if ground else "hovering at the route's first point"),
             f"start.x             {route[0][1]:.4f}", f"start.y             {route[0][0]:.4f}",
             f"start.z             {start_d:.4f}",
             f"nav.yawReverse      {reverse}"]
    if not ground:
        lines += ["nav.vMax            2.0", "nav.aMax            2.0", "nav.radius          0.2", "nav.lagMax          0.6"]
    lines += [f"SPLINE  {w[1]:.4f}  {w[0]:.4f}  {-w[2]:.4f}" for w in route[1:]]
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
            write_overlay(g, r, rev, out / f"formation-{name}-v{v}-ground.params", True, name, v)
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


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--params", action="append", default=None, help="parameter files with the ORIGIN line")
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"))
    ap.add_argument("--out", default=str(HERE / "out" / "formation" / "plans"))
    ap.add_argument("--sweep", action="store_true")
    a = ap.parse_args()
    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    if a.sweep:
        sweep(g)
        return
    origin = geo.Origin.from_params(a.params or [ROOT / "params/x500.params", ROOT / "params/ground.params"], a.origin)
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
