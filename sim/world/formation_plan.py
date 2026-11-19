"""Two X500s in the gorge on parallel routes: the two formation plans, their routes, level start and land sites, and the
QGroundControl plan file of each vehicle.

Each vehicle flies its own mission; vehicle 2's route is vehicle 1's route plus one constant offset vector, so the legs
have the same lengths, curvatures and slopes and the nominal offset stays constant.

Plans (`PLANS`). Offsets are given in the frame of the gorge's mean direction over the flight (the chord from the first
to the last waypoint, `frame`): `lat` to its right (east-ish), `along` forward (up-gorge), `up`. The pair is centered on
the route centre: vehicle 1 flies centre - offset/2, vehicle 2 centre + offset/2.
  abreast    side by side: lat 1.8 m, along 0 (centre distance 1.80 m);
  staggered  vehicle 2 behind and to the side: lat 2.2 m, along -1.8 m (centre distance 2.84 m); `reverse` (0, 1) marks
             vehicle 2 as the one that flies nose against the direction of travel, its camera looking behind the pair.
Every plan keeps the nominal clearance of both routes above 1.5 m. The vertical component of the offset is the difference
of the two start rest heights (a few cm; see below), not a design choice.

Route centre (`centre`): the gorge route `Gorge.path` (3.5 m above the floor on the centerline), with its first point
moved to a level start site.

Level start sites (`level_start`). The two offset start points are not level where the single vehicle's is (the
centerline at north 0); a vehicle resting tilted is pushed sideways during its takeoff. The first point of the route
centre is therefore moved, within 3 m back and 1 m across the axis, to where the larger of the two rest tilts is
smallest: the candidates are ranked by the plane fitted to the ground under each collision disc (`rest_tilt`), and the
best 12 are settled in PyBullet (`settled_tilt`: the X500 dropped 5 mm onto the floor, 0.5 s at 1200 Hz, motors off) and
judged by the settled tilt; the other waypoints are unchanged, so the offset stays constant.

Level land sites (`land_sites`). At the route's last point the floor slopes by 5 to 12 deg under the two vehicles. The
plan's NAV_LAND item carries its own location (the vehicle flies there at its altitude, then descends), so each
vehicle's land point is a level site found as above, up to 6 m ahead of its own last point along its last leg and at
most 0.25 m to the side, so that the land leg continues the last leg and the heading does not turn; the pair is chosen
with the two land points at least the offset apart; the route is unchanged.

Equal takeoff climbs (`routes`). A QGroundControl plan gives altitudes relative to home, which each vehicle sets at its
start on the floor. The two start points are on different ground, so the same route height would mean different climbs.
The offset's vertical component is therefore the difference of the two rest heights, so that both takeoff items have the
same relative altitude and both climbs the same length.

`write_plan`: one vehicle's QGroundControl plan (gorge_plan.plan_items' layout for its route and land site).
"""
import json
import math
from pathlib import Path

import numpy as np
import pybullet as p

import gorge as G
import gorge_plan
from airframes import AIRFRAMES

URDF = AIRFRAMES["x500"]["urdf"]

PLANS = {
    "abreast": dict(lat=1.8, along=0.0, reverse=(0, 0)),
    "staggered": dict(lat=2.2, along=-1.8, reverse=(0, 1)),
}


def frame(g):
    """Unit vectors (ENU) of the mean direction over the flight: along, lat (right of it), up."""
    a = g.path[-1, :2] - g.path[0, :2]
    a = a / np.linalg.norm(a)
    return np.array([a[0], a[1], 0.0]), np.array([a[1], -a[0], 0.0]), np.array([0.0, 0.0, 1.0])


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
    level, motors off, 0.5 s of PyBullet at 1200 Hz without velocity damping."""
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


def centre(g, plan):
    """The route centre of a plan: Gorge.path with its first point at the level start site."""
    c = g.path.copy()
    c[0] = level_start(g, offset_vector(g, plan))
    return c


def offset_vector(g, plan, dz=0.0):
    al, la, up = frame(g)
    pl = PLANS[plan] if isinstance(plan, str) else plan
    return pl["lat"] * la + pl["along"] * al + dz * up


def routes(g, plan, c=None):
    """The two routes (ENU waypoints, the first is the takeoff point above the start) and the offset
    vector (vehicle 2 - vehicle 1), with the vertical component that equalizes the takeoff climbs; and the two
    start rest heights."""
    c = centre(g, plan) if c is None else c
    o = offset_vector(g, plan)
    r1, r2 = c - o / 2, c + o / 2
    z1 = gorge_plan.start_rest_z(g, r1[0, :2])
    z2 = gorge_plan.start_rest_z(g, r2[0, :2])
    r2 = r2 + [0, 0, z2 - z1]
    return r1, r2, r2[0] - r1[0], (z1, z2)


def write_plan(g, origin, route, out, land=None):
    """One vehicle's QGroundControl 5.1.5 plan file (fileType "Plan", version 1; mission version 2, firmwareType 3
    ArduPilot, vehicleType 2 quadrotor; empty geofence and rally points): takeoff at the start to the first point's
    height, spline waypoints, land at `land` (default the last point); altitudes relative to this vehicle's home (its
    rest height). Returns the plan."""
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
