"""The missions: the gorge mission (one X500) and the two formation missions (two X500s) as the items a scripted ground
station uploads, (command, frame, (param1..4), lat, lon, alt) with seq 0 the home. sim/gorgesim/write_qgc_plans.py writes
the same items as the QGroundControl plans of sim/plans/.

The gorge mission (`gorge_mission`): gorge_plan.plan_items' items (the plan's latitudes and longitudes, the
geo.Origin.latlon_e7 integers, and its relative altitudes), uploaded as MISSION_ITEM_INT: NAV_TAKEOFF at the start, the
10 NAV_SPLINE_WAYPOINTs, NAV_LAND at the last waypoint. The plan's param4 null of the spline items is sent as 0:
AP_Mission::sanity_check_params allows NaN in param4 only for WAYPOINT, LOITER_UNLIM, LAND, TAKEOFF, ARC_WAYPOINT and the
VTOL items, and answers a NaN param4 of NAV_SPLINE_WAYPOINT with MAV_MISSION_INVALID_PARAM4. The plan's relative
altitudes refer to the X500's rest height (base 0.2 m above the floor, gorge_plan.start_rest_z), so every waypoint is
where the plan puts it in the world, 3.5 m above the floor on the centerline. `respaced_path` and `PathView` give the
same mission on other waypoints of the centerline (ardulean/sim/fly_gorge.py --spline-north, --straight-north).

The formation missions (`formation_missions`): sim/world/formation_plan.py's route centre, the two routes and the land
sites, written as plans and translated as the single route is.
"""
import sys

import numpy as np

import formation_plan as FP
import gorge as G
import gorge_plan as GP


class PathView:
    """A Gorge with another waypoint path (--spline-north) for gorge_plan.plan_items: every attribute is the
    Gorge's except .path (the Gorge object itself is not modified)."""

    def __init__(self, g, path):
        self._g = g
        self.path = path

    def __getattr__(self, name):
        return getattr(self._g, name)


def respaced_path(g, north):
    """The takeoff point of g.path, then spline waypoints on the gorge's centerline at the north coordinates `north`
    (Gorge.flight_path's points: x_c(y), y, floor_c(y) + gorge.FLIGHT_H); the last one must be the plan's last waypoint."""
    ys = np.array(north, float)
    if len(ys) < 2 or np.any(np.diff(ys) <= 0) or ys[0] <= g.path[0, 1] or abs(ys[-1] - g.path[-1, 1]) > 1e-9:
        sys.exit(f"fly_gorge: --spline-north must increase from above {g.path[0, 1]} and end at the plan's last "
                 f"waypoint north {g.path[-1, 1]}")
    pts = np.stack([g.xc_fn(ys), ys, g.floor_c(ys) + G.FLIGHT_H], -1)
    return np.vstack([g.path[:1], pts])


def gorge_mission(m, g, origin, leg_cmd=None):
    """The plan's items (gorge_plan.plan_items) for g.path, seq 0 home at the plan's planned home, the relative
    altitudes the plan's; with leg_cmd the spline waypoints sent as that command (MAV_CMD_NAV_WAYPOINT: straight
    legs). Returns the items and the plan's items."""
    items, home_z = GP.plan_items(g, origin)
    lat0, lon0 = origin.latlon_e7(g.path[0, 1], g.path[0, 0])
    FR = m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT
    out = [(m.MAV_CMD_NAV_WAYPOINT, m.MAV_FRAME_GLOBAL, (0, 0, 0, 0), lat0 / 1e7, lon0 / 1e7, origin.alt_m + home_z)]
    for it in items:
        q = it["params"]
        rel = 0.0 if it["command"] == 21 else float(q[6])
        p4 = 0.0 if q[3] is None else float(q[3])       # the plan's null: ArduPilot refuses NaN here (see above)
        cmd = leg_cmd if (leg_cmd is not None and it["command"] == 82) else it["command"]
        out.append((cmd, FR, (float(q[0]), float(q[1]), float(q[2]), p4), float(q[4]), float(q[5]), rel))
    return out, items


def leg_headings(route):
    """NED compass heading (deg, 0..360) of each leg of a route (ENU waypoints, the first the takeoff point): leg k from
    route[k - 1] to route[k], k = 1..len - 1."""
    d = np.diff(np.asarray(route, float)[:, :2], axis=0)
    return np.degrees(np.arctan2(d[:, 0], d[:, 1])) % 360.0


def formation_missions(g, origin, plan, m, out, reverse=(0, 0), yaw_rate=10.0):
    """The two vehicles' plans (formation_plan: route centre, routes, land sites; write_plan into OUT/vN/) and their
    ArduCopter items as gorge_mission builds them (seq 0 home at the planned home, then the plan's items in
    MAV_FRAME_GLOBAL_RELATIVE_ALT_INT, the spline items' param4 null sent as 0). A vehicle with reverse[v] set gets, before
    each spline waypoint item k, a MAV_CMD_CONDITION_YAW item (absolute heading = the direction of leg k + 180 deg,
    yaw_rate deg/s, shortest way). AP_Mission starts the do and condition commands that follow a nav command when that nav
    command completes (it runs them while the next nav command flies), so the item placed after nav item k - 1 (the
    takeoff for k = 1) turns the nose while the vehicle flies leg k toward waypoint k (placed after the
    waypoints, they would turn it one leg late); with WP_YAW_BEHAVIOR 0 the spline waypoint
    keeps the FIXED heading (ModeAuto::sl_start: the yaw mode is reset to the default unless it is ROI, or
    FIXED with WP_YAW_BEHAVIOR NONE); its start heading (`start_yaw_deg`) is leg 1's + 180 deg."""
    c = FP.centre(g, plan)
    r1, r2, o, rest_z = FP.routes(g, plan, c)
    lands = FP.land_sites(g, r1, r2)
    FR = m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT
    res = []
    for v, (r, land) in enumerate(zip((r1, r2), lands), start=1):
        (out / f"v{v}").mkdir(parents=True, exist_ok=True)
        qplan = FP.write_plan(g, origin, r, out / f"v{v}" / f"formation-{plan}-v{v}.plan", land)
        home = qplan["mission"]["plannedHomePosition"]
        items = [(m.MAV_CMD_NAV_WAYPOINT, m.MAV_FRAME_GLOBAL, (0, 0, 0, 0), home[0], home[1], home[2])]
        rev = bool(reverse[v - 1])
        heads = (leg_headings(r) + 180.0) % 360.0
        n_spl = 0
        for it in qplan["mission"]["items"]:
            q = it["params"]
            rel = 0.0 if it["command"] == 21 else float(q[6])
            p4 = 0.0 if q[3] is None else float(q[3])
            if it["command"] == 82:
                n_spl += 1
                if rev:
                    items.append((m.MAV_CMD_CONDITION_YAW, m.MAV_FRAME_MISSION, (round(float(heads[n_spl - 1]), 2), float(yaw_rate), 0.0, 0.0),
                                  0.0, 0.0, 0.0))
            items.append((it["command"], FR, (float(q[0]), float(q[1]), float(q[2]), p4), float(q[4]), float(q[5]), rel))
        nav = {s: k for k, s in enumerate([s for s, it in enumerate(items) if s == 0 or it[0] in (16, 21, 22, 82)])}
        res.append(dict(route=r, land=np.asarray(land, float), items=items, plan_items=qplan["mission"]["items"],
                        rest_z=float(rest_z[v - 1]), planned_home=home, reverse=rev, nav_index=nav, n_spline=n_spl,
                        start_yaw_deg=float(heads[0]) if rev else 0.0, yaw_items_deg=[float(h) for h in heads] if rev else []))
    return res, np.asarray(o, float)
