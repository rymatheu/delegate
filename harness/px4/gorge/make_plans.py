#!/usr/bin/env python3
"""PX4 QGroundControl plans for the gorge routes, generated from the simulator's ArduCopter plans.

    python3 -I px4/gorge/make_plans.py [--src DIR] [--out px4/plans] [--speed 2.0] [--accept 1.0]

The simulator's plans (DIR: gorge.plan, formation-{abreast,staggered}-v{1,2}.plan; default the
shared simulator's plan folder, sim/plans at the repository root, or $GORGE_PLANS) are written for
ArduCopter: a takeoff, NAV_SPLINE_WAYPOINT items, and for the staggered plan's rear vehicle a
CONDITION_YAW item before each waypoint. PX4 flies neither spline waypoints nor CONDITION_YAW in a
mission, so each plan is rewritten item by item, keeping every point:

  NAV_TAKEOFF (22)          the same point and altitude (above home), yaw free;
  DO_CHANGE_SPEED (178)     ground speed --speed m/s for the whole route (PX4's MPC_XY_CRUISE is 5);
  NAV_WAYPOINT (16)         for each spline waypoint: the same point and altitude, straight legs,
                            acceptance radius --accept m (param 2), no hold; param 4 (yaw) is the
                            heading of the CONDITION_YAW item before it if there is one, else free
                            (PX4 then faces the next waypoint, MPC_YAW_MODE 0);
  NAV_WAYPOINT (16)         if the land site is not the last waypoint (the formation plans' level
                            land sites, up to 6 m ahead): the land site at the last waypoint's
                            altitude, with the last waypoint's heading, so that the vehicle arrives
                            above it with the heading of the route (PX4 drops the yaw of a land
                            item, mission_base.cpp:624, and would turn to face the land site);
  NAV_LAND (21)             the same point: a vertical descent there.

The simulator's waypoints lie on the gorge's centerline (or a constant offset from it) and the
straight leg between two of them stays within 0.35 m of the centerline (the route's own
construction, Gorge.flight_path max_dev), so no points are added. Latitudes and longitudes are the
source's values. The plans are QGroundControl plan files for PX4 (firmwareType 12, vehicleType 2):
open one in Plan view and upload it. Deterministic: rerunning gives the same bytes."""
import argparse
import json
import math
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PX4_DIR = HERE.parent
NAMES = ["gorge"] + [f"formation-{p}-v{v}" for p in ("abreast", "staggered") for v in (1, 2)]
TAKEOFF, LAND, WAYPOINT, SPLINE, CONDITION_YAW, CHANGE_SPEED = 22, 21, 16, 82, 115, 178
REL_ALT, MISSION = 3, 2           # MAV_FRAME_GLOBAL_RELATIVE_ALT, MAV_FRAME_MISSION


def default_src():
    if os.environ.get("GORGE_PLANS"):
        return Path(os.environ["GORGE_PLANS"])
    return PX4_DIR.parent.parent / "sim" / "plans"   # harness/px4 -> repository root -> sim/plans


def item(seq, cmd, frame, params):
    return {"type": "SimpleItem", "command": cmd, "frame": frame, "autoContinue": True,
            "doJumpId": seq, "params": params}


def convert(src, speed, accept):
    """The PX4 plan of one ArduCopter plan, and the headings it asks for (deg, per waypoint)."""
    m = src["mission"]
    out, yaw, headings = [], None, []
    for it in m["items"]:
        cmd, p = it["command"], it["params"]
        seq = len(out) + 1
        if cmd == TAKEOFF:
            out.append(item(seq, TAKEOFF, REL_ALT, [0, 0, 0, None, p[4], p[5], p[6]]))
            out.append(item(seq + 1, CHANGE_SPEED, MISSION, [1, speed, -1, 0, 0, 0, 0]))
        elif cmd == CONDITION_YAW:
            yaw = round(float(p[0]) % 360.0, 2)   # the heading of the next waypoint (absolute, deg)
        elif cmd == SPLINE:
            out.append(item(seq, WAYPOINT, REL_ALT, [0, accept, 0, yaw, p[4], p[5], p[6]]))
            headings.append(yaw)
            yaw = None
        elif cmd == LAND:
            last = out[-1]["params"]
            if (last[4], last[5]) != (p[4], p[5]):
                out.append(item(seq, WAYPOINT, REL_ALT, [0, accept, 0, last[3], p[4], p[5], last[6]]))
                headings.append(last[3])
                seq += 1
            out.append(item(seq, LAND, REL_ALT, [0, 0, 0, None, p[4], p[5], 0]))
        else:
            raise SystemExit(f"make_plans: item {cmd} not converted")
    plan = {"fileType": "Plan", "version": 1, "groundStation": "QGroundControl",
            "mission": {"version": 2, "firmwareType": 12, "vehicleType": 2,
                        "cruiseSpeed": speed, "hoverSpeed": speed,
                        "plannedHomePosition": m["plannedHomePosition"], "items": out},
            "geoFence": {"version": 2, "circles": [], "polygons": []},
            "rallyPoints": {"version": 2, "points": []}}
    return plan, headings


def leg_bearings(plan):
    """Bearing (deg) of each leg between consecutive positioned items, flat-earth."""
    pts = [(i["params"][4], i["params"][5]) for i in plan["mission"]["items"] if i["command"] != CHANGE_SPEED]
    out = []
    for (a, b), (c, d) in zip(pts, pts[1:]):
        dn, de = c - a, (d - b) * math.cos(math.radians(a))
        out.append(math.degrees(math.atan2(de, dn)) % 360 if (dn or de) else None)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--src", default=None, help="folder of the simulator's plans (default sim/plans)")
    ap.add_argument("--out", default=str(PX4_DIR / "plans"))
    ap.add_argument("--speed", type=float, default=2.0, help="ground speed along the route, m/s")
    ap.add_argument("--accept", type=float, default=1.0, help="waypoint acceptance radius, m")
    a = ap.parse_args()
    src = Path(a.src) if a.src else default_src()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for name in NAMES:
        plan, headings = convert(json.loads((src / f"{name}.plan").read_text()), a.speed, a.accept)
        (out / f"{name}.plan").write_text(json.dumps(plan, indent=4) + "\n")
        legs = leg_bearings(plan)
        back = [h for h in headings if h is not None]
        note = ""
        if back:
            # each waypoint's heading against the leg flown to it (legs[0] is the takeoff point to waypoint 1)
            off = [((h - l + 180) % 360) - 180 for h, l in zip(headings, legs) if h is not None and l is not None]
            note = (f"; heading set on {len(back)} waypoints, {min(abs(x) for x in off):.0f} to "
                    f"{max(abs(x) for x in off):.0f} deg from the direction of travel")
        print(f"{out / (name + '.plan')}: {len(plan['mission']['items'])} items "
              f"({sum(1 for i in plan['mission']['items'] if i['command'] == WAYPOINT)} waypoints){note}")


if __name__ == "__main__":
    main()
