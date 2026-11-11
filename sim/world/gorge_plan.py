"""The gorge mission as a QGroundControl 5.1.5 plan file, and as the controller's parameter overlay.

Plan (`.plan`, the JSON of src/MissionManager/PlanMasterController.cc `saveToJson` and
MissionController.cc `_saveJsonMissionFileV2` at 5.1.5): fileType "Plan", version 1, groundStation
"QGroundControl"; mission version 2 with plannedHomePosition, firmwareType 3 (ArduPilot), vehicleType
2 (quadrotor) and no cruiseSpeed or hoverSpeed (no plan-wide speed, so no DO_CHANGE_SPEED item; and
QGroundControl writes those two keys into its offline-editing settings when it loads them); empty
geoFence and rallyPoints (version 2). Items (SimpleItem, MissionItem.cc `save`), all in frame 3
(MAV_FRAME_GLOBAL_RELATIVE_ALT: altitude above home):
  1        NAV_TAKEOFF (22) at the start, to the first waypoint's height;
  2 .. 10  NAV_SPLINE_WAYPOINT (82) along the gorge (`Gorge.path`: 3.5 m above the floor on the
           centerline, the waypoints of fly_gorge.py), no hold;
  11       NAV_LAND (21) at the last waypoint.
Altitudes are relative to home, which the controller sets at arming from its estimate of the vehicle
resting on the floor at the start: waypoint height above the floor + floor rise - the start's rest
height. Latitudes and longitudes are the controller's own `toLatLon` integers (geo.Origin.latlon_e7),
so the controller's `toNE` gives back each point within 1 cm.

Overlay (the session's parameter file after x500.params and ground.params): the start on the floor at
the first waypoint, and the same nine waypoints as SPLINE lines, so the onboard mission that
QGroundControl downloads at connect is the gorge route (AUTO from the ground still needs the uploaded
plan's takeoff item; "Auto: Missing Takeoff Cmd" otherwise).

    python gorge_plan.py [--gorge-seed 7] [--params FILE ...] [--origin LAT LON ALT] [--out gorge.plan]
"""
import argparse
import json
import math
from pathlib import Path

import numpy as np

import geo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
REST_H = 0.2       # m, the X500's base above the ground when resting (collision cylinder 0.22 m, offset -0.09 m)


def start_rest_z(g, xy, radius=0.25):
    """Height (ENU z) of the vehicle's base resting at xy: the highest ground point under its disc + REST_H."""
    ang = np.linspace(0, 2 * np.pi, 13)[:-1]
    pts = [xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.12, radius) for a in ang]
    return float(np.max(g.ground_z(np.array(pts)))) + REST_H


def site_check(g, xy, radius=0.6):
    """Ground relief (max - min of the ground height) within `radius` of xy: a boulder or step shows up."""
    ang = np.linspace(0, 2 * np.pi, 25)[:-1]
    pts = [xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.2, 0.4, radius) for a in ang]
    z = g.ground_z(np.array(pts))
    return float(z.max() - z.min())


def plan_items(g, origin):
    path = g.path
    home_z = start_rest_z(g, path[0, :2])
    items = []

    def item(cmd, x, y, rel, seq):
        lat, lon = origin.latlon_e7(y, x)
        return {"type": "SimpleItem", "command": cmd, "frame": 3, "autoContinue": True, "doJumpId": seq,
                "params": [0, 0, 0, None if cmd == 82 else 0, lat / 1e7, lon / 1e7, round(rel, 3)]}
    items.append(item(22, path[0, 0], path[0, 1], path[0, 2] - home_z, 1))
    for k, w in enumerate(path[1:], start=2):
        items.append(item(82, w[0], w[1], w[2] - home_z, k))
    items.append(item(21, path[-1, 0], path[-1, 1], 0.0, len(path) + 1))
    return items, home_z


def write_plan(g, origin, out):
    items, home_z = plan_items(g, origin)
    lat, lon = origin.latlon_e7(g.path[0, 1], g.path[0, 0])
    plan = {"fileType": "Plan", "version": 1, "groundStation": "QGroundControl",
            "mission": {"version": 2, "firmwareType": 3, "vehicleType": 2,
                        "plannedHomePosition": [lat / 1e7, lon / 1e7, round(origin.alt_m + home_z, 3)],
                        "items": items},
            "geoFence": {"version": 2, "circles": [], "polygons": []},
            "rallyPoints": {"version": 2, "points": []}}
    Path(out).write_text(json.dumps(plan, indent=4) + "\n")
    return plan, home_z


def write_overlay(g, out):
    """The session's parameter overlay (NED: north = ENU y, east = x, down = -z)."""
    path = g.path
    lines = ["# gorge session overlay (sim/world/gorge_plan.py): load after x500.params and ground.params",
             f"# gorge seed {g.seed}: start resting on the floor at the first waypoint; the onboard mission is the",
             "# gorge route (3.5 m above the floor on the centerline) as SPLINE legs",
             f"start.x             {path[0][1]:.4f}", f"start.y             {path[0][0]:.4f}",
             f"start.z             {-start_rest_z(g, path[0, :2]):.4f}"]
    lines += [f"SPLINE  {w[1]:.4f}  {w[0]:.4f}  {-w[2]:.4f}" for w in path[1:]]
    Path(out).write_text("\n".join(lines) + "\n")


def main():
    import gorge as G
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--params", action="append", default=None, help="parameter files with the ORIGIN line")
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"))
    ap.add_argument("--out", default=str(HERE / "gorge.plan"))
    a = ap.parse_args()
    files = a.params or [ROOT / "params/x500.params", ROOT / "params/ground.params"]
    origin = geo.Origin.from_params(files, a.origin)
    g = G.Gorge(a.gorge_seed)
    plan, home_z = write_plan(g, origin, a.out)
    print(f"{a.out}: {len(plan['mission']['items'])} items, origin {origin.lat_e7} {origin.lon_e7} {origin.alt_mm} mm, "
          f"home rest height z {home_z:.3f} m; ground relief within 0.6 m: start {site_check(g, g.path[0, :2]):.3f} m, "
          f"landing {site_check(g, g.path[-1, :2]):.3f} m")


if __name__ == "__main__":
    main()
