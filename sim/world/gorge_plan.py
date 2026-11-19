"""The gorge mission as QGroundControl 5.1.5 plan items, and the X500's rest height on the gorge floor.

Items (`plan_items`: SimpleItem dictionaries as QGroundControl's MissionItem.cc `save` writes them, all in frame 3,
MAV_FRAME_GLOBAL_RELATIVE_ALT: altitude above home):
  1        NAV_TAKEOFF (22) at the start, to the first waypoint's height;
  2 .. n-1 NAV_SPLINE_WAYPOINT (82) along the gorge (`Gorge.path` after its first point: 3.5 m above the floor on the
           centerline), no hold, param4 null;
  n        NAV_LAND (21) at the last waypoint.
Altitudes are relative to home, the X500 resting on the floor at the start (`start_rest_z`): waypoint height above the
floor + floor rise - the start's rest height. Latitudes and longitudes are geo.Origin.latlon_e7's integers / 1e7.
"""
import math

import numpy as np

REST_H = 0.2       # m, the X500's base above the ground when resting (collision cylinder 0.22 m, offset -0.09 m)


def start_rest_z(g, xy, radius=0.25):
    """Height (ENU z) of the vehicle's base resting at xy: the highest ground point under its disc + REST_H."""
    ang = np.linspace(0, 2 * np.pi, 13)[:-1]
    pts = [xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.12, radius) for a in ang]
    return float(np.max(g.ground_z(np.array(pts)))) + REST_H


def plan_items(g, origin):
    """The plan's items for the waypoint path g.path, and home's height (ENU z of the X500 resting at the start)."""
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
