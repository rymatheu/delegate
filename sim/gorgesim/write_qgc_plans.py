#!/usr/bin/env python3
"""Write the gorge missions as QGroundControl plan files, for the real-time sessions (sim/fly_qgc.sh): exactly the items
the scripted ground stations upload, from the same code.

    .venv/bin/python sim/gorgesim/write_qgc_plans.py [--out sim/plans]

Writes OUT/gorge.plan (missions.gorge_mission, as sim/fly_gorge.py uploads it) and
OUT/formation-{abreast,staggered}-v{1,2}.plan (missions.formation_missions with sim/fly_gorge_formation.py's default
options, i.e. the staggered plan's vehicle 2 reversed: a MAV_CMD_CONDITION_YAW item before each spline waypoint).

Plan format: QGroundControl's .plan JSON (fileType "Plan", version 1; mission version 2, firmwareType 3 = ArduPilot,
vehicleType 2 = quadrotor, plannedHomePosition = the scripted station's seq 0 home item [lat, lon, alt AMSL]; empty
geofence and rally points). Each item is a SimpleItem with the scripted item's command, params 1..4, latitude, longitude
and altitude, in order (doJumpId = mission seq). Two deliberate differences of form, the same mission on the vehicle:
- frame: 3 (MAV_FRAME_GLOBAL_RELATIVE_ALT, QGroundControl's frame for plan items) where the scripted station sends 6
  (MAV_FRAME_GLOBAL_RELATIVE_ALT_INT); AP_Mission stores both as altitude above home. CONDITION_YAW items keep frame 2.
- latitude and longitude: QGroundControl sends param5 * 1e7 converted to int32 by truncation toward zero
  (PlanManager::_writeMissionItem), so each value is written as the double nearest to n / 1e7 whose product with 1e7
  truncates to the scripted integer n (at most a few ulps away; the JSON keeps all 17 digits).
The spline items' param4 is 0, as the scripted station sends it (ArduPilot answers a NaN param4 of NAV_SPLINE_WAYPOINT
with MAV_MISSION_INVALID_PARAM4), where QGroundControl's own spline items would have null.
"""
import argparse
import json
import math
import sys
import tempfile
from pathlib import Path

SIM_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SIM_DIR))
sys.dont_write_bytecode = True

from gorgesim import missions  # noqa: E402
from gorgesim.simulator import GORGE_SEED, gorge_origin  # noqa: E402


def qgc_degrees(x: float) -> float:
    """A double v with int(v * 1e7) (QGroundControl's truncation) equal to round(x * 1e7), the scripted integer."""
    n = int(round(x * 1e7))
    v = n / 1e7
    away = math.inf if n >= 0 else -math.inf
    for _ in range(64):
        if int(v * 1e7) == n:
            return v
        v = math.nextafter(v, away)
    raise ValueError(f"no double truncates to {n}")


def plan_json(items, m):
    """A QGroundControl plan from the scripted items [(command, frame, (p1..p4), lat, lon, alt)], seq 0 the home."""
    home = items[0]
    out = []
    for seq, (cmd, frame, p, lat, lon, alt) in enumerate(items[1:], start=1):
        if frame == m.MAV_FRAME_MISSION:
            f, ll = int(frame), [float(lat), float(lon)]
        else:
            f, ll = 3, [qgc_degrees(lat), qgc_degrees(lon)]
        out.append({"type": "SimpleItem", "command": int(cmd), "frame": f, "autoContinue": True, "doJumpId": seq,
                    "params": [float(x) for x in p] + ll + [float(alt)]})
    return {"fileType": "Plan", "version": 1, "groundStation": "QGroundControl",
            "mission": {"version": 2, "firmwareType": 3, "vehicleType": 2,
                        "plannedHomePosition": [qgc_degrees(home[3]), qgc_degrees(home[4]), float(home[5])],
                        "items": out},
            "geoFence": {"version": 2, "circles": [], "polygons": []},
            "rallyPoints": {"version": 2, "points": []}}


def single_items(m):
    import gorge as G
    g = G.Gorge(GORGE_SEED)
    origin = gorge_origin()
    items, _ = missions.gorge_mission(m, g, origin)
    return items, g, origin


def formation_items(m, g, origin, plan):
    reverse = tuple(int(x) for x in missions.FP.PLANS[plan]["reverse"])
    with tempfile.TemporaryDirectory() as tmp:                  # formation_missions also writes formation_plan's plans
        ms, _ = missions.formation_missions(g, origin, plan, m, Path(tmp), reverse)
    return [x["items"] for x in ms]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", default=str(SIM_DIR / "plans"))
    a = ap.parse_args()
    from pymavlink.dialects.v20 import ardupilotmega as m
    out = Path(a.out)
    items, g, origin = single_items(m)
    files = {"gorge.plan": items}
    for plan in ("abreast", "staggered"):
        for v, its in enumerate(formation_items(m, g, origin, plan), start=1):
            files[f"formation-{plan}-v{v}.plan"] = its
    for name, its in files.items():
        (out / name).write_text(json.dumps(plan_json(its, m), indent=4) + "\n")
        print(f"{out / name}: home + {len(its) - 1} items "
              f"({', '.join(f'{c}' for c, *_ in its[1:])})")


if __name__ == "__main__":
    main()
