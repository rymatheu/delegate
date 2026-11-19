"""The 100 Hz flight record (track.csv) and the flight numbers computed from it.

Every 4th step (REC_EVERY, 100 Hz) a flight program records per vehicle: time, the true pose (ENU position, PyBullet
quaternion), the NED velocity as (vn, ve, up), the four actuators, the clearance (closest distance from the vehicle's
collision cylinder to every body of the gorge, up to CLEAR_MAX, PyBullet getClosestPoints), the contact count, and from
the downlink the armed state, the mode and the mission item (TRACK_COLS).
"""
import math

import numpy as np

REC_EVERY = 4                            # steps per record row (100 Hz)
CLEAR_MAX = 4.0                          # m: clearances beyond are recorded as CLEAR_MAX
TRACK_COLS = "t,x,y,z,qx,qy,qz,qw,vn,ve,vz_up,m1,m2,m3,m4,clearance,contacts,armed,mode,item".split(",")


def seg_dist(q, route):
    """Distance of each point of q (N x 3) to the polyline route (M x 3)."""
    best = np.full(len(q), np.inf)
    for p0, p1 in zip(route[:-1], route[1:]):
        v = p1 - p0
        s = np.clip((q - p0) @ v / (v @ v), 0, 1)
        best = np.minimum(best, np.linalg.norm(q - (p0 + s[:, None] * v), axis=1))
    return best


def gorge_metrics(track, rec, gpath, home_z, n_spline):
    """Flight numbers from the 100 Hz record. 'In the air' (after the takeoff and before the landing) is here from the takeoff item's MISSION_ITEM_REACHED to the MISSION_CURRENT of the
    land item; contacts are counted from the liftoff (the first record without contact after arming) to the touchdown
    (the first contact after the land item began)."""
    t = track["t"]
    pos = np.column_stack([track["x"], track["y"], track["z"]])
    out = {}
    reached = [s for _, s in rec["reached"]]
    out["reached"] = reached
    out["current"] = [s for _, s in rec["current"]]
    land_seq = n_spline + 2
    t_to = next((tt for tt, s in rec["reached"] if s == 1), None)
    t_land = next((tt for tt, s in rec["current"] if s == land_seq), None)
    if rec.get("t_arm") is not None and rec.get("t_disarm") is not None:
        out["arm_to_disarm_s"] = rec["t_disarm"] - rec["t_arm"]
    armed = track["armed"] > 0
    contact = track["contacts"] > 0
    if armed.any():
        k_arm = int(np.argmax(armed))
        free = np.nonzero(~contact[k_arm:])[0]
        k_lift = k_arm + int(free[0]) if len(free) else None
        k_td = None
        if k_lift is not None and t_land is not None:
            after = np.nonzero(contact & (t >= t_land))[0]
            k_td = int(after[0]) if len(after) else None
        if k_lift is not None:
            k_end = k_td if k_td is not None else len(t)
            out["liftoff_t"] = float(t[k_lift])
            out["touchdown_t"] = float(t[k_td]) if k_td is not None else None
            out["contacts_between_liftoff_and_touchdown"] = int(contact[k_lift:k_end].sum())
            if k_td is not None:
                out["touchdown_speed_down_ms"] = float(-track["vz_up"][max(k_td - 1, 0)])
                out["landing_error_m"] = float(np.hypot(*(pos[k_td, :2] - gpath[-1, :2])))
    if t_to is not None and t_land is not None:
        air = (t >= t_to) & (t < t_land)
        out["air_window_s"] = [float(t_to), float(t_land)]
        out["clearance_min_in_air_m"] = float(track["clearance"][air].min())
        k = int(np.nonzero(air)[0][np.argmin(track["clearance"][air])])
        out["clearance_min_at"] = dict(t=float(t[k]), north=float(pos[k, 1]), east=float(pos[k, 0]), up=float(pos[k, 2]))
        route = np.vstack([[gpath[0, 0], gpath[0, 1], home_z], gpath])
        d = seg_dist(pos[air], route)
        out["route_distance_in_air_max_m"] = float(d.max())
        out["route_distance_in_air_rms_m"] = float(math.sqrt((d ** 2).mean()))
        k = int(np.nonzero(air)[0][np.argmax(d)])
        out["route_distance_max_at"] = dict(t=float(t[k]), north=float(pos[k, 1]), east=float(pos[k, 0]), up=float(pos[k, 2]))
        gs = np.hypot(track["vn"], track["ve"])
        sp = np.sqrt(track["vn"] ** 2 + track["ve"] ** 2 + track["vz_up"] ** 2)
        out["ground_speed_max_ms"] = float(gs[air].max())
        out["speed_3d_max_ms"] = float(sp[air].max())
        tilt = np.degrees(np.arccos(np.clip(1 - 2 * (track["qx"] ** 2 + track["qy"] ** 2), -1, 1)))
        out["tilt_max_in_air_deg"] = float(tilt[air].max())
        m = np.column_stack([track[f"m{i}"] for i in range(1, 5)])
        out["actuator_range_in_air"] = [float(m[air].min()), float(m[air].max())]
    out["clearance_min_whole_record_m"] = float(track["clearance"].min())
    return out
