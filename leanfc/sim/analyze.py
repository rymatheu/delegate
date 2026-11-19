"""Metrics and a figure for one leanfc run. Usage: analyze.py run.csv [--plot out.png]

Report: tracking error to the moving target (max, with where it occurs, and rms); per waypoint the
vehicle's closest approach (distance and time, over the ticks whose leg column is that waypoint's leg
or the next); the mission time (first time from which the vehicle stays within nav.radius of the last
waypoint to the end of the run) and the time the navigator completes the mission (the leg column reaches the
number of legs); the largest distance of the target path from the straight polyline
start -> waypoints (how far spline legs depart from the chords); the target's largest speed (one-tick
differences of the target column); hold error over the last 4 s, estimate and
attitude-estimate errors, tilt, motors and saturated ticks.

CSV columns (one row per 400 Hz tick): t, p_n, p_e, p_d, v_n, v_e, v_d, q_w, q_x, q_y, q_z,
ph_n, ph_e, ph_d, vh_n, vh_e, vh_d, qh_w, qh_x, qh_y, qh_z, sp_n, sp_e, sp_d, leg, m1, m2, m3, m4.
The waypoints come from the run's JSON sidecar (run.json next to run.csv, written by run_leanfc.py
from the parameter file); a CSV without one is taken to be a CF2X run of the pyfc 1 m square.

A run made with `run_leanfc.py --trace-ekf` has more columns: the diagonal of P (P0..P14), the bias
estimates (bg_*, ba_*) and the true position, velocity and attitude at the start of each tick (pt_*,
vt_*, qt_*), the instant the estimate refers to. For it the report adds: position, velocity and
attitude estimate errors against that start-of-tick truth (rms and max over the run), the gyro and
accelerometer bias errors at the end against the true biases of the sidecar (for the fixed estimator,
whose acceleration bias is NED, against R(q) b_a), and, for the EKF, the fraction of position-error
components inside +-3 sigma of P.

A run whose CSV ends with the heading setpoint (hsp_c, hsp_s; every run of a controller that prints
it) also gets the heading report: the true yaw against the setpoint (rms and max of the wrapped
difference), the largest true yaw rate and the largest setpoint rate (one-tick differences).
"""
import json
import sys
from pathlib import Path

import numpy as np

CF2X_SQUARE = [[1, 0, -1.0], [1, 1, -1.5], [0, 1, -1.5], [0, 0, -1.0]]
HZ = 400


def waypoints(csv_path):
    side = Path(csv_path).with_suffix(".json")
    if side.exists():
        meta = json.loads(side.read_text())
        return np.array(meta["waypoints"], dtype=float), meta
    return np.array(CF2X_SQUARE), None


def load(path):
    d = np.genfromtxt(path, delimiter=",", names=True)
    cols = lambda *n: np.column_stack([d[c] for c in n])
    log = dict(t=d["t"], p=cols("p_n", "p_e", "p_d"), v=cols("v_n", "v_e", "v_d"),
               q=cols("q_w", "q_x", "q_y", "q_z"), p_hat=cols("ph_n", "ph_e", "ph_d"),
               v_hat=cols("vh_n", "vh_e", "vh_d"), q_hat=cols("qh_w", "qh_x", "qh_y", "qh_z"),
               p_sp=cols("sp_n", "sp_e", "sp_d"), leg=d["leg"].astype(int), m=cols("m1", "m2", "m3", "m4"))
    if "hsp_c" in d.dtype.names:
        log.update(hsp=cols("hsp_c", "hsp_s"))
    if "P0" in d.dtype.names:
        log.update(Pd=cols(*[f"P{i}" for i in range(15)]), bg=cols("bg_x", "bg_y", "bg_z"),
                   ba=cols("ba_x", "ba_y", "ba_z"), pt=cols("pt_n", "pt_e", "pt_d"),
                   vt=cols("vt_n", "vt_e", "vt_d"), qt=cols("qt_w", "qt_x", "qt_y", "qt_z"))
    return log


def rotate(q, v):
    """R(q) v for one (w, x, y, z) body-to-world quaternion."""
    w, x, y, z = q
    R = np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                  [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                  [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])
    return R @ np.asarray(v)


def ekf_report(log, meta):
    """Estimate errors against the start-of-tick truth, bias errors at the end, 3 sigma fraction."""
    rms = lambda x: float(np.sqrt(np.mean(x ** 2)))
    pe = np.linalg.norm(log["pt"] - log["p_hat"], axis=1)
    ve = np.linalg.norm(log["vt"] - log["v_hat"], axis=1)
    ae = np.degrees(att_err(log["qt"], log["q_hat"]))
    r = dict(pe_rms=rms(pe), pe_max=float(pe.max()), ve_rms=rms(ve), ve_max=float(ve.max()),
             ae_rms=rms(ae), ae_max=float(ae.max()))
    print(f"  estimate errors (start-of-tick truth): position rms {r['pe_rms']*1000:.1f} mm (max {r['pe_max']*1000:.1f}), "
          f"velocity rms {r['ve_rms']*1000:.1f} mm/s (max {r['ve_max']*1000:.1f}), "
          f"attitude rms {r['ae_rms']:.2f} deg (max {r['ae_max']:.2f})")
    if meta and "gyro_bias" in meta:
        ekf = meta.get("estimator") == "ekf"
        ba_true = np.asarray(meta["accel_bias"]) if ekf else rotate(log["q"][-1], meta["accel_bias"])
        r["bg_err"] = float(np.degrees(np.linalg.norm(log["bg"][-1] - np.asarray(meta["gyro_bias"]))))
        r["ba_err"] = float(np.linalg.norm(log["ba"][-1] - ba_true))
        print(f"  bias errors at the end: gyro {r['bg_err']:.4f} deg/s, accelerometer {r['ba_err']*1000:.1f} mm/s^2"
              + ("" if ekf else " (fixed: NED acceleration bias against R(q) b_a)"))
        if ekf:
            sig = np.sqrt(log["Pd"][:, 6:9])
            inside = np.abs(log["pt"] - log["p_hat"]) <= 3 * sig
            r["in3"] = float(np.mean(inside))
            print(f"  position-error components inside +-3 sigma of P: {r['in3']*100:.2f}% "
                  f"(north {np.mean(inside[:, 0])*100:.2f}, east {np.mean(inside[:, 1])*100:.2f}, "
                  f"down {np.mean(inside[:, 2])*100:.2f}); min diag P {log['Pd'].min():.3g}")
    return r


def yaw_of(q):
    """Yaw (rad) of (w, x, y, z) body-to-NED quaternions: the heading of the body x axis."""
    w, x, y, z = q.T
    return np.arctan2(2 * (w * z + x * y), 1 - 2 * (y * y + z * z))


def heading_report(log):
    """True yaw against the controller's heading setpoint: tracking error (rms, max), largest true yaw
    rate and largest setpoint rate (finite differences of the unwrapped angles over one tick)."""
    yaw = yaw_of(log["q"])
    sp = np.arctan2(log["hsp"][:, 1], log["hsp"][:, 0])
    err = np.degrees(np.angle(np.exp(1j * (yaw - sp))))
    rate = np.degrees(np.abs(np.diff(np.unwrap(yaw)))) * HZ
    sp_rate = np.degrees(np.abs(np.diff(np.unwrap(sp)))) * HZ
    r = dict(hdg_rms=float(np.sqrt(np.mean(err ** 2))), hdg_max=float(np.abs(err).max()),
             yaw_rate_max=float(rate.max()), sp_rate_max=float(sp_rate.max()))
    print(f"  heading: tracking error rms {r['hdg_rms']:.2f} deg (max {r['hdg_max']:.2f} deg), "
          f"yaw rate max {r['yaw_rate_max']:.1f} deg/s (setpoint {r['sp_rate_max']:.1f} deg/s)")
    return r


def att_err(q, qh):
    # angle of conj(q) ⊗ qh
    w1, x1, y1, z1 = q[:, 0], -q[:, 1], -q[:, 2], -q[:, 3]
    w2, x2, y2, z2 = qh.T
    vx = w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2
    vy = w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2
    vz = w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2
    return 2 * np.arcsin(np.clip(np.sqrt(vx * vx + vy * vy + vz * vz), 0, 1))


def param_value(meta, name, default):
    """The last value of `name` in the run's parameter files (for sidecars written before they recorded it)."""
    v = default
    root = Path(__file__).resolve().parent.parent
    for f in (meta or {}).get("params", []):
        path = Path(f) if Path(f).is_absolute() else root / f
        if path.exists():
            for line in path.read_text().splitlines():
                ws = line.split("#", 1)[0].split()
                if len(ws) == 2 and ws[0] == name:
                    v = float(ws[1])
    return v


def seg_dist(x, a, b):
    """Distance of each row of x from the segment a-b."""
    ab = b - a
    t = np.clip(((x - a) @ ab) / max(ab @ ab, 1e-12), 0, 1)
    return np.linalg.norm(x - (a + t[:, None] * ab), axis=1)


def tilt_of(q):
    """Angle (deg) between the body z axis and the vertical."""
    return np.degrees(np.arccos(np.clip(1 - 2 * (q[:, 1] ** 2 + q[:, 2] ** 2), -1, 1)))


def report(log, wps, name="run", meta=None):
    t, p, sp, leg, m = log["t"], log["p"], log["p_sp"], log["leg"], log["m"]
    track = np.linalg.norm(p - sp, axis=1)
    hold = slice(-4 * HZ, None)
    est = np.linalg.norm(p - log["p_hat"], axis=1)
    ae = np.degrees(att_err(log["q"], log["q_hat"]))
    sat = int(np.sum((m <= 0) | (m >= 1)))
    radius = (meta or {}).get("radius") or param_value(meta, "nav.radius", 0.1)
    start = np.asarray((meta or {}).get("start", p[0]), dtype=float)
    pts = np.vstack([start, wps])
    print(f"{name}: {len(t)} ticks, {t[-1]:.2f} s")
    if meta:
        lag = meta["motor_lag"]
        print(f"  {meta['vehicle']}, noise {meta['noise']}, seed {meta['seed']}, fix {meta['fix_hz']:g} Hz, "
              f"motor lag {'off' if lag is None else f'{lag[0]:g}/{lag[1]:g} s'}, params {' + '.join(meta['params'])}, "
              f"wall {meta['wall_s']:.1f} s" + (f", legs {' '.join(k.split()[0][0] + ('!' if 'stop' in k else '') for k in meta['legs'])}"
                                               if meta.get("legs") else ""))
    k = int(np.argmax(track))
    near = int(np.argmin(np.linalg.norm(pts - sp[k], axis=1)))
    sp_speed = np.linalg.norm(np.diff(sp, axis=0), axis=1) * HZ
    print(f"  tracking error to the moving target: max {track.max()*1000:.1f} mm at t={t[k]:.3f} s (leg {leg[k]}, target "
          f"{np.linalg.norm(sp[k]-pts[near])*1000:.0f} mm from {'the start' if near == 0 else f'waypoint {near}'}, target speed "
          f"{sp_speed[min(k, len(sp_speed)-1)]:.2f} m/s), rms {np.sqrt(np.mean(track**2))*1000:.1f} mm")
    closest = []
    for i, w in enumerate(wps):
        win = np.where((leg == i) | (leg == i + 1))[0]
        if not len(win):
            win = np.arange(len(t))
        d = np.linalg.norm(p[win] - w, axis=1)
        j = int(np.argmin(d))
        closest.append((float(d[j]), float(t[win[j]])))
    print("  closest approach of the vehicle: " + ", ".join(f"wp {i + 1} {d*1000:.0f} mm at {tt:.2f} s"
                                                         for i, (d, tt) in enumerate(closest)))
    inside = np.linalg.norm(p - wps[-1], axis=1) <= radius
    out = np.where(~inside)[0]
    k_in = 0 if not len(out) else out[-1] + 1
    mission = float(t[k_in]) if k_in < len(t) else None
    done = int(leg.max())
    kc = np.where(leg >= len(wps))[0]
    complete = float(t[kc[0]]) if len(kc) else None
    poly = np.min(np.column_stack([seg_dist(sp, pts[i], pts[i + 1]) for i in range(len(wps))]), axis=1)
    tilt = tilt_of(log["q"])
    print(f"  mission time {'not reached' if mission is None else f'{mission:.2f} s'} (vehicle within {radius:g} m of the last "
          f"waypoint from then on), navigator complete {'never' if complete is None else f'at {complete:.2f} s'} (leg column = number "
          f"of legs: target at rest on the last waypoint and the estimate within radius), legs done {done}/{len(wps)}; target path from the straight polyline: max "
          f"{poly.max()*1000:.0f} mm; target speed max {sp_speed.max():.2f} m/s (one-tick differences)")
    print(f"  hold (last 4 s): error max {np.linalg.norm(p[hold]-wps[-1],axis=1).max()*1000:.1f} mm, "
          f"estimate error rms {np.sqrt(np.mean(est[hold]**2))*1000:.1f} mm (over run: rms {np.sqrt(np.mean(est**2))*1000:.1f} mm, max {est.max()*1000:.1f} mm), "
          f"attitude error rms {np.sqrt(np.mean(ae[hold]**2)):.2f} deg (max {ae.max():.2f} deg)")
    print(f"  tilt max {tilt.max():.1f} deg, motors {m.min():.3f}-{m.max():.3f}, saturated ticks {sat}")
    r = dict(track_max=track.max(), track_rms=np.sqrt(np.mean(track ** 2)), track_max_t=float(t[k]),
             hold_max=np.linalg.norm(p[hold]-wps[-1], axis=1).max(), done=done, sat=sat,
             att_max=ae.max(), est_rms=np.sqrt(np.mean(est**2)), mission=mission, complete=complete, closest=closest,
             closest_max=max(d for d, _ in closest), poly_max=float(poly.max()), tilt_max=float(tilt.max()),
             sp_speed_max=float(sp_speed.max()), m_min=float(m.min()), m_max=float(m.max()))
    if "hsp" in log:
        r.update(heading_report(log))
    if "pt" in log:
        r.update(ekf_report(log, meta))
    return r


def plot(log, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    t, p, sp = log["t"], log["p"], log["p_sp"]
    fig, ax = plt.subplots(2, 2, figsize=(9, 7))
    ax[0, 0].plot(sp[:, 1], sp[:, 0], "k--", lw=0.8, label="target")
    ax[0, 0].plot(p[:, 1], p[:, 0], label="vehicle")
    ax[0, 0].plot(log["p_hat"][:, 1], log["p_hat"][:, 0], ":", lw=0.8, label="estimate")
    ax[0, 0].set_xlabel("east [m]"); ax[0, 0].set_ylabel("north [m]"); ax[0, 0].set_aspect("equal"); ax[0, 0].legend(fontsize=8)
    ax[0, 1].plot(t, -p[:, 2], label="altitude"); ax[0, 1].plot(t, -sp[:, 2], "k--", lw=0.8, label="target")
    ax[0, 1].set_xlabel("t [s]"); ax[0, 1].set_ylabel("altitude [m]"); ax[0, 1].legend(fontsize=8)
    ax[1, 0].plot(t, np.linalg.norm(p - sp, axis=1) * 1000); ax[1, 0].set_xlabel("t [s]"); ax[1, 0].set_ylabel("|p − target| [mm]")
    ax[1, 1].plot(t, log["m"], lw=0.6); ax[1, 1].set_xlabel("t [s]"); ax[1, 1].set_ylabel("motors")
    fig.tight_layout(); fig.savefig(out, dpi=130); print("wrote", out)


if __name__ == "__main__":
    log = load(sys.argv[1])
    wps, meta = waypoints(sys.argv[1])
    report(log, wps, sys.argv[1], meta)
    if "--plot" in sys.argv:
        plot(log, sys.argv[sys.argv.index("--plot") + 1])
