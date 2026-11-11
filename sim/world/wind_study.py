"""Wind study: closed-loop gorge flights (fly_gorge.py, cameras off, field noise) with the wind off,
at the default 4 m/s mean with gusts, and in steps of the mean speed (gust sigma = TI x mean) in
both directions until the vehicle fails; writes out/wind.md.

Per flight: path error (3D distance from the vehicle to the waypoint polyline) max and rms, minimum
clearance from the collision cylinder to terrain and boulders, maximum tilt, motor command range and
ticks with a motor at 0 or 1, the strongest mean wind and gust seen at the vehicle, and the outcome.

Run: python wind_study.py [--seed N] [--jobs J]
"""
import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
PY = sys.executable
TI = 0.25                     # turbulence intensity: gust sigma / mean speed
STEPS = [6, 8, 9, 10, 11, 12, 14, 16, 18, 20]
HOLD_M = 3.0                  # not completed: holding (within this of the current target waypoint) or pushed off


from gorge import Gorge  # noqa: E402
import wind as Wd  # noqa: E402

GORGE = Gorge(7)
WREF = Wd.Wind(GORGE, 1, 0, 0).w_ref
WMIN = float(GORGE.width_at(np.linspace(0, 72, 721)).min())
FAC = min(WREF / WMIN, Wd.CAP)                # mean-speed factor in the narrowest section


def run(mean, gust, seed, out, reuse=False):
    if reuse and (out / "flight.json").exists():
        return metrics(out)
    cmd = [PY, "-B", str(HERE / "fly_gorge.py"), "--cameras", "off", "--noise", "field", "--seed", str(seed), "--out", str(out)]
    if mean is not None:
        cmd += ["--wind", str(mean), str(gust)]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    return metrics(out)


def seg_dist(P, wps):
    best = np.full(len(P), np.inf)
    for a, b in zip(wps, wps[1:]):
        ab = b - a
        t = np.clip((P - a) @ ab / (ab @ ab), 0, 1)
        best = np.minimum(best, np.linalg.norm(P - (a + t[:, None] * ab), axis=1))
    return best


def metrics(out):
    d = np.genfromtxt(out / "flight.csv", delimiter=",", names=True)
    meta = json.loads((out / "flight.json").read_text())
    wps = np.array([meta["start"]] + meta["waypoints"])
    P = np.column_stack([d["p_n"], d["p_e"], d["p_d"]])
    e = seg_dist(P, wps)
    tilt = np.degrees(np.arccos(np.clip(1 - 2 * (d["q_x"] ** 2 + d["q_y"] ** 2), -1, 1)))
    m = np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]])
    w = np.column_stack([d["w_n"], d["w_e"], d["w_d"]])
    outcome = meta["outcome"]
    target = wps[min(meta["legs_done"] + 1, len(wps) - 1)]
    dist_end = float(np.linalg.norm(P[-1] - target))
    if outcome == "time limit":
        outcome = (f"holding {dist_end:.1f} m from waypoint {meta['legs_done'] + 1}" if dist_end <= HOLD_M
                   else f"pushed {dist_end:.1f} m off waypoint {meta['legs_done'] + 1}")
    leg = d["leg"].astype(int)
    ends = [0.0] + [float(d["t"][np.argmax(leg >= L)]) for L in range(1, leg.max() + 1)] + [float(d["t"][-1])]
    return dict(outcome=outcome, legs_done=meta["legs_done"], legs=meta["legs"], dist_end=dist_end, leg_max=max(np.diff(ends)), last_leg=ends[-1] - ends[-2], t_end=meta["seconds"], contact=meta["contact"], err_max=e.max(), err_rms=np.sqrt(np.mean(e ** 2)),
                clear_min=d["clearance"].min(), clear_at=float(d["p_n"][np.argmin(d["clearance"])]), tilt_max=tilt.max(),
                m_min=m.min(), m_max=m.max(), sat=int(np.sum(np.any((m >= 1.0) | (m <= 0.0), axis=1))),
                w_max=float(np.linalg.norm(w, axis=1).max()), f_max=float(np.linalg.norm(np.column_stack([d["f_n"], d["f_e"], d["f_d"]]), axis=1).max()),
                w_ref=(meta["wind"] or {}).get("w_ref"))


def holding_note(out, name):
    """Why a run holds off its waypoint: over the last 20 s, the mean horizontal aerodynamic force
    per unit mass a against the velocity integrator's limit iMax; the steady position error that the
    P-P cascade then needs is (a - iMax) / (kpPos kp)."""
    sys.path.insert(0, str(HERE.parent))
    from run_leanfc import read_params
    v, _, _ = read_params([HERE / "snapshot/params/x500.params"])
    d = np.genfromtxt(out / "flight.csv", delimiter=",", names=True)
    meta = json.loads((out / "flight.json").read_text())
    wps = np.array([meta["start"]] + meta["waypoints"])
    tgt = wps[meta["legs_done"] + 1]
    k = d["t"] > d["t"][-1] - 20
    a = np.linalg.norm(np.column_stack([d["f_n"], d["f_e"]])[k], axis=1).mean() / v["vehicle.mass"]
    e_true = np.linalg.norm(np.column_stack([d["p_n"], d["p_e"], d["p_d"]])[k] - tgt, axis=1)
    e_est = np.linalg.norm(np.column_stack([d["ph_n"], d["ph_e"], d["ph_d"]])[k] - tgt, axis=1)
    pred = max(a - v["position.vel.iMax"], 0) / (v["position.kpPos"] * v["position.vel.kp"])
    return (f"Holding ({name}, last 20 s at waypoint {meta['legs_done'] + 1}): mean horizontal aerodynamic force "
            f"{a:.2f} m/s^2 per unit mass against the velocity integrator's limit iMax = {v['position.vel.iMax']:g} m/s^2 "
            f"(snapshot x500.params), so the cascade needs a steady position error of (a - iMax) / (kpPos kp) = "
            f"({a:.2f} - {v['position.vel.iMax']:g}) / ({v['position.kpPos']:g} x {v['position.vel.kp']:g}) = {pred:.2f} m; measured: "
            f"true distance to the waypoint {e_true.mean():.2f} m mean, estimated {e_est.mean():.2f} m mean and {e_est.min():.2f} m "
            f"minimum, above nav.radius = 0.2 m, so the leg ends only when a gust carries the estimate inside the radius. "
            f"Below the first holding step the same wait appears as long legs in the narrows (column 'longest leg').")


def row(name, mean, gust, r):
    out = r["outcome"] if r["outcome"] != "contact" else (
        f"contact with {r['contact']['body'][0]} at t {r['contact']['t']:.2f} s, N {r['contact']['pos_enu'][1]:.1f} m, "
        f"{r['contact']['speed']:.1f} m/s")
    if r["outcome"].startswith(("holding", "pushed")):
        out += f" at the time limit {r['t_end']:.0f} s"
    nar = "-" if mean is None else f"{abs(mean) * FAC:.1f}"
    return (f"| {name} | {'-' if mean is None else f'{mean:+g}'} | {nar} | {'-' if gust is None else f'{gust:g}'} | {r['w_max']:.1f} | "
            f"{r['err_max']:.2f} | {r['err_rms']:.2f} | {r['clear_min']:.2f} (N {r['clear_at']:.1f}) | {r['tilt_max']:.1f} | "
            f"{r['m_min']:.3f}..{r['m_max']:.3f} | {r['sat']} | {r['legs_done']}/{r['legs']} | {r['leg_max']:.1f} | {out} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--reuse", action="store_true", help="recompute the report from flights already in out/runs")
    a = ap.parse_args()
    base = HERE / "out" / "runs"
    cases = [("off", None, None), ("4 m/s up-gorge", 4.0, 1.0), ("4 m/s down-gorge", -4.0, 1.0)]
    cases += [(f"{s} m/s up", float(s), TI * s) for s in STEPS] + [(f"{s} m/s down", -float(s), TI * s) for s in STEPS]
    with ThreadPoolExecutor(a.jobs) as ex:
        futs = {c: ex.submit(run, c[1], c[2], a.seed, reuse=a.reuse, out=base / ("off" if c[1] is None else f"w{c[1]:+g}_g{c[2]:g}")) for c in cases}
        res = {c: f.result() for c, f in futs.items()}
    head = ("| case | mean m/s | mean in the narrows m/s | gust sigma m/s | max wind at vehicle m/s | path error max m | rms m | "
            "min clearance m (at N) | max tilt deg | motor range | saturated ticks | waypoints reached | longest leg s | outcome |\n"
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    lines = ["# Wind study, gorge seed 7", "",
             f"Closed-loop flights up the gorge (fly_gorge.py, frozen leanfc snapshot, field noise seed {a.seed}, cameras off). "
             f"Mean speed: + up-gorge (tailwind), - down-gorge (headwind), at 3.5 m above the floor where the floor is "
             f"{WREF:.2f} m wide (the median); in the narrowest section (W = {WMIN:.2f} m) the mean is "
             f"{FAC:.2f} x that. Gusts: Dryden-style first-order filters, sigma_u = sigma_v = gust, sigma_w = gust / 1.96; "
             f"in the steps gust = {TI} x mean. Path error: 3D distance to the waypoint polyline. Clearance: closest distance "
             f"from the collision cylinder (radius 0.25 m) to terrain and boulders (capped at 4 m). Saturated tick: a motor "
             f"command at 0 or 1.", "", head]
    for c in cases[:3]:
        lines.append(row(c[0], c[1], c[2], res[c]))
    lines += ["", "Search in steps (gust = 0.25 x mean):", "", head]
    for c in cases[3:]:
        lines.append(row(c[0], c[1], c[2], res[c]))
    for sign, name in ((1, "up-gorge"), (-1, "down-gorge")):
        for what, good in (("completed the mission", lambda o: o == "completed"),
                           (f"survived (no contact, held within {HOLD_M:g} m of its waypoint)", lambda o: o == "completed" or o.startswith("holding"))):
            ok = [c[1] for c in cases[3:] if np.sign(c[1]) == sign and good(res[c]["outcome"])]
            bad = [c[1] for c in cases[3:] if np.sign(c[1]) == sign and not good(res[c]["outcome"])]
            first_bad = min(bad, key=abs) if bad else None
            surv = max([v for v in ok if first_bad is None or abs(v) < abs(first_bad)], key=abs, default=None)
            lines += ["", f"Strongest {name} mean that {what}, all smaller steps too: "
                      + (f"{abs(surv):g} m/s ({abs(surv) * FAC:.1f} m/s mean in the narrows)" if surv else "none")
                      + (f"; first step that did not: {abs(first_bad):g} m/s ({abs(first_bad) * FAC:.1f} m/s in the narrows), "
                         f"{res[[c for c in cases[3:] if c[1] == first_bad][0]]['outcome']}." if first_bad else "; none failed.")]
    hold = [c for c in cases[3:] if res[c]["outcome"].startswith("holding")]
    if hold:                                  # the run that held longest at its last waypoint
        c = max(hold, key=lambda c: res[c]["last_leg"])
        lines += ["", holding_note(base / f"w{c[1]:+g}_g{c[2]:g}", c[0])]
    (HERE / "out" / "wind.md").write_text("\n".join(lines) + "\n")
    print("wrote", HERE / "out" / "wind.md")


if __name__ == "__main__":
    main()
