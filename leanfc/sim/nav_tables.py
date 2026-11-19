"""Markdown tables of the navigator runs (sim/nav_runs.sh): per vehicle the WAYPOINT and the SPLINE square side
by side (deterministic run, and mean / worst over the field seeds), then the test missions.

Reads sim/out/flythrough/{vehicle}-{waypoint,spline}-{det,field-sN}.csv and {vehicle}-{mixed,collinear}-det.csv
through analyze.py. Usage: nav_tables.py [DIR]
"""
import contextlib
import io
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analyze  # noqa: E402

COLS = [  # key, header, scale, format, worst is the max (True) or the min (False)
    ("done", "legs", 1, "{:.0f}", False), ("complete", "complete s", 1, "{:.2f}", True),
    ("mission", "within radius from s", 1, "{:.2f}", True),
    ("track_max", "track max mm", 1e3, "{:.1f}", True), ("track_rms", "track rms mm", 1e3, "{:.1f}", True),
    ("closest_max", "worst closest approach mm", 1e3, "{:.0f}", True), ("poly_max", "path off chords mm", 1e3, "{:.0f}", True),
    ("hold_max", "hold max mm", 1e3, "{:.1f}", True), ("att_max", "att est max °", 1, "{:.2f}", True),
    ("hdg_rms", "heading err rms °", 1, "{:.2f}", True), ("hdg_max", "heading err max °", 1, "{:.2f}", True),
    ("tilt_max", "tilt max °", 1, "{:.1f}", True), ("m_min", "motor min", 1, "{:.3f}", False),
    ("m_max", "motor max", 1, "{:.3f}", True), ("sat", "sat ticks", 1, "{:.0f}", True), ("wall", "wall s", 1, "{:.1f}", True)]


def metrics(csv):
    log = analyze.load(csv)
    wps, meta = analyze.waypoints(csv)
    with contextlib.redirect_stdout(io.StringIO()):
        r = analyze.report(log, wps, str(csv), meta)
    r.update(wall=meta["wall_s"])
    return r


def cells(rs):
    out = []
    for key, _, scale, fmt, worst_max in COLS:
        xs = [r[key] * scale for r in rs if r.get(key) is not None]
        if not xs:
            out.append("–")
            continue
        w = max(xs) if worst_max else min(xs)
        out.append(fmt.format(xs[0]) if len(xs) == 1 else f"{fmt.format(np.mean(xs))} / {fmt.format(w)}")
    return out


def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent / "out" / "flythrough")
    head = "| mission | run | " + " | ".join(h for _, h, *_ in COLS) + " |\n|---|---|" + "---:|" * len(COLS)
    for veh in ("x500", "cf2x"):
        print(f"\n**{veh.upper()}** (field: mean / worst over the seeds)\n")
        print(head)
        for m in ("waypoint", "spline"):
            det = out / f"{veh}-{m}-det.csv"
            if det.exists():
                print(f"| {m} | none (100 Hz) | " + " | ".join(cells([metrics(det)])) + " |")
            field = [metrics(c) for c in sorted(out.glob(f"{veh}-{m}-field-s*.csv"))]
            if field:
                print(f"| {m} | field, {len(field)} seeds | " + " | ".join(cells(field)) + " |")
        for m in ("mixed", "collinear"):
            det = out / f"{veh}-{m}-det.csv"
            if det.exists():
                print(f"| {m} | none (100 Hz) | " + " | ".join(cells([metrics(det)])) + " |")
    print("\nPer-seed rows (navigator complete s, track max mm, hold max mm, att est max °, sat ticks):\n")
    for veh in ("x500", "cf2x"):
        for m in ("waypoint", "spline"):
            rows = []
            for c in sorted(out.glob(f"{veh}-{m}-field-s*.csv"), key=lambda c: int(c.stem.split("-s")[-1])):
                r = metrics(c)
                rows.append(f"s{c.stem.split('-s')[-1]}: {r['complete']:.2f}, {r['track_max']*1e3:.0f}, {r['hold_max']*1e3:.0f}, "
                            f"{r['att_max']:.2f}, {r['sat']}")
            if rows:
                print(f"- {veh} {m}: " + "; ".join(rows))


if __name__ == "__main__":
    main()
