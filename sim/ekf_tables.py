"""Markdown tables of the estimator runs: vehicle x estimator x case, mean / worst over seeds.

Reads sim/out/ekf/{vehicle}-{estimator}-{case}-s{seed}.csv (made by sim/ekf_runs.sh with --trace-ekf) through
analyze.py. Usage: ekf_tables.py [DIR]   (default sim/out/ekf)
"""
import contextlib
import io
import re
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analyze  # noqa: E402

CASES = [("det", "noiseless, 100 Hz"), ("field", "field, 10 Hz"), ("nocal", "field, no calibration"),
         ("drop", "field, dropout 10-14 s")]
COLS = [  # key, header, scale, format, worst is the max (True) or the min (False)
    ("done", "legs", 1, "{:.0f}", False), ("track_max", "track max mm", 1e3, "{:.0f}", True),
    ("track_rms", "track rms mm", 1e3, "{:.0f}", True), ("hold_max", "hold max mm", 1e3, "{:.0f}", True),
    ("pe_rms", "pos est rms mm", 1e3, "{:.0f}", True), ("ve_rms", "vel est rms mm/s", 1e3, "{:.0f}", True),
    ("ae_rms", "att est rms °", 1, "{:.2f}", True), ("ae_max", "att est max °", 1, "{:.2f}", True),
    ("bg_err", "b_g err end °/s", 1, "{:.3f}", True), ("ba_err", "b_a err end mm/s²", 1e3, "{:.0f}", True),
    ("in3", "pos in ±3σ %", 100, "{:.2f}", False), ("sat", "sat ticks", 1, "{:.0f}", True)]


def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent / "out" / "ekf")
    runs = defaultdict(list)
    for csv in sorted(out.glob("*.csv")):
        m = re.fullmatch(r"(cf2x|x500)-(fixed|ekf)-(\w+)-s(\d+)", csv.stem)
        if not m:
            continue
        log = analyze.load(csv)
        wps, meta = analyze.waypoints(csv)
        with contextlib.redirect_stdout(io.StringIO()):
            r = analyze.report(log, wps, str(csv), meta)
        runs[m.group(1), m.group(2), m.group(3)].append(r)
    for veh in ("x500", "cf2x"):
        print(f"\n**{veh.upper()}** (each cell: mean / worst over the runs; n = number of runs)\n")
        print("| case | estimator | n | " + " | ".join(h for _, h, *_ in COLS) + " |")
        print("|---|---|---:|" + "---:|" * len(COLS))
        for case, label in CASES:
            for est in ("fixed", "ekf"):
                rs = runs.get((veh, est, case))
                if not rs:
                    continue
                cells = []
                for key, _, scale, fmt, worst_max in COLS:
                    xs = [r[key] * scale for r in rs if key in r]
                    if not xs:
                        cells.append("–")
                        continue
                    w = max(xs) if worst_max else min(xs)
                    cells.append(fmt.format(np.mean(xs)) if len(xs) == 1 else f"{fmt.format(np.mean(xs))} / {fmt.format(w)}")
                print(f"| {label} | {est} | {len(rs)} | " + " | ".join(cells) + " |")


if __name__ == "__main__":
    main()
