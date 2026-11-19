#!/usr/bin/env python3
"""flight-parity.tex: the tick-by-tick comparison of the two vehicles on the 1 m/s figure-eight course.

Sources (sim/out): lean-course-1ms and ref-course-1ms (flight.csv for m1; motors.txt for the actuator
lines as flown), compare-course-1ms.csv (the actuators of both as bit patterns), and a fresh replay of
each run's recorded state lines through its own binary with --exact --trace --bits
(compare_flights.replay, the command of summary.txt's first line), which gives the bit patterns of all
22 values of every tick.

    sim/.venv/bin/python sim/figs/make_parity.py [--out DIR]   (default: the staging figs folder)
"""
from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

import numpy as np

import common as C

sys.path.insert(0, str(C.SIM))
import compare_flights  # noqa: E402

N_PTS = 400
X0, WIDTH = 0.84, 7.17
# strips: (data range, bottom cm, height cm)
M1 = ((0.40, 0.50), 1.62, 1.30)
ACT = ((0.0, 4.0), 0.82, 0.55)
ALL = ((0.0, 22.0), 0.00, 0.55)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    lean_dir, ref_dir = C.run_dir("lean"), C.run_dir("ref")
    L, R = C.load_flight(lean_dir), C.load_flight(ref_dir)
    t = L["t"]
    n = len(t)
    if len(R["t"]) != n:
        raise SystemExit("the runs have different tick counts")

    # actuators as flown: motors.txt, value by value (exact decimals as the vehicles printed them)
    fl = [ln.split() for ln in (lean_dir / "motors.txt").read_text().splitlines()]
    fr = [ln.split() for ln in (ref_dir / "motors.txt").read_text().splitlines()]
    act_flown = np.array([sum(a != b for a, b in zip(x, y)) for x, y in zip(fl, fr)])
    # actuators as bit patterns: compare-course-1ms.csv
    with open(C.OUT / f"compare-{C.MISSION}.csv") as f:
        rows = list(csv.DictReader(f))
    act_hex = np.array([sum(r[f"lean_m{j}"] != r[f"ref_m{j}"] for j in range(1, 5)) for r in rows])
    # all 22 values: fresh replays with --exact --trace --bits
    rl, rr = compare_flights.replay(lean_dir), compare_flights.replay(ref_dir)
    if len(rl) != n or len(rr) != n or len(rows) != n or len(fl) != n:
        raise SystemExit("tick counts disagree between the sources")
    all22 = np.array([sum(a != b for a, b in zip(x[1], y[1])) for x, y in zip(rl, rr)])
    nvals = len(rl[0][1])
    # the replays reproduce the flights and the compare CSV
    rep_vs_flown = sum(" ".join(x[0][:4]) != " ".join(m) for x, m in zip(rl, fl)) + \
        sum(" ".join(y[0][:4]) != " ".join(m) for y, m in zip(rr, fr))
    rep_vs_csv = sum(x[1][:4] != [r[f"lean_m{j}"] for j in range(1, 5)] for x, r in zip(rl, rows)) + \
        sum(y[1][:4] != [r[f"ref_m{j}"] for j in range(1, 5)] for y, r in zip(rr, rows))
    if rep_vs_flown or rep_vs_csv:
        raise SystemExit(f"replay differs from the recorded flight on {rep_vs_flown} lines, "
                         f"from the compare CSV on {rep_vs_csv}")
    states = sum(a != b for a, b in zip((lean_dir / "inputs.txt").read_text().splitlines(),
                                        (ref_dir / "inputs.txt").read_text().splitlines()))
    tmax = float(t[-1])
    kx = WIDTH / tmax

    def thin(y, strip):
        (lo, hi), _, h = strip
        idx = C.lttb(np.stack([t * kx, y * h / (hi - lo)], axis=1), N_PTS)
        return t[idx], y[idx]

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Tick-by-tick parity of the two vehicles -- one sigconf text width")
    w("%  (8.2 cm), pdfLaTeX, plain TikZ")
    w("%  Preamble:  \\usepackage{tikz}  (no pgfplots; coordinates are embedded)")
    w("%  Flights:   the 1 m/s figure-eight course with the tuned gains (params")
    w("%             copter-cf2x.txt + copter-course-speed.txt +")
    w(f"%             copter-cf2x-tuned.txt), {n} ticks at 400 Hz, flown once by")
    w("%             copter_lean (the Lean translations of ArduPilot's classes) and")
    w("%             once by copter_ref (ArduPilot's classes compiled unmodified),")
    w("%             separate processes and separate simulations from the same")
    w("%             initial state; cpp2lean sim/out/lean-course-1ms and")
    w("%             sim/out/ref-course-1ms.")
    w("%  Design:    one time axis, three strips. Top: actuator m1 (motor slot 0)")
    w("%             of both vehicles from flight.csv, copter_ref as a pale wide")
    w("%             stroke under copter_lean (they coincide). Middle: the number")
    w("%             of the four actuators whose values differ between the two")
    w("%             runs at each tick, as the simulator received them (motors.txt,")
    w("%             exact decimals). Bottom: the number of the 22 values of the")
    w("%             tick (4 actuators and 18 trace numbers: position, velocity and")
    w("%             acceleration targets, thrust vector, attitude-target angles,")
    w("%             body-rate targets) whose bit patterns differ, from a replay of")
    w("%             each run's recorded state lines through its own binary with")
    w("%             --exact --trace --bits (compare_flights.replay). Both counts")
    w("%             are drawn on their full scale (0 to 4, 0 to 22) so that a")
    w("%             single differing value would show; each count curve thinned")
    w(f"%             to {N_PTS} points by largest-triangle-three-buckets.")
    w(f"%  Results:   actuators differing (as flown): 0 on {int((act_flown == 0).sum())} of {n} ticks"
      f" (max {int(act_flown.max())});")
    w(f"%             as bit patterns (compare-course-1ms.csv): 0 on {int((act_hex == 0).sum())} of {n}"
      f" (max {int(act_hex.max())});")
    w(f"%             all {nvals} values (replay bits): 0 on {int((all22 == 0).sum())} of {n}"
      f" (max {int(all22.max())});")
    w(f"%             simulator state lines (inputs.txt) differing: {states} of {n}.")
    w("%             The replays reproduce the flown actuator lines and the bit")
    w("%             patterns of compare-course-1ms.csv on every tick (checked).")
    w("%  Generated by cpp2lean sim/figs/make_parity.py; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  ylab/.style={font=\\scriptsize, text=fwInk!80, rotate=90, anchor=south, inner sep=0},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  crv/.style={line width=0.5pt},
  ref/.style={line width=1.4pt, draw opacity=0.25},
  cnt/.style={draw=fwBlue, line width=0.6pt},
  key/.style={font=\\scriptsize, inner sep=1pt},
  note/.style={font=\\scriptsize, text=fwInk!80, inner sep=1pt},
]""")
    ticks_t = list(range(0, int(tmax) + 1, 4))

    def strip(name, rng, y0, h, yticks):
        lo, hi = rng
        ky = h / (hi - lo)
        w(f"% ---------------- {name}")
        w(f"\\begin{{scope}}[shift={{({X0},{C.num(y0 - lo * ky, 4)})}}, x={C.num(kx, 5)}cm, y={C.num(ky, 6)}cm]")
        w(f"  \\draw[axis] (0,{C.num(hi)}) -- (0,{C.num(lo)}) -- ({C.num(tmax, 4)},{C.num(lo)});")
        for v, lab in yticks:
            w(f"  \\draw[mk] (0,{C.num(v)}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
        for v in ticks_t:
            w(f"  \\draw[mk] ({v},{C.num(lo)}) -- ++(0,-0.06cm);")

    # m1
    (lo, hi), y0, h = M1
    strip("actuator m1 of both vehicles", (lo, hi), y0, h, [(0.40, "$0.40$"), (0.45, "$0.45$"), (0.50, "$0.50$")])
    tt, yy = thin(R["m1"], M1)
    w("  \\draw[ref, fwOchre] plot coordinates {  % copter_ref\n" + C.coords(tt, yy, 4) + "\n  };")
    tt, yy = thin(L["m1"], M1)
    w("  \\draw[crv, fwOchre] plot coordinates {  % copter_lean\n" + C.coords(tt, yy, 4) + "\n  };")
    w("  \\draw[ref, fwOchre] (8.3,0.493) -- (9.5,0.493);")
    w("  \\draw[crv, fwOchre] (8.3,0.493) -- (9.5,0.493);")
    w("  \\node[key, text=fwMute, anchor=west] at (9.65,0.493) {\\texttt{copter\\_lean} over \\texttt{copter\\_ref}};")
    w("\\end{scope}")
    w(f"\\node[ylab] at (0.06,{C.num(y0 + h / 2)}) {{$m_1$}};")

    # counts
    for (rng, y0, h), cnt, of, what in [(ACT, act_flown, 4, "actuators that differ, of 4"),
                                        (ALL, all22, nvals, f"values whose bits differ, of {nvals}")]:
        lo, hi = rng
        strip(what, rng, y0, h, [(0, "$0$"), (of, f"${of}$")])
        tt, yy = thin(cnt.astype(float), (rng, y0, h))
        w("  \\draw[cnt] plot coordinates {\n" + C.coords(tt, yy, 0) + "\n  };")
        w(f"  \\node[note, anchor=north west] at (0.25,{C.num(hi)}) {{{what}}};")
        zero = int((cnt == 0).sum())
        w(f"  \\node[note, anchor=north east] at ({C.num(tmax, 4)},{C.num(hi)}) "
          + ("{0 on all %d ticks};" % n if zero == n else "{nonzero on %d of %d ticks};" % (n - zero, n)))
        w("\\end{scope}")
    w(f"\\node[ylab] at (0.06,{C.num((ALL[1] + ACT[1] + ACT[2]) / 2)}) {{differing}};")
    for v in ticks_t:
        lab = f"{v}\\,s" if v == ticks_t[-1] else f"${v}$"
        w(f"\\node[tick, anchor=north] at ({X0 + v * kx:.3f},-0.060) {{{lab}}};")
    w(f"\\node[tick, anchor=north, text=fwInk!80] at ({X0 + WIDTH / 2:.3f},-0.360) {{time}};")
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "flight-parity.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: {n} ticks; actuators differing (flown) max {act_flown.max()}, (hex) max {act_hex.max()}; "
          f"all {nvals} values differing max {all22.max()}; state lines differing {states}")


if __name__ == "__main__":
    main()
