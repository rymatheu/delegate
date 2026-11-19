#!/usr/bin/env python3
"""parity-trace.tex: bit-for-bit parity of the two harnessed vehicles from their traces.

The recorded course flight's state lines (sim/out/lean-course-1ms/inputs.txt) are replayed through
copter_lean and copter_ref with --exact --trace --bits (as compare_flights.py does): per tick the 4
actuators and the 18 trace numbers, as exact decimals and then, after `|`, as bit patterns in hex
(float 8 digits, the three position targets 16-digit doubles). The figure shows three traced signals
of both vehicles, a raster of the number of differing bits of each of the 22 values at each tick, and,
as a contrast, the same replay through a mutated Lean vehicle (build/mutated: the translation of
AC_AttitudeControl_Multi with single-precision trig in Quaternion::from_axis_angle, the documented
CPP2LEAN_MUTATE sensitivity check), whose per-tick count of differing values against copter_ref shows
that the comparison sees a wrong translation. Without the mutated vehicle the contrast falls back to
the recorded composition check (ardupilot/data/oracle-diag-floattrig.txt against oracle-nosincos.txt).

    sim/.venv/bin/python sim/figs/make_parity_trace.py [--out DIR]
"""
from __future__ import annotations

import argparse
import math
import re
import subprocess
from pathlib import Path

import numpy as np

import common as C

RUN = C.run_dir("lean")
MUTATED = C.ROOT / "build" / "mutated" / "lean" / ".lake" / "build" / "bin" / "copter_lean"
NAMES = ["m1", "m2", "m3", "m4", "pos_n", "pos_e", "pos_d", "vel_n", "vel_e", "vel_d", "acc_n", "acc_e", "acc_d",
         "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
GROUPS = [("actuators", 0, 4), ("position target", 4, 7), ("velocity target", 7, 10),
          ("acceleration target", 10, 13), ("thrust vector", 13, 16), ("attitude target", 16, 19),
          ("rate target", 19, 22)]
X0, X1 = 2.35, 8.1          # time axis, cm
N_PTS = 400
ROW = 0.105                 # raster row height, cm
BINS = 390                  # raster time bins


def replay(binary: Path, cmd_tail: list[str], inputs: str):
    res = subprocess.run([str(binary), *cmd_tail, "--trace", "--bits"], cwd=C.SIM, input=inputs,
                         capture_output=True, text=True, check=True)
    dec, hx = [], []
    for ln in res.stdout.splitlines():
        a, b = ln.split("|")
        dec.append([float(v) for v in a.split()])
        hx.append([int(v, 16) for v in b.split()])
    return np.array(dec), np.array(hx, dtype=np.uint64)


def popcount(a: np.ndarray) -> np.ndarray:
    a = a.copy()
    c = np.zeros(a.shape, dtype=np.int64)
    while np.any(a):
        c += (a & np.uint64(1)).astype(np.int64)
        a >>= np.uint64(1)
    return c


def oracle_values(path: Path):
    """The 22 values of each line of a recorded composition file (bit patterns after `|`)."""
    out = []
    for ln in path.read_text().splitlines():
        out.append([int(v, 16) for v in ln.split("|")[1].split()])
    return np.array(out, dtype=np.uint64)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    first = (RUN / "summary.txt").read_text().splitlines()[0]
    cmd = re.match(r"^.*?: (.*) \(cwd (.*)\)$", first).group(1).split()
    tail = cmd[1:]                                     # --exact --params ...
    inputs = (RUN / "inputs.txt").read_text()
    n = inputs.count("\n")
    Ld, Lh = replay(C.BINARIES["lean"], tail, inputs)
    Rd, Rh = replay(C.BINARIES["ref"], tail, inputs)
    if Lh.shape != (n, 22) or Rh.shape != (n, 22):
        raise SystemExit(f"unexpected replay shapes {Lh.shape} {Rh.shape}")
    bits = popcount(Lh ^ Rh)                            # ticks x 22
    ndiff = int((bits > 0).sum())
    flown = np.array([[float(v) for v in ln.split()] for ln in (RUN / "motors.txt").read_text().splitlines()])
    if not np.array_equal(Ld[:, :4], flown):
        raise SystemExit("the replayed actuators differ from the flown ones")

    # contrast
    if MUTATED.exists():
        Md, Mh = replay(MUTATED, tail, inputs)
        cdiff = (Mh != Rh)
        contrast = "mutated"
        clabel = "mutated Lean vehicle vs C++"
    else:
        a = oracle_values(C.ROOT / "ardupilot" / "data" / "oracle-diag-floattrig.txt")
        b = oracle_values(C.ROOT / "ardupilot" / "data" / "oracle-nosincos.txt")
        cdiff = (a != b)
        contrast = "composition"
        clabel = "composition check, single-precision trig"
    cnt = cdiff.sum(axis=1)
    cfirst = int(np.argmax(cnt > 0)) if cnt.any() else None
    cfirst_act = int(np.argmax(cdiff[:, :4].any(axis=1))) if cdiff[:, :4].any() else None
    cfirst_names = [NAMES[j] for j in range(22) if cdiff[cfirst, j]] if cfirst is not None else []
    cn = len(cnt)

    t = np.arange(n) / 400.0
    T = t[-1]
    X = lambda tt: X0 + tt / T * (X1 - X0)
    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Parity from the traces of the two harnessed vehicles -- one sigconf text")
    w("%  width (8.2 cm), pdfLaTeX, plain TikZ (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      the state lines of the recorded course flight ({C.rel(RUN / 'inputs.txt')},")
    w(f"%             {n} ticks, the 1 m/s figure-eight course with the tuned gains) replayed by the")
    w("%             script through copter_lean (lean/.lake/build/bin) and copter_ref")
    w("%             (build/vehicle) with " + " ".join(tail[:1]) + " --trace --bits and the course parameter files:")
    w("%             per tick the 4 actuators and the 18 trace numbers (position, velocity and")
    w("%             acceleration targets, thrust vector, attitude-target Euler angles, body-rate")
    w("%             targets) with their bit patterns. The replayed actuators equal the flown")
    w("%             ones (motors.txt).")
    w(f"%  Top:       the north position target, the roll attitude target and actuator m1 of")
    w("%             both vehicles (copter_ref pale and wide under copter_lean), thinned to")
    w(f"%             {N_PTS} points each (largest-triangle-three-buckets).")
    w(f"%  Middle:    per value and tick, the number of bits that differ between the two")
    w(f"%             vehicles (popcount of the XOR of the bit patterns), the maximum over bins")
    w(f"%             of {math.ceil(n / BINS)} ticks: {ndiff} of 22 x {n} = {22 * n} values differ; the largest count is {int(bits.max())}.")
    w("%             Equal runs of cells are merged into one rectangle per row.")
    if contrast == "mutated":
        w("%  Bottom:    contrast: the same state lines through a mutated Lean vehicle, built")
        w("%             separately in cpp2lean build/mutated/lean from a copy of lean/ with")
        w("%             AC_Attitude_lib.lean edited as the CPP2LEAN_MUTATE sensitivity check")
        w("%             does: single-precision sinf/cosf of 0.5f*theta in")
        w("%             Quaternion::from_axis_angle (2 replacements); per tick the number of the")
        w(f"%             22 values that differ from copter_ref: first at tick {cfirst} (t = {cfirst / 400:.4f} s,")
        w(f"%             {', '.join(cfirst_names)}), first actuator at tick {cfirst_act} (t = {cfirst_act / 400:.4f} s);")
        w(f"%             {int((cnt > 0).sum())} of {cn} ticks differ in some value.")
    else:
        w("%  Bottom:    contrast, the composition check (not this flight): the recorded")
        w("%             ardupilot/data/oracle-diag-floattrig.txt (single-precision")
        w("%             from_axis_angle) against oracle-nosincos.txt, per tick the number of")
        w(f"%             the 22 values that differ: first at line {cfirst}, first actuator at line {cfirst_act}.")
    w("%  Generated by cpp2lean sim/figs/make_parity_trace.py; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  lab/.style={font=\\scriptsize, text=fwInk!85, inner sep=1pt},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  ref/.style={line width=1.6pt, draw opacity=0.28},
  crv/.style={line width=0.5pt},
  bnd/.style={draw=fwHair, line width=0.3pt},
]""")
    # ---------------- top: three signals, each in its own lane
    lanes = [("north target", Ld[:, 4], Rd[:, 4], "m", 1.0),
             ("roll target", Ld[:, 16], Rd[:, 16], "deg", 180 / math.pi),
             ("actuator m1", Ld[:, 0], Rd[:, 0], "", 1.0)]
    lane_h, lane_gap = 0.62, 0.14
    y = 0.0
    tops = []
    for name, lv, rv, unit, sc in lanes:
        lv, rv = lv * sc, rv * sc
        lo_, hi_ = float(min(lv.min(), rv.min())), float(max(lv.max(), rv.max()))
        pad = 0.08 * (hi_ - lo_)
        lo_, hi_ = lo_ - pad, hi_ + pad
        Y = lambda v, y0=y - lane_h: y0 + (v - lo_) / (hi_ - lo_) * lane_h
        y0 = y - lane_h
        w(f"% ---------------- {name}")
        w(f"\\draw[axis] ({C.num(X0)},{C.num(y)}) -- ({C.num(X0)},{C.num(y0)}) -- ({C.num(X1)},{C.num(y0)});")
        w(f"\\node[lab, anchor=east, align=right] at ({C.num(X0 - 0.12)},{C.num(y0 + lane_h / 2)}) "
          f"{{{name}{(' (' + unit + ')') if unit else ''}}};")
        for vals, style, col in ((rv, "ref", "fwBlue"), (lv, "crv", "fwBlue")):
            pts = np.stack([[X(tt) for tt in t], [Y(v_) for v_ in vals]], axis=1)
            keep = C.lttb(pts, N_PTS)
            w(f"\\draw[{style}, {col}] plot coordinates {{{' '.join(f'({C.num(a)},{C.num(b)})' for a, b in pts[keep])}}};")
        tops.append(y0)
        y = y0 - lane_gap
    w(f"\\draw[ref, fwBlue] ({C.num(X1 - 2.55)},{C.num(0.22)}) -- ++(0.35,0);")
    w(f"\\node[lab, anchor=west] at ({C.num(X1 - 2.15)},{C.num(0.22)}) {{C++}};")
    w(f"\\draw[crv, fwBlue] ({C.num(X1 - 1.35)},{C.num(0.22)}) -- ++(0.35,0);")
    w(f"\\node[lab, anchor=west] at ({C.num(X1 - 0.95)},{C.num(0.22)}) {{Lean}};")

    # ---------------- raster
    ytop = y - 0.12
    edges = np.linspace(0, n, BINS + 1).astype(int)
    binned = np.stack([bits[edges[i]:edges[i + 1]].max(axis=0) for i in range(BINS)])   # bins x 22
    def shade(b):
        if b == 0:
            return "fwSage!45"
        return f"fwVerm!{min(100, 30 + 70 * min(b, 32) // 32)}"
    w("% ---------------- raster: differing bits per value and tick")
    for j in range(22):
        yr = ytop - (j + 1) * ROW
        row = binned[:, j]
        i = 0
        while i < BINS:
            k = i
            while k + 1 < BINS and row[k + 1] == row[i]:
                k += 1
            xa, xb = X0 + (edges[i] / n) * (X1 - X0), X0 + (edges[k + 1] / n) * (X1 - X0)
            w(f"\\fill[{shade(int(row[i]))}] ({C.num(xa)},{C.num(yr)}) rectangle ({C.num(xb)},{C.num(yr + ROW)});")
            i = k + 1
    for gname, a, b in GROUPS:
        ya, yb = ytop - a * ROW, ytop - b * ROW
        w(f"\\draw[bnd] ({C.num(X0)},{C.num(yb)}) -- ({C.num(X1)},{C.num(yb)});")
        w(f"\\draw[bnd] ({C.num(X0 - 0.06)},{C.num(ya - 0.015)}) -- ({C.num(X0 - 0.06)},{C.num(yb + 0.015)});")
        w(f"\\node[tick, text=fwInk!80, anchor=east] at ({C.num(X0 - 0.1)},{C.num((ya + yb) / 2)}) {{{gname}}};")
    w(f"\\draw[bnd] ({C.num(X0)},{C.num(ytop)}) rectangle ({C.num(X1)},{C.num(ytop - 22 * ROW)});")
    yb = ytop - 22 * ROW
    # time axis under the raster
    for tt in range(0, int(T) + 1, 5):
        lab = f"{tt}\\,s" if tt + 5 > T else f"${tt}$"
        w(f"\\draw[mk] ({C.num(X(tt))},{C.num(yb)}) -- ++(0,-0.06) node[tick, anchor=north] {{{lab}}};")
    # color scale and the total
    ys = yb - 0.55
    w(f"\\node[lab, anchor=west] at ({C.num(X0 - 2.3)},{C.num(ys)}) {{differing bits:}};")
    xs = X0 - 0.15
    for b_, lab in [(0, "0"), (1, "1"), (8, "8"), (32, "32+")]:
        w(f"\\fill[{shade(b_)}] ({C.num(xs)},{C.num(ys - 0.07)}) rectangle ++(0.28,0.14);")
        w(f"\\node[tick, anchor=west] at ({C.num(xs + 0.3)},{C.num(ys)}) {{{lab}}};")
        xs += 0.75 if lab != "32+" else 0.95
    w(f"\\node[lab, anchor=east] at ({C.num(X1)},{C.num(ys)}) "
      f"{{{ndiff} of 22 $\\times$ {f'{n:,}'.replace(',', '{,}')} values differ}};")

    # ---------------- contrast strip
    ch = 0.75
    yc1 = ys - 0.35
    yc0 = yc1 - ch
    Tc = (cn - 1) / 400.0 if contrast == "mutated" else (cn - 1) / 400.0
    Xc = lambda tt: X0 + tt / Tc * (X1 - X0)
    w("% ---------------- contrast")
    w(f"\\draw[axis] ({C.num(X0)},{C.num(yc1)}) -- ({C.num(X0)},{C.num(yc0)}) -- ({C.num(X1)},{C.num(yc0)});")
    Yc = lambda c: yc0 + c / 22 * ch
    for c_, lab in [(0, "0"), (22, "22")]:
        w(f"\\draw[mk] ({C.num(X0)},{C.num(Yc(c_))}) -- ++(-0.06,0) node[tick, anchor=east] {{{lab}}};")
    w(f"\\node[lab, anchor=east, align=right] at ({C.num(X0 - 0.42)},{C.num((yc0 + yc1) / 2)}) "
      f"{{values that\\\\\\\\[-1pt]differ, {'mutant' if contrast == 'mutated' else 'diag.'}}};")
    tc = np.arange(cn) / 400.0
    pts = np.stack([[Xc(x) for x in tc], [Yc(c) for c in cnt]], axis=1)
    keep = C.lttb(pts, 600)
    w(f"\\draw[crv, fwVerm] plot coordinates {{{' '.join(f'({C.num(a)},{C.num(b)})' for a, b in pts[keep])}}};")
    if cfirst is not None:
        xf = Xc(cfirst / 400)
        w(f"\\draw[fwVerm, line width=0.4pt, dash pattern=on 1pt off 1pt] ({C.num(xf)},{C.num(yc0)}) -- ({C.num(xf)},{C.num(yc1 + 0.05)});")
        w(f"\\node[tick, text=fwVerm, anchor=south west] at ({C.num(xf + 0.03)},{C.num(yc1 - 0.08)}) "
          f"{{first at tick {cfirst} ({cfirst / 400:.2f}\\,s); actuators from tick {cfirst_act} ({cfirst_act / 400:.2f}\\,s)}};")
    for tt in range(0, int(Tc) + 1, 5):
        lab = f"{tt}\\,s" if tt + 5 > Tc else f"${tt}$"
        w(f"\\draw[mk] ({C.num(Xc(tt))},{C.num(yc0)}) -- ++(0,-0.06) node[tick, anchor=north] {{{lab}}};")
    w(f"\\node[tick, anchor=north] at ({C.num((X0 + X1) / 2)},{C.num(yc0 - 0.3)}) {{{clabel}}};")
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "parity-trace.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: {n} ticks, {ndiff} of {22 * n} values differ (max bits {int(bits.max())}); contrast {contrast}: "
          f"first differing tick {cfirst}, first actuator tick {cfirst_act}, {int((cnt > 0).sum())} of {cn} ticks "
          f"differ; first values {cfirst_names}")


if __name__ == "__main__":
    main()
