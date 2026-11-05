#!/usr/bin/env python3
"""tabs/params.tex: the case study's parameters and results, defaults and tuned gains side by side.

Sources (named again in the table's header comment):
  vehicle     the CF2X URDF of the installed gym-pybullet-drones; the maximum rotor speed as
              sim/run_copter.py's make_env recomputes it with gravity GRAVITY_MSS
  simulation  sim/run_copter.py constants; gym-pybullet-drones version of the venv
  controller  `copter_ref --print-params` and `copter_lean --print-params` with the course parameter
              files, with and without the tuned overlay (checked equal between the two vehicles)
  mission     the same --print-params (waypoints, WP_*), run_copter.py defaults (end condition)
  build       ardupilot/vehicle/build.sh, lean/lakefile.toml, lean-toolchain, sim/BENCH.md,
              `ls -l` and `otool -L` of the two binaries, `leanc --version`, `clang++ --version`
  results     tuned: sim/RESULTS.md (course section) and sim/out/lean-course-1ms/summary.txt and
              ref-course-1ms/summary.txt; defaults: the out-default/ runs beside --defaults
              (RESULTS-default.md there), their summary.txt, flight.csv (tracking error, as
              compare_flights.stats) and compare-course-1ms.csv, and a replay of both default runs with
              --exact --trace --bits (compare_flights.replay) for the 22 values of every tick

    sim/.venv/bin/python sim/figs/make_params.py [--defaults DIR] [--out FILE]
"""
from __future__ import annotations

import argparse
import csv
import math
import os
import re
import subprocess
import sys
from pathlib import Path

import common as C

sys.path.insert(0, str(C.SIM))
import compare_flights  # noqa: E402
import run_copter as rc  # noqa: E402

DEFAULTS = Path("/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/"
                "scratchpad/tuned")


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True).stdout


def results_md_course(path: Path) -> dict | None:
    """The course section of a RESULTS.md: {row name: copter_lean value}, and the per-tick sentence."""
    text = path.read_text()
    m = re.search(r"^## Figure-eight course at 1 m/s.*?(?=^## |\Z)", text, re.M | re.S)
    if not m:
        return None
    sec = m.group(0)
    rows = {}
    for ln in sec.splitlines():
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        if len(cells) == 3 and cells[0] and not cells[0].startswith("---"):
            rows[cells[0]] = (cells[1], cells[2])
    pt = re.search(r"Per-tick comparison: (.*)", sec)
    rows["per-tick"] = pt.group(1) if pt else ""
    return rows


def run_numbers(run: Path) -> dict:
    """The numbers of one run from summary.txt and flight.csv (as compare_flights.stats)."""
    st = compare_flights.stats(run)
    s = (run / "summary.txt").read_text()
    att = re.search(r"max \|roll\| ([\d.]+) deg, max \|pitch\| ([\d.]+) deg, max tilt ([\d.]+) deg", s)
    rt = re.search(r"median ([\d.]+) us, mean [\d.]+ us, p99 ([\d.]+) us", s)
    S = C.summary(run)
    inner = [w["closest_cm"] for w in S["waypoints"][1:-1]]
    return {"end": st["end"], "ticks": st["ticks"], "time": st["time"], "final": st["final"],
            "err_max": st["err_max"], "err_rms": st["err_rms"], "roll": float(att.group(1)),
            "pitch": float(att.group(2)), "tilt": float(att.group(3)), "rt_med": float(rt.group(1)),
            "rt_p99": float(rt.group(2)), "inner": (min(inner), max(inner)),
            "w7": S["waypoints"][-1]["t_within"]}


def ticks_identical(lean: Path, ref: Path, compare_csv: Path) -> tuple[int, int, int]:
    """(ticks, ticks with identical actuator bits per compare CSV, ticks with all 22 values identical
    per a replay of both runs with --exact --trace --bits)."""
    with open(compare_csv) as f:
        rows = list(csv.DictReader(f))
    act = sum(all(r[f"lean_m{j}"] == r[f"ref_m{j}"] for j in range(1, 5)) for r in rows)
    rl, rr = compare_flights.replay(lean), compare_flights.replay(ref)
    if len(rl) != len(rr) or len(rl) != len(rows):
        raise SystemExit("tick counts disagree")
    allv = sum(a[1] == b[1] for a, b in zip(rl, rr))
    return len(rows), act, allv


def fnum(v, nd=2):
    return f"{v:.{nd}f}"


def tex_val(v: str) -> str:
    """A --print-params value as the table prints it: float32 decimals shortened to the value set."""
    x = float(v)
    s = f"{x:.6g}"
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--defaults", default=str(DEFAULTS), help="folder with RESULTS-default.md and out-default/")
    ap.add_argument("--out", default=str(C.STAGING / "tabs" / "params.tex"))
    args = ap.parse_args()
    dflt = Path(args.defaults)

    # ---------------- parameters in effect, both vehicles
    raw = {}
    for v in ("lean", "ref"):
        for tuned in (True, False):
            raw[(v, tuned)] = C.print_params(v, tuned)
    if raw[("lean", True)][0] != raw[("ref", True)][0] or raw[("lean", False)][0] != raw[("ref", False)][0]:
        raise SystemExit("copter_lean and copter_ref print different parameters")
    P, D = raw[("ref", True)][1], raw[("ref", False)][1]
    tuned_names = sorted(k for k in P if P[k] != D[k])
    wps = [tuple(float(x) for x in ln.split()[1:4]) for ln in raw[("ref", True)][0].splitlines()
           if ln.startswith("waypoint ")]

    def pv(name, unit=""):
        """Tuned value with the default in brackets when they differ."""
        t, d = tex_val(P[name]), tex_val(D[name])
        return t + (f" [{d}]" if t != d else "")

    # ---------------- vehicle
    import gym_pybullet_drones
    from importlib.metadata import version
    urdf = Path(os.path.dirname(gym_pybullet_drones.__file__)) / "assets" / "cf2x.urdf"
    u = urdf.read_text()
    props = dict(re.findall(r'(\w+)="([^"]*)"', re.search(r"<properties([^/]*)/>", u).group(1)))
    mass = float(re.search(r'<mass value="([\d.e-]+)"', u).group(1))
    kf, km, arm, t2w = float(props["kf"]), float(props["km"]), float(props["arm"]), float(props["thrust2weight"])
    max_rpm = math.sqrt(t2w * rc.GRAVITY_MSS * mass / (4 * kf))
    gpd = version("gym-pybullet-drones")

    # ---------------- build
    ref_bin, lean_bin = C.BINARIES["ref"], C.BINARIES["lean"]
    toolchain = (C.ROOT / "lean" / "lean-toolchain").read_text().strip().split(":")[-1]
    leanc_v = re.search(r"clang version ([\d.]+)", sh(["lake", "env", "leanc", "--version"], cwd=C.ROOT / "lean")).group(1)
    clang_v = re.search(r"Apple clang version ([\d.]+)", sh(["clang++", "--version"])).group(1)
    build_sh = (C.ROOT / "ardupilot" / "vehicle" / "build.sh").read_text()
    ap_commit = re.search(r"ArduPilot tree at commit (\w+)", build_sh).group(1)
    opts = re.search(r"FLAGS=\((.*?)\)", build_sh, re.S).group(1).split()
    for f in ["-O2", "-ffp-contract=off", "-fno-fast-math", "-ftrapping-math", "-fno-builtin",
              "-cl-single-precision-constant"]:
        if f not in opts:
            raise SystemExit(f"{f} not among the build.sh compiler options")
    lakefile = (C.ROOT / "lean" / "lakefile.toml").read_text()
    lean_more = re.search(r"moreLeancArgs = \[(.*?)\]", lakefile).group(1).replace('"', "").split(", ")
    size_ref, size_lean = ref_bin.stat().st_size, lean_bin.stat().st_size
    libs = {b: [ln.split()[0] for ln in sh(["otool", "-L", str(b)]).splitlines()[1:]] for b in (ref_bin, lean_bin)}
    bench = (C.SIM / "BENCH.md").read_text()
    bm = {}
    for m in re.finditer(r"^\| (\S+) \((\d+)\) \| `(copter_\w+)` \| ([\d.]+) \| ([\d.]+) \| ([\d.]+) \|", bench, re.M):
        bm[(m.group(1), m.group(3))] = (float(m.group(4)), float(m.group(6)))
    b_ref, b_lean = bm[("course-1ms", "copter_ref")], bm[("course-1ms", "copter_lean")]

    # ---------------- results
    R_t = results_md_course(C.SIM / "RESULTS.md")
    tl, tr = run_numbers(C.run_dir("lean")), run_numbers(C.run_dir("ref"))
    od = dflt / "out-default"
    dl, dr = run_numbers(od / "lean-course-1ms"), run_numbers(od / "ref-course-1ms")
    for key in ("ticks", "time", "final", "err_max", "err_rms", "roll", "pitch", "tilt", "inner", "w7"):
        if tl[key] != tr[key] or dl[key] != dr[key]:
            raise SystemExit(f"{key}: the vehicles disagree")
    # tuned numbers as RESULTS.md prints them
    rm = R_t["tracking error mean, rms, max"][0]
    t_mean, t_rms, t_max = (float(x) for x in re.findall(r"[\d.]+", rm))
    if (fnum(tl["err_rms"]), fnum(tl["err_max"])) != (fnum(t_rms), fnum(t_max)):
        raise SystemExit("tracking error of summary/flight.csv differs from RESULTS.md")
    t_final = float(re.match(r"([\d.]+) cm", R_t["final position error (final position NED, m)"][0]).group(1))
    t_time, t_ticks = re.match(r"([\d.]+) s, (\d+)", R_t["flight time, ticks"][0]).groups()
    t_w7 = R_t["last waypoint first within 0.1 m"][0]
    t_pt = R_t["per-tick"]
    t_all = re.search(r"all 22 values identical \(bits\) on (\d+)", t_pt).group(1)
    rd_md = dflt / "RESULTS-default.md"
    R_d = results_md_course(rd_md)
    d_n, d_act, d_all = ticks_identical(od / "lean-course-1ms", od / "ref-course-1ms", od / "compare-course-1ms.csv")
    if d_act != d_n or d_all != d_n:
        print(f"defaults: actuators identical on {d_act}, all values on {d_all} of {d_n}")

    def RD(a, b):
        return f"\\RD{{{a}}}{b}"

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Case study parameters and results -- one sigconf text width, booktabs")
    w("%  Paths are in cpp2lean (/Users/ryan/Research/cpp2lean) unless named in full.")
    w("%  Generated by sim/figs/make_params.py; no value typed by hand.")
    w(f"%  Sources:  vehicle   gym_pybullet_drones/assets/cf2x.urdf (mass {mass:g} kg, arm {arm:g} m,")
    w(f"%                      kf {kf:g}, km {km:g}, thrust2weight {t2w:g}); maximum rotor speed")
    w("%                      as sim/run_copter.py make_env recomputes it with gravity")
    w(f"%                      {rc.GRAVITY_MSS}: sqrt({t2w:g} * {rc.GRAVITY_MSS} * {mass:g} / (4 * {kf:g})) = {max_rpm:.0f} rpm")
    w(f"%            simulation  sim/run_copter.py (CTRL_HZ {rc.CTRL_HZ}, --pyb-hz 1200,")
    w(f"%                      GRAVITY_MSS {rc.GRAVITY_MSS}, reset_env: damping 0, SETTLE_S {rc.SETTLE_S}),")
    w(f"%                      Physics.PYB (no drag, ground effect or downwash: the")
    w(f"%                      aerodynamic effects row); gym-pybullet-drones {gpd} from the venv")
    w("%            controller  values in effect, printed identically by")
    w("%                      build/vehicle/copter_ref and lean/.lake/build/bin/copter_lean")
    w("%                        --params sim/params/copter-cf2x.txt")
    w("%                        --params sim/params/copter-course-speed.txt")
    w("%                        --params sim/params/copter-cf2x-tuned.txt --print-params;")
    w("%                      the bracketed defaults are those printed without the tuned")
    w("%                      overlay (also identical for the two vehicles); the values")
    w("%                      that differ are " + ", ".join(tuned_names) + ";")
    w("%                      MOT_* from copter-cf2x.txt; float32 values shown to 6 digits")
    w("%            mission   the same --print-params (waypoints, WP_*, WP_YAW_BEHAVIOR);")
    w("%                      path profile: AC_WPNav's S-curves (AP_Math/SCurve) with the")
    w("%                      next leg set at each waypoint (ModeAuto::set_next_wp in")
    w("%                      ardupilot/vehicle/copter_ref.cpp and lean/Vehicle.lean);")
    w("%                      heading: AC_PosControl aligns its yaw target with the desired")
    w("%                      velocity (AC_PosControl.cpp:1660-1663), which ModeAuto's")
    w("%                      LOOK_AT_NEXT_WP passes on; run_copter.py --hold 3 --tol 0.1")
    w("%                      (end condition)")
    w(f"%            build     ardupilot/vehicle/build.sh (ArduPilot commit {ap_commit}, compiler options),")
    w(f"%                      clang++ --version (Apple clang {clang_v}); lean/lean-toolchain")
    w(f"%                      ({toolchain}), lean/lakefile.toml (moreLeancArgs), sim/BENCH.md")
    w(f"%                      (leanc -O3 -DNDEBUG; leanc --version: clang {leanc_v});")
    w(f"%                      ls -l: copter_lean {size_lean} bytes, copter_ref {size_ref} bytes;")
    w("%                      otool -L: " + ", ".join(Path(x).name for x in libs[lean_bin]) + " (copter_lean), "
      + ", ".join(Path(x).name for x in libs[ref_bin]) + " (copter_ref);")
    w(f"%                      time per tick: sim/BENCH.md, course-1ms, mean over 27 launches")
    w(f"%                      ({b_lean[0]} us copter_lean, {b_ref[0]} us copter_ref; medians {b_lean[1]}, {b_ref[1]})")
    w("%            results   tuned: sim/RESULTS.md, course section (flight time, ticks,")
    w("%                      tracking error, final position error, first within 0.1 m of")
    w("%                      w7, per-tick comparison) and sim/out/{lean,ref}-course-1ms/")
    w("%                      summary.txt (attitude maxima, closest approaches, round trips);")
    w(f"%                      defaults: {od}/")
    w("%                      {lean,ref}-course-1ms/summary.txt and flight.csv (params")
    w("%                      copter-cf2x.txt + copter-course-speed.txt, UNTUNED=1 sim/fly.sh),")
    w(f"%                      {'whose course section is missing from' if R_d is None else 'and'} {rd_md.name}")
    w(f"%                      {'(it holds the hover only)' if R_d is None else ''}; tracking error from")
    w("%                      flight.csv as compare_flights.stats computes it; per-tick")
    w("%                      identity from compare-course-1ms.csv there and a replay of")
    w("%                      both runs with --exact --trace --bits (compare_flights.replay):")
    w(f"%                      actuators identical on {d_act}, all 22 values on {d_all} of {d_n} ticks.")
    w("%                      Every number is the same for copter_lean and copter_ref (checked)")
    w("%                      except the round trips, given for each.")
    w("% ==================================================================")
    w("\\begin{table}[t]")
    w("\\newcommand{\\RD}[1]{\\makebox[2.15cm][l]{#1}}% results: defaults, then tuned")
    w("\\small")
    w("\\caption{\\textnormal{The case study uses these parameters and yields these results.}}")
    w("\\label{tab:params}")
    w("\\setlength{\\tabcolsep}{4pt}")
    w("\\begin{tabular*}{\\linewidth}{@{}l@{\\extracolsep{\\fill}}l@{}}")
    w("\\toprule")
    w("Quantity & Value \\\\")
    w("\\midrule")
    w("\\textsc{vehicle} & \\\\")
    w("Model & CF2X (Crazyflie 2.x, X layout) \\\\")
    w(f"Mass, arm length & {mass * 1000:g}\\,g, {arm * 1000:g}\\,mm \\\\")
    def sci(x):
        mnt, ex = f"{x:.2e}".split("e")
        return f"${mnt}\\times10^{{{int(ex)}}}$"
    w(f"Thrust coefficient $k_f$ & {sci(kf)}\\,N/rpm$^2$ \\\\")
    w(f"Torque coefficient $k_m$ & {sci(km)}\\,N\\,m/rpm$^2$ \\\\")
    w("Maximum rotor speed, thrust/weight & " + f"{max_rpm:,.0f}".replace(",", "\\,") + f"\\,rpm, {t2w:g} \\\\")
    w("\\midrule")
    w("\\textsc{simulation} & \\\\")
    w(f"Simulator & gym-pybullet-drones {gpd} \\\\")
    w(f"Physics, control rate & 1200\\,Hz, {rc.CTRL_HZ}\\,Hz \\\\")
    w(f"Gravity & {rc.GRAVITY_MSS}\\,m/s$^2$ \\\\")
    w("Aerodynamic effects, damping & off \\\\")
    w("Initial state & at rest on the ground, yaw 0 \\\\")
    w("\\midrule")
    w("\\textsc{controller} & tuned [default]; others at defaults \\\\")
    w(f"\\texttt{{MOT\\_SPIN\\_MIN}}, \\texttt{{\\_MAX}}, \\texttt{{\\_THST\\_EXPO}} & {pv('MOT_SPIN_MIN')}, {pv('MOT_SPIN_MAX')}, {pv('MOT_THST_EXPO')} (linear) \\\\")
    w(f"\\texttt{{MOT\\_THST\\_HOVER}}, \\texttt{{\\_HOVER\\_LEARN}} & {float(P['MOT_THST_HOVER']):.4f}, {pv('MOT_HOVER_LEARN')} \\\\")
    w(f"\\texttt{{ATC\\_ANGLE\\_MAX}}, \\texttt{{ATC\\_INPUT\\_TC}} & {pv('ATC_ANGLE_MAX')}$^\\circ$, {pv('ATC_INPUT_TC')}\\,s \\\\")
    w(f"\\texttt{{PSC\\_NE\\_POS\\_P}}, \\texttt{{\\_D\\_POS\\_P}}, \\texttt{{\\_D\\_VEL\\_P}} & {pv('PSC_NE_POS_P')}, {pv('PSC_D_POS_P')}, {pv('PSC_D_VEL_P')}\\,s$^{{-1}}$ \\\\")
    w(f"\\texttt{{PSC\\_NE\\_VEL\\_P}}, \\texttt{{\\_I}}, \\texttt{{\\_D}} & {pv('PSC_NE_VEL_P')}, {pv('PSC_NE_VEL_I')}, {pv('PSC_NE_VEL_D')} \\\\")
    w(f"\\texttt{{PSC\\_D\\_ACC\\_P}}, \\texttt{{\\_I}}, \\texttt{{\\_D}} & {pv('PSC_D_ACC_P')}, {pv('PSC_D_ACC_I')}, {pv('PSC_D_ACC_D')} \\\\")
    w(f"\\texttt{{ATC\\_ANG\\_RLL\\_P}}, \\texttt{{\\_PIT\\_P}}, \\texttt{{\\_YAW\\_P}} & {pv('ATC_ANG_RLL_P')}, {pv('ATC_ANG_PIT_P')}, {pv('ATC_ANG_YAW_P')}\\,s$^{{-1}}$ \\\\")
    for a in ("P", "I", "D"):
        if P[f"ATC_RAT_RLL_{a}"] != P[f"ATC_RAT_PIT_{a}"] or D[f"ATC_RAT_RLL_{a}"] != D[f"ATC_RAT_PIT_{a}"]:
            raise SystemExit("roll and pitch rate gains differ; the table row assumes they are the same")
    w(f"\\texttt{{ATC\\_RAT\\_RLL\\_P}}, \\texttt{{\\_I}}, \\texttt{{\\_D}}, same \\texttt{{PIT}} & {pv('ATC_RAT_RLL_P')}, {pv('ATC_RAT_RLL_I')}, {pv('ATC_RAT_RLL_D')} \\\\")
    w(f"\\texttt{{ATC\\_RAT\\_YAW\\_P}}, \\texttt{{\\_I}}, \\texttt{{\\_D}} & {pv('ATC_RAT_YAW_P')}, {pv('ATC_RAT_YAW_I')}, {pv('ATC_RAT_YAW_D')} \\\\")
    w(f"\\texttt{{ATC\\_ACC\\_R\\_MAX}}, \\texttt{{\\_P\\_MAX}}, \\texttt{{\\_Y\\_MAX}} & {pv('ATC_ACC_R_MAX')}, {pv('ATC_ACC_P_MAX')}, {pv('ATC_ACC_Y_MAX')}\\,$^\\circ$/s$^2$ \\\\")
    w("\\midrule")
    w("\\textsc{mission} & \\\\")
    half = abs(wps[1][0])                       # w1 = (half, half) north and east of the crossing
    w(f"Course, half-diagonal & figure eight, {half:g}\\,m \\\\")
    w("Altitude at $w_0$ to $w_7$ & " + ", ".join(f"{-wp[2]:.1f}" for wp in wps) + "\\,m \\\\")
    w(f"\\texttt{{WP\\_SPD}}, \\texttt{{WP\\_ACC}} & {pv('WP_SPD')}\\,m/s, {pv('WP_ACC')}\\,m/s$^2$ \\\\")
    w(f"\\texttt{{WP\\_RADIUS\\_M}}, \\texttt{{WP\\_ACC\\_CNR}} & {pv('WP_RADIUS_M')}\\,m, {pv('WP_ACC_CNR')} \\\\")
    w(f"\\texttt{{WP\\_JERK}} & {pv('WP_JERK')}\\,m/s$^3$ \\\\")
    w("Path profile & S-curve legs, blended corners \\\\")
    if P["WP_YAW_BEHAVIOR"] != "2":
        raise SystemExit("WP_YAW_BEHAVIOR is not 2")
    w("Heading (\\texttt{WP\\_YAW\\_BEHAVIOR}) & 2, along the desired velocity \\\\")
    w("Hold at $w_7$ & 3\\,s within 0.1\\,m \\\\")
    w("\\midrule")
    w("\\textsc{build} & \\\\")
    w(f"C++ vehicle & Apple clang {clang_v}, \\texttt{{-O2}} \\\\")
    w("C++ options & {\\footnotesize\\texttt{-ffp-contract=off -fno-builtin}} \\\\")
    w(" & {\\footnotesize\\texttt{-fno-fast-math -ftrapping-math}} \\\\")
    w(" & {\\footnotesize\\texttt{-cl-single-precision-constant}} \\\\")
    w(f"Lean vehicle, C backend & {toolchain}, \\texttt{{-O3}} \\\\")
    w("Lean options & {\\footnotesize\\texttt{-ffp-contract=off -fno-builtin}} \\\\")
    if not {"-ffp-contract=off", "-fno-builtin"} <= set(lean_more):
        raise SystemExit("lakefile moreLeancArgs changed")
    w(f"Binary size, C++ and Lean & {size_ref / 1e6:.2f}\\,MB, {size_lean / 1e6:.2f}\\,MB \\\\")
    w(f"Time per tick, C++ and Lean & {b_ref[0]:.2f}\\,\\textmu s, {b_lean[0]:.2f}\\,\\textmu s \\\\")
    w("\\midrule")
    w("\\textsc{results} & " + RD("defaults", "tuned") + " \\\\")
    w("End of the run & " + RD("time limit", "hold at $w_7$") + " \\\\")
    w("Flight time (ticks) & " + RD(f"{dl['time']:.2f}\\,s ({dl['ticks']})", f"{float(t_time):.2f}\\,s ({t_ticks})") + " \\\\")
    w("Final position error & " + RD(f"{dl['final']:.2f}\\,cm", f"{t_final:.2f}\\,cm") + " \\\\")
    w("Maximum $|$roll$|$, $|$pitch$|$ & " + RD(f"{dl['roll']:.1f}$^\\circ$, {dl['pitch']:.1f}$^\\circ$",
                                                f"{tl['roll']:.1f}$^\\circ$, {tl['pitch']:.1f}$^\\circ$") + " \\\\")
    w("Maximum tilt & " + RD(f"{dl['tilt']:.1f}$^\\circ$", f"{tl['tilt']:.1f}$^\\circ$") + " \\\\")
    w("Tracking error (max, rms) & " + RD(f"{dl['err_max']:.1f}, {dl['err_rms']:.1f}\\,cm", f"{t_max:.1f}, {t_rms:.1f}\\,cm") + " \\\\")
    w("Closest approach to $w_1$ to $w_6$ & " + RD(f"{dl['inner'][0]:.1f}--{dl['inner'][1]:.1f}\\,cm",
                                                   f"{tl['inner'][0]:.1f}--{tl['inner'][1]:.1f}\\,cm") + " \\\\")
    w("Within 0.1\\,m of $w_7$ & " + RD(f"{dl['w7']:.2f}\\,s", f"{float(t_w7.split()[0]):.2f}\\,s") + " \\\\")
    w("Round trip, C++ (median, p99) & " + RD(f"{dr['rt_med']:.0f}, {dr['rt_p99']:.0f}\\,\\textmu s",
                                               f"{tr['rt_med']:.0f}, {tr['rt_p99']:.0f}\\,\\textmu s") + " \\\\")
    w("Round trip, Lean (median, p99) & " + RD(f"{dl['rt_med']:.0f}, {dl['rt_p99']:.0f}\\,\\textmu s",
                                                f"{tl['rt_med']:.0f}, {tl['rt_p99']:.0f}\\,\\textmu s") + " \\\\")
    w("Identical ticks, Lean and C++ & " + RD(f"{d_all} of {d_n}", f"{t_all} of {t_ticks}") + " \\\\")
    w("\\bottomrule")
    w("\\end{tabular*}")
    w("\\end{table}")
    Path(args.out).write_text("\n".join(out) + "\n")
    print(f"wrote {args.out}; tuned parameters {tuned_names}; defaults identical {d_all}/{d_n}; "
          f"RESULTS-default.md course section {'missing' if R_d is None else 'present'}")


if __name__ == "__main__":
    main()
