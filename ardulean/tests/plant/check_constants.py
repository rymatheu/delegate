#!/usr/bin/env python3
"""Compare the constants of Plant/Model/Constants.lean with the X500 simulator they are read from.

Every `def NAME : ℝ := LITERAL` of Constants.lean is compared exactly (both sides read as `fractions.Fraction` of
their decimal strings, a quotient `a / b` as the quotient of fractions) with its source in the repository's shared
`sim/` (Constants.lean cites the files by their earlier names: sim/harness/X is sim/gorgesim/X):
  - sim/world/x500/x500.urdf: mass, ixx/iyy/izz (Jx, Jy, Jz), arm (armL), kf, km, thrust2weight; the lever is |x| = |y|
    of the four propeller links' inertial origins, which must all be (+-0.174, +-0.174, z) with one height z (the
    thrust-point height, reported);
  - sim/world/airframes.py: LAG = (up, down) (tauUp, tauDown);
  - sim/harness/simulator.py: GRAVITY_MSS (grav), CTRL_HZ (h = 1/CTRL_HZ), STEP_US (h = STEP_US us);
  - sim/fly_gorge.py: the --pyb-hz default (hPhys = 1/pyb_hz); the shared sim/gorgesim/plant.py: `substeps = pyb_hz //
    CTRL_HZ`.
The definitions that are formulas (maxRPM, fmax, amax, kmkf) are checked as text and evaluated in floating point:
MAX_RPM by the formula of sim/harness/simulator.py:139 (about 9549.2966 rpm = 1000 rad/s), fmax = kf MAX_RPM^2 (about
8.54858 N), km/kf (0.016); the numbers stated in the URDF's header comment are recomputed. Reads files only (regex
and XML); no simulation, nothing written.

    python3 tests/plant/check_constants.py        (from any directory; exit status 1 on a failure)
"""
from __future__ import annotations

import ast
import math
import re
import sys
import xml.etree.ElementTree as ET
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent          # ardulean/
PLANT = REPO
SIM = REPO.parent / "sim"                                       # the repository's shared simulator
CONSTS = PLANT / "Plant" / "Model" / "Constants.lean"
URDF = SIM / "world" / "x500" / "x500.urdf"
AIRFRAMES = SIM / "world" / "airframes.py"
SIMULATOR = SIM / "gorgesim" / "simulator.py"                   # sim/harness/simulator.py in Constants.lean's citations
FLIGHT = REPO / "sim" / "fly_gorge.py"
PLANT_PY = SIM / "gorgesim" / "plant.py"

LITERAL = re.compile(r"^[0-9.eE+\- /]+$")
FORMULAS = {"maxRPM": "Real.sqrt (thrust2weight * grav * mass / (4 * kf))", "fmax": "kf * maxRPM ^ 2",
            "amax": "thrust2weight * grav", "kmkf": "km / kf"}
bad = 0


def report(ok: bool, name: str, text: str) -> None:
    global bad
    bad += not ok
    print(f"{'OK  ' if ok else 'FAIL'} {name:13s} {text}")


def frac(s: str) -> Fraction:
    if "/" in s:
        a, b = s.split("/")
        return frac(a) / frac(b)
    return Fraction(s.strip())


def close(a: float, b: float, rel: float = 1e-12) -> bool:
    return abs(a - b) <= rel * max(abs(a), abs(b))


def grab(path: Path, pattern: str) -> str:
    m = re.search(pattern, path.read_text(), re.M)
    if m is None:
        raise SystemExit(f"FAIL pattern {pattern!r} not found in {path}")
    return m.group(1)


def lean_defs() -> dict[str, str]:
    """NAME -> right-hand side of every one-line `def NAME : ℝ := ...` of Constants.lean."""
    return {m.group(1): m.group(2).strip()
            for m in re.finditer(r"^def (\w+) : ℝ := (.+)$", CONSTS.read_text(), re.M)}


def sources() -> dict[str, tuple[str, str]]:
    """NAME -> (decimal string of the source, where it comes from); also checks the propeller geometry and the
    substep count, which have no literal of their own."""
    root = ET.parse(URDF).getroot()
    props = root.find("properties").attrib
    base = root.find("link[@name='base_link']/inertial")
    inertia = base.find("inertia").attrib
    xs, ys, zs = set(), set(), set()
    for i in range(4):
        x, y, z = root.find(f"link[@name='prop{i}_link']/inertial/origin").attrib["xyz"].split()
        xs.add(x.lstrip("-"))
        ys.add(y.lstrip("-"))
        zs.add(z)
    report(len(xs) == 1 and xs == ys and len(zs) == 1, "propellers",
           f"|x| = |y| = {', '.join(map(str, xs | ys))} m, z = {', '.join(zs)} m at prop0..3 (x500.urdf inertial origins)")
    print(f"INFO thrust-point height {', '.join(zs)} m above the base origin (no moment for a force along body z)")
    lag = ast.literal_eval(grab(AIRFRAMES, r"^LAG\s*=\s*(\(.*?\))\s*$"))
    hz = grab(SIMULATOR, r"^CTRL_HZ\s*=\s*([0-9]+)")
    step_us = grab(SIMULATOR, r"^STEP_US\s*=\s*([0-9]+)")
    pyb_hz = grab(FLIGHT, r'"--pyb-hz",\s*type=int,\s*default=([0-9]+)')
    # the substeps are taken in the shared plant (sim/gorgesim/plant.py: substeps = pyb_hz // CTRL_HZ)
    grab(PLANT_PY, r"^\s*self\.(substeps)\s*=\s*pyb_hz\s*//\s*CTRL_HZ\s*$")
    grab(PLANT_PY, r"^CTRL_HZ\s*=\s*(simulator\.CTRL_HZ)\b")
    per = hz
    report(per == hz and int(pyb_hz) % int(per) == 0, "substeps",
           f"pyb_hz {pyb_hz} // {per} = {int(pyb_hz) // int(per)} substeps per control period (fly_gorge.py;"
           f" CTRL_HZ {hz})")
    report(Fraction(int(step_us), 10 ** 6) == Fraction(1, int(hz)), "STEP_US",
           f"simulator.py STEP_US {step_us} us = 1/CTRL_HZ")
    u = URDF.name
    return {
        "mass": (base.find("mass").attrib["value"], f"{u} mass"),
        "Jx": (inertia["ixx"], f"{u} ixx"),
        "Jy": (inertia["iyy"], f"{u} iyy"),
        "Jz": (inertia["izz"], f"{u} izz"),
        "armL": (props["arm"], f"{u} arm"),
        "lever": (xs.pop(), f"{u} prop |x| = |y|"),
        "kf": (props["kf"], f"{u} kf"),
        "km": (props["km"], f"{u} km"),
        "thrust2weight": (props["thrust2weight"], f"{u} thrust2weight"),
        "grav": (grab(SIMULATOR, r"^GRAVITY_MSS\s*=\s*([0-9.]+)"), "simulator.py GRAVITY_MSS"),
        "h": (f"1/{hz}", "simulator.py 1/CTRL_HZ"),
        "hPhys": (f"1/{pyb_hz}", "fly_gorge.py 1/(--pyb-hz default)"),
        "tauUp": (repr(float(lag[0])), "airframes.py LAG[0]"),
        "tauDown": (repr(float(lag[1])), "airframes.py LAG[1]"),
    }


def main() -> int:
    lean = lean_defs()
    sim = sources()
    literals = {k: v for k, v in lean.items() if LITERAL.match(v)}
    for name, (val, src) in sim.items():
        if name not in literals:
            report(False, name, f"not a literal in Constants.lean (source {val}, {src})")
            continue
        report(frac(literals[name]) == frac(val), name, f"Lean {literals[name]:>22s}   source {val:>22s}   ({src})")
    for name in sorted(set(literals) - set(sim)):
        report(False, name, f"literal {literals[name]} in Constants.lean with no source checked")
    for name in sorted(set(lean) - set(literals)):
        report(FORMULAS.get(name) == lean[name], name, f"formula `{lean[name]}`")
    # the formulas in floating point, as the simulator computes them (env.GRAVITY = G * M, sim/harness/simulator.py:136-140)
    m, t2w, g, kf, km, lever, arm = (float(sim[k][0]) for k in
                                     ("mass", "thrust2weight", "grav", "kf", "km", "lever", "armL"))
    max_rpm = math.sqrt((t2w * (g * m)) / (4 * kf))
    fmax = kf * max_rpm ** 2
    report(abs(max_rpm - 9549.2966) < 5e-5 and abs(max_rpm * math.pi / 30 - 1000) < 1e-9, "maxRPM (float)",
           f"{max_rpm:.7f} rpm = {max_rpm * math.pi / 30:.12f} rad/s (header: 9549.2966 rpm = 1000 rad/s)")
    report(close(fmax, t2w * g * m / 4) and abs(fmax - 8.54858) < 5e-6, "fmax (float)",
           f"kf maxRPM^2 = {fmax:.12f} N = thrust2weight g m / 4 = {t2w * g * m / 4:.12f} N (header: 8.54858 N)")
    report(close(km / kf, 0.016), "kmkf (float)", f"km / kf = {km / kf:.15f} m (header: momentConstant 0.016)")
    print(f"INFO amax = thrust2weight g = {t2w * g:.12f} m/s^2; hover thrust fraction 1/thrust2weight = {1 / t2w:.12f}")
    # the numbers of the URDF's header comment, recomputed
    rotor = float(grab(URDF, r"base_link 2\.0 \+ rotor_0\.\.3 at ([0-9.]+) each"))
    mc = float(grab(URDF, r"motorConstant ([0-9.e-]+) N/\(rad/s\)\^2"))
    wmax = float(grab(URDF, r"maxRotVelocity ([0-9.]+) rad/s"))
    report(close(2.0 + 4 * rotor, m), "header mass", f"2.0 + 4 x {rotor} = {2.0 + 4 * rotor!r} kg")
    report(close(mc * (math.pi / 30) ** 2, kf), "header kf", f"{mc} (2 pi / 60)^2 = {mc * (math.pi / 30) ** 2!r}")
    report(close(0.016 * kf, km), "header km", f"0.016 kf = {0.016 * kf!r}")
    report(close(4 * mc * wmax ** 2 / (m * g), t2w), "header t2w",
           f"4 x {mc * wmax ** 2:.6g} N / (m g) = {4 * mc * wmax ** 2 / (m * g)!r}")
    report(close(lever * math.sqrt(2), arm), "header arm", f"0.174 sqrt 2 = {lever * math.sqrt(2)!r}")
    print("check_constants: all constants agree with the simulator" if bad == 0 else
          f"check_constants: {bad} check(s) FAILED")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
