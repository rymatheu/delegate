#!/usr/bin/env python3
"""Compare the literal constants of plant/Plant/Model/Constants.lean with the simulator (plant/PLAN.md, rule 6).

Reads the `def NAME : ℝ := LITERAL` lines of Constants.lean and compares each, exactly (as fractions of the decimal
strings), with the value the simulator uses: the CF2X URDF of the installed gym-pybullet-drones
(sim/.venv/lib/python3.12/site-packages/gym_pybullet_drones/assets/cf2x.urdf) and the driver sim/run_copter.py
(GRAVITY_MSS, CTRL_HZ). Also checks the derived maxRPM against run_copter.py's formula in floating point. Reads
files only; no simulation.

    python3 plant/tests/check_constants.py
"""
from __future__ import annotations

import math
import re
import sys
import xml.etree.ElementTree as ET
from fractions import Fraction
from pathlib import Path

PLANT = Path(__file__).resolve().parent.parent
REPO = PLANT.parent
CONSTS = PLANT / "Plant" / "Model" / "Constants.lean"
URDF = REPO / "sim/.venv/lib/python3.12/site-packages/gym_pybullet_drones/assets/cf2x.urdf"
DRIVER = REPO / "sim" / "run_copter.py"


def lean_literals() -> dict[str, str]:
    out = {}
    for m in re.finditer(r"^def (\w+) : ℝ := ([0-9.e/+ -]+?)\s*$", CONSTS.read_text(), re.M):
        out[m.group(1)] = m.group(2)
    return out


def frac(s: str) -> Fraction:
    if "/" in s:
        a, b = s.split("/")
        return Fraction(frac(a.strip()), frac(b.strip()))
    return Fraction(s)


def simulator() -> dict[str, tuple[str, str]]:
    root = ET.parse(URDF).getroot()
    props = root.find("properties").attrib
    base = root.find("link[@name='base_link']/inertial")
    inertia = base.find("inertia").attrib
    # the inertial origins of the four motor links prop0..prop3: the lever of Physics.PYB
    levers = set()
    for i in range(4):
        x, y, _ = root.find(f"link[@name='prop{i}_link']/inertial/origin").attrib["xyz"].split()
        levers.add(abs(Fraction(x)))
        levers.add(abs(Fraction(y)))
    assert len(levers) == 1, levers
    drv = DRIVER.read_text()
    g = re.search(r"^GRAVITY_MSS\s*=\s*([0-9.]+)", drv, re.M).group(1)
    hz = re.search(r"^CTRL_HZ\s*=\s*([0-9]+)", drv, re.M).group(1)
    u = URDF.name
    return {
        "mass": (base.find("mass").attrib["value"], f"{u} mass"),
        "Jx": (inertia["ixx"], f"{u} ixx"),
        "Jy": (inertia["iyy"], f"{u} iyy"),
        "Jz": (inertia["izz"], f"{u} izz"),
        "armL": (props["arm"], f"{u} arm"),
        "lever": (str(float(levers.pop())), f"{u} prop link inertial origins"),
        "kf": (props["kf"], f"{u} kf"),
        "km": (props["km"], f"{u} km"),
        "thrust2weight": (props["thrust2weight"], f"{u} thrust2weight"),
        "grav": (g, "run_copter.py GRAVITY_MSS"),
        "h": (f"1/{hz}", "run_copter.py 1/CTRL_HZ"),
    }


def main() -> int:
    lean = lean_literals()
    sim = simulator()
    bad = 0
    for name, (val, src) in sim.items():
        if name not in lean:
            print(f"MISSING {name}: not a literal in Constants.lean (simulator {val}, {src})")
            bad += 1
            continue
        ok = frac(lean[name]) == frac(val)
        bad += not ok
        print(f"{'OK  ' if ok else 'DIFF'} {name:14s} Lean {lean[name]:>10s}   simulator {val:>10s}   ({src})")
    for name in sorted(set(lean) - set(sim)):
        print(f"NOTE {name}: literal in Constants.lean with no simulator counterpart checked")
    # derived: MAX_RPM as run_copter.py recomputes it (env.GRAVITY = G * M in BaseAviary)
    kf, t2w, g, m = (float(sim[k][0]) for k in ("kf", "thrust2weight", "grav", "mass"))
    max_rpm = math.sqrt(t2w * g * m / (4 * kf))
    print(f"INFO maxRPM = sqrt(thrust2weight g m / (4 kf)) = {max_rpm:.6f} rpm; fmax = kf maxRPM^2 = {kf * max_rpm**2:.6f} N"
          f"; thrust2weight g m / 4 = {t2w * g * m / 4:.6f} N")
    print("all constants agree" if bad == 0 else f"{bad} constant(s) disagree")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
