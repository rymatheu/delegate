#!/usr/bin/env python3
"""Build the reference vehicle build/reference/copter_ref (REFERENCE.md).

Inputs: the build copy build/reference/ap prepared by reference/prepare.sh (ArduPilot 802db19de1 with
reference/patches applied, configured by waf for the SITL board with reference/cfg/ref.hwdef), whose
compile_commands.json gives every ArduCopter translation unit with waf's exact defines and include paths.

What is compiled:
  - every C++ unit of ArduCopter/ and libraries/ in waf's copter build, unmodified, except the SITL HAL
    (libraries/AP_HAL_SITL), the simulator (libraries/SITL) and the four SITL sensor back ends, with
    waf's flags minus -O/-g/-MMD plus the reference's code-generation flags (CODEGEN below, the flags of
    ardupilot/vehicle/build.sh), and reference/hal first on the include path (the stand-in headers
    SITL/SITL.h, SITL/SIM_*.h, AP_HAL_SITL/Semaphores.h);
  - the lock-step HAL, the stand-ins and the estimation probe, reference/hal/*.cpp, with the same flags
    (est_probe.cpp also with -fno-access-control: it reads private members, REFERENCE.md);
  - musl 1.2.5's math sources (libm/musl-1.2.5, the list libm/musl_files.txt, read-only) as
    libm/build_musl.sh compiles them (prefix cpp2lean_musl_, bound to the C names at link time), plus the
    functions of reference/libm_extra.txt that the vehicle needs beyond that list, into
    build/reference/libm.

Usage: reference/build.py [-j N]
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
AP = ROOT / "build" / "reference" / "ap"
WAF = AP / "build" / "sitl"
OUT = ROOT / "build" / "reference"
OBJ = OUT / "obj"
LIBM = ROOT / "libm"
MUSL = LIBM / "musl-1.2.5"

CODEGEN = ["-O2", "-ffp-contract=off", "-fno-fast-math", "-fno-builtin-sinf", "-fno-builtin-cosf",
           "-fno-builtin-sin", "-fno-builtin-cos", "-fno-builtin"]
# flags of waf's command lines that are dropped (optimization, debug info, dependency files, colors)
DROP = re.compile(r"^(-O[0-9s]?|-g|-MMD|-fcolor-diagnostics)$")

EXCLUDE_DIRS = ("libraries/AP_HAL_SITL/", "libraries/SITL/")
EXCLUDE_FILES = ("libraries/AP_InertialSensor/AP_InertialSensor_SITL.cpp",
                 "libraries/AP_Baro/AP_Baro_SITL.cpp",
                 "libraries/AP_Compass/AP_Compass_SITL.cpp",
                 "libraries/AP_GPS/AP_GPS_SITL.cpp",
                 # simulation consumers outside the vehicle's feature set (simulator on hardware boards,
                 # IR-LOCK simulators): they read the real SITL::SIM, which the stand-in replaces
                 "libraries/AP_HAL/SIMState.cpp",
                 "libraries/AP_IRLock/AP_IRLock_SITL.cpp",
                 "libraries/AP_IRLock/AP_IRLock_SITL_Gazebo.cpp")
HAL_SOURCES = ["lockstep.cpp", "sensors.cpp", "sensors_ins.cpp", "sensors_baro.cpp", "sensors_compass.cpp", "sensors_gps.cpp", "est_probe.cpp",
               "param_dump.cpp"]
# per-file extra flags: the estimation probe (--est) reads private members of ArduPilot classes
HAL_EXTRA_FLAGS = {"est_probe.cpp": ["-fno-access-control"], "param_dump.cpp": ["-fno-access-control"]}


def rel(path: str) -> str:
    """Path of a compile_commands file relative to the ArduPilot tree."""
    return os.path.relpath(os.path.normpath(os.path.join(WAF, path)), AP)


def units():
    cc = json.loads((WAF / "compile_commands.json").read_text())
    out = []
    template = None
    for e in cc:
        r = rel(e["file"])
        if not r.endswith(".cpp"):
            continue
        if not (r.startswith("libraries/") or r.startswith("ArduCopter/")):
            continue
        args = e["arguments"] if "arguments" in e else shlex.split(e["command"])
        if r.startswith("ArduCopter/") and template is None:
            template = args
        if r.startswith(EXCLUDE_DIRS) or r in EXCLUDE_FILES:
            continue
        out.append((r, args))
    return out, template


def flags_of(args: list[str], source: str) -> list[str]:
    """waf's arguments without the compiler, the source, -c/-o and DROP, plus CODEGEN and the
    stand-in include directory in front."""
    res = []
    skip = False
    for a in args[1:]:
        if skip:
            skip = False
            continue
        if a == "-c":
            continue
        if a == "-o":
            skip = True
            continue
        if a.startswith("-o") and len(a) > 2:
            continue
        if DROP.match(a):
            continue
        if os.path.normpath(os.path.join(WAF, a)) == os.path.normpath(os.path.join(WAF, source)):
            continue
        res.append(a)
    return ["-I" + str(HERE / "hal")] + res + CODEGEN


def obj_path(r: str) -> Path:
    return OBJ / (r.replace("/", "__") + ".o")


def needs(o: Path, deps: list[Path]) -> bool:
    """Out of date: no object, or a dependency newer than it (the given ones and, for C++ units, the
    headers of the depfile clang wrote next to the object)."""
    if not o.exists():
        return True
    t = o.stat().st_mtime
    d = o.with_suffix(".d")
    if d.exists():
        txt = d.read_text().replace("\\\n", " ")
        deps = deps + [Path(x if os.path.isabs(x) else os.path.join(WAF, x))
                       for x in txt.split(":", 1)[1].split()]
    return any(p.exists() and p.stat().st_mtime > t for p in deps)


def compile_one(cmd: list[str], o: Path) -> tuple[Path, int, str]:
    p = subprocess.run(cmd, cwd=WAF, capture_output=True, text=True)
    return o, p.returncode, p.stderr


MUSL_FLAGS = ["-x", "c", "-std=c99", "-O2", "-ffp-contract=off", "-fno-fast-math", "-fno-builtin",
              "-Wno-unknown-pragmas", "-I", str(LIBM / "env"), "-I", str(MUSL / "src" / "internal"),
              "-I", str(MUSL / "src" / "math")]


def musl_jobs():
    """musl's math sources: libm/musl_files.txt with libm/env/musl_prefix.h (as libm/build_musl.sh), and
    reference/libm_extra.txt with reference/hal/musl_prefix_extra.h (that list's names added)."""
    jobs, names = [], []
    base = [l.strip() for l in (LIBM / "musl_files.txt").read_text().split() if l.strip()]
    extra_files = HERE / "libm_extra.txt"
    extra = [l.split("#")[0].strip() for l in extra_files.read_text().splitlines()] if extra_files.exists() else []
    extra = [l for l in extra if l]
    prefix = HERE / "hal" / "musl_prefix_extra.h"
    for f in base + extra:
        src = MUSL / "src" / "math" / (f + ".c")
        o = OUT / "libm" / (f + ".o")
        cmd = ["clang"] + MUSL_FLAGS + ["-include", str(prefix), "-c", str(src), "-o", str(o)]
        jobs.append((cmd, o, [src, prefix, LIBM / "env" / "musl_prefix.h"]))
    names = [l.strip() for l in (LIBM / "env" / "musl_names.txt").read_text().split() if l.strip()]
    names += [l.split()[0] for l in extra if not l.startswith("__") and "_data" not in l]
    return jobs, names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-j", type=int, default=4)
    args = ap.parse_args()
    us, template = units()
    jobs = []
    for r, a in us:
        src = AP / r
        o = obj_path(r)
        cmd = [a[0]] + flags_of(a, e_file(a)) + ["-MMD", "-MF", str(o.with_suffix(".d")), "-c", str(src), "-o", str(o)]
        jobs.append((cmd, o, [src]))
    for h in HAL_SOURCES:
        src = HERE / "hal" / h
        o = OBJ / ("reference_hal__" + h + ".o")
        cmd = [template[0]] + flags_of(template, e_file(template)) + HAL_EXTRA_FLAGS.get(h, []) + ["-MMD", "-MF", str(o.with_suffix(".d")), "-c", str(src), "-o", str(o)]
        jobs.append((cmd, o, [src]))
    mj, names = musl_jobs()
    jobs += mj
    OBJ.mkdir(parents=True, exist_ok=True)
    (OUT / "libm").mkdir(parents=True, exist_ok=True)
    todo = [(c, o) for c, o, d in jobs if needs(o, d)]
    print(f"build.py: {len(jobs)} units, {len(todo)} to compile", flush=True)
    failed = 0
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for o, rc, err in ex.map(lambda co: compile_one(*co), todo):
            if rc != 0:
                failed += 1
                errs = [l for l in err.splitlines() if "error" in l]
                print(f"FAILED {o.name}: " + " | ".join(errs[:4]), file=sys.stderr)
    if failed:
        sys.exit(f"build.py: {failed} units failed")
    # as waf links: the vehicle's objects, then the libraries as a static archive (only the members
    # that resolve a reference are linked), then musl's objects
    lib_objs = [str(obj_path(r)) for r, a in us if r.startswith("libraries/")]
    direct = [str(obj_path(r)) for r, a in us if not r.startswith("libraries/")] + \
             [str(OBJ / ("reference_hal__" + h + ".o")) for h in HAL_SOURCES]
    musl_objs = [str(o) for c, o, d in mj]
    archive = OUT / "libardupilot.a"
    if archive.exists():
        archive.unlink()
    subprocess.run(["ar", "rcs", str(archive)] + lib_objs, check=True)
    exe = OUT / "copter_ref"
    link = ["clang++", "-o", str(exe)] + direct + [str(archive)] + musl_objs + [f"-Wl,-alias,_cpp2lean_musl_{n},_{n}" for n in names] + \
           ["-Wl,-dead_strip,-ld_classic", "-pthread", "-fno-builtin"]   # waf's LINKFLAGS for SITL, without -lm
    (OUT / "link.rsp").write_text("\n".join(shlex.quote(x) for x in link[1:]))
    p = subprocess.run(["clang++", "@" + str(OUT / "link.rsp")], capture_output=True, text=True)
    if p.returncode != 0:
        print(p.stderr[-20000:], file=sys.stderr)
        sys.exit("build.py: link failed")
    # the math functions the reference still imports from the platform (none expected)
    nm = subprocess.run(["nm", "-u", str(exe)], capture_output=True, text=True).stdout.split()
    mathre = re.compile(r"^_(a?(sin|cos|tan)h?f?|atan2?f?|sqrtf?|powf?|expf?|exp2f?|expm1f?|logf?|log2f?|log10f?|log1pf?|"
                        r"fmodf?|f(min|max|abs)f?|floorf?|ceilf?|truncf?|l?l?roundf?|l?l?rintf?|nearbyintf?|"
                        r"copysignf?|scalbnf?|ldexpf?|frexpf?|modff?|hypotf?|cbrtf?|fmaf?|remainderf?|__sincos.*|__exp10.*)$")
    imp = [s for s in nm if mathre.match(s)]
    print(f"built {exe}; math functions imported from the platform's libm: {' '.join(imp) if imp else 'none'}")


def e_file(args: list[str]) -> str:
    """The source file argument of a waf command line (the argument before -c)."""
    for i, a in enumerate(args):
        if a == "-c" and i > 0:
            return args[i - 1]
    return args[-1]


if __name__ == "__main__":
    main()
