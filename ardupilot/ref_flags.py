#!/usr/bin/env python3
"""The reference build's compiler flags for one ArduPilot source (README.md, "Phase 3: EKF data structures").

reference/build.py compiles every unit with waf's command line (build/reference/ap/build/sitl/
compile_commands.json) minus optimization, debug, dependency and color flags, plus the reference's
code-generation flags (CODEGEN: -O2 -ffp-contract=off -fno-fast-math -fno-builtin ...), with
reference/hal (the stand-in headers) first on the include path, run in waf's build directory. This
prints those flags for SOURCE (a path under libraries/, e.g. AP_NavEKF/EKF_Buffer.cpp), with every
relative include directory and `-include` file made absolute, so that cpp2lean (clang's AST) and the
difftest's C++ side preprocess the source exactly as the reference build does.

Usage: ardupilot/ref_flags.py [--ast] [--json] SOURCE
  --ast   only the flags that change the AST (no warnings, no code generation), for cpp2lean
  --json  one JSON list (default: one flag per line)
Environment: CPP2LEAN_REF (the reference build copy; default build/reference/ap).
"""
import importlib.util
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def load_build():
    spec = importlib.util.spec_from_file_location("cpp2lean_reference_build", os.path.join(ROOT, "reference", "build.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    ref = os.environ.get("CPP2LEAN_REF")
    if ref:
        m.AP = type(m.AP)(ref)
        m.WAF = m.AP / "build" / "sitl"
    return m


def flags(source, ast=False):
    b = load_build()
    units, template = b.units()
    want = "libraries/" + source
    args = next((a for r, a in units if r == want), None)
    if args is None:
        sys.exit("ref_flags: %s is not a unit of the reference build" % source)
    fl = b.flags_of(args, next(x for x in json.loads((b.WAF / "compile_commands.json").read_text())
                               if b.rel(x["file"]) == want)["file"])
    out, i = [], 0
    while i < len(fl):
        a = fl[i]
        if a == "-include" and i + 1 < len(fl):
            p = fl[i + 1]
            out += ["-include", p if os.path.isabs(p) else os.path.normpath(os.path.join(str(b.WAF), p))]
            i += 2
            continue
        if a.startswith("-I") and len(a) > 2 and not os.path.isabs(a[2:]):
            a = "-I" + os.path.normpath(os.path.join(str(b.WAF), a[2:]))
        if a.startswith("-ffile-prefix-map"):
            i += 1
            continue
        out.append(a)
        i += 1
    if ast:
        keep = []
        for a in out:
            if a.startswith("-W") or a in b.CODEGEN or a.startswith(("-fdata-sections", "-ffunction-sections", "-fno-slp-vectorize", "-O")):
                continue
            keep.append(a)
        out = keep + ["-Wno-everything"]
    return out


def main():
    argv = sys.argv[1:]
    ast = "--ast" in argv
    js = "--json" in argv
    src = [a for a in argv if not a.startswith("--")]
    if len(src) != 1:
        sys.exit(__doc__)
    fl = flags(src[0], ast)
    print(json.dumps(fl) if js else "\n".join(fl))


if __name__ == "__main__":
    main()
