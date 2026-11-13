#!/usr/bin/env python3
"""Check that a unity translation unit preprocesses each source the same as that source's own
translation unit (the way the reference build and the difftest compile it): macros defined by one
included .cpp file must not change the conditional code of a later one.

Usage: python3 ardupilot/check_unity.py UNITY.cpp FILE... -- CLANG ARGS
(also for a C unity, UNITY.c and .c files, preprocessed with clang: libm/translate_libm.sh)
For each FILE (a .cpp the unity includes, or a header), the preprocessed lines attributed to FILE
(by the `# line "file"` markers of `clang++ -E -P0`) in the unity are compared with those in the
first .cpp's own translation unit that contains FILE. Exit status 0 iff all are equal.
Two differences are not differences: the names WITH_SEMAPHORE and EXPECT_DELAY_MS make with __COUNTER__
(`_getsem17`, `_getdelay21`), which count the macros' uses in the translation unit; and a file-static name a unity renames to avoid a clash
between two included sources (`--rename=FILE:OLD=NEW` among the files, before `--`: the identifier OLD in
FILE is NEW in the unity, e.g. FILTER_KOEF of AP_Compass_Backend.cpp, a second `static constexpr float
FILTER_KOEF = 0.1f` after AP_Baro_Backend.cpp's).
"""
import os
import re
import subprocess
import sys


COUNTER_NAMES = re.compile(r"\b_get(sem|delay)\d+\b")


def attributed(text, normalize=False):
    """{file: [lines]} of preprocessed text, by line markers; for each file its first contiguous
    occurrences are concatenated. normalize: file names as os.path.normpath spells them (the generated
    MAVLink headers include each other as `../common/./mavlink_msg_x.h`)."""
    out, cur = {}, None
    for line in text.splitlines():
        m = re.match(r'^# \d+ "([^"]+)"', line)
        if m:
            cur = os.path.normpath(m.group(1)) if normalize else m.group(1)
            continue
        if cur is not None and line.strip():
            out.setdefault(cur, []).append(COUNTER_NAMES.sub(r"_get\1", line.strip()))
    return out


def main():
    i = sys.argv.index("--")
    unity, files, args = sys.argv[1], sys.argv[2:i], sys.argv[i + 1:]
    renames = [tuple(f[len("--rename="):].rsplit(":", 1)[0:1] + f[len("--rename="):].rsplit(":", 1)[1].split("=", 1))
               for f in files if f.startswith("--rename=")]
    normalize = "--normalize" in files       # (Phase 4: the MAVLink headers, named through `..` by each other)
    # --home=FILE (Phase 4): a translation unit whose headers are compared, not itself included by the unity
    homes = [os.path.normpath(f[len("--home="):]) for f in files if f.startswith("--home=")]
    files = [os.path.normpath(f) if normalize else f for f in files if not f.startswith(("--rename=", "--home=")) and f != "--normalize"]
    cxx = "clang" if unity.endswith(".c") else "clang++"      # a C unity (libm/unity) is preprocessed as C
    pp = lambda f: subprocess.run([cxx] + args + ["-E", f], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True).stdout
    u = attributed(pp(unity), normalize)
    cpps = homes + [f for f in files if f.endswith((".cpp", ".c"))]
    sep = {c: attributed(pp(c), normalize) for c in cpps}
    bad = 0
    for f in files:
        home = next((c for c in cpps if f in sep[c]), None)
        if home is None:
            print("check_unity: %s not found in any of the .cpp translation units" % f)
            bad += 1
            continue
        a, b = u.get(f, []), sep[home].get(f, [])
        for rf, old, new in renames:
            if rf == f:
                b = [re.sub(r"\b%s\b" % re.escape(old), new, l) for l in b]
        if a != b:
            k = next((j for j in range(min(len(a), len(b))) if a[j] != b[j]), min(len(a), len(b)))
            print("check_unity: %s differs (unity %d lines, %s %d lines), first at line %d:\n  unity: %s\n  alone: %s"
                  % (f, len(a), home, len(b), k, a[k] if k < len(a) else "<end>", b[k] if k < len(b) else "<end>"))
            bad += 1
        else:
            print("check_unity: %s: %d preprocessed lines, the same in the unity and in %s's own translation unit" % (f, len(a), home.split("/")[-1]))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
