#!/usr/bin/env python3
"""Check that a unity translation unit preprocesses each source the same as that source's own
translation unit (the way the reference build and the difftest compile it): macros defined by one
included .cpp file must not change the conditional code of a later one.

Usage: python3 ardupilot/check_unity.py UNITY.cpp FILE... -- CLANG ARGS
For each FILE (a .cpp the unity includes, or a header), the preprocessed lines attributed to FILE
(by the `# line "file"` markers of `clang++ -E -P0`) in the unity are compared with those in the
first .cpp's own translation unit that contains FILE. Exit status 0 iff all are equal.
"""
import re
import subprocess
import sys


def attributed(text):
    """{file: [lines]} of preprocessed text, by line markers; for each file its first contiguous
    occurrences are concatenated."""
    out, cur = {}, None
    for line in text.splitlines():
        m = re.match(r'^# \d+ "([^"]+)"', line)
        if m:
            cur = m.group(1)
            continue
        if cur is not None and line.strip():
            out.setdefault(cur, []).append(line.strip())
    return out


def main():
    i = sys.argv.index("--")
    unity, files, args = sys.argv[1], sys.argv[2:i], sys.argv[i + 1:]
    cxx = "clang++"
    pp = lambda f: subprocess.run([cxx] + args + ["-E", f], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True).stdout
    u = attributed(pp(unity))
    cpps = [f for f in files if f.endswith(".cpp")]
    sep = {c: attributed(pp(c)) for c in cpps}
    bad = 0
    for f in files:
        home = next((c for c in cpps if f in sep[c]), None)
        if home is None:
            print("check_unity: %s not found in any of the .cpp translation units" % f)
            bad += 1
            continue
        a, b = u.get(f, []), sep[home].get(f, [])
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
