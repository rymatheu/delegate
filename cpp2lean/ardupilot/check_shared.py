#!/usr/bin/env python3
"""Check that two cpp2lean translations agree on the library code they share.

Usage: python3 ardupilot/check_shared.py A.lean B.lean [--only NS,NS...] [--rename OLD=NEW]... [--skip NAME,...]

Each translation of an ArduPilot class carries its own translation of the library functions and
classes it uses (AP_Math, Filter, AC_PID; `--lib-dir`), in its own top namespace (`--nest`). For
every declaration (def, structure, inductive) that both files contain under the same name and
namespace path, the two texts are compared after replacing each file's top namespace by a common
placeholder. A declaration whose code is identical but whose doc comment differs (the source
location of a class's state: the header, or the explicit instantiation in the .cpp when the unity
includes it) is counted apart; `--rename` maps a type name of B to A's (a translation without
`--type-name` names `Vector2<double>` `Vector2_double`). Exit status 0 iff no shared declaration
differs in code; the counts per namespace are printed, and the first lines of each difference.
`--skip` leaves declarations of these names out (`Output,Outputs`: each translation's own boundary
calls, not library code).
"""
import re
import sys
from collections import OrderedDict


def blocks(path):
    """{(namespace path, kind, name): text} of the file's declarations, and the module's namespace
    (the file name: `AC_PID_lib`), which is left out of the namespace path (with `--nest` every
    class is inside it, without it only the free functions are)."""
    lines = open(path).read().splitlines()
    top = path.split("/")[-1][:-len(".lean")]
    stack = []
    out = OrderedDict()
    cur = None
    doc = []
    for line in lines:
        m = re.match(r"^namespace (\S+)$", line)
        if m:
            stack.append(m.group(1))
            cur = None
            continue
        m = re.match(r"^end (\S+)$", line)
        if m:
            stack.pop()
            cur = None
            continue
        if line.startswith("/--"):
            doc = [line]
            cur = None
            if not line.rstrip().endswith("-/"):
                cur = ("doc",)
            continue
        if cur == ("doc",):
            doc.append(line)
            if line.rstrip().endswith("-/"):
                cur = None
            continue
        m = re.match(r"^(?:set_option \S+ \S+ in\s*)?(def|structure|inductive|abbrev) (\S+)", line)
        if m:
            key = (".".join(stack[1:] if stack[:1] == [top] else stack), m.group(1), m.group(2))
            cur = key
            out[key] = doc + [line]
            doc = []
            continue
        if cur is not None and cur != ("doc",) and line.strip() != "":
            out[cur].append(line)
        elif line.strip() == "":
            cur = None if cur != ("doc",) else cur
    return top, out


def norm(text, top, renames=()):
    text = re.sub(r"\b%s\." % re.escape(top), "NS.", text)
    for old, new in renames:
        text = text.replace(old, new)   # also inside overload suffixes (`op_sub_Vector2_double`)
    return text


def code(text):
    """The text without its doc comment."""
    lines = text.splitlines()
    i = 0
    if lines and lines[0].startswith("/--"):
        while i < len(lines) and not lines[i].rstrip().endswith("-/"):
            i += 1
        i += 1
    return "\n".join(lines[i:])


def main():
    a, b = sys.argv[1], sys.argv[2]
    only = None
    if "--only" in sys.argv:
        only = set(sys.argv[sys.argv.index("--only") + 1].split(","))
    renames = [tuple(sys.argv[i + 1].split("=", 1)) for i, x in enumerate(sys.argv) if x == "--rename"]
    skip = set(sys.argv[sys.argv.index("--skip") + 1].split(",")) if "--skip" in sys.argv else set()
    ta, ba = blocks(a)
    tb, bb = blocks(b)
    shared = [k for k in ba if k in bb and (only is None or (k[0].split(".")[0] if k[0] else "") in only) and k[2] not in skip]
    per = OrderedDict()
    bad = docs = 0
    for k in shared:
        x = norm("\n".join(ba[k]), ta)
        y = norm("\n".join(bb[k]), tb, renames)
        ns = k[0] or "(top)"
        s, dd, d = per.get(ns, (0, 0, 0))
        if x == y:
            per[ns] = (s + 1, dd, d)
        elif code(x) == code(y):
            per[ns] = (s, dd + 1, d)
            docs += 1
        else:
            per[ns] = (s, dd, d + 1)
            bad += 1
            if bad <= 5:
                xl, yl = x.splitlines(), y.splitlines()
                j = next((i for i in range(min(len(xl), len(yl))) if xl[i] != yl[i]), min(len(xl), len(yl)))
                print("differs: %s %s %s at line %d\n  %s: %s\n  %s: %s" % (k[0], k[1], k[2], j + 1, ta, xl[j] if j < len(xl) else "<end>", tb, yl[j] if j < len(yl) else "<end>"))
    for ns, (s, dd, d) in per.items():
        print("  %-28s %4d shared declarations identical%s%s" % (ns, s, ", %d in code (doc comment differs)" % dd if dd else "",
                                                                ", %d differ" % d if d else ""))
    print("%s vs %s: %d shared declarations, %d identical in code (%d of them differ in the doc comment), %d differ"
          % (ta, tb, len(shared), len(shared) - bad, docs, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
