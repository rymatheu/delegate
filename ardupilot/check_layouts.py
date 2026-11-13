#!/usr/bin/env python3
"""Cross-check the record layouts a translation used against clang's (README.md, "Phase 4: the MAVLink C
library"): for every record of the signatures' "layouts" (cpp2lean --mavlink: the structs whose object
representation or byte view the translated code uses), the size, the alignment and every member's offset
and size (a bit-field's bit offset and width) must equal clang's record layout for the translation unit,
dumped with `-Xclang -fdump-record-layouts` on the unity the signatures name (and a `sizeof` of each
record, so that clang lays every one out). Exit status 0 iff all are equal; a mismatch is printed.

Usage: python3 ardupilot/check_layouts.py SIGNATURES.json -- CLANG ARGS
"""
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
UNIONS = set()      # the records of the signatures that are unions (cpp2lean --mission's byte unions)
ROOT = os.path.dirname(HERE)


def clang_layouts(unity, records, args):
    """{record name: (size, align, [(member, offset or bit offset, is bit-field, width or None)])} of the
    records clang lays out for the unity plus a sizeof of each record."""
    with tempfile.NamedTemporaryFile("w", suffix=".cpp", delete=False) as f:
        f.write('#include "%s"\n' % os.path.abspath(unity))
        for i, r in enumerate(records):
            f.write("unsigned long cpp2lean_layout_%d = sizeof(%s %s);\n" % (i, "union" if r in UNIONS else "struct", r))
        tmp = f.name
    try:
        p = subprocess.run(["clang++"] + args + ["-fsyntax-only", "-Xclang", "-fdump-record-layouts", tmp],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    finally:
        os.unlink(tmp)
    if p.returncode != 0:
        sys.exit("check_layouts: clang failed:\n" + p.stderr[-2000:])
    out = {}
    for block in p.stdout.split("*** Dumping AST Record Layout")[1:]:
        lines = block.strip("\n").splitlines()
        m = re.match(r"^\s*0 \| (?:struct|class|union) (\S+)", lines[0])
        if not m:
            continue
        name = m.group(1)
        members = []
        size = align = None
        for l in lines[1:]:
            ma = re.match(r"^\s*(\d+) \|   union \S+::\(anonymous at [^)]*:(\d+):\d+\)\s*$", l)
            if ma:
                # an anonymous union member (cpp2lean --mission names it after its line, `union'804`)
                members.append(("union'%s" % ma.group(2), int(ma.group(1)), False, None))
                continue
            mm = re.match(r"^\s*(\d+)(?::(\d+)-(\d+))? \|   (\S.*?) (\w+)$", l)        # a direct member (two spaces)
            if mm:
                if mm.group(2) is not None:
                    bit = int(mm.group(1)) * 8 + int(mm.group(2))
                    members.append((mm.group(5), bit, True, int(mm.group(3)) - int(mm.group(2)) + 1))
                else:
                    members.append((mm.group(5), int(mm.group(1)), False, None))
                continue
            ms = re.search(r"\[sizeof=(\d+), (?:dsize=\d+, )?align=(\d+)", l)
            if ms:
                size, align = int(ms.group(1)), int(ms.group(2))
                break
        if name not in out:
            out[name] = (size, align, members)
    return out


def main():
    i = sys.argv.index("--")
    sig_path, args = sys.argv[1], sys.argv[i + 1:]
    with open(sig_path) as f:
        sig = json.load(f)
    lays = sig.get("layouts", [])
    UNIONS.update(l["cxx"] for l in lays if l.get("union"))
    unity = os.path.join(ROOT, sig["source"])
    clang = clang_layouts(unity, [l["cxx"] for l in lays], args)
    bad = 0
    nfields = 0
    for l in lays:
        c = clang.get(l["cxx"])
        if c is None:
            print("check_layouts: %s: no layout from clang" % l["record"])
            bad += 1
            continue
        size, align, members = c
        cm = {m[0]: m for m in members}
        if (size, align) != (l["size"], l["align"]):
            print("check_layouts: %s: size/align %d/%d, clang %s/%s" % (l["record"], l["size"], l["align"], size, align))
            bad += 1
        if [m[0] for m in members] != [f[0] for f in l["fields"]]:
            print("check_layouts: %s: members %s, clang %s" % (l["record"], [f[0] for f in l["fields"]], [m[0] for m in members]))
            bad += 1
        for name, off, sz, isbit in l["fields"]:
            nfields += 1
            m = cm.get(name)
            if m is None:
                continue
            if isbit != m[2] or off != m[1] or (isbit and sz != m[3]):
                print("check_layouts: %s.%s: %s %d%s, clang %s %d%s" % (l["record"], name, "bit" if isbit else "byte", off,
                                                                         " width %d" % sz if isbit else "", "bit" if m[2] else "byte",
                                                                         m[1], " width %d" % m[3] if m[2] else ""))
                bad += 1
    print("check_layouts: %d records, %d members: %s" % (len(lays), nfields, "all equal to clang's" if not bad else "%d differ" % bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
