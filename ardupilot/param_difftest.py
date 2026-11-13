#!/usr/bin/env python3
"""Per-function differential test of the translated AP_Param (README.md, "Phase 4: AP_Param").

Both sides run the vehicle's AP_Param boot sequence on a storage image and then the same command script; the C++ side is
the reference vehicle itself (`copter_ref --storage IMAGE --param-dump OUT --param-test SCRIPT`: ArduPilot's real AP_Param,
StorageManager and every parameter table of the vehicle, after static construction), the Lean side the translation
(`lean/.lake/build/bin/param_dump IMAGE OUT --test SCRIPT`). Every output line must be equal.

Storage images (random, seeded): the recorded flight's image; blank storage; a valid header and garbage; the flight's
records with a sentinel (type 0x1f, key 0x1ff, 0x00000000 or 0xffffffff) at a random record boundary; the flight's image
with random bytes flipped; synthetic images of random records (real keys, types and group elements of the vehicle's
parameters, and random ones) with random values; a wrong header over valid records.
Commands (see reference/hal/param_dump.cpp): next_scalar from random tokens (real ones, neighbours, random), find_by_name
and find with real names, other case, prefixes, vector suffixes and random strings, find_by_index, set_float + save_sync
sequences with the storage digest after each, load, count_parameters after setting enable parameters, the enumeration,
load_all again.

Usage: ardupilot/param_difftest.py [--seed S] [--cases N] [--keep DIR]
CPP2LEAN_PARAM_MUTANT=1: also report against a mutated Lean build (the caller swaps the binary; see README).
"""
import argparse
import os
import random
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REF = os.path.join(ROOT, "build", "reference", "copter_ref")
LEAN = os.path.join(ROOT, "lean", ".lake", "build", "bin", "param_dump")
FLIGHT = os.path.join(ROOT, "sim", "out", "lockstep-flight", "storage_in.bin")
SIZE = 16384
TSIZE = {1: 1, 2: 2, 3: 4, 4: 4, 5: 12}


def records(img):
    out, ofs = [], 4
    while ofs + 4 <= len(img):
        h = struct.unpack_from("<I", img, ofs)[0]
        key = (h & 0xff) | (((h >> 13) & 1) << 8)
        typ = (h >> 8) & 0x1f
        if typ == 0x1f or key == 0x1ff or h in (0, 0xffffffff):
            break
        out.append((ofs, key, typ, h >> 14))
        ofs += 4 + TSIZE.get(typ, 0)
    return out, ofs


def header(key, typ, ge):
    return struct.pack("<I", (key & 0xff) | ((typ & 0x1f) << 8) | (((key >> 8) & 1) << 13) | ((ge & 0x3ffff) << 14))


def rand_value(r, typ):
    n = TSIZE.get(typ, 4)
    if typ == 4 and r.random() < 0.7:
        return struct.pack("<f", r.choice([0.0, 1.0, -1.0, 0.5, 100.0, 1e-3, 3e4, -0.0, float("inf")]) * r.choice([1, 2, 0.1]))
    return bytes(r.randrange(256) for _ in range(n))


def gen_image(r, kind, flight, params):
    img = bytearray(SIZE)
    if kind == 0:
        return bytes(flight)
    if kind == 1:
        return bytes(img)
    if kind == 2:
        img[0:4] = flight[0:4]
        for i in range(4, r.randrange(8, 400)):
            img[i] = r.randrange(256)
        return bytes(img)
    recs, end = records(flight)
    if kind == 3:
        img[:] = flight
        ofs = r.choice([o for o, _, _, _ in recs] + [end])
        img[ofs:ofs + 4] = r.choice([header(r.randrange(512), 0x1f, r.randrange(1 << 18)), header(0x1ff, r.randrange(1, 6), 0),
                                     b"\0\0\0\0", b"\xff\xff\xff\xff"])
        return bytes(img)
    if kind == 4:
        img[:] = flight
        for _ in range(r.randrange(1, 6)):
            img[r.randrange(4, end + 8)] ^= 1 << r.randrange(8)
        return bytes(img)
    if kind in (5, 6):
        img[0:4] = flight[0:4] if kind == 5 else bytes([0x50, 0x41, 7, 0])
        ofs = 4
        for _ in range(r.randrange(1, 60)):
            if r.random() < 0.8:
                key, ge, typ = r.choice(params)
            else:
                key, ge, typ = r.randrange(512), r.randrange(1 << 18) if r.random() < 0.5 else r.randrange(64), r.randrange(1, 6)
            if r.random() < 0.1:
                typ = r.randrange(1, 6)
            rec = header(key, typ, ge) + rand_value(r, typ)
            if ofs + len(rec) + 4 > SIZE:
                break
            img[ofs:ofs + len(rec)] = rec
            ofs += len(rec)
        img[ofs:ofs + 4] = header(0x1ff, 0x1f, 0x3ffff) if r.random() < 0.9 else bytes(4)
        return bytes(img)
    raise ValueError(kind)


def gen_script(r, names, tokens):
    out = []
    for _ in range(r.randrange(10, 40)):
        c = r.random()
        if c < 0.25:
            if r.random() < 0.6:
                k, g, i = r.choice(tokens)
                if r.random() < 0.4:
                    g = max(0, g + r.choice([-1, 1, 64, -64, 4096]))
                i = r.choice([0, 0, 1, 2, 3])
            else:
                k, g, i = r.randrange(80), r.randrange(1 << 18) if r.random() < 0.3 else r.randrange(256), r.randrange(4)
            out.append("enum %d %d %d" % (k % 512, g % (1 << 18), i))
        elif c < 0.45:
            n = r.choice(names)
            m = r.random()
            if m < 0.2:
                n = n.lower()
            elif m < 0.3:
                n = n[:r.randrange(1, len(n) + 1)]
            elif m < 0.4:
                n = n + r.choice(["_X", "_Y", "_Z", "X", "_"])
            elif m < 0.5:
                n = "".join(r.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789") for _ in range(r.randrange(1, 17)))
            out.append("name %s" % n)
        elif c < 0.55:
            out.append("index %d" % r.randrange(700))
        elif c < 0.8:
            n = r.choice(names)
            typ = r.choice([1, 2, 3, 4, 4])
            v = r.choice([0.0, 1.0, 2.0, -1.0, 0.5, 100.0, 1e5, 3.25, 1e-4]) if r.random() < 0.8 else struct.unpack("<f", bytes(r.randrange(256) for _ in range(4)))[0]
            out.append("set %s %d %08x %d" % (n, typ, struct.unpack("<I", struct.pack("<f", v))[0], r.random() < 0.3))
        elif c < 0.88:
            out.append("load %s" % r.choice(names))
        elif c < 0.95:
            en = [n for n in names if n.endswith(("_ENABLE", "_TYPE", "_ENABLED"))]
            n = r.choice(en) if en else r.choice(names)
            out.append("set %s 1 %08x 0" % (n, struct.unpack("<I", struct.pack("<f", r.choice([0.0, 1.0, 2.0])))[0]))
            out.append("count")
        else:
            out.append("loadall")
    out.append("count")
    out.append("dump")
    return out


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if p.returncode != 0:
        sys.exit("param_difftest: %s failed: %s" % (cmd[0], p.stderr[-2000:]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261104)
    ap.add_argument("--cases", type=int, default=60)
    ap.add_argument("--keep", default=None)
    ap.add_argument("--lean", default=LEAN)
    a = ap.parse_args()
    r = random.Random(a.seed)
    flight = open(FLIGHT, "rb").read()
    # the vehicle's parameters (names, tokens, storage keys) from the reference's enumeration of the flight image
    tmp = tempfile.mkdtemp(prefix="param_difftest")
    run([REF, "--storage", FLIGHT, "--param-dump", os.path.join(tmp, "names.txt")])
    names, tokens, params = [], [], []
    for line in open(os.path.join(tmp, "names.txt")):
        if line.startswith("#"):
            continue
        idx, tok, name, typ, val = line.split()
        k, g, i = (int(x) for x in tok.split(","))
        names.append(name)
        tokens.append((k, g, i))
        params.append((k, g, int(typ)))
    names = sorted(set(names))
    total = differ = cases_differ = 0
    kinds = [0, 1, 2, 3, 3, 4, 4, 5, 5, 5, 6]
    per_kind = {}
    for c in range(a.cases):
        kind = kinds[c % len(kinds)] if c < len(kinds) else r.choice(kinds)
        img = gen_image(r, kind, flight, params)
        script = gen_script(r, names, tokens)
        ip, sp = os.path.join(tmp, "img%d.bin" % c), os.path.join(tmp, "script%d.txt" % c)
        open(ip, "wb").write(img)
        open(sp, "w").write("\n".join(script) + "\n")
        ro, lo = os.path.join(tmp, "ref%d.txt" % c), os.path.join(tmp, "lean%d.txt" % c)
        run([REF, "--storage", ip, "--param-dump", ro, "--param-test", sp])
        run([a.lean, ip, lo, "--test", sp])
        A, B = open(ro).read().split("\n"), open(lo).read().split("\n")
        n = max(len(A), len(B))
        d = sum(1 for i in range(n) if (A[i] if i < len(A) else None) != (B[i] if i < len(B) else None))
        total += n
        differ += d
        cases_differ += d > 0
        pk = per_kind.setdefault(kind, [0, 0, 0])
        pk[0] += 1
        pk[1] += n
        pk[2] += d
        if d and cases_differ <= 3:
            first = next(i for i in range(n) if (A[i] if i < len(A) else None) != (B[i] if i < len(B) else None))
            print("case %d (image kind %d) line %d:\n  C++:  %s\n  Lean: %s" % (c, kind, first + 1, A[first] if first < len(A) else None,
                                                                            B[first] if first < len(B) else None))
    print("ardupilot/AP_Param: %d cases (images by kind: %s), %d commands; %d of %d lines differ; %d cases differ"
          % (a.cases, ", ".join("%d:%d" % (k, v[0]) for k, v in sorted(per_kind.items())),
             sum(1 for c in range(a.cases) for _ in open(os.path.join(tmp, "script%d.txt" % c))), differ, total, cases_differ))
    if a.keep:
        os.makedirs(a.keep, exist_ok=True)
        subprocess.run(["cp", "-R", tmp + "/.", a.keep])
    sys.exit(1 if differ else 0)


if __name__ == "__main__":
    main()
