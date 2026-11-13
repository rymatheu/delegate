#!/usr/bin/env python3
"""Compare two estimation traces (copter_ref --est, REFERENCE.md "Estimation output (Phase 3)").

Usage: reference/tools/est_compare.py A B [--from T] [--to T] [--show N] [--keys-of-a]

Steps are matched by their t= value (us; T may also be given in seconds with a trailing "s"); only steps
with from <= t <= to are compared. Every key=value token is split at the commas into values, and the
values are compared as strings, i.e. bit pattern against bit pattern (floats are hexadecimal bit
patterns). Prints the number of steps compared, the number of values compared and equal, the first
differing step and key with both values decoded, and the mismatch count per key (with the first step
of each). A step present in only one trace, or a key present in only one line, counts as a mismatch.
With --keys-of-a only the keys A's lines have are compared (B a trace of a probe with keys added since A was
written: the earlier keys). Exit 0 iff everything compared is equal (1 otherwise, 2 on a usage or format error).
Comment lines (starting with #, the task table) are not compared.
"""
from __future__ import annotations

import argparse
import re
import struct
import sys

# value kinds: n = decimal integer, f = float bit pattern (8 hex digits: binary32, 16: binary64),
# x = other hexadecimal bits (flag words, digests), s = one opaque string (the task list).
# A key's list of kinds is matched position by position; a trailing "*" repeats the last kind.
SCHEMA = {
    "t": "n", "init": "n", "in": "n", "dcb": "n", "tick": "n", "tasks": "s",
    "armed": "n", "flying": "nn", "tkd": "nnnn", "thgt": "n", "home": "nnnnnn",
    "cfg": "nnnnf*", "comp": "f*", "bgnd": "nf*",
    "q": "nffff", "rpy": "f*", "dcm": "f*", "vel": "nf*", "pos": "nf*", "loc": "nnnnn",
    "gyro": "f*", "accef": "f*", "resets": "n*", "healthy": "n", "initialised": "n",
    "origin": "nnnnn", "ekf": "n", "fs": "nx", "primary": "n", "ncores": "n",
    "gbias": "f*", "abias": "f*", "var": "nf*",
}
CORE_SCHEMA = {"x": "f*", "fs": "xn", "P": "x", "out": "x", "imu": "x", "var": "nf*", "gsf": "nffnx"}
CORE_KEY = re.compile(r"^c(\d+)\.(\w+)$")


def kinds_of(key: str, n: int) -> str:
    m = CORE_KEY.match(key)
    k = CORE_SCHEMA.get(m.group(2)) if m else SCHEMA.get(key)
    if k is None:
        k = "s*"
    if k.endswith("*"):
        base = k[:-1]
        return (base + base[-1] * max(0, n - len(base)))[:max(n, len(base))]
    return k


def decode(kind: str, v: str) -> str:
    try:
        if kind == "f":
            if len(v) == 8:
                return f"{struct.unpack('>f', bytes.fromhex(v))[0]!r} (binary32 {v})"
            if len(v) == 16:
                return f"{struct.unpack('>d', bytes.fromhex(v))[0]!r} (binary64 {v})"
        if kind == "x":
            return f"0x{v}"
    except ValueError:
        pass
    return v


def parse_time(s: str) -> int:
    return int(round(float(s[:-1]) * 1e6)) if s.endswith("s") else int(s)


def read(path: str, lo: int | None, hi: int | None) -> dict[int, dict[str, list[str]]]:
    steps: dict[int, dict[str, list[str]]] = {}
    with open(path) as f:
        for ln, line in enumerate(f, 1):
            if not line.strip() or line.startswith("#"):
                continue
            d: dict[str, list[str]] = {}
            for tok in line.split():
                k, sep, v = tok.partition("=")
                if not sep:
                    sys.exit(f"est_compare: {path}:{ln}: token without '=': {tok!r}")
                d[k] = [v] if SCHEMA.get(k) == "s" else v.split(",")
            if "t" not in d:
                sys.exit(f"est_compare: {path}:{ln}: no t=")
            t = int(d["t"][0])
            if (lo is not None and t < lo) or (hi is not None and t > hi):
                continue
            steps[t] = d
    return steps


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("a")
    ap.add_argument("b")
    ap.add_argument("--from", dest="lo", type=parse_time)
    ap.add_argument("--to", dest="hi", type=parse_time)
    ap.add_argument("--show", type=int, default=10, help="other differing keys listed at the first differing step")
    ap.add_argument("--keys-of-a", action="store_true", help="compare only the keys of A's lines (B may have more)")
    args = ap.parse_args()
    A = read(args.a, args.lo, args.hi)
    B = read(args.b, args.lo, args.hi)
    ts = sorted(set(A) | set(B))
    compared = equal = 0
    steps_compared = 0
    per_key: dict[str, list] = {}       # key -> [mismatching values, mismatching steps, first t]
    first = None                        # (t, key, index, kind, va, vb)
    first_step_keys: list[str] = []
    only = {"A": 0, "B": 0}
    for t in ts:
        if t not in A or t not in B:
            only["A" if t in A else "B"] += 1
            e = per_key.setdefault("<step>", [0, 0, t])
            e[0] += 1
            e[1] += 1
            if first is None:
                first = (t, "<step>", 0, "s", "present" if t in A else "absent", "present" if t in B else "absent")
            continue
        steps_compared += 1
        a, b = A[t], B[t]
        for key in list(a) + ([] if args.keys_of_a else [k for k in b if k not in a]):
            va, vb = a.get(key), b.get(key)
            if va is None or vb is None:
                e = per_key.setdefault(key, [0, 0, t])
                e[0] += 1
                e[1] += 1
                compared += 1
                if first is None:
                    first = (t, key, 0, "s", ",".join(va) if va else "<missing>", ",".join(vb) if vb else "<missing>")
                if first is not None and first[0] == t:
                    first_step_keys.append(key)
                continue
            n = max(len(va), len(vb))
            kinds = kinds_of(key, n)
            bad = 0
            for i in range(n):
                x = va[i] if i < len(va) else "<missing>"
                y = vb[i] if i < len(vb) else "<missing>"
                compared += 1
                if x == y:
                    equal += 1
                    continue
                bad += 1
                if first is None:
                    first = (t, key, i, kinds[i] if i < len(kinds) else "s", x, y)
            if bad:
                e = per_key.setdefault(key, [0, 0, t])
                e[0] += bad
                e[1] += 1
                if first is not None and first[0] == t:
                    first_step_keys.append(key)
    print(f"A: {args.a}\nB: {args.b}")
    rng = f" in [{args.lo if args.lo is not None else '-inf'}, {args.hi if args.hi is not None else '+inf'}] us" \
        if args.lo is not None or args.hi is not None else ""
    print(f"steps compared: {steps_compared}{rng} (only in A: {only['A']}, only in B: {only['B']})")
    print(f"values compared: {compared}, equal: {equal}, different: {compared - equal}")
    if first is None and not only["A"] and not only["B"]:
        print("all equal")
        return 0
    t, key, i, kind, x, y = first
    print(f"first difference: step t={t} ({t / 1e6:.6f} s), key {key}, value {i}")
    print(f"  A: {decode(kind, x)}")
    print(f"  B: {decode(kind, y)}")
    others = [k for k in first_step_keys if k != key]
    if others:
        print(f"  other keys differing at that step: {' '.join(others[:args.show])}" + (" ..." if len(others) > args.show else ""))
    print("mismatches per key (values, steps, first t):")
    for key, (nv, ns, t0) in sorted(per_key.items(), key=lambda kv: (kv[1][2], kv[0])):
        print(f"  {key:12s} {nv:9d} {ns:7d}  {t0}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
