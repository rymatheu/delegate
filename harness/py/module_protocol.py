"""module_protocol.py: the generic Python side of a harness module (the counterpart of cpp/module_protocol.h).

A module provides an adapter that calls `serve(...)` with two functions:

    init(params: dict) -> None            build or reset the real objects from a parameter record
    step(inp: dict) -> dict               one tick of the real code: the output record, by field name

The schemas are not written here or in the adapter: they are read from build/gen/NAME/module_schema.json, which
`harness gen NAME` writes from the module's Lean declaration. The adapter names the fields it reads and writes;
`check_fields` refuses to start when they differ from the schema.

Protocol (all integers little-endian; records packed field by field, f32/i32/u32 as 4 bytes, floats as their bit
patterns, bool as one byte 0 or 1):

    request             reply
    'D'                 'K', u32 length, manifest (JSON text: name, code hash, flags, compiler, schemas)
    'I' params-record   'K'
    'S' input-record    'K' output-record          ('E' if no init has been done)
    'Q'                 'K', then the process exits

Values: an f32 field is given to the adapter as the Python float of its binary32 value (exact) and taken from it as
the binary32 nearest to the Python float (round to nearest even, overflow to an infinity, NaN kept); u32 and i32 as
Python ints (out of range is an error, not a wrap); bool as a Python bool.

The protocol owns file descriptor 1. `take_stdout()` must be called before anything else can print (a C library
writing to stdout would corrupt the records): it moves the protocol onto a private copy of fd 1 and points fd 1 and
sys.stdout at stderr.
"""
from __future__ import annotations

import json
import math
import os
import struct
import sys

TYPES = ("f32", "i32", "u32", "bool")


def load_schema(path):
    """{"name", "params", "input", "output"}: the module's schemas, each a list of {"name", "type", "doc"}."""
    with open(path) as fh:
        s = json.load(fh)
    for port in ("params", "input", "output"):
        for f in s[port]:
            if f["type"] not in TYPES:
                raise ValueError(f"{path}: field {f['name']}: unknown type {f['type']}")
    return s


def record_bytes(fields):
    return sum(1 if f["type"] == "bool" else 4 for f in fields)


def f32_bits(x) -> bytes:
    """The binary32 nearest to x (round to nearest even), overflow to +-inf, NaN as the quiet NaN 0x7fc00000."""
    x = float(x)
    if math.isnan(x):
        return struct.pack("<I", 0x7FC00000)
    try:
        return struct.pack("<f", x)
    except OverflowError:
        return struct.pack("<f", math.copysign(math.inf, x))


def unpack(fields, buf: bytes) -> dict:
    out, o = {}, 0
    for f in fields:
        t = f["type"]
        if t == "bool":
            out[f["name"]] = buf[o] != 0
            o += 1
            continue
        w = buf[o:o + 4]
        o += 4
        if t == "f32":
            out[f["name"]] = struct.unpack("<f", w)[0]
        elif t == "u32":
            out[f["name"]] = struct.unpack("<I", w)[0]
        else:
            out[f["name"]] = struct.unpack("<i", w)[0]
    return out


def pack(fields, rec: dict) -> bytes:
    parts = []
    for f in fields:
        v, t = rec[f["name"]], f["type"]
        if t == "f32":
            parts.append(f32_bits(v))
        elif t == "bool":
            parts.append(b"\x01" if v else b"\x00")
        elif t == "u32":
            v = int(v)
            if not 0 <= v < 2 ** 32:
                raise ValueError(f"output {f['name']} = {v} is not a u32")
            parts.append(struct.pack("<I", v))
        else:
            v = int(v)
            if not -2 ** 31 <= v < 2 ** 31:
                raise ValueError(f"output {f['name']} = {v} is not an i32")
            parts.append(struct.pack("<i", v))
    return b"".join(parts)


def check_fields(schema, params, inputs, outputs):
    """Refuse to run when the adapter's field names differ from the declaration's (order is the schema's)."""
    bad = []
    for port, mine in (("params", params), ("input", inputs), ("output", outputs)):
        theirs = [f["name"] for f in schema[port]]
        if sorted(theirs) != sorted(mine):
            bad.append(f"{port}: declaration {theirs}, adapter {list(mine)}")
    if bad:
        raise SystemExit(f"{schema['name']}: the adapter does not match the declaration "
                         f"(rebuild after `lake build`):\n  " + "\n  ".join(bad))


def take_stdout():
    """The protocol's output stream; fd 1 and sys.stdout then go to stderr."""
    proto = os.fdopen(os.dup(1), "wb", buffering=1 << 16)
    os.dup2(2, 1)
    sys.stdout = sys.stderr
    return proto


def manifest_json(schema, code_hash, flags, compiler) -> bytes:
    strip = lambda fs: [{"name": f["name"], "type": f["type"]} for f in fs]
    m = {"name": schema["name"], "code_hash": code_hash, "flags": flags, "compiler": compiler,
         "params": strip(schema["params"]), "input": strip(schema["input"]), "output": strip(schema["output"])}
    return json.dumps(m, separators=(",", ":")).encode()


def serve(schema, manifest: bytes, init, step, proto_out, proto_in=None):
    """The request loop on stdin (binary) and proto_out."""
    rin = proto_in or sys.stdin.buffer
    out = proto_out
    P, I, O = schema["params"], schema["input"], schema["output"]
    nP, nI = record_bytes(P), record_bytes(I)

    def read_exact(n):
        b = b""
        while len(b) < n:
            c = rin.read(n - len(b))
            if not c:
                return None
            b += c
        return b

    initialized = False
    while True:
        op = rin.read(1)
        if not op:
            return 0
        if op == b"D":
            out.write(b"K" + struct.pack("<I", len(manifest)) + manifest)
        elif op == b"I":
            b = read_exact(nP)
            if b is None:
                return 1
            init(unpack(P, b))
            initialized = True
            out.write(b"K")
        elif op == b"S":
            b = read_exact(nI)
            if b is None:
                return 1
            if not initialized:
                out.write(b"E")
            else:
                rec = pack(O, step(unpack(I, b)))
                out.write(b"K" + rec)
        elif op == b"Q":
            out.write(b"K")
            out.flush()
            return 0
        else:
            out.write(b"E")
            out.flush()
            return 2
        out.flush()
