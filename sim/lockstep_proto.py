#!/usr/bin/env python3
"""The per-step protocol of the reference vehicle (reference/REFERENCE.md, "Protocol"; the successor of
PROTOCOL.md proposed in PORT-PLAN.md 3.3).

One input line per step, one output line per input line. Every floating-point number is written as the
hexadecimal bit pattern of its binary32 (8 digits) or binary64 (16 digits) value, so a line denotes
exactly one set of bits and a recorded trace is a bit-level record of everything that crosses the
boundary.

Input:  t=<us> [imu0=<ax>,<ay>,<az>,<gx>,<gy>,<gz>[;...]] [imu1=...] [baro=<Pa>,<degC>]
        [mag=<x>,<y>,<z>] [gps=<lat>,<lon>,<alt>,<vn>,<ve>,<vd>] [rc=<16 decimal PWM>] [bat=<V>,<A>]
        [up=<hex bytes>]
Output: t=<us> pwm=<16 decimal PWM> [down=<hex bytes>]

As a script: `lockstep_proto.py decode FILE` prints a recorded input or output file with the numbers
in decimal and the MAVLink messages of up=/down= named (needs pymavlink).
"""
from __future__ import annotations

import struct
import sys


def f32(x: float) -> str:
    return struct.pack(">f", x).hex()


def f64(x: float) -> str:
    return struct.pack(">d", x).hex()


def unf32(h: str) -> float:
    return struct.unpack(">f", bytes.fromhex(h))[0]


def unf64(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


def encode_input(t_us: int, imu=None, imu1=None, baro=None, mag=None, gps=None, rc=None, bat=None,
                 up: bytes = b"") -> str:
    """imu, imu1: lists of (accel(3), gyro(3)) samples; baro: (Pa, degC); mag: (3,) mGauss;
    gps: (lat, lon, alt, vn, ve, vd) as doubles; rc: 16 ints; bat: (V, A)."""
    parts = [f"t={int(t_us)}"]
    for key, samples in (("imu0", imu), ("imu1", imu1)):
        if samples:
            parts.append(key + "=" + ";".join(",".join(f32(v) for v in (*a, *g)) for a, g in samples))
    if baro is not None:
        parts.append("baro=" + ",".join(f32(v) for v in baro))
    if mag is not None:
        parts.append("mag=" + ",".join(f32(v) for v in mag))
    if gps is not None:
        parts.append("gps=" + ",".join(f64(v) for v in gps))
    if rc is not None:
        parts.append("rc=" + ",".join(str(int(v)) for v in rc))
    if bat is not None:
        parts.append("bat=" + ",".join(f32(v) for v in bat))
    if up:
        parts.append("up=" + up.hex())
    return " ".join(parts)


def decode_output(line: str):
    """(t_us, pwm list of 16, downlink bytes) of an output line."""
    t_us, pwm, down = None, None, b""
    for tok in line.split():
        k, _, v = tok.partition("=")
        if k == "t":
            t_us = int(v)
        elif k == "pwm":
            pwm = [int(x) for x in v.split(",")]
        elif k == "down":
            down = bytes.fromhex(v)
    if t_us is None or pwm is None or len(pwm) != 16:
        raise ValueError(f"bad output line: {line[:200]!r}")
    return t_us, pwm, down


def decode_input(line: str) -> dict:
    d = {}
    for tok in line.split():
        k, _, v = tok.partition("=")
        if k == "t":
            d[k] = int(v)
        elif k in ("imu0", "imu1"):
            d[k] = [[unf32(h) for h in s.split(",")] for s in v.split(";")]
        elif k in ("baro", "mag", "bat"):
            d[k] = [unf32(h) for h in v.split(",")]
        elif k == "gps":
            d[k] = [unf64(h) for h in v.split(",")]
        elif k == "rc":
            d[k] = [int(x) for x in v.split(",")]
        elif k == "up":
            d[k] = bytes.fromhex(v)
    return d


def _main():
    if len(sys.argv) != 3 or sys.argv[1] != "decode":
        sys.exit("usage: lockstep_proto.py decode FILE")
    try:
        from pymavlink.dialects.v20 import ardupilotmega as mav
        parsers = {"up": mav.MAVLink(None), "down": mav.MAVLink(None)}
        for p in parsers.values():
            p.robust_parsing = True
    except ImportError:
        parsers = None
    for line in open(sys.argv[2]):
        line = line.rstrip("\n")
        if " pwm=" in line:
            t, pwm, down = decode_output(line)
            out = [f"t={t}", "pwm=" + ",".join(map(str, pwm))]
            data = {"down": down}
        else:
            d = decode_input(line)
            out = [f"t={d['t']}"]
            for k in ("imu0", "imu1"):
                if k in d:
                    out.append(k + "=" + ";".join(",".join(f"{x:.9g}" for x in s) for s in d[k]))
            for k in ("baro", "mag", "bat"):
                if k in d:
                    out.append(k + "=" + ",".join(f"{x:.9g}" for x in d[k]))
            if "gps" in d:
                out.append("gps=" + ",".join(f"{x:.17g}" for x in d["gps"]))
            if "rc" in d:
                out.append("rc=" + ",".join(map(str, d["rc"])))
            data = {"up": d.get("up", b"")}
        for k, b in data.items():
            if b and parsers:
                msgs = parsers[k].parse_buffer(b) or []
                out.append(k + "=[" + " ".join(m.get_type() for m in msgs) + f"] ({len(b)} bytes)")
            elif b:
                out.append(f"{k}=({len(b)} bytes)")
        print(" ".join(out))


if __name__ == "__main__":
    _main()
