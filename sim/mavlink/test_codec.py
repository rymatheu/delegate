#!/usr/bin/env python3
"""Codec test: the Lean MAVLink codec against pymavlink, message by message.

Run from the repository root after `lake build` (the codec driver is `leanfc --codec`):

    sim/mavlink/.venv/bin/python sim/mavlink/test_codec.py [--n 50] [--seed 1]

pymavlink is a test oracle only (LGPL, installed in the private sim/mavlink/.venv, not shipped). Its
Python dialect is generated from the same XML as Leanfc/Mavlink/Messages.lean, into
sim/mavlink/.gen/apm2.py, with pymavlink's own generator (mavgen).

For every supported message, `--n` random instances (random field values, about a third of the
fields zero so that MAVLink 2 truncation removes trailing bytes; floats from random bit patterns
plus infinities, -0 and the quiet NaN):

  1. encode: Lean (`E msgid seq sys comp words`) must give exactly pymavlink's MAVLink 2 bytes;
  2. decode MAVLink 2: pymavlink's frame parsed by Lean gives the same field values (floats by bits);
  3. decode MAVLink 1: pymavlink's frame with force_mavlink1, and a hand-built MAVLink 1 frame with
     only the base payload (extensions then decode as zero);
  4. a bad checksum is rejected; a signed frame is skipped;
  5. a stream of all frames with random garbage between them, and truncated frames (a frame cut short,
     then whole frames) through one persistent parser: every whole frame is found, in order.

Then the robustness test: random bytes through the parser (no crash; frames found only at the
checksum's chance rate) and frames cut at every length.
"""

import argparse
import os
import random
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".gen"))

import gen_messages  # noqa: E402

GEN = os.path.join(HERE, ".gen", "apm2.py")
if not os.path.exists(GEN):
    os.makedirs(os.path.dirname(GEN), exist_ok=True)
    subprocess.check_call([sys.executable, "-m", "pymavlink.tools.mavgen", "--lang=Python3",
                           "--wire-protocol=2.0", "--output=" + GEN,
                           os.path.join(gen_messages.DEFAULT_XML, "ardupilotmega.xml")])
import importlib  # noqa: E402
importlib.invalidate_caches()
import apm2  # noqa: E402
from pymavlink.generator.mavcrc import x25crc  # noqa: E402

BIN = os.path.join(ROOT, ".lake", "build", "bin", "leanfc")


class Lean:
    def __init__(self):
        self.p = subprocess.Popen([BIN, "--codec"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)

    def encode(self, msgid, seq, sys_, comp, words):
        self.p.stdin.write(f"E {msgid} {seq} {sys_} {comp} {' '.join(map(str, words))}\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline().split()
        return bytes.fromhex(line[1]) if line[1] != "?" else None

    def parse(self, data, persistent=False):
        self.p.stdin.write(f"{'S' if persistent else 'P'} {data.hex() or '00'}\n")
        self.p.stdin.flush()
        frames = []
        while True:
            t = self.p.stdout.readline().split()
            if t[0] == "END":
                return frames, int(t[1]), int(t[2])
            frames.append((int(t[1]), int(t[2]), int(t[3]), int(t[4]), int(t[5]),
                           None if t[6] == "?" else [int(x) for x in t[6:]]))

    def close(self):
        self.p.stdin.close()
        self.p.wait()


def f32_from_bits(b):
    return struct.unpack("<f", struct.pack("<I", b))[0]


def random_float_bits(rng):
    r = rng.random()
    if r < 0.03:
        return rng.choice([0x7F800000, 0xFF800000, 0x80000000, 0x7FC00000])
    while True:
        b = rng.getrandbits(32)
        if (b >> 23) & 0xFF != 0xFF:  # not NaN or infinity
            return b


def random_scalar(rng, t, zero):
    if zero:
        return 0
    if t == "float":
        return random_float_bits(rng)
    if t == "double":
        return rng.getrandbits(64)
    if t == "char":
        return rng.randrange(32, 127)
    bits = gen_messages.SIZES[t] * 8
    if t.startswith("u"):
        return rng.getrandbits(bits)
    return rng.getrandbits(bits) - (1 << (bits - 1))


def random_message(rng, m, cls):
    """(pymavlink message, words in declaration order)."""
    args, words = [], []
    for f in m.fields:
        zero = rng.random() < 0.3
        if f.type == "char":
            n = 0 if zero else rng.randrange(0, f.array + 1)
            s = bytes(random_scalar(rng, "char", False) for _ in range(n))
            args.append(s)
            words += list(s) + [0] * (f.array - n)
        elif f.array:
            vals = [random_scalar(rng, f.type, zero or rng.random() < 0.2) for _ in range(f.array)]
            if f.type == "float":
                args.append([f32_from_bits(v) for v in vals])
            else:
                args.append(vals)
            words += vals
        else:
            v = random_scalar(rng, f.type, zero)
            args.append(f32_from_bits(v) if f.type == "float" else v)
            words.append(v)
    msg = cls(*args)
    return msg, words


def v1_base_frame(m, seq, sys_, comp, full_payload):
    payload = full_payload[:m.base_len]
    hdr = struct.pack("<BBBBBB", 0xFE, len(payload), seq, sys_, comp, m.id)
    crc = x25crc(hdr[1:] + payload)
    crc.accumulate(struct.pack("B", m.crc_extra))
    return hdr + payload + struct.pack("<H", crc.crc), payload


def base_words(m, words):
    """The words with the extension fields zero (a MAVLink 1 frame carries no extensions)."""
    out, i = [], 0
    for f in m.fields:
        n = f.array or 1
        out += ([0] * n) if f.ext else words[i:i + n]
        i += n
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--random-bytes", type=int, default=2_000_000)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    msgs = gen_messages.load(gen_messages.DEFAULT_XML)
    sel = sorted((msgs[n] for n in gen_messages.MESSAGES), key=lambda m: m.id)
    lean = Lean()
    mav = apm2.MAVLink(None, srcSystem=1, srcComponent=1)
    smav = apm2.MAVLink(None, srcSystem=7, srcComponent=9)
    smav.signing.secret_key = bytes(range(32))
    smav.signing.sign_outgoing = True
    counts = dict(enc=0, enc_ok=0, dec2=0, dec2_ok=0, dec1=0, dec1_ok=0, dec1b=0, dec1b_ok=0,
                  badcrc=0, badcrc_ok=0, signed=0, signed_ok=0, truncated=0)
    fails = []
    all_frames = []  # (bytes, expected tuple)
    for m in sel:
        cls = apm2.mavlink_map[m.id]
        for k in range(a.n):
            msg, words = random_message(rng, m, cls)
            seq, sys_, comp = rng.randrange(256), rng.randrange(1, 256), rng.randrange(256)
            mav.seq, mav.srcSystem, mav.srcComponent = seq, sys_, comp
            v2 = msg.pack(mav)
            if v2[1] < m.max_len:
                counts["truncated"] += 1
            # 1. encode
            counts["enc"] += 1
            got = lean.encode(m.id, seq, sys_, comp, words)
            if got == v2:
                counts["enc_ok"] += 1
            else:
                fails.append(f"encode {m.name}: lean {got.hex() if got else None} pymavlink {v2.hex()}")
            # 2. decode MAVLink 2
            counts["dec2"] += 1
            fr, rej, sg = lean.parse(v2)
            exp = (2, seq, sys_, comp, m.id, words)
            if fr == [exp]:
                counts["dec2_ok"] += 1
            else:
                fails.append(f"decode v2 {m.name}: {fr} expected {exp}")
            all_frames.append((v2, exp))
            # 3. decode MAVLink 1 (pymavlink force_mavlink1: full payload, then base-only)
            if m.id < 256:
                v1 = msg.pack(mav, force_mavlink1=True)
                counts["dec1"] += 1
                fr, _, _ = lean.parse(v1)
                if fr == [(1, seq, sys_, comp, m.id, words)]:
                    counts["dec1_ok"] += 1
                else:
                    fails.append(f"decode v1 {m.name}: {fr}")
                v1b, _ = v1_base_frame(m, seq, sys_, comp, v1[6:-2])
                counts["dec1b"] += 1
                fr, _, _ = lean.parse(v1b)
                if fr == [(1, seq, sys_, comp, m.id, base_words(m, words))]:
                    counts["dec1b_ok"] += 1
                else:
                    fails.append(f"decode v1 base {m.name}: {fr}")
                all_frames.append((v1b, (1, seq, sys_, comp, m.id, base_words(m, words))))
            # 4. bad checksum, signed
            if k < 5:
                bad = bytearray(v2)
                bad[-1 - rng.randrange(2)] ^= 1 << rng.randrange(8)
                counts["badcrc"] += 1
                fr, rej, _ = lean.parse(bytes(bad))
                if fr == [] and rej >= 1:
                    counts["badcrc_ok"] += 1
                else:
                    fails.append(f"bad crc {m.name}: {fr}")
                smav.seq = seq
                sv = msg.pack(smav)
                counts["signed"] += 1
                fr, _, sgn = lean.parse(sv + v2)
                if fr == [exp] and sgn == 1:
                    counts["signed_ok"] += 1
                else:
                    fails.append(f"signed {m.name}: {fr} signed={sgn}")
    # 5. one stream with garbage between frames, and truncated frames
    rng.shuffle(all_frames)
    stream, expected = bytearray(), []
    garbage_bytes = 0
    cut = 0
    for data, exp in all_frames:
        r = rng.random()
        if r < 0.3:
            g = bytes(rng.getrandbits(8) for _ in range(rng.randrange(1, 40)))
            stream += g
            garbage_bytes += len(g)
        elif r < 0.4:
            other = all_frames[rng.randrange(len(all_frames))][0]
            stream += other[:rng.randrange(1, len(other))]
            cut += 1
        stream += data
        expected.append(exp)
    found = []
    for i in range(0, len(stream), 4096):
        fr, _, _ = lean.parse(bytes(stream[i:i + 4096]), persistent=True)
        found += fr
    # every expected frame must appear, in order (a garbage or cut prefix may in principle form an
    # extra frame only at the checksum's chance rate)
    it = iter(found)
    missing = sum(1 for e in expected if not any(e == f for f in it))
    extra = len(found) - (len(expected) - missing)
    # robustness: random bytes
    rnd = bytes(rng.getrandbits(8) for _ in range(a.random_bytes))
    false_frames = 0
    for i in range(0, len(rnd), 8192):
        fr, _, _ = lean.parse(rnd[i:i + 8192], persistent=True)
        false_frames += len(fr)
    # every prefix of a few frames: no frame, no crash
    prefix_frames = 0
    prefixes = 0
    for data, _ in all_frames[:40]:
        for n in range(len(data)):
            fr, _, _ = lean.parse(data[:n])
            prefixes += 1
            prefix_frames += len(fr)
    lean.close()

    print(f"messages: {len(sel)}  instances per message: {a.n}  (seed {a.seed})")
    print(f"encode (Lean bytes == pymavlink MAVLink 2 bytes): {counts['enc_ok']}/{counts['enc']}"
          f"  (truncated payloads among them: {counts['truncated']})")
    print(f"decode MAVLink 2 (pymavlink frame -> Lean fields): {counts['dec2_ok']}/{counts['dec2']}")
    print(f"decode MAVLink 1, pymavlink force_mavlink1: {counts['dec1_ok']}/{counts['dec1']}")
    print(f"decode MAVLink 1, base payload only (extensions zero): {counts['dec1b_ok']}/{counts['dec1b']}")
    print(f"bad checksum rejected: {counts['badcrc_ok']}/{counts['badcrc']}")
    print(f"signed frame skipped, next frame parsed: {counts['signed_ok']}/{counts['signed']}")
    print(f"stream: {len(expected)} frames, {garbage_bytes} garbage bytes, {cut} cut frames, "
          f"{len(stream)} bytes: missing {missing}, extra {extra}")
    print(f"random bytes: {len(rnd)} bytes, frames found {false_frames}")
    print(f"prefixes of 40 frames: {prefixes} parses, frames found {prefix_frames}")
    for f in fails[:20]:
        print("FAIL", f)
    ok = (not fails and missing == 0 and prefix_frames == 0)
    print("PASS" if ok else f"FAIL ({len(fails)} failures)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
