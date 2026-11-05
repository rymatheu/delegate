#!/usr/bin/env python3
"""Differential test of cpp2lean: the C++ examples compiled with clang against their Lean
translations compiled with Lean, on the same inputs, compared bit for bit.

Usage: python3 difftest.py [--seed S] [--random N] [example ...]
       (default: seed 20261104, 2000 random lines, every examples/*.cpp except *_driver.cpp)

For each example E (examples/E.cpp):
  1. cpp2lean.py translates E.cpp into lean/<Namespace>.lean (+ signatures.json);
  2. a C++ driver examples/E_driver.cpp is generated (it #includes E.cpp, so static functions are
     visible) and compiled with clang and the flags of the compilation assumptions;
  3. lean/Main.lean, the Lean driver for every example, is generated, the translated modules are
     added to the roots in lean/lakefile.toml, and the package is built with `lake build`;
  4. inputs are generated: 2000 random lines (fixed seed) plus corner-case lines;
  5. both drivers read the same lines from stdin; for every input line they call every function
     of the example and print one line per call: `<input line> <function> <fields>`, where a
     Float32/Float result is printed as its bit pattern in hex and a decimal, an integer result
     in decimal, a bool as 0/1;
  6. the outputs are compared line by line: function name and the hex bit pattern for floating
     results (the decimals are informational: C prints %.9g/%.17g, Lean its own toString), the
     decimal for integer and bool results.

Signaling NaNs. A Lean `Float32`/`Float` cannot hold a signaling NaN (`ofBits` quiets it), and
libm's `fmaxf`/`fminf` (IEEE 754-2008 maxNum/minNum) treat a signaling NaN operand differently from a
quiet one, so the C++ drivers read a signaling NaN input with its quiet bit set (sign and payload
kept): both sides then get a quiet NaN.

NaN rule. Lean 4.33's `Float32.toBits`/`Float.toBits` (and `ofBits`) canonicalize every NaN to
0x7fc00000 / 0x7ff8000000000000 (the runtime agrees with the logical model of floats, which has a
single NaN), so a Lean program cannot observe a NaN's sign or payload. A floating result therefore
matches if the hex fields are equal, or if both are NaN. The number of lines that match only by this
rule is reported separately. No other relaxation is applied.

Exit status 0 iff no line differs.
"""

import json
import os
import random
import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEMO = os.path.join(HERE, "lean")
EX = os.path.join(HERE, "examples")
BUILD = os.path.join(HERE, "build")
sys.path.insert(0, HERE)
import cpp2lean  # noqa: E402

CXX = os.environ.get("CXX", "clang++")
SEED = 20261104
N_RANDOM = 2000
CORNER_CAP = 20000

# ---------------------------------------------------------------------------------------------
# Types of the drivers' I/O, by the C++ type names of signatures.json.

INTS = {"int8_t": (8, True), "int16_t": (16, True), "int32_t": (32, True), "int64_t": (64, True),
        "uint8_t": (8, False), "uint16_t": (16, False), "uint32_t": (32, False), "uint64_t": (64, False),
        "size_t": (64, False)}
LEAN_INT = {"size_t": "USize"}
TYPE_ORDER = ["float", "double", "bool"] + sorted(INTS)


def lean_type(c):
    if c == "float":
        return "Float32"
    if c == "double":
        return "Float"
    if c == "bool":
        return "Bool"
    if c in LEAN_INT:
        return LEAN_INT[c]
    bits, signed = INTS[c]
    return ("Int" if signed else "UInt") + str(bits)


def slots_of(funcs):
    """Input columns: for each type, as many as the most parameters of that type in a function."""
    need = {}
    for f in funcs:
        count = {}
        for _, t in f["params"]:
            count[t] = count.get(t, 0) + 1
        for t, c in count.items():
            need[t] = max(need.get(t, 0), c)
    return [(t, k) for t in TYPE_ORDER for k in range(need.get(t, 0))]


def arg_slots(f, slots):
    seen = {}
    out = []
    for _, t in f["params"]:
        k = seen.get(t, 0)
        seen[t] = k + 1
        out.append(slots.index((t, k)))
    return out


# ---------------------------------------------------------------------------------------------
# Inputs. Floating values are written as bit patterns in hex, integers in decimal.

def f32_bits(x):
    return struct.unpack(">I", struct.pack(">f", x))[0]


def f64_bits(x):
    return struct.unpack(">Q", struct.pack(">d", x))[0]


def rand_value(rng, t):
    u = rng.random()
    if t == "float" or t == "double":
        tobits = f32_bits if t == "float" else f64_bits
        if u < 0.4:
            return tobits(rng.uniform(-2.0, 2.0))
        if u < 0.6:
            return tobits(rng.uniform(-1000.0, 1000.0))
        if u < 0.8:
            return tobits(rng.choice([-1.0, 1.0]) * 10.0 ** rng.uniform(-8.0, 8.0))
        if t == "float":
            return (rng.getrandbits(1) << 31) | (rng.randrange(0, 255) << 23) | rng.getrandbits(23)
        return (rng.getrandbits(1) << 63) | (rng.randrange(0, 2047) << 52) | rng.getrandbits(52)
    if t == "bool":
        return rng.getrandbits(1)
    bits, signed = INTS[t]
    lo, hi = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)
    if u < 0.4:
        return max(lo, min(hi, rng.randint(-10, 10)))
    if u < 0.7:
        return max(lo, min(hi, rng.randint(-100000, 100000)))
    return rng.randint(lo, hi)


F32_CORNERS = [0x00000000, 0x80000000, 0x3f800000, 0xbf800000, 0x3f000000, 0x3dcccccd,
               0x00000001, 0x80000001, 0x007fffff, 0x00800000, 0x34000000, 0x4b800000,
               0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000,
               0x7fc00000, 0xffc00000, 0x7fc00001, 0x7f800001]
F64_CORNERS = [0x0000000000000000, 0x8000000000000000, 0x3ff0000000000000, 0xbff0000000000000,
               0x3fe0000000000000, 0x3fb999999999999a, 0x0000000000000001, 0x8000000000000001,
               0x000fffffffffffff, 0x0010000000000000, 0x3cb0000000000000, 0x4340000000000000,
               0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000,
               0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000001, 0x7ff0000000000001]


def corners(t):
    if t == "float":
        return F32_CORNERS
    if t == "double":
        return F64_CORNERS
    if t == "bool":
        return [0, 1]
    bits, signed = INTS[t]
    if signed:
        return [0, 1, -1, 2, -2, 7, 8, 9, 31, 32, -(1 << (bits - 1)), (1 << (bits - 1)) - 1]
    return [0, 1, 2, 7, 8, 9, 31, 32, 1 << (bits - 1), (1 << bits) - 1]


def corner_lines(slots):
    """The full product of the slots' corner values, over the longest prefix of slots whose
    product stays within CORNER_CAP lines; the remaining slots cycle through their corners."""
    lists = [corners(t) for t, _ in slots]
    prefix, size = 0, 1
    while prefix < len(lists) and size * len(lists[prefix]) <= CORNER_CAP:
        size *= len(lists[prefix])
        prefix += 1
    rows = [[]]
    for lst in lists[:prefix]:
        rows = [r + [v] for r in rows for v in lst]
    out = []
    for i, r in enumerate(rows):
        rest = [lists[j][(i * (j + 1) + j) % len(lists[j])] for j in range(prefix, len(lists))]
        out.append(r + rest)
    return out


def fmt_value(t, v):
    if t == "float":
        return "%08x" % v
    if t == "double":
        return "%016x" % v
    return str(v)


def make_inputs(slots, seed):
    rng = random.Random(seed)
    rows = [[rand_value(rng, t) for t, _ in slots] for _ in range(N_RANDOM)]
    rows += corner_lines(slots)
    return "".join(" ".join(fmt_value(t, v) for (t, _), v in zip(slots, r)) + "\n" for r in rows), len(rows)


# ---------------------------------------------------------------------------------------------
# C++ driver.

def cpp_driver(example, funcs, slots):
    ctype = {"float": "float", "double": "double", "bool": "bool"}
    lines = ["// Generated by cpp2lean/difftest.py. Reads input lines (README.md, \"Differential test\"),",
             "// calls every function of %s.cpp on each line, prints one line per call." % example,
             "#include \"%s.cpp\"" % example,
             "#include <cinttypes>", "#include <cstdio>", "#include <cstdlib>", "#include <cstring>", "",
             "static float in_f32(const char *s) { uint32_t u = (uint32_t)strtoul(s, nullptr, 16); if ((u & 0x7f800000u) == 0x7f800000u && (u & 0x7fffffu)) u |= 0x400000u; float f; memcpy(&f, &u, 4); return f; }",
             "static double in_f64(const char *s) { uint64_t u = strtoull(s, nullptr, 16); if ((u & 0x7ff0000000000000ull) == 0x7ff0000000000000ull && (u & 0xfffffffffffffull)) u |= 0x8000000000000ull; double d; memcpy(&d, &u, 8); return d; }",
             "static void out_f32(float f) { uint32_t u; memcpy(&u, &f, 4); printf(\" %08x %.9g\\n\", u, (double)f); }",
             "static void out_f64(double d) { uint64_t u; memcpy(&u, &d, 8); printf(\" %016llx %.17g\\n\", (unsigned long long)u, d); }",
             "static void out_i(long long v) { printf(\" %lld\\n\", v); }",
             "static void out_u(unsigned long long v) { printf(\" %llu\\n\", v); }", "",
             "int main() {", "    char buf[4096];", "    long line = 0;",
             "    while (fgets(buf, sizeof buf, stdin)) {", "        line++;",
             "        char *tok[%d];" % max(1, len(slots)), "        int nt = 0;",
             "        for (char *p = strtok(buf, \" \\n\"); p && nt < %d; p = strtok(nullptr, \" \\n\")) tok[nt++] = p;" % max(1, len(slots)),
             "        if (nt != %d) { fprintf(stderr, \"bad input line %%ld\\n\", line); return 1; }" % len(slots)]
    for i, (t, k) in enumerate(slots):
        if t == "float":
            lines.append("        float s%d = in_f32(tok[%d]);" % (i, i))
        elif t == "double":
            lines.append("        double s%d = in_f64(tok[%d]);" % (i, i))
        elif t == "bool":
            lines.append("        bool s%d = atoi(tok[%d]) != 0;" % (i, i))
        else:
            bits, signed = INTS[t]
            fn = "strtoll" if signed else "strtoull"
            lines.append("        %s s%d = (%s)%s(tok[%d], nullptr, 10);" % (t, i, t, fn, i))
    for f in funcs:
        args = ", ".join("s%d" % j for j in arg_slots(f, slots))
        call = "%s(%s)" % (f["name"], args)
        lines.append("        printf(\"%%ld %s\", line);" % f["name"])
        r = f["ret"]
        if r == "float":
            lines.append("        out_f32(%s);" % call)
        elif r == "double":
            lines.append("        out_f64(%s);" % call)
        elif r == "bool":
            lines.append("        out_i(%s ? 1 : 0);" % call)
        elif INTS[r][1]:
            lines.append("        out_i((long long)%s);" % call)
        else:
            lines.append("        out_u((unsigned long long)%s);" % call)
    lines += ["    }", "    return 0;", "}", ""]
    return "\n".join(lines)


# ---------------------------------------------------------------------------------------------
# Lean driver.

LEAN_HEADER = '''%s

/-!
Generated by cpp2lean/difftest.py: the Lean side of the differential test. `demo <example>` reads
input lines from stdin (README.md, "Differential test"), calls every translated function of the
example on each line, and prints one line per call: floating results as the hex bit pattern
(`Float32.toBits`/`Float.toBits`) and Lean's `toString`, integers in decimal, bools as 0/1.
-/

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d

def inF32 (s : String) : Float32 := Float32.ofBits (hexNat s).toUInt32
def inF64 (s : String) : Float := Float.ofBits (hexNat s).toUInt64
def inInt (s : String) : Int := (s.toInt?).getD 0
def inNat (s : String) : Nat := (s.toNat?).getD 0

def outF32 (x : Float32) : String := " " ++ hex 8 x.toBits.toNat ++ " " ++ toString x
def outF64 (x : Float) : String := " " ++ hex 16 x.toBits.toNat ++ " " ++ toString x
def outB (b : Bool) : String := if b then " 1" else " 0"

-- typed tokens of the class drivers
def tF32 (x : Float32) : String := " f:" ++ hex 8 x.toBits.toNat
def tF64 (x : Float) : String := " d:" ++ hex 16 x.toBits.toNat
def tB (b : Bool) : String := if b then " b:1" else " b:0"
def tI (x : String) : String := " i:" ++ x
def tS (x : String) : String := " s:" ++ String.join (x.toUTF8.toList.map (fun b => hex 2 b.toNat))
'''


def lean_in(t, tok):
    if t == "float":
        return "inF32 %s" % tok
    if t == "double":
        return "inF64 %s" % tok
    if t == "bool":
        return "(%s != \"0\")" % tok
    bits, signed = INTS[t]
    lt = lean_type(t)
    if signed:
        return "%s.ofInt (inInt %s)" % (lt, tok)
    return "%s.ofNat (inNat %s)" % (lt, tok)


def lean_out(t, e):
    if t == "float":
        return "outF32 (%s)" % e
    if t == "double":
        return "outF64 (%s)" % e
    if t == "bool":
        return "outB (%s)" % e
    return "\" \" ++ toString (%s)" % e


def lean_driver(examples, class_parts):
    """examples: (namespace, scalar free functions, slots, literals); class_parts: (tag, lines)."""
    imports = "\n".join("import %s" % ns for ns in [ns for ns, _, _, _ in examples] + [x for x in EXTRA_IMPORTS if x not in [e[0] for e in examples]])
    out = [LEAN_HEADER % imports]
    for ns, funcs, slots, _ in examples:
        if not funcs:
            continue
        out.append("def run%s (line : Nat) (t : Array String) : String := Id.run do" % ns)
        for i, (t, k) in enumerate(slots):
            out.append("  let s%d : %s := %s" % (i, lean_type(t), lean_in(t, "t[%d]!" % i)))
        out.append("  let mut o := \"\"")
        for f in funcs:
            args = " ".join("s%d" % j for j in arg_slots(f, slots))
            out.append("  o := o ++ toString line ++ \" %s\" ++ %s ++ \"\\n\"" % (f["name"], lean_out(f["ret"], "%s %s" % (f["lean"], args))))
        out.append("  return o")
        out.append("")
    for tag, lines in class_parts:
        out += lines
    out.append("partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (run : Nat → Array String → String) (n : Nat) : IO Unit := do")
    out.append("  let line ← h.getLine")
    out.append("  if line.isEmpty then return")
    out.append("  let toks := ((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")")
    out.append("  out.putStr (run (n + 1) toks.toArray)")
    out.append("  loop h out run (n + 1)")
    out.append("")
    out.append("/-- Each floating literal the translator emitted, with the bit pattern clang gives it. -/")
    out.append("def literals : List (String × String × String) := [")
    rows = []
    for ns, _, _, lits in examples:
        for l in lits:
            hexw = len(l["bits"])
            rows.append("  (%s, \"%s\", hex %d (%s).toBits.toNat)" % (json.dumps(ns + ":" + l["at"] + " " + l["cpp"]), l["bits"], hexw, l["lean"]))
    out.append(",\n".join(rows))
    out.append("]")
    out.append("")
    out.append("def main (args : List String) : IO UInt32 := do")
    out.append("  if args == [\"--literals\"] then")
    out.append("    for (w, e, a) in literals do IO.println s!\"{w} {e} {a}\"")
    out.append("    return 0")
    for tag, _ in class_parts:
        out.append("  if args == [\"%s\"] then" % tag)
        out.append("    run%s" % tag)
        out.append("    return 0")
    out.append("  let run : Option (Nat → Array String → String) := match args with")
    names = [ns for ns, funcs, _, _ in examples if funcs]
    for ns in names:
        out.append("    | [\"%s\"] => some run%s" % (ns, ns))
    out.append("    | _ => none")
    out.append("  match run with")
    out.append("  | none => IO.eprintln \"usage: demo <%s>\"; return 1" % "|".join(names + [t for t, _ in class_parts]))
    out.append("  | some r => loop (← IO.getStdin) (← IO.getStdout) r 0; return 0")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------------------------
# Class drivers: an input line is a member function name, its arguments, and a value for every
# field of the class's Inputs; one object (C++) or one state (Lean) persists across the lines.
# Every line prints the call's result, its reference parameters after the call, and every leaf of
# the state (and parameters) after the call, as typed tokens: f:<hex> (float), d:<hex> (double),
# b:0/1, i:<decimal> (integers and enums).

SCALARS = ("float", "double", "bool")
EMITTED_ENUMOF = set()
EXTRA_IMPORTS = []      # modules of other translations a configuration's Lean expressions use ("lean_imports")


def is_int_type(t):
    return t in INTS


def drivable(cls, m, extra=(), enum_leaves=False):
    if m["kind"] != "method" or (m["access"] != "public" and m["lean"].split(".", 1)[1] not in extra):
        return False
    if any(p["ref"] == "ptr" for p in m["params"]):
        return False                        # a nullable out-pointer parameter (not driven)
    if not all((p["scalar"] or simple_leaves(p.get("leaves")) or (enum_leaves and p.get("leaves") and p["ref"] != "mut"))
               and not p["boundary"] for p in m["params"]):
        return False
    return m["ret"] == "void" or m["ret_scalar"] or m["ret"] == "const char *" or simple_leaves(m.get("ret_leaves"))


def simple_leaves(leaves):
    return bool(leaves) and all(lf["enum"] is None for lf in leaves)


def slots_of_param(p):
    """The input tokens of a parameter: (type, name for its range, enum); a struct or class value
    has one per scalar leaf, whose range is that of `param.leaf`, else that of `param`."""
    if p.get("leaves") and not p["scalar"]:
        return [(lf["type"], "%%%s.%s" % (p["name"], lf["lean"]), lf.get("enum")) for lf in p["leaves"]]
    return [(p["type"], p["name"], p["enum"])]


def cpp_call_name(cls, m):
    rel = m["lean"][len(cls["lean"]) + 1:] if m["lean"].startswith(cls["lean"] + ".") else m["lean"]
    if m["owner"] != cls["cxx"] and "." in rel:       # a base's version a derived class overrides
        return "%s::%s" % (m["owner"], m["cxx"])
    return m["cxx"]


def enum_info(sig, lean):
    for e in sig["enums"]:
        if e["lean"] == lean:
            return e
    raise KeyError(lean)


def range_of(ranges, name):
    """The range of a parameter or state leaf (its name), of a leaf of a struct parameter (`%` and
    `param.leaf`, `%heading.yaw_rate_rads`: that name, else the parameter's, `heading`) or of an
    input (`@` and its path, `@get_gyro_latest.x`: the path, else each shorter prefix of it, else
    its last component, `millis` for `_slew_limiter.millis`)."""
    if name.startswith("@"):
        parts = name[1:].split(".")
        for k in range(len(parts), 0, -1):
            if ".".join(parts[:k]) in ranges:
                return ranges[".".join(parts[:k])]
        return ranges.get(parts[-1])
    if name.startswith("%"):
        return ranges.get(name[1:], ranges.get(name[1:].split(".")[0]))
    return ranges.get(name)


def rand_arg(rng, ptype, name, ranges, sig, enum=None, prob=0.85):
    """A random value (as the line token) for a parameter or input: with probability prob from
    its range, if it has one, else from the free-function mixture."""
    if enum is not None:
        return str(rng.choice(enum_info(sig, enum)["values"])[1])
    r = range_of(ranges, name)
    if ptype in ("float", "double"):
        tobits = f32_bits if ptype == "float" else f64_bits
        if r is not None and rng.random() < prob:
            return fmt_value(ptype, tobits(rng.uniform(r[0], r[1])))
        return fmt_value(ptype, rand_value(rng, ptype))
    if ptype == "bool":
        return str(rng.getrandbits(1))
    if r is not None and rng.random() < prob:
        v = rng.randint(int(r[0]), int(r[1]))
        bits, signed = INTS[ptype]
        v %= 1 << bits                      # a value of the type (as the C++ driver's conversion makes it)
        if signed and v >= 1 << (bits - 1):
            v -= 1 << bits
        return str(v)
    return str(rand_value(rng, ptype))


def token_value(ptype, tok):
    """The number a token stands for (a NaN compares false with everything, so it is outside every domain)."""
    if ptype == "float":
        return struct.unpack(">f", struct.pack(">I", int(tok, 16)))[0]
    if ptype == "double":
        return struct.unpack(">d", struct.pack(">Q", int(tok, 16)))[0]
    return int(tok)


def corner_tokens(ptype, sig, enum=None):
    if enum is not None:
        return [str(v[1]) for v in enum_info(sig, enum)["values"]]
    return [fmt_value(ptype, v) for v in corners(ptype)]


def flat_inputs(sig, cls, prefix=""):
    """The Inputs fields of a class with those of its members' Inputs, as dotted paths; a field of
    a struct or class type (`get_quat_body_to_ned_q : Quaternion.State`) by its scalar leaves."""
    out = []
    for i in cls["inputs"]:
        # a live read (--boundary-live): its value on the line, which the Lean driver turns into a
        # function of the output log so far and of the read's arguments (lean_inputs_record)
        live = {"field": prefix + i["lean"], "args": i["live"]["args"]} if i.get("live") else None
        if i.get("leaves") and i["type"] not in SCALARS and i["type"] not in INTS:
            out += [{"path": prefix + i["lean"] + "." + lf["lean"], "type": lf["type"], "live": live} for lf in i["leaves"]]
        else:
            out.append({"path": prefix + i["lean"], "type": i["type"], "live": live})
    for sub in cls["sub_inputs"]:
        sc = next(c for c in sig["classes"] if c["cxx"] == sub["class"])
        out += flat_inputs(sig, sc, prefix + sub["field"] + ".")
    return out


def flat_outputs(sig, cls, prefix=""):
    """The scalar leaves of a class's Outputs with those of its members' Outputs, as dotted paths."""
    out = []
    for o in cls.get("outputs", []):
        if o["scalar"]:
            out.append({"path": prefix + o["lean"], "type": o["type"]})
        elif o["leaves"] is not None:
            out += [{"path": prefix + o["lean"] + "." + lf["lean"], "type": lf["type"]} for lf in o["leaves"]]
        else:
            raise SystemExit("difftest: output `%s` of %s has no scalar leaves" % (o["lean"], cls["cxx"]))
    for sub in cls.get("sub_outputs", []):
        sc = next(c for c in sig["classes"] if c["cxx"] == sub["class"])
        out += flat_outputs(sig, sc, prefix + sub["field"] + ".")
    return out


def live_value(ftype, v, args):
    """The value a live read returns in the difftest (ardupilot/cpp2lean_events.h): the line's value
    plus 0.125 times the number of calls in the log `o'` so far, plus 0.5, 0.25, ... times its
    floating arguments of the same type, evaluated left to right as the C++ stand-ins do."""
    if ftype not in ("float", "double"):
        return v
    lt = lean_type(ftype)
    n = "o'.size.toFloat" + (".toFloat32" if ftype == "float" else "")
    text = "%s + (0.125 : %s) * %s" % (v, lt, n)
    c = 0.5
    for k, a in enumerate(args):
        if a == ftype:
            text += " + (%s : %s) * a'%d" % (repr(c), lt, k)
            c /= 2
    return text


def lean_inputs_record(fins, first_tok):
    """Lean structure instance for the flattened Inputs, the k-th field read from token first_tok + k;
    a live read is a function `fun o' a'0 ... => value` (live_value)."""
    tree = {}
    lives = {}
    for k, fi in enumerate(fins):
        parts = fi["path"].split(".")
        node = tree
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        if fi.get("enum"):
            v = "enumOf_%s (inInt t[%d]!)" % (fi["enum"].replace(".", "_"), first_tok + k)
        else:
            v = lean_in(fi["type"], "t[%d]!" % (first_tok + k))
        if fi.get("live"):
            lives[fi["live"]["field"]] = fi["live"]["args"]
            v = live_value(fi["type"], v, fi["live"]["args"])
        node[parts[-1]] = v

    def render(node, path):
        items = []
        for k, v in node.items():
            p = path + [k]
            text = render(v, p) if isinstance(v, dict) else v
            if ".".join(p) in lives:
                text = "fun o'%s => %s" % ("".join(" a'%d" % i for i in range(len(lives[".".join(p)]))), text)
            items.append("%s := %s" % (k, text))
        return "{ " + ", ".join(items) + " }"
    return render(tree, [])


def state_leaves(cls, cfg):
    """The state leaves an input line sets before the call (config "state_from_line"): every leaf of
    the class's State (not its Params)."""
    if not cfg.get("state_from_line"):
        return []
    return [lf for lf in cls["leaves"] if lf["root"] == "s"]


def unit_vector(rng, n):
    """A random unit vector of dimension n (normal deviates, normalized in double), as float bits."""
    while True:
        v = [rng.gauss(0.0, 1.0) for _ in range(n)]
        norm = sum(x * x for x in v) ** 0.5
        if norm > 1e-6:
            return [fmt_value("float", f32_bits(x / norm)) for x in v]


def rotation_matrix(rng):
    """The nine entries (rows a, b, c) of a random rotation matrix as float bits: ZYX Euler angles,
    with pitch exactly +-90 degrees (gimbal lock: c.x = -+1) on one draw in ten."""
    import math
    r, y = rng.uniform(-math.pi, math.pi), rng.uniform(-math.pi, math.pi)
    p = rng.choice([-math.pi / 2, math.pi / 2]) if rng.random() < 0.1 else rng.uniform(-1.5, 1.5)
    cr, sr, cp, sp, cy, sy = math.cos(r), math.sin(r), math.cos(p), math.sin(p), math.cos(y), math.sin(y)
    m = [cp * cy, sr * sp * cy - cr * sy, cr * sp * cy + sr * sy,
         cp * sy, sr * sp * sy + cr * cy, cr * sp * sy - sr * cy,
         -sp, sr * cp, cr * cp]
    return [fmt_value("float", f32_bits(v)) for v in m]


def class_inputs(sig, cls, cfg, seed, ncalls, methods=None):
    rng = random.Random(seed)
    ranges = cfg.get("ranges", {})
    if methods is None:
        methods = [m for m in cls["methods"] if drivable(cls, m, cfg.get("extra_methods", []))]
    exclude = set(cfg.get("exclude", []))       # not called at random nor with corner values (setup calls may use them)
    chosen = [m for m in methods if m["lean"].split(".")[-1] not in exclude and m["lean"].split(".", 1)[1] not in exclude]
    sleaves = state_leaves(cls, cfg)
    unit_args = cfg.get("unit_args", {})          # parameter name -> probability of a unit vector
    unit_state = cfg.get("unit_state")            # {"leaves": [...], "prob": p}: a unit quaternion
    weights = [cfg.get("weights", {}).get(m["lean"].split(".", 1)[1], 1) for m in chosen]
    ins = flat_inputs(sig, cls)
    aliases = cfg.get("input_aliases", {})
    paths = [i["path"] for i in ins]

    def line(m, args):
        return " ".join([m["lean"].split(".", 1)[1]] + args) + "\n"

    prob = cfg.get("range_prob", 0.85)
    monotonic = cfg.get("monotonic", {})     # path -> [lo, hi]: each value is the previous plus a step
    clock = {path: 0 for path in monotonic}

    consts = cfg.get("const_inputs", {})
    in_domains = cfg.get("input_domains", {})   # path -> [lo, hi]: every value (what the boundary can return)
    unit_inputs = cfg.get("unit_inputs", {})    # struct input -> probability that its leaves are a unit vector
    rotation_inputs = cfg.get("rotation_inputs", {})   # Matrix3 input -> probability of a rotation matrix (rows a, b, c)

    def inputs_tokens():
        toks = [rand_arg(rng, i["type"], "@" + i["path"], ranges, sig, prob=prob) for i in ins]
        for k, i in enumerate(ins):
            if i["path"] in in_domains:
                lo, hi = in_domains[i["path"]]
                if i["type"] in ("float", "double"):
                    toks[k] = fmt_value(i["type"], (f32_bits if i["type"] == "float" else f64_bits)(rng.uniform(lo, hi)))
                else:
                    toks[k] = str(rng.randint(int(lo), int(hi)))
        for pre_, prob_ in sorted(unit_inputs.items()):
            ks = [k for k, i in enumerate(ins) if i["path"].startswith(pre_ + ".")]
            if rng.random() < prob_:
                for k, v in zip(ks, unit_vector(rng, len(ks))):
                    toks[k] = v
        for pre_, prob_ in sorted(rotation_inputs.items()):
            ks = [k for k, i in enumerate(ins) if i["path"].startswith(pre_ + ".")]
            if rng.random() < prob_:
                for k, v in zip(ks, rotation_matrix(rng)):
                    toks[k] = v
        for k, i in enumerate(ins):
            if i["path"] in consts:
                toks[k] = str(consts[i["path"]])
        for k, i in enumerate(ins):
            if i["path"] in monotonic:
                lo, hi = monotonic[i["path"]]
                clock[i["path"]] += rng.randint(lo, hi)
                toks[k] = str(clock[i["path"]] % (1 << 32))
        return alias(toks)

    def alias(toks):
        for k, path in enumerate(paths):
            if path in aliases:
                toks[k] = toks[paths.index(aliases[path])]
        return toks

    domains = cfg.get("domains", {})          # "Class.method.param" or "param" -> [lo, hi]: every value

    def domain(m, nm):
        if nm.startswith("%"):          # a leaf of a struct parameter: its own domain, else the parameter's
            d = domain(m, nm[1:])
            return d if d is not None or "." not in nm else domain(m, nm[1:].split(".")[0])
        return domains.get("%s.%s" % (m["lean"].split(".", 1)[1], nm), domains.get(nm))

    def rand_args(m):
        out = []
        for p in m["params"]:
            d = domain(m, p["name"])
            if d is not None and p["scalar"]:
                if p["type"] in ("float", "double"):
                    tobits = f32_bits if p["type"] == "float" else f64_bits
                    out.append(fmt_value(p["type"], tobits(rng.uniform(d[0], d[1]))))
                else:
                    out.append(str(rng.randint(int(d[0]), int(d[1]))))
                continue
            toks = [rand_arg(rng, t, nm, ranges, sig, en, prob=prob) for t, nm, en in slots_of_param(p)]
            if p["name"] in unit_args and p.get("leaves") and not p["scalar"] and rng.random() < unit_args[p["name"]]:
                toks = unit_vector(rng, len(toks))
            out += toks
        return out

    def state_tokens():
        toks = [rand_arg(rng, lf["type"], lf["lean"], ranges, sig, lf["enum"], prob=prob) for lf in sleaves]
        if unit_state and rng.random() < unit_state.get("prob", 0.5):
            names = unit_state["leaves"]
            vals = unit_vector(rng, len(names))
            for nm, v in zip(names, vals):
                toks[[lf["lean"] for lf in sleaves].index(nm)] = v
        return toks

    out = []
    keys = {m["lean"].split(".", 1)[1]: m for m in methods}
    for st in cfg.get("setup", []):         # calls that put the object in the state under test
        parts = st.split()
        if parts[0] not in keys:
            raise SystemExit("difftest: setup call `%s` is not a driven member function" % st)
        out.append(" ".join(parts) + " " + " ".join(inputs_tokens() + state_tokens()) + "\n")
    nsetup = len(out)
    for _ in range(ncalls):
        m = rng.choices(chosen, weights)[0]
        out.append(line(m, rand_args(m) + inputs_tokens() + state_tokens()))
    corner_count = nsetup
    for m in chosen:
        slots = [x for p in m["params"] for x in slots_of_param(p)]
        for k, (t, nm, en) in enumerate(slots):
            for c in corner_tokens(t, sig, en):
                d = domain(m, nm)
                if d is not None and not d[0] <= token_value(t, c) <= d[1]:
                    continue                    # outside the domain: undefined behavior in the C++
                args = rand_args(m)
                args[k] = c
                out.append(line(m, args + inputs_tokens() + state_tokens()))
                corner_count += 1
        for k, i in enumerate(ins):
            if cfg.get("input_corners") == "readers" and not m["uses_inp"]:
                break                           # corner inputs only where the call reads the boundary
            for c in corner_tokens(i["type"], sig):
                args = rand_args(m)
                if i["path"] in aliases or i["path"] in consts:
                    continue
                if i["path"] in in_domains and not in_domains[i["path"]][0] <= token_value(i["type"], c) <= in_domains[i["path"]][1]:
                    continue                    # a value the boundary object cannot return
                toks = inputs_tokens()
                toks[k] = c
                out.append(line(m, args + alias(toks) + state_tokens()))
                corner_count += 1
        for k, lf in enumerate(sleaves):
            for c in corner_tokens(lf["type"], sig, lf["enum"]):
                args = rand_args(m)
                st = state_tokens()
                st[k] = c
                out.append(line(m, args + inputs_tokens() + st))
                corner_count += 1
    return "".join(out), ncalls, corner_count, methods


def cpp_value_text(ptype, v, enum_cxx=None):
    if enum_cxx is not None:
        return v
    if ptype == "float":
        return v + "f"
    if ptype == "bool":
        return v
    return v


def cpp_token_print(ctype, expr, enum=False):
    if enum:
        return "ti((long long)(%s));" % expr
    if ctype == "const char *":
        return "tstr(%s);" % expr
    if ctype == "float":
        return "tf(%s);" % expr
    if ctype == "double":
        return "td(%s);" % expr
    if ctype == "bool":
        return "tb(%s);" % expr
    if INTS[ctype][1]:
        return "ti((long long)(%s));" % expr
    return "tu((unsigned long long)(%s));" % expr


def cpp_read(ptype, tok, enum_cxx=None):
    if enum_cxx is not None:
        return "static_cast<%s>(strtoll(%s, nullptr, 10))" % (enum_cxx, tok)
    if ptype == "float":
        return "in_f32(%s)" % tok
    if ptype == "double":
        return "in_f64(%s)" % tok
    if ptype == "bool":
        return "(atoi(%s) != 0)" % tok
    if INTS[ptype][1]:
        return "(%s)strtoll(%s, nullptr, 10)" % (ptype, tok)
    return "(%s)strtoull(%s, nullptr, 10)" % (ptype, tok)


def top_ctor(cls, cfg):
    want = len(cfg.get("ctor", []))
    for m in cls["methods"]:
        if m["kind"] == "ctor" and m["top"] and len([p for p in m["params"] if not p["boundary"]]) == want:
            return m
    if want == 0:
        return None
    raise SystemExit("difftest: no constructor of %s with %d arguments" % (cls["cxx"], want))


def cpp_class_driver(example, sig, cls, cfg, methods, free=False):
    ctor = None if free else top_ctor(cls, cfg)
    lines = ["// Generated by cpp2lean/difftest.py: the C++ side of the class differential test for `%s`." % cls["cxx"],
             "// Reads input lines (README.md, \"Differential test\"), calls the member function each names on one",
             "// persistent object, prints the result, the reference parameters and every state leaf after the call.",
             "#include <cfloat>", "#include <cinttypes>", "#include <cmath>", "#include <cstddef>", "#include <cstdint>",
             "#include <cstdio>", "#include <cstdlib>", "#include <cstring>"] + cfg.get("cxx_prelude", []) + [
             "#define private public   // the driver reads every data member",
             "#define protected public",
             ] + ["#include %s" % x for x in ([cfg["cxx_include"]] if isinstance(cfg.get("cxx_include"), str) else cfg.get("cxx_include", ["\"%s.cpp\"" % example]))] + [
             "#undef private", "#undef protected", ""] + ([
             "// config \"quiet_console\": the library's console messages (`::printf` under SITL, SCurve.cpp:217)",
             "// go to /dev/null; the driver prints its lines to the original standard output",
             "#include <fcntl.h>", "#include <unistd.h>",
             "static FILE *cpp2lean_out;", "#define printf(...) fprintf(cpp2lean_out, __VA_ARGS__)", ""] if cfg.get("quiet_console") else []) + [
             "static float in_f32(const char *s) { uint32_t u = (uint32_t)strtoul(s, nullptr, 16); if ((u & 0x7f800000u) == 0x7f800000u && (u & 0x7fffffu)) u |= 0x400000u; float f; memcpy(&f, &u, 4); return f; }",
             "static double in_f64(const char *s) { uint64_t u = strtoull(s, nullptr, 16); if ((u & 0x7ff0000000000000ull) == 0x7ff0000000000000ull && (u & 0xfffffffffffffull)) u |= 0x8000000000000ull; double d; memcpy(&d, &u, 8); return d; }",
             "static void tf(float f) { uint32_t u; memcpy(&u, &f, 4); printf(\" f:%08x\", u); }",
             "static void td(double d) { uint64_t u; memcpy(&u, &d, 8); printf(\" d:%016llx\", (unsigned long long)u); }",
             "static void tb(bool b) { printf(\" b:%d\", b ? 1 : 0); }",
             "static void ti(long long v) { printf(\" i:%lld\", v); }",
             "static void tu(unsigned long long v) { printf(\" i:%llu\", v); }",
             "static void tstr(const char *x) { printf(\" s:\"); for (; *x; x++) printf(\"%02x\", (unsigned char)*x); }", ""]
    lines += cfg.get("globals", [])
    args = []
    if ctor is not None:
        vals = list(cfg.get("ctor", []))
        bargs = list(cfg.get("boundary_args", []))
        for p in ctor["params"]:
            if p["boundary"]:
                args.append(bargs.pop(0))
            else:
                v = str(vals.pop(0))
                args.append(cpp_value_text(p["type"], v, p["enum"]))
    if not free:
        lines.append("static %s obj%s;   // static storage: zero-filled before construction, as ArduPilot's objects" %
                     (cfg.get("cxx_class", cls["cxx"]), "(%s)" % ", ".join(args) if args else ""))
    lines.append("")
    lines.append("static void dump() {")
    for lf in cls["leaves"]:
        lines.append("    " + cpp_token_print(lf["type"], "obj." + lf["cxx"], lf["enum"] is not None))
    if cls.get("output_log"):
        # the boundary calls of this call, in order, as the environment recorded them (cxx_env)
        lines.append("    printf(\"%s\", cpp2lean_events.c_str()); cpp2lean_events.clear();")
    for fo in flat_outputs(sig, cls):       # what the boundary object received (config "outputs")
        if fo["path"] not in cfg.get("outputs", {}):
            raise SystemExit("difftest: no C++ expression for output `%s` of %s (config \"outputs\")" % (fo["path"], cls["cxx"]))
        lines.append("    " + cpp_token_print(fo["type"], cfg["outputs"][fo["path"]]))
    lines.append("}")
    lines.append("")
    overrides = []
    for path, v in cfg.get("params", {}).items():     # parameters set after construction, on both sides
        lf = next((x for x in cls["leaves"] if x["root"] == "p" and x["lean"] == path), None)
        if lf is None:
            raise SystemExit("difftest: no parameter `%s` in %s" % (path, cls["cxx"]))
        overrides.append("    obj.%s.set(%s);" % (lf["cxx"][:-len(".get()")], v + ("f" if lf["type"] == "float" and "." in v else "")))
    quiet = ["    cpp2lean_out = fdopen(dup(1), \"w\");", "    dup2(open(\"/dev/null\", O_WRONLY), 1);"] if cfg.get("quiet_console") else []
    lines += ["int main() {", "    char buf[4096];", "    long line = 0;"] + quiet + overrides + [
              "    printf(\"0 init\"); dump(); printf(\"\\n\");",
              "    while (fgets(buf, sizeof buf, stdin)) {", "        line++;", "        char *tok[64];", "        int nt = 0;",
              "        for (char *p = strtok(buf, \" \\n\"); p && nt < 64; p = strtok(nullptr, \" \\n\")) tok[nt++] = p;",
              "        printf(\"%ld %s\", line, tok[0]);"]
    first = True
    for m in methods:
        key = m["lean"].split(".", 1)[1]
        lines.append("        %sif (!strcmp(tok[0], \"%s\")) {" % ("" if first else "} else ", key))
        first = False
        k = 1
        names = []
        for i, p in enumerate(m["params"]):
            names.append("a%d" % i)
            if not p["scalar"]:                 # a struct or class value: default-constructed, then each leaf
                lines.append("            %s a%d;" % (p["type"], i))
                for lf in p["leaves"]:
                    ecx = enum_info(sig, lf["enum"])["cxx"] if lf.get("enum") else None
                    lines.append("            a%d.%s = %s;" % (i, lf["cxx"], cpp_read(lf["type"], "tok[%d]" % k, ecx)))
                    k += 1
                continue
            enum_cxx = enum_info(sig, p["enum"])["cxx"] if p["enum"] else None
            ty = enum_cxx or p["type"]
            lines.append("            %s a%d = %s;" % (ty, i, cpp_read(p["type"], "tok[%d]" % k, enum_cxx)))
            k += 1
        fins = flat_inputs(sig, cls)
        for j, inp in enumerate(fins):
            if inp["path"] in cfg.get("input_aliases", {}) or inp["path"] in cfg.get("const_inputs", {}):
                continue                        # the same C++ object as the aliased input; a constant input
            tmpl = cfg["inputs"][inp["path"]]
            lines.append("            " + tmpl.replace("%s", cpp_read(inp["type"], "tok[%d]" % (k + j))))
        k += len(fins)
        for lf in state_leaves(cls, cfg):       # the object's state, from the line
            lines.append("            obj.%s = %s;" % (lf["cxx"], cpp_read(lf["type"], "tok[%d]" % k)))
            k += 1
        if free:
            call = "%s(%s)" % (m["cxx_call"], ", ".join(names))
        elif m.get("via"):
            call = "obj.%s.%s(%s)" % (m["via"], m["cxx"], ", ".join(names))     # a method of a member object
        else:
            call = "obj.%s(%s)" % (cpp_call_name(cls, m), ", ".join(names))
        if m["ret"] == "void":
            lines.append("            %s;" % call)
        elif m["ret"] == "const char *":
            lines.append("            const char *r = %s;" % call)
            lines.append("            tstr(r);")
        elif not m["ret_scalar"]:
            lines.append("            %s r = %s;" % (m["ret"], call))
            for lf in m["ret_leaves"]:
                lines.append("            " + cpp_token_print(lf["type"], "r." + lf["cxx"]))
        else:
            rt = enum_info(sig, m["ret_enum"])["cxx"] if m["ret_enum"] else m["ret"]
            lines.append("            %s r = %s;" % (rt, call))
            lines.append("            " + cpp_token_print(m["ret_under"] or m["ret"], "r", m["ret_enum"] is not None))
        for i, p in enumerate(m["params"]):
            if p["ref"] == "mut" and not p["scalar"]:
                for lf in p["leaves"]:
                    lines.append("            " + cpp_token_print(lf["type"], "a%d.%s" % (i, lf["cxx"])))
            elif p["ref"] == "mut":
                lines.append("            " + cpp_token_print(p["under"] or p["type"], "a%d" % i, p["enum"] is not None))
        for stmt in cfg.get("after_call_for", {}).get(m["lean"].split(".", 1)[1], []):
            lines.append("            " + stmt)
        for stmt in cfg.get("after_call", []):
            lines.append("            " + stmt)
    lines += ["        } else { printf(\" ?\"); }", "        printf(\" |\"); dump(); printf(\"\\n\");", "    }", "    return 0;", "}", ""]
    # the init line has no `|`: make it uniform
    lines = [l.replace('printf("0 init"); dump();', 'printf("0 init |"); dump();') for l in lines]
    return "\n".join(lines)


def lean_tok(ctype, expr, enum=None):
    if enum is not None:
        return "tI (toString (%s.toInt (%s)))" % (enum, expr)
    if ctype == "const char *":
        return "tS (%s)" % expr
    if ctype == "float":
        return "tF32 (%s)" % expr
    if ctype == "double":
        return "tF64 (%s)" % expr
    if ctype == "bool":
        return "tB (%s)" % expr
    return "tI (toString (%s))" % expr


def lean_read(ptype, tok, sig, enum=None):
    if enum is not None:
        return "enumOf_%s (inInt %s)" % (enum.replace(".", "_"), tok)
    return lean_in(ptype, tok)


def lean_class_driver(sig, cls, cfg, methods, tag, free=False):
    L = cls["lean"]
    hp = cls["has_params"]
    ctor = None if free else top_ctor(cls, cfg)
    out = []
    used_enums = set()
    for m in methods:
        for p in m["params"]:
            if p["enum"]:
                used_enums.add(p["enum"])
            if not p["scalar"]:
                used_enums |= {lf["enum"] for lf in p.get("leaves") or [] if lf.get("enum")}
    if ctor is not None:
        for p in ctor["params"]:
            if p["enum"]:
                used_enums.add(p["enum"])
    for en in sorted(used_enums - EMITTED_ENUMOF):
        EMITTED_ENUMOF.add(en)              # one definition per enum across the class runs
        e = enum_info(sig, en)
        out.append("def enumOf_%s (v : Int) : %s :=" % (en.replace(".", "_"), en))
        for i, (nm, v, ln) in enumerate(e["values"]):
            out.append("  %sif v == %d then %s.%s" % ("" if i == 0 else "else ", v, en, ln))
        out.append("  else default")
        out.append("")
    log = bool(cls.get("output_log"))
    ho = bool(flat_outputs(sig, cls)) or log
    OT = (sig["output_ns"] + "Outputs") if log else "%s.Outputs" % L
    ps = "(p : %s.Params) " % L if hp else ""
    os_ = " (ob : %s)" % OT if ho else ""
    ob = " ob" if ho else ""
    if log:
        out += lean_output_tokens(sig, tag)
    out.append("def dump%s %s(s : %s.State)%s : String :=" % (tag, ps, L, os_))
    toks = []
    for lf in cls["leaves"]:
        toks.append(lean_tok(lf["type"], "%s.%s" % (lf["root"], lf["lean"]), lf["enum"]))
    for fo in flat_outputs(sig, cls):
        # config "lean_outputs": what the boundary object stores of the value it received, when the
        # C++ side prints a stored value that is a function of the argument (a Lean expression, %s
        # the value)
        toks.append(lean_tok(fo["type"], cfg.get("lean_outputs", {}).get(fo["path"], "%s") % ("ob.%s" % fo["path"])))
    if log:
        toks.append("ob.foldl (fun acc e => acc ++ outTok%s e) \"\"" % tag)
    out.append("  \"\"" + "".join(" ++ " + t for t in toks))
    out.append("")
    out.append("partial def loop%s (h : IO.FS.Stream) (out : IO.FS.Stream) %s(s : %s.State)%s (n : Nat) : IO Unit := do" % (tag, ps, L, os_))
    out.append("  let line ← h.getLine")
    out.append("  if line.isEmpty then return")
    out.append("  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray")
    if hp:
        out.append("  let mut p := p")
    out.append("  let mut s := s")
    if ho:
        out.append("  let mut ob := ob")
    out.append("  let mut o := toString (n + 1) ++ \" \" ++ t[0]!")
    out.append("  match t[0]! with")
    for m in methods:
        key = m["lean"].split(".", 1)[1]
        out.append("  | \"%s\" =>" % key)
        k = 1
        args = []
        via = m.get("via")                  # a method of the member object `via`: its own components
        sp = (lambda x: "%s.%s" % (x, via)) if via else (lambda x: x)
        if "p" in m["reads"] + m["writes"]:
            args.append(sp("p"))
        if "s" in m["reads"] + m["writes"]:
            args.append(sp("s"))
        if "o" in m["writes"] or "olive" in m["reads"]:
            args.append("ob")           # the log so far (empty at the start of the call): written, or read by live inputs
        for i, p in enumerate(m["params"]):
            if not p["scalar"]:
                fins = [{"path": lf["lean"], "type": lf["type"], "enum": lf.get("enum")} for lf in p["leaves"]]
                out.append("    let a%d : %s := %s" % (i, p["lean_type"], lean_inputs_record(fins, k)))
                k += len(fins)
                continue
            ptype = p["type"]
            lt = p["enum"] if p["enum"] else lean_type(ptype)
            out.append("    let a%d : %s := %s" % (i, lt, lean_read(ptype, "t[%d]!" % k, sig, p["enum"])))
            k += 1
        if m["uses_inp"]:
            out.append("    let inp : %s.Inputs := %s" % (L, lean_inputs_record(flat_inputs(sig, cls), k)))
            args.append(sp("inp"))
        if m.get("uses_own"):
            args.append("(%s.owner_%s p s)" % (L, via))
        sl = state_leaves(cls, cfg)
        if sl:
            k2 = k + len(flat_inputs(sig, cls))
            out.append("    s := %s" % lean_inputs_record([{"path": lf["lean"], "type": lf["type"]} for lf in sl], k2))
        args += ["a%d" % i for i in range(len(m["params"]))]
        comps = []
        if "p" in m["writes"]:
            comps.append("p")
        if "s" in m["writes"]:
            comps.append("s")
        if "o" in m["writes"]:
            comps.append("ob")
        outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
        comps += ["o%d" % i for i in outs]
        if m["ret"] != "void":
            comps.append("r")
        names = ["c%d" % i for i in range(len(comps))]
        call = "%s %s" % (m["lean"], " ".join(args))
        if len(comps) == 1:
            out.append("    let %s := %s" % (names[0], call))
        else:
            out.append("    let (%s) := %s" % (", ".join(names), call))
        for c, nm in zip(comps, names):
            if c in ("p", "s") and via:
                out.append("    %s := { %s with %s := %s }" % (c, c, via, nm))
            elif c == "p":
                out.append("    p := %s" % nm)
            elif c == "s":
                out.append("    s := %s" % nm)
            elif c == "ob":
                out.append("    ob := %s" % nm)
        rtoks = []
        if m["ret"] == "const char *":
            rtoks.append(lean_tok(m["ret"], names[comps.index("r")]))
        elif m["ret"] != "void" and not m["ret_scalar"]:
            rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("r")], lf["lean"])) for lf in m["ret_leaves"]]
        elif m["ret"] != "void":
            rtoks.append(lean_tok(m["ret_under"] or m["ret"], names[comps.index("r")], m["ret_enum"]))
        for i in outs:
            p = m["params"][i]
            if not p["scalar"]:
                rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("o%d" % i)], lf["lean"])) for lf in p["leaves"]]
            else:
                rtoks.append(lean_tok(p["under"] or p["type"], names[comps.index("o%d" % i)], p["enum"]))
        if rtoks:
            out.append("    o := o ++ " + " ++ ".join(rtoks))
    out.append("  | _ => o := o ++ \" ?\"")
    out.append("  out.putStr (o ++ \" |\" ++ dump%s %ss%s ++ \"\\n\")" % (tag, "p " if hp else "", ob))
    out.append("  loop%s h out %ss%s (n + 1)" % (tag, "p " if hp else "", " #[]" if log else ob))
    out.append("")
    out.append("def run%s : IO Unit := do" % tag)
    cargs = []
    if ctor is not None:
        vals = list(cfg.get("ctor", []))
        for p in ctor["params"]:
            if p["boundary"]:
                continue
            v = str(vals.pop(0))
            if p["enum"]:
                cargs.append(v.replace("::", "."))
            elif p["type"] in ("float", "double"):
                cargs.append("(%s : %s)" % (v, lean_type(p["type"])))
            elif p["type"] == "bool":
                cargs.append(v)
            else:
                cargs.append("(%s : %s)" % (v, lean_type(p["type"])))
        if ctor.get("uses_inp"):
            # what the constructor reads from the boundary: the environment's static storage before
            # construction (zero), as the C++ object is constructed before main
            cargs.insert(0, "({} : %s.Inputs)" % L)
        init = "%s %s" % (ctor["lean"], " ".join(cargs))
    else:
        init = None
    if hp:
        out.append("  let (p, s) := %s" % (init or "(({} : %s.Params), ({} : %s.State))" % (L, L)))
    else:
        out.append("  let s : %s.State := %s" % (L, init or "{}"))
    for path, v in cfg.get("params", {}).items():     # parameters set after construction, on both sides
        lf = next(x for x in cls["leaves"] if x["root"] == "p" and x["lean"] == path)
        out.append("  let p := { p with %s := (%s : %s) }" % (path, v, lean_type(lf["type"])))
    out.append("  let out ← IO.getStdout")
    if log:
        out.append("  let ob : %s := #[]   -- no boundary calls yet" % OT)
    elif ho:
        out.append("  let ob : %s.Outputs := {}   -- the boundary object's static storage: zero" % L)
    out.append("  out.putStr (\"0 init |\" ++ dump%s %ss%s ++ \"\\n\")" % (tag, "p " if hp else "", ob))
    out.append("  loop%s (← IO.getStdin) out %ss%s 0" % (tag, "p " if hp else "", ob))
    out.append("")
    return out


def lean_call_lines(sig, cls, cfg, m, k, out, objargs):
    """Lines of the Lean driver that read the arguments of m from tokens k.., call it, and append
    its result and reference parameters to `o`. objargs: the leading p/s/ob/inp arguments."""
    args = list(objargs)
    for i, p in enumerate(m["params"]):
        if not p["scalar"]:
            fins = [{"path": lf["lean"], "type": lf["type"]} for lf in p["leaves"]]
            out.append("    let a%d : %s := %s" % (i, p["lean_type"], lean_inputs_record(fins, k)))
            k += len(fins)
            continue
        ptype = p["type"]
        lt = p["enum"] if p["enum"] else lean_type(ptype)
        out.append("    let a%d : %s := %s" % (i, lt, lean_read(ptype, "t[%d]!" % k, sig, p["enum"])))
        k += 1
    args += ["a%d" % i for i in range(len(m["params"]))]
    return args, k


def lean_output_tokens(sig, tag):
    """`outTok<tag> : Output → String`: the tokens of one boundary call, as the C++ environment
    prints them (` e:<name>` and the typed arguments)."""
    ns = sig["output_ns"]
    out = ["def outTok%s : %sOutput → String" % (tag, ns)]
    for ev in sig["output_log"]:
        names = ["a%d" % i for i in range(len(ev["args"]))]
        toks = ["\" e:%s\"" % ev["name"]]
        for a, nm in zip(ev["args"], names):
            if a.get("leaves"):         # a struct argument (`set_pos_vel_accel_NED_m(const Vector3p &, ...)`): its leaves
                toks += [lean_tok(lf["type"], "%s.%s" % (nm, lf["lean"]), lf.get("enum")) for lf in a["leaves"]]
            else:
                toks.append(lean_tok(a["type"], nm, a["enum"]))
        out.append("  | .%s%s => %s" % (ev["name"], "".join(" " + n for n in names), " ++ ".join(toks)))
    out.append("")
    return out


def lean_free_driver(sig, cfg, methods, tag):
    """The Lean side of the free-function harness: each line names a function and its arguments;
    the result and the reference parameters after the call are printed as typed tokens."""
    out = []
    out.append("partial def loop%s (h : IO.FS.Stream) (out : IO.FS.Stream) (n : Nat) : IO Unit := do" % tag)
    out.append("  let line ← h.getLine")
    out.append("  if line.isEmpty then return")
    out.append("  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray")
    out.append("  let mut o := toString (n + 1) ++ \" \" ++ t[0]!")
    out.append("  match t[0]! with")
    for m in methods:
        key = m["lean"].split(".", 1)[1]
        out.append("  | \"%s\" =>" % key)
        args, _ = lean_call_lines(sig, None, cfg, m, 1, out, [])
        outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
        comps = ["o%d" % i for i in outs] + (["r"] if m["ret"] != "void" else [])
        names = ["c%d" % i for i in range(len(comps))]
        call = "%s %s" % (m["lean"], " ".join(args))
        out.append("    let %s := %s" % (names[0] if len(comps) == 1 else "(%s)" % ", ".join(names), call))
        rtoks = []
        if m["ret"] != "void" and not m["ret_scalar"]:
            rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("r")], lf["lean"])) for lf in m["ret_leaves"]]
        elif m["ret"] != "void":
            rtoks.append(lean_tok(m["ret_under"] or m["ret"], names[comps.index("r")], m["ret_enum"]))
        for i in outs:
            p = m["params"][i]
            if not p["scalar"]:
                rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("o%d" % i)], lf["lean"])) for lf in p["leaves"]]
            else:
                rtoks.append(lean_tok(p["under"] or p["type"], names[comps.index("o%d" % i)], p["enum"]))
        out.append("    o := o ++ " + (" ++ ".join(rtoks) if rtoks else "\"\""))
    out.append("  | _ => o := o ++ \" ?\"")
    out.append("  out.putStr (o ++ \" |\" ++ \"\\n\")")
    out.append("  loop%s h out (n + 1)" % tag)
    out.append("")
    out.append("def run%s : IO Unit := do" % tag)
    out.append("  let out ← IO.getStdout")
    out.append("  out.putStr \"0 init |\\n\"")
    out.append("  loop%s (← IO.getStdin) out 0" % tag)
    out.append("")
    return out


def drivable_free(f):
    if f.get("file_static"):              # a static function of a .cpp: not callable from a driver
        return False
    if any(p["ref"] == "ptr" for p in f["params"]):
        return False                        # a nullable out-pointer parameter (not driven)
    if not all((p["scalar"] or simple_leaves(p.get("leaves"))) and not p["boundary"] for p in f["params"]):
        return False
    return f["ret"] == "void" or f["ret_scalar"] or simple_leaves(f.get("ret_leaves"))


def compare_tokens(cpp_out, lean_out):
    a, b = cpp_out.splitlines(), lean_out.splitlines()
    diffs, nan_only = [], {}
    for i in range(max(len(a), len(b))):
        x = a[i].split() if i < len(a) else []
        y = b[i].split() if i < len(b) else []
        same = len(x) == len(y)
        if same:
            for tx, ty in zip(x, y):
                if tx == ty:
                    continue
                if tx[:2] in ("f:", "d:") and ty[:2] == tx[:2] and is_nan_hex(tx[2:]) and is_nan_hex(ty[2:]):
                    key = (tx[2:], ty[2:])
                    nan_only[key] = nan_only.get(key, 0) + 1
                    continue
                same = False
                break
        if not same:
            diffs.append((i, a[i] if i < len(a) else "<missing>", b[i] if i < len(b) else "<missing>"))
    return diffs, nan_only, max(len(a), len(b))


# ---------------------------------------------------------------------------------------------

def is_nan_hex(h):
    if len(h) == 8:
        u = int(h, 16)
        return (u >> 23) & 0xff == 0xff and u & 0x7fffff != 0
    u = int(h, 16)
    return (u >> 52) & 0x7ff == 0x7ff and u & ((1 << 52) - 1) != 0


def compare(cpp_out, lean_out, rets):
    a, b = cpp_out.splitlines(), lean_out.splitlines()
    diffs, nan_only = [], {}
    for i in range(max(len(a), len(b))):
        x = a[i].split() if i < len(a) else []
        y = b[i].split() if i < len(b) else []
        if len(x) < 3 or len(y) < 3 or x[:2] != y[:2]:
            diffs.append((i, a[i] if i < len(a) else "<missing>", b[i] if i < len(b) else "<missing>"))
            continue
        if rets[i % len(rets)] in ("float", "double"):
            if x[2] == y[2]:
                continue
            if is_nan_hex(x[2]) and is_nan_hex(y[2]):
                key = (x[2], y[2])
                nan_only[key] = nan_only.get(key, 0) + 1
                continue
        elif x[2] == y[2]:
            continue
        diffs.append((i, a[i], b[i]))
    return diffs, nan_only, max(len(a), len(b))


def update_lakefile_roots(namespaces):
    """Keep the `roots` of the `Translated` library in lean/lakefile.toml in step with the
    translated modules: the existing roots whose .lean file is present, in their order, then the
    namespaces translated in this run that are not listed yet; CppLibm is always kept (written
    here if no translation wrote it)."""
    path = os.path.join(DEMO, "lakefile.toml")
    with open(path) as f:
        text = f.read()
    m = re.search(r'^roots = \[(.*)\]$', text, re.M)
    if not m:
        sys.exit("difftest: no `roots = [...]` line in %s" % path)
    old = re.findall(r'"([^"]+)"', m.group(1))
    roots = [r for r in old if r == "CppLibm" or os.path.exists(os.path.join(DEMO, r + ".lean"))]
    roots += [ns for ns in namespaces if ns not in roots]
    if "CppLibm" not in roots:
        roots.append("CppLibm")
    if not os.path.exists(os.path.join(DEMO, "CppLibm.lean")):
        with open(os.path.join(DEMO, "CppLibm.lean"), "w") as f:
            f.write(cpp2lean.CPPLIBM)
    line = "roots = [%s]" % ", ".join('"%s"' % r for r in roots)
    if line != m.group(0):
        with open(path, "w") as f:
            f.write(text[:m.start()] + line + text[m.end():])


def run(cmd, **kw):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kw)
    if p.returncode != 0:
        sys.stderr.write(p.stdout.decode() + p.stderr.decode())
        sys.exit("difftest: command failed: %s" % " ".join(cmd))
    return p


AP_DEFAULT = os.path.join(HERE, "ardupilot", "src")


def ardupilot_target(e):
    """An ArduPilot translation (ardupilot/<Name>.json): run its translation script, copy the Lean
    into lean/, compile the C++ sources with the oracle's flags. Returns (namespace, signatures,
    configuration, object files)."""
    with open(os.path.join(HERE, e + ".json")) as f:
        cfg = json.load(f)
    run([os.path.join(HERE, cfg["translate"])], cwd=HERE)
    out = os.path.join(HERE, cfg["out"])
    ns = cfg["namespace"]
    for fn in os.listdir(out):
        if fn.endswith(".lean"):
            with open(os.path.join(out, fn)) as src, open(os.path.join(DEMO, fn), "w") as dst:
                text = src.read()
                if os.environ.get("CPP2LEAN_MUTATE") and fn == ns + ".lean":
                    # harness sensitivity checks (README.md): a JSON list of [regex, replacement]
                    # applied to the translation before it is built, e.g. single-precision trig
                    for pat, rep in json.loads(os.environ["CPP2LEAN_MUTATE"]):
                        text, k = re.subn(pat, rep, text)
                        print("mutation of %s: %d replacements of /%s/" % (fn, k, pat))
                dst.write(text)
    with open(os.path.join(out, ns + ".signatures.json")) as f:
        sig = json.load(f)
    for d in cfg.get("lean_imports", []):    # another translation (its committed output), imported by the driver
        d = os.path.join(HERE, d)
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".lean"):
                with open(os.path.join(d, fn)) as src, open(os.path.join(DEMO, fn), "w") as dst:
                    dst.write(src.read())
                if fn != "CppLibm.lean" and fn[:-5] not in EXTRA_IMPORTS:
                    EXTRA_IMPORTS.append(fn[:-5])
    ap = os.environ.get("AP", AP_DEFAULT)
    lib = os.path.join(ap, "libraries")
    stubs = os.path.realpath(os.path.join(HERE, "ardupilot", "stubs"))
    flags = [x.replace("$STUBS", stubs).replace("$L", lib).replace("$HERE", HERE) for x in cfg["cxx_flags"]] + cpp2lean.CODEGEN_EXTRA
    objdir = os.path.join(BUILD, e.replace("/", "_") + "_obj")
    os.makedirs(objdir, exist_ok=True)
    if cfg.get("cxx_overlay"):
        # a boundary header that a translated file includes from its own directory, replaced by a
        # stand-in for the C++ side (clang's virtual file system overlay; README.md)
        roots = [{"name": os.path.join(lib, k), "type": "file", "external-contents": os.path.join(HERE, v)}
                 for k, v in sorted(cfg["cxx_overlay"].items())]
        ov = os.path.join(objdir, "overlay.json")
        with open(ov, "w") as f:
            json.dump({"version": 0, "case-sensitive": "false", "roots": roots}, f, indent=1)
        flags += ["-ivfsoverlay", ov]
    cfg["cxx_flags"] = flags
    objs = []
    seen = set()
    for src in [os.path.join(lib, x) for x in cfg["cxx_sources"]] + [os.path.join(HERE, x) for x in cfg.get("cxx_env", [])]:
        name = os.path.basename(src).replace(".cpp", ".o")
        if name.lower() in seen:        # AP_Common/Location.cpp and AP_Math/location.cpp on a case-insensitive file system
            name = os.path.basename(os.path.dirname(src)) + "_" + name
        seen.add(name.lower())
        o = os.path.join(objdir, name)
        run([CXX] + flags + ["-c", src, "-o", o])
        objs.append(o)
    return ns, sig, cfg, objs


def load_config(e):
    p = os.path.join(EX, e + ".json")
    if not os.path.exists(p):
        return {}
    with open(p) as f:
        return json.load(f)


def report(label, diffs, nan_only, m, head):
    print("%s: %d of %d lines differ (%d %s equal only as NaN vs NaN with different bits)" %
          (label, len(diffs), m, sum(nan_only.values()), head))
    for (cx, lx), cnt in sorted(nan_only.items(), key=lambda kv: (-kv[1], kv[0])):
        print("  NaN rule: C++ %s, Lean %s: %d %s" % (cx, lx, cnt, head))
    bad = [lx for (cx, lx) in nan_only if lx not in ("7fc00000", "7ff8000000000000")]
    n = len(diffs)
    if bad:
        print("  unexpected: Lean printed a non-canonical NaN: %s" % ", ".join(sorted(set(bad))))
        n += 1
    for i, x, y in diffs[:5]:
        print("  line %d\n    C++:  %s\n    Lean: %s" % (i + 1, x, y))
    return n


def main():
    global N_RANDOM
    import argparse
    ap = argparse.ArgumentParser(description="Differential test of cpp2lean (C++ vs. Lean, bit for bit).")
    ap.add_argument("examples", nargs="*", help="example names (default: every examples/*.cpp)")
    ap.add_argument("--seed", type=int, default=SEED, help="random seed (default %(default)s)")
    ap.add_argument("--random", type=int, default=N_RANDOM, help="random input lines for free functions (default %(default)s)")
    ap.add_argument("--calls", type=int, default=None, help="random calls per class (default: the example's configuration, else 20000)")
    a = ap.parse_args()
    N_RANDOM = a.random
    names = a.examples or sorted(f[:-4] for f in os.listdir(EX) if f.endswith(".cpp") and not f.endswith("_driver.cpp"))
    os.makedirs(BUILD, exist_ok=True)
    examples, class_runs, class_parts = [], [], []
    for e in names:
        if e.startswith("ardupilot/"):
            ns, sig, cfg, objs = ardupilot_target(e)
            funcs = []
        else:
            cfg = load_config(e)
            objs = None
            src = os.path.join("examples", e + ".cpp")
            ns = cfg.get("namespace") or cpp2lean.default_namespace(src)
            run([sys.executable, os.path.join(HERE, "cpp2lean.py"), src, "-o", "lean", "--namespace", ns] + cfg.get("cpp2lean", []), cwd=HERE)
            with open(os.path.join(DEMO, ns + ".signatures.json")) as f:
                sig = json.load(f)
            funcs = sig["functions"]
        slots = slots_of(funcs)
        examples.append((ns, funcs, slots, sig["literals"]))
        if funcs:
            drv = os.path.join(EX, e + "_driver.cpp")
            with open(drv, "w") as f:
                f.write(cpp_driver(e, funcs, slots))
            run([CXX] + cpp2lean.CLANG_FLAGS + cpp2lean.CODEGEN_EXTRA + ["-o", os.path.join(BUILD, e + "_driver"), drv])
        if objs is not None and cfg.get("free"):
            fcfg = dict(cfg["free"])
            fcfg.setdefault("cxx_include", cfg.get("cxx_include", []))
            fcls = {"cxx": "free functions", "lean": ns, "has_params": False, "inputs": [], "sub_inputs": [],
                    "outputs": [], "sub_outputs": [], "methods": [], "leaves": []}
            fmethods = [f for f in sig.get("free", []) if drivable_free(f)]
            ncalls = a.calls if a.calls is not None else fcfg.get("calls", 20000)
            inputs, nrand, ncorner, methods = class_inputs(sig, fcls, fcfg, a.seed, ncalls, fmethods)
            tag = "%s_free" % ns
            base = e.replace("/", "_")
            drv = os.path.join(HERE, "ardupilot", "%s_free_driver.cpp" % os.path.basename(e))
            with open(drv, "w") as f:
                f.write(cpp_class_driver(e, sig, fcls, fcfg, methods, free=True))
            exe = os.path.join(BUILD, "%s_free_driver" % base)
            o = exe + ".o"
            run([CXX] + cfg["cxx_flags"] + ["-c", drv, "-o", o])
            run([CXX, "-o", exe, o] + objs + ["-Wl,-dead_strip"])
            class_parts.append((tag, lean_free_driver(sig, fcfg, methods, tag)))
            class_runs.append((e, sig, fcls, tag, exe, inputs, nrand, ncorner, methods))
        for ccfg in cfg.get("classes", []):
            cls = next(c for c in sig["classes"] if c["cxx"] == ccfg["class"])
            ncalls = a.calls if a.calls is not None else ccfg.get("calls", 20000)
            mlist = [m for m in cls["methods"] if drivable(cls, m, ccfg.get("extra_methods", []), ccfg.get("enum_leaves", False))]
            for mm in ccfg.get("member_methods", []):       # methods of a member object, driven through it
                mc = next(c for c in sig["classes"] if c["cxx"] == mm["class"])
                for m in mc["methods"]:
                    if drivable(mc, m, mm.get("extra_methods", [])) and m["lean"].split(".")[-1] in mm["methods"]:
                        mlist.append(dict(m, via=mm["member"]))
            inputs, nrand, ncorner, methods = class_inputs(sig, cls, ccfg, a.seed, ncalls, mlist)
            tag = "%s_%s" % (ns, cls["lean"].replace(".", "_")) + ("_" + ccfg["run"] if ccfg.get("run") else "")
            base = e.replace("/", "_")
            run_tag = cls["lean"].replace(".", "_") + ("_" + ccfg["run"] if ccfg.get("run") else "")
            drv = os.path.join(HERE, "ardupilot" if objs is not None else "examples", "%s_%s_driver.cpp" % (os.path.basename(e), run_tag))
            with open(drv, "w") as f:
                f.write(cpp_class_driver(e, sig, cls, ccfg, methods))
            exe = os.path.join(BUILD, "%s_%s_driver" % (base, run_tag))
            if objs is None:
                run([CXX] + cpp2lean.CLANG_FLAGS + cpp2lean.CODEGEN_EXTRA + ["-o", exe, drv])
            else:
                o = exe + ".o"
                run([CXX] + cfg["cxx_flags"] + ["-c", drv, "-o", o])
                run([CXX, "-o", exe, o] + objs + ["-Wl,-dead_strip"])
            class_parts.append((tag, lean_class_driver(sig, cls, ccfg, methods, tag)))
            cls = dict(cls, state_from_line=bool(ccfg.get("state_from_line")), run=ccfg.get("run"))
            class_runs.append((e, sig, cls, tag, exe, inputs, nrand, ncorner, methods))
    with open(os.path.join(DEMO, "Main.lean"), "w") as f:
        f.write(lean_driver(examples, class_parts))
    update_lakefile_roots([ns for ns, _, _, _ in examples] + EXTRA_IMPORTS)
    p = run(["lake", "build"], cwd=DEMO)
    if "warning" in (p.stdout + p.stderr).decode():
        sys.stderr.write((p.stdout + p.stderr).decode())
        sys.exit("difftest: lake build printed warnings")
    lean_exe = os.path.join(DEMO, ".lake", "build", "bin", "demo")
    lits = run([lean_exe, "--literals"]).stdout.decode().splitlines()
    bad = [l for l in lits if l.split()[-1] != l.split()[-2]]
    print("literals: %d floating literals; %d elaborate in Lean to bits other than clang's" % (len(lits), len(bad)))
    for l in bad:
        print("  " + l)
    total_diff = len(bad)
    for (ns, funcs, slots, _), e in zip(examples, names):
        if not funcs:
            continue
        inputs, nlines = make_inputs(slots, a.seed)
        with open(os.path.join(BUILD, e + ".in"), "w") as f:
            f.write(inputs)
        c = run([os.path.join(BUILD, e + "_driver")], input=inputs.encode()).stdout.decode()
        l = run([lean_exe, ns], input=inputs.encode()).stdout.decode()
        with open(os.path.join(BUILD, e + ".cpp.out"), "w") as f:
            f.write(c)
        with open(os.path.join(BUILD, e + ".lean.out"), "w") as f:
            f.write(l)
        diffs, nan_only, m = compare(c, l, [f["ret"] for f in funcs])
        print("%s: %d input lines (%d random, %d corner) x %d functions; columns: %s" %
              (e, nlines, N_RANDOM, nlines - N_RANDOM, len(funcs), " ".join("%s#%d" % s for s in slots)))
        total_diff += report(e, diffs, nan_only, m, "lines")
    for e, sig, cls, tag, exe, inputs, nrand, ncorner, methods in class_runs:
        base = os.path.join(BUILD, tag)
        with open(base + ".in", "w") as f:
            f.write(inputs)
        c = run([exe], input=inputs.encode()).stdout.decode()
        l = run([lean_exe, tag], input=inputs.encode()).stdout.decode()
        with open(base + ".cpp.out", "w") as f:
            f.write(c)
        with open(base + ".lean.out", "w") as f:
            f.write(l)
        diffs, nan_only, m = compare_tokens(c, l)
        label = "%s %s" % (e, cls["cxx"]) + (" (%s)" % cls["run"] if cls.get("run") else "")
        if cls["cxx"] == "free functions":
            print("%s: %d calls (%d random, %d corner) over %d functions" % (label, nrand + ncorner, nrand, ncorner, len(methods)))
        else:
            print("%s: %d calls on one object (%d random, %d corner) over %d member functions, %d state leaves per line%s; inputs: %s%s" %
                  (label, nrand + ncorner, nrand, ncorner, len(methods), len(cls["leaves"]),
                   " (set from the line before each call)" if cls.get("state_from_line") else "",
                   ", ".join(i["path"] for i in flat_inputs(sig, cls)) or "none",
                   "; outputs: " + ", ".join(o["path"] for o in flat_outputs(sig, cls)) if flat_outputs(sig, cls) else ""))
        total_diff += report(label, diffs, nan_only, m, "tokens")
    sys.exit(0 if total_diff == 0 else 1)


if __name__ == "__main__":
    main()
