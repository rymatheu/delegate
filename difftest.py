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
     Binary32/Binary64 result is printed as its bit pattern in hex and a decimal, an integer result
     in decimal, a bool as 0/1;
  6. the outputs are compared line by line: function name and the hex bit pattern for floating
     results (the decimals are informational: C prints %.9g/%.17g, Lean its own toString), the
     decimal for integer and bool results.

Signaling NaNs. Both drivers read a signaling NaN input with its quiet bit set (sign and payload
kept), so both sides get the same quiet NaN (a C library's `fmaxf`/`fminf` may treat a signaling NaN
operand differently from a quiet one; C leaves signaling NaNs implementation-defined).

NaN rule. FloatLib's `Binary32`/`Binary64` keep a NaN's sign and payload, but which payload an
operation on NaN operands returns, and how a payload converts between the two formats, are not
fixed by IEEE 754 or C, and FloatLib's choice (IEEE 754-2019 §6.2.3: the payload of an operand,
quieted; across formats the payload as an integer when it fits) differs from arm64's (the first NaN
operand; across formats the payload's high bits). A floating result therefore matches if the hex
fields are equal, or if both are NaN. The number of lines that match only by this rule is reported
separately, grouped by the two patterns. No other relaxation is applied.

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
ARRAY_MAX = 512         # the longest array argument of a driven call (cpp2lean --pointer-params)
LITERAL_CHUNK = 128     # literals per Lean definition of the literal check
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
        return "Binary32"
    if c == "double":
        return "Binary64"
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
(`Binary32.toBits`/`Binary64.toBits`) and FloatLib's `toString` (the shortest decimal), integers in
decimal, bools as 0/1.
-/

open FloatLib.Floats (Binary32 Binary64)

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d

-- a signaling NaN is read with its quiet bit set, as the C++ drivers read it
def inF32 (s : String) : Binary32 :=
  let u := (hexNat s).toUInt32
  Binary32.ofBits (if u &&& 0x7f800000 == 0x7f800000 && u &&& 0x7fffff != 0 then u ||| 0x400000 else u)
def inF64 (s : String) : Binary64 :=
  let u := (hexNat s).toUInt64
  Binary64.ofBits (if u &&& 0x7ff0000000000000 == 0x7ff0000000000000 && u &&& 0xfffffffffffff != 0 then u ||| 0x8000000000000 else u)
def inInt (s : String) : Int := (s.toInt?).getD 0
def inNat (s : String) : Nat := (s.toNat?).getD 0

def outF32 (x : Binary32) : String := " " ++ hex 8 (Binary32.toBits x).toNat ++ " " ++ toString x
def outF64 (x : Binary64) : String := " " ++ hex 16 (Binary64.toBits x).toNat ++ " " ++ toString x
def outB (b : Bool) : String := if b then " 1" else " 0"

-- typed tokens of the class drivers
def tF32 (x : Binary32) : String := " f:" ++ hex 8 (Binary32.toBits x).toNat
def tF64 (x : Binary64) : String := " d:" ++ hex 16 (Binary64.toBits x).toNat
def tB (b : Bool) : String := if b then " b:1" else " b:0"
def tI (x : String) : String := " i:" ++ x
def tS (x : String) : String := " s:" ++ String.join (x.toUTF8.toList.map (fun b => hex 2 b.toNat))
def tP (x : String) : String := " p:" ++ x
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
    rows = []
    for ns, _, _, lits in examples:
        for l in lits:
            hexw = len(l["bits"])
            rows.append("  (%s, \"%s\", hex %d (%s.toBits (%s)).toNat)" % (json.dumps(ns + ":" + l["at"] + " " + l["cpp"]), l["bits"], hexw,
                                                                         "Binary32" if hexw == 8 else "Binary64", l["lean"]))
    if len(rows) <= LITERAL_CHUNK:
        out.append("def literals : List (String × String × String) := [")
        out.append(",\n".join(rows))
        out.append("]")
    else:
        # in chunks: a list literal of thousands of elements exceeds the code generator's recursion depth
        chunks = [rows[i:i + LITERAL_CHUNK] for i in range(0, len(rows), LITERAL_CHUNK)]
        for k, ch in enumerate(chunks):
            out.append("def literals%d : List (String × String × String) := [" % k)
            out.append(",\n".join(ch))
            out.append("]")
            out.append("")
        out.append("def literals : List (String × String × String) := %s" % " ++ ".join("literals%d" % k for k in range(len(chunks))))
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
SUPPORT_MODULES = {"CFloat", "Musl", "CString"}   # written by cpp2lean next to every translation


def is_int_type(t):
    return t in INTS


def has_arrays(m):
    """Does m take a pointer parameter into an array (cpp2lean --pointer-params)? Its input tokens
    are then of variable number: for each array, its length and its elements (config "array_len")."""
    return any(p.get("array_elem") for p in m["params"])


def drivable(cls, m, extra=(), enum_leaves=False, nullable=False):
    if m["kind"] != "method" or (m["access"] != "public" and m["lean"].split(".", 1)[1] not in extra):
        return False
    if any(p["ref"] == "ptr" and not (nullable and p["scalar"]) for p in m["params"]):
        return False                        # a nullable out-pointer parameter (driven only with config "nullable_params")
    if not all((p["scalar"] or simple_leaves(p.get("leaves")) or (enum_leaves and p.get("leaves") and (p["ref"] != "mut" or enum_leaves == "all")))
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
    if p["ref"] == "ptr":       # a nullable out-pointer (config "nullable_params"): whether it is given, its value
        return [("bool", p["name"] + "'given", None), (p["type"], p["name"], p["enum"])]
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


INDEXED_INPUT_LEN = {}      # config "indexed_input_lengths": path of an input array (cpp2lean --ins-gps) -> its length (default 2)


def flat_inputs(sig, cls, prefix=""):
    """The Inputs fields of a class with those of its members' Inputs, as dotted paths; a field of
    a struct or class type (`get_quat_body_to_ned_q : Quaternion.State`) by its scalar leaves; an input
    array (`find_serial_found... : Array Bool`, per value of a call's index) by its elements `path[k]`."""
    out = []
    for i in cls["inputs"]:
        m = re.match(r"^(.*)\[0\]$", i["type"])
        if m and (m.group(1) in SCALARS or m.group(1) in INTS):
            n = INDEXED_INPUT_LEN.get(prefix + i["lean"], 2)
            out += [{"path": "%s%s[%d]" % (prefix, i["lean"], k), "type": m.group(1), "array": prefix + i["lean"]} for k in range(n)]
            continue
        if i.get("leaves") and i["type"] not in SCALARS and i["type"] not in INTS:
            out += [{"path": prefix + i["lean"] + "." + lf["lean"], "type": lf["type"]} for lf in i["leaves"]]
        else:
            out.append({"path": prefix + i["lean"], "type": i["type"]})
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


def lean_inputs_record(fins, first_tok, base=None):
    """Lean structure instance for the flattened Inputs, the k-th field read from token first_tok + k
    (from token `base + first_tok + k` if base, a Lean expression, is given)."""
    tree = {}
    for k, fi in enumerate(fins):
        parts = (fi["array"] if fi.get("array") else fi["path"]).split(".")
        node = tree
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        idx = "%s + %d" % (base, first_tok + k) if base else "%d" % (first_tok + k)
        if fi.get("enum"):
            v = "enumOf_%s (inInt t[%s]!)" % (fi["enum"].replace(".", "_"), idx)
        else:
            v = lean_in(fi["type"], "t[%s]!" % idx)
        if fi.get("array"):
            node.setdefault(parts[-1], []).append(v)     # an input array: its elements in order
            continue
        node[parts[-1]] = v

    def render(node, path):
        items = []
        for k, v in node.items():
            p = path + [k]
            text = render(v, p) if isinstance(v, dict) else "#[%s]" % ", ".join(v) if isinstance(v, list) else v
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

    # config "leaf_domains": a data member (by name) -> [lo, hi], every value it can hold (a one-bit
    # bit-field: [0, 1]), for the state leaves set from the line and the leaves of struct arguments
    sdomains = cfg.get("leaf_domains", {})

    def leaf_domain(nm):
        return sdomains.get(nm.split(".")[-1]) if sdomains else None

    # config "object_ranges" (World runs): per World object, ranges of its member functions'
    # parameters, over the common "ranges"
    oranges = cfg.get("object_ranges", {})

    def mranges(m):
        if not oranges or not m.get("object"):
            return ranges
        return dict(ranges, **oranges.get(m["object"]["name"], {}))

    def rand_args(m, fixed=None, fill=None):
        if has_arrays(m):
            return array_args(m, fixed or {}, fill)
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
            toks = [rand_arg(rng, t, nm, mranges(m), sig, en, prob=prob) for t, nm, en in slots_of_param(p)]
            if sdomains:
                for j, (t, nm, en) in enumerate(slots_of_param(p)):
                    ld = leaf_domain(nm) if nm.startswith("%") else None
                    if ld is not None:
                        toks[j] = str(rng.randint(int(ld[0]), int(ld[1])))
            if p["name"] in unit_args and p.get("leaves") and not p["scalar"] and rng.random() < unit_args[p["name"]]:
                toks = unit_vector(rng, len(toks))
            out += toks
        return out

    def array_args(m, fixed, fill):
        """Tokens of a call with array arguments: each scalar as rand_args draws it (or fixed[i]),
        then each array as its length (config "array_len": `function.param` or `param` -> a Python
        expression over the integer arguments by name) and its elements (random, or all `fill`)."""
        per = []
        for i, p in enumerate(m["params"]):
            if p.get("array_elem"):
                per.append(None)
                continue
            d = domain(m, p["name"])
            if i in fixed:
                per.append([fixed[i]])
            elif d is not None:
                if p["type"] in ("float", "double"):
                    tobits = f32_bits if p["type"] == "float" else f64_bits
                    per.append([fmt_value(p["type"], tobits(rng.uniform(d[0], d[1])))])
                else:
                    per.append([str(rng.randint(int(d[0]), int(d[1])))])
            else:
                per.append([rand_arg(rng, p["type"], p["name"], ranges, sig, p["enum"], prob=prob)])
        env = {p["name"]: token_value(p["type"], per[i][0]) for i, p in enumerate(m["params"])
               if not p.get("array_elem") and p["type"] in INTS}
        lens = cfg.get("array_len", {})
        for i, p in enumerate(m["params"]):
            if not p.get("array_elem"):
                continue
            key = "%s.%s" % (m["lean"].split(".", 1)[1], p["name"])
            if key not in lens and p["name"] not in lens:
                raise SystemExit("difftest: no length for array argument `%s` (config \"array_len\")" % key)
            n = int(eval(lens.get(key, lens.get(p["name"])), {}, dict(env)))
            if not 0 <= n <= ARRAY_MAX:
                raise SystemExit("difftest: array argument `%s` of length %d (at most %d; config \"domains\")" % (key, n, ARRAY_MAX))
            et = p["array_elem"]
            per[i] = [str(n)] + [fill if fill is not None else rand_arg(rng, et, "%" + key if key in ranges else p["name"], ranges, sig, prob=prob)
                               for _ in range(n)]
        return [t for toks in per for t in toks]

    def array_corners(m):
        """Corner lines of a call with array arguments: each corner value of each scalar argument
        (inside its domain), and for each array, every element at one corner value of its type."""
        lines = []
        for i, p in enumerate(m["params"]):
            if p.get("array_elem"):
                for c in corner_tokens(p["array_elem"], sig):
                    lines.append(line(m, rand_args(m, fill=c)))
                continue
            for c in corner_tokens(p["type"], sig, p["enum"]):
                d = domain(m, p["name"])
                if d is not None and not d[0] <= token_value(p["type"], c) <= d[1]:
                    continue
                lines.append(line(m, rand_args(m, fixed={i: c})))
        return lines


    def state_tokens():
        toks = [rand_arg(rng, lf["type"], lf["lean"], ranges, sig, lf["enum"], prob=prob) for lf in sleaves]
        for k, lf in enumerate(sleaves):
            if leaf_domain(lf["lean"]) is not None:
                toks[k] = str(rng.randint(int(leaf_domain(lf["lean"])[0]), int(leaf_domain(lf["lean"])[1])))
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
        if cfg.get("corner_objects") is not None and m.get("object") and m["object"]["name"] not in cfg["corner_objects"]:
            continue                            # (World runs) corner lines only for these objects' member functions
        if has_arrays(m):
            ls = array_corners(m)
            out += ls
            corner_count += len(ls)
            continue
        slots = [x for p in m["params"] for x in slots_of_param(p)]
        for k, (t, nm, en) in enumerate(slots):
            for c in corner_tokens(t, sig, en):
                d = domain(m, nm)
                if d is not None and not d[0] <= token_value(t, c) <= d[1]:
                    continue                    # outside the domain: undefined behavior in the C++
                ld = leaf_domain(nm) if nm.startswith("%") else None
                if ld is not None and not ld[0] <= token_value(t, c) <= ld[1]:
                    continue                    # a value the member cannot hold
                args = rand_args(m)
                args[k] = c
                out.append(line(m, args + inputs_tokens() + state_tokens()))
                corner_count += 1
        for k, i in enumerate(ins):
            if cfg.get("input_corners") in ("readers", "own") and not m["uses_inp"]:
                break                           # corner inputs only where the call reads the boundary
            if cfg.get("input_corners") == "own" and not i["path"].startswith(m["object"]["name"] + "."):
                continue                        # (World runs) only the inputs of the call's own object
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
                if leaf_domain(lf["lean"]) is not None and not leaf_domain(lf["lean"])[0] <= token_value(lf["type"], c) <= leaf_domain(lf["lean"])[1]:
                    continue                    # a value the member cannot hold
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


def is_fun_type(ctype):
    """A functor leaf (cpp2lean --world-pointers: `Functor<void>`, AP_HAL::MemberProc)."""
    return ctype == "Functor<void>"


def is_ptr_type(ctype):
    """A World pointer leaf (cpp2lean --world-pointers): `C *` other than a C string; or (--member-pointers) `C &`,
    a reference member bound to a member object, printed as the object's address."""
    return (ctype.endswith("*") and ctype != "const char *") or ctype.endswith(" &")


def cpp_token_print(ctype, expr, enum=False):
    # (cpp2lean --mission: `x.bytes'[k]`, byte k of the object representation of the union x)
    expr = re.sub(r"^(.*)\.bytes'\[(\d+)\]$", lambda m: "((const unsigned char *)&(%s))[%s]" % (m.group(1), m.group(2)), expr)
    if enum:
        return "ti((long long)(%s));" % expr
    if ctype.endswith(" &"):
        return "tp((const void *)&(%s));" % expr
    if is_ptr_type(ctype):
        return "tp((const void *)(%s));" % expr
    if is_fun_type(ctype):
        return "tfun(%s);" % expr
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
             "#include <cstdio>", "#include <cstdlib>", "#include <cstring>"] + cfg.get("cxx_prelude", []) + ([
             "#define private public   // the driver reads every data member",
             "#define protected public",
             ] if cfg.get("access_control", True) is not False else ["// compiled with -fno-access-control: the driver reads every data member"]) + [
             "#include %s" % x for x in ([cfg["cxx_include"]] if isinstance(cfg.get("cxx_include"), str) else cfg.get("cxx_include", ["\"%s.cpp\"" % example]))] + ([
             "#undef private", "#undef protected", ""] if cfg.get("access_control", True) is not False else [""]) + ([
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
             "static void tstr(const char *x) { if (!x) x = \"\"; printf(\" s:\"); for (; *x; x++) printf(\"%02x\", (unsigned char)*x); }", ""]
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
    big = any(has_arrays(m) for m in methods)       # array arguments: long lines
    lines += ["int main() {", "    static char buf[%d];" % (1 << 16) if big else "    char buf[4096];", "    long line = 0;"] + quiet + overrides + [
              "    printf(\"0 init\"); dump(); printf(\"\\n\");",
              "    while (fgets(buf, sizeof buf, stdin)) {", "        line++;", "        static char *tok[%d];" % (2 * ARRAY_MAX + 64 if big else 64) if big else "        char *tok[64];", "        int nt = 0;",
              "        for (char *p = strtok(buf, \" \\n\"); p && nt < %d; p = strtok(nullptr, \" \\n\")) tok[nt++] = p;" % (2 * ARRAY_MAX + 64 if big else 64),
              "        printf(\"%ld %s\", line, tok[0]);"]
    first = True
    for m in methods:
        key = m["lean"].split(".", 1)[1]
        lines.append("        %sif (!strcmp(tok[0], \"%s\")) {" % ("" if first else "} else ", key))
        first = False
        if has_arrays(m):
            lines += cpp_array_call(m, free)
            continue
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
            if p["ref"] == "ptr":
                # a nullable out-pointer: `&a` if the line's flag is set, else a null pointer
                lines.append("            bool g%d = %s;" % (i, cpp_read("bool", "tok[%d]" % k)))
                k += 1
                names[-1] = "g%d ? &a%d : nullptr" % (i, i)
            lines.append("            %s a%d = %s;" % (ty, i, cpp_read(p["type"], "tok[%d]" % k, enum_cxx)))
            if p.get("by_pointer"):
                names[-1] = "&a%d" % i          # a scalar pointer parameter (cpp2lean --pointer-params)
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
                    lines.append("            " + cpp_token_print(lf["type"], "a%d.%s" % (i, lf["cxx"]), lf.get("enum") is not None))
            elif p["ref"] in ("mut", "ptr"):
                lines.append("            " + cpp_token_print(p["under"] or p["type"], "a%d" % i, p["enum"] is not None))
        for stmt in cfg.get("after_call_for", {}).get(m["lean"].split(".", 1)[1], []):
            lines.append("            " + stmt)
        for stmt in cfg.get("after_call", []):
            lines.append("            " + stmt)
    lines += ["        } else { printf(\" ?\"); }", "        printf(\" |\"); dump(); printf(\"\\n\");", "    }", "    return 0;", "}", ""]
    # the init line has no `|`: make it uniform
    lines = [l.replace('printf("0 init"); dump();', 'printf("0 init |"); dump();') for l in lines]
    return "\n".join(lines)


def cpp_array_call(m, free):
    """C++ driver lines for a free function with array arguments (cpp2lean --pointer-params): the
    tokens are read in order (an array: its length, then its elements, into a static buffer), the
    result is printed, then each scalar reference or pointer parameter, and each array the function
    writes, as its length and its elements."""
    if not free:
        raise SystemExit("difftest: array arguments of member functions are not driven")
    out = ["            int k = 1;"]
    names = []
    for i, p in enumerate(m["params"]):
        if p.get("array_elem"):
            et = p["array_elem"]
            out.append("            static %s a%d[%d]; int n%d = atoi(tok[k++]);" % (et, i, ARRAY_MAX, i))
            out.append("            for (int j = 0; j < n%d; j++) a%d[j] = %s;" % (i, i, cpp_read(et, "tok[k++]")))
            names.append("a%d" % i)
            continue
        out.append("            %s a%d = %s;" % (p["type"], i, cpp_read(p["type"], "tok[k++]")))
        names.append("&a%d" % i if p.get("by_pointer") else "a%d" % i)
    call = "%s(%s)" % (m["cxx_call"], ", ".join(names))
    if m["ret"] == "void":
        out.append("            %s;" % call)
    else:
        out.append("            %s r = %s;" % (m["ret"], call))
        out.append("            " + cpp_token_print(m["ret"], "r"))
    for i, p in enumerate(m["params"]):
        if p["ref"] != "mut":
            continue
        if p.get("array_elem"):
            out.append("            ti(n%d); for (int j = 0; j < n%d; j++) %s" % (i, i, cpp_token_print(p["array_elem"], "a%d[j]" % i)))
        else:
            out.append("            " + cpp_token_print(p["type"], "a%d" % i))
    return out


def lean_array_call(m, out):
    """The Lean side of cpp_array_call: tokens read with a running index `k`; a written array is
    printed as its size (which must be the length passed) and its first elements."""
    out.append("    let mut k : Nat := 1")
    args = []
    for i, p in enumerate(m["params"]):
        if p.get("array_elem"):
            et = p["array_elem"]
            out.append("    let n%d := inNat t[k]!" % i)
            out.append("    let a%d : Array %s := (List.range n%d).toArray.map (fun j => %s)" % (i, lean_type(et), i, lean_in(et, "t[k + 1 + j]!")))
            out.append("    k := k + 1 + n%d" % i)
        else:
            out.append("    let a%d : %s := %s" % (i, lean_type(p["type"]), lean_in(p["type"], "t[k]!")))
            out.append("    k := k + 1")
        args.append("a%d" % i)
    outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
    comps = ["o%d" % i for i in outs] + (["r"] if m["ret"] != "void" else [])
    names = ["c%d" % i for i in range(len(comps))]
    call = "%s %s" % (m["lean"], " ".join(args))
    out.append("    let %s := %s" % (names[0] if len(comps) == 1 else "(%s)" % ", ".join(names), call))
    rtoks = []
    if m["ret"] != "void":
        rtoks.append(lean_tok(m["ret"], names[comps.index("r")]))
    for i in outs:
        p = m["params"][i]
        c = names[comps.index("o%d" % i)]
        if p.get("array_elem"):
            rtoks.append("tI (toString %s.size)" % c)
            rtoks.append("String.join ((List.range n%d).map (fun j => %s))" % (i, lean_tok(p["array_elem"], "%s[j]!" % c)))
        else:
            rtoks.append(lean_tok(p["type"], c))
    out.append("    o := o ++ " + (" ++ ".join(rtoks) if rtoks else "\"\""))


def lean_tok(ctype, expr, enum=None):
    if enum is not None:
        return "tI (toString (%s.toInt (%s)))" % (enum, expr)
    if is_ptr_type(ctype) or is_fun_type(ctype):
        return "tP ((%s).name)" % expr
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
        if "o" in m["writes"]:
            args.append("ob")           # the log so far (empty at the start of the call): written, or read by live inputs
        for i, p in enumerate(m["params"]):
            if not p["scalar"]:
                fins = [{"path": lf["lean"], "type": lf["type"], "enum": lf.get("enum")} for lf in p["leaves"]]
                out.append("    let a%d : %s := %s" % (i, p["lean_type"], lean_inputs_record(fins, k)))
                k += len(fins)
                continue
            ptype = p["type"]
            lt = p["enum"] if p["enum"] else lean_type(ptype)
            if p["ref"] == "ptr":
                out.append("    let g%d : Bool := %s" % (i, lean_read("bool", "t[%d]!" % k, sig)))
                k += 1
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
        args += [("g%d a%d" % (i, i)) if p["ref"] == "ptr" else "a%d" % i for i, p in enumerate(m["params"])]
        comps = []
        if "p" in m["writes"]:
            comps.append("p")
        if "s" in m["writes"]:
            comps.append("s")
        if "o" in m["writes"]:
            comps.append("ob")
        outs = [i for i, p in enumerate(m["params"]) if p["ref"] in ("mut", "ptr")]
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
                rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("o%d" % i)], lf["lean"]), lf.get("enum")) for lf in p["leaves"]]
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


UNLOGGED_OUTPUTS = set()    # config "unlogged_outputs": Output events the C++ environment cannot record (writes to a static struct)


def lean_output_tokens(sig, tag):
    """`outTok<tag> : Output → String`: the tokens of one boundary call, as the C++ environment
    prints them (` e:<name>` and the typed arguments); an event of config "unlogged_outputs" (an
    assignment to a field of a boundary class's static struct, `AP_Notify::flags.gps_status = ...`,
    which the C++ side cannot observe) prints nothing."""
    ns = sig["output_ns"]
    out = ["def outTok%s : %sOutput → String" % (tag, ns)]
    for ev in sig["output_log"]:
        names = ["a%d" % i for i in range(len(ev["args"]))]
        if ev["name"] in UNLOGGED_OUTPUTS:
            out.append("  | .%s%s => \"\"" % (ev["name"], "".join(" _" for _ in names)))
            continue
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
        if has_arrays(m):
            if m.get("hidden"):
                sys.exit("difftest: %s: array arguments and a hidden parameter" % m["lean"])
            lean_array_call(m, out)
            continue
        args, _ = lean_call_lines(sig, None, cfg, m, 1, out, [])
        outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
        hidden = m.get("hidden", [])
        comps = ["o%d" % i for i in outs] + ["h%d" % i for i, p in enumerate(hidden) if p["ref"] == "mut"] + (["r"] if m["ret"] != "void" else [])
        names = ["_" if c.startswith("h") else "c%d" % i for i, c in enumerate(comps)]
        # (a hidden parameter: the HAL storage, zero-filled; Phase 4 --mavlink: a file-scope variable at its
        # initial value, `<ns>.<name>'init`; the test functions set the state they read)
        args = args + [p["hidden"]["init"] if p["hidden"]["kind"] == "global" else "(Array.replicate %d (0 : UInt8))" % p["hidden"]["size"]
                       for p in hidden]
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
                rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("o%d" % i)], lf["lean"]), lf.get("enum")) for lf in p["leaves"]]
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


CPP_PRELUDE = [
    "static float in_f32(const char *s) { uint32_t u = (uint32_t)strtoul(s, nullptr, 16); if ((u & 0x7f800000u) == 0x7f800000u && (u & 0x7fffffu)) u |= 0x400000u; float f; memcpy(&f, &u, 4); return f; }",
    "static double in_f64(const char *s) { uint64_t u = strtoull(s, nullptr, 16); if ((u & 0x7ff0000000000000ull) == 0x7ff0000000000000ull && (u & 0xfffffffffffffull)) u |= 0x8000000000000ull; double d; memcpy(&d, &u, 8); return d; }",
    "static void tf(float f) { uint32_t u; memcpy(&u, &f, 4); printf(\" f:%08x\", u); }",
    "static void td(double d) { uint64_t u; memcpy(&u, &d, 8); printf(\" d:%016llx\", (unsigned long long)u); }",
    "static void tb(bool b) { printf(\" b:%d\", b ? 1 : 0); }",
    "static void ti(long long v) { printf(\" i:%lld\", v); }",
    "static void tu(unsigned long long v) { printf(\" i:%llu\", v); }",
    "static void tstr(const char *x) { if (!x) x = \"\"; printf(\" s:\"); for (; *x; x++) printf(\"%02x\", (unsigned char)*x); }", ""]


def world_objects(sig, wcfg):
    """The World objects (cpp2lean --world) the configuration drives, each with its class."""
    objs = wcfg.get("objects") or [w["name"] for w in sig["world"]]
    return [(w, next(c for c in sig["classes"] if c["cxx"] == w["class"])) for w in sig["world"] if w["name"] in objs]


def world_methods(sig, wcfg):
    """The drivable member functions of the World objects (cpp2lean --world), each as
    dict(method, lean="World.<object>.<method>", object=..., cls=..., short=<method>): a line names
    `object.method` (the method relative to its class: `AP_Motors.get_type_string` for a base's
    version). Public member functions and those listed in "extra_methods" (`object.method`); a member
    function that reads the boundary takes the object's inputs `w.<object>'inp` (set from the line),
    one that writes the output log takes the log. "member_methods": member functions of a member
    object, called through it (`motors.thr_lin.thrust_to_actuator`)."""
    out, skipped = [], []
    extra = set(wcfg.get("extra_methods", []))
    for w, cls in world_objects(sig, wcfg):
        subs = [(cls, None, None)]
        for mm in wcfg.get("member_methods", []):
            if mm["object"] == w["name"]:
                subs.append((next(c for c in sig["classes"] if c["cxx"] == mm["class"]), mm["member"], set(mm["methods"])))
        for c, via, only in subs:
            for m in c["methods"]:
                if m["kind"] != "method":
                    continue
                if any(p.get("hidden", {}).get("kind") == "hal_storage" for p in m["params"]):
                    # (cpp2lean --hal-storage in a World, Phase 4 AP_Mission: the HAL storage, threaded through the run,
                    # the last argument and the result after the outputs; the C++ keeps it in its HAL object)
                    m = dict(m, params=[p for p in m["params"] if not p.get("hidden")],
                             hal_storage=next(p for p in m["params"] if p.get("hidden")))
                short = m["lean"][len(c["lean"]) + 1:] if m["lean"].startswith(c["lean"] + ".") else m["lean"]
                key = "%s.%s" % (w["name"], short) if via is None else "%s.%s.%s" % (w["name"], via, short)
                if only is not None and short not in only:
                    continue
                if not drivable(c, m, [m["lean"].split(".", 1)[1]] if key in extra or only is not None else [], wcfg.get("enum_leaves", False)):
                    continue
                if "r" in m["reads"] or m.get("uses_own") or (via is not None and "w" in m["reads"] + m["writes"]):
                    skipped.append(key)     # live reads, const reference members, owner helpers: not in a World
                    continue
                out.append(dict(m, lean="World." + key, object=w, cls=c, short=short, via=via))
    if skipped:
        print("World: not driven (live reads, reference members or owner reads): %s" % ", ".join(skipped))
    return out


def world_leaves(sig, w):
    if w.get("static"):         # a static data member (cpp2lean --ekf-types --world): `Class::member`
        return [(lf, "%s::%s%s" % (w["static"], w["cxx"], lf["cxx"]), "w.%s%s" % (w["name"], lf["lean"])) for lf in w["leaves"]]
    cls = next(c for c in sig["classes"] if c["cxx"] == w["class"])
    return [(lf, "%s.%s" % (w["cxx"], lf["cxx"]), "w.%s%s.%s" % (w["name"], "'p" if lf["root"] == "p" else "", lf["lean"]))
            for lf in cls["leaves"]]


def world_class(sig, wcfg):
    """The pseudo-class of the World run: its flattened inputs are those of every World object,
    prefixed by the object (`attitude_control.yaw`), its leaves those of every World object."""
    return {"cxx": "World", "lean": "World", "has_params": False, "inputs": [], "outputs": [], "sub_outputs": [],
            "sub_inputs": [{"field": w["name"], "class": w["class"]} for w in sig["world"]] +
                          [{"field": h["field"], "class": h["class"]} for h in sig.get("heap", []) if h.get("inputs")], "methods": [],
            "leaves": [lf for w in sig["world"] + sig.get("world_statics", []) for lf, _, _ in world_leaves(sig, w)]}


def world_ns(sig):
    """The namespace prefix of the World and its classes (`Copter_lib.` under --nest, else empty)."""
    w = sig["world"][0]
    cls = next(c for c in sig["classes"] if c["cxx"] == w["class"])
    return cls["lean"][:-len(w["lean"])] if cls["lean"].endswith(w["lean"]) else ""


def world_unity_globals(wcfg):
    """The definitions of the World objects for the C++ driver, as the unity file has them (config
    "cxx_world": {"unity": the unity file, "classes": {object: C++ class}}): every line after the
    file's last #include, each listed object defined with the given class instead (a driver
    subclass that records the --boundary-call members, e.g. `DriverMotors`), constructed alike."""
    cw = wcfg["cxx_world"]
    with open(os.path.join(HERE, cw["unity"])) as f:
        lines = f.read().splitlines()
    last = max(i for i, l in enumerate(lines) if l.startswith("#include"))
    out = ["// the World objects as %s defines them (lines %d-%d)%s" % (cw["unity"], last + 2, len(lines),
           "; " + ", ".join("`%s` of class %s" % kv for kv in sorted(cw.get("classes", {}).items())) if cw.get("classes") else "")]
    done = set()
    for l in lines[last + 1:]:
        for name, cxx_class in cw.get("classes", {}).items():
            m = re.match(r"^(\s*)([A-Za-z_][\w:<>, ]*?)(\s+)%s(\s*[(;{])" % re.escape(name), l)
            if m:
                l = m.group(1) + cxx_class + m.group(3) + name + l[m.end(3) + len(name):]
                done.add(name)
        out.append(l)
    missing = set(cw.get("classes", {})) - done
    if missing:
        raise SystemExit("difftest: no definition of %s in %s" % (", ".join(sorted(missing)), cw["unity"]))
    return out


def cpp_world_driver(example, sig, wcfg, methods):
    """The C++ side of the World differential test: each line names `object.method`, its arguments,
    then a value for every input of every World object (the last tokens); the inputs are made the
    boundary's answers by the configuration's C++ statements ("inputs"; aliases are one C++ object),
    the call is made on the file-scope object, and the line prints the result, the reference
    parameters, every leaf of every World object and the output log of the call."""
    lines = ["// Generated by cpp2lean/difftest.py: the C++ side of the World differential test (cpp2lean --world).",
             "// Reads input lines, calls the member function each names on the named file-scope object, prints",
             "// the result, the reference parameters and every state leaf of every object after the call.",
             "#include <cfloat>", "#include <cinttypes>", "#include <cmath>", "#include <cstddef>", "#include <cstdint>",
             "#include <cstdio>", "#include <cstdlib>", "#include <cstring>"] + wcfg.get("cxx_prelude", []) + [
             "#define private public   // the driver reads every data member", "#define protected public"] + \
            heap_registry(sig) + \
            ["#include %s" % x for x in wcfg.get("cxx_include", ["\"%s.cpp\"" % example])] + ["#undef private", "#undef protected", ""]
    if wcfg.get("cxx_world"):
        lines += world_unity_globals(wcfg) + [""]
    lines += heap_names(sig)
    if wcfg.get("quiet_console"):
        lines += ["// config \"quiet_console\": the library's console messages (`::printf` under SITL, SCurve.cpp:217)",
                  "// go to /dev/null; the driver prints its lines to the original standard output",
                  "#include <fcntl.h>", "#include <unistd.h>",
                  "static FILE *cpp2lean_out;", "#define printf(...) fprintf(cpp2lean_out, __VA_ARGS__)", ""]
    lines += CPP_PRELUDE + wcfg.get("globals", []) + [""]
    log = bool(sig.get("output_log"))
    lines.append("static void dump() {")
    for w in sig["world"] + sig.get("world_statics", []):
        for lf, cxx, _ in world_leaves(sig, w):
            lines.append("    " + cpp_token_print(lf["type"], cxx, lf["enum"] is not None))
    for hi, h in enumerate(sig.get("heap", [])):
        # the heap objects of class h in creation order: their number, then each one's leaves
        cls = next(c for c in sig["classes"] if c["cxx"] == h["class"])
        lines.append("    { int k = 0; for (int i = 0; i < cpp2lean_nalloc; i++) { size_t m; if (cpp2lean_class_of(cpp2lean_allocs[i], &m) == %d) k += (int)m; } printf(\" h:%%d\", k); }" % hi)
        lines.append("    for (int i = 0; i < cpp2lean_nalloc; i++) { size_t m; if (cpp2lean_class_of(cpp2lean_allocs[i], &m) != %d) continue;" % hi)
        lines.append("        for (size_t j = 0; j < m; j++) { %s *o = (%s *)((char *)cpp2lean_allocs[i].p + j * sizeof(%s));" % (h["class"], h["class"], h["class"]))
        for lf in cls["leaves"]:
            lines.append("            " + cpp_token_print(lf["type"], "o->" + lf["cxx"], lf["enum"] is not None))
        lines.append("        } }")
    if log:
        # the boundary calls of this call, in order, as the environment recorded them (cxx_env)
        lines.append("    printf(\"%s\", cpp2lean_events.c_str()); cpp2lean_events.clear();")
    lines += ["}", ""]
    fins = flat_inputs(sig, world_class(sig, wcfg))
    aliases, consts = wcfg.get("input_aliases", {}), wcfg.get("const_inputs", {})
    lines.append("static void set_inputs(char **tok) {   // tok: the line's input tokens")
    for j, inp in enumerate(fins):
        if inp["path"] in aliases or inp["path"] in consts:
            continue                        # the same C++ object as the aliased input; a constant input
        if inp["path"] not in wcfg.get("inputs", {}):
            raise SystemExit("difftest: no C++ statement for World input `%s` (config \"inputs\")" % inp["path"])
        lines.append("    " + wcfg["inputs"][inp["path"]].replace("%s", cpp_read(inp["type"], "tok[%d]" % j)))
    lines += ["}", ""]
    overrides = []
    for key, v in wcfg.get("params", {}).items():     # parameters set after construction, on both sides
        obj, path = key.split(".", 1)
        w = next(x for x in sig["world"] if x["name"] == obj)
        lf = next((x for x, _, _ in world_leaves(sig, w) if x["root"] == "p" and x["lean"] == path), None)
        if lf is None:
            raise SystemExit("difftest: no parameter `%s` of World object %s" % (path, obj))
        overrides.append("    %s.%s.set(%s);" % (w["cxx"], lf["cxx"][:-len(".get()")], v + ("f" if lf["type"] == "float" and "." in v else "")))
    for key, v in wcfg.get("state_params", {}).items():     # parameters that are state (cpp2lean --param-ext), set after construction
        obj, path = key.split(".", 1)
        w = next(x for x in sig["world"] if x["name"] == obj)
        lf = next((x for x, _, _ in world_leaves(sig, w) if x["root"] == "s" and x["cxx"] == path), None)
        if lf is None:
            raise SystemExit("difftest: no state leaf `%s` of World object %s (config \"state_params\")" % (path, obj))
        overrides.append("    %s.%s = %s;" % (w["cxx"], lf["cxx"], v))
    quiet = ["    cpp2lean_out = fdopen(dup(1), \"w\");", "    dup2(open(\"/dev/null\", O_WRONLY), 1);"] if wcfg.get("quiet_console") else []
    nin = len(fins)
    lines += ["int main() {", "    static char buf[1 << 15];", "    long line = 0;"] + quiet + overrides + [
              "    printf(\"0 init |\"); dump(); printf(\"\\n\");",
              "    while (fgets(buf, sizeof buf, stdin)) {", "        line++;", "        static char *tok[1024];", "        int nt = 0;",
              "        for (char *p = strtok(buf, \" \\n\"); p && nt < 1024; p = strtok(nullptr, \" \\n\")) tok[nt++] = p;",
              "        if (nt < %d) { fprintf(stderr, \"bad input line %%ld\\n\", line); return 1; }" % (nin + 1),
              "        set_inputs(tok + nt - %d);" % nin,
              "        printf(\"%ld %s\", line, tok[0]);"]
    first = True
    for m in methods:
        key = m["lean"].split(".", 1)[1]
        g = wcfg.get("guards", {}).get(key)
        if g:
            # config "guards": the call is made only if the World satisfies the condition (else " skip" on both sides):
            # AP_InertialSensor::update waits for samples until they come, which needs input records to consume
            lines.append("        %sif (!strcmp(tok[0], \"%s\") && !(%s)) { printf(\" skip\");" % ("" if first else "} else ", key, g["cxx"]))
            first = False
        lines.append("        %sif (!strcmp(tok[0], \"%s\")) {" % ("" if first else "} else ", key))
        first = False
        names = []
        k = 1
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
            un = wcfg.get("cxx_union_params", {}).get("%s.%s" % (key, p.get("name")))
            if un:      # config "cxx_union_params": a bit-field union the model holds as its integer (`nav_filter_status`)
                lines.append("            %s a%d; a%d.value = %s;" % (un, i, i, cpp_read(p["type"], "tok[%d]" % k)))
                names[-1] = "a%d" % i
                k += 1
                continue
            lines.append("            %s a%d = %s;" % (enum_cxx or p["type"], i, cpp_read(p["type"], "tok[%d]" % k, enum_cxx)))
            k += 1
        target = m["object"]["cxx"] + ("." + m["via"] if m.get("via") else "")
        call = "%s.%s(%s)" % (target, cpp_call_name(m["cls"], dict(m, lean=m["cls"]["lean"] + "." + m["short"])), ", ".join(names))
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
                    lines.append("            " + cpp_token_print(lf["type"], "a%d.%s" % (i, lf["cxx"]), lf.get("enum") is not None))
            elif p["ref"] == "mut" and wcfg.get("cxx_union_params", {}).get("%s.%s" % (key, p.get("name"))):
                lines.append("            " + cpp_token_print(p["type"], "a%d.value" % i))
            elif p["ref"] == "mut":
                lines.append("            " + cpp_token_print(p["under"] or p["type"], "a%d" % i, p["enum"] is not None))
        for stmt in wcfg.get("after_call_for", {}).get(key, []):
            lines.append("            " + stmt)
    lines += ["        } else { printf(\" ?\"); }"]
    for stmt in wcfg.get("after_call", []):
        lines.append("        " + stmt)
    lines += ["        printf(\" |\"); dump(); printf(\"\\n\");", "    }", "    return 0;", "}", ""]
    return "\n".join(lines)


def heap_registry(sig):
    """C++ lines before the example (cpp2lean --world-pointers): every allocation by `new` and by
    malloc is recorded in order (the Lean side keeps the heap objects of each class in creation
    order); a deleted object's memory is kept, so that its last state can be printed as Lean keeps
    its slot."""
    if not sig.get("heap"):
        return []
    return ["// cpp2lean --world-pointers: the allocations, in order (heap slots of the World)",
            "#include <new>",
            "struct cpp2lean_alloc { void *p; size_t n; bool raw; };",
            "static cpp2lean_alloc cpp2lean_allocs[1 << 16];",
            "static int cpp2lean_nalloc;",
            "static void cpp2lean_log(void *p, size_t n, bool raw) { if (p && cpp2lean_nalloc < (1 << 16)) cpp2lean_allocs[cpp2lean_nalloc++] = {p, n, raw}; }",
            "void *operator new(size_t n) { void *p = malloc(n); if (!p) abort(); cpp2lean_log(p, n, false); return p; }",
            "void *operator new(size_t n, const std::nothrow_t &) noexcept { void *p = malloc(n); cpp2lean_log(p, n, false); return p; }",
            "void operator delete(void *) noexcept {}          // kept: its last state is printed",
            "void operator delete(void *, size_t) noexcept {}",
            "void operator delete(void *, const std::nothrow_t &) noexcept {}",
            "static void *cpp2lean_malloc(size_t n) { void *p = malloc(n); cpp2lean_log(p, n, true); return p; }",
            "#define malloc(n) cpp2lean_malloc(n)", ""]


def heap_names(sig):
    """C++ lines after the example: the class of a recorded allocation (by its size: the classes of
    `new` have distinct sizes, checked; memory for placement new holds a multiple of its class's
    size) and the name of a pointer as `WPtr.name` gives it."""
    heap = sig.get("heap") or []
    if not heap and sig.get("mtags"):
        # cpp2lean --member-pointers without heap objects: the World objects and the tagged member objects
        out = ["static const char *cpp2lean_ptr_name(const void *p) {", "    if (p == nullptr) return \"null\";"]
        for tg in sig["mtags"]:     # (first: a member at offset 0 has its object's address)
            out.append("    if (p == (const void *)&%s) return \"%s\";" % (tg["cxx"], tg["name"]))
        for w in sig["world"]:
            out.append("    if (p == (const void *)&%s) return \"%s\";" % (w["cxx"], w["name"]))
        return out + ["    return \"?\";", "}", "static void tp(const void *p) { printf(\" p:%s\", cpp2lean_ptr_name(p)); }", ""]
    if not heap:
        return []
    out = ["static int cpp2lean_class_of(const cpp2lean_alloc &a, size_t *m) {"]
    news = [h for h in heap if not h["placement"]]
    for i, a in enumerate(news):
        for b in news[i + 1:]:
            out.append("    static_assert(sizeof(%s) != sizeof(%s), \"difftest: heap classes %s and %s have the same size\");" % (a["class"], b["class"], a["class"], b["class"]))
    for hi, h in enumerate(heap):
        if h["placement"]:
            out.append("    if (a.raw && a.n %% sizeof(%s) == 0) { *m = a.n / sizeof(%s); return %d; }" % (h["class"], h["class"], hi))
        else:
            out.append("    if (!a.raw && a.n == sizeof(%s)) { *m = 1; return %d; }" % (h["class"], hi))
    out += ["    *m = 0;", "    return -1;", "}", "",
            "static const char *cpp2lean_ptr_name(const void *p) {", "    static char buf[160];",
            "    if (p == nullptr) return \"null\";"]
    for tg in sig.get("mtags", []):     # (cpp2lean --member-pointers; first: a member at offset 0 has its object's address)
        out.append("    if (p == (const void *)&%s) return \"%s\";" % (tg["cxx"], tg["name"]))
    for w in sig["world"]:
        out.append("    if (p == (const void *)&%s) return \"%s\";" % (w["cxx"], w["name"]))
    out.append("    int idx[%d] = {0};" % len(heap))
    out.append("    static const size_t sz[%d] = {%s};" % (len(heap), ", ".join("sizeof(%s)" % h["class"] for h in heap)))
    out.append("    static const char *nm[%d] = {%s};" % (len(heap), ", ".join("\"%s\"" % h["field"] for h in heap)))
    out += ["    for (int i = 0; i < cpp2lean_nalloc; i++) {", "        size_t m; int c = cpp2lean_class_of(cpp2lean_allocs[i], &m);",
            "        if (c < 0) continue;", "        const char *b = (const char *)cpp2lean_allocs[i].p;",
            "        if ((const char *)p >= b && (const char *)p < b + m * sz[c]) { snprintf(buf, sizeof buf, \"%s#%d\", nm[c], idx[c] + (int)(((const char *)p - b) / sz[c])); return buf; }",
            "        idx[c] += (int)m;", "    }", "    return \"?\";", "}",
            "static void tp(const void *p) { printf(\" p:%s\", cpp2lean_ptr_name(p)); }", ""]
    if sig.get("funcs") or any(is_fun_type(lf["type"]) for c in sig["classes"] for lf in c["leaves"]):
        # a functor: the bound member function (by its wrapper) and the object's name, as `WFun.name`
        out += ["static void tfun(const Functor<void> &f) {", "    if (f._method == nullptr) { printf(\" p:null\"); return; }"]
        for fn in sig["funcs"]:
            out.append("    if (f._method == &Functor<void>::method_wrapper<%s, &%s::%s>) { printf(\" p:%s@%%s\", cpp2lean_ptr_name(f._obj)); return; }" %
                       (fn["class"], fn["class"], fn["method"], fn["ctor"]))
        out += ["    printf(\" p:?\");", "}", ""]
    return out


def lean_world_driver(sig, wcfg, methods, tag):
    """The Lean side of the World differential test: the World from `World.init` (parameters set as
    in the C++), each line sets every object's inputs `w.<object>'inp` from the line's last tokens,
    calls the member function on its object's components and the World (`w`), threads the output
    log, and prints what the C++ side prints. One definition per driven member function."""
    pre = world_ns(sig)
    W = pre + "World"
    log = bool(sig.get("output_log"))
    OT = (sig["output_ns"] or "") + "Outputs" if log else None
    out = []
    # runs of one translation that drive the same member functions share every definition but
    # `run<tag>` (the parameters): the first run's
    shared = (sig["namespace"], tuple(m["lean"] for m in methods))
    if shared in WORLD_SHARED:
        hsz = next((m["hal_storage"]["hidden"]["size"] for m in methods if m.get("hal_storage")), None)
        return out + lean_world_run(sig, wcfg, tag, WORLD_SHARED[shared], W, log, hsz)
    WORLD_SHARED[shared] = tag
    used_enums = set()
    for m in methods:
        for p in m["params"]:
            if p["enum"]:
                used_enums.add(p["enum"])
            if not p["scalar"]:
                used_enums |= {lf["enum"] for lf in p.get("leaves") or [] if lf.get("enum")}
    for en in sorted(used_enums - EMITTED_ENUMOF):
        EMITTED_ENUMOF.add(en)              # one definition per enum across the runs
        e = enum_info(sig, en)
        out.append("def enumOf_%s (v : Int) : %s :=" % (en.replace(".", "_"), en))
        for i, (nm, v, ln) in enumerate(e["values"]):
            out.append("  %sif v == %d then %s.%s" % ("" if i == 0 else "else ", v, en, ln))
        out.append("  else default")
        out.append("")
    if log:
        out += lean_output_tokens(sig, tag)
    # the dump, in definitions of at most 200 tokens (one expression of thousands of `++` is slow to elaborate)
    toks = [lean_tok(lf["type"], lean, lf["enum"]) for w in sig["world"] + sig.get("world_statics", []) for lf, _, lean in world_leaves(sig, w)]
    chunks = [toks[i:i + 200] for i in range(0, len(toks), 200)] or [[]]
    for ci, ch in enumerate(chunks):
        out.append("def dump%s_%d (w : %s) : String :=" % (tag, ci, W))
        out.append("  \"\"" + "".join(" ++ " + t for t in ch))
        out.append("")
    hparts = []
    for hi, h in enumerate(sig.get("heap", [])):
        cls = next(c for c in sig["classes"] if c["cxx"] == h["class"])
        if len(cls["leaves"]) > 50:
            # one heap object's leaves in definitions of at most 50 tokens, its state typed (a long `++`
            # inside the fold's lambda exceeds Lean's elaboration budget)
            htoks = [lean_tok(lf["type"], "st.%s" % lf["lean"], lf["enum"]) for lf in cls["leaves"]]
            hch = [htoks[i:i + 50] for i in range(0, len(htoks), 50)]
            for ci, ch in enumerate(hch):
                out.append("def dump%sO_%d_%d (st : %s.State) : String :=" % (tag, hi, ci, cls["lean"]))
                out.append("  \"\"" + "".join(" ++ " + t for t in ch))
                out.append("")
            out.append("def dump%sH_%d (w : %s) : String :=" % (tag, hi, W))
            out.append("  \" h:\" ++ toString w.%s.size ++ w.%s.foldl (fun acc st => acc%s) \"\"" %
                       (h["field"], h["field"], "".join(" ++ dump%sO_%d_%d st" % (tag, hi, ci) for ci in range(len(hch)))))
            out.append("")
            hparts.append("dump%sH_%d w" % (tag, hi))
            continue
        out.append("def dump%sH_%d (w : %s) : String :=" % (tag, hi, W))
        out.append("  \" h:\" ++ toString w.%s.size ++ w.%s.foldl (fun acc st => acc%s) \"\"" %
                   (h["field"], h["field"], "".join(" ++ " + lean_tok(lf["type"], "st.%s" % lf["lean"], lf["enum"]) for lf in cls["leaves"])))
        out.append("")
        hparts.append("dump%sH_%d w" % (tag, hi))
    out.append("def dump%s (w : %s)%s : String :=" % (tag, W, " (ob : %s)" % OT if log else ""))
    out.append("  " + " ++ ".join(["dump%s_%d w" % (tag, ci) for ci in range(len(chunks))] + hparts)
               + (" ++ ob.foldl (fun acc e => acc ++ outTok%s e) \"\"" % tag if log else ""))
    out.append("")
    # the inputs of every World object, from the line's last tokens (k: the first of them)
    nin = 0
    sets = []
    for w in sig["world"] + [{"name": h["field"], "class": h["class"]} for h in sig.get("heap", []) if h.get("inputs")]:
        # (cpp2lean --front-ends: what the heap objects of a class read from the boundary, `heap'C'inp`)
        cls = next(c for c in sig["classes"] if c["cxx"] == w["class"])
        fins = flat_inputs(sig, cls)
        if fins:
            sets.append("%s'inp := %s" % (w["name"], lean_inputs_record(fins, nin, base="k")))
        nin += len(fins)
    out.append("def inputs%s (w : %s) (_t : Array String) (_k : Nat) : %s :=" % (tag, W, W))
    out.append("  " + ("{ w with %s }" % ", ".join(sets) if sets else "w").replace("t[k + ", "_t[_k + "))
    out.append("")
    obp = " (ob : %s)" % OT if log else ""
    ret = "%s%s × String" % (W, " × %s" % OT if log else "")
    hsz = next((m["hal_storage"]["hidden"]["size"] for m in methods if m.get("hal_storage")), None)
    if hsz is not None:
        # (the HAL storage, threaded through the run: `hs`)
        obp += " (hs : Array UInt8)"
        ret = "%s%s × Array UInt8 × String" % (W, " × %s" % OT if log else "")
    for mi, m in enumerate(methods):
        g = m["object"]["name"]
        via = m.get("via")
        sel = (lambda x: "%s.%s" % (x, via)) if via else (lambda x: x)
        out.append("/-- `%s` -/" % m["lean"].split(".", 1)[1])
        out.append("def call%s_%d (w : %s)%s (_t : Array String) : %s :=" % (tag, mi, W, obp, ret))
        args = []
        if "p" in m["reads"] + m["writes"]:
            args.append(sel("w.%s'p" % g))
        if "s" in m["reads"] + m["writes"]:
            args.append(sel("w.%s" % g))
        if "w" in m["reads"] + m["writes"]:
            args.append("w")
        if "o" in m["writes"]:
            args.append("ob")
        if m["uses_inp"]:
            args.append(sel("w.%s'inp" % g))
        k = 1
        for i, p in enumerate(m["params"]):
            if not p["scalar"]:
                fins = [{"path": lf["lean"], "type": lf["type"], "enum": lf.get("enum")} for lf in p["leaves"]]
                out.append("  let a%d : %s := %s" % (i, p["lean_type"], lean_inputs_record(fins, k).replace("t[", "_t[")))
                k += len(fins)
                continue
            lt = p["enum"] if p["enum"] else lean_type(p["type"])
            out.append("  let a%d : %s := %s" % (i, lt, lean_read(p["type"], "_t[%d]!" % k, sig, p["enum"])))
            k += 1
        args += ["a%d" % i for i in range(len(m["params"]))]
        if m.get("hal_storage"):
            args.append("hs")
        comps = [c for c in ("p", "s", "w", "o") if c in m["writes"]]
        outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
        comps += ["o%d" % i for i in outs]
        if m.get("hal_storage") and m["hal_storage"]["ref"] == "mut":
            comps.append("hs")
        if m["ret"] != "void":
            comps.append("r")
        names = ["c%d" % i for i in range(len(comps))]
        call = "%s %s" % (m["cls"]["lean"] + "." + m["short"], " ".join(args))
        if comps:
            out.append("  let %s := %s" % (names[0] if len(comps) == 1 else "(%s)" % ", ".join(names), call))
        # the World first: a component of this object written after it takes precedence (the result
        # order of the translation: Params, State, World, Outputs)
        for c, nm in sorted(zip(comps, names), key=lambda x: 0 if x[0] == "w" else 1):
            if c == "w":
                out.append("  let w := %s" % nm)
            elif c == "p":
                out.append("  let w := { w with %s := %s }" % (sel("%s'p" % g), nm))
            elif c == "s":
                out.append("  let w := { w with %s := %s }" % (sel(g), nm))
            elif c == "o":
                out.append("  let ob := %s" % nm)
            elif c == "hs":
                out.append("  let hs := %s" % nm)
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
                rtoks += [lean_tok(lf["type"], "%s.%s" % (names[comps.index("o%d" % i)], lf["lean"]), lf.get("enum")) for lf in p["leaves"]]
            else:
                rtoks.append(lean_tok(p["under"] or p["type"], names[comps.index("o%d" % i)], p["enum"]))
        out.append("  (w%s%s, %s)" % (", ob" if log else "", ", hs" if hsz is not None else "", " ++ ".join(["\"\""] + rtoks)))
        out.append("")
    if hsz is not None:
        return out + lean_world_loop_hs(sig, wcfg, methods, tag, W, nin, log) + lean_world_run(sig, wcfg, tag, tag, W, log, hsz)
    out += ["partial def loop%s (h : IO.FS.Stream) (out : IO.FS.Stream) (w : %s) (n : Nat) : IO Unit := do" % (tag, W),
            "  let line ← h.getLine", "  if line.isEmpty then return",
            "  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray",
            "  let w := inputs%s w t (t.size - %d)" % (tag, nin)]
    if log:
        out.append("  let ob : %s := #[]   -- the boundary calls of this call" % OT)
    out.append("  let (w%s, o) := match t[0]! with" % (", ob" if log else ""))
    for mi, m in enumerate(methods):
        g = wcfg.get("guards", {}).get(m["lean"].split(".", 1)[1])
        if g:       # config "guards" (cpp_world_driver)
            out.append("    | \"%s\" => if %s then call%s_%d w%s t else (w%s, \" skip\")" % (m["lean"].split(".", 1)[1], g["lean"], tag, mi, " ob" if log else "", ", ob" if log else ""))
            continue
        out.append("    | \"%s\" => call%s_%d w%s t" % (m["lean"].split(".", 1)[1], tag, mi, " ob" if log else ""))
    out.append("    | _ => (w%s, \" ?\")" % (", ob" if log else ""))
    out += ["  out.putStr (toString (n + 1) ++ \" \" ++ t[0]! ++ o ++ \" |\" ++ dump%s w%s ++ \"\\n\")" % (tag, " ob" if log else ""),
            "  loop%s h out w (n + 1)" % tag, ""]
    return out + lean_world_run(sig, wcfg, tag, tag, W, log)


WORLD_SHARED = {}       # (namespace, driven member functions) -> the tag whose definitions the runs share


def lean_world_loop_hs(sig, wcfg, methods, tag, W, nin, log):
    """lean_world_driver's loop with the HAL storage `hs` threaded (cpp2lean --hal-storage in a World)."""
    if log:
        raise SystemExit("difftest: a World with the HAL storage and the output log")
    out = ["partial def loop%s (h : IO.FS.Stream) (out : IO.FS.Stream) (w : %s) (hs : Array UInt8) (n : Nat) : IO Unit := do" % (tag, W),
           "  let line ← h.getLine", "  if line.isEmpty then return",
           "  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray",
           "  let w := inputs%s w t (t.size - %d)" % (tag, nin),
           "  let (w, hs, o) := match t[0]! with"]
    for mi, m in enumerate(methods):
        out.append("    | \"%s\" => call%s_%d w hs t" % (m["lean"].split(".", 1)[1], tag, mi))
    out.append("    | _ => (w, hs, \" ?\")")
    out += ["  out.putStr (toString (n + 1) ++ \" \" ++ t[0]! ++ o ++ \" |\" ++ dump%s w ++ \"\\n\")" % tag,
            "  loop%s h out w hs (n + 1)" % tag, ""]
    return out


def lean_world_run(sig, wcfg, tag, base, W, log, hsz=None):
    """`run<tag>`: the World from `World.init`, the run's parameters set, then the loop of `base`."""
    out = ["def run%s : IO Unit := do" % tag, "  let w := %s.init" % W]
    for key, v in wcfg.get("params", {}).items():     # parameters set after construction, on both sides
        obj, path = key.split(".", 1)
        wo = next(x for x in sig["world"] if x["name"] == obj)
        lf = next(x for x, _, _ in world_leaves(sig, wo) if x["root"] == "p" and x["lean"] == path)
        out.append("  let w := { w with %s'p.%s := (%s : %s) }" % (obj, path, v, lean_type(lf["type"])))
    for key, v in wcfg.get("state_params", {}).items():     # parameters that are state (cpp2lean --param-ext)
        obj, path = key.split(".", 1)
        wo = next(x for x in sig["world"] if x["name"] == obj)
        lf = next(x for x, _, _ in world_leaves(sig, wo) if x["root"] == "s" and x["cxx"] == path)
        out.append("  let w := %s" % lean_update("w", [("f", obj)] + lean_path_steps(lf["lean"]), "(%s : %s)" % (v, lean_type(lf["type"]))))
    out += ["  let out ← IO.getStdout",
            "  out.putStr (\"0 init |\" ++ dump%s w%s ++ \"\\n\")" % (base, " #[]" if log else ""),
            "  loop%s (← IO.getStdin) out w%s 0" % (base, " (Array.replicate %d (0 : UInt8))" % hsz if hsz is not None else ""), ""]
    return out


def lean_path_steps(lean_path):
    """`_source_set[1]!.posxy._value` -> [("f", "_source_set"), ("i", "1"), ("f", "posxy"), ("f", "_value")]."""
    out = []
    for comp in re.findall(r"(«[^»]+»|[^.\[\]!]+)(\[\d+\]!)?", lean_path):
        out.append(("f", comp[0]))
        if comp[1]:
            out.append(("i", comp[1][1:-2]))
    return out


def lean_update(base, steps, value):
    """The Lean expression of `base` with the location `steps` (fields and constant indices) set to value."""
    if not steps:
        return value
    k, x = steps[0]
    b = base if re.match(r"^[\w.'«»]+$", base) else "(%s)" % base
    if k == "f":
        return "{ %s with %s := %s }" % (b, x, lean_update("%s.%s" % (b, x), steps[1:], value))
    return "%s.set! %s (%s)" % (b, x, lean_update("%s[%s]!" % (b, x), steps[1:], value))


def drivable_free(f):
    if f.get("file_static"):              # a static function of a .cpp: not callable from a driver
        return False
    if any(p["ref"] == "ptr" for p in f["params"]):
        return False                        # a nullable out-pointer parameter (not driven)
    if not all((p["scalar"] or simple_leaves(p.get("leaves")) or p.get("array_elem") in TYPE_ORDER) and not p["boundary"] for p in f["params"]):
        return False
    if any(p.get("array_elem") for p in f["params"]) and not all(p["scalar"] or p.get("array_elem") for p in f["params"]):
        return False                        # (arrays with struct arguments: not driven)
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


def split_world_statics(sig):
    """cpp2lean --ekf-types --world: the static data members among the World's fields are not objects."""
    if sig.get("world") and any(w.get("static") for w in sig["world"]):
        # (a static local, cpp2lean --reachable, is not printed: the C++ driver cannot name it)
        sig["world_statics"] = [w for w in sig["world"] if w.get("static") and not w.get("local")]
        sig["world"] = [w for w in sig["world"] if not w.get("static")]
    return sig


def world_runs(cfg):
    """The World runs of a configuration: "world" (one run), or "world" as the settings common to the
    runs and "world_runs" as each run's own settings over them (a dictionary-valued setting, e.g.
    "params", "weights", "ranges", is updated key by key; any other replaced)."""
    if not cfg.get("world"):
        return []
    if not cfg.get("world_runs"):
        return [cfg["world"]]
    out = []
    for r in cfg["world_runs"]:
        w = dict(cfg["world"])
        for k, v in r.items():
            if isinstance(v, dict) and isinstance(w.get(k), dict) and not r.get("replace_" + k):
                w[k] = dict(w[k], **v)
            else:
                w[k] = v
        out.append(w)
    return out


def line_differs(x, y, nan_only):
    """Token comparison of one output line (compare_tokens): False if every token is equal, or both
    are floating NaNs (counted in nan_only by bit patterns)."""
    if x == y:
        return False
    x, y = x.split(), y.split()
    if len(x) != len(y):
        return True
    for tx, ty in zip(x, y):
        if tx == ty:
            continue
        if tx[:2] in ("f:", "d:") and ty[:2] == tx[:2] and is_nan_hex(tx[2:]) and is_nan_hex(ty[2:]):
            key = (tx[2:], ty[2:])
            nan_only[key] = nan_only.get(key, 0) + 1
            continue
        return True
    return False


def compare_stream(cpp_cmd, lean_cmd, base, keep=5):
    """Run both drivers on base + ".in" and compare their output lines as they come (compare_tokens),
    without holding the outputs (a World line holds every leaf of every object). The first `keep`
    differing lines are returned in full, the others by number; the first 100 differing pairs go to
    base + ".diff". With CPP2LEAN_KEEP_OUTPUT set, the outputs are written to base + ".cpp.out" and
    ".lean.out"."""
    procs = []
    errs = []
    for cmd, suf in ((cpp_cmd, ".cpp.err"), (lean_cmd, ".lean.err")):
        err = open(base + suf, "w")
        errs.append(err)
        procs.append(subprocess.Popen(cmd, stdin=open(base + ".in"), stdout=subprocess.PIPE, stderr=err, bufsize=1 << 20))
    keepf = [open(base + ".cpp.out", "w"), open(base + ".lean.out", "w")] if os.environ.get("CPP2LEAN_KEEP_OUTPUT") else None
    diffs, nan_only, n = [], {}, 0
    with open(base + ".diff", "w") as df:
        while True:
            x = procs[0].stdout.readline().decode()
            y = procs[1].stdout.readline().decode()
            if not x and not y:
                break
            if keepf:
                keepf[0].write(x)
                keepf[1].write(y)
            if not x or not y or line_differs(x, y, nan_only):
                if len(diffs) < 100:
                    df.write("line %d\n  C++:  %s\n  Lean: %s\n" % (n + 1, x.rstrip("\n") or "<missing>", y.rstrip("\n") or "<missing>"))
                diffs.append((n, x.rstrip("\n") or "<missing>", y.rstrip("\n") or "<missing>") if len(diffs) < keep else (n, None, None))
            n += 1
    for p, err, cmd in zip(procs, errs, (cpp_cmd, lean_cmd)):
        p.wait()
        err.close()
        if p.returncode != 0:
            sys.stderr.write(open(err.name).read()[-4000:])
            sys.exit("difftest: command failed: %s" % " ".join(cmd))
    if keepf:
        for f in keepf:
            f.close()
    return diffs, nan_only, n


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
    namespaces translated in this run that are not listed yet; the support modules CFloat (written
    here from cpp2lean's support/ if no translation wrote it) and the C library's module are kept."""
    path = os.path.join(DEMO, "lakefile.toml")
    with open(path) as f:
        text = f.read()
    m = re.search(r'^roots = \[(.*)\]$', text, re.M)
    if not m:
        sys.exit("difftest: no `roots = [...]` line in %s" % path)
    old = re.findall(r'"([^"]+)"', m.group(1))
    roots = [r for r in old if os.path.exists(os.path.join(DEMO, r + ".lean"))]
    roots += [ns for ns in namespaces if ns not in roots]
    for sup in ["CFloat", "CString"]:
        if sup == "CString" and not os.path.exists(os.path.join(DEMO, sup + ".lean")):
            continue                    # written by the translations that use it (--c-strings, --byte-objects)
        if not os.path.exists(os.path.join(DEMO, sup + ".lean")) and os.path.exists(os.path.join(cpp2lean.SUPPORT_DIR, sup + ".lean")):
            with open(os.path.join(cpp2lean.SUPPORT_DIR, sup + ".lean")) as src, open(os.path.join(DEMO, sup + ".lean"), "w") as f:
                f.write(src.read())
        if sup not in roots and os.path.exists(os.path.join(DEMO, sup + ".lean")):
            roots.append(sup)
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
        sig = split_world_statics(json.load(f))
    for cxx, prefixes in cfg.get("skip_leaves", {}).items():
        # config "skip_leaves": {class: [leaf prefix, ...]}: leaves not printed on either side (the scheduler
        # stand-in's ring of 1024 input records, whose records reach the state through `_in` when consumed)
        for c in sig["classes"]:
            if c["cxx"] == cxx:
                c["leaves"] = [lf for lf in c["leaves"] if not any(lf["cxx"].startswith(p) for p in prefixes)]
    for d in cfg.get("lean_imports", []):    # another translation (its committed output), imported by the driver
        d = os.path.join(HERE, d)
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".lean"):
                with open(os.path.join(d, fn)) as src, open(os.path.join(DEMO, fn), "w") as dst:
                    dst.write(src.read())
                if fn[:-5] not in SUPPORT_MODULES and fn[:-5] not in EXTRA_IMPORTS:
                    EXTRA_IMPORTS.append(fn[:-5])
    ap = os.environ.get("AP", AP_DEFAULT)
    lib = os.path.join(ap, "libraries")
    stubs = os.path.realpath(os.path.join(HERE, "ardupilot", "stubs"))
    ref = os.environ.get("CPP2LEAN_REF", os.path.join(HERE, "build", "reference", "ap"))
    if cfg.get("ref_flags"):
        # Phase 3 (README.md "Phase 3: EKF data structures"): the reference build's flags of this unit
        # (ardupilot/ref_flags.py, with reference/hal first and its code-generation flags), warnings
        # left out, and the sources compiled from the reference build's copy of the libraries
        p = run([sys.executable, os.path.join(HERE, "ardupilot", "ref_flags.py"), "--json", cfg["ref_flags"]])
        cfg["cxx_flags"] = [x for x in json.loads(p.stdout.decode()) if not x.startswith("-W")] + ["-Wno-everything"] + cfg.get("cxx_flags", [])
        lib = os.path.join(ref, "libraries")
    flags = [x.replace("$STUBS", stubs).replace("$REF", ref).replace("$L", lib).replace("$HERE", HERE) for x in cfg["cxx_flags"]] + cpp2lean.CODEGEN_EXTRA
    if cfg.get("access_control") is False:
        flags.append("-fno-access-control")     # the driver reads private members (no `#define private public`)
        for c in cfg.get("classes", []):
            c.setdefault("access_control", False)
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
    n = len(diffs)
    for i, x, y in diffs[:5]:
        print("  line %d\n    C++:  %s\n    Lean: %s" % (i + 1, x, y))
    return n


MUSL_LINK = []


def musl_link():
    """The objects of musl's C sources and the linker options that bind the C library names to them
    (libm/build_musl.sh): every C++ driver calls musl's functions, not the platform's libm, as the
    Lean side runs their translation (README.md, "The C library")."""
    if not MUSL_LINK:
        p = run([os.path.join(HERE, "libm", "build_musl.sh")])
        with open(p.stdout.decode().strip()) as f:
            MUSL_LINK.extend(l.strip() for l in f if l.strip())
    return list(MUSL_LINK)


def musl_translation():
    """Translate musl's C sources (libm/translate_libm.sh) and put the modules into lean/ (Musl/,
    Musl.lean), which the translations import."""
    run([os.path.join(HERE, "libm", "translate_libm.sh")], cwd=HERE)
    out = os.path.join(HERE, "libm", "out")
    os.makedirs(os.path.join(DEMO, "Musl"), exist_ok=True)
    for fn in os.listdir(os.path.join(out, "Musl")):
        if fn.endswith(".lean"):
            with open(os.path.join(out, "Musl", fn)) as src, open(os.path.join(DEMO, "Musl", fn), "w") as dst:
                dst.write(src.read())
    with open(os.path.join(out, "Musl.lean")) as src, open(os.path.join(DEMO, "Musl.lean"), "w") as dst:
        dst.write(src.read())


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
    musl_translation()
    harness_rc = 0
    for e in [x for x in names if x.startswith("ardupilot/")]:
        # a target with a harness of its own (config "harness": ardupilot/EKF3, ardupilot/ekf3_difftest.py)
        hp = os.path.join(HERE, e + ".json")
        hc = json.load(open(hp)) if os.path.exists(hp) else {}
        if hc.get("harness"):
            names.remove(e)
            harness_rc |= subprocess.run([sys.executable, os.path.join(HERE, hc["harness"]), e]).returncode
    if not names:
        sys.exit(harness_rc)
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
            if os.environ.get("CPP2LEAN_MUTATE"):
                # sensitivity checks also on examples (as for the ArduPilot translations)
                fn = os.path.join(DEMO, ns + ".lean")
                with open(fn) as f:
                    text = f.read()
                for pat, rep in json.loads(os.environ["CPP2LEAN_MUTATE"]):
                    text, k = re.subn(pat, rep, text)
                    print("mutation of %s: %d replacements of /%s/" % (ns + ".lean", k, pat))
                with open(fn, "w") as f:
                    f.write(text)
            with open(os.path.join(DEMO, ns + ".signatures.json")) as f:
                sig = split_world_statics(json.load(f))
            funcs = sig["functions"]
        slots = slots_of(funcs)
        examples.append((ns, funcs, slots, sig["literals"]))
        if funcs:
            drv = os.path.join(EX, e + "_driver.cpp")
            with open(drv, "w") as f:
                f.write(cpp_driver(e, funcs, slots))
            run([CXX] + cpp2lean.CLANG_FLAGS + cpp2lean.CODEGEN_EXTRA + ["-o", os.path.join(BUILD, e + "_driver"), drv] + musl_link())
        for f in sig.get("free", []):
            # a parameter that is not a C++ parameter (cpp2lean --hal-storage: the HAL storage, which
            # the C++ keeps in the HAL object): the Lean driver passes a zero-filled storage of its
            # size and discards the one returned (README.md, "Phase 2b")
            hid = [p for p in f["params"] if p.get("hidden")]
            if hid:
                f["hidden"] = hid
                f["params"] = [p for p in f["params"] if not p.get("hidden")]
        if objs is not None and cfg.get("free"):
            fcfg = dict(cfg["free"])
            fcfg.setdefault("cxx_include", cfg.get("cxx_include", []))
            fcls = {"cxx": "free functions", "lean": ns, "has_params": False, "inputs": [], "sub_inputs": [],
                    "outputs": [], "sub_outputs": [], "methods": [], "leaves": []}
            fmethods = [f for f in sig.get("free", []) if drivable_free(f)]
            if fcfg.get("only"):
                # config "free"."only" (Phase 4): a regular expression of the C++ names driven (the unity's test
                # functions, not the library functions they reach)
                fmethods = [f for f in fmethods if re.fullmatch(fcfg["only"], f["cxx"])]
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
            run([CXX, "-o", exe, o] + objs + ["-Wl,-dead_strip"] + musl_link())
            class_parts.append((tag, lean_free_driver(sig, fcfg, methods, tag)))
            class_runs.append((e, sig, fcls, tag, exe, inputs, nrand, ncorner, methods))
        for wcfg in world_runs(cfg):
            INDEXED_INPUT_LEN.clear()
            INDEXED_INPUT_LEN.update(wcfg.get("indexed_input_lengths", {}))
            UNLOGGED_OUTPUTS.clear()
            UNLOGGED_OUTPUTS.update(wcfg.get("unlogged_outputs", []))
            ncalls = a.calls if a.calls is not None else wcfg.get("calls", 20000)
            wcls = world_class(sig, wcfg)
            inputs, nrand, ncorner, methods = class_inputs(sig, wcls, wcfg, a.seed, ncalls, world_methods(sig, wcfg))
            suffix = "_" + wcfg["run"] if wcfg.get("run") else ""
            tag = "%s_World%s" % (ns, suffix)
            base = e.replace("/", "_")
            drv = os.path.join(HERE, "ardupilot" if objs is not None else "examples", "%s_World%s_driver.cpp" % (os.path.basename(e), suffix))
            with open(drv, "w") as f:
                f.write(cpp_world_driver(e, sig, wcfg, methods))
            exe = os.path.join(BUILD, "%s_World%s_driver" % (base, suffix))
            if objs is None:
                run([CXX] + cpp2lean.CLANG_FLAGS + cpp2lean.CODEGEN_EXTRA + cfg.get("cxx_extra", []) + ["-o", exe, drv] + musl_link())
            else:
                o = exe + ".o"
                run([CXX] + cfg["cxx_flags"] + ["-c", drv, "-o", o])
                run([CXX, "-o", exe, o] + objs + ["-Wl,-dead_strip"] + musl_link())
            class_parts.append((tag, lean_world_driver(sig, wcfg, methods, tag)))
            wcls = dict(wcls, run=wcfg.get("run"), stream=True)
            class_runs.append((e, sig, wcls, tag, exe, inputs, nrand, ncorner, methods))
        for ccfg in cfg.get("classes", []):
            cls = next(c for c in sig["classes"] if c["cxx"] == ccfg["class"])
            ncalls = a.calls if a.calls is not None else ccfg.get("calls", 20000)
            mlist = [m for m in cls["methods"] if drivable(cls, m, ccfg.get("extra_methods", []), ccfg.get("enum_leaves", False), ccfg.get("nullable_params", False))
                     and (not ccfg.get("only_own") or m["owner"] == cls["cxx"])]
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
                run([CXX] + cpp2lean.CLANG_FLAGS + cpp2lean.CODEGEN_EXTRA + cfg.get("cxx_extra", []) + ["-o", exe, drv] + musl_link())
            else:
                o = exe + ".o"
                run([CXX] + cfg["cxx_flags"] + ["-c", drv, "-o", o])
                run([CXX, "-o", exe, o] + objs + ["-Wl,-dead_strip"] + musl_link())
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
        if cls.get("stream"):
            diffs, nan_only, m = compare_stream([exe], [lean_exe, tag], base)
            label = "%s %s" % (e, cls["cxx"]) + (" (%s)" % cls["run"] if cls.get("run") else "")
            print("%s: %d calls (%d random, %d corner) over %d member functions of %d objects, %d leaves per line; inputs: %s" %
                  (label, nrand + ncorner, nrand, ncorner, len(methods), len({mm["object"]["name"] for mm in methods}),
                   len(cls["leaves"]), ", ".join(i["path"] for i in flat_inputs(sig, cls)) or "none"))
            total_diff += report(label, diffs, nan_only, m, "tokens")
            continue
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
    sys.exit(0 if total_diff == 0 and harness_rc == 0 else 1)


if __name__ == "__main__":
    main()
