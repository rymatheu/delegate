#!/usr/bin/env python3
"""cpp2lean: a deterministic, syntax-directed translator from a subset of C++ to Lean 4.

Usage: python3 cpp2lean.py file.cpp -o OutDir [--namespace Name] [--header FILE]...
           [--boundary Class,Class | --boundary @file]... [--param-class Class=type]...
           [--extern name:LeanName[:N]]... [-I dir]... [--clang-arg ARG]... [--keep-going]

Runs clang on file.cpp with the compilation flags of README.md ("Compilation assumptions"), reads
clang's semantic AST as JSON, and writes OutDir/Name.lean. Free functions become `def`s in
namespace Name, with the body inside `Id.run do`. A class `C` becomes namespace `C` with
`structure C.State` (its data members, base classes flattened), `C.Params` (its members of a
--param-class type), `C.Inputs` (the values it reads from objects of a --boundary class),
constructors `C.init` and one `def` per member function, threading the state through. Every
implicit conversion, literal type, overload resolution and evaluation order is taken from clang's
AST; the translator only maps node kinds to Lean syntax. Anything outside the subset (README.md,
"The subset") is reported as `file:line:col: rejected: <construct>` and the exit status is 2. No
heuristics, no search: the same input gives the same output.

Also written: OutDir/Name.signatures.json (the translated functions and classes and their C++
signatures, read by difftest.py to generate drivers), and OutDir/CppLibm.lean when the C++ calls a
<cmath> function that core Lean 4.33 does not expose (fmaxf, fminf, fmax, fmin, fmodf, fmod).
"""

import argparse
import json
import os
import re
import struct
import subprocess
import sys
from fractions import Fraction

CLANG = os.environ.get("CXX", "clang++")
CLANG_FLAGS = ["-std=c++17", "-O2", "-ffp-contract=off", "-fno-fast-math",
               "-fno-builtin-sinf", "-fno-builtin-cosf", "-fno-builtin-sin", "-fno-builtin-cos"]
# Added for code generation (the C++ driver of difftest.py, and moreLeancArgs of the Lean side),
# not needed for the AST: without it clang -O2 rewrites libm calls with constant arguments, e.g.
# powf(x, 0.5f) into an fsqrt-based sequence that differs from libm powf by 1 ulp (README.md,
# "Compilation assumptions").
CODEGEN_EXTRA = ["-fno-builtin"]


class Reject(Exception):
    """A construct outside the subset, with the AST node whose location is reported."""

    def __init__(self, node, construct):
        super().__init__(construct)
        self.node = node
        self.construct = construct


# ---------------------------------------------------------------------------------------------
# Locations. clang's JSON dumper omits "file" and "line" when they equal those of the previously
# printed location, so they are filled in by replaying the document in print order.

def fill_locations(tree):
    state = {"file": None, "line": None}

    def walk(o):
        if isinstance(o, dict):
            if "offset" in o and "col" in o:
                if "file" in o:
                    state["file"] = o["file"]
                if "line" in o:
                    state["line"] = o["line"]
                o["file"] = state["file"]
                o["line"] = state["line"]
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)

    walk(tree)


def expansion(loc):
    if not loc:
        return None
    if "expansionLoc" in loc:
        return loc["expansionLoc"]
    return loc


def node_loc(n):
    """The location reported for a node: a declaration's name, else the start of its range."""
    loc = expansion(n.get("loc")) if n.get("loc") else None
    if not loc or "line" not in loc:
        loc = expansion(n.get("range", {}).get("begin"))
    return loc


# ---------------------------------------------------------------------------------------------
# Types.

INT_TYPES = {
    "signed char": (8, True), "unsigned char": (8, False),
    "short": (16, True), "unsigned short": (16, False),
    "int": (32, True), "unsigned int": (32, False),
    "long": (64, True), "unsigned long": (64, False),
    "long long": (64, True), "unsigned long long": (64, False),
}

TYPEDEFS = {}       # typedef name -> underlying type spelling, from the TypedefDecls of the unit
RECORDS = {}        # qualified C++ name -> RecordInfo (translated structs and classes)
ENUMS = {}          # qualified C++ name -> EnumInfo
BOUNDARY = set()    # class names that are not translated (--boundary)
PARAM_CLASSES = {}  # class name -> C++ scalar type name (--param-class)
KEEP_GOING = [False]  # --keep-going: translate the member functions of a class with rejected members
AP_PARAM = [False]    # --ap-param: ArduPilot's AP_Param conventions (see README.md, "ArduPilot")
DROP = set()          # --drop: qualified names of functions whose calls are left out (logging, errors)
BOUNDARY_FN = set()   # --boundary-fn: qualified names of free functions whose results are inputs
REV_TYPEDEFS = {}     # desugared type spelling -> the unique typedef naming it
PARAM_STORAGE = {}    # parameter class of an enum type (AP_Enum<E>) -> the integer type it stores
OUTPUT_LOG = [False]  # --output-log: outputs are the boundary calls in order (Array Output), not last values
ARRAY_PARAMS = [False]  # --array-params: a `const T *` parameter read only by subscript is the caller's array
SITE_INPUTS = [False]   # --site-inputs: a const boundary call with non-constant arguments is one input per call site
BOUNDARY_CALL = set() # --boundary-call: member functions of translated classes whose calls are boundary calls
BOUNDARY_QUERY = set()  # --boundary-query: non-const member functions of boundary classes that only read (inputs, as const ones)
BOUNDARY_LIVE = set()   # --boundary-live: boundary classes whose reads are functions of the output log so far (README.md)
BOUNDARY_STATIC = set()  # --boundary-static: member functions of boundary classes that read nothing of their object: translated
SRC_ROOTS = []        # --src-root: source paths in comments and messages are shown relative to these
PKG_ROOT = os.path.dirname(os.path.abspath(__file__))   # the cpp2lean directory: other paths are shown relative to it
USE = []              # --use: library functions and member functions translated as if a translated file called them
ROOT_NS = [None]      # the file's namespace (the prefix of every name with --nest)
NEST = [False]        # --nest: classes are emitted inside the file's namespace (several translations in one Lean package)
TYPE_NAMES = {}       # --type-name: C++ class template specialization -> Lean name (when its typedef is not unique)
BIT1_FIELDS = set()   # decl ids of one-bit unsigned bit-fields (`uint8_t f : 1`): a write stores its value modulo 2


class CType:
    """A C++ type of the subset: arithmetic, a fixed-size array, a translated struct or class
    (`record`), an enum, a boundary class, or a parameter class."""

    def __init__(self, kind, bits=0, signed=False, usize=False, elem=None, n=0, info=None, name=None, args=()):
        self.kind, self.bits, self.signed, self.usize, self.elem, self.n = kind, bits, signed, usize, elem, n
        self.info, self.name = info, name
        self.args = tuple(args)     # kind "fun": the argument types after the output log; elem: the result

    def key(self):
        return (self.kind, self.bits, self.signed, self.usize, self.elem.key() if self.elem else None, self.n,
                id(self.info) if self.info else None, self.name, tuple(a.key() for a in self.args))

    def __eq__(self, o):
        return isinstance(o, CType) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    @property
    def lean(self):
        if self.kind == "float":
            return "Float32"
        if self.kind == "double":
            return "Float"
        if self.kind == "bool":
            return "Bool"
        if self.kind == "int":
            if self.usize:
                return "USize"
            return ("Int" if self.signed else "UInt") + str(self.bits)
        if self.kind == "array":
            return "Array " + self.elem.lean_atom
        if self.kind == "fun":
            # a live boundary read (--boundary-live): the value after the calls made so far
            return " → ".join(["Outputs"] + [a.lean_atom for a in self.args] + [self.elem.lean_atom])
        if self.kind == "record":
            return self.info.lean_type
        if self.kind == "enum":
            return self.info.lean
        if self.kind == "string":
            return "String"
        raise AssertionError(self.kind)

    @property
    def lean_atom(self):
        t = self.lean
        return "(" + t + ")" if " " in t else t

    @property
    def cname(self):
        if self.kind == "param":
            return pretty_type(self.name)
        if self.kind == "int":
            if self.usize:
                return "size_t"
            return ("int" if self.signed else "uint") + str(self.bits) + "_t"
        if self.kind == "array":
            return "%s[%d]" % (self.elem.cname, self.n)
        if self.kind in ("record", "enum"):
            return self.info.cxx
        if self.kind in ("boundary", "param"):
            return self.name
        if self.kind == "string":
            return "const char *"
        return self.kind

    def is_float(self):
        return self.kind in ("float", "double")

    def is_int(self):
        return self.kind == "int"

    def is_scalar(self):
        return self.kind in ("float", "double", "bool", "int", "enum")

    def under_cname(self):
        """The C++ name of an enum's underlying type (what the drivers print)."""
        return self.info.under.cname


FLOAT = CType("float")
DOUBLE = CType("double")
BOOL = CType("bool")
VOID = CType("void")
STRING = CType("string")    # `const char *` pointing to a string literal (README.md, "ArduPilot")


def collect_typedefs(tree):
    rev = {}

    def visit(n, scope_ok):
        for c in kids(n):
            if not isinstance(c, dict):
                continue
            if c.get("kind") in ("TypedefDecl", "TypeAliasDecl") and "name" in c:
                t = c["type"]
                d = norm_template_args(t.get("desugaredQualType", t["qualType"]))
                TYPEDEFS.setdefault(c["name"], d)
                if scope_ok:            # a namespace-scope typedef names the type for reading
                    rev.setdefault(d, set()).add(c["name"])
            visit(c, scope_ok and c.get("kind") in ("NamespaceDecl", "LinkageSpecDecl"))

    visit(tree, True)
    for d, names in rev.items():
        if len(names) == 1:
            REV_TYPEDEFS[d] = next(iter(names))


CHAR_ESCAPES = {"a": 7, "b": 8, "t": 9, "n": 10, "v": 11, "f": 12, "r": 13, "0": 0, "\\": 92, "'": 39, '"': 34, "?": 63}


def char_literal_value(lit_text):
    """The value of a C character literal such as `'\\a'` or `'\\x05'` (without the quotes)."""
    if not lit_text.startswith("\\"):
        return ord(lit_text)
    e = lit_text[1:]
    if e[0] == "x":
        return int(e[1:], 16)
    if e[0] in "01234567" and len(e) > 1:
        return int(e, 8)
    return CHAR_ESCAPES[e[0]]


def norm_template_args(name):
    """Integer template arguments that clang prints as character literals (a uint8_t 7 is `'\\a'`,
    `DerivativeFilter<float, '\\a'>`) are written as integers, as the specialization's own name has them."""
    return re.sub(r"'(\\[^']+|[^'\\])'", lambda m: str(char_literal_value(m.group(1))), name) if "'" in name else name


def pretty_type(spelling):
    """A type as a short name: its unique typedef (AP_Float, LowPassFilterFloat), else itself."""
    return REV_TYPEDEFS.get(spelling, spelling)


def name_part(spelling):
    """A type spelling as part of a Lean identifier."""
    return re.sub(r"\W+", "_", pretty_type(spelling)).strip("_")


def strip_quals(s):
    s = s.strip()
    words = s.split()
    if "volatile" in words:
        return None, "volatile"
    s = " ".join(w for w in words if w not in ("const", "constexpr"))
    return s, None


def strip_tag(s):
    for tag in ("struct ", "class ", "enum ", "union "):
        if s.startswith(tag):
            return s[len(tag):], tag.strip()
    return s, None


def parse_type_str(sugar, desugared, node):
    s, bad = strip_quals(sugar)
    if bad:
        raise Reject(node, "volatile type `%s`" % sugar)
    d, _ = strip_quals(desugared)
    if re.match(r"^const char ?\*$", desugared.strip()) or re.match(r"^const char ?\*$", sugar.strip()):
        return STRING
    if "*" in d or "&" in d:
        raise Reject(node, "pointer or reference type `%s`" % sugar)
    m = re.match(r"^(.*?)\s*\[(\d+)\]$", d)
    if m:
        ms = re.match(r"^(.*?)\s*\[(\d+)\]$", s)
        elem = parse_type_str(ms.group(1) if ms else m.group(1), m.group(1), node)
        if elem.kind == "array":
            raise Reject(node, "multidimensional array `%s`" % sugar)
        if elem.kind in ("boundary", "param") or (elem.kind == "record" and elem.info.kind != "plain" and not elem.info.lib):
            raise Reject(node, "array of class objects `%s` (arrays of scalars, enums, plain structs and library value classes only)" % sugar)
        return CType("array", elem=elem, n=int(m.group(2)))
    if "[" in d:
        raise Reject(node, "array of unknown bound `%s`" % sugar)
    if d == "float":
        return FLOAT
    if d == "double":
        return DOUBLE
    if d == "bool":
        return BOOL
    if d in INT_TYPES:
        bits, signed = INT_TYPES[d]
        usize = s in ("size_t", "std::size_t")
        return CType("int", bits, signed, usize)
    if d == "void":
        return VOID
    base = d[5:] if d.startswith("std::") else d
    if base in TYPEDEFS and TYPEDEFS[base] != d:
        return parse_type_str(sugar, TYPEDEFS[base], node)
    if d in ("char", "wchar_t", "char16_t", "char32_t", "char8_t"):
        raise Reject(node, "character type `%s` (string handling)" % sugar)
    if d == "long double":
        raise Reject(node, "type `long double`")
    name, tag = strip_tag(d)
    name = norm_template_args(name)
    if tag == "union":
        raise Reject(node, "union `%s`" % sugar)
    short = name.split("::")[-1]
    sname = strip_tag(s)[0]          # the type as written (a typedef such as AP_Float)
    if AP_PARAM[0]:
        m = re.match(r"^AP_ParamT<(.+), AP_PARAM_\w+>$", name)
        if m and name not in PARAM_CLASSES:
            PARAM_CLASSES[name] = m.group(1)
        m = re.match(r"^AP_Enum(16)?<(.+)>$", name)
        if m and name not in PARAM_CLASSES:
            # AP_Enum<E> (an AP_Int8 read as E through `operator const E`): a parameter of type E,
            # stored in int8_t (AP_Enum16: int16_t)
            PARAM_CLASSES[name] = m.group(2)
            PARAM_STORAGE[name] = "int16_t" if m.group(1) else "int8_t"
    for nm in (name, short, sname, sname.split("::")[-1]):
        if nm in BOUNDARY:
            return CType("boundary", name=nm)
        if nm in PARAM_CLASSES:
            return CType("param", name=nm)
    if name in RECORDS:
        return CType("record", info=RECORDS[name])
    if name in ENUMS:
        return CType("enum", info=ENUMS[name])
    # clang spells a member type used inside its class unqualified; accept a unique short name
    rs = [r for k, r in RECORDS.items() if k.split("::")[-1] == name]
    es = [e for k, e in ENUMS.items() if k.split("::")[-1] == name]
    if len(rs) + len(es) == 1:
        return CType("record", info=rs[0]) if rs else CType("enum", info=es[0])
    if tag is not None or re.match(r"^[A-Za-z_][\w:]*$", name):
        raise Reject(node, "type `%s` (not translated: not defined in the translated files, not a --boundary or --param-class)" % sugar)
    raise Reject(node, "type `%s`" % sugar)


def ctype_of(node, key="type"):
    t = node.get(key)
    if t is None:
        raise Reject(node, "expression without a type")
    return parse_type_str(t["qualType"], t.get("desugaredQualType", t["qualType"]), node)


def decl_type(node):
    """(CType, reference kind) of a declaration: kind is None, 'const' (const T&) or 'mut' (T&)."""
    t = node["type"]
    q, dq = t["qualType"].rstrip(), t.get("desugaredQualType", t["qualType"]).rstrip()
    if q.endswith("&&"):
        raise Reject(node, "rvalue reference `%s`" % q)
    if q.endswith("&") and "*" not in q:
        base_q = q[:-1].strip()
        base_d = dq[:-1].strip() if dq.endswith("&") else dq
        is_const = base_q.startswith("const ") or base_q.endswith(" const")
        return parse_type_str(base_q, base_d, node), ("const" if is_const else "mut")
    return parse_type_str(q, dq, node), None


def fn_return_type(fn):
    t = fn["type"]
    sugar = t["qualType"]
    desug = t.get("desugaredQualType", sugar)
    if sugar.startswith("typename ") and "desugaredQualType" not in t:
        # a template specialization whose return type clang spells only through the template's
        # dependent name (AP_Math's is_equal: `typename std::enable_if<..., bool>::type`): clang
        # has converted every returned expression to the return type, so it is their type
        ret = next((m for m in walk(fn) if m.get("kind") == "ReturnStmt" and kids(m)), None)
        if ret is not None and any(c.get("kind") == "TemplateArgument" for c in kids(fn)):
            return ctype_of(kids(ret)[0])
    if "..." in desug:
        raise Reject(fn, "variadic function")
    r = sugar.split("(")[0].strip()
    rd = desug.split("(")[0].strip()
    if r == "auto" and "->" in sugar:            # trailing return type (e.g. AP_Math's MIN)
        r = rd = sugar.rsplit("->", 1)[1].strip()
        if r.startswith("decltype"):
            if "desugaredQualType" not in t or desug.split("(")[0].strip() == "auto":
                # the type of the returned expression (AP_Math's MIN/MAX: `decltype(one < two ? one : two)`)
                ret = next((m for m in walk(fn) if m.get("kind") == "ReturnStmt" and kids(m)), None)
                if ret is None:
                    raise Reject(fn, "function with a `decltype` return type and no return")
                return ctype_of(kids(ret)[0])
            r = rd = desug.split("(")[0].strip()
    if r.endswith("&"):
        # a function returning a reference returns the value in Lean (README.md, "ArduPilot")
        if r.endswith("&&"):
            raise Reject(fn, "function returning an rvalue reference `%s`" % r)
        t2 = parse_type_str(r[:-1].strip(), rd[:-1].strip() if rd.endswith("&") else rd, fn)
        if t2.kind == "param":
            pt = PARAM_CLASSES.get(t2.name) or PARAM_CLASSES.get(t2.name.split("::")[-1])
            t2 = parse_type_str(pt, pt, fn)
        if t2.kind == "boundary":
            raise Reject(fn, "function returning a reference to a boundary object")
        return t2
    return parse_type_str(r, rd, fn)


def returns_reference(fn):
    q = fn["type"]["qualType"]
    return q.split("(")[0].strip().endswith("&")


def array_view_type(p):
    """For a parameter `const T *p` with T a number or plain struct: the Lean array type of what
    the caller passes (CType array of unknown length), else None. Uses other than `p[i]` are
    rejected where they occur."""
    q = p["type"].get("desugaredQualType", p["type"]["qualType"]).strip()
    m = re.match(r"^const (?:struct |class )?(.+?) ?\*$", q)
    if not m or m.group(1) in ("char",):
        return None
    try:
        elem = parse_type_str(m.group(1), m.group(1), p)
    except Reject:
        return None
    if not (elem.is_scalar() or (elem.kind == "record" and elem.info.kind == "plain")):
        return None
    return CType("array", elem=elem, n=0)


def all_zero(t, node):
    """The value whose bytes are all zero (memset), field by field: not the default member
    initializers."""
    if t.kind == "record":
        fs = [f for f in t.info.all_fields() if f.category == "state"]
        if not fs:
            return V("{}", ATOM)
        return V("{ %s }" % ", ".join("%s := %s" % (f.lean, all_zero(f.t, node).text) for f in fs), ATOM)
    if t.kind == "array":
        return app("Array.replicate", V(str(t.n), ATOM), all_zero(t.elem, node))
    return zero_of(t, node)


def lean_string(text):
    """A Lean string literal with the characters of a C++ string literal's value."""
    out = []
    for ch in text:
        if ch in "\\\"":
            out.append("\\" + ch)
        elif 32 <= ord(ch) < 127:
            out.append(ch)
        else:
            out.append("\\u{%x}" % ord(ch))
    return '"%s"' % "".join(out)


def zero_of(t, node):
    """The value of a zero-filled object of type t (ArduPilot zero-fills its objects)."""
    if t.kind == "string":
        raise Reject(node, "`const char *` without a string literal (its zero value is a null pointer, which is not a string)")
    if t.kind in ("float", "double"):
        return lit("0.0", t)
    if t.kind == "int":
        return lit("0", t)
    if t.kind == "bool":
        return V("false", ATOM)
    if t.kind == "enum":
        zero = [e for e, v in t.info.values if v == 0]
        if not zero:
            raise Reject(node, "enum `%s` has no enumerator with value 0 (the value of a zero-filled member)" % t.info.cxx)
        return V("%s.%s" % (t.info.lean, t.info.ctor_names[zero[0]]), ATOM)
    if t.kind == "array":
        return app("Array.replicate", V(str(t.n), ATOM), zero_of(t.elem, node))
    if t.kind == "record":
        return V("{}", ATOM)
    if t.kind == "fun":
        return V("fun%s => %s" % (" _" * (1 + len(t.args)), zero_of(t.elem, node).text), LOW)
    raise Reject(node, "no zero value for `%s`" % t.cname)


# ---------------------------------------------------------------------------------------------
# Lean names and precedence-aware printing.

LEAN_KEYWORDS = {
    "fun", "in", "have", "show", "from", "then", "match", "with", "at", "by", "def", "theorem", "where",
    "end", "structure", "instance", "section", "open", "import", "export", "mut", "unless", "finally",
    "macro", "syntax", "deriving", "variable", "universe", "axiom", "example", "abbrev", "opaque",
    "local", "scoped", "calc", "suffices", "obtain", "Type", "Prop", "Sort", "nomatch", "nofun", "let",
    "do", "if", "else", "for", "return", "break", "continue", "try", "catch", "namespace", "class",
    "private", "protected", "partial", "unsafe", "noncomputable", "attribute", "mutual", "inductive",
    "forall", "exists", "this", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "omit",
    "include", "set_option", "termination_by", "decreasing_by", "fun", "λ", "Σ", "Π",
}
# Names the emitted code uses unqualified; a C++ identifier with one of these names would capture it.
RESERVED = {"decide", "pure", "true", "false", "not", "and", "or", "Id"}
# In member functions also the object components.
RESERVED_IN_METHODS = {"s", "p", "inp", "own"}


def lean_ident(name, node):
    if name in RESERVED:
        raise Reject(node, "identifier `%s` (reserved: the emitted Lean uses this name)" % name)
    if name in LEAN_KEYWORDS:
        return "«%s»" % name
    return name


def lean_field(name, node):
    """A structure field, constructor or method name (each lives in its own namespace, so only
    Lean keywords and the generated `toInt`/`ofInt` need quoting)."""
    if name in LEAN_KEYWORDS or name in ("toInt", "ofInt"):
        return "«%s»" % name
    return name


ATOM, APP, NEG, SHIFT, MUL, ADD, BAND, BXOR, BOR, CMP, NOT, AND, OR, LOW = \
    1100, 1000, 75, 75, 70, 65, 60, 58, 55, 50, 40, 35, 30, 0


class V:
    """A translated expression: Lean text and the precedence at which it parses."""

    def __init__(self, text, prec):
        self.text, self.prec = text, prec

    def at(self, need):
        return self.text if self.prec >= need else "(" + self.text + ")"


def app(fn, *args):
    return V(fn + "".join(" " + a.at(ATOM) for a in args), APP)


def lit(text, t):
    return V("(%s : %s)" % (text, t.lean), ATOM)


# ---------------------------------------------------------------------------------------------
# Exact floating-point literal checking.

def round_to_binary(fr, p, emin, emax):
    """Round the rational fr to the nearest binary floating-point value with p significand bits,
    ties to even; returns a Fraction, or None for overflow to infinity."""
    if fr == 0:
        return Fraction(0)
    sign = -1 if fr < 0 else 1
    a = abs(fr)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** e > a:
        e -= 1
    while Fraction(2) ** (e + 1) <= a:
        e += 1
    e = max(e, emin)
    q = Fraction(2) ** (e - (p - 1))
    m = a / q
    fl = m.numerator // m.denominator
    rem = m - fl
    if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and fl % 2 == 1):
        fl += 1
    v = fl * q
    if v >= Fraction(2) ** (emax + 1):
        return None
    return sign * v


def float_bits(fr, t):
    if t.kind == "float":
        v = round_to_binary(fr, 24, -126, 127)
        f = float("inf") * (1 if fr > 0 else -1) if v is None else float(v)
        return struct.unpack(">I", struct.pack(">f", f))[0]
    v = round_to_binary(fr, 53, -1022, 1023)
    f = float("inf") * (1 if fr > 0 else -1) if v is None else float(v)
    return struct.unpack(">Q", struct.pack(">d", f))[0]


def parse_c_float(text):
    """Exact rational value of a C++ floating literal (decimal or hexadecimal), suffix removed."""
    s = text.replace("'", "")
    s = re.sub(r"[fFlL]$", "", s)
    if s.lower().startswith("0x"):
        m = re.match(r"^0[xX]([0-9a-fA-F]*)(?:\.([0-9a-fA-F]*))?[pP]([+-]?\d+)$", s)
        if not m:
            return None, s
        ip, fp, ex = m.group(1) or "", m.group(2) or "", int(m.group(3))
        mant = int((ip + fp) or "0", 16)
        return Fraction(mant) * Fraction(2) ** (ex - 4 * len(fp)), s
    try:
        return Fraction(s), s
    except ValueError:
        return None, s


def lean_decimal(s):
    """Lean scientific-literal spelling of a C++ decimal floating literal (suffix removed)."""
    m = re.match(r"^(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$", s)
    ip, fp, ex = m.group(1) or "0", m.group(2), m.group(3)
    out = ip + "." + (fp if fp else "0")
    if ex is not None:
        out += "e" + ex
    return out


# The floating constants of <cmath> that clang implements as builtin calls: name -> (type, bits).
# NAN is __builtin_nanf(""), INFINITY is __builtin_inff(), HUGE_VALF is __builtin_huge_valf().
BUILTIN_CONSTS = {
    "__builtin_nanf": ("float", 0x7fc00000), "__builtin_nan": ("double", 0x7ff8000000000000),
    "__builtin_inff": ("float", 0x7f800000), "__builtin_inf": ("double", 0x7ff0000000000000),
    "__builtin_huge_valf": ("float", 0x7f800000), "__builtin_huge_val": ("double", 0x7ff0000000000000),
}


# ---------------------------------------------------------------------------------------------
# <cmath>: (name, parameter types, result type) -> Lean function. The float overloads without the
# f suffix are libc++'s std:: overloads, which call the same libm functions (__builtin_sinf, ...).

def _sig(ps, r):
    return (tuple(ps), r)


F, D = "float", "double"
CMATH = {}
for base, lf in [("sin", "sin"), ("cos", "cos"), ("tan", "tan"), ("asin", "asin"), ("acos", "acos"),
                 ("atan", "atan"), ("sqrt", "sqrt"), ("fabs", "abs"), ("exp", "exp"), ("log", "log"),
                 ("floor", "floor"), ("ceil", "ceil"), ("round", "round"), ("log10", "log10"),
                 ("log2", "log2"), ("exp2", "exp2"), ("sinh", "sinh"), ("cosh", "cosh"), ("tanh", "tanh")]:
    CMATH[(base + "f",) + _sig([F], F)] = "Float32." + lf
    CMATH[(base,) + _sig([F], F)] = "Float32." + lf
    CMATH[(base,) + _sig([D], D)] = "Float." + lf
CMATH[("abs",) + _sig([F], F)] = "Float32.abs"
CMATH[("abs",) + _sig([D], D)] = "Float.abs"
for base, lf in [("atan2", "atan2"), ("pow", "pow")]:
    CMATH[(base + "f",) + _sig([F, F], F)] = "Float32." + lf
    CMATH[(base,) + _sig([F, F], F)] = "Float32." + lf
    CMATH[(base,) + _sig([D, D], D)] = "Float." + lf
for base in ["fmax", "fmin"]:
    CMATH[(base + "f",) + _sig([F, F], F)] = "CppLibm." + base + "f"
    CMATH[(base,) + _sig([F, F], F)] = "CppLibm." + base + "f"
    CMATH[(base,) + _sig([D, D], D)] = "CppLibm." + base
for base in ["fmod"]:
    CMATH[(base + "f",) + _sig([F, F], F)] = "CppLibm." + base + "f"
    CMATH[(base,) + _sig([F, F], F)] = "CppLibm." + base + "f"
    CMATH[(base,) + _sig([D, D], D)] = "CppLibm." + base
# libc++'s overloads of the two-argument functions for mixed float/double arguments
# (`fmod(double, float)`, ArduPilot's `fmod(angle, 360.0)` under -cl-single-precision-constant):
# both arguments are converted to double (exact) and the double function is called.
for base, lf in [("atan2", "Float.atan2"), ("pow", "Float.pow"), ("fmod", "CppLibm.fmod"), ("fmax", "CppLibm.fmax"),
                 ("fmin", "CppLibm.fmin")]:
    for ps in ([D, F], [F, D]):
        CMATH[(base,) + _sig(ps, D)] = (lf, "double")
for base, lf in [("isnan", "isNaN"), ("isinf", "isInf"), ("isfinite", "isFinite")]:
    CMATH[(base,) + _sig([F], "bool")] = "Float32." + lf
    CMATH[(base,) + _sig([D], "bool")] = "Float." + lf

COMPARISON_MACROS = {"isgreater": ">", "isgreaterequal": "≥", "isless": "<", "islessequal": "≤"}

CPPLIBM = """/-!
Generated by cpp2lean. C math functions that core Lean 4.33 does not expose, declared as externs
of the C library functions of the same name (the same mechanism core uses for `Float32.sin`,
which is `@[extern "sinf"]`). Like core's libm externs, they are opaque to the kernel.
-/

namespace CppLibm

/-- C `fmaxf`. -/
@[extern "fmaxf"] opaque fmaxf : Float32 → Float32 → Float32
/-- C `fminf`. -/
@[extern "fminf"] opaque fminf : Float32 → Float32 → Float32
/-- C `fmax`. -/
@[extern "fmax"] opaque fmax : Float → Float → Float
/-- C `fmin`. -/
@[extern "fmin"] opaque fmin : Float → Float → Float
/-- C `fmodf`. -/
@[extern "fmodf"] opaque fmodf : Float32 → Float32 → Float32
/-- C `fmod`. -/
@[extern "fmod"] opaque fmod : Float → Float → Float

end CppLibm
"""


# ---------------------------------------------------------------------------------------------
# Conversions: every cast node becomes the named Lean conversion.

def int_conv(v, s, d):
    """C++ integral conversion s -> d (both integer types, d != s): the value modulo 2^bits(d),
    as Lean's width conversions compute it (sign extension from a signed source, zero extension
    from an unsigned one, truncation when narrowing)."""
    if s.usize:
        v, s = app("USize.toUInt64", v), CType("int", 64, False)
    if d.usize:
        v = int_conv(v, s, CType("int", 64, False)) if s != CType("int", 64, False) else v
        return app("UInt64.toUSize", v)
    if s == d:
        return v
    pre = "Int" if s.signed else "UInt"
    if s.bits != d.bits:
        v = app("%s%d.to%s%d" % (pre, s.bits, pre, d.bits), v)
    if s.signed != d.signed:
        v = app("%s%d.to%s%d" % (pre, d.bits, "UInt" if s.signed else "Int", d.bits), v)
    return v


def conv(v, s, d, node):
    """The Lean conversion from C++ type s to C++ type d, applied to v."""
    if s == d:
        return v
    if s.kind == "enum":
        return conv(app("%s.toInt" % s.info.lean, v), s.info.under, d, node)
    if d.kind == "enum":
        e = d.info
        if not (s.is_int() or s.kind == "bool"):
            raise Reject(node, "conversion from `%s` to enum `%s`" % (s.cname, e.cxx))
        e.used_ofInt = True
        return app("%s.ofInt" % e.lean, conv(v, s, e.under, node))
    if s.kind == "bool":
        if d.is_int():
            return V("if %s then %s else %s" % (v.text, lit("1", d).text, lit("0", d).text), LOW)
        if d.is_float():
            return V("if %s then %s else %s" % (v.text, lit("1.0", d).text, lit("0.0", d).text), LOW)
    if d.kind == "bool":
        if s.is_int():
            return V("%s != %s" % (v.at(CMP + 1), lit("0", s).text), CMP)
        if s.is_float():
            return V("%s != %s" % (v.at(CMP + 1), lit("0.0", s).text), CMP)
    if s.kind == "float" and d.kind == "double":
        return app("Float32.toFloat", v)
    if s.kind == "double" and d.kind == "float":
        return app("Float.toFloat32", v)
    if s.is_int() and d.is_float():
        src = "USize" if s.usize else ("Int" if s.signed else "UInt") + str(s.bits)
        return app("%s.to%s" % (src, "Float32" if d.kind == "float" else "Float"), v)
    if s.is_float() and d.is_int():
        return app("%s.to%s" % (s.lean, d.lean), v)
    if s.is_int() and d.is_int():
        return int_conv(v, s, d)
    raise Reject(node, "conversion from `%s` to `%s`" % (s.cname, d.cname))


CAST_KINDS = {"FloatingCast", "IntegralCast", "IntegralToFloating", "FloatingToIntegral",
              "IntegralToBoolean", "FloatingToBoolean", "NoOp", "LValueToRValue"}


# ---------------------------------------------------------------------------------------------
# AST helpers.

def kids(n):
    return n.get("inner", [])


def strip_parens(n):
    while n.get("kind") in ("ParenExpr", "ConstantExpr"):
        n = kids(n)[0]
    return n


def strip_object(n):
    """An lvalue or object expression without the parentheses and the casts clang inserts
    around it (derived to base, added const, lvalue to rvalue)."""
    while n.get("kind") == "ParenExpr" or (n.get("kind") == "ImplicitCastExpr" and n.get("castKind") in (
            "NoOp", "UncheckedDerivedToBase", "DerivedToBase", "LValueToRValue") and not n.get("conversionFunc")):
        n = kids(n)[0]
    return n


def walk(n):
    yield n
    for c in kids(n):
        if isinstance(c, dict):
            yield from walk(c)


def lvalue_root(n):
    """The DeclRefExpr at the root of an lvalue chain (x, x.f, x[i], x.f[i].g), or None."""
    n = strip_object(n)
    while n.get("kind") in ("MemberExpr", "ArraySubscriptExpr"):
        if n.get("kind") == "ArraySubscriptExpr":
            b = kids(n)[0]
            n = strip_object(kids(b)[0]) if b.get("castKind") == "ArrayToPointerDecay" else strip_object(b)
        else:
            n = strip_object(kids(n)[0])
    return n if n.get("kind") == "DeclRefExpr" else None


def referenced_decls(n):
    return {m["referencedDecl"]["id"] for m in walk(n) if m.get("kind") == "DeclRefExpr"}


OPERATOR_WORDS = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod", "==": "eq", "!=": "ne",
                  "<": "lt", ">": "gt", "<=": "le", ">=": "ge", "+=": "add_assign", "-=": "sub_assign",
                  "*=": "mul_assign", "/=": "div_assign", "%=": "mod_assign", "[]": "index", "^": "xor",
                  "&": "and", "|": "or", "!": "not"}


def operator_word(name):
    """The Lean name part of an overloaded operator (`operator*` is `op_mul`), or None."""
    if not name or not name.startswith("operator"):
        return None
    sym = name[len("operator"):].strip()
    return ("op_" + OPERATOR_WORDS[sym]) if sym in OPERATOR_WORDS else None


def operator_name(n):
    callee = strip_parens(kids(n)[0])
    if callee.get("kind") == "ImplicitCastExpr":
        callee = kids(callee)[0]
    return callee.get("referencedDecl", {}).get("name")


WHILE_BAD = ("`while` loop whose trip count is not a compile-time constant (required: `while (i op C)` "
             "with i declared earlier in the block with a constant initializer, not assigned before the "
             "loop, stepped only by the body's last statement `i++ / i-- / i += C`, and no `continue`)")
DO_BAD = ("`do`/`while` loop whose trip count is not a compile-time constant (required: `do { ...; i++; } "
          "while (i op C)` with i declared earlier in the block with a constant initializer, not assigned "
          "before the loop, stepped only by the body's last statement, and no `continue`)")
FOR_BAD = ("`for` loop whose trip count is not a compile-time constant (required: `for (T i = C0; i op C1; "
           "i++ / i-- / i += C)` with constants C0, C1, C and no assignment to i in the body)")

DIVERGE = None  # definite-assignment state after return/break/continue: every variable


class Path:
    """An lvalue: a root (('var', id) a local or parameter, ('s',) the state, ('p',) the
    parameters) and a list of steps ('f', field), ('i', Nat index V) and ('v', (pairs, S)): a
    layout-prefix view of the object as a value of structure S (Vector3's `xy()`, `*(Vector2<T> *)
    this`), pairs mapping each field of S to the object's field it views."""

    def __init__(self, root, root_text, steps, t):
        self.root, self.root_text, self.steps, self.t = root, root_text, steps, t

    def text(self):
        out = self.root_text
        for kind, x in self.steps:
            if kind == "v":
                out = "({ %s } : %s)" % (", ".join("%s := %s.%s" % (th, out, mi) for th, mi in x[0]), x[1])
            else:
                out += ("." + x) if kind == "f" else ("[%s]!" % x.text)
        return out

    def extend(self, step, t):
        if self.steps and self.steps[-1][0] == "v" and step[0] == "f":
            # a field of the view (`v.xy().x`) is the viewed field of the object
            mine = dict(self.steps[-1][1][0])[step[1]]
            return Path(self.root, self.root_text, self.steps[:-1] + [("f", mine)], t)
        return Path(self.root, self.root_text, self.steps + [step], t)


SIMPLE = re.compile(r"^[\w'.«»]+$")


def update_text(base, steps, value):
    """Lean text of `base` with the element at `steps` replaced by `value` (a V): nested fields
    with `{ b with f.g := v }`, array elements with `Array.set!`."""
    if not steps:
        return value.text
    fields = []
    i = 0
    while i < len(steps) and steps[i][0] == "f":
        fields.append(steps[i][1])
        i += 1
    if i < len(steps) and steps[i][0] == "v":
        # a write through a layout-prefix view: each viewed field from the value (which is pure,
        # so naming it twice reads the same value; callers pass a variable)
        if i != len(steps) - 1:
            raise AssertionError("steps after a view")
        val = value.text if SIMPLE.match(value.text) else "(" + value.text + ")"
        pre = "".join(f + "." for f in fields)
        return "{ %s with %s }" % (base, ", ".join("%s%s := %s.%s" % (pre, mi, val, th) for th, mi in steps[i][1][0]))
    if fields:
        path = ".".join(fields)
        inner = update_text(base + "." + path, steps[i:], value) if i < len(steps) else value.text
        return "{ %s with %s := %s }" % (base, path, inner)
    idx = steps[0][1]
    inner = update_text("%s[%s]!" % (base, idx.text), steps[1:], value)
    if not (SIMPLE.match(inner) or (inner.startswith("(") and inner.endswith(")") and steps[1:] == [] and value.prec >= ATOM)):
        inner = "(" + inner + ")"
    return "%s.set! %s %s" % (base if SIMPLE.match(base) else "(" + base + ")", idx.at(ATOM), inner)


class Body:
    """Translates one function, method or constructor body (or one constant initializer) into
    lines of a Lean do block. In a method of context `ctx`, `this` is the state `s`, the
    parameters `p` and the boundary inputs `inp`."""

    def __init__(self, unit, fn=None, ctx=None, home=None):
        self.u = unit
        self.fn = fn
        self.ctx = ctx              # Context of the class whose method this is, or None
        self.home = home            # the Lean namespace the emitted code lives in
        self.vars = {}              # decl id -> (lean name, CType)
        self.mutable = set()        # decl ids assigned after their declaration
        self.uninit = set()         # decl ids declared without an initializer
        self.da = set()             # definitely assigned members of uninit; DIVERGE after a jump
        self.ntemp = 0
        self.loops = []             # stack of "for", "while", "do", "switch" for break/continue
        self.uses_libm = False
        self.declared = []          # (decl id, Lean name) of parameters and local bindings
        self.read = set()           # decl ids the emitted Lean reads
        self.reads = set()          # of "s", "p", "inp": what the body reads of the object
        self.writes = set()         # of "s", "p"
        self.outs = []              # (decl id, Lean name, CType) of non-const reference parameters
        self.rets = []              # value text of each `return`, filled in by finish()
        self.void = False
        self.deps = set()           # ids of free functions, constants and contexts used
        self.param_vars = set()     # parameters of a --param-class type (their value is the scalar)
        self.discard_node = None    # the call of the expression statement being translated (its value is discarded)
        self.loop_only = set()      # counters declared before the `for` loops that initialize them
        self.array_views = set()    # `const T *` parameters read only by subscript (arrays in Lean)
        self.boundary_locals = {}   # local references bound to boundary objects -> the object's name
        self.case_exited = False    # the switch case being translated has an `if (c) { ...; break; }` exit
        self.var_views = False      # resolve_path: a view (`v.xy()`) of a variable is a path (reference arguments of live reads)
        self.aliases = {}           # reference parameter id -> Path of the member of this object it is bound to (Context.method alias)
        self.live_refs = {}         # local reference id -> the live boundary read it names (read again at each use)
        self.nullable = {}          # nullable out-pointer parameter id -> the Lean name of its flag (`roll'given`)

    def temp(self):
        self.ntemp += 1
        return "t'%d" % self.ntemp

    def ident(self, name, node):
        if self.ctx is not None and name in RESERVED_IN_METHODS:
            raise Reject(node, "identifier `%s` in a member function (reserved: the state, parameters and inputs)" % name)
        return lean_ident(name, node)

    def qual(self, ns, name):
        """`name` in namespace `ns`, written as seen from this body's namespace."""
        return name if ns == self.home else "%s.%s" % (ns, name)

    def assigned(self, n):
        """Ids of the local variables a subtree writes: assignment, compound assignment, ++/--
        (also through a member or element), as an argument for a non-const reference parameter,
        or as the object of a non-const method."""
        out = set()
        for m in walk(n):
            k = m.get("kind")
            targets = []
            if k == "BinaryOperator" and m.get("opcode") == "=":
                targets.append(kids(m)[0])
            elif k == "CompoundAssignOperator":
                targets.append(kids(m)[0])
            elif k == "UnaryOperator" and m.get("opcode") in ("++", "--"):
                targets.append(kids(m)[0])
            elif k == "CXXOperatorCallExpr" and len(kids(m)) == 3 and operator_name(m) == "operator=":
                targets.append(kids(m)[1])
            elif k == "CXXOperatorCallExpr" and len(kids(m)) >= 2:
                # a non-const member operator (`v /= theta`, `v += w`) writes its first operand
                c = strip_parens(kids(m)[0])
                if c.get("kind") == "ImplicitCastExpr":
                    c = strip_parens(kids(c)[0])
                od = self.u.decl(c.get("referencedDecl", {}).get("id"))
                if od is not None and od.get("kind") == "CXXMethodDecl" and not od["type"]["qualType"].rstrip().endswith("const"):
                    targets.append(kids(m)[1])
            elif k in ("CallExpr", "CXXMemberCallExpr", "CXXConstructExpr"):
                callee = None
                args = kids(m)[1:] if k != "CXXConstructExpr" else kids(m)
                if k == "CallExpr":
                    c = strip_parens(kids(m)[0])
                    if c.get("kind") == "ImplicitCastExpr":
                        c = strip_parens(kids(c)[0])
                    callee = self.u.decl(c.get("referencedDecl", {}).get("id"))
                elif k == "CXXMemberCallExpr":
                    me = strip_parens(kids(m)[0])
                    callee = self.u.decl(me.get("referencedMemberDecl"))
                    q = callee["type"]["qualType"] if callee else ""
                    if callee is not None and not q.rstrip().endswith("const"):
                        targets.append(kids(me)[0])
                if callee is not None:
                    ps = [p for p in kids(callee) if p.get("kind") == "ParmVarDecl"]
                    for a, p in zip(args, ps):
                        q = p["type"]["qualType"].rstrip()
                        if q.endswith("&") and not q.endswith("&&") and not q.startswith("const "):
                            targets.append(a)
                        sa = strip_object(a)
                        if q.endswith("*") and not q.startswith("const ") and sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&":
                            targets.append(kids(sa)[0])     # `&x` for a (nullable) out-pointer parameter
            for t in targets:
                r = lvalue_root(t)
                if r is not None:
                    out.add(r["referencedDecl"]["id"])
        return out

    # -- expressions ------------------------------------------------------------------------
    # expr(n) returns (pre, V): pre is a list of do-block lines (relative indentation) that
    # perform the side effects of n in clang's evaluation order, and V is the value of n.

    def operands(self, nodes):
        """Translate operands left to right; if a later operand has side effects, the earlier
        values are bound to temporaries first so they are read before those effects."""
        return self.sequence([self.expr(c) for c in nodes])

    def sequence(self, res):
        pre, vals = [], []
        for i, (p, v) in enumerate(res):
            pre += p
            if v is not None and any(res[j][0] for j in range(i + 1, len(res))) and not self.is_constant(v):
                t = self.temp()
                pre.append("let %s := %s" % (t, v.text))
                v = V(t, ATOM)
            vals.append(v)
        return pre, vals

    @staticmethod
    def is_constant(v):
        return re.match(r"^\(?-?\(?[0-9.e+-]+ : \w+\)\)?$", v.text) is not None

    def expr(self, n):
        k = n.get("kind")
        h = getattr(self, "e_" + str(k), None)
        if h is None:
            raise Reject(n, self.describe(n))
        return h(n)

    def describe(self, n):
        k = n.get("kind")
        names = {
            "CXXNewExpr": "`new`", "CXXDeleteExpr": "`delete`", "CXXThrowExpr": "exception (`throw`)",
            "StringLiteral": "string literal (string handling)", "CharacterLiteral": "character literal",
            "CXXThisExpr": "`this` used as a value (only member access through `this` is translated)",
            "LambdaExpr": "lambda", "UnaryExprOrTypeTraitExpr": "`sizeof`/`alignof`",
            "InitListExpr": "initializer list outside an array declaration",
            "GNUNullExpr": "null pointer", "CXXNullPtrLiteralExpr": "null pointer",
            "CompoundLiteralExpr": "compound literal", "StmtExpr": "statement expression",
            "CXXTemporaryObjectExpr": "temporary object", "CXXDynamicCastExpr": "`dynamic_cast`",
            "CXXTypeidExpr": "`typeid`", "CXXStdInitializerListExpr": "`std::initializer_list`",
            "CXXPseudoDestructorExpr": "destructor call", "CXXUnresolvedConstructExpr": "uninstantiated template",
        }
        return names.get(k, "expression `%s`" % k)

    def e_ParenExpr(self, n):
        # The C++ parentheses are kept, so the Lean reads like the source.
        pre, v = self.expr(kids(n)[0])
        if v is None:
            return pre, v
        return pre, V("(%s)" % v.text, ATOM) if v.prec < ATOM else v

    def e_ConstantExpr(self, n):
        return self.expr(kids(n)[0])

    def transparent(self, n):
        return self.expr(kids(n)[0])

    e_MaterializeTemporaryExpr = transparent
    e_ExprWithCleanups = transparent
    e_CXXBindTemporaryExpr = transparent
    e_CXXDefaultArgExpr = transparent
    e_CXXDefaultInitExpr = transparent

    def e_InitListExpr(self, n):
        """`{a, b, c}` for a plain struct: its fields in declaration order (an element of a constant
        table such as AP_MotorsMatrix's `MotorDef motors[]`)."""
        t = ctype_of(n)
        if t.kind != "record" or t.info.kind != "plain":
            raise Reject(n, self.describe(n))
        fields = [f for f in t.info.all_fields() if f.category == "state"]
        vals = kids(n)
        if n.get("array_filler") or len(vals) != len(fields):
            raise Reject(n, "initializer list for `%s` with %d values for %d members" % (t.cname, len(vals), len(fields)))
        pre, vs = self.operands(vals)
        return pre, V("{ %s }" % ", ".join("%s := %s" % (f.lean, v.text) for f, v in zip(fields, vs)), ATOM)

    def array_size(self, n):
        """`sizeof(a) / sizeof(a[0])` (ArduPilot's ARRAY_SIZE) for an array a: its length, else None."""
        n = strip_parens(n)
        if n.get("kind") != "BinaryOperator" or n.get("opcode") != "/":
            return None
        a, b = [strip_parens(x) for x in kids(n)]
        if not all(x.get("kind") == "UnaryExprOrTypeTraitExpr" and x.get("name") == "sizeof" and kids(x) for x in (a, b)):
            return None
        ta, tb = ctype_of(kids(a)[0]), ctype_of(kids(b)[0])
        if ta.kind != "array" or ta.elem != tb or ta.n <= 0:
            return None
        return ta.n

    def e_ImplicitValueInitExpr(self, n):
        return [], zero_of(ctype_of(n), n)

    def e_CXXScalarValueInitExpr(self, n):
        return [], zero_of(ctype_of(n), n)     # `T()` for a number: zero

    def e_IntegerLiteral(self, n):
        t = ctype_of(n)
        return [], lit(n["value"], t)

    def string_literal(self, n):
        """A string literal used as a `const char *` (its decay is the only accepted use)."""
        v = n.get("value", "")
        try:
            text = json.loads(v)            # clang prints the literal with C escapes, as JSON reads them
        except ValueError:
            raise Reject(n, "string literal `%s` with escapes" % v)
        return [], V(lean_string(text), ATOM)

    def e_CXXBoolLiteralExpr(self, n):
        return [], V("true" if n["value"] else "false", ATOM)

    def e_FloatingLiteral(self, n):
        t = ctype_of(n)
        rng = n["range"]["begin"]
        text = None
        if "spellingLoc" not in rng and rng.get("file") in self.u.files:
            src = self.u.source_of(rng["file"])
            off, ln = rng["offset"], rng["tokLen"]
            text = src[off:off + ln].decode()
        if text is None:          # spelled inside a macro (e.g. FLT_EPSILON): clang's value text
            text = n["value"]
        val, s = parse_c_float(text)
        cval, _ = parse_c_float(n["value"])
        if val is None or cval is None:
            raise Reject(n, "floating literal `%s`" % text)
        bits = float_bits(val, t)
        if bits != float_bits(cval, t):
            raise Reject(n, "floating literal `%s` (value differs from clang's %s)" % (text, n["value"]))
        width = 8 if t.kind == "float" else 16
        if s.lower().startswith("0x"):
            v = app("%s.ofBits" % t.lean, V("0x%0*x" % (width, bits), ATOM))
        else:
            v = lit(lean_decimal(s), t)
        self.u.literal(n, v.text, "%0*x" % (width, bits), text)
        return [], v

    def e_DeclRefExpr(self, n):
        ref = n["referencedDecl"]
        rid = ref["id"]
        if rid in self.aliases:
            return [], self.read_path(self.aliases[rid], n)
        if rid in self.live_refs:
            return self.expr(self.live_refs[rid])
        if rid in self.vars:
            if rid in self.uninit and self.da is not DIVERGE and rid not in self.da:
                raise Reject(n, "read of `%s`, which may be uninitialized" % ref["name"])
            self.read.add(rid)
            return [], V(self.vars[rid][0], ATOM)
        if rid not in self.u.consts:
            d0 = self.u.decl(rid)
            if d0 is not None and d0.get("previousDecl") in self.u.consts:
                rid = d0["previousDecl"]    # `constexpr T C::x;` (the out-of-line definition): the in-class declaration
        if rid in self.u.consts:
            c = self.u.consts[rid]
            self.u.const_item(rid)
            self.deps.add(rid)
            return [], V(self.qual(c["ns"], c["lean"]), ATOM)
        if ref.get("kind") == "EnumConstantDecl":
            e = self.u.enum_of_constant(rid)
            if e is None:
                raise Reject(n, "enumerator `%s` of an enum that is not translated" % ref["name"])
            self.deps.add(("enum", e.cxx))
            return [], V("%s.%s" % (e.lean, e.ctor_names[ref["name"]]), ATOM)
        if ref.get("kind") in ("FunctionDecl", "CXXMethodDecl"):
            raise Reject(n, "function `%s` used as a value (function pointer)" % ref["name"])
        if ref.get("kind") == "VarDecl":
            d = self.u.decl(rid)
            v = self.constexpr_value(d, n)
            if v is not None:
                return [], v
            if self.dropped_ref(n) is not None:
                raise Reject(n, "read of `%s`, which is not part of the model (--drop)" % self.dropped_ref(n))
            if d is not None and self.u.parent_record(d) is not None:
                raise Reject(n, "static data member `%s` that is mutable or has no constant initializer" % ref["name"])
            raise Reject(n, "reference to global variable `%s` (mutable or non-constant globals are outside the subset)" % ref["name"])
        if ref.get("kind") == "ParmVarDecl":
            raise Reject(n, "reference to parameter `%s` (a boundary object, or outside its function)" % ref["name"])
        raise Reject(n, "reference to `%s`" % ref.get("name"))

    def e_SubstNonTypeTemplateParmExpr(self, n):
        inner = strip_parens(kids(n)[-1])     # the template argument substituted for the parameter
        if inner.get("kind") == "CharacterLiteral":
            # an integer template argument of a character type (`uint8_t FILTER_SIZE` = 7): its value
            return [], lit(str(inner["value"]), ctype_of(inner))
        return self.expr(kids(n)[-1])

    def constexpr_value(self, d, n):
        """The value of a `constexpr` variable, or of a call without arguments of a `constexpr`
        function whose body is one `return`, declared outside the translated files (libc++'s
        `std::is_same<T, U>::value`, `std::numeric_limits<float>::epsilon()`): its initializer or
        returned expression, translated as a constant (no variables, no effects), else None."""
        if d is None or not d.get("constexpr") or self.u.in_set(d):
            return None
        if d.get("kind") == "VarDecl":
            e = kids(d)[0] if kids(d) and d.get("init") else None
        elif d.get("kind") in ("FunctionDecl", "CXXMethodDecl"):
            if any(p.get("kind") == "ParmVarDecl" for p in kids(d)) or (d.get("kind") == "CXXMethodDecl" and d.get("storageClass") != "static"):
                return None
            body = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
            e = kids(kids(body)[0])[0] if body is not None and len(kids(body)) == 1 and kids(body)[0].get("kind") == "ReturnStmt" and kids(kids(body)[0]) else None
        else:
            return None
        if e is None:
            return None
        sub = Body(self.u, None, None, home=self.home)
        try:
            pre, v = sub.expr(e)
        except Reject as r:
            raise Reject(n, "`constexpr` `%s` whose value is not a constant the translator evaluates (%s)" % (d.get("name"), r.construct))
        if pre or v is None or sub.reads or sub.read:
            raise Reject(n, "`constexpr` `%s` whose value is not a constant" % d.get("name"))
        self.deps |= sub.deps
        self.uses_libm |= sub.uses_libm
        return v

    def cast(self, n):
        ck = n.get("castKind")
        c = kids(n)[0]
        if ck == "ArrayToPointerDecay" and strip_parens(c).get("kind") == "StringLiteral" and ctype_of(n).kind == "string":
            return self.string_literal(strip_parens(c))     # a string literal as `const char *`
        if ck == "ArrayToPointerDecay":
            raise Reject(n, "array used as a pointer")
        if ck == "UserDefinedConversion" or (ck == "LValueToRValue" and n.get("conversionFunc")):
            return self.expr(c)
        if ck in ("UncheckedDerivedToBase", "DerivedToBase"):
            raise Reject(n, "object converted to a base class (slicing)")
        if ck not in CAST_KINDS:
            raise Reject(n, "cast `%s`" % ck)
        pre, v = self.expr(c)
        if ck in ("NoOp", "LValueToRValue"):
            return pre, v
        s, d = ctype_of(c), ctype_of(n)
        expected = {
            "FloatingCast": s.is_float() and d.is_float(),
            "IntegralCast": s.kind in ("int", "bool", "enum") and d.kind in ("int", "enum"),
            "IntegralToFloating": s.kind in ("int", "bool", "enum") and d.is_float(),
            "FloatingToIntegral": s.is_float() and d.is_int(),
            "IntegralToBoolean": s.kind in ("int", "enum") and d.kind == "bool",
            "FloatingToBoolean": s.is_float() and d.kind == "bool",
        }[ck]
        if not expected:
            raise Reject(n, "cast `%s` from `%s` to `%s`" % (ck, s.cname, d.cname))
        self.deps |= type_deps(s) | type_deps(d)
        return pre, conv(v, s, d, n)

    e_ImplicitCastExpr = cast

    def explicit_cast(self, n):
        # clang puts the conversion of an explicit cast in an inner ImplicitCastExpr marked
        # isPartOfExplicitCast and gives the explicit node castKind NoOp; either way, cast().
        if ctype_of(n).kind == "void":
            raise Reject(n, "cast to void used as a value")
        return self.cast(n)

    e_CStyleCastExpr = explicit_cast
    e_CXXStaticCastExpr = explicit_cast
    e_CXXFunctionalCastExpr = explicit_cast

    def e_CXXReinterpretCastExpr(self, n):
        raise Reject(n, "`reinterpret_cast`")

    def e_CXXConstCastExpr(self, n):
        raise Reject(n, "`const_cast`")

    # -- lvalues ----------------------------------------------------------------------------

    def this_field(self, n):
        """The FieldInfo of `this->f` (n a MemberExpr), or None if n is not a member of `this`."""
        if n.get("kind") != "MemberExpr":
            return None
        base = strip_object(kids(n)[0])
        if base.get("kind") != "CXXThisExpr":
            return None
        if self.ctx is None:
            raise Reject(n, "`this` outside a member function")
        f = self.ctx.rec.field_by_id(n["referencedMemberDecl"])
        if f is None:
            if n["referencedMemberDecl"] in self.u.dropped:
                raise Reject(n, "read of `%s`, which is not part of the model (--drop)" % self.u.dropped[n["referencedMemberDecl"]])
            raise Reject(n, "member `%s` that is not a data member of the class" % n.get("name"))
        return f

    def nat_index(self, idx):
        pre_i, i = self.expr(idx)
        it = ctype_of(idx)
        if not it.is_int():
            raise Reject(idx, "array index of type `%s`" % it.cname)
        nat = app("%s.toNatClampNeg" % it.lean, i) if it.signed else app("%s.toNat" % it.lean, i)
        return pre_i, nat

    def resolve_path(self, n):
        """(pre, Path) of an lvalue expression, or None if n is not a variable, a data member
        or an array element of one."""
        n = strip_object(n)
        k = n.get("kind")
        if k == "DeclRefExpr":
            rid = n["referencedDecl"]["id"]
            if rid in self.aliases:
                return [], self.aliases[rid]
            if rid not in self.vars:
                return None
            name, t = self.vars[rid]
            return [], Path(("var", rid), name, [], t)
        if k == "MemberExpr":
            f = self.this_field(n)
            if f is not None:
                if f.category == "param":
                    return [], Path(("p",), "p", [("f", f.lean)], f.t)
                if f.category == "ref":
                    return [], Path(("r",), "r'", [("f", f.lean)], f.t)
                if f.category == "boundary":
                    return None
                return [], Path(("s",), "s", [("f", f.lean)], f.t)
            r = self.resolve_path(kids(n)[0])
            if r is None:
                return None
            pre, bp = r
            if bp.t is None or bp.t.kind != "record":
                return None
            f = bp.t.info.field_by_id(n["referencedMemberDecl"])
            if f is None:
                raise Reject(n, "member `%s`" % n.get("name"))
            if f.category != "state":
                raise Reject(n, "member `%s` of a nested object, which is a parameter or a boundary member" % n.get("name"))
            return pre, bp.extend(("f", f.lean), f.t)
        if k == "CXXOperatorCallExpr":
            return self.index_view_path(n)
        if k == "CXXMemberCallExpr":
            return self.object_accessor(n)
        if k == "UnaryOperator" and n.get("opcode") == "*" and self.nullable_ref(kids(n)[0]) is not None:
            rid = self.nullable_ref(kids(n)[0])
            name, t = self.vars[rid]
            return [], Path(("var", rid), name, [], t)
        if k == "UnaryOperator" and n.get("opcode") == "*" and strip_object(kids(n)[0]).get("kind") == "CXXThisExpr" \
                and self.ctx is not None:
            return [], Path(("s",), "s", [], ctype_of(n))     # `*this`: the whole state
        if k == "ArraySubscriptExpr":
            base, idx = kids(n)
            sb = strip_object(base)
            if sb.get("kind") == "DeclRefExpr" and sb["referencedDecl"]["id"] in self.array_views:
                name, t = self.vars[sb["referencedDecl"]["id"]]
                pre_i, nat = self.nat_index(idx)
                return pre_i, Path(("var", sb["referencedDecl"]["id"]), name, [("i", nat)], t.elem)
            if not (base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay"):
                raise Reject(n, "subscript of a pointer")
            r = self.resolve_path(kids(base)[0])
            if r is None:
                return None
            pre, bp = r
            if bp.t is None or bp.t.kind != "array":
                raise Reject(n, "subscript of `%s`" % (bp.t.cname if bp.t else "?"))
            pre_i, nat = self.nat_index(idx)
            return pre + pre_i, bp.extend(("i", nat), bp.t.elem)
        return None

    def read_path(self, p, n, check_init=True):
        root = p.root
        if root[0] == "var":
            rid = root[1]
            if check_init and rid in self.uninit and self.da is not DIVERGE and rid not in self.da:
                raise Reject(n, "read of `%s`, which may be uninitialized" % p.root_text)
            self.read.add(rid)
        else:
            self.reads.add(root[0])
        return V(p.text(), ATOM)

    def write_path(self, p, value, n):
        """The line that stores value at p."""
        root = p.root
        if root[0] == "var":
            rid = root[1]
            if rid not in self.mutable:
                raise Reject(n, "internal: write to `%s`, which was not found to be assigned" % p.root_text)
            if p.steps:
                self.read.add(rid)
            else:
                self.mark_assigned(rid)
        elif root[0] == "r":
            raise Reject(n, "write through a `const` reference member")
        elif root[0] == "o":
            self.writes.add("o")
        else:
            self.writes.add(root[0])
            self.reads.add(root[0])
        if any(k == "v" for k, _ in p.steps) and not SIMPLE.match(value.text):
            # a write through a view names the value once per viewed field: bind it first (one
            # entry of two lines; Body.finish indents the second like the first)
            t = self.temp()
            return "let %s := %s\n%s := %s" % (t, value.text, p.root_text, update_text(p.root_text, p.steps, V(t, ATOM)))
        return "%s := %s" % (p.root_text, update_text(p.root_text, p.steps, value))

    def lvalue(self, target, n):
        self.var_views = True
        try:
            r = self.resolve_path(target)
        finally:
            self.var_views = False
        if r is None:
            t = strip_object(target)
            if t.get("kind") == "MemberExpr":
                raise Reject(n, "assignment to member `%s` of an object that is not translated" % t.get("name"))
            raise Reject(n, "assignment to something other than a variable, parameter, data member or array element")
        return r

    def e_MemberExpr(self, n):
        f = self.this_field(n)
        if f is not None and f.category == "boundary":
            raise Reject(n, "boundary object `%s` used as a value" % n["name"])
        bo = self.boundary_obj(kids(n)[0])
        if bo is not None:
            if self.is_live(kids(n)[0]):
                return self.live_read(n, bo, n["name"], [], ctype_of(n), "%s.%s" % (bo, n["name"]))
            return [], self.boundary_read(n, bo, n["name"], None, [])
        base = strip_object(kids(n)[0])
        bf = self.this_field(base) if base.get("kind") == "MemberExpr" else None
        if bf is not None and bf.category == "owner":
            return [], self.owner_read(n, bf, n["name"], None)
        r = self.resolve_path(n)
        if r is None:
            bt = ctype_of(base)
            g = bt.info.field_by_id(n.get("referencedMemberDecl")) if bt.kind == "record" else None
            if g is not None and g.category == "state" and not n.get("isArrow"):
                # a member of a value (a call's result, a boundary read: `_ahrs.get_accel_ef().z`)
                pre, v = self.expr(base)
                return pre, V("%s.%s" % (v.at(ATOM), g.lean), ATOM)
            raise Reject(n, "member access `%s` on an object that is not translated" % n.get("name"))
        pre, p = r
        return pre, self.read_path(p, n)

    def e_ArraySubscriptExpr(self, n):
        r = self.resolve_path(n)
        if r is not None:
            pre, p = r
            return pre, self.read_path(p, n)
        base = kids(n)[0]
        if base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay":
            arr = strip_parens(kids(base)[0])
            if arr.get("kind") == "DeclRefExpr" and arr["referencedDecl"]["id"] in self.u.consts:
                pre_a, a = self.expr(arr)
                pre_i, nat = self.nat_index(kids(n)[1])
                return pre_a + pre_i, V("%s[%s]!" % (a.at(ATOM), nat.text), ATOM)
            raise Reject(n, "subscript of an array expression")
        raise Reject(n, "subscript of a pointer")

    # -- calls ------------------------------------------------------------------------------

    def nullable_out_type(self, p, body):
        """The pointee type of a parameter `T *p` (T a number or a translated struct or class, not
        const) that the body uses only in `p != nullptr` / `p == nullptr` and `*p` (to write or read
        the pointee), else None."""
        q = p.get("type", {}).get("qualType", "").strip()
        dq = p.get("type", {}).get("desugaredQualType", q).strip()
        m = re.match(r"^([\w:<>, ]+?) ?\*$", dq)
        if not m or m.group(1).startswith("const ") or body is None:
            return None
        try:
            pt = parse_type_str(m.group(1), m.group(1), p)
        except Reject:
            return None
        if not (pt.is_scalar() or pt.kind == "record"):
            return None
        uses = 0
        for r in walk(body):
            if r.get("kind") != "DeclRefExpr" or r.get("referencedDecl", {}).get("id") != p["id"]:
                continue
            uses += 1
            up = self.u.parent.get(r["id"])
            while up is not None and up.get("kind") in ("ImplicitCastExpr", "ParenExpr") and up.get("castKind", "LValueToRValue") in ("LValueToRValue", "NoOp"):
                up = self.u.parent.get(up["id"])
            if up is None:
                return None
            if up.get("kind") == "UnaryOperator" and up.get("opcode") == "*":
                continue
            if up.get("kind") == "BinaryOperator" and up.get("opcode") in ("==", "!=") and \
                    any(self.is_null(x) for x in kids(up)):
                continue
            return None
        return pt if uses else None

    @staticmethod
    def is_null(e):
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("NullToPointer", "NoOp"):
            e = strip_parens(kids(e)[0])
        return e.get("kind") in ("CXXNullPtrLiteralExpr", "GNUNullExpr") or (e.get("kind") == "IntegerLiteral" and e.get("value") == "0")

    def nullable_ref(self, e):
        """The parameter id if e (casts stripped) names a nullable out-pointer parameter, else None."""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("LValueToRValue", "NoOp"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in self.nullable:
            return e["referencedDecl"]["id"]
        return None

    def call_args(self, params, args, n):
        """Translate the arguments of a call (default arguments expanded); returns (pre, values,
        outs) where outs lists the Paths of arguments bound to non-const reference parameters.
        params: (decl, lean name or None for a boundary parameter, CType, ref)."""
        res, outs = [], []
        for i, a in enumerate(args):
            if i >= len(params):
                raise Reject(a, "argument without a parameter")
            p, pn, pt, ref = params[i]
            if pn is None:
                continue
            if a.get("kind") == "CXXDefaultArgExpr":
                res.append(self.expr(kids(a)[0]))
                continue
            if pt.kind == "array" and pt.n == 0:
                sa = strip_parens(a)
                if sa.get("kind") == "ImplicitCastExpr" and sa.get("castKind") == "ArrayToPointerDecay":
                    res.append(self.expr(kids(sa)[0]))      # the array itself
                    continue
                if strip_object(sa).get("kind") == "DeclRefExpr" and strip_object(sa)["referencedDecl"]["id"] in self.array_views:
                    res.append(self.expr(strip_object(sa)))
                    continue
                raise Reject(a, "argument for a `const T *` parameter that is not an array")
            if ref == "ptr":
                # a nullable out-pointer: `&x` passes the flag true and x, written back after the
                # call; a null pointer passes false and a zero, the result is discarded
                sa = strip_parens(a)
                if self.is_null(sa):
                    outs.append(None)
                    res.append(([], V("false", ATOM)))
                    res.append(([], zero_of(pt, a)))
                    continue
                sa = strip_object(sa)
                if not (sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&"):
                    raise Reject(a, "argument for a nullable pointer parameter other than `&x` or a null pointer")
                r = self.resolve_path(kids(sa)[0])
                if r is None:
                    raise Reject(a, "argument `&x` for a nullable pointer parameter where x is not a variable, member or element")
                pre, path = r
                outs.append(path)
                res.append(([], V("true", ATOM)))
                res.append((pre, self.read_path(path, a, check_init=False)))
                continue
            if ref == "mut":
                r = self.resolve_path(a)
                if r is None:
                    raise Reject(a, "argument for a reference parameter that is not a variable, member or element")
                pre, path = r
                outs.append(path)
                # an uninitialized variable may be passed to be written (its placeholder is passed)
                res.append((pre, self.read_path(path, a, check_init=False)))
            else:
                res.append(self.expr(a))
        pre, vals = self.sequence(res)
        return pre, vals, outs

    def apply_call(self, fname, writes, objargs, vals, outs, ret, n, setters):
        """Emit the call of a translated function or method. writes: the subset of {p, s} the
        callee returns; setters: p/s -> function from the returned V to the line storing it.
        Returns (pre, value)."""
        call = app(fname, *(objargs + vals))
        comps = []
        if "p" in writes:
            comps.append(("p", None))
        if "s" in writes:
            comps.append(("s", None))
        if "o" in writes:
            comps.append(("o", None))
        for p in outs:
            comps.append(("out", p))
        if ret.kind != "void":
            comps.append(("ret", None))
        if not comps:
            raise Reject(n, "call without an observable effect or result")
        if len(comps) == 1 and comps[0][0] == "ret":
            return [], call
        if len(comps) == 1:
            kind, p = comps[0]
            if (kind in ("p", "s", "o") and setters.get(kind) is None) or (kind == "out" and p is None):
                return [], None             # the state of a temporary object, or a value for a null pointer: discarded
            return [setters[kind](call) if kind in ("p", "s", "o") else self.write_path(p, call, n)], None
        # a component of a temporary object (setter None) is bound to `_`
        names = ["_" if (kind in ("p", "s", "o") and setters.get(kind) is None) or (kind == "out" and p is None) else self.temp() for kind, p in comps]
        pre = ["let (%s) := %s" % (", ".join(names), call.text)]
        value = None
        for (kind, p), t in zip(comps, names):
            if kind in ("p", "s", "o"):
                if t != "_":
                    pre.append(setters[kind](V(t, ATOM)))
            elif kind == "out":
                if p is not None:           # None: a null pointer argument, the value is discarded
                    pre.append(self.write_path(p, V(t, ATOM), n))
            else:
                value = V(t, ATOM)
        return pre, value

    def e_CallExpr(self, n):
        callee, args = kids(n)[0], kids(n)[1:]
        if callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "BuiltinFnToFnPtr":
            ref = strip_parens(kids(callee)[0])
            name = ref.get("referencedDecl", {}).get("name")
            if name in BUILTIN_CONSTS:
                ty, bits = BUILTIN_CONSTS[name]
                t = FLOAT if ty == "float" else DOUBLE
                width = 8 if ty == "float" else 16
                v = app("%s.ofBits" % t.lean, V("0x%0*x" % (width, bits), ATOM))
                self.u.literal(n, v.text, "%0*x" % (width, bits), name)
                return [], v
            raise Reject(n, "builtin `%s`" % name)
        if not (callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "FunctionToPointerDecay"):
            raise Reject(n, "call through a function pointer or object")
        ref = strip_parens(kids(callee)[0])
        if ref.get("kind") != "DeclRefExpr":
            raise Reject(n, "indirect call")
        decl = self.u.decl(ref["referencedDecl"]["id"])
        name = ref["referencedDecl"]["name"]
        if not args:
            v = self.constexpr_value(decl, n)
            if v is not None:
                return [], v
        if decl is not None and decl.get("kind") == "CXXMethodDecl":
            return self.static_method_call(n, self.u.canonical(decl), args)
        target = self.u.function_for(decl)
        if target is not None:
            fr = self.u.free_result(target, n)
            self.deps.add(target["id"])
            pre, vals, outs = self.call_args(fr.cparams, args, n)
            p2, v = self.apply_call(self.qual(self.u.ns, fr.lean), set(), [], vals, outs, fr.ret, n, {})
            return pre + p2, v
        qn = qualified_name(self.u, decl) if decl is not None else name
        if qn in DROP:
            return self.dropped(n, decl, qn)
        if name == "memset" and len(args) == 3:
            return self.memset_zero(n, args)
        if name in COMPARISON_MACROS and len(args) == 2:
            # <cmath>'s quiet comparisons: libc++ converts both operands to their promoted type
            # (double unless both are float) and compares; for numbers the result is the
            # relational operator's (both are false on NaN)
            ts = [ctype_of(a) for a in args]
            if not all(t.is_float() or t.is_int() for t in ts):
                raise Reject(n, "`%s` on `%s`" % (name, ", ".join(t.cname for t in ts)))
            ct = FLOAT if all(t.kind == "float" for t in ts) else DOUBLE
            pre, vals = self.operands(args)
            a, b = [conv(v, t, ct, n) for v, t in zip(vals, ts)]
            return pre, V("decide (%s %s %s)" % (a.at(CMP + 1), COMPARISON_MACROS[name], b.at(CMP + 1)), APP)
        if qn in BOUNDARY_FN:
            if any(a.get("kind") != "CXXDefaultArgExpr" for a in args):
                raise Reject(n, "call of boundary function `%s` with arguments" % qn)
            return [], self.boundary_read(n, qn, name, True, [])
        if name in self.u.externs:
            lean_name, nargs = self.u.externs[name]
            used = [kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in args]
            pre, vals = self.operands(used[:nargs] if nargs is not None else used)
            return pre, app(lean_name, *vals)
        if self.u.in_set(decl):
            raise Reject(n, "call to `%s`, which has no definition in the translated files (see --extern)" % name)
        for a in args:
            if a.get("kind") == "CXXDefaultArgExpr":
                raise Reject(a, "default argument of a library function")
        try:
            ps = tuple(ctype_of(a).cname for a in args)
            r = ctype_of(n).cname
        except Reject:
            raise Reject(n, "call to library function `%s`" % name)
        key = (name, ps, r)
        if key not in CMATH:
            raise Reject(n, "call to library function `%s(%s)` (not in the <cmath> table and no --extern)" % (name, ", ".join(ps)))
        pre, vals = self.operands(args)
        f = CMATH[key]
        if isinstance(f, tuple):        # libc++'s mixed-type overload: the arguments converted to double
            f = f[0]
            vals = [conv(v, ctype_of(a), DOUBLE, a) for v, a in zip(vals, args)]
        if f.startswith("CppLibm."):
            self.uses_libm = True
        return pre, app(f, *vals)

    def static_method_call(self, n, decl, args):
        qn = qualified_name(self.u, decl)
        if qn in DROP:
            return self.dropped(n, decl, qn)
        owner = self.u.decl(decl.get("parentDeclContextId")) or self.u.parent.get(decl["id"])
        if owner is not None and (owner.get("name") in BOUNDARY or qualified_name(self.u, owner) in BOUNDARY):
            return self.boundary_call(n, qualified_name(self.u, owner), decl, decl.get("name"), args, static=True)
        if AP_PARAM[0] and qn == "AP_Param::setup_object_defaults":
            return self.ap_param_defaults(n, args), None
        rec = self.u.parent_record(decl)
        if rec is None or decl.get("storageClass") != "static":
            raise Reject(n, "call of method `%s` without an object" % decl.get("name"))
        fr = self.u.static_result(rec, decl, n)
        self.deps.add(fr.key)
        pre, vals, outs = self.call_args(fr.cparams, args, n)
        p2, v = self.apply_call(self.qual(rec.lean, fr.lean), set(), [], vals, outs, fr.ret, n, {})
        return pre + p2, v

    def memset_zero(self, n, args):
        """`memset(&x, 0, sizeof(x))`: x becomes the all-zero value of its type."""
        a0, a1, a2 = [strip_parens(a) for a in args]
        while a0.get("kind") == "ImplicitCastExpr":
            a0 = strip_parens(kids(a0)[0])
        if not (a0.get("kind") == "UnaryOperator" and a0.get("opcode") == "&" and self.const_int(a1) == 0
                and a2.get("kind") == "UnaryExprOrTypeTraitExpr" and a2.get("name") == "sizeof"):
            raise Reject(n, "`memset` other than `memset(&x, 0, sizeof(x))`")
        target = kids(a0)[0]
        sz = strip_parens(kids(a2)[0]) if kids(a2) else None
        r = self.lvalue(target, n)
        pre, p = r
        if sz is None or self.u.text_of(strip_parens(target)) != self.u.text_of(sz):
            raise Reject(n, "`memset` whose size is not `sizeof` of its target")
        return pre + [self.write_path(p, all_zero(p.t, n), n)], None

    def dropped(self, n, decl, qn):
        if decl["type"]["qualType"].split("(")[0].strip() != "void" and self.discard_node is not n:
            raise Reject(n, "call of `%s` (--drop) whose result is used" % qn)
        return ["pure ()  -- C++ `%s(...)`: left out (--drop)" % qn], None

    def ap_param_defaults(self, n, args):
        """`AP_Param::setup_object_defaults(this, var_info)`: each entry of the class's var_info
        table sets its parameter to the default, a member (AP_GROUPINFO_FLAGS_DEFAULT_POINTER) or
        a constant (AP_GROUPINFO), in table order, as the oracle's copy of AP_Param.cpp:2685-2696."""
        if self.ctx is None or len(args) != 2 or not any(m.get("kind") == "CXXThisExpr" for m in walk(args[0])):
            raise Reject(n, "`AP_Param::setup_object_defaults` on an object other than `this`")
        ref = next((m for m in walk(args[1]) if m.get("kind") == "DeclRefExpr"), None)
        vd = self.u.decl(ref["referencedDecl"]["id"]) if ref else None
        owner = self.u.parent_record(vd) if vd else None
        if owner is None or owner.var_info is None:
            raise Reject(n, "`AP_Param::setup_object_defaults` with a table that is not a translated class's var_info")
        lines = []
        for entry in kids(kids(owner.var_info)[0]):
            if entry.get("kind") != "InitListExpr" or len(kids(entry)) < 3:
                raise Reject(entry, "var_info entry")
            offset, union = kids(entry)[1], kids(entry)[2]
            member = next((m for m in walk(offset) if m.get("kind") == "MemberExpr"), None)
            uf = union.get("field", {}).get("name")
            if uf in ("group_info", "group_info_ptr"):
                continue                        # nested groups (also AP_NESTEDGROUPINFO, at offset 0): setup_object_defaults skips them
            if member is None:
                break                           # AP_GROUPEND
            chain = []                      # `thr_lin.curve_expo`: the members from the outermost in
            m = member
            while m.get("kind") == "MemberExpr":
                chain.append(m)
                m = strip_object(kids(m)[0])
            chain.reverse()
            rec, steps = self.ctx.rec, []
            for mm in chain[:-1]:
                g = rec.field_by_id(mm["referencedMemberDecl"])
                if g is None or g.category != "state" or g.t.kind != "record":
                    raise Reject(entry, "var_info entry for `%s`, which is not a parameter member" % member.get("name"))
                steps.append(("f", g.lean))
                rec = g.t.info
            f = rec.field_by_id(member["referencedMemberDecl"])
            if f is None or f.category != "param":
                raise Reject(entry, "var_info entry for `%s`, which is not a parameter member" % member.get("name"))
            if uf == "def_value_offset":
                minus = strip_parens(kids(union)[0])
                dm = next((m for m in walk(kids(minus)[1]) if m.get("kind") == "MemberExpr"), None)
                g = self.ctx.rec.field_by_id(dm["referencedMemberDecl"]) if dm else None
                if g is None or g.category != "state" or g.t != FLOAT:
                    raise Reject(entry, "var_info default pointer to `%s`, which is not a float member" % (dm or {}).get("name"))
                # get_default_value reads the member as a float; set_value converts it to the type
                v = conv(self.read_path(Path(("s",), "s", [("f", g.lean)], g.t), entry), FLOAT, f.t, entry)
            elif uf == "def_value":
                e = kids(union)[0]
                pre, v0 = self.expr(e)
                if pre:
                    raise Reject(entry, "var_info default with side effects")
                if f.t.kind == "enum":
                    # AP_Param::set_value stores the float default in the parameter's integer type
                    st = parse_type_str(f.storage, f.storage, entry)
                    v = conv(conv(v0, ctype_of(e), st, entry), st, f.t, entry)
                else:
                    v = conv(v0, ctype_of(e), f.t, entry)
            else:
                raise Reject(entry, "var_info entry with `%s`" % uf)
            if f.t.kind == "enum":
                pass            # an AP_Enum default is converted to its enum by conv above (through the stored integer)
            lines.append(self.write_path(Path(("p",), "p", steps + [("f", f.lean)], f.t), v, entry))
        return lines

    def boundary_object_call(self, n):
        """Is n a call of a free function returning a reference to a boundary object (ArduPilot's
        singleton accessors, e.g. `AP::ahrs()`)?"""
        if n.get("kind") != "CallExpr" or kids(n)[1:]:
            return False
        name, _ = strip_tag(n["type"]["qualType"].replace("const ", "").strip())
        return name in BOUNDARY or name.split("::")[-1] in BOUNDARY

    def boundary_obj(self, n):
        """The name of the boundary object that expression n denotes, or None: a member of a
        --boundary class (`_ahrs`), a singleton accessor (`AP::ahrs()`), an `extern` reference to
        one (`hal`), a static data member of a boundary class (`AP_Notify::flags`), a local
        reference bound to one (`battery`), or a member of any of these (`hal.rcout`)."""
        n = strip_object(n)
        k = n.get("kind")
        if k == "MemberExpr":
            base = strip_object(kids(n)[0])
            if base.get("kind") == "CXXThisExpr":
                if self.ctx is None:
                    return None
                f = self.ctx.rec.field_by_id(n.get("referencedMemberDecl"))
                return f.name if f is not None and f.category == "boundary" else None
            b = self.boundary_obj(base)
            return None if b is None else "%s.%s" % (b, n["name"])
        if k == "CallExpr" and self.boundary_object_call(n):
            return self.u.text_of(n) or "boundary"
        if k == "CXXMemberCallExpr" and not kids(n)[1:] and n.get("valueCategory") == "lvalue":
            # `_pos_control.NE_get_pos_p()`: a --boundary-query accessor of a boundary object that
            # returns a reference to one of its member objects, which is part of the boundary too
            callee = strip_parens(kids(n)[0])
            d = self.u.decl(callee.get("referencedMemberDecl")) if callee.get("kind") == "MemberExpr" else None
            if d is not None and qualified_name(self.u, d) in BOUNDARY_QUERY and ctype_kind_record_ref(d):
                b = self.boundary_obj(kids(callee)[0])
                if b is not None:
                    return "%s.%s()" % (b, callee["name"])
        if k == "DeclRefExpr":
            rid = n["referencedDecl"]["id"]
            if rid in self.boundary_locals:
                return self.boundary_locals[rid]
            if rid in self.u.boundary_globals:
                return self.u.boundary_globals[rid]
            d = self.u.decl(rid)
            if d is not None and d.get("kind") == "ParmVarDecl":
                try:
                    if decl_type(d)[0].kind == "boundary":
                        return d.get("name")        # a boundary object passed by reference
                except Reject:
                    return None
            if d is not None and d.get("kind") == "VarDecl":
                owner = self.u.decl(d.get("parentDeclContextId")) or self.u.parent.get(rid)
                if owner is not None and owner.get("kind") in ("CXXRecordDecl", "ClassTemplateSpecializationDecl") and \
                        (owner.get("name") in BOUNDARY or qualified_name(self.u, owner) in BOUNDARY):
                    return "%s::%s" % (qualified_name(self.u, owner), d["name"])
        return None

    def is_live(self, obj_node):
        """Is the boundary object expression obj_node (or the object it is reached from, through
        accessors and members) of a --boundary-live class?"""
        if not BOUNDARY_LIVE:
            return False
        e = strip_object(obj_node)
        while True:
            q = e.get("type", {}).get("qualType", "")
            name = strip_tag(q.replace("const ", "").replace("&", "").strip())[0]
            if name in BOUNDARY_LIVE or name.split("::")[-1] in BOUNDARY_LIVE:
                return True
            if e.get("kind") in ("CXXMemberCallExpr", "MemberExpr") and kids(e):
                c = strip_parens(kids(e)[0])
                e = strip_object(kids(c)[0]) if e.get("kind") == "CXXMemberCallExpr" and c.get("kind") == "MemberExpr" and kids(c) else strip_object(c)
                if e.get("kind") == "CXXThisExpr":
                    return False
                continue
            return False

    def live_read(self, n, obj, member, arg_nodes, t, cxx):
        """A read of a --boundary-live object: an Inputs field that is a function of the output log so
        far (`o`) and of the call's arguments, applied here: `inp.f o a1 ...`. The member function
        takes the log `o` (README.md, "AC_WPNav, the AHRS view, and the two vehicles")."""
        if t.kind == "param":
            pt = PARAM_CLASSES.get(t.name) or PARAM_CLASSES.get(t.name.split("::")[-1])
            t = parse_type_str(pt, pt, n)       # a parameter of the boundary object, converted to its value
        if not (t.is_scalar() or t.kind == "record"):
            raise Reject(n, "boundary value of type `%s`" % t.cname)
        used = [kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in arg_nodes]
        pre, vals = self.operands(used)
        ats = []
        for a, v in zip(used, vals):
            at = ctype_of(a)
            if not (at.is_scalar() or at.kind == "record"):
                raise Reject(a, "argument of type `%s` of a live boundary read" % at.cname)
            ats.append(at)
            self.deps |= type_deps(at)
        ft = CType("fun", elem=t, args=ats)
        fld = self.ctx.input_field(obj, member, True, ("live",), ft, cxx, n)
        self.reads |= {"inp", "olive"}
        self.deps |= type_deps(ft)
        return pre, app("inp.%s" % fld, V("o", ATOM), *vals)

    def boundary_read(self, n, obj, member, method_args, node_args):
        """A value read from a boundary object (a data member, or the result of a const method)
        is a field of Inputs: one per distinct read with constant arguments, else one per call
        site, which must not be inside a loop (it is executed at most once per call)."""
        if self.ctx is None:
            raise Reject(n, "boundary object used outside a member function")
        cargs = []
        site = None
        for a in node_args:
            if a.get("kind") == "CXXDefaultArgExpr":
                a = kids(a)[0]
            c = self.const_value(a)
            if c is None and not SITE_INPUTS[0]:
                raise Reject(a, "argument of a call on a boundary object that is not a compile-time constant (only constant arguments of const boundary calls are translated)")
            if c is None:
                if any(l in ("for", "while", "do") for l in self.loops):
                    raise Reject(a, "argument of a call on a boundary object that is not a compile-time constant, inside a loop (a call site outside loops is one input)")
                loc = node_loc(n) or {}
                site = "%s:%d:%d" % (self.u.shown_path(loc.get("file")), loc.get("line", 0), loc.get("col", 0))
                c = self.u.text_of(a) or "?"
            cargs.append(c)
        t = ctype_of(n)
        if not (t.is_scalar() or t.kind == "record"):
            raise Reject(n, "boundary value of type `%s`" % t.cname)
        cxx = "%s.%s" % (obj, member) + ("(%s)" % ", ".join(str(c) for c in cargs) if method_args else "")
        if site is not None:
            cxx += " at %s" % site
        fld = self.ctx.input_field(obj, member, method_args, cargs if site is None else ("site", site), t, cxx, n)
        self.reads.add("inp")
        return V("inp.%s" % fld, ATOM)

    def owner_read(self, n, f, member, args):
        """A value read through the back-reference f to the owner (`motors.get_dt_s()`,
        `motors.has_option(BATT_RAW_VOLTAGE)`): a field of `Owner`, which the owner computes when it
        calls this object's member function (README.md, "ArduPilot"). Only reads: a call with
        constant arguments whose value is used, or a data member."""
        cargs = []
        for a in (args or []):
            if a.get("kind") == "CXXDefaultArgExpr":
                a = kids(a)[0]
            c = self.const_value(a)
            if c is None:
                raise Reject(a, "argument of a call through the back-reference `%s` that is not a compile-time constant" % f.name)
            cargs.append(c)
        t = ctype_of(n)
        if t.kind == "void" or self.discard_node is n or not (t.is_scalar() or t.kind == "record"):
            raise Reject(n, "use of the back-reference `%s` other than reading a value (`%s`)" % (f.name, member))
        key = (f.name, member, args is not None, tuple(str(c) for c in cargs))
        for k, name, _, _ in self.ctx.owner_reads:
            if k == key:
                break
        else:
            name = lean_field(re.sub(r"\W+", "_", "%s_%s%s" % (f.name, member, "".join("_" + str(c) for c in cargs))).strip("_"), n)
            self.ctx.owner_reads.append((key, name, t, n))
        self.reads.add("own")
        return V("own.%s" % name, ATOM)

    def output_event(self, n, obj, mname, args, params):
        """A call that writes the boundary, with --output-log: an `Output` value appended to `o`."""
        used = [kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in args]
        pre, vals = self.operands(used)
        targs = []
        for i, a in enumerate(used):
            p = params[i] if i < len(params) else {}
            pt = (decl_type(p)[0] if p["type"]["qualType"].startswith("const ") and p["type"]["qualType"].rstrip().endswith("&") else ctype_of(p)) if p else ctype_of(a)
            if not (pt.is_scalar() or pt.kind == "record"):
                raise Reject(a, "boundary output of type `%s`" % pt.cname)
            targs.append((p.get("name", "arg%d" % i), pt))
            vals[i] = conv(vals[i], ctype_of(a), pt, a)
        sig = "%s(%s)" % (mname if obj in ("this", None) else "%s.%s" % (obj, mname), ", ".join("%s %s" % (t.cname, nm) for nm, t in targs))
        name = self.u.output_ctor(obj, mname, targs, sig, n)
        self.writes.add("o")
        self.reads.add("o")
        return pre + ["o := o.push %s" % app("Output.%s" % name, *vals).at(ATOM)]

    def const_value(self, a):
        a = strip_parens(a)
        v = self.const_int(a)
        if v is not None:
            return v
        if a.get("kind") == "CXXBoolLiteralExpr":
            return "true" if a["value"] else "false"
        if a.get("kind") == "ImplicitCastExpr" and a.get("castKind") in ("IntegralToFloating", "FloatingCast", "NoOp"):
            return self.const_value(kids(a)[0])
        if a.get("kind") == "FloatingLiteral":
            return a["value"]
        if a.get("kind") == "DeclRefExpr" and a["referencedDecl"].get("kind") == "EnumConstantDecl":
            return a["referencedDecl"]["name"]
        return None

    def object_setters(self):
        return {"s": lambda v: "s := %s" % v.text, "p": lambda v: "p := %s" % v.text, "o": lambda v: "o := %s" % v.text}

    def this_call_args(self, res):
        """The leading p/s/inp arguments of a call of a method of the same object."""
        objargs = []
        if "p" in res.reads | res.writes:
            objargs.append(V("p", ATOM))
            self.reads.add("p")
        if "s" in res.reads | res.writes:
            objargs.append(V("s", ATOM))
            self.reads.add("s")
        if "o" in res.writes or "olive" in res.reads:
            objargs.append(V("o", ATOM))
            self.reads.add("o")
            if "olive" in res.reads:
                self.reads.add("olive")     # the callee reads a live boundary: this function takes the log too
        if "r" in res.reads:
            objargs.append(V("r'", ATOM))
            self.reads.add("r")
        if res.uses_inp:
            objargs.append(V("inp", ATOM))
            self.reads.add("inp")
        if res.uses_own:
            objargs.append(V("own", ATOM))
            self.reads.add("own")
        self.writes |= res.writes
        return objargs

    def e_CXXMemberCallExpr(self, n):
        callee, args = strip_parens(kids(n)[0]), kids(n)[1:]
        if callee.get("kind") != "MemberExpr":
            raise Reject(n, "call through a pointer to member")
        mdecl = self.u.canonical(self.u.decl(callee["referencedMemberDecl"]))
        obj = strip_object(kids(callee)[0])
        return self.member_call(n, callee, mdecl, obj, callee.get("name"), args)

    def member_call(self, n, callee, mdecl, obj, mname, args):
        """A call of member function mdecl on obj (callee: the MemberExpr, None for an operator
        call), with the arguments args."""
        if obj.get("kind") == "UnaryOperator" and obj.get("opcode") == "*" and strip_object(kids(obj)[0]).get("kind") == "CXXThisExpr":
            obj = strip_object(kids(obj)[0])        # `(*this) *= r`: a call on this object
        if mdecl is not None and qualified_name(self.u, mdecl) in DROP:
            return self.dropped(n, mdecl, qualified_name(self.u, mdecl))
        if obj.get("kind") == "DeclRefExpr" and obj["referencedDecl"]["id"] in self.param_vars:
            if (mname == "get" or mname.startswith("operator ")) and not args:
                v = self.e_DeclRefExpr(obj)[1]
                return [], self.param_conversion(v, self.vars[obj["referencedDecl"]["id"]][1], n)
            raise Reject(n, "method `%s` of a parameter-class value" % mname)
        of = self.this_field(obj) if obj.get("kind") == "MemberExpr" else None
        if of is not None and of.category == "param":
            return self.param_call(n, of, mname, args)
        if of is not None and of.category == "owner":
            return [], self.owner_read(n, of, mname, args)
        if obj.get("kind") == "ConditionalOperator" and (mname == "get" or mname.startswith("operator ")) and not args:
            r = self.param_value(obj)
            if r is not None:
                return r
        mp = self.member_param_path(obj)
        if mp is not None:                  # `lin.expo.set_default(x)`: a parameter of a member object
            return self.param_call(n, mp[1], mname, args, mp[0])
        acc = self.param_accessor(obj)
        if acc is not None:                 # `kP().set_default(x)`: the parameter the accessor returns
            pre_a, path, f = acc
            pre, v = self.param_call(n, f, mname, args, path)
            return pre_a + pre, v
        bo = self.boundary_obj(obj)
        if bo is not None:
            return self.boundary_call(n, bo, mdecl, mname, args)
        if (mname == "get" or mname.startswith("operator ")) and not args and obj.get("kind") == "CXXMemberCallExpr" \
                and ctype_of(obj).kind == "param":
            # `_pos_control.NE_get_pos_p().kP()` converted to its value: a read of the boundary's parameter
            ic = strip_parens(kids(obj)[0])
            ibo = self.boundary_obj(kids(ic)[0]) if ic.get("kind") == "MemberExpr" else None
            if ibo is not None:
                return self.boundary_call(obj, ibo, self.u.decl(ic.get("referencedMemberDecl")), ic["name"], kids(obj)[1:])
        if obj.get("kind") == "CXXThisExpr" and mdecl is not None and self.u.is_boundary_call(mdecl):
            return self.boundary_call(n, "this", mdecl, mname, args, static=True)
        if mdecl is None or self.u.parent_record(mdecl) is None:
            raise Reject(n, "call of `%s`, a method of a class that is not translated" % mname)
        if obj.get("kind") == "CXXThisExpr":
            if self.ctx is None:
                raise Reject(n, "`this` outside a member function")
            qualified = callee is not None and "::" in (self.u.text_of(callee) or "")
            target = self.ctx.resolve(mdecl, virtual_dispatch=not qualified)
            if qualified_name(self.u, target) in DROP:
                return self.dropped(n, target, qualified_name(self.u, target))     # the overrider is dropped
            res = self.ctx.method(target, n, self.alias_args(target, args))
            self.deps.add(res.bid)
            if res.noeffect:
                return ["pure ()  -- C++ `%s`: no effect in the model" % mname], None
            objargs = self.this_call_args(res)
            pre, vals, outs = self.call_args(res.cparams, args, n)
            p2, v = self.apply_call(res.lean, res.writes, objargs, vals, outs, res.ret, n, self.object_setters())
            return pre + p2, v
        # a method of a member object or of a local object of a translated class (also of a view of
        # a variable, `accel.xy() -= v`, SCurve.cpp:709)
        self.var_views = mdecl is not None and not mdecl.get("type", {}).get("qualType", "").rstrip().endswith("const")
        try:
            r = self.resolve_path(obj)
        finally:
            self.var_views = False
        if r is None:
            ot = ctype_of(obj)
            if ot.kind == "record" and ot.info.kind == "class":
                return self.temporary_call(n, obj, ot, mdecl, mname, args)
            raise Reject(n, "call of `%s` on an object that is not translated" % mname)
        pre0, op = r
        if op.t is None or op.t.kind != "record" or op.t.info.kind != "class":
            raise Reject(n, "method call on `%s`" % (op.t.cname if op.t else "?"))
        sub = self.u.context(op.t.info, n)
        self.deps.add(("T", op.t.info.id))
        res = sub.method(sub.resolve(mdecl, virtual_dispatch=True), n)
        self.deps.add(res.bid)
        if res.noeffect:
            return pre0 + ["pure ()  -- C++ `%s`: no effect in the model" % mname], None
        member = op.root[0] == "s" and all(k == "f" for k, _ in op.steps)
        objargs = []
        ppath = Path(("p",), "p", op.steps, None)
        if "p" in res.reads | res.writes:
            if not member:
                raise Reject(n, "method of a local object of class `%s`, which has parameters" % op.t.cname)
            objargs.append(self.read_path(ppath, n))
        if "s" in res.reads | res.writes:
            objargs.append(self.read_path(op, n))
        opath = None
        if ("o" in res.writes or "olive" in res.reads) and OUTPUT_LOG[0]:
            opath = Path(("o",), "o", [], None)     # one log for every object: the calls in order
            objargs.append(self.read_path(opath, n))
            if "olive" in res.reads:
                self.reads.add("olive")
        elif "o" in res.writes:
            if not member or len(op.steps) != 1:
                raise Reject(n, "method of an object of class `%s` that is not a direct member, and writes boundary outputs" % op.t.cname)
            fld = self.ctx.sub_output(op.steps[0][1], sub)
            opath = Path(("o",), "o", [("f", fld)], None)
            objargs.append(self.read_path(opath, n))
        if "r" in res.reads:
            if not member or len(op.steps) != 1:
                raise Reject(n, "method of an object of class `%s` with reference members that is not a direct member" % op.t.cname)
            fields = []
            pre_r = []
            for rf, arg in self.ctx.sub_refs(op.steps[0][1], op.t.info, n):
                p_, v_ = self.expr(arg)
                pre_r += p_
                fields.append("%s := %s" % (rf, v_.text))
            pre0 = pre0 + pre_r
            objargs.append(V("{ %s }" % ", ".join(fields), ATOM))
        if res.uses_inp:
            if not member or len(op.steps) != 1:
                raise Reject(n, "method of an object of class `%s` that is not a direct member, and reads boundary inputs" % op.t.cname)
            objargs.append(V("inp." + self.ctx.sub_input(op.steps[0][1], sub), ATOM))
            self.reads.add("inp")
        if res.uses_own:
            # the values this member reads through its back-reference to this object, computed now
            if not member or len(op.steps) != 1:
                raise Reject(n, "method of an object of class `%s` with a back-reference that is not a direct member" % op.t.cname)
            helper = self.ctx.owner_helper(op.steps[0][1], sub, n)
            objargs.append(V("(%s p s)" % helper, ATOM))
            self.reads |= {"p", "s"}
            self.deps.add(("own", self.ctx.rec.id, op.steps[0][1]))
        setters = {"s": lambda v: self.write_path(op, v, n), "p": lambda v: self.write_path(ppath, v, n),
                   "o": lambda v: self.write_path(opath, v, n)}
        pre, vals, outs = self.call_args(res.cparams, args, n)
        p2, v = self.apply_call("%s.%s" % (op.t.info.lean, res.lean), res.writes, objargs, vals, outs, res.ret, n, setters)
        return pre0 + pre + p2, v

    def temporary_call(self, n, obj, ot, mdecl, mname, args):
        """A member function called on a temporary object (the value of an expression): its
        state is passed, a state it writes is discarded with the temporary."""
        pre0, v = self.expr(obj)
        if not (pre0 == [] or self.is_constant(v)):
            t = self.temp()
            pre0 = pre0 + ["let %s := %s" % (t, v.text)]
            v = V(t, ATOM)
        sub = self.u.context(ot.info, n)
        self.deps.add(("T", ot.info.id))
        res = sub.method(sub.resolve(mdecl, virtual_dispatch=True), n)
        self.deps.add(res.bid)
        if "s" in res.writes and obj.get("valueCategory") == "lvalue":
            raise Reject(n, "call of non-const `%s` on an object returned by reference (the write would reach the referenced object)" % mname)
        if res.noeffect or "p" in res.reads | res.writes or res.uses_inp or "r" in res.reads or "o" in res.writes or "olive" in res.reads:
            raise Reject(n, "call of `%s` on a temporary object of class `%s` with parameters, inputs or references" % (mname, ot.cname))
        objargs = [v] if "s" in res.reads | res.writes else []
        pre, vals, outs = self.call_args(res.cparams, args, n)
        p2, val = self.apply_call("%s.%s" % (ot.info.lean, res.lean), res.writes, objargs, vals, outs, res.ret, n, {"s": None})
        return pre0 + pre + p2, val

    def boundary_call(self, n, obj, mdecl, mname, args, static=False):
        """A call on a boundary object. A const member function: its result and the values it
        writes into reference parameters are Inputs fields. A non-const one returning void: its
        arguments are Outputs fields (one per parameter; the last call's values), or with
        --output-log an `Output` event appended in call order. A static function of a boundary
        class, or a --boundary-call member function, returning a value is read like a const one;
        one returning void, or whose result is discarded, is an output."""
        if self.ctx is None:
            raise Reject(n, "boundary object used outside a member function")
        if mdecl is not None and qualified_name(self.u, mdecl) in BOUNDARY_STATIC:
            # `ahrs.calc_trig(rot, ...)` (AP_AHRS_View.cpp:80): a member function of the boundary class
            # that reads nothing of its object, translated as a function of its arguments
            fr = self.u.boundary_static_result(mdecl, n)
            self.deps.add(fr.key)
            pre, vals, outs = self.call_args(fr.cparams, args, n)
            p2, v = self.apply_call(self.qual(self.u.ns, fr.lean), set(), [], vals, outs, fr.ret, n, {})
            return pre + p2, v
        params = [p for p in kids(mdecl) if p.get("kind") == "ParmVarDecl"] if mdecl else []
        refs = []
        for p in params:
            q = p["type"]["qualType"].rstrip()
            refs.append(q.endswith("&") and not q.endswith("&&") and not q.startswith("const "))
        is_const = mdecl is not None and (mdecl["type"]["qualType"].rstrip().endswith("const") or qualified_name(self.u, mdecl) in BOUNDARY_QUERY)
        if static and ctype_of(n).kind != "void" and self.discard_node is not n:
            is_const = True                 # a query of the environment
        if mdecl is not None and not is_const:
            if OUTPUT_LOG[0]:
                if (ctype_of(n).kind != "void" and self.discard_node is not n) or any(refs):
                    raise Reject(n, "call of non-const `%s` on a boundary object whose result is used or with reference parameters (outputs are calls whose result is discarded)" % mname)
                return self.output_event(n, obj, mname, args, params), None
            if ctype_of(n).kind != "void" or any(refs):
                raise Reject(n, "call of non-const method `%s` on a boundary object with a result or reference parameters (only `void` outputs are translated)" % mname)
            pre, vals = self.operands([kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in args])
            lines = list(pre)
            for i, (a, v) in enumerate(zip(args, vals)):
                pname = params[i].get("name", "arg%d" % i) if i < len(params) else "arg%d" % i
                t = ctype_of(kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a)
                if not (t.is_scalar() or t.kind == "record"):
                    raise Reject(a, "boundary output of type `%s`" % t.cname)
                fld = self.ctx.output_field(obj, mname, pname if len(args) > 1 else None, t,
                                            "%s` of `%s.%s(%s)" % (pname, obj, mname, ", ".join(pp.get("name", "?") for pp in params)), n)
                lines.append(self.write_path(Path(("o",), "o", [("f", fld)], t), v, n))
            if not args:
                raise Reject(n, "call of non-const method `%s` without arguments on a boundary object" % mname)
            return lines, None
        if self.is_live(strip_parens(kids(n)[0]) if n.get("kind") == "CXXMemberCallExpr" and kids(n) else n) and n.get("kind") == "CXXMemberCallExpr":
            # a const call on a live boundary object: each value it writes into a reference
            # parameter and its result are functions of the log so far and of the other arguments
            vargs = [a for i, a in enumerate(args) if not (i < len(refs) and refs[i])]
            sig = "%s.%s(%s)" % (obj, mname, ", ".join(pp.get("name", "?") for pp in params))
            lines = []
            for i, a in enumerate(args):
                if i < len(refs) and refs[i]:
                    self.var_views = True
                    try:
                        r = self.resolve_path(a)
                    finally:
                        self.var_views = False
                    if r is None:
                        raise Reject(a, "argument for a reference parameter of a boundary call that is not a variable, member or element")
                    pre_a, path = r
                    pname = params[i].get("name", "arg%d" % i)
                    pre_v, v = self.live_read(a, obj, mname + "." + pname, vargs, path.t, "%s writes %s" % (sig, pname))
                    lines += pre_a + pre_v + [self.write_path(path, v, a)]
            if ctype_of(n).kind == "void":
                if not lines:
                    raise Reject(n, "const `void` call on a boundary object without reference parameters (no effect)")
                return lines, None
            pre_v, v = self.live_read(n, obj, mname, vargs, ctype_of(n), sig)
            return lines + pre_v, v
        pre = []
        consts = []
        for i, a in enumerate(args):
            if i < len(refs) and refs[i]:
                r = self.resolve_path(a)
                if r is None:
                    raise Reject(a, "argument for a reference parameter of a boundary call that is not a variable, member or element")
                pre_a, path = r
                pname = params[i].get("name", "arg%d" % i)
                fld = self.ctx.input_field(obj, mname + "." + pname, True, [], path.t,
                                           "%s.%s(%s) writes %s" % (obj, mname, ", ".join(pp.get("name", "?") for pp in params), pname), a)
                self.reads.add("inp")
                pre += pre_a + [self.write_path(path, V("inp.%s" % fld, ATOM), a)]
            else:
                consts.append(a)
        if ctype_of(n).kind == "void":
            if not pre:
                raise Reject(n, "const `void` call on a boundary object without reference parameters (no effect)")
            return pre, None
        v = self.boundary_read(n, obj, mname, True, consts)
        return pre, v

    def param_conversion(self, v, pt, n):
        """A parameter's value v (of its scalar type pt) as the result of the conversion n:
        `explicit operator double ()` and `operator int ()` of AP_Float (AP_Param.h:1010-1016)
        convert it; `get()` and `operator const float &()` do not."""
        rt = ctype_of(n)
        if rt.is_scalar() and pt is not None and pt.is_scalar() and rt != pt:
            return conv(v, pt, rt, n)
        return v

    def param_value(self, n):
        """The value of an expression of a parameter class (a parameter member, a parameter passed
        by value, `c ? p1 : p2` of two of them), or None."""
        n = strip_object(n)
        if n.get("kind") == "MemberExpr":
            f = self.this_field(n)
            if f is not None and f.category == "param":
                return [], self.read_path(Path(("p",), "p", [("f", f.lean)], f.t), n)
            return None
        if n.get("kind") == "DeclRefExpr" and n["referencedDecl"]["id"] in self.param_vars:
            return self.e_DeclRefExpr(n)
        if n.get("kind") == "ConditionalOperator":
            c_n, a_n, b_n = kids(n)
            a, b = self.param_value(a_n), self.param_value(b_n)
            if a is None or b is None or a[0] or b[0]:
                return None
            pre_c, c = self.cond(c_n)
            return pre_c, V("if %s then %s else %s" % (c.text, a[1].text, b[1].text), LOW)
        return None

    def member_param_path(self, obj):
        """For `lin.expo`: a parameter member of a direct member object: (Path p.lin.expo, FieldInfo)."""
        if obj.get("kind") != "MemberExpr" or self.ctx is None:
            return None
        base = strip_object(kids(obj)[0])
        if base.get("kind") != "MemberExpr":
            return None
        r = self.resolve_path(base)
        if r is None or r[0] or r[1].root[0] != "s" or not all(k == "f" for k, _ in r[1].steps) or \
                r[1].t is None or r[1].t.kind != "record" or r[1].t.info.kind != "class":
            return None
        f = r[1].t.info.field_by_id(obj.get("referencedMemberDecl"))
        if f is None or f.category != "param":
            return None
        return Path(("p",), "p", list(r[1].steps) + [("f", f.lean)], f.t), f

    def param_accessor(self, obj):
        """For `kP()` in `kP().set_default(x)`: a call without arguments of a member function whose
        body is `return _kp;` with `_kp` a parameter member (of this object, or of a direct member
        object `_pid.kP()`): (pre, Path of the parameter, FieldInfo), else None."""
        if obj.get("kind") != "CXXMemberCallExpr" or kids(obj)[1:] or self.ctx is None:
            return None
        callee = strip_parens(kids(obj)[0])
        if callee.get("kind") != "MemberExpr":
            return None
        base = strip_object(kids(callee)[0])
        decl = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
        if decl is None or self.u.parent_record(decl) is None:
            return None
        if base.get("kind") == "CXXThisExpr":
            ctx, steps = self.ctx, []
        else:
            r = self.resolve_path(base)
            if r is None or r[0] or r[1].root[0] != "s" or not all(k == "f" for k, _ in r[1].steps) or \
                    r[1].t is None or r[1].t.kind != "record" or r[1].t.info.kind != "class":
                return None
            ctx, steps = self.u.context(r[1].t.info, obj), list(r[1].steps)
        target = ctx.resolve(decl, virtual_dispatch=True)
        body = self.u.body_of(target)
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None) if body else None
        if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
            return None
        e = strip_object(kids(kids(cs)[0])[0])
        if e.get("kind") != "MemberExpr" or strip_object(kids(e)[0]).get("kind") != "CXXThisExpr":
            return None
        f = ctx.rec.field_by_id(e.get("referencedMemberDecl"))
        if f is None or f.category != "param":
            return None
        return [], Path(("p",), "p", steps + [("f", f.lean)], f.t), f

    def alias_args(self, target, args):
        """For a call of member function `target` of this object: the reference arguments that are
        members of this object (`calc_dt_speed_max(..., _destination_speed_max, ...)`, SplineCurve.cpp:93)
        and that the callee also reaches through `this` (transitively): ((index, path steps), ...),
        else None. In C++ the parameter and the member are one object, so the callee is translated
        for this call with the parameter replaced by the member (Context.method)."""
        params = [p for p in kids(self.u.body_of(target) or target) if p.get("kind") == "ParmVarDecl"]
        out = []
        for i, a in enumerate(args):
            if i >= len(params) or a.get("kind") == "CXXDefaultArgExpr":
                continue
            q = params[i]["type"]["qualType"].rstrip()
            if not q.endswith("&") or q.endswith("&&"):
                continue
            sa = strip_object(a)
            base = sa
            while base.get("kind") in ("MemberExpr", "ArraySubscriptExpr") and kids(base):
                inner = strip_object(kids(base)[0])
                if inner.get("kind") == "ImplicitCastExpr" and inner.get("castKind") == "ArrayToPointerDecay":
                    inner = strip_object(kids(inner)[0])
                if inner.get("kind") == "CXXThisExpr":
                    break
                base = inner
            if base.get("kind") != "MemberExpr" or strip_object(kids(base)[0]).get("kind") != "CXXThisExpr":
                continue
            f = self.ctx.rec.field_by_id(base.get("referencedMemberDecl"))
            if f is None or f.category != "state" or f.id not in self.ctx.fields_reached(target):
                continue
            r = self.resolve_path(a)
            if r is None or r[0] or r[1].root[0] != "s" or any(k != "f" for k, _ in r[1].steps):
                raise Reject(a, "reference argument `%s`, a part of this object that the called member function also reaches through `this`, by a path other than data members" % (self.u.text_of(a) or "?"))
            out.append((i, tuple(r[1].steps)))
        return tuple(out) or None

    def object_accessor(self, n):
        """For `get_rate_roll_pid()` (AC_AttitudeControl.h:83, overridden in
        AC_AttitudeControl_Multi.h:50 by `return _pid_rate_roll;`): a call without arguments, on
        this object or on a member object, of a member function that returns a reference and whose
        body (after virtual dispatch) is `return m;` with m a data member: (pre, Path of m), else
        None. The call is then the member itself, so `get_rate_roll_pid().reset_I()` is a call on
        `_pid_rate_roll` and `get_pid_info().slew_rate` a read of `_pid_info.slew_rate`."""
        if n.get("kind") != "CXXMemberCallExpr" or kids(n)[1:] or self.ctx is None:
            return None
        callee = strip_parens(kids(n)[0])
        if callee.get("kind") != "MemberExpr":
            return None
        base = strip_object(kids(callee)[0])
        decl = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
        if decl is None or self.u.parent_record(decl) is None:
            return None
        if base.get("kind") == "CXXThisExpr":
            ctx, pre, root = self.ctx, [], None
        else:
            r = self.resolve_path(base)
            if r is None or r[1].root[0] not in (("s", "var") if self.var_views else ("s",)) or not all(k == "f" for k, _ in r[1].steps) or \
                    r[1].t is None or r[1].t.kind != "record" or r[1].t.info.kind != "class":
                return None
            ctx, pre, root = self.u.context(r[1].t.info, n), r[0], r[1]
        qualified = "::" in (self.u.text_of(callee) or "")
        target = ctx.resolve(decl, virtual_dispatch=not qualified)
        if not returns_reference(target):
            return None
        body = self.u.body_of(target)
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None) if body else None
        if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
            return None
        e = strip_object(kids(kids(cs)[0])[0])
        c = strip_parens(kids(e)[0]) if e.get("kind") == "UnaryOperator" and e.get("opcode") == "*" else {}
        if c.get("kind") in ("CStyleCastExpr", "CXXReinterpretCastExpr") and c.get("castKind") == "BitCast" and \
                strip_object(kids(c)[0]).get("kind") == "CXXThisExpr":
            # `Vector2<T> &xy() { return *(Vector2<T> *)this; }`: a writable view of the first members
            vt = ctype_of(e)
            pairs = ctx.layout_prefix(vt, n)
            if root is None:
                root = Path(("s",), "s", [], CType("record", info=ctx.rec))
            return pre, root.extend(("v", (pairs, vt.lean)), vt)
        if e.get("kind") != "MemberExpr" or strip_object(kids(e)[0]).get("kind") != "CXXThisExpr":
            return None
        f = ctx.rec.field_by_id(e.get("referencedMemberDecl"))
        if f is None or f.category not in ("state", "param"):
            return None
        if f.category == "param":
            if root is not None and root.root[0] != "s":
                return None         # a parameter of a local or a reference parameter: not a path of this object
            steps = list(root.steps) if root is not None else []
            return pre, Path(("p",), "p", steps + [("f", f.lean)], f.t)
        if root is None:
            return pre, Path(("s",), "s", [("f", f.lean)], f.t)
        return pre, root.extend(("f", f.lean), f.t)

    def param_call(self, n, f, mname, args, path=None):
        path = path or Path(("p",), "p", [("f", f.lean)], f.t)
        if (mname == "get" or mname.startswith("operator ")) and not args:
            return [], self.param_conversion(self.read_path(path, n), f.t, n)
        if (mname == "set" or (AP_PARAM[0] and mname in ("set_and_save", "set_and_save_ifchanged", "set_and_notify", "set_and_default"))) and len(args) == 1:
            # set_and_default also registers the default with AP_Param (storage, outside the model)
            pre, v = self.expr(args[0])
            return pre + [self.write_path(path, v, n)], None
        pname = "_".join(x for k, x in path.steps if k == "f")
        if AP_PARAM[0] and mname == "configured" and not args:
            # whether the parameter was configured in storage: an input (AP_Param storage is outside the model)
            fld = self.ctx.input_field("AP_Param", "%s.configured" % pname, True, [], BOOL, "%s.configured()" % f.name, n)
            self.reads.add("inp")
            return [], V("inp.%s" % fld, ATOM)
        if AP_PARAM[0] and mname == "set_default" and len(args) == 1:
            # AP_ParamT.cpp:45-51: `if (!configured()) set(v)` (the default's registration is storage)
            pre, v = self.expr(args[0])
            fld = self.ctx.input_field("AP_Param", "%s.configured" % pname, True, [], BOOL, "%s.configured()" % f.name, n)
            self.reads.add("inp")
            return pre + ["if !inp.%s then" % fld, "  " + self.write_path(path, v, n)], None
        if AP_PARAM[0] and mname in ("save", "load", "notify") and all(a.get("kind") == "CXXDefaultArgExpr" for a in args):
            return ["pure ()  -- C++ `%s.%s()`: AP_Param storage, outside the model (--ap-param)" % (f.name, mname)], None
        raise Reject(n, "method `%s` of parameter class `%s` (get, set, the conversion and unary minus are translated)" % (mname, f.decl["type"]["qualType"]))

    def e_CXXOperatorCallExpr(self, n):
        name = operator_name(n)
        args = kids(n)[1:]
        r = self.index_view_path(n)
        if r is not None:
            pre, p = r
            return pre, self.read_path(p, n)
        if name == "operator-" and len(args) == 1:
            f = self.this_field(strip_object(args[0])) if strip_object(args[0]).get("kind") == "MemberExpr" else None
            if f is not None and f.category == "param":
                v = self.read_path(Path(("p",), "p", [("f", f.lean)], f.t), n)
                return [], V("-" + v.at(ATOM), NEG)
        if AP_PARAM[0] and len(args) == 2 and name in ("operator+", "operator-", "operator*", "operator/", "operator>",
                                                         "operator<", "operator<=", "operator>="):
            # AP_ParamT<float>'s PARAM_SELF_OPER (AP_Param.h, clang only): `this->_value OP other._value`
            a, b = self.param_value(args[0]), self.param_value(args[1])
            if a is not None and b is not None:
                sym = name[len("operator"):]
                pre = a[0] + b[0]
                if sym in self.ARITH:
                    return pre, self.binop_text(sym, a[1], b[1], FLOAT, n)
                return pre, V("decide (%s %s %s)" % (a[1].at(CMP + 1), self.REL[sym], b[1].at(CMP + 1)), APP)
        callee = strip_parens(kids(n)[0])
        if callee.get("kind") == "ImplicitCastExpr":
            callee = strip_parens(kids(callee)[0])
        decl = self.u.canonical(self.u.decl(callee.get("referencedDecl", {}).get("id")))
        if name == "operator=" and len(args) == 2 and ctype_of(n).kind == "record" and \
                (decl is None or decl.get("isImplicit") or decl.get("explicitlyDefaulted") or self.u.body_of(decl) is None):
            pre_r, v = self.expr(args[1])
            pre_l, p = self.lvalue(args[0], n)
            return pre_r + pre_l + [self.write_path(p, v, n)], self.read_path(p, n)
        if decl is not None and operator_word(name) is not None:
            if decl.get("kind") == "CXXMethodDecl" and self.u.parent_record(decl) is not None:
                # a member operator of a translated class: a call of that member on the first operand
                return self.member_call(n, None, decl, strip_object(args[0]), name, args[1:])
            if decl.get("kind") == "FunctionDecl":
                target = self.u.function_for(decl)
                if target is not None:
                    fr = self.u.free_result(target, n)
                    self.deps.add(target["id"])
                    pre, vals, outs = self.call_args(fr.cparams, args, n)
                    p2, v = self.apply_call(self.qual(self.u.ns, fr.lean), set(), [], vals, outs, fr.ret, n, {})
                    return pre + p2, v
        raise Reject(n, "overloaded operator `%s`" % name)

    def e_CXXTemporaryObjectExpr(self, n):
        return self.e_CXXConstructExpr(n)

    def e_CXXConstructExpr(self, n):
        t = ctype_of(n)
        args = kids(n)
        if t.kind == "record":
            info = t.info
            if len(args) == 1 and ctype_of(args[0]) == t:
                return self.expr(args[0])       # copy or move construction: the value
            ctor = info.find_ctor(n.get("ctorType", {}).get("qualType", ""))
            if ctor is None:
                if args:
                    raise Reject(n, "construction of `%s` with arguments and no matching constructor" % info.cxx)
                return [], V("{}", ATOM)
            sub = self.u.context(info, n)
            self.deps.add(("T", info.id))
            res = sub.ctor(ctor, top=True, node=n)
            self.deps.add(res.bid)
            if res.has_params:
                raise Reject(n, "construction of a local or temporary object of class `%s`, which has parameters" % info.cxx)
            if res.uses_inp:
                raise Reject(n, "construction of a local or temporary object whose constructor reads boundary inputs")
            pre, vals, outs = self.call_args(res.cparams, args, n)
            if outs:
                raise Reject(n, "constructor with reference parameters")
            call = app("%s.%s" % (info.lean, res.lean), *vals) if vals else V("%s.%s" % (info.lean, res.lean), ATOM)
            return pre, call
        if t.kind == "param" and len(args) == 1 and strip_object(args[0]).get("kind") == "DeclRefExpr" and \
                strip_object(args[0])["referencedDecl"]["id"] in self.param_vars:
            return self.e_DeclRefExpr(strip_object(args[0]))
        if t.kind == "param" and len(args) == 1:
            a = strip_object(args[0])
            f = self.this_field(a) if a.get("kind") == "MemberExpr" else None
            if f is not None and f.category == "param":      # a parameter copied (passed by value): its value
                return [], self.read_path(Path(("p",), "p", [("f", f.lean)], f.t), n)
            acc = self.param_accessor(a)
            if acc is not None:     # `is_zero(get_rate_yaw_pid().kP())`: the parameter the accessor returns, copied
                return acc[0], self.read_path(acc[1], n)
        if t.kind in ("boundary", "param"):
            raise Reject(n, "construction of an object of class `%s`" % t.name)
        if len(args) == 1:
            return self.expr(args[0])
        raise Reject(n, "construction of `%s`" % t.cname)

    # -- operators ---------------------------------------------------------------------------

    def e_UnaryOperator(self, n):
        op = n["opcode"]
        c = kids(n)[0]
        t = ctype_of(n)
        if op in ("++", "--"):
            return self.incdec(n, want_value=True)
        if op == "*" and strip_object(c).get("kind") == "CXXThisExpr" and self.ctx is not None:
            self.reads.add("s")
            return [], V("s", ATOM)             # `*this`: the object, i.e. the state
        if op == "*" and self.ctx is not None and strip_parens(c).get("kind") in ("CStyleCastExpr", "CXXReinterpretCastExpr") \
                and strip_parens(c).get("castKind") == "BitCast" and strip_object(kids(strip_parens(c))[0]).get("kind") == "CXXThisExpr":
            return [], self.prefix_view(n, t)
        if op == "*" and self.nullable_ref(c) is not None:
            rid = self.nullable_ref(c)
            self.read.add(rid)
            return [], V(self.vars[rid][0], ATOM)       # the pointee of a nullable out-pointer
        if op in ("&", "*"):
            raise Reject(n, "pointer operation `%s`" % op)
        pre, v = self.expr(c)
        if op == "-":
            return pre, V("-" + v.at(ATOM), NEG)
        if op == "+":
            return pre, v
        if op == "!":
            return pre, V("!" + v.at(ATOM), NOT)
        if op == "~":
            if not t.is_int():
                raise Reject(n, "`~` on `%s`" % t.cname)
            return pre, V("~~~" + v.at(ATOM), APP)
        raise Reject(n, "unary operator `%s`" % op)

    def prefix_view(self, n, t):
        """`*(const S *)this` (Vector3's `xy()`): the object read as a value of S, where the data
        members of S are the first data members of this class, with the same names and types, in
        the same order (S is a layout prefix). The value is `{ x := s.x, y := s.y }`; writes through
        the non-const view are rejected where they happen (no lvalue, no non-const call on it)."""
        pairs = self.ctx.layout_prefix(t, n)
        self.reads.add("s")
        return V("{ %s }" % ", ".join("%s := s.%s" % (th, mi) for th, mi in pairs), ATOM)

    def field_index_view(self, mdecl):
        """For `T &operator[](uint8_t i) { T *_v = &x; return _v[i]; }` (Vector3, Vector2): the data
        members that index i names, [FieldInfo] from x on, all of type T; else None."""
        body = self.u.body_of(mdecl)
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None) if body else None
        ps = [p for p in kids(mdecl) if p.get("kind") == "ParmVarDecl"]
        if cs is None or len(kids(cs)) != 2 or len(ps) != 1:
            return None
        d, r = kids(cs)
        if d.get("kind") != "DeclStmt" or len(kids(d)) != 1 or r.get("kind") != "ReturnStmt" or not kids(r):
            return None
        v = kids(d)[0]
        init = strip_parens(kids(v)[0]) if kids(v) else {}
        if v.get("kind") != "VarDecl" or init.get("kind") != "UnaryOperator" or init.get("opcode") != "&":
            return None
        mem = strip_parens(kids(init)[0])
        if mem.get("kind") != "MemberExpr" or strip_object(kids(mem)[0]).get("kind") != "CXXThisExpr":
            return None
        sub = strip_parens(kids(r)[0])
        if sub.get("kind") != "ArraySubscriptExpr":
            return None
        base, idx = [strip_object(x) for x in kids(sub)]
        while idx.get("kind") == "ImplicitCastExpr":
            idx = strip_parens(kids(idx)[0])
        if base.get("kind") != "DeclRefExpr" or base["referencedDecl"]["id"] != v["id"] or \
                idx.get("kind") != "DeclRefExpr" or idx["referencedDecl"]["id"] != ps[0]["id"]:
            return None
        rec = self.u.parent_record(mdecl)
        fields = rec.all_fields() if rec else []
        k = next((i for i, f in enumerate(fields) if f.id == mem["referencedMemberDecl"]), None)
        if k is None:
            return None
        out = []
        for f in fields[k:]:
            if f.t != fields[k].t or f.category != "state":
                break
            out.append(f)
        return out

    def index_view_path(self, n):
        """(pre, Path) of `v[k]` where operator[] is a field index view and k a constant, or None."""
        name = operator_name(n)
        if name != "operator[]" or len(kids(n)) != 3:
            return None
        callee = strip_parens(kids(n)[0])
        if callee.get("kind") == "ImplicitCastExpr":
            callee = strip_parens(kids(callee)[0])
        decl = self.u.canonical(self.u.decl(callee.get("referencedDecl", {}).get("id")))
        if decl is None or decl.get("kind") != "CXXMethodDecl":
            return None
        fields = self.field_index_view(decl)
        if fields is None:
            return None
        k = self.const_int(kids(n)[2])
        if k is None or not 0 <= k < len(fields):
            raise Reject(n, "`operator[]` of `%s` with an index that is not a constant in [0, %d) (it indexes the data members from `%s` on)" % (
                self.u.parent_record(decl).cxx, len(fields), fields[0].name))
        obj = kids(n)[1]
        if strip_object(obj).get("kind") == "CXXThisExpr":
            f = fields[k]
            return [], Path(("s",), "s", [("f", f.lean)], f.t)
        r = self.resolve_path(obj)
        if r is None:
            raise Reject(n, "`operator[]` on an object that is not a variable, member or element")
        pre, bp = r
        return pre, bp.extend(("f", fields[k].lean), fields[k].t)

    def incdec(self, n, want_value):
        if strip_object(kids(n)[0]).get("referencedMemberDecl") in BIT1_FIELDS:
            raise Reject(n, "`%s` on a one-bit bit-field" % n["opcode"])
        pre, p = self.lvalue(kids(n)[0], n)
        t = p.t
        if t.kind not in ("int", "float", "double"):
            raise Reject(n, "`%s` on `%s`" % (n["opcode"], t.cname))
        one = lit("1", t) if t.is_int() else lit("1.0", t)
        op = "+" if n["opcode"] == "++" else "-"
        cur = self.read_path(p, n)
        upd = self.write_path(p, V("%s %s %s" % (cur.text, op, one.text), ADD), n)
        if not want_value:
            return pre + [upd], None
        if n.get("isPostfix"):
            tmp = self.temp()
            return pre + ["let %s := %s" % (tmp, cur.text), upd], V(tmp, ATOM)
        return pre + [upd], self.read_path(p, n)

    def mark_assigned(self, rid):
        if rid in self.uninit and self.da is not DIVERGE:
            self.da.add(rid)

    def assign(self, n, want_value):
        lhs, rhs = kids(n)
        sl = strip_object(lhs)
        if sl.get("kind") == "MemberExpr" and self.boundary_obj(kids(sl)[0]) is not None:
            # `AP_Notify::flags.armed = arm`: a write to a boundary object
            if not OUTPUT_LOG[0] or want_value:
                raise Reject(n, "assignment to member `%s` of a boundary object (an output only with --output-log, as a statement)" % sl.get("name"))
            obj = self.boundary_obj(kids(sl)[0])
            pre, v = self.expr(rhs)
            t = ctype_of(sl)
            if not (t.is_scalar() or t.kind == "record"):
                raise Reject(n, "boundary output of type `%s`" % t.cname)
            name = self.u.output_ctor(obj, "=" + sl["name"], [(sl["name"], t)], "%s.%s = %s" % (obj, sl["name"], t.cname), n)
            self.writes.add("o")
            self.reads.add("o")
            return pre + ["o := o.push %s" % app("Output.%s" % name, conv(v, ctype_of(rhs), t, rhs)).at(ATOM)], None
        pre, v = self.expr(rhs)
        pre_l, p = self.lvalue(lhs, n)
        v = self.bit1_store(lhs, v, p.t)
        pre = pre + pre_l + [self.write_path(p, v, n)]
        return pre, (self.read_path(p, n) if want_value else None)

    def bit1_store(self, lhs, v, t):
        """The value stored into lhs: modulo 2 if lhs is a one-bit unsigned bit-field (C++ converts
        the value to the field's width, [conv.integral])."""
        sl = strip_object(lhs)
        if sl.get("kind") == "MemberExpr" and sl.get("referencedMemberDecl") in BIT1_FIELDS:
            return V("%s &&& %s" % (v.at(BAND), lit("1", t).at(BAND + 1)), BAND)
        return v

    def compound(self, n, want_value):
        lhs, rhs = kids(n)
        pre, r = self.expr(rhs)
        pre_l, p = self.lvalue(lhs, n)
        t = p.t
        lt = ctype_of(n, "computeLHSType")
        rt = ctype_of(n, "computeResultType")
        op = n["opcode"][:-1]
        x = conv(self.read_path(p, n), t, lt, n)
        rty = ctype_of(rhs)
        if op in ("<<", ">>"):
            r = conv(r, rty, lt, n)
        elif rty != lt:
            raise Reject(n, "compound assignment with operand of type `%s`" % rty.cname)
        res = self.binop_text(op, x, r, lt, n)
        res = self.bit1_store(lhs, conv(res, rt, t, n), t)
        pre = pre + pre_l + [self.write_path(p, res, n)]
        return pre, (self.read_path(p, n) if want_value else None)

    def e_CompoundAssignOperator(self, n):
        return self.compound(n, True)

    ARITH = {"+": ("+", ADD), "-": ("-", ADD), "*": ("*", MUL), "/": ("/", MUL), "%": ("%", MUL),
             "&": ("&&&", BAND), "|": ("|||", BOR), "^": ("^^^", BXOR), "<<": ("<<<", SHIFT), ">>": (">>>", SHIFT)}
    REL = {"<": "<", ">": ">", "<=": "≤", ">=": "≥"}

    def binop_text(self, op, a, b, t, n):
        if op in ("%", "&", "|", "^", "<<", ">>") and not t.is_int():
            raise Reject(n, "operator `%s` on `%s`" % (op, t.cname))
        sym, p = self.ARITH[op]
        return V("%s %s %s" % (a.at(p), sym, b.at(p + 1)), p)

    def e_BinaryOperator(self, n, as_prop=False):
        op = n["opcode"]
        if op == "=":
            return self.assign(n, True)
        if op == ",":
            return self.comma(n)
        if op in ("&&", "||"):
            return self.logical(n)
        k = self.array_size(n)
        if k is not None:
            return [], lit(str(k), ctype_of(n))
        a_n, b_n = kids(n)
        if op in ("==", "!=") and (self.nullable_ref(a_n) is not None or self.nullable_ref(b_n) is not None) and \
                (self.is_null(a_n) or self.is_null(b_n)):
            g = self.nullable[self.nullable_ref(a_n) if self.nullable_ref(a_n) is not None else self.nullable_ref(b_n)]
            return [], V(g if op == "!=" else "!" + g, ATOM if op == "!=" else NOT)
        pre, (a, b) = self.operands([a_n, b_n])
        ta, tb = ctype_of(a_n), ctype_of(b_n)
        if op in self.ARITH:
            t = ctype_of(n)
            if op in ("<<", ">>"):
                b = conv(b, tb, ta, n)
            elif ta != tb or ta != t:
                raise Reject(n, "operator `%s` on `%s` and `%s`" % (op, ta.cname, tb.cname))
            return pre, self.binop_text(op, a, b, t, n)
        if ta != tb:
            raise Reject(n, "comparison of `%s` and `%s`" % (ta.cname, tb.cname))
        if op in ("==", "!="):
            return pre, V("%s %s %s" % (a.at(CMP + 1), op, b.at(CMP + 1)), CMP)
        if op in self.REL:
            if ta.kind == "enum":
                raise Reject(n, "ordering comparison of enum values")
            prop = "%s %s %s" % (a.at(CMP + 1), self.REL[op], b.at(CMP + 1))
            if as_prop:
                return pre, V(prop, CMP)
            return pre, V("decide (%s)" % prop, APP)
        raise Reject(n, "binary operator `%s`" % op)

    def comma(self, n):
        """`a, b`: a for its side effects (its value is discarded), then the value of b."""
        a_n, b_n = kids(n)
        pre_a = self.effect(a_n, discard_pure=True)
        pre_b, b = self.expr(b_n)
        return pre_a + pre_b, b

    def dropped_ref(self, n):
        """The qualified name of the data member or member function (--drop) that n names, or None."""
        n = strip_object(n)
        if n.get("kind") == "MemberExpr":
            return self.u.dropped.get(n.get("referencedMemberDecl"))
        if n.get("kind") == "DeclRefExpr":
            rid = n["referencedDecl"]["id"]
            if rid in self.u.dropped:
                return self.u.dropped[rid]
            d = self.u.decl(rid)
            if d is not None and d.get("kind") == "VarDecl" and qualified_name(self.u, d) in DROP:
                return qualified_name(self.u, d)       # the out-of-line definition of a static member
        return None

    @staticmethod
    def has_effects(n):
        """Can evaluating n change anything (assignments, increments, calls other than of a
        --boundary-fn function, which reads a value such as a clock, new/delete)?"""
        for m in walk(n):
            k = m.get("kind")
            if k == "CallExpr" and kids(m) and not kids(m)[1:]:
                c = strip_parens(kids(m)[0])
                while c.get("kind") == "ImplicitCastExpr":
                    c = strip_parens(kids(c)[0])
                d = CURRENT_UNIT[0].decl(c.get("referencedDecl", {}).get("id")) if c.get("kind") == "DeclRefExpr" and CURRENT_UNIT[0] else None
                if d is not None and d.get("kind") == "FunctionDecl" and qualified_name(CURRENT_UNIT[0], d) in BOUNDARY_FN:
                    continue
            if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr", "CXXNewExpr", "CXXDeleteExpr",
                     "CompoundAssignOperator") or (k == "BinaryOperator" and m.get("opcode") == "=") or \
                    (k == "UnaryOperator" and m.get("opcode") in ("++", "--")):
                return True
        return False

    def left_out(self, n):
        """Does statement n only concern what --drop leaves out of the model: a call of a dropped
        function (arguments without effects), an assignment to a dropped data member (right side
        without effects), an `if` whose condition reads a dropped member and has no effects and
        whose branches are left out?"""
        n = strip_parens(n)
        while n.get("kind") in ("ExprWithCleanups",) or (n.get("kind") in ("CStyleCastExpr", "CXXStaticCastExpr", "ImplicitCastExpr")
                                                         and ctype_of(n).kind == "void"):
            n = strip_parens(kids(n)[0])
        k = n.get("kind")
        if k == "NullStmt":
            return True
        if k == "CompoundStmt":
            return bool(kids(n)) and all(self.left_out(c) for c in kids(n))
        if k == "IfStmt":
            c = kids(n)[0]
            return not self.has_effects(c) and any(self.dropped_ref(m) for m in walk(c) if m.get("kind") in ("MemberExpr", "DeclRefExpr")) \
                and all(self.left_out(x) for x in kids(n)[1:])
        if k == "BinaryOperator" and n.get("opcode") == "=":
            return self.dropped_ref(kids(n)[0]) is not None and not self.has_effects(kids(n)[1])
        if k in ("CallExpr", "CXXMemberCallExpr"):
            c = strip_parens(kids(n)[0])
            if c.get("kind") == "ImplicitCastExpr":
                c = strip_parens(kids(c)[0])
            d = self.u.decl(c.get("referencedMemberDecl") or c.get("referencedDecl", {}).get("id"))
            return d is not None and (d["id"] in self.u.dropped or qualified_name(self.u, d) in DROP) and \
                not any(self.has_effects(a) for a in kids(n)[1:])
        return False

    def effect(self, n, discard_pure=False):
        """Lines for an expression evaluated only for its side effects."""
        s = strip_parens(n)
        k = s.get("kind")
        if k == "BinaryOperator" and s.get("opcode") == "=" and self.dropped_ref(kids(s)[0]) is not None:
            if self.has_effects(kids(s)[1]):
                raise Reject(s, "assignment to `%s` (--drop) whose right side has effects" % self.dropped_ref(kids(s)[0]))
            return ["pure ()  -- C++ `%s`: left out (--drop)" % comment_safe(self.u.text_of(s) or self.dropped_ref(kids(s)[0]))]
        if k == "BinaryOperator" and s.get("opcode") == "=":
            return self.assign(s, False)[0]
        if k == "CompoundAssignOperator":
            return self.compound(s, False)[0]
        if k == "UnaryOperator" and s.get("opcode") in ("++", "--"):
            return self.incdec(s, False)[0]
        if k == "BinaryOperator" and s.get("opcode") == ",":
            return self.effect(kids(s)[0], True) + self.effect(kids(s)[1], discard_pure)
        if k in ("CStyleCastExpr", "CXXStaticCastExpr") and ctype_of(s).kind == "void":
            return self.effect(kids(s)[0], True)
        if k == "ImplicitCastExpr" and ctype_of(s).kind == "void":
            return self.effect(kids(s)[0], discard_pure)
        if k in ("ExprWithCleanups",):
            return self.effect(kids(s)[0], discard_pure)
        saved, self.discard_node = self.discard_node, s if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr") else None
        try:
            pre, v = self.expr(s)
        finally:
            self.discard_node = saved
        if pre:
            # a discarded result bound to a temporary: bind it to `_` (no unused-variable warning)
            if v is not None and re.match(r"^t'\d+$", v.text) and not any(re.search(r"\b%s\b" % re.escape(v.text), l)
                                                                           for l in pre[-1:] if not l.startswith("let ")):
                uses = sum(len(re.findall(r"(?<![\w'])%s(?![\w'])" % re.escape(v.text), l)) for l in pre)
                if uses == 1:
                    pre = [re.sub(r"(?<![\w'])%s(?![\w'])" % re.escape(v.text), "_", l) for l in pre]
            return pre
        if discard_pure:
            return []
        if k in ("CXXMemberCallExpr", "CallExpr", "CXXOperatorCallExpr"):
            raise Reject(n, "call whose result is discarded (no side effect)")
        raise Reject(n, "expression statement without a side effect")

    def logical(self, n):
        op = n["opcode"]
        a_n, b_n = kids(n)
        pre_a, a = self.expr(a_n)
        saved = self.copy_da()
        pre_b, b = self.expr(b_n)
        self.da = saved        # assignments in the right operand may not happen
        sym, p = ("&&", AND) if op == "&&" else ("||", OR)
        if not pre_b:
            return pre_a, V("%s %s %s" % (a.at(p), sym, b.at(p + 1)), p)
        t = self.temp()
        lines = pre_a + ["let mut %s := %s" % (t, a.text),
                         "if %s then" % (t if op == "&&" else "!" + t)]
        lines += ["  " + l for l in pre_b + ["%s := %s" % (t, b.text)]]
        return lines, V(t, ATOM)

    def e_ConditionalOperator(self, n):
        c_n, a_n, b_n = kids(n)
        pre_c, c = self.cond(c_n)
        saved = self.copy_da()
        pre_a, a = self.expr(a_n)
        self.da = self.copy_da(saved)
        pre_b, b = self.expr(b_n)
        self.da = saved
        if not pre_a and not pre_b:
            return pre_c, V("if %s then %s else %s" % (c.text, a.text, b.text), LOW)
        t = self.temp()
        ty = ctype_of(n)
        lines = pre_c + ["let mut %s : %s := %s" % (t, ty.lean, zero_of(ty, n).text), "if %s then" % c.text]
        lines += ["  " + l for l in pre_a + ["%s := %s" % (t, a.text)]]
        lines += ["else"] + ["  " + l for l in pre_b + ["%s := %s" % (t, b.text)]]
        return lines, V(t, ATOM)

    def cond(self, n):
        """A condition of if/?:; a relational comparison is left as a decidable proposition."""
        s = strip_parens(n)
        if s.get("kind") == "BinaryOperator" and s.get("opcode") in self.REL:
            return self.e_BinaryOperator(s, as_prop=True)
        return self.expr(n)

    def copy_da(self, src=0):
        src = self.da if src == 0 else src
        return DIVERGE if src is DIVERGE else set(src)

    # -- statements -------------------------------------------------------------------------

    def ret_line(self, value):
        self.rets.append(value)
        return "return @@RET%d@@" % (len(self.rets) - 1)

    def stmt(self, n):
        k = n.get("kind")
        if k == "CompoundStmt":
            return self.block(kids(n))
        if k == "NullStmt":
            return [], False
        if k == "DeclStmt":
            out = []
            for d in kids(n):
                out += self.local_decl(d)
            return out, False
        if k == "ReturnStmt":
            if not kids(n):
                if not self.void:
                    raise Reject(n, "`return` without a value")
                self.da = DIVERGE
                return [self.ret_line(None)], True
            if self.void:
                pre = self.effect(kids(n)[0], True)
                self.da = DIVERGE
                return pre + [self.ret_line(None)], True
            pre, v = self.expr(kids(n)[0])
            self.da = DIVERGE
            return pre + [self.ret_line(v.text)], True
        if k == "IfStmt":
            if self.left_out(n):
                return ["pure ()  -- C++ `if (%s) ...`: only dropped members, left out (--drop)" %
                        comment_safe(self.u.text_of(kids(n)[0]) or "...")], False
            return self.if_stmt(n)
        if k == "ForStmt":
            return self.for_stmt(n)
        if k == "WhileStmt":
            raise Reject(n, WHILE_BAD)
        if k == "DoStmt":
            raise Reject(n, DO_BAD)
        if k == "SwitchStmt":
            return self.switch_stmt(n)
        if k in ("BreakStmt", "ContinueStmt"):
            if not self.loops:
                raise Reject(n, "`%s` outside a loop" % ("break" if k == "BreakStmt" else "continue"))
            if k == "BreakStmt" and self.loops[-1] == "switch":
                raise Reject(n, "`break` inside a `switch` case other than as the case's last statement")
            loop = next((l for l in reversed(self.loops) if l != "switch"), None)
            if loop is None:
                raise Reject(n, "`continue` outside a loop")
            if k == "ContinueStmt" and loop in ("while", "do"):
                raise Reject(n, "`continue` in a `while` or `do` loop (it would skip the counter step)")
            self.da = DIVERGE
            return ["break" if k == "BreakStmt" else "continue"], True
        named = {"GotoStmt": "`goto`", "LabelStmt": "label", "CXXTryStmt": "exception (`try`)",
                 "GCCAsmStmt": "inline assembly", "MSAsmStmt": "inline assembly", "CXXForRangeStmt": "range-based `for`",
                 "IndirectGotoStmt": "`goto`", "AttributedStmt": "attributed statement",
                 "CaseStmt": "`case` label outside the top level of a `switch` body",
                 "DefaultStmt": "`default` label outside the top level of a `switch` body"}
        if k in named:
            raise Reject(n, named[k])
        return self.effect(n), False

    def local_decl(self, d):
        k = d.get("kind")
        if k != "VarDecl":
            if k in ("TypedefDecl", "TypeAliasDecl", "UsingDecl", "UsingDirectiveDecl", "StaticAssertDecl"):
                return []
            raise Reject(d, "local declaration `%s`" % k)
        if d.get("storageClass") == "static" and self.fn is not None and "name" in d:
            qn = "%s::%s" % (qualified_name(self.u, self.fn), d["name"])
            if qn in DROP:
                # a static local left out of the model (--drop `Function::name`: SCurve::calculate_path's
                # logging latch `logged_scve`); a statement that reads it must be left out too
                if kids(d) and self.has_effects(kids(d)[0]):
                    raise Reject(d, "static local `%s` (--drop) whose initializer has effects" % d["name"])
                self.u.dropped[d["id"]] = qn
                return ["pure ()  -- C++ `%s`: left out (--drop)" % comment_safe(self.u.text_of(d) or d["name"])]
        t, ref = decl_type(d)
        if t.kind == "boundary" and ref is not None and kids(d) and self.boundary_obj(kids(d)[0]) is not None:
            # `AP_BattMonitor &battery = AP::battery();`: another name for the boundary object
            self.boundary_locals[d["id"]] = self.boundary_obj(kids(d)[0])
            return []
        if ref == "mut":
            raise Reject(d, "local reference variable `%s`" % d["name"])
        if ref == "const" and kids(d):
            # `const T &x = e;` is a copy of e only if what e refers to cannot change while x is
            # live: e must be an element or member of a variable this function never assigns
            r = self.resolve_path(kids(d)[0])
            const_fn = self.fn is not None and self.fn.get("kind") == "CXXMethodDecl" and \
                self.fn["type"]["qualType"].rstrip().endswith("const")
            i0 = strip_object(kids(d)[0])
            c0 = strip_parens(kids(i0)[0]) if i0.get("kind") == "CXXMemberCallExpr" else {}
            if r is None and c0.get("kind") == "MemberExpr" and self.boundary_obj(kids(c0)[0]) is not None and \
                    self.is_live(c0) and i0.get("valueCategory") == "lvalue":
                # `const Vector3p& psc_pos_offset_ned_m = _pos_control.get_pos_offset_NED_m();` on a live
                # boundary object (AC_WPNav.cpp:572): the reference names the member, which the calls
                # made after it may change; each use reads it again, with the log as it is then
                if kids(i0)[1:]:
                    raise Reject(d, "local reference `%s` to the result of a live boundary read with arguments" % d["name"])
                self.live_refs[d["id"]] = kids(d)[0]
                return []
            if r is None and c0.get("kind") == "MemberExpr" and self.boundary_obj(kids(c0)[0]) is not None:
                pass        # `const Vector3f &v = _attitude_control.get_att_target_euler_rad();`: a boundary read,
                            # which does not change while the member function runs (README, "Classes"): a copy
            elif r is None or not ((r[1].root[0] == "var" and r[1].root[1] not in self.mutable) or (r[1].root[0] in ("s", "p") and const_fn)):
                raise Reject(d, "local reference `%s` to something that may change while it is live (only references into variables that are never assigned, into the object in a const member function, or to the result of a const call on a boundary object are translated, as copies)" % d["name"])
        quals = d["type"]["qualType"]
        is_const = quals.startswith("const ") or " const" in quals or d.get("constexpr")
        if d.get("storageClass") == "static" and not is_const:
            raise Reject(d, "static local variable `%s` (state across calls)" % d["name"])
        if d.get("storageClass") == "extern":
            raise Reject(d, "extern local declaration")
        if t.kind in ("boundary", "param"):
            raise Reject(d, "local object of class `%s`" % t.name)
        if t.kind == "void":
            raise Reject(d, "void variable")
        name = self.ident(d["name"], d)
        rid = d["id"]
        init = kids(d)[0] if kids(d) else None
        mut = "let mut" if rid in self.mutable else "let"
        if t.kind == "array":
            if init is None or init.get("kind") != "InitListExpr":
                raise Reject(d, "array `%s` without an initializer list" % d["name"])
            pre, v = self.array_init(init, t)
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            return pre + ["%s %s : %s := %s" % (mut, name, t.lean, v.text)]
        if init is None:
            if rid not in self.mutable:
                raise Reject(d, "variable `%s` declared without an initializer and never assigned" % d["name"])
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            self.uninit.add(rid)
            return ["%s %s : %s := %s  -- uninitialized in C++; assigned before every read" % (mut, name, t.lean, zero_of(t, d).text)]
        if init.get("kind") in ("InitListExpr", "ParenListExpr"):
            if t.kind == "record" and not kids(init):
                pre, v = [], V("{}", ATOM)
            else:
                raise Reject(d, "brace or parenthesized initializer list for a scalar or object")
        else:
            pre, v = self.expr(init)
        self.vars[rid] = (name, t)
        self.declared.append((rid, name))
        return pre + ["%s %s : %s := %s" % (mut, name, t.lean, v.text)]

    def array_init(self, init, t):
        elems = kids(init)
        filler = init.get("array_filler")
        if filler is not None:
            if not all(f.get("kind") == "ImplicitValueInitExpr" for f in filler):
                raise Reject(init, "array initializer with a non-zero filler")
        elif len(elems) != t.n:
            raise Reject(init, "array initializer with %d elements for `%s`" % (len(elems), t.cname))
        pre, vals = self.operands(elems)
        if pre:
            raise Reject(init, "array initializer with side effects")
        if filler is not None:
            z = zero_of(t.elem, init)
            if not vals:
                return [], app("Array.replicate", V(str(t.n), ATOM), z)
            return [], V("#[%s] ++ Array.replicate %d %s" % (", ".join(v.text for v in vals), t.n - len(vals), z.at(ATOM)), ADD)
        return [], V("#[%s]" % ", ".join(v.text for v in vals), ATOM)

    def if_stmt(self, n):
        if n.get("hasInit") or n.get("hasVar"):
            raise Reject(n, "`if` with an initializer or a condition variable")
        if n.get("isConstexpr"):
            raise Reject(n, "`if constexpr`")
        parts = kids(n)
        c_n, then_n = parts[0], parts[1]
        else_n = parts[2] if n.get("hasElse") else None
        pre, c = self.cond(c_n)
        before = self.copy_da()
        then_lines, then_div = self.stmt(then_n)
        after_then = self.da
        self.da = self.copy_da(before)
        out = pre + ["if %s then" % c.text]
        out += ["  " + l for l in (then_lines or ["pure ()"])]
        if else_n is None:
            self.da = self.meet(after_then, self.copy_da(before))
            return out, False
        else_lines, else_div = self.stmt(else_n)
        after_else = self.da
        self.da = self.meet(after_then, after_else)
        if strip_parens(else_n).get("kind") == "IfStmt" and else_lines and else_lines[0].startswith("if "):
            out += ["else " + else_lines[0]] + else_lines[1:]
        else:
            out += ["else"] + ["  " + l for l in (else_lines or ["pure ()"])]
        return out, then_div and else_div

    @staticmethod
    def meet(a, b):
        if a is DIVERGE:
            return b
        if b is DIVERGE:
            return a
        return a & b

    def switch_stmt(self, n):
        """`switch` whose cases each end in break/return/continue (or are empty and share the next
        case's body): `match` on an enum, an `if` chain on an integer. The default case, wherever
        it is written, is the last alternative."""
        if n.get("hasInit") or n.get("hasVar"):
            raise Reject(n, "`switch` with an initializer or a condition variable")
        cond, body = kids(n)[0], kids(n)[-1]
        stmts = kids(body) if body.get("kind") == "CompoundStmt" else [body]
        groups = []           # [labels, stmts]; the label None is default
        for s in stmts:
            labels = []
            while s.get("kind") in ("CaseStmt", "DefaultStmt"):
                if s.get("kind") == "CaseStmt":
                    if len(kids(s)) != 2:
                        raise Reject(s, "`case` range")
                    v = kids(s)[0].get("value")
                    if v is None:
                        v = self.const_int(kids(s)[0])
                    if v is None:
                        raise Reject(s, "`case` label that is not a constant")
                    labels.append(int(v))
                    s = kids(s)[1]
                else:
                    labels.append(None)
                    s = kids(s)[0]
            if labels:
                groups.append([labels, []])
            elif not groups:
                raise Reject(s, "statement before the first `case` of a `switch`")
            if s.get("kind") != "NullStmt":
                groups[-1][1].append(s)
        merged, pending = [], []
        for labels, ss in groups:
            if not ss:
                pending += labels
                continue
            merged.append([pending + labels, ss])
            pending = []
        if pending:
            merged.append([pending, []])
        # the condition: an enum (without its promotion to int) or an integer
        c = strip_parens(cond)
        inner = c
        while inner.get("kind") == "ImplicitCastExpr" and inner.get("castKind") in ("IntegralCast", "LValueToRValue", "NoOp"):
            if ctype_of(kids(inner)[0]).kind == "enum":
                inner = kids(inner)[0]
                break
            inner = kids(inner)[0]
        et = ctype_of(inner)
        if et.kind != "enum":
            inner, et = c, ctype_of(c)
            if not et.is_int():
                raise Reject(n, "`switch` on `%s`" % et.cname)
        pre, cv = self.expr(inner)
        before = self.copy_da()
        arms = []
        for gi, (labels, ss) in enumerate(merged):
            ss = list(ss)
            while len(ss) >= 1 and ss[0].get("kind") == "CompoundStmt" and (len(ss) == 1 or (len(ss) == 2 and ss[1].get("kind") == "BreakStmt")):
                # `case X: { ...; break; }` (the braces only scope the case's declarations)
                ss = list(kids(ss[0])) + ss[1:]
            ends = bool(ss) and ss[-1].get("kind") == "BreakStmt"
            if ends:
                ss = ss[:-1]
            self.da = self.copy_da(before)
            self.loops.append("switch")
            self.case_exited = False
            lines, div = self.block(ss)
            self.loops.pop()
            if not div and not ends and gi != len(merged) - 1 and not (self.case_exited and self.falls_off_only_by_exit(ss)):
                raise Reject(ss[-1] if ss else n, "`switch` case that falls through into the next case")
            arms.append((labels, lines, div, self.da))
        if all(None not in l for l, _, _, _ in arms) is False:
            arms = [a for a in arms if None not in a[0]] + [a for a in arms if None in a[0]]
        has_default = any(None in a[0] for a in arms)
        out = list(pre)
        exhaustive = has_default
        reach = []
        if et.kind == "enum":
            e = et.info
            explicit = set()
            for labels, _, _, _ in arms:
                for lab in labels:
                    if lab is not None:
                        nm = e.name_of_value(lab)
                        if nm is None:
                            raise Reject(n, "`case` value %d is not an enumerator of `%s`" % (lab, e.cxx))
                        explicit.add(nm)
            covered_all = len(explicit) == len(e.values)
            out.append("match %s with" % cv.text)
            for labels, lines, div, da in arms:
                if None in labels:
                    if covered_all:
                        pats = [".%s" % e.ctor_names[e.name_of_value(l)] for l in labels if l is not None]
                    else:
                        pats = ["_"]
                else:
                    pats = [".%s" % e.ctor_names[e.name_of_value(l)] for l in labels]
                if not pats:
                    continue
                out.append("| %s =>" % " | ".join(pats))
                out += ["  " + l for l in (lines or ["pure ()"])]
                reach.append((div, da))
            if not has_default and not covered_all:
                out.append("| _ =>")
                out.append("  pure ()")
            exhaustive = has_default or covered_all
        else:
            if not any(l is not None for a in arms for l in a[0]):
                raise Reject(n, "`switch` with only a `default` label")
            t = self.temp()
            out.append("let %s := %s" % (t, cv.text))
            first = True
            for labels, lines, div, da in arms:
                if None in labels:
                    out.append("else")
                else:
                    test = " || ".join("%s == %s" % (t, lit(str(v), et).text) for v in labels)
                    out.append(("if " if first else "else if ") + test + " then")
                    first = False
                out += ["  " + l for l in (lines or ["pure ()"])]
                reach.append((div, da))
        st = DIVERGE
        for div, da in reach:
            st = self.meet(st, da)
        if not exhaustive:
            st = self.meet(st, self.copy_da(before))
        self.da = st
        return out, exhaustive and all(div for div, _ in reach) and bool(reach)

    # -- loops ------------------------------------------------------------------------------

    def const_int(self, n):
        """Value of an integer constant expression, or None."""
        n = strip_parens(n)
        k = n.get("kind")
        if k == "IntegerLiteral":
            return int(n["value"])
        if k == "SubstNonTypeTemplateParmExpr":
            inner = strip_parens(kids(n)[-1])
            if inner.get("kind") == "CharacterLiteral":
                return int(inner["value"])
            return self.const_int(inner)
        if k == "ImplicitCastExpr" and n.get("castKind") in ("IntegralCast", "LValueToRValue", "NoOp"):
            v = self.const_int(kids(n)[0])
            if v is None:
                return None
            t = ctype_of(n)
            if t.is_int():
                m = v % (1 << t.bits)
                return m - (1 << t.bits) if t.signed and m >= 1 << (t.bits - 1) else m
            return None
        if k == "UnaryOperator" and n.get("opcode") in ("-", "+"):
            v = self.const_int(kids(n)[0])
            return None if v is None else (-v if n["opcode"] == "-" else v)
        if k == "BinaryOperator" and n.get("opcode") in ("+", "-", "*"):
            a, b = self.const_int(kids(n)[0]), self.const_int(kids(n)[1])
            if a is None or b is None:
                return None
            return a + b if n["opcode"] == "+" else a - b if n["opcode"] == "-" else a * b
        if k == "DeclRefExpr":
            d = self.u.decl(n["referencedDecl"]["id"])
            if d is not None and d.get("kind") == "VarDecl" and kids(d):
                q = d["type"]["qualType"]
                if (q.startswith("const ") or d.get("constexpr")) and d["id"] not in self.mutable:
                    return self.const_int(kids(d)[0])
        return None

    def loop_counter_step(self, inc, rid):
        inc = strip_parens(inc)
        if inc.get("kind") == "UnaryOperator" and inc.get("opcode") in ("++", "--"):
            tgt = strip_parens(kids(inc)[0])
            if tgt.get("kind") == "DeclRefExpr" and tgt["referencedDecl"]["id"] == rid:
                return 1 if inc["opcode"] == "++" else -1
        if inc.get("kind") == "CompoundAssignOperator" and inc.get("opcode") in ("+=", "-="):
            tgt = strip_parens(kids(inc)[0])
            if tgt.get("kind") == "DeclRefExpr" and tgt["referencedDecl"]["id"] == rid:
                c = self.const_int(kids(inc)[1])
                lt, tt = ctype_of(inc, "computeLHSType"), ctype_of(tgt)
                # a narrow counter (`uint8_t i; i += 2`) is stepped in int and converted back: the
                # same value as long as every value the loop reaches fits (checked by for_stmt)
                if c is not None and c != 0 and (lt == tt or (lt.is_int() and tt.is_int() and lt.bits > tt.bits)):
                    return c if inc["opcode"] == "+=" else -c
        return None

    def trip_count(self, start, op, bound, step):
        """Iterations of `for (i = start; i op bound; i += step)`, or None if unbounded."""
        if op in ("<", "<="):
            if step <= 0:
                return None if (start < bound or (op == "<=" and start == bound)) else 0
            last = bound - 1 if op == "<" else bound
            return 0 if start > last else (last - start) // step + 1
        if op in (">", ">="):
            if step >= 0:
                return None if (start > bound or (op == ">=" and start == bound)) else 0
            last = bound + 1 if op == ">" else bound
            return 0 if start < last else (start - last) // (-step) + 1
        if op == "!=":
            if (bound - start) % step != 0 or (bound - start) // step < 0:
                return None
            return (bound - start) // step
        return None

    def counter_cond(self, cond, rid, t):
        """(op, bound) for a condition `i op C` with C a constant, else None. The counter may be
        promoted (e.g. a uint8_t counter compared with an int constant); the bound must then be a
        value of the counter's type, so the counter reaches it without wrapping."""
        c = strip_parens(cond)
        if c.get("kind") != "BinaryOperator" or c.get("opcode") not in ("<", "<=", ">", ">=", "!="):
            return None
        lhs = strip_parens(kids(c)[0])
        promoted = None
        if lhs.get("kind") == "ImplicitCastExpr" and lhs.get("castKind") == "IntegralCast":
            promoted = ctype_of(lhs)
            lhs = strip_parens(kids(lhs)[0])
        if lhs.get("kind") == "ImplicitCastExpr" and lhs.get("castKind") == "LValueToRValue":
            lhs = strip_parens(kids(lhs)[0])
        if lhs.get("kind") != "DeclRefExpr" or lhs["referencedDecl"]["id"] != rid:
            return None
        ct = promoted if promoted is not None else t
        if ctype_of(kids(c)[1]) != ct:
            return None
        if promoted is not None:
            if not promoted.is_int() or promoted.bits < t.bits or (t.signed and not promoted.signed):
                return None
        elif ctype_of(kids(c)[0]) != t:
            return None
        b = self.const_int(kids(c)[1])
        if b is None:
            return None
        lo, hi = (-(1 << (t.bits - 1)), (1 << (t.bits - 1)) - 1) if t.signed else (0, (1 << t.bits) - 1)
        if not lo <= b <= hi:
            return None
        return c["opcode"], b

    def for_stmt(self, n):
        init, condvar, cond, inc, body = (kids(n) + [{}] * 5)[:5]
        if condvar:
            raise Reject(n, "`for` with a condition variable")
        if not init or not cond or not inc:
            raise Reject(n, FOR_BAD)
        if init.get("kind") == "BinaryOperator" and init.get("opcode") == "=" and \
                strip_parens(kids(init)[0]).get("kind") == "DeclRefExpr" and \
                strip_parens(kids(init)[0])["referencedDecl"]["id"] in self.loop_only:
            # `int8_t i; ... for (i = 0; ...)`: a counter declared before the loop whose every use is
            # in loops that initialize it (README.md, "ArduPilot"); each loop binds it afresh
            d = self.u.decl(strip_parens(kids(init)[0])["referencedDecl"]["id"])
            start_n = kids(init)[1]
        elif init.get("kind") == "DeclStmt" and len(kids(init)) == 1 and kids(init)[0].get("kind") == "VarDecl" and kids(kids(init)[0]):
            d = kids(init)[0]
            start_n = kids(d)[0]
        else:
            raise Reject(n, FOR_BAD)
        t = ctype_of(d)
        if not t.is_int():
            raise Reject(n, FOR_BAD)
        rid = d["id"]
        start = self.const_int(start_n)
        cc = self.counter_cond(cond, rid, t)
        step = self.loop_counter_step(inc, rid)
        var_bound = None
        var_start = None
        if start is None and step == 1:
            # `for (uint8_t i = first; ...)` with first an unsigned parameter or local no wider than
            # the counter, not assigned in the body (SCurve::fill_empty_segments)
            var_start = self.variable_value(start_n, t, body)
            if var_start is not None:
                start = 0
        if cc is None and start is not None and start >= 0 and step == 1:
            var_bound = self.variable_bound(cond, rid, t, body)
        elif var_start is not None and cc is not None:
            var_bound = V(str(cc[1] + (1 if cc[0] == "<=" else 0)), ATOM) if cc[0] in ("<", "<=") else None
            cc = None
        if start is None or (cc is None and var_bound is None) or step is None or rid in self.assigned(body):
            raise Reject(n, FOR_BAD)
        trips = self.trip_count(start, cc[0], cc[1], step) if cc is not None else 0
        if trips is None:
            raise Reject(n, FOR_BAD)
        lo, hi = (-(1 << (t.bits - 1)), (1 << (t.bits - 1)) - 1) if t.signed else (0, (1 << t.bits) - 1)
        if cc is not None and not lo <= start + trips * step <= hi:
            raise Reject(n, FOR_BAD + " (the counter's last step leaves its type)")
        name = self.ident(d["name"], d)
        self.vars[rid] = (name, t)
        used = rid in referenced_decls(body)
        saved = self.copy_da()
        self.loops.append("for")
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        nat_to = "Nat.to%s" % t.lean
        if var_bound is not None:
            # `for (T i = C0; i < n; i++)` with n not assigned in the body: n is read once, as the
            # C++ reads the same value on every test; the counter's type holds every value below n
            head = "for %s in [%s:%s] do" % ("%s'" % name if used else "_", var_start.text if var_start is not None else start, var_bound.text)
            pre_body = ["let %s : %s := %s %s'" % (name, t.lean, nat_to, name)] if used else []
        elif not used:
            head = "for _ in [0:%d] do" % trips
            pre_body = []
        elif step == 1 and start >= 0:
            head = "for %s' in [%d:%d] do" % (name, start, start + trips)
            pre_body = ["let %s : %s := %s %s'" % (name, t.lean, nat_to, name)]
        else:
            head = "for %s' in [0:%d] do" % (name, trips)
            k = "%s %s'" % (nat_to, name)
            off = "(%s : %s) * %s" % (abs(step), t.lean, "(%s)" % k) if abs(step) != 1 else k
            sign = "+" if step > 0 else "-"
            pre_body = ["let %s : %s := %s %s %s" % (name, t.lean, lit(str(start), t).text, sign, off)]
        lines = [head] + ["  " + l for l in pre_body + (body_lines or ["pure ()"])]
        return lines, False

    def variable_bound(self, cond, rid, t, body):
        """For `i < n` where n is a parameter or local of an unsigned type no wider than the counter's
        type (so the counter never wraps before reaching it), not assigned in the body, or a data
        member of this object read in a const member function (`i < num_segs`, SCurve::valid): n as
        a Nat (V). For `i <= n` with n of the counter's own unsigned type: n + 1, which assumes n is
        below the type's maximum (for n = max the C++ loop does not terminate)."""
        c = strip_parens(cond)
        if c.get("kind") != "BinaryOperator" or c.get("opcode") not in ("<", "<="):
            return None
        lhs, rhs = [strip_parens(x) for x in kids(c)]
        while lhs.get("kind") == "ImplicitCastExpr" and lhs.get("castKind") in ("IntegralCast", "LValueToRValue"):
            lhs = strip_parens(kids(lhs)[0])
        if lhs.get("kind") != "DeclRefExpr" or lhs["referencedDecl"]["id"] != rid:
            return None
        v = self.variable_value(kids(c)[1], t, body)
        if v is None:
            return None
        if c["opcode"] == "<=":
            return V("%s + 1" % v.text, ADD)
        return v

    def variable_value(self, e, t, body):
        """The value of e as a Nat, if e is a parameter or local of an unsigned type no wider than t
        (and narrower if t is signed) that the loop body does not assign, or such a data member of
        this object in a const member function; else None."""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("IntegralCast", "LValueToRValue"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") == "DeclRefExpr":
            bid = e["referencedDecl"]["id"]
            if bid not in self.vars or bid in self.assigned(body):
                return None
            bt = self.vars[bid][1]
            if not bt.is_int() or bt.signed or bt.bits > t.bits or (t.signed and bt.bits == t.bits):
                return None
            self.read.add(bid)
            return V("%s.toNat" % self.vars[bid][0], ATOM)
        if e.get("kind") == "MemberExpr" and strip_object(kids(e)[0]).get("kind") == "CXXThisExpr" and self.ctx is not None \
                and (self.fn or {}).get("type", {}).get("qualType", "").endswith(" const"):
            f = self.ctx.rec.field_by_id(e.get("referencedMemberDecl"))
            if f is None or f.category != "state" or not f.t.is_int() or f.t.signed or f.t.bits > t.bits or (t.signed and f.t.bits == t.bits):
                return None
            return V("%s.toNat" % self.read_path(Path(("s",), "s", [("f", f.lean)], f.t), e).at(ATOM), ATOM)
        return None

    def counted_loop(self, n, kind, stmts, i):
        """`while (i op C) { ...; step }` or `do { ...; step } while (i op C)` with i declared
        earlier in the block with a constant initializer and stepped only by the body's last
        statement: the body runs a constant number of times; translated as a `for` over that
        count, the body keeping the counter up to date as the C++ does."""
        bad = WHILE_BAD if kind == "while" else DO_BAD
        if n.get("hasVar"):
            raise Reject(n, bad)
        if kind == "while":
            cond, body = kids(n)
        else:
            body, cond = kids(n)
        c = strip_parens(cond)
        if c.get("kind") != "BinaryOperator":
            raise Reject(n, bad)
        lhs = strip_parens(kids(c)[0])
        if lhs.get("kind") == "ImplicitCastExpr":
            lhs = strip_parens(kids(lhs)[0])
        if lhs.get("kind") != "DeclRefExpr":
            raise Reject(n, bad)
        rid = lhs["referencedDecl"]["id"]
        pos = next((j for j in range(i) if stmts[j].get("kind") == "DeclStmt" and
                    any(d.get("id") == rid for d in kids(stmts[j]))), None)
        if pos is None:
            raise Reject(n, bad)
        d = next(d for d in kids(stmts[pos]) if d.get("id") == rid)
        if not kids(d) or any(rid in self.assigned(stmts[j]) for j in range(pos + 1, i)):
            raise Reject(n, bad)
        v0 = self.const_int(kids(d)[0])
        if v0 is None:
            raise Reject(n, bad)
        t = ctype_of(d)
        cc = self.counter_cond(cond, rid, t)
        bstmts = kids(body) if body.get("kind") == "CompoundStmt" else [body]
        if cc is None or not bstmts:
            raise Reject(n, bad)
        step = self.loop_counter_step(bstmts[-1], rid)
        if step is None or rid in self.assigned({"kind": "CompoundStmt", "inner": bstmts[:-1]}):
            raise Reject(n, bad)
        if kind == "while":
            trips = self.trip_count(v0, cc[0], cc[1], step)
        else:
            rest = self.trip_count(v0 + step, cc[0], cc[1], step)
            trips = None if rest is None else 1 + rest
        if trips is None:
            raise Reject(n, bad)
        saved = self.copy_da()
        self.loops.append(kind)
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        return ["for _ in [0:%d] do" % trips] + ["  " + l for l in body_lines]

    def falls_off_only_by_exit(self, ss):
        """For a case whose statements were split at `if (c) { ...; break; }` (block, case_exit):
        does every path that does not take such an exit end in return/break/continue?"""
        for i, s in enumerate(ss):
            if self.case_exit(s):
                return self.falls_off_only_by_exit(ss[i + 1:])
        return bool(ss) and self.ends_in_jump(ss[-1])

    def ends_in_jump(self, s):
        k = s.get("kind")
        if k in ("ReturnStmt", "BreakStmt", "ContinueStmt"):
            return True
        if k == "CompoundStmt":
            return bool(kids(s)) and self.falls_off_only_by_exit(kids(s))
        if k == "IfStmt" and s.get("hasElse"):
            return self.ends_in_jump(kids(s)[1]) and self.ends_in_jump(kids(s)[2])
        return False

    @staticmethod
    def case_exit(s):
        """`if (c) { ...; break; }` without else, the break leaving the enclosing switch case."""
        if s.get("kind") != "IfStmt" or s.get("hasElse") or s.get("hasInit") or s.get("hasVar"):
            return False
        then = kids(s)[1]
        if then.get("kind") == "BreakStmt":
            return True
        return then.get("kind") == "CompoundStmt" and bool(kids(then)) and kids(then)[-1].get("kind") == "BreakStmt" and \
            not any(m.get("kind") == "BreakStmt" for c in kids(then)[:-1] for m in walk(c))

    def loop_only_decl(self, s, rest):
        """`T i;` (no initializer) whose every use in the rest of the block is inside a `for` loop
        that assigns it in its init statement: the declaration is not emitted, each loop binds it."""
        if s.get("kind") != "DeclStmt" or len(kids(s)) != 1:
            return False
        d = kids(s)[0]
        if d.get("kind") != "VarDecl" or kids(d) or not ctype_of(d).is_int():
            return False
        rid = d["id"]
        inside = set()
        for m in walk({"inner": rest}):
            if m.get("kind") == "ForStmt":
                init = kids(m)[0] if kids(m) else {}
                if init.get("kind") == "BinaryOperator" and init.get("opcode") == "=" and \
                        strip_parens(kids(init)[0]).get("kind") == "DeclRefExpr" and strip_parens(kids(init)[0])["referencedDecl"]["id"] == rid:
                    inside |= {id(x) for x in walk(m)}
        refs = [m for m in walk({"inner": rest}) if m.get("kind") == "DeclRefExpr" and m["referencedDecl"]["id"] == rid]
        if not refs or any(id(m) not in inside for m in refs):
            return False
        self.loop_only.add(rid)
        return True

    def block(self, stmts):
        """Translate a statement list; returns (lines, diverges). Statements after a return,
        break or continue are unreachable and are not emitted. Counted while and do loops are
        recognized here, since they need the declaration of their counter."""
        out = []
        for i, s in enumerate(stmts):
            if self.loop_only_decl(s, stmts[i + 1:]):
                continue
            if self.loops and self.loops[-1] == "switch" and self.case_exit(s):
                # `if (c) { ...; break; }` in a `switch` case: the rest of the case is the else branch;
                # the then branch leaves the switch as a final `break` does
                then = kids(s)[1]
                body = kids(then)[:-1] if then.get("kind") == "CompoundStmt" else []
                rest = {"kind": "CompoundStmt", "inner": stmts[i + 1:]}
                lines, div = self.if_stmt({"kind": "IfStmt", "inner": [kids(s)[0], {"kind": "CompoundStmt", "inner": body}, rest],
                                           "hasElse": True, "range": s.get("range"), "loc": s.get("loc")})
                self.case_exited = True
                return out + lines, div
            if s.get("kind") == "WhileStmt":
                out += self.counted_loop(s, "while", stmts, i)
                continue
            if s.get("kind") == "WhileStmt":
                out += self.counted_loop(s, "while", stmts, i)
                continue
            if s.get("kind") == "DoStmt":
                out += self.counted_loop(s, "do", stmts, i)
                continue
            lines, div = self.stmt(s)
            out += lines
            if div:
                return out, True
        return out, False

    # -- functions --------------------------------------------------------------------------

    def setup_params(self, params, body, exclude=()):
        """Declare the parameters; returns [(decl, lean name, CType, ref)], lean name None for a
        boundary-typed parameter or one in exclude (not passed in Lean)."""
        self.mutable = self.assigned(body) if body is not None else set()
        ps = []
        for p in params:
            av = array_view_type(p) if ARRAY_PARAMS[0] else None
            if av is not None:
                # `const T *p` read only as p[i]: the array the caller passes (README.md, "ArduPilot")
                if "name" not in p:
                    raise Reject(p, "unnamed parameter")
                for m in walk(body or {}):
                    if m.get("kind") == "DeclRefExpr" and m["referencedDecl"]["id"] == p["id"]:
                        pass
                pn = self.ident(p["name"], p)
                self.vars[p["id"]] = (pn, av)
                self.declared.append((p["id"], pn))
                self.array_views.add(p["id"])
                ps.append((p, pn, av, None))
                continue
            npt = self.nullable_out_type(p, body)
            if npt is not None:
                # `T *roll` used only as `roll != nullptr` and `*roll = e` (Matrix3::to_euler,
                # matrix3.cpp:49-60): a flag `roll'given` and the value written, returned as for `T &`
                if "name" not in p:
                    raise Reject(p, "unnamed parameter")
                pn = self.ident(p["name"], p)
                self.vars[p["id"]] = (pn, npt)
                self.nullable[p["id"]] = pn + "'given"
                self.declared.append((p["id"], pn))
                ps.append((p, pn, npt, "ptr"))
                self.outs.append((p["id"], pn, npt))
                self.mutable.add(p["id"])
                continue
            pt, ref = decl_type(p)
            if p["id"] in exclude:
                ps.append((p, None, pt, ref))
                continue
            if pt.kind == "array":
                raise Reject(p, "array parameter (decays to a pointer)")
            if pt.kind == "boundary":
                if ref is None:
                    raise Reject(p, "boundary object passed by value")
                ps.append((p, None, pt, ref))
                continue
            if pt.kind == "param":
                # passed by value: the parameter's value (e.g. AP_Math's is_positive<AP_Float>)
                sc = PARAM_CLASSES.get(pt.name) or PARAM_CLASSES.get(pt.name.split("::")[-1])
                pt = parse_type_str(sc, sc, p)
                self.param_vars.add(p["id"])
            if "name" not in p:
                raise Reject(p, "unnamed parameter")
            pn = self.ident(p["name"], p)
            same = [q for q in params if q.get("name") == p["name"]]
            if len(same) > 1:
                # the parameters of an expanded pack (`sq(first, parameters...)`) share one name
                pn = "%s'%d" % (pn, same.index(p) + 1)
            self.vars[p["id"]] = (pn, pt)
            self.declared.append((p["id"], pn))
            ps.append((p, pn, pt, ref))
            if ref == "mut":
                self.outs.append((p["id"], pn, pt))
                self.mutable.add(p["id"])
        return ps

    def finish(self, lines, comps):
        """Replace the return markers by the returned tuple: comps are the component texts that
        precede the value (p, s, out-parameters)."""
        out = []
        for l in lines:
            m = re.search(r"@@RET(\d+)@@", l)
            if m:
                v = self.rets[int(m.group(1))]
                items = comps + ([v] if v is not None else [])
                text = items[0] if len(items) == 1 else "(%s)" % ", ".join(items)
                l = l[:m.start()] + text + l[m.end():]
            if "\n" in l:              # an entry of several lines (Body.write_path): each at the first's indentation
                ind = l[:len(l) - len(l.lstrip())]
                parts = l.split("\n")
                out += [parts[0]] + [ind + x for x in parts[1:]]
                continue
            out.append(l)
        return out

    def unused(self):
        return [nm for rid, nm in self.declared if rid not in self.read and rid not in [o[0] for o in self.outs]]


def default_text(u, p, home, deps):
    """Lean text of the default argument of parameter p, if it is a constant expression (the
    constants it uses are added to deps)."""
    if not (p.get("init") and kids(p)):
        return None
    try:
        cb = Body(u, None, None, home=home)
        pre, v = cb.expr(kids(p)[0])
    except Reject:
        return None
    if pre:
        return None
    deps |= cb.deps
    return v.text


class FreeResult:
    """A translated free function or static method."""

    def __init__(self):
        self.lean = None
        self.cparams = []
        self.outs = []
        self.ret = None
        self.lines = []
        self.unused = []
        self.binders = ""
        self.ret_lean = ""
        self.key = None
        self.deps = set()
        self.decl = None
        self.defn = None


def translate_free(u, d, home, lean_name, defn=None):
    """A free function or a static method: its parameters, its result, its body."""
    defn = defn or d
    b = Body(u, defn, None, home=home)
    r = FreeResult()
    r.lean = lean_name
    params = [p for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
    body = next((c for c in kids(defn) if c.get("kind") == "CompoundStmt"), None)
    ret = fn_return_type(d)
    if ret.kind in ("array", "boundary", "param"):
        raise Reject(d, "function returning `%s`" % ret.cname)
    b.void = ret.kind == "void"
    ps = b.setup_params(params, body)
    if any(pn is None for _, pn, _, _ in ps):
        raise Reject(d, "boundary object as a parameter of a free function")
    lines = []
    for p, pn, pt, ref in ps:
        if p["id"] in b.mutable:
            lines.append("let mut %s := %s" % (pn, pn))
    body_lines, div = b.block(kids(body))
    if not div:
        if ret.kind != "void":
            raise Reject(d, "control may reach the end of non-void function `%s`" % d["name"])
        body_lines.append(b.ret_line(None))
    comps = [pn for _, pn, _ in b.outs]
    if not comps and ret.kind == "void":
        raise Reject(d, "function `%s` returning void without reference parameters (no observable result)" % d["name"])
    r.lines = b.finish(lines + body_lines, comps)
    r.cparams, r.outs, r.ret = ps, list(b.outs), ret
    r.unused = b.unused()
    decl_params = [p for p in kids(d) if p.get("kind") == "ParmVarDecl"]
    groups = []
    for i, (p, pn, pt, ref) in enumerate(ps):
        dp = decl_params[i] if i < len(decl_params) else p
        dflt = default_text(u, dp, home, b.deps) or default_text(u, p, home, b.deps)
        if ref == "ptr":
            groups.append(([pn + "'given"], BOOL, None))     # a nullable out-pointer's flag
            groups.append(([pn], pt, None))
            continue
        if dflt is None and groups and groups[-1][1] == pt and groups[-1][2] is None and groups[-1][0][-1][-6:] != "'given":
            groups[-1][0].append(pn)
        else:
            groups.append(([pn], pt, dflt))
    r.binders = "".join(" (%s : %s%s)" % (" ".join(g), t.lean, "" if df is None else " := " + df) for g, t, df in groups)
    rtys = [pt.lean_atom for _, _, pt in b.outs]
    if ret.kind != "void":
        rtys.append(ret.lean_atom if rtys else ret.lean)
    r.ret_lean = " × ".join(rtys)
    u.uses_libm |= b.uses_libm
    r.deps = b.deps
    r.decl, r.defn = d, defn
    return r


# ---------------------------------------------------------------------------------------------
# Records, enums and class contexts.

class FieldInfo:
    def __init__(self, decl, owner, t, category):
        self.decl, self.owner, self.t, self.category = decl, owner, t, category
        self.name = decl["name"]
        self.lean = lean_field(decl["name"], decl)
        self.id = decl["id"]
        self.default = None     # V
        self.deps = set()
        self.storage = None     # an enum parameter (AP_Enum<E>): the integer type it is stored in


class EnumInfo:
    def __init__(self, node, cxx, lean, parent):
        self.node, self.cxx, self.lean, self.parent = node, cxx, lean, parent
        self.values = []        # (name, value)
        self.ctor_names = {}
        self.used_ofInt = False
        v = -1
        for c in kids(node):
            if c.get("kind") != "EnumConstantDecl":
                continue
            init = [x for x in kids(c) if x.get("kind") not in ("FullComment", "ParagraphComment", "TextComment")]
            if init:
                ce = next((x for x in walk(init[0]) if x.get("kind") == "ConstantExpr" and "value" in x), None)
                if ce is None:
                    raise Reject(c, "enumerator without a constant value")
                v = int(ce["value"])
            else:
                v += 1
            self.values.append((c["name"], v))
            self.ctor_names[c["name"]] = lean_field(c["name"], c)
        if not self.values:
            raise Reject(node, "enum without enumerators")
        if len({x for _, x in self.values}) != len(self.values):
            raise Reject(node, "enum with two enumerators of the same value")
        ft = node.get("fixedUnderlyingType")
        if ft:
            self.under = parse_type_str(ft["qualType"], ft.get("desugaredQualType", ft["qualType"]), node)
        else:
            self.under = CType("int", 32, any(x < 0 for _, x in self.values))

    def name_of_value(self, v):
        for nm, x in self.values:
            if x == v:
                return nm
        return None


class RecordInfo:
    def __init__(self, node, cxx, lean, parent):
        self.node, self.cxx, self.lean, self.parent = node, cxx, lean, parent
        self.id = node["id"]
        self.name = node.get("name")
        self.bases = []
        self.fields = []
        self.methods = []       # in-class declarations of methods, constructors, destructors
        self.statics = []       # static data members (VarDecl)
        self.kind = "plain"
        self.abstract = False
        self.lib = False
        self.var_info = None    # the AP_Param table (--ap-param)
        self.failed = False     # a member was rejected: the class is not translated further
        self.dropped = []       # data members left out of the model (--drop)

    @property
    def lean_type(self):
        return self.lean if self.kind == "plain" else self.lean + ".State"

    def chain(self):
        out = [self]
        while out[-1].bases:
            out.append(out[-1].bases[0])
        return out

    def all_fields(self):
        out = []
        for r in reversed(self.chain()):
            out += r.fields
        return out

    def field_by_id(self, fid):
        for f in self.all_fields():
            if f.id == fid:
                return f
        return None

    def has_params(self):
        for f in self.all_fields():
            if f.category == "param":
                return True
            if f.category == "state" and f.t.kind == "record" and f.t.info.kind == "class" and f.t.info.has_params():
                return True
        return False

    def find_ctor(self, ctor_type):
        want = ctor_type.replace(" noexcept", "").strip()
        for m in self.methods:
            if m.get("kind") == "CXXConstructorDecl" and m["type"]["qualType"].replace(" noexcept", "").strip() == want:
                return m
        return None


def ctype_kind_record_ref(d):
    """Does member function d return a non-const reference to a class object?"""
    q = d.get("type", {}).get("qualType", "")
    ret = q.split("(")[0].strip()
    name = ret[:-1].strip() if ret.endswith("&") else ""
    if name in PARAM_CLASSES or name.split("::")[-1] in PARAM_CLASSES:
        return False                # a parameter: its value is read (Body.member_call), it is not an object
    return ret.endswith("&") and not ret.startswith("const ") and not re.match(r"^(float|double|bool|u?int\d+_t|int|unsigned|AP_\w+) ?&$", ret)


def zero_default_ctor(u, t):
    """Does default construction of an object of type t give the zero value (the field default of an
    element of a zero-filled array)? True for a struct without a default constructor, and for a
    class whose default constructor has an empty body and initializes members with zeros only
    (`Vector3() : x(0), y(0), z(0) {}`)."""
    if t.kind != "record":
        return t.is_scalar()
    ctor = t.info.find_ctor("void ()")
    if ctor is None:
        return True
    body = u.body_of(ctor) or ctor
    for c in kids(body):
        if c.get("kind") == "CompoundStmt" and kids(c):
            return False
        if c.get("kind") == "CXXCtorInitializer":
            e = kids(c)[0] if kids(c) else None
            while e is not None and e.get("kind") in ("ImplicitCastExpr", "ConstantExpr", "ParenExpr"):
                e = kids(e)[0]
            if e is None or e.get("kind") not in ("IntegerLiteral", "FloatingLiteral") or float(e.get("value", "1")) != 0:
                return False
    return True


def method_sigkey(m):
    """(name, parameter types, const): the key under which a member function overrides or hides
    one of a base class (parameter types desugared, without `enum`/`struct` tags)."""
    q = m["type"]["qualType"]
    ps = []
    for p in kids(m):
        if p.get("kind") == "ParmVarDecl":
            t = p["type"].get("desugaredQualType", p["type"]["qualType"])
            ps.append(re.sub(r"\b(enum|struct|class) ", "", t))
    return (m.get("name"), ", ".join(ps), q.rstrip().endswith("const"))


class MethodResult:
    def __init__(self):
        self.lean = None
        self.reads, self.writes = set(), set()
        self.uses_inp = False
        self.outs = []
        self.ret = None
        self.cparams = []
        self.lines = []
        self.header = ""
        self.doc = ""
        self.unused = []
        self.has_params = False
        self.decl = None
        self.order = 0
        self.top = False
        self.noeffect = False
        self.uses_own = False
        self.ref_bind = {}      # constructor parameter index -> reference member it binds
        self.alias = None       # Context.method: the reference parameters bound to members of the object


class Context:
    """The translation of the member functions of one concrete class R, the most-derived class:
    inherited member functions are translated again against R's state, so a virtual call through
    `this` resolves to R's final overrider."""

    def __init__(self, unit, rec):
        self.u, self.rec = unit, rec
        self.results = {}       # key -> MethodResult
        self.in_progress = set()
        self.inputs = []        # (key, lean field, CType, cxx text, node)
        self.sub_inputs = {}    # member field -> sub Context
        self.outputs = []       # (key, lean field, CType, cxx text, node): values written to the boundary
        self.sub_outputs = {}
        self.counter = 0
        self.ctor_base = "init"
        self.owner_reads = []   # (key, Owner field, CType, node): values read through the back-reference
        self.owner_helpers = {} # member field -> (sub Context, helper name): `owner_<member> p s`
        self.helper_blocks = [] # emitted helpers: (member field, lines, deps)
        self.names = self.assign_names()

    def assign_names(self):
        """Lean names, in R's namespace, of the member function definitions of the chain: the
        C++ name (suffixed by the parameter types when it is overloaded in the chain) for the
        version that R's member lookup finds, `Base.name` for a base's version that a more-derived
        class overrides or hides. Constructors are `init` (`construct` if the chain has a member
        function named init), `Base.init` for a base class's constructor."""
        chain = self.rec.chain()
        by_name = {}
        self.aliases = {}       # non-const accessor returning a reference -> its const twin
        for r in chain:
            for m in r.methods:
                if m.get("kind") in ("CXXDestructorDecl", "CXXConstructorDecl") or m.get("explicitlyDeleted"):
                    continue
                key = method_sigkey(m)
                twin = next((x for x in r.methods if x is not m and method_sigkey(x) == (key[0], key[1], True)), None) \
                    if not key[2] else None
                if twin is not None and returns_reference(m) and returns_reference(twin):
                    self.aliases[m["id"]] = twin   # `AP_Float &kP()` and `const AP_Float &kP() const`: one value function
                    continue
                by_name.setdefault(m["name"], set()).add(key[1:])
        self.ctor_base = "construct" if "init" in by_name else "init"
        names = {}
        for depth, r in enumerate(chain):
            ctors = [x for x in r.methods if x.get("kind") == "CXXConstructorDecl" and not x.get("explicitlyDeleted")
                     and not x.get("explicitlyDefaulted")]
            for m in r.methods:
                k = m.get("kind")
                if k == "CXXDestructorDecl":
                    continue
                if k == "CXXConstructorDecl":
                    base = self.ctor_base + ("_" + self.sig_suffix(m) if len(ctors) > 1 else "")
                    names[m["id"]] = base if r is self.rec else "%s.%s" % (r.name, base)
                    continue
                if m["name"].startswith("operator") and operator_word(m["name"]) is None:
                    names[m["id"]] = None
                    continue
                if m["id"] in self.aliases:
                    continue
                base = operator_word(m["name"]) or m["name"]
                if len(by_name.get(m["name"], ())) > 1:
                    base = base + "_" + self.sig_suffix(m)
                base = lean_field(base, m)
                key = method_sigkey(m)
                hidden = any(method_sigkey(x) == key for rr in chain[:depth] for x in rr.methods)
                names[m["id"]] = base if not hidden else "%s.%s" % (r.name, base)
        return names

    @staticmethod
    def sig_suffix(m):
        """The parameter types (or, for a template specialization, the template arguments) as part
        of a Lean name; a run of k equal types is written once with k appended (`float11`)."""
        targs = []
        for c in kids(m):
            if c.get("kind") == "TemplateArgument":
                if not c.get("type") and kids(c) and all(x.get("kind") == "TemplateArgument" for x in kids(c)):
                    targs += kids(c)          # a pack: its elements
                elif c.get("type") or kids(c) or "value" in c:
                    targs.append(c)
        out = []
        if targs:
            for a in targs:
                t = a.get("type", {})
                q = t.get("qualType", str(a.get("value", "x")))
                try:
                    out.append(re.sub(r"\W+", "_", parse_type_str(q, t.get("desugaredQualType", q), a).cname).strip("_"))
                except Reject:
                    out.append(name_part(q))
        else:
            ps = [p for p in kids(m) if p.get("kind") == "ParmVarDecl"]
            if not ps:
                return "void"
            for p in ps:
                try:
                    t, ref = decl_type(p)
                    cn = t.info.lean.split(".")[-1] if t.kind in ("record", "enum") else t.cname
                    out.append(re.sub(r"\W+", "_", cn).strip("_"))
                except Reject:
                    out.append(name_part(p["type"].get("desugaredQualType", p["type"]["qualType"])))
        runs = []
        for x in out:
            if runs and runs[-1][0] == x:
                runs[-1][1] += 1
            else:
                runs.append([x, 1])
        return "_".join(x if k == 1 else "%s%d" % (x, k) for x, k in runs)

    def layout_prefix(self, t, n):
        """For a view `*(S *)this` of this class's object as a value of S: [(field of S, field of
        this class)], where the data members of S are the first data members of this class, with the
        same names and types, in the same order (S is a layout prefix); else rejected."""
        if t.kind != "record":
            raise Reject(n, "pointer cast of `this` to `%s`" % t.cname)
        mine = [f for f in self.rec.all_fields()]
        theirs = [f for f in t.info.all_fields()]
        if not theirs or any(f.category != "state" for f in mine[:len(theirs)] + theirs) or len(theirs) > len(mine) or \
                any((a.name, a.t) != (b.name, b.t) for a, b in zip(mine, theirs)):
            raise Reject(n, "pointer cast of `this` to `%s`, whose data members are not the first data members of `%s` (same names and types)" % (t.cname, self.rec.cxx))
        return [(b.lean, a.lean) for a, b in zip(mine, theirs)]

    def resolve(self, mdecl, virtual_dispatch):
        """The member function a call of mdecl through `this` runs in context R: the final
        overrider in R for a virtual function (unless the call is qualified), else mdecl."""
        if mdecl["id"] in self.aliases:
            mdecl = self.aliases[mdecl["id"]]   # the merged const/non-const accessor (still dispatched below)
        if virtual_dispatch and (mdecl.get("virtual") or self.u.is_override(mdecl)):
            key = method_sigkey(mdecl)
            for r in self.rec.chain():
                for m in r.methods:
                    if m.get("kind") == "CXXMethodDecl" and method_sigkey(m) == key and not m.get("pure"):
                        return m
        return mdecl

    def input_field(self, obj, member, is_call, cargs, t, cxx, node):
        key = (obj, member, is_call, tuple(cargs))
        for k, name, _, _, _ in self.inputs:
            if k == key:
                return name
        if cargs == ("live",):
            # a live read (--boundary-live): named after the member, after the accessor it is reached
            # through if any (`_pos_control.NE_get_pos_p().kP()` is `NE_get_pos_p_kP`)
            base = member.replace(".", "_")
            if obj.endswith("()"):
                base = obj.split(".")[-1][:-2] + "_" + base
        elif isinstance(cargs, tuple) and cargs[:1] == ("site",):
            # one input per call site (non-constant arguments): the member's name, then with the line
            base = member.replace(".", "_")
            if any(nm == lean_field(base, node) for _, nm, _, _, _ in self.inputs):
                base += "_%s" % cargs[1].split(":")[-2]
        else:
            base = member.replace(".", "_") + "".join("_" + re.sub(r"\W+", "_", str(c)).strip("_") for c in cargs)
            if not is_call and "." in obj:
                # a data member of a member of the boundary object (`_motors.limit.roll`): named with
                # the member it belongs to (`limit_roll`)
                base = re.sub(r"\W+", "_", obj.split(".")[-1]).strip("_") + "_" + base
        name = lean_field(base, node)
        if any(nm == name for _, nm, _, _, _ in self.inputs) or name in self.sub_inputs:
            name = lean_field(re.sub(r"\W+", "_", obj).strip("_") + "_" + base, node)
        self.inputs.append((key, name, t, cxx, node))
        return name

    def sub_refs(self, field_lean, info, node):
        """The values a member object's reference members are bound to: [(field of its Refs,
        expression of this class)], from the member's initializer (default member initializer or
        constructor initializer)."""
        f = next(x for x in self.rec.all_fields() if x.lean == field_lean)
        inits = []
        if f.decl.get("hasInClassInitializer"):
            inits.append(kids(f.decl)[-1])
        for r in self.rec.chain():
            for m in r.methods:
                if m.get("kind") == "CXXConstructorDecl":
                    for ini in kids(self.u.body_of(m) or m):
                        if ini.get("kind") == "CXXCtorInitializer" and ini.get("anyInit", {}).get("id") == f.id and kids(ini) \
                                and kids(ini)[0].get("kind") != "CXXDefaultInitExpr":
                            inits.append(kids(ini)[0])
        found = None
        for e in inits:
            e = strip_parens(e)
            while e.get("kind") in ("ExprWithCleanups", "MaterializeTemporaryExpr", "CXXBindTemporaryExpr"):
                e = kids(e)[0]
            if e.get("kind") != "CXXConstructExpr":
                raise Reject(node, "member `%s` with reference members, initialized by something other than a constructor" % f.name)
            ctor = info.find_ctor(e.get("ctorType", {}).get("qualType", ""))
            if ctor is None:
                raise Reject(node, "member `%s` with reference members and no matching constructor" % f.name)
            res = self.u.context(info, node).ctor(ctor, top=True, node=node)
            binds = [(rf, kids(e)[i]) for i, rf in sorted(res.ref_bind.items())]
            key = [(rf, self.u.text_of(a)) for rf, a in binds]
            if found is not None and found[0] != key:
                raise Reject(node, "member `%s` whose reference members are bound differently by different constructors" % f.name)
            found = (key, binds)
        if found is None:
            raise Reject(node, "member `%s` with reference members that no initializer binds" % f.name)
        return found[1]

    def output_field(self, obj, member, pname, t, cxx, node):
        key = (obj, member, pname)
        for k, name, _, _, _ in self.outputs:
            if k == key:
                return name
        base = member if pname is None else "%s_%s" % (member, pname)
        name = lean_field(base, node)
        if any(nm == name for _, nm, _, _, _ in self.outputs) or name in self.sub_outputs:
            name = lean_field(re.sub(r"\W+", "_", obj).strip("_") + "_" + base, node)
        self.outputs.append((key, name, t, cxx, node))
        return name

    def owner_helper(self, field, sub, node):
        """The name of the function of this class that computes the `Owner` record of member
        `field` (translated after everything else, when every read through the back-reference is
        known: finish_owner_helpers)."""
        if field not in self.owner_helpers:
            f = next(x for x in self.rec.all_fields() if x.lean == field)
            if not owner_binds(self.u, next(r for r in self.rec.chain() if f in r.fields), f):
                raise Reject(node, "member `%s` with a back-reference, not initialized with `*this`" % f.name)
            self.owner_helpers[field] = (sub, "owner_%s" % field)
        return self.owner_helpers[field][1]

    def finish_owner_helpers(self):
        """Translate, for each member with a back-reference to this object, the function that
        reads what the member reads through it: each read `motors.f(c)` becomes the call `f(c)`
        on this object, which must not write anything nor read the member itself."""
        for field, (sub, name) in self.owner_helpers.items():
            f = next(x for x in self.rec.all_fields() if x.lean == field)
            b = Body(self.u, None, self, home=self.rec.lean)
            b.mutable = set()
            lines, vals = [], []
            for key, fname, t, node in sub.owner_reads:
                syn = this_copy(node)
                check_no_member_read(self.u, self, syn, f, set(), node)
                pre, v = b.expr(syn)
                if b.writes - {"o"} or "o" in b.writes or "inp" in b.reads or "own" in b.reads:
                    raise Reject(node, "read through the back-reference that writes or reads the boundary (`%s`)" % fname)
                lines += pre
                vals.append("%s := %s" % (fname, v.text))
            body = ["let _ := (p, s)"] if False else []
            text = ["set_option linter.unusedVariables false in",
                    "/-- What member `%s` (C++ `%s`) reads through its reference to this object, computed when this object calls it (README.md, \"ArduPilot\"). -/" % (field, comment_safe(cpp_var_decl(f.decl))),
                    "def %s (p : Params) (s : State) : %s.Owner := Id.run do" % (name, sub.rec.lean)]
            text += ["  " + l for l in lines + ["return { %s }" % ", ".join(vals)]]
            self.helper_blocks.append((field, text, set(b.deps) | {("T", sub.rec.id), ("T", self.rec.id)}))

    def sub_output(self, field, sub):
        self.sub_outputs.setdefault(field, sub)
        return field

    def sub_input(self, field, sub):
        self.sub_inputs.setdefault(field, sub)
        return field

    def fields_reached(self, mdecl, seen=None):
        """The ids of the data members of this object that member function mdecl reads or writes
        through `this`, also in the member functions of this object it calls."""
        key = mdecl["id"]
        cache = self.__dict__.setdefault("_reached", {})
        if key in cache:
            return cache[key]
        seen = set() if seen is None else seen
        if key in seen:
            return set()
        seen.add(key)
        out = set()
        for m in walk(self.u.body_of(mdecl) or {}):
            k = m.get("kind")
            if k == "MemberExpr" and kids(m) and strip_object(kids(m)[0]).get("kind") == "CXXThisExpr":
                d = self.u.decl(m.get("referencedMemberDecl"))
                if d is not None and d.get("kind") in ("CXXMethodDecl",):
                    try:
                        out |= self.fields_reached(self.resolve(d, virtual_dispatch=True), seen)
                    except Reject:
                        pass
                else:
                    out.add(m.get("referencedMemberDecl"))
        cache[key] = out
        return out

    def method(self, mdecl, node, alias=None):
        """The MethodResult of a member function in this context (translated on first use). alias:
        ((parameter index, path steps), ...) for a call whose reference arguments are members of
        this object that the callee also reaches through `this` (Body.alias_args): a translation of
        the member function for that call, in which each such parameter is the member itself."""
        body = self.u.body_of(mdecl)
        if body is None:
            raise Reject(node, "call of `%s`, which has no definition in the translated files" % mdecl.get("name"))
        key = mdecl["id"] if not alias else (mdecl["id"], alias)
        if key in self.results:
            return self.results[key]
        if key in self.in_progress:
            raise Reject(node, "recursive call (member function `%s` is on a call cycle)" % mdecl.get("name"))
        self.in_progress.add(key)
        try:
            res = self.translate(mdecl, body, ctor=False, top=False, alias=alias)
        finally:
            self.in_progress.discard(key)
        res.bid = ("m", self.rec.id, key)
        self.results[key] = res
        return res

    def ctor(self, cdecl, top, node):
        key = ("top" if top else "on", cdecl["id"])
        if key in self.results:
            return self.results[key]
        if key in self.in_progress:
            raise Reject(node, "recursive constructor call")
        self.in_progress.add(key)
        try:
            res = self.translate(cdecl, self.u.body_of(cdecl) or cdecl, ctor=True, top=top)
        finally:
            self.in_progress.discard(key)
        res.bid = ("m", self.rec.id, key)
        self.results[key] = res
        return res

    def translate(self, mdecl, defn, ctor, top, alias=None):
        u = self.u
        body = next((c for c in kids(defn) if c.get("kind") == "CompoundStmt"), None)
        if body is None and not ctor:
            raise Reject(mdecl, "member function without a body")
        owner = u.parent_record(mdecl)
        if ctor and top and owner is not self.rec:
            raise Reject(mdecl, "constructor of a base class used for a complete object")
        b = Body(u, defn, self, home=self.rec.lean)
        params = [p for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
        for i, steps in (alias or ()):
            # this parameter is the member `steps` of this object at the call being translated
            pt0, _ = decl_type(params[i])
            b.aliases[params[i]["id"]] = Path(("s",), "s", list(steps), pt0)
        decl_params = [p for p in kids(mdecl) if p.get("kind") == "ParmVarDecl"]
        res = MethodResult()
        res.decl, res.top = mdecl, ctor and top
        ret = VOID if ctor else fn_return_type(mdecl)
        if ret.kind in ("array", "boundary", "param"):
            raise Reject(mdecl, "member function returning `%s`" % ret.cname)
        b.void = ret.kind == "void"
        ref_params = {}
        if ctor:
            for ini in kids(defn):
                if ini.get("kind") == "CXXCtorInitializer" and "anyInit" in ini:
                    f = self.rec.field_by_id(ini["anyInit"]["id"])
                    if f is not None and f.category in ("ref", "owner"):
                        e = strip_object(kids(ini)[0]) if kids(ini) else {}
                        if e.get("kind") != "DeclRefExpr" or e["referencedDecl"].get("kind") != "ParmVarDecl":
                            raise Reject(defn, "reference member `%s` bound to something other than a constructor parameter" % f.name)
                        ref_params[e["referencedDecl"]["id"]] = f.lean
        ps = b.setup_params(params, body, exclude=set(ref_params) | set(b.aliases))
        res.ref_bind = {i: ref_params[p_["id"]] for i, (p_, pn, pt, ref) in enumerate(ps) if p_["id"] in ref_params}
        res.cparams, res.outs, res.ret = ps, list(b.outs), ret
        lines = []
        if ctor:
            b.writes.add("s")
            b.reads.add("s")
            if self.rec.has_params():
                b.writes.add("p")
                b.reads.add("p")
        for p_, pn, pt, ref in ps:
            if pn is not None and p_["id"] in b.mutable:
                lines.append("let mut %s := %s" % (pn, pn))
        if ctor:
            lines += self.ctor_inits(b, defn, owner, top)
        if body is not None:
            body_lines, div = b.block(kids(body))
            if not div:
                if ret.kind != "void":
                    raise Reject(mdecl, "control may reach the end of non-void member function `%s`" % mdecl.get("name"))
                body_lines.append(b.ret_line(None))
            lines += body_lines
        else:
            lines.append(b.ret_line(None))
        res.reads, res.writes = set(b.reads) - {"inp", "own"}, set(b.writes)
        res.uses_inp = "inp" in b.reads
        res.uses_own = "own" in b.reads
        if ctor and top:
            res.reads -= {"s", "p"}
        if ctor and "olive" in res.reads:
            raise Reject(mdecl, "constructor that reads a live boundary object (--boundary-live)")
        if ctor and "o" in res.writes:
            raise Reject(mdecl, "constructor that writes outputs to the boundary")
        comps = (["p"] if "p" in res.writes else []) + (["s"] if "s" in res.writes else []) + \
            (["o"] if "o" in res.writes else []) + [pn for _, pn, _ in b.outs]
        if not comps and ret.kind == "void":
            # no effect in the model (e.g. it only saves parameters or logs): not emitted, and a
            # call of it is no statement
            res.noeffect = True
        lines = b.finish(lines, comps)
        if ctor and top:
            pre = (["let mut p : Params := {}"] if "p" in res.writes else []) + ["let mut s : State := {}"]
        else:
            pre = (["let mut p := p"] if "p" in res.writes else []) + (["let mut s := s"] if "s" in res.writes else []) + \
                (["let mut o := o"] if "o" in res.writes else [])
        res.lines = pre + lines
        res.has_params = ctor and "p" in res.writes
        binders = []
        if not (ctor and top):
            if "p" in res.reads | res.writes:
                binders.append("(p : Params)")
            if "s" in res.reads | res.writes:
                binders.append("(s : State)")
            if "o" in res.writes or "olive" in res.reads:
                binders.append("(o : Outputs)")
        if "r" in res.reads:
            binders.append("(r' : Refs)")
        if res.uses_inp:
            binders.append("(inp : Inputs)")
        if res.uses_own:
            binders.append("(own : Owner)")
        for i, (p_, pn, pt, ref) in enumerate(ps):
            if pn is None:
                continue
            dp = decl_params[i] if i < len(decl_params) else p_
            dflt = default_text(u, dp, self.rec.lean, b.deps) or default_text(u, p_, self.rec.lean, b.deps)
            if ref == "ptr":
                binders.append("(%s'given : Bool)" % pn)
            binders.append("(%s : %s%s)" % (pn, pt.lean, "" if dflt is None else " := " + dflt))
        rtys = (["Params"] if "p" in res.writes else []) + (["State"] if "s" in res.writes else []) + \
            (["Outputs"] if "o" in res.writes else [])
        rtys += [pt.lean_atom for _, _, pt in b.outs]
        if ret.kind != "void":
            rtys.append(ret.lean_atom if rtys else ret.lean)
        if ctor and top:
            ctors = [x for x in owner.methods if x.get("kind") == "CXXConstructorDecl" and not x.get("explicitlyDeleted")
                     and not x.get("explicitlyDefaulted")]
            res.lean = self.ctor_base + ("_" + self.sig_suffix(mdecl) if len(ctors) > 1 else "")
        else:
            res.lean = self.names.get(mdecl["id"])
        if res.lean is None:
            raise Reject(mdecl, "overloaded operator `%s`" % mdecl.get("name"))
        if alias:
            res.lean += "'" + "'".join("_".join(str(x) for _, x in steps) for _, steps in alias)
            res.alias = alias
        res.header = "def %s%s : %s := Id.run do" % (res.lean, "".join(" " + x for x in binders), " × ".join(rtys))
        res.deps = set(b.deps) | {("T", self.rec.id)}
        for _, pn, pt, _ in ps:
            if pn is not None:          # not a boundary object or the owner, which are not passed
                res.deps |= type_deps(pt)
        res.deps |= type_deps(ret)
        res.unused = b.unused()
        rng = defn["range"]
        l0, l1 = expansion(rng["begin"])["line"], expansion(rng["end"])["line"]
        where = line_range(u.shown_path(expansion(rng["begin"]).get("file")), l0, l1)
        note = "" if owner is self.rec else " (a member of `%s`, translated for `%s`)" % (owner.cxx, self.rec.cxx)
        if alias:
            note += "; for a call that binds %s, which the function also reaches through `this`, so each such parameter is that member here" % \
                ", ".join("`%s` to member `%s`" % (params[i].get("name"), ".".join(str(x) for _, x in steps)) for i, steps in alias)
        res.doc = "/-- C++ `%s`, `%s`%s. -/" % (comment_safe(cpp_signature_method(owner, mdecl)), comment_safe(where), note)
        u.uses_libm |= b.uses_libm
        self.counter += 1
        res.order = self.counter        # after its callees, which finish first
        return res

    def ctor_inits(self, b, defn, owner, top):
        """Lines for a constructor's base and member initializers, in declaration order, or for
        the target of a delegating constructor."""
        lines = []
        for ini in kids(defn):
            if ini.get("kind") != "CXXCtorInitializer":
                continue
            e = kids(ini)[0] if kids(ini) else None
            if e is not None and e.get("kind") == "ExprWithCleanups":
                e = kids(e)[0]      # `_p_angle_roll(4.5f)` into `AC_P(const float &)`: the temporary's cleanup
            if "delegatingInit" in ini:
                target = owner.find_ctor(e.get("ctorType", {}).get("qualType", "")) if e and e.get("kind") == "CXXConstructExpr" else None
                if target is None:
                    raise Reject(defn, "delegating constructor without a matching target constructor")
                res = self.ctor(target, top=top, node=ini)
                b.deps.add(res.bid)
                if res.uses_inp:
                    raise Reject(ini, "delegating constructor whose target reads boundary inputs")
                pre, vals, outs = b.call_args(res.cparams, kids(e), ini)
                if top:
                    call = app(res.lean, *vals) if vals else V(res.lean, ATOM)
                    if res.has_params:
                        t1, t2 = b.temp(), b.temp()
                        lines += pre + ["let (%s, %s) := %s" % (t1, t2, call.text), "p := %s" % t1, "s := %s" % t2]
                    else:
                        lines += pre + ["s := %s" % call.text]
                else:
                    objargs = b.this_call_args(res)
                    p2, _ = b.apply_call(res.lean, res.writes, objargs, vals, outs, VOID, ini, b.object_setters())
                    lines += pre + p2
                continue
            if "baseInit" in ini:
                base = owner.bases[0] if owner.bases else None
                if base is None or e is None or e.get("kind") != "CXXConstructExpr":
                    raise Reject(ini, "base initializer")
                ctor = base.find_ctor(e.get("ctorType", {}).get("qualType", ""))
                if ctor is None:
                    if kids(e):
                        raise Reject(ini, "base initializer without a matching constructor")
                    continue
                res = self.ctor(ctor, top=False, node=ini)
                b.deps.add(res.bid)
                if res.uses_inp:
                    raise Reject(ini, "base constructor that reads boundary inputs")
                objargs = b.this_call_args(res)
                pre, vals, outs = b.call_args(res.cparams, kids(e), ini)
                p2, _ = b.apply_call(res.lean, res.writes, objargs, vals, outs, VOID, ini, b.object_setters())
                lines += pre + p2
                continue
            if "anyInit" not in ini:
                raise Reject(defn, "delegating constructor")
            f = self.rec.field_by_id(ini["anyInit"]["id"])
            if f is None and ini["anyInit"]["id"] in self.u.dropped and (e is None or not Body.has_effects(e)):
                continue        # a member left out of the model (--drop), initialized without effects
            if f is None:
                raise Reject(defn, "initializer of member `%s`, which is not translated" % ini["anyInit"].get("name"))
            if e is not None and e.get("kind") == "CXXDefaultInitExpr" and f.category == "state" and deferred_init(f) is not None:
                e = deferred_init(f)    # the default member initializer, run by this constructor
            elif e is None or e.get("kind") == "CXXDefaultInitExpr" or f.category in ("boundary", "ref", "owner"):
                continue        # the field's default is its member initializer; references are not state
            if f.category == "param":
                if e.get("kind") == "CXXConstructExpr" and not kids(e):
                    continue
                raise Reject(ini, "initializer of parameter member `%s`" % f.name)
            spath = Path(("s",), "s", [("f", f.lean)], f.t)
            if e.get("kind") == "CXXConstructExpr" and f.t.kind == "record" and not (len(kids(e)) == 1 and ctype_of(kids(e)[0]) == f.t):
                ctor = f.t.info.find_ctor(e.get("ctorType", {}).get("qualType", ""))
                if ctor is None:
                    if kids(e):
                        raise Reject(ini, "member initializer without a matching constructor")
                    continue    # implicit default construction: the field's default
                sub = self.u.context(f.t.info, ini)
                b.deps.add(("T", f.t.info.id))
                res = sub.ctor(ctor, top=True, node=ini)
                b.deps.add(res.bid)
                if res.uses_inp:
                    raise Reject(ini, "member constructor that reads boundary inputs")
                pre, vals, outs = b.call_args(res.cparams, kids(e), ini)
                call = app("%s.%s" % (f.t.info.lean, res.lean), *vals) if vals else V("%s.%s" % (f.t.info.lean, res.lean), ATOM)
                if res.has_params:
                    t1, t2 = b.temp(), b.temp()
                    lines += pre + ["let (%s, %s) := %s" % (t1, t2, call.text),
                                    b.write_path(Path(("p",), "p", [("f", f.lean)], None), V(t1, ATOM), ini),
                                    b.write_path(spath, V(t2, ATOM), ini)]
                else:
                    lines += pre + [b.write_path(spath, call, ini)]
                continue
            if e.get("kind") == "CXXConstructExpr" and f.t.kind == "array" and not kids(e) and zero_default_ctor(self.u, f.t.elem):
                continue        # default construction of an array member whose elements construct to zero: the field's default
            if f.t.kind == "array" and e.get("kind") == "InitListExpr":
                pre, v = b.array_init(e, f.t)
            elif e.get("kind") == "InitListExpr" and not kids(e):
                pre, v = [], zero_of(f.t, ini)
            else:
                pre, v = b.expr(e)
            lines += pre + [b.write_path(spath, v, ini)]
        return lines

    def translate_all(self, reject):
        """Translate every member function and constructor of R and its bases; a rejection is
        reported per member function."""
        for r in reversed(self.rec.chain()):
            for m in r.methods:
                try:
                    self.translate_member(r, m)
                except Reject as e:
                    reject(e)

    def translate_member(self, r, m):
        k = m.get("kind")
        if k == "CXXDestructorDecl":
            body = self.u.body_of(m)
            cs = [c for c in kids(body) if c.get("kind") == "CompoundStmt"] if body else []
            if any(kids(c) for c in cs):
                raise Reject(m, "destructor with a body")
            return
        if m.get("storageClass") == "static":
            return
        if m.get("explicitlyDefaulted") or m.get("explicitlyDeleted") or m["id"] in self.aliases:
            return
        if m["id"] in self.u.dropped or self.u.dropped_def(m):
            return              # --drop: not translated, its calls are left out
        if self.u.is_boundary_call(m):
            return              # --boundary-call: not translated, its calls are boundary calls
        if m.get("name") == "operator[]" and Body(self.u, None, self, home=self.rec.lean).field_index_view(m) is not None:
            return              # a view of the data members: its calls with constant indices are member accesses
        if self.u.body_of(m) is None:
            return
        if k == "CXXConstructorDecl":
            if r is self.rec:
                self.ctor(m, top=True, node=m)
            return
        if m["name"].startswith("operator") and operator_word(m["name"]) is None:
            raise Reject(m, "overloaded operator `%s`" % m["name"])
        self.method(m, m)


def this_copy(node):
    """A copy of the call or member read `r.f(...)` / `r.x` through a back-reference r, with the
    object replaced by `this` (the owner): the same read, made by the owner."""
    import copy
    n = copy.deepcopy(node)
    target = n
    if n.get("kind") in ("CXXMemberCallExpr",):
        target = strip_parens(kids(n)[0])
    me = target
    if me.get("kind") != "MemberExpr":
        raise Reject(node, "read through a back-reference")
    me["inner"] = [{"kind": "CXXThisExpr", "type": {"qualType": "this"}, "range": me.get("range")}]
    return n


def check_no_member_read(u, ctx, n, f, seen, node):
    """Reject if evaluating n in ctx may read member f (the object holding the back-reference,
    which changes during the member's call), looking through calls of member functions of this."""
    for m in walk(n):
        if m.get("kind") == "MemberExpr" and m.get("referencedMemberDecl") == f.id:
            raise Reject(node, "read through the back-reference that reads `%s` itself" % f.name)
        if m.get("kind") in ("CXXMemberCallExpr",):
            c = strip_parens(kids(m)[0])
            if c.get("kind") == "MemberExpr" and strip_object(kids(c)[0]).get("kind") == "CXXThisExpr":
                d = u.canonical(u.decl(c.get("referencedMemberDecl")))
                if d is not None and d["id"] not in seen:
                    seen.add(d["id"])
                    t = ctx.resolve(d, virtual_dispatch=True)
                    b = u.body_of(t)
                    if b is not None:
                        check_no_member_read(u, ctx, b, f, seen, node)


def cpp_signature_method(owner, m):
    q = m["type"]["qualType"]
    params = ", ".join("%s %s" % (p["type"]["qualType"], p.get("name", "")) for p in kids(m) if p.get("kind") == "ParmVarDecl")
    if m.get("kind") == "CXXConstructorDecl":
        return "%s::%s(%s)" % (owner.cxx, m.get("name"), params)
    const = " const" if q.rstrip().endswith("const") else ""
    return "%s %s::%s(%s)%s" % (q.split("(")[0].strip(), owner.cxx, m["name"], params, const)


# ---------------------------------------------------------------------------------------------
# Translation unit.

class Unit:
    def __init__(self, path, tree, ns, headers, externs, lib_dirs=()):
        self.path = path
        self.tree = tree
        self.ns = ns
        self.ids = {}
        self.ast_order = {}     # decl id -> position in a pre-order walk of the AST
        self.parent = {}
        self.sources = {}
        self.consts = {}        # decl id -> {"lean", "ns", "t", "decl"}
        self.fn_names = {}      # FunctionDecl id (definition) -> Lean name
        self.defs_by_mangled = {}
        self.literals = []      # every floating literal emitted, with the bits clang gives it
        self.lit_seen = set()
        self.index(tree, None)
        self.main_file = find_main_file(tree, path)
        self.files = {self.main_file}
        for h in headers:
            hf = find_file(tree, h)
            if hf:
                self.files.add(hf)
        self.externs = externs
        self.lib_dirs = [os.path.realpath(x) + os.sep for x in lib_dirs]
        self.lib_cache = {}
        self.lib_rejects = {}   # record id -> Reject of a library record (reported if it is used)
        self.const_items = {}   # decl id -> emitted constant (library constants on first use)
        self.records = []
        self.records_by_id = {}
        self.enums = []
        self.contexts = {}      # record id -> Context
        self.free_results = {}
        self.static_results = {}
        self.uses_libm = False
        self.ctx_deps = {}
        self.method_bodies = {}  # mangled name -> out-of-line definition
        self.dropped = {}       # decl id -> qualified name: data members and member functions left out (--drop)
        self.boundary_globals = {}  # `extern` references to boundary objects (`hal`): decl id -> name
        self.out_ctors = {}     # --output-log: Lean constructor name -> ([(param name, CType)], C++ text, node)
        self.out_keys = {}      # (object, member) -> constructor name

    def index(self, n, parent):
        if isinstance(n, dict) and "id" in n and n["id"] not in self.ast_order:
            self.ast_order[n["id"]] = len(self.ast_order)     # pre-order position: a tie-break independent of the ids' values
        if isinstance(n, dict) and "id" in n:
            old = self.ids.get(n["id"])
            # a declaration may be listed twice (a template's specializations): keep the full node
            if old is None or "inner" in n or "inner" not in old:
                self.ids[n["id"]] = n
                self.parent[n["id"]] = parent
        for c in kids(n):
            if isinstance(c, dict):
                self.index(c, n)

    def decl(self, i):
        return self.ids.get(i) if i is not None else None

    def decl_file(self, d):
        loc = expansion(d.get("loc"))
        return loc.get("file") if loc else None

    def in_set(self, d):
        return d is not None and (self.decl_file(d) in self.files or self.is_lib(d))

    def is_lib_file(self, f):
        if f is None:
            return False
        if f not in self.lib_cache:
            rf = os.path.realpath(f)
            self.lib_cache[f] = f not in self.files and any(rf.startswith(x) for x in self.lib_dirs)
        return self.lib_cache[f]

    def is_lib(self, d):
        """Is d in a --lib-dir file (translated only when the translated files use it)?"""
        return d is not None and self.is_lib_file(self.decl_file(d))

    def source_of(self, f):
        if f not in self.sources:
            try:
                with open(f, "rb") as fh:
                    self.sources[f] = fh.read()
            except OSError:
                self.sources[f] = b""
        return self.sources[f]

    def text_of(self, n):
        rng = n.get("range", {})
        b, e = rng.get("begin", {}), rng.get("end", {})
        if "spellingLoc" in b or "offset" not in b or "offset" not in e or b.get("file") != e.get("file"):
            return None
        return self.source_of(b["file"])[b["offset"]:e["offset"] + e.get("tokLen", 0)].decode(errors="replace")

    def shown_path(self, f):
        if f is None:
            f = self.path
        rf = os.path.realpath(f)
        for root in SRC_ROOTS:
            if rf.startswith(root):
                return rf[len(root):]
        return portable_path(f)

    def literal(self, n, lean, bits, cpp):
        if lean in self.lit_seen:
            return
        self.lit_seen.add(lean)
        loc = node_loc(n) or {}
        self.literals.append({"lean": lean, "bits": bits, "cpp": cpp,
                              "at": "%d:%d" % (loc.get("line", 0), loc.get("col", 0))})

    def function_for(self, decl):
        """The translated definition a called FunctionDecl refers to (a prototype resolves to its
        definition through the mangled name), or None for functions outside the files."""
        if decl is None or not self.in_set(decl) or decl.get("kind") != "FunctionDecl":
            return None
        return self.defs_by_mangled.get(decl.get("mangledName"))

    def parent_record(self, d):
        if d is None:
            return None
        p = self.decl(d.get("parentDeclContextId")) if d.get("parentDeclContextId") else self.parent.get(d["id"])
        if p is None:
            return None
        return self.records_by_id.get(p.get("id"))

    def canonical(self, m):
        """The in-class declaration of a member function, for a reference to its out-of-line
        definition (clang refers to the latest redeclaration)."""
        if m is None or m.get("kind") not in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl"):
            return m
        r = self.parent_record(m)
        if r is None:
            return m
        for x in r.methods:
            if x["id"] == m["id"] or (x.get("mangledName") and x.get("mangledName") == m.get("mangledName")):
                return x
        return m

    def is_boundary_call(self, m):
        """Is member function m (or the base declaration it overrides) a --boundary-call?"""
        return qualified_name(self, m) in BOUNDARY_CALL

    def output_ctor(self, obj, mname, targs, sig, node):
        """The constructor of `Output` for calls of mname on obj (--output-log)."""
        key = (obj, mname)
        if key in self.out_keys:
            name = self.out_keys[key]
            if [t for _, t in self.out_ctors[name][0]] != [t for _, t in targs]:
                raise Reject(node, "boundary output `%s` called with different argument types" % sig)
            return name
        if mname.startswith("="):
            base = re.sub(r"\W+", "_", "%s.%s" % (obj, mname[1:])).strip("_")
        else:
            base = mname
        name = lean_field(base, node)
        if name in self.out_ctors:
            name = lean_field(re.sub(r"\W+", "_", "%s.%s" % (obj, mname.lstrip("="))).strip("_"), node)
        self.out_ctors[name] = (targs, sig, node)
        self.out_keys[key] = name
        return name

    def dropped_def(self, m):
        """Is m (an in-class declaration) a member function named by --drop (also as `Base::f` for an override)?"""
        r = self.parent_record(m)
        return r is not None and "%s::%s" % (r.cxx, m.get("name")) in DROP

    def body_of(self, m):
        if any(c.get("kind") == "CompoundStmt" for c in kids(m)):
            return m
        return self.method_bodies.get(m.get("mangledName"))

    def is_override(self, m):
        return any(c.get("kind") == "OverrideAttr" for c in kids(m))

    def enum_of_constant(self, cid):
        for e in self.enums:
            if any(c.get("id") == cid for c in kids(e.node)):
                return e
        return None

    def enclosing_record(self, n):
        """The innermost registered record a node belongs to (for library rejections)."""
        x = n
        while x is not None:
            if x.get("id") in self.records_by_id:
                return self.records_by_id[x["id"]]
            owner = self.decl(x.get("parentDeclContextId")) if x.get("parentDeclContextId") else None
            x = owner if owner is not None else self.parent.get(x.get("id"))
        return None

    def check_lib(self, rec, node):
        """A library record is used: report what was rejected in it."""
        for r in rec.chain():
            if r.id in self.lib_rejects:
                raise self.lib_rejects[r.id]

    def ensure_fields(self, rec):
        """The field defaults of a record and its bases (a library record: when first used)."""
        if getattr(rec, "fields_ready", False):
            return
        self.check_lib(rec, rec.node)
        rec.fields_ready = True
        for r in rec.chain():
            if r is not rec:
                self.ensure_fields(r)
            for f in r.fields:
                field_default(self, r, f)
                t = f.t.elem if f.t.kind == "array" else f.t
                if t.kind == "record":
                    self.ensure_fields(t.info)

    def const_item(self, rid):
        """The emitted form of a constant (translated on first use)."""
        if rid in self.const_items:
            return self.const_items[rid]
        c = self.consts[rid]
        d = c["decl"]
        tr = Body(self, None, None, home=c["ns"])
        t, init = c["t"], kids(d)[0]
        if t.kind == "array":
            if init.get("kind") != "InitListExpr":
                raise Reject(d, "array `%s` without an initializer list" % d["name"])
            pre, v = tr.array_init(init, t)
        else:
            pre, v = tr.expr(init)
        if pre:
            raise Reject(d, "constant initializer with side effects")
        self.uses_libm |= tr.uses_libm
        item = {"key": srckey_node(self, d), "kind": "const", "id": d["id"], "payload": (d, c, v), "deps": tr.deps}
        self.const_items[rid] = item
        return item

    def context(self, rec, node):
        if rec.kind != "class":
            raise Reject(node, "member functions of plain struct `%s`" % rec.cxx)
        if rec.abstract:
            raise Reject(node, "object of abstract class `%s`" % rec.cxx)
        if rec.id not in self.contexts:
            self.ensure_fields(rec)
            self.contexts[rec.id] = Context(self, rec)
        return self.contexts[rec.id]

    def boundary_static_result(self, d, node):
        """A --boundary-static member function (`AP_AHRS::calc_trig`, AP_AHRS_Backend.cpp:93-135),
        translated as a free function named after its class (`AP_AHRS_calc_trig`): its definition
        must not use `this`."""
        d = self.canonical(d)
        if d["id"] in self.free_results and self.free_results[d["id"]] is not None:
            return self.free_results[d["id"]]
        defn = self.body_of(d)
        if defn is None:
            # the out-of-line definition of a member of a class that is not translated
            defn = next((m for m in self.ids.values() if m.get("kind") == "CXXMethodDecl" and m.get("previousDecl") == d["id"]
                         and any(c.get("kind") == "CompoundStmt" for c in kids(m))), None)
        if defn is None or not any(c.get("kind") == "CompoundStmt" for c in kids(defn)):
            raise Reject(node, "--boundary-static member function `%s` without a definition" % qualified_name(self, d))
        for m in walk(defn):
            if m.get("kind") == "CXXThisExpr":
                raise Reject(m, "--boundary-static member function `%s` that uses its object" % qualified_name(self, d))
        self.fn_names[d["id"]] = re.sub(r"\W+", "_", qualified_name(self, d))
        self.free_results[d["id"]] = None
        try:
            r = translate_free(self, d, self.ns, self.fn_names[d["id"]], defn=defn)
        except Reject:
            del self.free_results[d["id"]]
            raise
        r.key = d["id"]
        self.free_results[d["id"]] = r
        return r

    def free_result(self, d, node):
        if d["id"] in self.free_results:
            r = self.free_results[d["id"]]
            if r is None:
                raise Reject(node, "recursive call (function `%s` is on a call cycle)" % d["name"])
            return r
        self.free_results[d["id"]] = None
        try:
            r = translate_free(self, d, self.ns, self.fn_names[d["id"]])
        except Reject:
            del self.free_results[d["id"]]
            raise
        r.key = d["id"]
        self.free_results[d["id"]] = r
        return r

    def static_result(self, rec, m, node):
        body = self.body_of(m)
        if body is None:
            raise Reject(node, "static member function `%s` without a definition" % m.get("name"))
        key = ("static", m["id"])
        if key in self.static_results:
            r = self.static_results[key]
            if r is None:
                raise Reject(node, "recursive call (static member function `%s` is on a call cycle)" % m["name"])
            return r
        self.static_results[key] = None
        try:
            r = translate_free(self, m, rec.lean, lean_field(m["name"], m), defn=body)
        except Reject:
            del self.static_results[key]
            raise
        r.key = key
        self.static_results[key] = r
        return r


def run_clang(path, extra=()):
    cmd = [CLANG] + CLANG_FLAGS + list(extra) + ["-Xclang", "-ast-dump=json", "-fsyntax-only", path]
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        sys.stderr.write(p.stderr.decode())
        sys.stderr.write("cpp2lean: clang failed on %s\n" % path)
        sys.exit(1)
    return json.loads(p.stdout)


def default_namespace(path):
    stem = os.path.splitext(os.path.basename(path))[0]
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[^A-Za-z0-9]+", stem) if w)


def find_main_file(tree, path):
    real = os.path.realpath(path)
    for d in kids(tree):
        loc = expansion(d.get("loc"))
        if loc and loc.get("file") and os.path.realpath(loc["file"]) == real:
            return loc["file"]
    return path


def find_file(tree, path):
    real = os.path.realpath(path)
    for n in walk(tree):
        loc = expansion(n.get("loc")) if n.get("loc") else None
        if loc and loc.get("file") and os.path.realpath(loc["file"]) == real:
            return loc["file"]
    return None


def cpp_signature(fn, ps):
    """The C++ declaration as clang spells its types."""
    ret = fn["type"]["qualType"].split("(")[0].strip()
    return "%s %s(%s)" % (ret, fn["name"], ", ".join("%s %s" % (p["type"]["qualType"], p["name"]) for p, pn, pt, ref in ps))


def cpp_var_decl(d, name=None):
    q = d["type"]["qualType"]
    name = name or d["name"]
    m = re.match(r"^(.*?)\s*(\[\d+\])$", q)
    return "%s %s%s" % (m.group(1), name, m.group(2)) if m else "%s %s" % (q, name)


CURRENT_UNIT = [None]   # the Unit being translated (for lookups from static helpers)
SHOW_PATH = [None]   # the current unit's shown_path (set by translate; else portable_path)


def comment_safe(text):
    """Lean block comments nest, so `/-` and `-/` inside a comment are split with a space. The file
    of clang's name for an anonymous struct (`(unnamed struct at FILE:L:C)`) is shown as other paths."""
    text = UNNAMED_AT.sub(lambda m: "(unnamed %s at %s:%s:%s)" % (m.group(1), (SHOW_PATH[0] or portable_path)(m.group(2)), m.group(3), m.group(4)), text)
    return text.replace("/-", "/ -").replace("-/", "- /")


def comment_safe_pair(a, b):
    return comment_safe(a), comment_safe(b)


def line_range(path, l0, l1):
    return "%s:%d" % (path, l0) if l0 == l1 else "%s:%d-%d" % (path, l0, l1)


def spec_name(n):
    """`Name<args>` for a class template specialization, as clang spells the type."""
    if n.get("kind") != "ClassTemplateSpecializationDecl":
        return n.get("name")
    args = []
    for a in kids(n):
        if a.get("kind") == "TemplateArgument":
            args.append(a.get("type", {}).get("qualType") or str(a.get("value", "?")))
    return "%s<%s>" % (n.get("name"), ", ".join(args))


def qualified_name(u, n):
    """The C++ qualified name of a record, enum or function declaration."""
    parts = [spec_name(n)]
    p = u.parent.get(n["id"])
    while p is not None and p.get("kind") in ("CXXRecordDecl", "NamespaceDecl", "ClassTemplateSpecializationDecl",
                                              "LinkageSpecDecl", "FunctionTemplateDecl", "ClassTemplateDecl"):
        if p.get("kind") in ("CXXRecordDecl", "NamespaceDecl", "ClassTemplateSpecializationDecl"):
            parts.append(spec_name(p))
        p = u.parent.get(p["id"])
    if n.get("parentDeclContextId"):
        owner = u.decl(n["parentDeclContextId"])
        if owner is not None and owner.get("kind") in ("CXXRecordDecl", "ClassTemplateSpecializationDecl", "NamespaceDecl"):
            return qualified_name(u, owner) + "::" + parts[0]
    return "::".join(reversed(parts))


def lean_record_name(cxx):
    """The Lean name of a record: a class template specialization by its unique typedef
    (`LowPassFilter<float>` is `LowPassFilterFloat`), else with its arguments in the name."""
    if cxx in TYPE_NAMES:
        return TYPE_NAMES[cxx]
    if "<" in cxx:
        td = REV_TYPEDEFS.get(cxx)
        if td is not None:
            return td
        return re.sub(r"\W+", "_", cxx).strip("_")
    return cxx.replace("::", ".")


def collect_types(u, decls, reject):
    """Register the records and enums of the translated files (also those nested in classes)."""
    def visit(d, parent_rec):
        k = d.get("kind")
        try:
            if k == "EnumDecl":
                if not d.get("name"):
                    td = next((c for c in kids(u.parent.get(d["id"]) or {}) if c.get("kind") == "TypedefDecl" and
                               any(x.get("ownedTagDecl", {}).get("id") == d["id"] for x in kids(c))), None)
                    if td is None:
                        raise Reject(d, "anonymous enum")
                    # `typedef enum { ... } Function;` (SRV_Channel::Function): named by the typedef
                    owner = u.parent.get(d["id"])
                    cxx = (qualified_name(u, owner) + "::" if owner is not None and owner.get("kind") in ("CXXRecordDecl", "NamespaceDecl") else "") + td["name"]
                    e = EnumInfo(d, cxx, cxx.replace("::", "."), parent_rec)
                    ENUMS[cxx] = e
                    u.enums.append(e)
                    return
                cxx = qualified_name(u, d)
                e = EnumInfo(d, cxx, cxx.replace("::", "."), parent_rec)
                ENUMS[cxx] = e
                u.enums.append(e)
            elif k == "ClassTemplateDecl":
                for c in kids(d):
                    if c.get("kind") == "ClassTemplateSpecializationDecl":
                        visit(u.decl(c["id"]), parent_rec)
            elif k in ("CXXRecordDecl", "ClassTemplateSpecializationDecl") and d.get("completeDefinition") and not d.get("isImplicit"):
                if d["id"] in u.records_by_id:
                    return
                anon_field = None
                if "name" not in d:
                    anon_field = anonymous_member(u, d)
                    if anon_field is None or parent_rec is None:
                        raise Reject(d, "anonymous struct or class (other than the type of one data member of a class)")
                if d.get("tagUsed") == "union":
                    raise Reject(d, "union `%s`" % d["name"])
                if anon_field is not None:
                    # `struct { ... } member;`: the type is named after the member (`AP_Motors._motor_pwm_scaled_t`)
                    loc = expansion(d.get("loc")) or {}
                    cxx = "%s::(unnamed %s at %s:%d:%d)" % (parent_rec.cxx, d.get("tagUsed", "struct"), loc.get("file"), loc.get("line", 0), loc.get("col", 0))
                    r = RecordInfo(d, cxx, parent_rec.lean + "." + anon_field + "_t", parent_rec)
                    r.name = anon_field + "_t"
                    r.lib = u.is_lib(d)
                    RECORDS[cxx] = r
                    u.records.append(r)
                    u.records_by_id[r.id] = r
                    return
                cxx = qualified_name(u, d)
                if cxx in BOUNDARY or d["name"] in BOUNDARY or cxx in PARAM_CLASSES or d["name"] in PARAM_CLASSES:
                    return
                if AP_PARAM[0] and re.match(r"^AP_(ParamT|Enum|Enum16)<", cxx):
                    return
                lean = lean_record_name(cxx)
                r = RecordInfo(d, cxx, lean, parent_rec)
                if "<" in cxx:
                    r.name = lean.split(".")[-1]
                r.lib = u.is_lib(d)
                RECORDS[cxx] = r
                u.records.append(r)
                u.records_by_id[r.id] = r
                for c in kids(d):
                    if c.get("kind") in ("CXXRecordDecl", "EnumDecl"):
                        visit(c, r)
        except Reject as e:
            reject(e)

    for d in decls:
        visit(d, None)


def member_initializers(u, o, g):
    """The initializer expressions of data member g of record o: its default member initializer
    and the constructor initializers that name it."""
    out = []
    if g.decl.get("hasInClassInitializer") and kids(g.decl):
        out.append(kids(g.decl)[-1])
    for m in o.methods:
        if m.get("kind") == "CXXConstructorDecl":
            for ini in kids(u.body_of(m) or m):
                if ini.get("kind") == "CXXCtorInitializer" and ini.get("anyInit", {}).get("id") == g.id and kids(ini) \
                        and kids(ini)[0].get("kind") != "CXXDefaultInitExpr":
                    out.append(kids(ini)[0])
    return out


def is_star_this(e):
    e = strip_object(e)
    return e.get("kind") == "UnaryOperator" and e.get("opcode") == "*" and strip_object(kids(e)[0]).get("kind") == "CXXThisExpr"


def owner_binds(u, o, g):
    """Does record o initialize its member g with a constructor call that passes `*this`?"""
    for e in member_initializers(u, o, g):
        e = strip_parens(e)
        while e.get("kind") in ("ExprWithCleanups", "MaterializeTemporaryExpr", "CXXBindTemporaryExpr", "InitListExpr") and kids(e):
            e = kids(e)[0]
        if e.get("kind") == "CXXConstructExpr" and any(is_star_this(a) for a in kids(e)):
            return True
    return False


def anonymous_member(u, d):
    """The name of the data member whose type is the anonymous struct d (`struct { ... } m;`), or None."""
    parent = u.parent.get(d["id"])
    loc = expansion(d.get("loc")) or {}
    key = "unnamed %s at %s:%d:%d)" % (d.get("tagUsed", "struct"), loc.get("file"), loc.get("line", 0), loc.get("col", 0))
    fields = [c for c in kids(parent or {}) if c.get("kind") == "FieldDecl" and re.sub(r"\[\d+\]$", "", c["type"]["qualType"]).endswith(key)]
    return fields[0]["name"] if len(fields) == 1 else None


def fill_records(u, reject):
    """Bases, fields, member functions and kinds of the registered records."""
    for r in u.records:
        d = r.node
        try:
            for b in d.get("bases", []):
                if b.get("isVirtual"):
                    raise Reject(d, "virtual base class")
                bt = b["type"]
                name, _ = strip_tag(bt.get("desugaredQualType", bt["qualType"]))
                name = norm_template_args(name)
                if name not in RECORDS:
                    raise Reject(d, "base class `%s` that is not translated" % name)
                r.bases.append(RECORDS[name])
            if len(r.bases) > 1:
                raise Reject(d, "multiple inheritance")
        except Reject as e:
            reject(e)
        for c in kids(d):
            k = c.get("kind")
            if k in ("FieldDecl", "VarDecl") and "name" in c and "%s::%s" % (r.cxx, c["name"]) in DROP:
                u.dropped[c["id"]] = "%s::%s" % (r.cxx, c["name"])      # not part of the model (--drop)
                r.dropped.append(c)
                continue
            if k in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl") and "name" in c and "%s::%s" % (r.cxx, c["name"]) in DROP:
                u.dropped[c["id"]] = "%s::%s" % (r.cxx, c["name"])
            if k == "FriendDecl" and c.get("type"):
                continue                # `friend class X;`: access control only, no effect on the model
            try:
                if k == "FieldDecl":
                    if c.get("mutable"):
                        raise Reject(c, "mutable member `%s`" % c.get("name", ""))
                    if "name" not in c:
                        raise Reject(c, "unnamed member")
                    t, ref = decl_type(c)
                    if c.get("isBitfield") and t.kind != "bool":
                        width = next((int(x["value"]) for x in kids(c) if x.get("kind") == "ConstantExpr" and "value" in x), None)
                        if not (t.kind == "int" and not t.signed and width == 1):
                            raise Reject(c, "bit-field `%s` of type `%s` (only bool bit-fields are translated)" % (c["name"], t.cname))
                        BIT1_FIELDS.add(c["id"])     # `uint8_t f : 1` (AC_WPNav::wpnav_flags): its declared type, writes masked
                    if t.kind == "boundary":
                        cat = "boundary"
                    elif t.kind == "param":
                        pt = PARAM_CLASSES.get(t.name) or PARAM_CLASSES.get(t.name.split("::")[-1])
                        storage = PARAM_STORAGE.get(t.name) or PARAM_STORAGE.get(t.name.split("::")[-1])
                        t, cat = parse_type_str(pt, pt, c), "param"
                    elif ref == "const" and t.is_scalar():
                        cat = "ref"     # bound by the constructor to a value of the owner: a field of Refs
                    elif ref is not None and t.kind == "record":
                        cat = "owner"   # checked below: the back-reference of a member object to its owner
                    elif ref is not None:
                        raise Reject(c, "reference member `%s` to a class that is not a --boundary class (a back-reference to the owner, e.g. `AP_Motors &`, would need the owner's state; only `const` references to numbers are translated, as `Refs`)" % c["name"]
                                     if t.kind == "record" else "non-const reference member `%s` (only `const` references to numbers are translated, as `Refs`)" % c["name"])
                    else:
                        cat = "state"
                    r.fields.append(FieldInfo(c, r, t, cat))
                    if cat == "param":
                        r.fields[-1].storage = storage if t.kind == "enum" else None
                elif k in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl", "CXXConversionDecl"):
                    if c.get("isImplicit"):
                        continue
                    if k == "CXXConversionDecl":
                        raise Reject(c, "conversion operator")
                    r.methods.append(c)
                elif k == "VarDecl":
                    q = c["type"]["qualType"]
                    if AP_PARAM[0] and "GroupInfo" in q:
                        continue        # the AP_Param table: read by setup_object_defaults
                    if not (q.startswith("const ") or c.get("constexpr")) or not kids(c):
                        raise Reject(c, "static data member `%s` that is mutable or has no constant initializer" % c["name"])
                    r.statics.append(c)
                elif k in ("FunctionTemplateDecl", "ClassTemplateDecl"):
                    raise Reject(c, "member template `%s`" % c.get("name", ""))
                elif k == "FriendDecl":
                    raise Reject(c, "friend declaration")
            except Reject as e:
                reject(e)
                if k == "FieldDecl":
                    r.failed = True
        for f in r.fields:
            for b in r.chain()[1:]:
                if any(g.name == f.name for g in b.fields):
                    reject(Reject(f.decl, "member `%s` hides a member of base class `%s`" % (f.name, b.cxx)))
        if r.methods or r.bases:
            r.kind = "class"
    for r in u.records:
        if any(b.kind == "class" for b in r.chain()):
            r.kind = "class"
    for r in u.records:
        # a reference member to a class is the owner's back-reference (`AP_Motors &motors` of
        # Thrust_Linearization) only if a class holds an object of r as a member and passes `*this`
        # to its constructor (`Thrust_Linearization thr_lin {*this}`); otherwise it is rejected
        for f in [f for f in r.fields if f.category == "owner"]:
            if not any(owner_binds(u, o, g) for o in u.records for g in o.fields if g.t.kind == "record" and g.t.info is r):
                reject(Reject(f.decl, "reference member `%s` to a class that is not a --boundary class (a back-reference to the owner, e.g. `AP_Motors &`, would need the owner's state; only `const` references to numbers are translated, as `Refs`)" % f.name))
                r.fields.remove(f)
                r.failed = True
    for r in u.records:
        chain = r.chain()
        r.abstract = False
        for depth, rr in enumerate(chain):
            for pm in rr.methods:
                if pm.get("pure"):
                    key = method_sigkey(pm)
                    if not any(method_sigkey(x) == key and not x.get("pure") for c in chain[:depth] for x in c.methods):
                        r.abstract = True


def portable_path(p):
    """A path as the output shows it: relative to the cpp2lean directory if it lies there (also through
    the symlinks it holds, such as ardupilot/src), else unchanged; so the output does not depend on
    where the tree sits."""
    a = os.path.abspath(p)
    if a.startswith(PKG_ROOT + os.sep):
        return os.path.relpath(a, PKG_ROOT)
    r = os.path.realpath(p)
    rr = os.path.realpath(PKG_ROOT)
    if r.startswith(rr + os.sep):
        return os.path.relpath(r, rr)
    return p


def portable_arg(arg):
    """A command-line argument with the paths in it made portable (`-Ipath`, `@file`, a bare path)."""
    for pre in ("-I", "@"):
        if arg.startswith(pre) and len(arg) > len(pre) and os.path.exists(arg[len(pre):]):
            return pre + portable_path(arg[len(pre):])
    return portable_path(arg) if os.path.exists(arg) else arg


UNNAMED_AT = re.compile(r"\(unnamed (struct|union|class|enum) at ([^():`]+):(\d+):(\d+)\)")


def srckey_node(u, d):
    """The emission order of a declaration: the main file first, then by the file as shown (relative to
    --src-root or to the cpp2lean directory, so the order does not depend on where the tree sits), line,
    column."""
    loc = node_loc(d) or {}
    f = loc.get("file")
    return (0 if f == u.main_file else 1, u.shown_path(f) if f else "", loc.get("line", 0), loc.get("col", 0))


def translate(path, ns, headers=(), externs=None, clang_extra=(), options="", lib_dirs=()):
    ROOT_NS[0] = ns
    tree = run_clang(path, clang_extra)
    fill_locations(tree)
    collect_typedefs(tree)
    u = Unit(path, tree, ns, headers, externs or {}, lib_dirs)
    rejects = []
    shown = portable_path(path)
    SHOW_PATH[0] = u.shown_path
    CURRENT_UNIT[0] = u
    deferring = [True]      # while collecting: rejections in library files wait until the item is used

    def report(r):
        loc = node_loc(r.node) or {}
        f = loc.get("file")
        key = (0 if f in (None, u.main_file) else 1, u.shown_path(f) if f else shown, loc.get("line", 0), loc.get("col", 0), r.construct)
        if key not in rejects:
            rejects.append(key)

    def reject(r):
        if deferring[0] and u.is_lib_file((node_loc(r.node) or {}).get("file")):
            rec = u.enclosing_record(r.node)
            if rec is not None:
                u.lib_rejects.setdefault(rec.id, r)
            return
        report(r)

    top = [d for d in kids(tree) if u.in_set(d)]
    collect_types(u, top, reject)
    fill_records(u, reject)
    for r in u.records:
        if r.lean == ns:
            reject(Reject(r.node, "class `%s` has the name of the file's namespace (pass another --namespace)" % r.cxx))
    for d in top:
        if d.get("kind") in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl") and \
                any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            u.method_bodies[d.get("mangledName")] = d

    # free functions (and specializations of function templates), constants, names
    defs, consts, names = [], [], {}

    def add_function(d):
        if not any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            return
        if d.get("variadic"):
            raise Reject(d, "variadic function")
        if d["name"] == "main":
            raise Reject(d, "function `main`")
        if d.get("mangledName") in u.defs_by_mangled:
            return
        names.setdefault(d["name"], []).append(d)
        u.defs_by_mangled[d.get("mangledName")] = d
        if not u.is_lib(d):
            defs.append(d)

    for d in top:
        k = d.get("kind")
        lib = u.is_lib(d)
        try:
            if k == "FunctionDecl":
                add_function(d)
            elif k == "FunctionTemplateDecl" and (lib or instantiated(d)):
                for c in kids(d):
                    if c.get("kind") == "FunctionDecl" and c.get("mangledName"):
                        add_function(u.decl(c["id"]))
            elif k == "VarDecl" and d.get("storageClass") == "extern" and not kids(d) and not lib:
                t, ref = decl_type(d)
                if t.kind != "boundary":
                    raise Reject(d, "`extern` variable `%s` of a type that is not a --boundary class" % d["name"])
                u.boundary_globals[d["id"]] = d["name"]     # `extern const AP_HAL::HAL& hal;`
            elif k == "VarDecl":
                if AP_PARAM[0] and "GroupInfo" in d["type"]["qualType"]:
                    owner = u.decl(d.get("parentDeclContextId"))
                    rec = u.records_by_id.get(owner["id"]) if owner else None
                    if rec is not None and kids(d):
                        rec.var_info = d        # the AP_Param table, read by setup_object_defaults
                    continue
                if d.get("parentDeclContextId"):
                    continue                    # the out-of-line definition of a static member
                q = d["type"]["qualType"]
                if not (q.startswith("const ") or d.get("constexpr")) or not kids(d):
                    if lib:
                        continue
                    raise Reject(d, "global variable `%s` (mutable or non-constant globals are outside the subset)" % d["name"])
                try:
                    u.consts[d["id"]] = {"lean": lean_ident(d["name"], d), "ns": ns, "t": ctype_of(d), "decl": d}
                except Reject:
                    if not lib:
                        raise
                    continue
                if not lib:
                    consts.append(d)
            elif k in ("ClassTemplateDecl", "FunctionTemplateDecl") and not lib and not instantiated(d):
                raise Reject(d, "template `%s` that is not instantiated" % d.get("name", ""))
            elif k in ("TypedefDecl", "TypeAliasDecl", "UsingDirectiveDecl", "UsingDecl", "EmptyDecl", "StaticAssertDecl",
                       "CXXRecordDecl", "EnumDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl",
                       "ClassTemplateDecl", "ClassTemplateSpecializationDecl", "ClassTemplatePartialSpecializationDecl"):
                continue
            elif lib:
                continue                        # anything else in a library file is used or not
            elif k == "NamespaceDecl":
                # a namespace of declarations only (e.g. ArduPilot's `namespace AP { AP_AHRS &ahrs(); }`)
                # declares the boundary; definitions inside a namespace are not translated
                for c in kids(d):
                    if any(x.get("kind") == "CompoundStmt" for x in kids(c)) and qualified_name(u, c) in DROP:
                        continue                # e.g. `AP::motors()`, the singleton accessor (--drop)
                    for x in walk(c):
                        if any(y.get("kind") == "CompoundStmt" for y in kids(x)) or x.get("kind") in ("VarDecl", "CXXRecordDecl", "EnumDecl"):
                            raise Reject(x, "definition inside namespace `%s` (file-scope definitions only)" % d.get("name", ""))
            elif k == "LinkageSpecDecl":
                raise Reject(d, "`extern \"C\"` block")
            else:
                raise Reject(d, "declaration `%s`" % k)
        except Reject as r:
            reject(r)
    u.fn_by_name = names
    for nm, ds in names.items():
        taken = set()
        for d in ds:
            name = lean_ident(nm, d) + ("_" + Context.sig_suffix(d) if len(ds) > 1 else "")
            while name in taken:
                name += "_"
            taken.add(name)
            u.fn_names[d["id"]] = name
    for r in u.records:
        for c in r.statics:
            try:
                u.consts[c["id"]] = {"lean": lean_field(c["name"], c), "ns": r.lean, "t": ctype_of(c), "decl": c}
            except Reject as e:
                reject(e)
    deferring[0] = False
    for r in u.records:
        if not r.lib:
            try:
                u.ensure_fields(r)
            except Reject as e:
                reject(e)

    for d in consts + [c for r in u.records if not r.lib for c in r.statics]:
        if d["id"] in u.consts:
            try:
                u.const_item(d["id"])
            except Reject as r:
                reject(r)
    for d in defs:
        try:
            u.free_result(d, d)
        except Reject as r:
            reject(r)
    for r in u.records:
        if r.lib:
            continue
        for m in r.methods:
            if m.get("storageClass") == "static" and u.body_of(m) is not None and m["id"] not in u.dropped:
                try:
                    u.static_result(r, m, m)
                except Reject as e:
                    reject(e)
    for r in u.records:
        if r.lib:
            continue
        if r.kind == "class" and not r.abstract and (KEEP_GOING[0] or not any(x.failed for x in r.chain())):
            try:
                u.context(r, r.node).translate_all(reject)
            except Reject as e:
                reject(e)

    for spec in USE:
        try:
            targets = resolve_use(u, spec)
        except Reject as e:
            reject(e)
            continue
        if not targets:
            print("cpp2lean: --use %s: no library function, member function or constructor of this name%s" %
                  (spec, " and these parameter types" if "(" in spec else ""))
            sys.exit(2)
        for kind, rec, d in targets:
            try:
                if kind == "fn":
                    u.free_result(d, d)
                elif kind == "static":
                    u.static_result(rec, d, d)
                elif kind == "ctor":
                    u.context(rec, d).ctor(d, top=True, node=d)
                else:
                    ctx = u.context(rec, d)
                    ctx.method(ctx.resolve(d, virtual_dispatch=False), d)
            except Reject as e:
                reject(e)

    for ctx in list(u.contexts.values()):
        try:
            ctx.finish_owner_helpers()
        except Reject as e:
            reject(e)

    if rejects:
        for _, f, line, col, what in sorted(rejects):
            what = UNNAMED_AT.sub(lambda m: "(unnamed %s at %s:%s:%s)" % (m.group(1), u.shown_path(m.group(2)), m.group(3), m.group(4)), what)
            print("%s:%d:%d: rejected: %s" % (f, line, col, what))
        sys.exit(2)
    return emit(u, ns, shown, list(u.const_items.values()), options)


def split_top(text, sep=","):
    """Split at `sep` outside angle brackets and parentheses."""
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out]


def norm_param_type(q):
    """A parameter type for --use matching: without const, references and tags, spaces normalized."""
    q = re.sub(r"\b(const|struct|class|enum)\b", " ", q).replace("&", " ")
    q = re.sub(r"\s+", " ", q).strip()
    return q.replace("< ", "<").replace(" >", ">").replace(" ,", ",")


def resolve_use(u, spec):
    """The definitions a --use SPEC names: `name` or `Class<args>::member`, optionally followed by
    the parameter types `(T1, T2)` (as written or as clang desugars them, without const and &):
    [(kind, record or None, decl)], kind fn, static, method or ctor."""
    m = re.match(r"^(.*?)(?:\((.*)\))?$", spec.strip())
    name, ptext = m.group(1).strip(), m.group(2)
    want = None if ptext is None else [norm_param_type(x) for x in split_top(ptext)]

    def params_match(d):
        if want is None:
            return True
        ps = [p for p in kids(d) if p.get("kind") == "ParmVarDecl"]
        if len(ps) != len(want):
            return False
        for p, w in zip(ps, want):
            t = p["type"]
            forms = {norm_param_type(t["qualType"]), norm_param_type(t.get("desugaredQualType", t["qualType"]))}
            forms |= {norm_param_type(TYPEDEFS[f]) for f in list(forms) if f in TYPEDEFS}
            if w not in forms and norm_param_type(TYPEDEFS.get(w, w)) not in forms:
                return False
        return True

    out = []
    if "::" in name:
        cls, member = name.rsplit("::", 1)
        rec = RECORDS.get(cls) or next((r for r in u.records if r.lean == cls), None)
        if rec is None:
            return []
        short = rec.node.get("name")
        for d in rec.methods:
            if not params_match(d) or u.body_of(d) is None or d.get("explicitlyDeleted") or d.get("explicitlyDefaulted"):
                continue
            if d.get("kind") == "CXXConstructorDecl" and member == short:
                out.append(("ctor", rec, d))
            elif d.get("kind") == "CXXMethodDecl" and d.get("name") == member:
                out.append(("static" if d.get("storageClass") == "static" else "method", rec, d))
        return out
    for d in u.fn_by_name.get(name, []):
        if params_match(d):
            out.append(("fn", None, d))
    return out


def instantiated(d):
    """Has a class or function template a specialization in the unit?"""
    return any(c.get("kind") == "ClassTemplateSpecializationDecl" or (c.get("kind") == "FunctionDecl" and c.get("mangledName"))
               for c in kids(d))


def deferred_init(f):
    """A default member initializer that constructs an object of a class with parameters or with a
    back-reference (`Thrust_Linearization thr_lin {*this}`): run by each constructor that does not
    initialize the member (as C++ does), not a structure default."""
    if not f.decl.get("hasInClassInitializer") or f.t.kind != "record" or f.t.info.kind != "class":
        return None
    e = strip_parens(kids(f.decl)[-1])
    while e.get("kind") in ("ExprWithCleanups", "MaterializeTemporaryExpr", "CXXBindTemporaryExpr") and kids(e):
        e = kids(e)[0]
    if e.get("kind") != "CXXConstructExpr":
        return None
    if f.t.info.has_params() or any(g.category == "owner" for g in f.t.info.all_fields()) or any(is_star_this(a) for a in kids(e)):
        return e
    return None


def field_default(u, r, f):
    """The default of a field (its member initializer, else zero), and the items it uses."""
    if f.category in ("boundary", "ref", "owner"):
        return
    if deferred_init(f) is not None:
        f.default = zero_of(f.t, f.decl)
        return
    if f.decl.get("hasInClassInitializer"):
        init = kids(f.decl)[-1]
        tr = Body(u, None, None, home=r.lean)
        if f.t.kind == "array" and init.get("kind") == "InitListExpr":
            pre, v = tr.array_init(init, f.t)
        elif init.get("kind") == "InitListExpr":
            if kids(init):
                raise Reject(init, "brace initializer with values for member `%s`" % f.name)
            pre, v = [], zero_of(f.t, f.decl)
        else:
            pre, v = tr.expr(init)
        if pre:
            raise Reject(init, "member initializer with side effects")
        f.default, f.deps = v, tr.deps
    else:
        f.default = zero_of(f.t, f.decl)


# ---------------------------------------------------------------------------------------------
# Emission.

def where_of(u, n):
    rng = n["range"]
    b, e = expansion(rng["begin"]), expansion(rng["end"])
    return line_range(u.shown_path(b.get("file")), b["line"], e["line"])


def emit_enum(e, u):
    short = e.lean.split(".")[-1]
    out = ["/-- C++ `enum %s%s`, `%s`. -/" % ("class " if e.node.get("scopedEnumTag") else "", comment_safe(e.cxx), comment_safe(where_of(u, e.node))),
           "inductive %s where" % short]
    out += ["  | %s" % e.ctor_names[nm] for nm, _ in e.values]
    out.append("deriving DecidableEq, Inhabited")
    out.append("")
    out.append("/-- The value of each enumerator of `%s` (underlying type `%s`). -/" % (comment_safe(e.cxx), e.under.cname))
    out.append("def %s.toInt : %s → %s" % (short, short, e.under.lean))
    out += ["  | .%s => %s" % (e.ctor_names[nm], lit(str(v), e.under).text) for nm, v in e.values]
    if e.used_ofInt:
        out.append("")
        out.append("/-- The enumerator of `%s` with value `v` (the C++ converts only enumerator values; any other" % comment_safe(e.cxx))
        out.append("value gives the first enumerator, the `Inhabited` default). -/")
        out.append("def %s.ofInt (v : %s) : %s :=" % (short, e.under.lean, short))
        for i, (nm, v) in enumerate(e.values):
            out.append("  %sif v == %s then .%s" % ("" if i == 0 else "else ", lit(str(v), e.under).text, e.ctor_names[nm]))
        out.append("  else default")
    return out


def emit_structure(name, fields, doc):
    """fields: (lean name, Lean type, default text, doc comment)."""
    out = [doc, "structure %s where" % name]
    for fname, ftype, fdefault, fdoc in fields:
        out.append("  " + fdoc)
        out.append("  %s : %s := %s" % (fname, ftype, fdefault))
    out.append("deriving Inhabited")
    return out


def field_doc(f, u):
    loc = expansion(f.decl.get("loc"))
    where = line_range(u.shown_path(loc.get("file")), loc["line"], loc["line"])
    bit = " : 1" if f.decl.get("isBitfield") else ""
    return "/-- `%s%s` of `%s` (`%s`). -/" % (comment_safe(cpp_var_decl(f.decl)), bit, comment_safe(f.owner.cxx), comment_safe(where))


def emit_plain(r, u):
    fields = [(f.lean, f.t.lean, f.default.text, field_doc(f, u)) for f in r.all_fields() if f.category == "state"]
    doc = "/-- C++ `%s %s`, `%s`. -/" % (r.node.get("tagUsed", "struct"), comment_safe(r.cxx), comment_safe(where_of(u, r.node)))
    return emit_structure(r.lean.split(".")[-1], fields, doc)


def emit_context(ctx, u):
    r = ctx.rec
    out = []
    where = where_of(u, r.node)
    chain = r.chain()
    bases = "" if len(chain) == 1 else "; base classes flattened, base first: %s" % ", ".join("`%s`" % comment_safe(b.cxx) for b in chain[1:])
    pf = [f for f in r.all_fields() if f.category == "param"]
    sub_p = [f for f in r.all_fields() if f.category == "state" and f.t.kind == "record" and f.t.info.kind == "class" and f.t.info.has_params()]
    if pf or sub_p:
        fields = [(f.lean, f.t.lean, zero_of(f.t, f.decl).text, field_doc(f, u)) for f in pf]
        fields += [(f.lean, f.t.info.lean + ".Params", "{}", field_doc(f, u)) for f in sub_p]
        out += emit_structure("Params", fields, "/-- Parameters of C++ `%s` (`%s`): its members of a --param-class type%s. -/" % (comment_safe(r.cxx), comment_safe(where), bases))
        out.append("")
    fields = [(f.lean, f.t.lean, f.default.text, field_doc(f, u)) for f in r.all_fields() if f.category == "state"]
    out += emit_structure("State", fields, "/-- State of C++ `%s` (`%s`): its data members%s. -/" % (comment_safe(r.cxx), comment_safe(where), bases))
    if ctx.owner_reads:
        out.append("")
        ofs = []
        for key, name, t, node in ctx.owner_reads:
            loc = node_loc(node) or {}
            ofs.append((name, t.lean, zero_of(t, node).text, "/-- `%s` (first read at `%s`). -/" % (
                comment_safe(ctx.u.text_of(node) or name), comment_safe(line_range(ctx.u.shown_path(loc.get("file")), loc.get("line", 0), loc.get("line", 0))))))
        out += emit_structure("Owner", ofs, "/-- What C++ `%s` reads through its reference to the object that holds it as a member (one field per distinct read): the owner computes these values when it calls a member function that reads them. -/" % comment_safe(r.cxx))
    rf = [f for f in r.all_fields() if f.category == "ref"]
    if rf:
        out.append("")
        out += emit_structure("Refs", [(f.lean, f.t.lean, zero_of(f.t, f.decl).text, field_doc(f, u)) for f in rf],
                              "/-- The values the `const` reference members of C++ `%s` refer to (bound by its constructor to values of the owner; the owner passes them). -/" % comment_safe(r.cxx))
    if ctx.inputs or ctx.sub_inputs:
        out.append("")
        ifields = []
        for key, name, t, cxx, node in ctx.inputs:
            loc = node_loc(node) or {}
            ifields.append((name, t.lean, zero_of(t, node).text, "/-- `%s` (first read at `%s`). -/" % (
                comment_safe(cxx), comment_safe(line_range(u.shown_path(loc.get("file")), loc.get("line", 0), loc.get("line", 0))))))
        for fld, sub in ctx.sub_inputs.items():
            ifields.append((fld, sub.rec.lean + ".Inputs", "{}", "/-- What member `%s` reads from the boundary. -/" % fld))
        out += emit_structure("Inputs", ifields, "/-- Values C++ `%s` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/" % comment_safe(r.cxx))
    if ctx.outputs or ctx.sub_outputs:
        out.append("")
        ofields = []
        for key, name, t, cxx, node in ctx.outputs:
            loc = node_loc(node) or {}
            ofields.append((name, t.lean, zero_of(t, node).text, "/-- Argument `%s` (first written at `%s`); the last call's value. -/" % (
                comment_safe(cxx), comment_safe(line_range(u.shown_path(loc.get("file")), loc.get("line", 0), loc.get("line", 0))))))
        for fld, sub in ctx.sub_outputs.items():
            ofields.append((fld, sub.rec.lean + ".Outputs", "{}", "/-- What member `%s` writes to the boundary. -/" % fld))
        out += emit_structure("Outputs", ofields, "/-- Values C++ `%s` writes to objects outside the translation (--boundary) through non-const `void` member functions: one field per parameter, holding the last value written. -/" % comment_safe(r.cxx))
    return out


def emit_method(m):
    out = []
    if m.unused:
        out.append("-- not read in the Lean: %s" % ", ".join(m.unused))
        out.append("set_option linter.unusedVariables false in")
    out.append(m.doc)
    out.append(m.header)
    out += ["  " + l for l in m.lines]
    return out


def emit_skipped(skipped):
    out = ["/-! Not emitted, since they have no effect in the model (they write neither the state, the",
           "parameters nor a reference parameter; e.g. they only save parameters):"]
    for m in skipped:
        out.append("- %s" % m.doc[4:-3].strip())
    out.append("-/")
    return out


def emit_free(fr, u):
    d = fr.decl
    out = []
    if fr.unused:
        out.append("-- not read in the Lean: %s" % ", ".join(fr.unused))
        out.append("set_option linter.unusedVariables false in")
    sig = cpp_signature(d, fr.cparams)
    owner = u.parent_record(d)
    if owner is not None:
        sig = "static " + sig.replace(" %s(" % d["name"], " %s::%s(" % (owner.cxx, d["name"]), 1)
    out.append("/-- C++ `%s`, `%s`. -/" % comment_safe_pair(sig, where_of(u, fr.defn)))
    out.append("def %s%s : %s := Id.run do" % (fr.lean, fr.binders, fr.ret_lean))
    out += ["  " + l for l in fr.lines]
    return out


def type_deps(t):
    if t is None:
        return set()
    if t.kind == "record":
        return {("rec", t.info.id) if t.info.kind == "plain" else ("T", t.info.id)}
    if t.kind == "enum":
        return {("enum", t.info.cxx)}
    if t.kind == "array":
        return type_deps(t.elem)
    if t.kind == "fun":
        d = {("outputs",)} | type_deps(t.elem)
        for a in t.args:
            d |= type_deps(a)
        return d
    return set()


def plain_block(u, r):
    deps = set()
    for f in r.all_fields():
        deps |= f.deps | type_deps(f.t)
    return {"key": srckey_node(u, r.node), "ns": r.lean.rsplit(".", 1)[0] if "." in r.lean else None,
            "lines": emit_plain(r, u), "deps": deps, "id": ("rec", r.id)}


def emit(u, ns, shown, items, options):
    blocks = []
    optional = {}       # library enums and plain structs: emitted only if something emitted uses them
    for e in u.enums:
        b = {"key": srckey_node(u, e.node), "ns": e.lean.rsplit(".", 1)[0] if "." in e.lean else None,
             "lines": emit_enum(e, u), "deps": type_deps(e.under), "id": ("enum", e.cxx)}
        if u.is_lib(e.node):
            optional[b["id"]] = b
        else:
            blocks.append(b)
    for r in u.records:
        if r.kind == "plain":
            if r.lib:
                optional[("rec", r.id)] = r
            else:
                blocks.append(plain_block(u, r))
    items = items + [{"key": srckey_node(u, fr.decl), "kind": "fn", "id": k, "payload": fr, "deps": fr.deps}
                     for k, fr in u.free_results.items() if fr is not None]
    for it in items:
        if it["kind"] == "const":
            d, c, v = it["payload"]
            owner = u.parent_record(d) if c["ns"] != ns else None
            txt = cpp_var_decl(d) if owner is None else "static " + cpp_var_decl(d, "%s::%s" % (owner.cxx, d["name"]))
            lines = ["/-- C++ `%s`, `%s`. -/" % comment_safe_pair(txt, where_of(u, d)), "def %s : %s := %s" % (c["lean"], c["t"].lean, v.text)]
            blocks.append({"key": it["key"], "ns": c["ns"], "lines": lines, "deps": set(it["deps"]) | type_deps(c["t"]), "id": it["id"]})
        else:
            fr = it["payload"]
            deps = set(fr.deps) | type_deps(fr.ret)
            for _, _, pt, _ in fr.cparams:
                deps |= type_deps(pt)
            blocks.append({"key": it["key"], "ns": ns, "lines": emit_free(fr, u), "deps": deps, "id": it["id"]})
    for key, sr in u.static_results.items():
        owner = u.parent_record(sr.decl)
        deps = set(sr.deps) | type_deps(sr.ret)
        for _, _, pt, _ in sr.cparams:
            deps |= type_deps(pt)
        blocks.append({"key": srckey_node(u, sr.decl), "ns": owner.lean, "lines": emit_free(sr, u), "deps": deps, "id": key})
    done_ctx = set()

    def context_blocks(rid, ctx):
        """The structures of a class (one block), and one block per member function, so that the
        functions of two classes that call each other (Vector2f.todouble, Vector2d.tofloat) are
        ordered one by one."""
        done_ctx.add(rid)
        deps = set()
        for f in ctx.rec.all_fields():
            if f.category != "owner":       # the back-reference's class is not part of this object
                deps |= f.deps | type_deps(f.t)
        for key, name, t, cxx, node in ctx.inputs:
            deps |= type_deps(t)
        for sub in ctx.sub_inputs.values():
            deps.add(("T", sub.rec.id))
        for key, name, t, cxx, node in ctx.outputs:
            deps |= type_deps(t)
        for sub in ctx.sub_outputs.values():
            deps.add(("T", sub.rec.id))
        key0 = srckey_node(u, ctx.rec.node)
        if OUTPUT_LOG[0] and u.out_ctors:
            deps.add(("outputs",))
        out = [{"key": key0, "ns": ctx.rec.lean, "lines": emit_context(ctx, u), "deps": deps, "id": ("T", rid)}]
        skipped = []
        for m in sorted(ctx.results.values(), key=lambda m: m.order):
            if m.noeffect:
                skipped.append(m)
                continue
            out.append({"key": key0 + (m.order,), "ns": ctx.rec.lean, "lines": emit_method(m), "deps": set(m.deps), "id": m.bid})
        for field, text, hdeps in ctx.helper_blocks:
            out.append({"key": key0 + (0,), "ns": ctx.rec.lean, "lines": text, "deps": set(hdeps) - {("T", rid)} | {("T", rid)},
                        "id": ("own", rid, field)})
        if skipped:
            out.append({"key": key0 + (10 ** 6,), "ns": ctx.rec.lean, "lines": emit_skipped(skipped),
                        "deps": {m.bid for m in ctx.results.values() if not m.noeffect} | {("T", rid)}, "id": ("skipped", rid)})
        return out

    if OUTPUT_LOG[0] and u.out_ctors:
        deps = set()
        lines = ["/-- What the translated classes write to objects outside the translation (--boundary, --boundary-call):",
                 "one constructor per boundary function or data member written, with its arguments (--output-log). -/",
                 "inductive Output where"]
        for name, (targs, sig, node) in u.out_ctors.items():
            loc = node_loc(node) or {}
            lines.append("  /-- `%s` (first at `%s`). -/" % (comment_safe(sig), comment_safe(line_range(u.shown_path(loc.get("file")), loc.get("line", 0), loc.get("line", 0)))))
            lines.append("  | %s%s" % (name, "".join(" (%s : %s)" % (lean_ident(nm, node), t.lean) for nm, t in targs)))
            for _, t in targs:
                deps |= type_deps(t)
        lines += ["", "/-- The boundary calls of a member function, in the order the C++ makes them. -/", "abbrev Outputs := Array Output"]
        blocks.append({"key": (-1, "", 0, 0), "ns": ns, "lines": lines, "deps": deps, "id": ("outputs",)})
    for rid, ctx in list(u.contexts.items()):
        blocks += context_blocks(rid, ctx)
    while True:         # add the library types the emitted blocks use (transitively)
        have = {b["id"] for b in blocks}
        need = [d for b in blocks for d in b["deps"] if (d in optional or (d[0] == "T" and d[1] not in done_ctx)) and d not in have]
        if not need:
            break
        for d in sorted(set(need), key=str):
            if d[0] == "T":             # a class used only as a type: its structures
                rec = u.records_by_id[d[1]]
                if rec.abstract:
                    users = [b["id"] for b in blocks if d in b["deps"]]
                    raise AssertionError("abstract %s needed by %s" % (rec.cxx, users[:5]))
                blocks += context_blocks(d[1], u.context(rec, rec.node))
                continue
            o = optional[d]
            if isinstance(o, RecordInfo):
                u.ensure_fields(o)
                o = plain_block(u, o)
            blocks.append(o)
    for b in blocks:
        b["deps"].discard(b["id"])
    byid = {b["id"]: b for b in blocks}
    # equal keys (two specializations of one template, `MIN<float, float>` and `MIN<float, AP_Float>`,
    # at the template's location): by the emitted text, so the order does not depend on the AST's ids
    def ast_pos(x):
        """The AST position of the first declaration id in a block id (a tie-break for equal keys:
        two specializations of one template at the template's location, which would otherwise keep
        the order of the dependency search, sorted by the ids' values)."""
        if isinstance(x, str):
            return u.ast_order.get(x)
        if isinstance(x, tuple):
            for y in x:
                p = ast_pos(y)
                if p is not None:
                    return p
        return None
    blocks.sort(key=lambda b: (b["key"], ast_pos(b["id"]) or 0))
    order, done = [], set()

    def place(b):
        if b["id"] in done:
            return
        done.add(b["id"])
        for dep in sorted((d for d in b["deps"] if d in byid), key=lambda d: (byid[d]["key"], ast_pos(d) or 0)):
            place(byid[dep])
        order.append(b)

    for b in blocks:
        place(b)

    out = []
    if u.uses_libm:
        out += ["import CppLibm", ""]
    out.append("/-!")
    out.append("Generated by cpp2lean from `%s`. Do not edit; regenerate with" % comment_safe(shown))
    out.append("`python3 cpp2lean.py %s -o <dir> --namespace %s%s`." % (comment_safe(shown), ns, comment_safe(options)))
    out.append("")
    out.append("Each `def` is the C++ function of the same name, translated node by node from clang's AST")
    out.append("(`clang++ %s`)." % " ".join(CLANG_FLAGS))
    out.append("Under the compilation assumptions of cpp2lean/README.md, each computes the same result as the")
    out.append("C++ bit for bit (checked by cpp2lean/difftest.py).")
    out.append("-/")
    outer = ns if NEST[0] else None
    if outer is not None:
        out += ["", "namespace %s" % outer]
    cur = None
    for b in order:
        bns = None if outer is not None and b["ns"] == outer else b["ns"]
        if bns != cur:
            if cur is not None:
                out += ["", "end %s" % cur]
            if bns is not None:
                out += ["", "namespace %s" % bns]
            cur = bns
        out.append("")
        out += b["lines"]
    if cur is not None:
        out += ["", "end %s" % cur]
    if outer is not None:
        out += ["", "end %s" % outer]
    return "\n".join(out) + "\n", signatures(u, ns, shown), u.uses_libm, u.literals


def leaf_fields(t, lean, cxx):
    """The scalar leaves of a value of type t: (Lean access, C++ access, C++ type, enum)."""
    out = []
    if t.kind == "record":
        for f in t.info.all_fields():
            if f.category == "state":
                out += leaf_fields(f.t, lean + "." + f.lean, cxx + "." + f.name)
    elif t.kind == "array":
        for k in range(t.n):
            out += leaf_fields(t.elem, "%s[%d]!" % (lean, k), "%s[%d]" % (cxx, k))
    elif t.kind == "enum":
        out.append((lean, cxx, t.info.under.cname, t.info.lean))
    else:
        out.append((lean, cxx, t.cname, None))
    return out


def record_leaves(t):
    """The scalar leaves of a value of a translated struct or class type, for the drivers:
    [{lean, cxx, type, enum}], or None for another type."""
    if t is None or t.kind != "record":
        return None
    if any(f.category != "state" for f in t.info.all_fields()):
        return None
    out = []
    pre = ROOT_NS[0] + "." if NEST[0] and ROOT_NS[0] else ""
    for a, b, c, e in leaf_fields(t, "", ""):
        if "[" in a:
            return None
        out.append({"lean": a.lstrip("."), "cxx": b.lstrip("."), "type": c, "enum": None if e is None else pre + e})
    return out


def param_leaves(r, lean, cxx):
    """The parameters of record r and of its member objects: (Lean path, C++ access, type, enum);
    an enum parameter (AP_Enum<E>) is printed as its value."""
    out = []
    for f in r.all_fields():
        if f.category == "param" and f.t.kind == "enum":
            out.append((lean + f.lean, cxx + f.name + ".get()", f.t.info.under.cname, f.t.info.lean))
        elif f.category == "param":
            out.append((lean + f.lean, cxx + f.name + ".get()", f.t.cname, None))
        elif f.category == "state" and f.t.kind == "record" and f.t.info.kind == "class" and f.t.info.has_params():
            out += param_leaves(f.t.info, lean + f.lean + ".", cxx + f.name + ".")
    return out


def access_of(u, d):
    """C++ access of a member declaration: the last access specifier before it in its class."""
    p = u.parent.get(d["id"])
    if p is None:
        return "public"
    acc = "private" if p.get("tagUsed") == "class" else "public"
    for c in kids(p):
        if c.get("kind") == "AccessSpecDecl":
            acc = c["access"]
        if c.get("id") == d["id"]:
            return acc
    return acc


def template_call_name(d):
    """The C++ name that calls exactly this function: `name<args>` for a function template
    specialization (so that a non-template overload with the same parameters is not chosen)."""
    targs = [c for c in kids(d) if c.get("kind") == "TemplateArgument"]
    if not targs:
        return d["name"]
    out = []
    for a in targs:
        if a.get("type"):
            out.append(a["type"]["qualType"])
        elif kids(a):           # a pack: its elements
            out += [x.get("type", {}).get("qualType", "?") for x in kids(a) if x.get("kind") == "TemplateArgument"]
        else:
            return d["name"]
    return "%s<%s>" % (d["name"], ", ".join(out))


def var_info_sig(u, rec):
    """The AP_Param table of a class (--ap-param), for the vehicles' parameter loaders: one entry per
    line, in table order: a parameter `{name, param: Lean path in the class's Params, type, enum,
    storage}` or a nested table `{name, group: class, member: Lean path of the member object or None}`
    (AP_SUBGROUPINFO, AP_NESTEDGROUPINFO)."""
    out = []
    for entry in kids(kids(rec.var_info)[0]) if rec.var_info is not None and kids(rec.var_info) else []:
        if entry.get("kind") != "InitListExpr" or len(kids(entry)) < 3:
            continue
        lit = next((m for m in walk(kids(entry)[0]) if m.get("kind") == "StringLiteral"), None)
        name = json.loads(lit["value"]) if lit is not None else ""
        offset, union = kids(entry)[1], kids(entry)[2]
        member = next((m for m in walk(offset) if m.get("kind") == "MemberExpr"), None)
        chain = []
        m = member
        while m is not None and m.get("kind") == "MemberExpr":
            chain.append(m)
            m = strip_object(kids(m)[0])
        chain.reverse()
        r, steps, ok = rec, [], True
        for mm in chain[:-1]:
            g = r.field_by_id(mm["referencedMemberDecl"])
            if g is None or g.t.kind != "record":
                ok = False
                break
            steps.append(g.lean)
            r = g.t.info
        uf = union.get("field", {}).get("name")
        if uf in ("group_info", "group_info_ptr"):
            ref = next((x for x in walk(union) if x.get("kind") == "DeclRefExpr"), None)
            vd = u.decl(ref["referencedDecl"]["id"]) if ref else None
            owner = u.parent_record(vd) if vd else None
            mem = None
            if member is not None and ok:
                g = r.field_by_id(member["referencedMemberDecl"])
                mem = ".".join(steps + [g.lean]) if g is not None else None
            if owner is None:
                break                   # AP_GROUPEND: `{ "", 0, { group_info : nullptr }, ... }`
            out.append({"name": name, "group": owner.cxx, "member": mem})
            continue
        if member is None:
            break                       # AP_GROUPEND
        f = r.field_by_id(member["referencedMemberDecl"]) if ok else None
        if f is None or f.category != "param":
            continue
        out.append({"name": name, "param": ".".join(steps + [f.lean]), "type": f.t.cname,
                    "enum": (ROOT_NS[0] + "." if NEST[0] and ROOT_NS[0] else "") + f.t.info.lean if f.t.kind == "enum" else None,
                    "storage": f.storage})
    return out


def input_sig(name, t, cxx):
    """An Inputs field in signatures.json; a live read (--boundary-live) as the type of its value,
    with `live` holding the argument types after the output log."""
    if t.kind == "fun":
        return {"lean": name, "type": t.elem.cname, "cxx": cxx, "leaves": record_leaves(t.elem),
                "live": {"args": [a.cname for a in t.args]}}
    return {"lean": name, "type": t.cname, "cxx": cxx, "leaves": record_leaves(t)}


def signatures(u, ns, shown):
    scalar = ("float", "double", "bool", "int")
    pre = ns + "." if NEST[0] else ""

    def param_entries(cparams):
        params = []
        for p, pn, pt, ref in cparams:
            params.append({"name": p.get("name"), "type": pt.cname, "ref": ref, "boundary": pn is None,
                           "enum": pre + pt.info.lean if pt.kind == "enum" else None,
                           "under": pt.info.under.cname if pt.kind == "enum" else None,
                           "scalar": pt.kind in scalar or pt.kind == "enum",
                           "lean_type": pre + pt.lean if pt.kind == "record" else None,
                           "leaves": record_leaves(pt)})
        return params

    def ret_entries(ret):
        return {"ret": ret.cname, "ret_enum": pre + ret.info.lean if ret.kind == "enum" else None,
                "ret_under": ret.info.under.cname if ret.kind == "enum" else None,
                "ret_scalar": ret.kind in scalar or ret.kind == "enum", "ret_leaves": record_leaves(ret)}

    free = []
    for key in sorted(u.free_results, key=lambda k: srckey_node(u, u.decl(k))):
        fr = u.free_results[key]
        if fr is None:
            continue
        f = u.decl_file(fr.decl) or ""
        e = {"cxx": fr.decl["name"], "cxx_call": template_call_name(fr.decl), "lean": "%s.%s" % (ns, fr.lean),
             "file_static": fr.decl.get("storageClass") == "static" and not f.endswith((".h", ".hpp")),
             "kind": "free", "top": False, "owner": None, "access": "public", "reads": [], "writes": [],
             "uses_inp": False, "params": param_entries(fr.cparams)}
        e.update(ret_entries(fr.ret))
        free.append(e)
    for key, sr in u.static_results.items():
        owner = u.parent_record(sr.decl)
        e = {"cxx": sr.decl["name"], "cxx_call": "%s::%s" % (owner.cxx, sr.decl["name"]),
             "lean": "%s%s.%s" % (pre, owner.lean, sr.lean), "kind": "free", "top": False, "owner": owner.cxx,
             "access": access_of(u, sr.decl), "reads": [], "writes": [], "uses_inp": False,
             "params": param_entries(sr.cparams)}
        e.update(ret_entries(sr.ret))
        free.append(e)
    sigs = []
    for key in sorted(u.free_results, key=lambda k: srckey_node(u, u.decl(k))):
        fr = u.free_results[key]
        if fr.outs or fr.ret.kind not in scalar or any(pt.kind not in scalar for _, _, pt, _ in fr.cparams):
            continue
        d = fr.decl
        rng = d["range"]
        sigs.append({"name": d["name"], "lean": "%s.%s" % (ns, fr.lean),
                     "params": [[p["name"], pt.cname] for p, pn, pt, ref in fr.cparams], "ret": fr.ret.cname,
                     "source": line_range(shown, expansion(rng["begin"])["line"], expansion(rng["end"])["line"])})
    classes = []
    for rid, ctx in u.contexts.items():
        r = ctx.rec
        methods = []
        for res in sorted(ctx.results.values(), key=lambda m: m.order):
            if res.noeffect or res.alias:
                continue            # a translation for one call site (Context.method alias) is not driven
            d = res.decl
            e = {"cxx": d.get("name"), "lean": "%s%s.%s" % (pre, r.lean, res.lean), "top": res.top,
                 "kind": "ctor" if d.get("kind") == "CXXConstructorDecl" else "method",
                 "owner": u.parent_record(d).cxx, "access": access_of(u, d),
                 "reads": sorted(res.reads), "writes": sorted(res.writes), "uses_inp": res.uses_inp,
                 "uses_own": res.uses_own,
                 "params": param_entries(res.cparams)}
            e.update(ret_entries(res.ret))
            methods.append(e)
        leaves = [("p", a, b, c, None if e is None else pre + e) for a, b, c, e in param_leaves(r, "", "")]
        for f in r.all_fields():
            if f.category == "state":
                leaves += [("s", a, b, c, None if e is None else pre + e) for a, b, c, e in leaf_fields(f.t, f.lean, f.name)]
        classes.append({"cxx": r.cxx, "lean": pre + r.lean, "has_params": r.has_params(),
                        "inputs": [input_sig(name, t, cxx) for key, name, t, cxx, node in ctx.inputs],
                        "sub_inputs": [{"field": k, "class": v.rec.cxx} for k, v in ctx.sub_inputs.items()],
                        "outputs": [{"lean": name, "type": t.cname, "cxx": cxx, "scalar": t.kind in scalar, "leaves": record_leaves(t)}
                                    for key, name, t, cxx, node in ctx.outputs],
                        "sub_outputs": [{"field": k, "class": v.rec.cxx} for k, v in ctx.sub_outputs.items()], "methods": methods,
                        "leaves": [{"root": a, "lean": b, "cxx": c, "type": t, "enum": e} for a, b, c, t, e in leaves]})
    enums = [{"cxx": e.cxx, "lean": pre + e.lean, "under": e.under.cname, "values": [[nm, v, e.ctor_names[nm]] for nm, v in e.values]}
             for e in u.enums]
    out_log = [{"name": name, "cxx": sig, "args": [{"name": nm, "type": t.under_cname() if t.kind == "enum" else t.cname,
                                                     "enum": pre + t.info.lean if t.kind == "enum" else None,
                                                     "leaves": record_leaves(t)} for nm, t in targs]}
               for name, (targs, sig, node) in u.out_ctors.items()]
    for c in classes:
        c["output_log"] = bool(OUTPUT_LOG[0] and u.out_ctors)
    var_info = {r.cxx: var_info_sig(u, r) for r in u.records if getattr(r, "var_info", None) is not None}
    return {"functions": sigs, "classes": classes, "enums": enums, "free": free, "output_log": out_log,
            "output_ns": pre if OUTPUT_LOG[0] else None, "var_info": var_info}


def main():
    ap = argparse.ArgumentParser(description="Translate a subset of C++ to Lean 4.")
    ap.add_argument("file")
    ap.add_argument("-o", "--out", required=True, help="output directory")
    ap.add_argument("--namespace", help="Lean namespace of the free functions, and the module name (default: from the file name)")
    ap.add_argument("--header", action="append", default=[], help="a header whose declarations are also translated")
    ap.add_argument("--boundary", action="append", default=[], help="classes that are not translated (comma-separated, or @file)")
    ap.add_argument("--param-class", action="append", default=[], help="Class=type: members of this class are parameters of the scalar type")
    ap.add_argument("--extern", action="append", default=[], help="name:LeanName[:N]: a library function and its Lean counterpart (with N, only the first N arguments are passed)")
    ap.add_argument("-I", dest="includes", action="append", default=[], help="include directory passed to clang")
    ap.add_argument("--lib-dir", action="append", default=[], help="a directory whose files are translated only as far as the translated files use them")
    ap.add_argument("--ap-param", action="store_true", help="ArduPilot's AP_Param: AP_ParamT<T> members are parameters; var_info, setup_object_defaults, load/save (README.md, \"ArduPilot\")")
    ap.add_argument("--drop", action="append", default=[], help="qualified name of a function (e.g. AP_InternalError::error) whose calls are left out: effects outside the model")
    ap.add_argument("--boundary-fn", action="append", default=[], help="qualified name of a free function (e.g. AP_HAL::millis) whose result is an input")
    ap.add_argument("--src-root", action="append", default=[], help="show source paths relative to this directory (e.g. ArduPilot's libraries/)")
    ap.add_argument("--keep-going", action="store_true", help="survey mode: also translate the member functions of a class some of whose data members were rejected (to list every rejection)")
    ap.add_argument("--clang-arg", action="append", default=[], help="an extra clang argument for the AST (e.g. -DNAME=1, -include file, -cl-single-precision-constant)")
    ap.add_argument("--use", action="append", default=[], help="a library function, member function or constructor to translate as if a translated file called it: `name`, `Class<args>::member`, optionally with parameter types `(T1, T2)`; or @file with one per line")
    ap.add_argument("--array-params", action="store_true", help="a `const T *` parameter read only by subscript (`motors[i]`) is the array the caller passes (AP_MotorsMatrix::add_motors)")
    ap.add_argument("--site-inputs", action="store_true", help="a const boundary call with non-constant arguments, outside loops, is one input per call site")
    ap.add_argument("--output-log", action="store_true", help="outputs to the boundary are the calls in order (`Output` events in an `Array`), not the last values written")
    ap.add_argument("--boundary-query", action="append", default=[], help="Class::member: a non-const member function of a boundary class that does not change the object (a getter not marked const, e.g. AC_AttitudeControl::get_bf_feedforward): its calls are inputs, as for a const member function")
    ap.add_argument("--boundary-static", action="append", default=[], help="Class::member: a member function of a boundary class that reads nothing of its object (AP_AHRS::calc_trig): translated as a function of its arguments")
    ap.add_argument("--boundary-live", action="append", default=[], help="Class: a boundary class whose reads are functions of the output log so far (with --output-log): the member function reads it after calling into it (AC_WPNav reading AC_PosControl)")
    ap.add_argument("--boundary-call", action="append", default=[], help="Class::member: a member function of a translated class that is part of the boundary (not translated; calls are boundary calls), e.g. AP_Motors::rc_write")
    ap.add_argument("--nest", action="store_true", help="emit the classes inside the file's namespace too (several translations in one Lean package)")
    ap.add_argument("--type-name", action="append", default=[], help="CXX=Lean: the Lean name of a class template specialization (when its typedef is not unique, e.g. Vector2<double>=Vector2p)")
    a = ap.parse_args()
    for b in a.boundary:
        if b.startswith("@"):
            with open(b[1:]) as f:
                BOUNDARY.update(x for x in re.split(r"[\s,]+", f.read()) if x)
        else:
            BOUNDARY.update(x for x in b.split(",") if x)
    for pc in a.param_class:
        k, _, v = pc.partition("=")
        PARAM_CLASSES[k] = v
    KEEP_GOING[0] = a.keep_going
    AP_PARAM[0] = a.ap_param
    SRC_ROOTS.extend(os.path.realpath(x) + os.sep for x in a.src_root)
    for x in a.drop:
        DROP.update(y for y in x.split(",") if y)
    for x in a.boundary_fn:
        BOUNDARY_FN.update(y for y in x.split(",") if y)
    for x in a.use:
        if x.startswith("@"):
            with open(x[1:]) as f:
                USE.extend(l.strip() for l in f if l.strip() and not l.lstrip().startswith("#"))
        else:
            USE.append(x)
    NEST[0] = a.nest
    OUTPUT_LOG[0] = a.output_log
    ARRAY_PARAMS[0] = a.array_params
    SITE_INPUTS[0] = a.site_inputs
    for x in a.boundary_call:
        BOUNDARY_CALL.update(y for y in x.split(",") if y)
    for x in a.boundary_query:
        BOUNDARY_QUERY.update(y for y in x.split(",") if y)
    for x in a.boundary_live:
        BOUNDARY_LIVE.update(y for y in x.split(",") if y)
    for x in a.boundary_static:
        BOUNDARY_STATIC.update(y for y in x.split(",") if y)
    if BOUNDARY_LIVE and not a.output_log:
        ap.error("--boundary-live needs --output-log")
    for x in a.type_name:
        k, _, v = x.partition("=")
        TYPE_NAMES[k.strip()] = v.strip()
    externs = {}
    for e in a.extern:
        parts = e.split(":")
        externs[parts[0]] = (parts[1], int(parts[2]) if len(parts) > 2 else None)
    ns = a.namespace or default_namespace(a.file)
    opts = ["--header " + portable_path(h) for h in a.header]
    if BOUNDARY:
        opts.append("--boundary " + ",".join(sorted(BOUNDARY)))
    opts += ["--param-class " + pc for pc in a.param_class]
    opts += ["--extern " + e for e in a.extern]
    opts += ["--lib-dir " + portable_path(x) for x in a.lib_dir]
    if a.ap_param:
        opts.append("--ap-param")
    opts += ["--drop " + x for x in a.drop] + ["--boundary-fn " + x for x in a.boundary_fn]
    opts += ["--boundary-call " + x for x in a.boundary_call]
    opts += ["--boundary-query " + x for x in a.boundary_query]
    opts += ["--boundary-live " + x for x in a.boundary_live]
    opts += ["--boundary-static " + x for x in a.boundary_static]
    if a.output_log:
        opts.append("--output-log")
    if a.array_params:
        opts.append("--array-params")
    if a.site_inputs:
        opts.append("--site-inputs")
    opts += ["--use " + portable_arg(x) for x in a.use]
    if a.nest:
        opts.append("--nest")
    opts += ["--type-name " + x for x in a.type_name]
    opts += ["-I" + portable_path(i) for i in a.includes] + ["--clang-arg " + c for c in a.clang_arg]
    text, sigs, uses_libm, lits = translate(a.file, ns, a.header, externs, ["-I" + i for i in a.includes] + a.clang_arg,
                                            (" " + " ".join(opts)) if opts else "", a.lib_dir)
    os.makedirs(a.out, exist_ok=True)
    with open(os.path.join(a.out, ns + ".lean"), "w") as f:
        f.write(text)
    with open(os.path.join(a.out, ns + ".signatures.json"), "w") as f:
        json.dump({"namespace": ns, "source": portable_path(a.file), "functions": sigs["functions"], "classes": sigs["classes"],
                   "enums": sigs["enums"], "free": sigs["free"], "output_log": sigs["output_log"],
                   "output_ns": sigs["output_ns"], "literals": lits, "var_info": sigs["var_info"]}, f, indent=1)
        f.write("\n")
    if uses_libm:
        with open(os.path.join(a.out, "CppLibm.lean"), "w") as f:
            f.write(CPPLIBM)


if __name__ == "__main__":
    main()
