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
signatures, read by difftest.py to generate drivers), and OutDir/CFloat.lean (a copy of
support/CFloat.lean: C's floating-point conversions and exact <math.h> functions on FloatLib's
Binary32/Binary64). A .c file is translated as C (musl's math sources, libm/translate_libm.sh).
"""

import argparse
import copy
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction

CLANG = os.environ.get("CXX", "clang++")
CLANG_FLAGS = ["-std=c++17", "-O2", "-ffp-contract=off", "-fno-fast-math",
               "-fno-builtin-sinf", "-fno-builtin-cosf", "-fno-builtin-sin", "-fno-builtin-cos"]
# Added for code generation (the C++ driver of difftest.py, and moreLeancArgs of the Lean side),
# not needed for the AST: without it clang -O2 rewrites libm calls with constant arguments, e.g.
# powf(x, 0.5f) into an fsqrt-based sequence that differs from libm powf by 1 ulp (README.md,
# "Compilation assumptions").
CODEGEN_EXTRA = ["-fno-builtin"]
# C sources (a .c file: musl's libm, README.md "The C library") are parsed as C99 with the C compiler.
CC = os.environ.get("CC", "clang")
C_FLAGS = ["-x", "c", "-std=c99"] + CLANG_FLAGS[1:]
C_MODE = [False]    # the translation unit is C: conditions and comparisons are int-valued
GENERAL_LOOPS = [False]  # --general-loops
UNINIT_READS = [False]  # --uninit-reads
MODULE_FNS = {}     # --module-sig: C function name -> its signature in another translation (signatures.json "free")
IMPORTS = []        # --import


class Reject(Exception):
    """A construct outside the subset, with the AST node whose location is reported."""

    def __init__(self, node, construct):
        super().__init__(construct)
        self.node = node
        self.construct = construct


# ---------------------------------------------------------------------------------------------
# Locations. clang's JSON dumper omits "file" and "line" when they equal those of the previously
# printed location, so they are filled in by replaying the document in print order.

def fill_locations(tree, state=None):
    """Fill in the elided locations of tree; state is the location printed last before tree (a
    declaration read on its own by the streaming reader), and is left at the last one in tree."""
    if state is None:
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
UNION_VIEWS = {}    # --ekf-types: id of an unnamed union member -> (id of its array member, id of its struct member, struct CType)
BITFIELD_VIEWS = set()  # --front-ends: ids of the structs of bit-fields that are views of a bit union (not records)
BITUNIONS = {}      # --ekf-types: union type spelling -> BitUnion (a struct of one-bit bit-fields over an unsigned integer)
ENUMS = {}          # qualified C++ name -> EnumInfo
BOUNDARY = set()    # class names that are not translated (--boundary)
PARAM_CLASSES = {}  # class name -> C++ scalar type name (--param-class)
KEEP_GOING = [False]  # --keep-going: translate the member functions of a class with rejected members
SURVEY = [None]       # --survey (with --keep-going): the reject function; every rejected statement is reported, not only a function's first
AP_PARAM = [False]    # --ap-param: ArduPilot's AP_Param conventions (see README.md, "ArduPilot")
DROP = set()          # --drop: qualified names of functions whose calls are left out (logging, errors)
BOUNDARY_FN = set()   # --boundary-fn: qualified names of free functions whose results are inputs
OUTPUT_FN = set()     # --output-fn (with --output-log): free functions outside the model whose calls are `Output` events
REV_TYPEDEFS = {}     # desugared type spelling -> the unique typedef naming it
PARAM_STORAGE = {}    # parameter class of an enum type (AP_Enum<E>) -> the integer type it stores
WORLD = [False]       # --world: the file-scope objects of translated classes are one `World` (PORT-PLAN.md D1)
OUTPUT_LOG = [False]  # --output-log: outputs are the boundary calls in order (Array Output), not last values
ENUM_AS_INT = set()   # --enum-as-int (Phase 5c): enums outside the translated files whose values are used as their integers (MAV_SEVERITY)
TEXT_BUFFERS = [False]  # --text-buffers (Phase 5c, with --text-log): a local `char buf[N]` and a `char *` parameter are a pending text, `(size, format, arguments)` of the `AP_HAL::Util::snprintf` that fills it (README.md "Phase 5c")
TEXT_RESULTS = set()  # --text-results (Phase 5d, with --text-buffers): `const char *` member functions returning a `char` data member that is a text (TEXTBUF) or the null pointer: their result is a `CText` (`CText.null`)
TEXT_LOG = [False]  # --text-log (Phase 5c): `GCS::send_text(severity, fmt, ...)` is an `Output.send_text severity fmt args` event (README.md "Phase 5c")
PARAM_SAVE_LOG = [False]  # --param-save-log: `AP_Param::save(force)` of a parameter is an `Output.AP_Param_save path force` event
ARRAY_PARAMS = [False]  # --array-params: a `const T *` parameter read only by subscript is the caller's array
SITE_INPUTS = [False]   # --site-inputs: a const boundary call with non-constant arguments is one input per call site
BOUNDARY_CALL = set() # --boundary-call: member functions of translated classes whose calls are boundary calls
BOUNDARY_QUERY = set()  # --boundary-query: non-const member functions of boundary classes that only read (inputs, as const ones)
BOUNDARY_STATIC = set()  # --boundary-static: member functions of boundary classes that read nothing of their object: translated
SRC_ROOTS = []        # --src-root: source paths in comments and messages are shown relative to these
PKG_ROOT = os.path.dirname(os.path.abspath(__file__))   # the cpp2lean directory: other paths are shown relative to it
USE = []              # --use: library functions and member functions translated as if a translated file called them
ROOT_NS = [None]      # the file's namespace (the prefix of every name with --nest)
NEST = [False]        # --nest: classes are emitted inside the file's namespace (several translations in one Lean package)
TYPE_NAMES = {}       # --type-name: C++ class template specialization -> Lean name (when its typedef is not unique)
BITFIELD_WIDTH = {}   # --mavlink: decl id of an unsigned bit-field wider than one bit (`uint32_t msgid:24`) -> its width (writes masked)
SBITFIELD_WIDTH = {}  # --mission: decl id of a signed bit-field (`int32_t alt:24`, PackedLocation) -> its width
BIT1_FIELDS = set()   # decl ids of one-bit unsigned bit-fields (`uint8_t f : 1`): a write stores its value modulo 2
POINTER_PARAMS = [False]  # --pointer-params (phase 2, F6): pointer parameters and local pointers into arrays (README.md, "Phase 2")
RUNTIME_LOOPS = [False]   # --runtime-loops (phase 2, F8): loops bounded by a runtime value (README.md, "Phase 2")
C_STRINGS = [False]       # --c-strings (phase 2b, F7): `char`, string literals, byte pointers, the C string runtime, varargs (README.md, "Phase 2b")
GOTOS = [False]           # --gotos (phase 2b): forward `goto`, `continue` in `do` loops, switch fallthrough, by flags (README.md, "Phase 2b")
BYTE_OBJECTS = [False]    # --byte-objects (phase 2b, F5): object representations as bytes (README.md, "Phase 2b")
EKF_ARRAYS = [False]      # --ekf-arrays (phase 3, F9, F15): multidimensional arrays flat, in-place array writes (README.md, "Phase 3: EKF data structures")
EKF_TYPES = [False]       # --ekf-types (phase 3): the type forms of EKF3's data members (README.md, "Phase 3: EKF data structures")
RING_BUFFERS = [False]    # --ring-buffers (phase 3, F12): type-erased ring buffers monomorphized per typed wrapper (README.md, "Phase 3: EKF data structures")
HAL_STORAGE = [False]     # --hal-storage (phase 2b): `hal.storage->read_block/write_block` on the HAL storage bytes, threaded (README.md, "Phase 2b")
INDEXED_INPUTS = [False]  # --indexed-inputs (Phase 3, AP_DAL): a const boundary call with one non-constant integer argument reads an input array at that index
SIZEOFS = {}              # --sizeof C=N: sizeof of a class whose object representation the model does not hold (from clang)
REACHABLE = [False]       # --reachable (Phase 3, NavEKF3): member functions of translated classes only as far as the --use entry points reach them
WORLD_PTRS = [False]      # --world-pointers (Phase 3, F1/F2/F4): pointers to World objects as tags, dispatch, heap slots (README.md, "Phase 3: World pointers")
SEMAPHORES = set()        # --semaphores (Phase 3, F11): classes whose objects and calls are no-ops (one thread)
WORLD_CLASSES = set()     # --world-class (with --front-ends): library classes whose pointers are World pointers (`SITL::SIM *`, `AP_AccelCal *`)
PARAM_NAMES = {}          # --param-name (with --param-ext): ArduPilot parameter name -> its World object path (set_default_by_name)
FRONT_ENDS = [False]      # --front-ends (Phase 3, sensor front ends): the constructs of the four front ends and their stand-ins (README.md, "Phase 3: sensor front ends and AP_Param")
PARAM_EXT = [False]       # --param-ext (Phase 3, part of F13): AP_Param beyond scalar members: vectors, arrays, parameters in structs and arrays of structs, nested groups (README.md, "Phase 3: sensor front ends and AP_Param")
EST_WORLD = [False]       # --est-world (Phase 3, the estimator World): the front ends and NavEKF3 in one World (README.md, "Phase 3: the estimator World and the EKF3 replay")
INS_GPS = [False]         # --ins-gps (Phase 3, the inertial sensor and GPS front ends): their constructs (README.md, "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source")
ARRAY_OFFSETS = [False]   # --array-offsets (Phase 3, speed): a pointer into an array is passed as the array and an offset, not a slice (README.md, "Phase 3: AP_AHRS, and speed")
MEMBER_OBJECTS = [False]  # --member-objects (Phase 3, AP_AHRS): a static data member of a translated class is a World object (README.md, "Phase 3: AP_AHRS, and speed")
AHRS_EXT = [False]        # --ahrs-ext (Phase 3, AP_AHRS): AP_AHRS's and DCM's other constructs (README.md, "Phase 3: AP_AHRS translated")
MEMBER_PTRS = [False]     # --member-pointers (Phase 3, AP_AHRS): pointers and references to member objects of a World object as tags (README.md, "Phase 3: AP_AHRS translated")
MEMBER_REACH = [False]    # --member-reach (Phase 5c): a call on a member object adds the World objects its callee reaches to the caller's (README.md, "Phase 5c")
SWAP_OUT = [False]        # --swap-out (Phase 3, speed): a World or heap object whose state a call writes is taken out of the World for the call (README.md, "Phase 3: AP_AHRS, and speed")
MAVLINK = [False]         # --mavlink (Phase 4, the MAVLink C library): file-scope state, struct pointers, packed byte layouts, `extern "C"` blocks (README.md, "Phase 4: the MAVLink C library")
MISSION = [False]         # --mission (Phase 4, AP_Mission): unions of members of different types as bytes with member views, signed bit-fields, case ranges, nullable local pointers to members (README.md, "Phase 4: AP_Mission")
NULL_MEMBERS = set()      # --null-member (Phase 4): qualified names of pointer data members that are always null (folded before translation)
HEAP_ALLOC = {"malloc", "calloc"}   # --heap-alloc (Phase 3, F4): functions returning raw memory that placement new constructs objects in


class CType:
    """A C++ type of the subset: arithmetic, a fixed-size array, a translated struct or class
    (`record`), an enum, a boundary class, or a parameter class."""

    def __init__(self, kind, bits=0, signed=False, usize=False, elem=None, n=0, info=None, name=None, args=()):
        self.kind, self.bits, self.signed, self.usize, self.elem, self.n = kind, bits, signed, usize, elem, n
        self.info, self.name = info, name
        self.args = tuple(args)     # kind "fun": the argument types after the output log; elem: the result

    def key(self):
        return (self.kind, self.bits, self.signed, self.usize, self.elem.key() if self.elem else None, self.n,
                id(self.info) if self.info else None, self.name, tuple(a.key() for a in self.args)) + \
            ((self.dims,) if getattr(self, "dims", None) else ())

    def __eq__(self, o):
        return isinstance(o, CType) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    @property
    def lean(self):
        if self.kind == "float":
            return "Binary32"
        if self.kind == "double":
            return "Binary64"
        if self.kind == "bool":
            return "Bool"
        if self.kind == "int":
            if self.usize:
                return "USize"
            if self.name == "char":
                return "UInt8"          # --c-strings: a `char` is stored as its byte (README.md, "Phase 2b")
            return ("Int" if self.signed else "UInt") + str(self.bits)
        if self.kind == "cstr":
            return "Array UInt8"
        if self.kind == "valist":
            return "VaList"
        if self.kind == "args":
            return "Array CArg"
        if self.kind == "nat":
            return "Nat"
        if self.kind == "array":
            return "Array " + self.elem.lean_atom
        if self.kind == "record":
            return self.info.lean_type
        if self.kind == "enum":
            return self.info.lean
        if self.kind == "string":
            return "String"
        if self.kind == "textargs":
            return "Array (Sum UInt64 String)"     # --text-log: the variadic arguments, tagged (below)
        if self.kind == "textbuf":
            return "CText"     # --text-buffers: the formatted write that filled the buffer (Phase 5d: `inductive CText`, text_prelude)
        if self.kind == "obj":
            return "WPtr"           # --world-pointers: a tag of the World's objects (README.md, "Phase 3: World pointers")
        if self.kind == "wfun":
            return "WFun"           # --world-pointers: a functor bound to an object (`FUNCTOR_BIND_MEMBER`)
        if self.kind == "opt":
            return "Option " + self.elem.lean_atom     # --mavlink: a `const T *` that is null or points to a constant
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
            if self.name == "char":
                return "char"
            return ("int" if self.signed else "uint") + str(self.bits) + "_t"
        if self.kind == "cstr":
            return "const char *"
        if self.kind == "valist":
            return "va_list"
        if self.kind == "array":
            if getattr(self, "dims", None):
                return self.elem.cname + "".join("[%d]" % d for d in self.dims)
            return "%s[%d]" % (self.elem.cname, self.n)
        if self.kind in ("record", "enum"):
            return self.info.cxx
        if self.kind in ("boundary", "param"):
            return self.name
        if self.kind == "string":
            return "const char *"
        if self.kind == "textargs":
            return "..."
        if self.kind == "textbuf":
            return "char *"
        if self.kind == "obj":
            return self.info.cxx + " *"
        if self.kind == "sem":
            return self.name
        if self.kind == "wfun":
            return "Functor<void>"
        if self.kind == "opt":
            return "const %s *" % self.elem.cname
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
TEXTBUF = CType("textbuf")  # --text-buffers: a `char` buffer filled by `AP_HAL::Util::snprintf`, as the call's size, format and arguments (`CText`)
CHAR = CType("int", 8, True, name="char")   # --c-strings: C's `char` (signed on the reference target), stored as a byte
INT8 = CType("int", 8, True)
UINT8 = CType("int", 8, False)
CSTR = CType("cstr")        # --c-strings: an element of a table of string literals (`const char *const t[]`): its bytes
VALIST = CType("valist")    # --c-strings: `va_list`
VARARGS = CType("args")     # --c-strings: the variadic arguments of a call (`...`)
NAT = CType("nat")          # an offset into an array (the result of a function returning a pointer into its argument)


def collect_typedefs(tree, found=None):
    """TYPEDEFS and REV_TYPEDEFS from the typedefs of the unit: those of tree, or `found`, the
    (typedef node, at namespace scope) pairs of the whole unit in document order (the streaming
    reader, whose tree holds only the declarations the translation can reach)."""
    rev = {}

    def visit(n, scope_ok):
        for c in kids(n):
            if not isinstance(c, dict):
                continue
            if c.get("kind") in ("TypedefDecl", "TypeAliasDecl") and "name" in c:
                yield c, scope_ok
            yield from visit(c, scope_ok and c.get("kind") in ("NamespaceDecl", "LinkageSpecDecl"))

    for c, scope_ok in (visit(tree, True) if found is None else found):
        if "name" not in c:
            continue
        t = c["type"]
        d = norm_template_args(t.get("desugaredQualType", t["qualType"]))
        TYPEDEFS.setdefault(c["name"], d)
        if scope_ok:            # a namespace-scope typedef names the type for reading
            rev.setdefault(d, set()).add(c["name"])
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


VOLATILE_OK = ("VarDecl", "ParmVarDecl", "DeclRefExpr", "ImplicitCastExpr")


def parse_type_str(sugar, desugared, node):
    s, bad = strip_quals(sugar)
    if bad:
        # a volatile local variable or parameter (musl's fp_barrierf, libm.h): no other code can
        # reach it (no pointers, no mutable globals), so its accesses are ordinary reads and writes;
        # volatile data members and globals stay rejected
        if node.get("kind") not in VOLATILE_OK or (node.get("kind") == "VarDecl" and node.get("storageClass") in ("static", "extern")):
            raise Reject(node, "volatile type `%s`" % sugar)
        s, _ = strip_quals(sugar.replace("volatile", ""))
    d, _ = strip_quals(desugared.replace("volatile", ""))
    if C_STRINGS[0]:
        if s in ("va_list", "__builtin_va_list", "std::va_list") or d == "__builtin_va_list":
            return VALIST
        m3 = re.match(r"^const char \*(?: ?const)?\s*\[(\d+)\]$", desugared.strip())
        if m3:
            return CType("array", elem=CSTR, n=int(m3.group(1)))
    if not C_STRINGS[0] and re.match(r"^const char ?\*$", desugared.strip()) or re.match(r"^const char ?\*$", sugar.strip()):
        return STRING
    if TEXT_BUFFERS[0] and not C_STRINGS[0] and re.match(r"^char ?(\*|\[\d+\])$", d) and \
            (node.get("kind") != "FieldDecl" or re.match(r"^char ?\[\d+\]$", d)) and \
            not (node.get("kind") == "VarDecl" and node.get("storageClass") in ("static", "extern")):
        # --text-buffers: a local `char buffer[N]` or a `char *` parameter (AP_GPS_Backend::_detection_message's, filled
        # by `hal.util->snprintf`, GPS_Backend.cpp:129-154): the pending text (TEXTBUF); (Phase 5d) a `char buffer[N]`
        # data member too (NavEKF3_core::prearm_fail_string, filled by `dal.snprintf`); `char *` data members stay rejected
        return TEXTBUF
    if WORLD_PTRS[0] and "*" in d and "&" not in d:
        # --world-pointers: a pointer to a translated class (or an array of them) is a tag of the
        # closed set of World and heap objects (README.md, "Phase 3: World pointers")
        ma = re.match(r"^(.*?\*(?:\s*const)?)\s*\[(\d+)\]$", d)
        if ma:
            el = world_ptr_type(ma.group(1))
            if el is not None:
                return CType("array", elem=el, n=int(ma.group(2)))
        el = world_ptr_type(d)
        if el is not None:
            return el
    if "*" in d or "&" in d:
        raise Reject(node, "pointer or reference type `%s`" % sugar)
    m2 = re.match(r"^([^\[]*?)\s*\[(\d+)\]\[(\d+)\]$", d)
    if m2 and node.get("kind") == "VarDecl" and "const" in sugar.split("[")[0]:
        # `const T t[A][B]` (a constant table of two dimensions): an array of A rows of B elements
        ms = re.match(r"^([^\[]*?)\s*\[(\d+)\]\[(\d+)\]$", s)
        elem = parse_type_str(ms.group(1) if ms else m2.group(1), m2.group(1), node)
        if not elem.is_scalar():
            raise Reject(node, "two-dimensional array `%s` of something other than numbers" % sugar)
        return CType("array", elem=CType("array", elem=elem, n=int(m2.group(3))), n=int(m2.group(2)))
    m = re.match(r"^(.*?)\s*\[(\d+)\]$", d)
    if m:
        ms = re.match(r"^(.*?)\s*\[(\d+)\]$", s)
        elem = parse_type_str(ms.group(1) if ms else m.group(1), m.group(1), node)
        if elem.kind == "array" and EKF_ARRAYS[0] and (elem.elem.is_scalar() or elem.elem.kind == "record"):
            # --ekf-arrays: `T a[N][M]` (EKF3's Matrix24) is one flat row-major array of N*M elements,
            # `a[i][j]` its element i*M + j (README.md, "Phase 3: EKF data structures")
            t = CType("array", elem=elem.elem, n=int(m.group(2)) * elem.n)
            # (the regular expression takes the last bound: `T[A][B]` is `T[A]` and B here)
            t.dims = (getattr(elem, "dims", None) or (elem.n,)) + (int(m.group(2)),)
            return t
        if elem.kind == "array":
            raise Reject(node, "multidimensional array `%s`" % sugar)
        if elem.kind in ("boundary", "param") or (elem.kind == "record" and elem.info.kind != "plain" and not elem.info.lib and not INS_GPS[0]):
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
    if d == "char" and C_STRINGS[0]:
        return CHAR
    if d in ("char", "wchar_t", "char16_t", "char32_t", "char8_t"):
        raise Reject(node, "character type `%s` (string handling)" % sugar)
    if d == "long double":
        raise Reject(node, "type `long double`")
    name, tag = strip_tag(d)
    name = norm_template_args(name)
    if EKF_TYPES[0] and FRONT_ENDS[0] and name not in BITUNIONS and "::" in name:
        parts = name.split("::")
        name = next(("::".join(parts[k:]) for k in range(1, len(parts)) if "::".join(parts[k:]) in BITUNIONS), name)
    if EKF_TYPES[0] and (d in BITUNIONS or name in BITUNIONS):
        bu = BITUNIONS.get(d) or BITUNIONS[name]
        t = CType("int", bu.word.bits, False)
        t.bu = bu
        return t
    if tag == "union" and not MISSION[0]:       # (--mission: every union is a byte union, looked up below)
        raise Reject(node, "union `%s`" % sugar)
    short = name.split("::")[-1]
    sname = strip_tag(s)[0]          # the type as written (a typedef such as AP_Float)
    if WORLD_PTRS[0] and (name == "Functor<void>" or TYPEDEFS.get(short) == "Functor<void>"):
        return CType("wfun")                # --world-pointers: AP_HAL::MemberProc, a bound (object, method) (F3, timer processes)
    if SEMAPHORES and (name in SEMAPHORES or sname in SEMAPHORES or short in SEMAPHORES):
        return CType("sem", name=name)      # --semaphores: no state, no effect (PORT-PLAN 4.11, F11)
    if AP_PARAM[0] and not PARAM_EXT[0]:
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
    if (PARAM_EXT[0] or FRONT_ENDS[0]) and name not in RECORDS:
        name = param_ext_name(name)
    if FRONT_ENDS[0] and name not in RECORDS and name not in ENUMS and "::" in name and "<" not in name:
        # --front-ends: a member of a class defined with a qualified name at file scope (`class
        # AP_HAL::Device { enum BusType ...`) is registered under the class's own name (`Device::BusType`)
        parts = name.split("::")
        for k in range(1, len(parts) - 1):
            suf = "::".join(parts[k:])
            if suf in RECORDS or suf in ENUMS:
                name = suf
                break
    if name in RECORDS:
        return CType("record", info=RECORDS[name])
    if name in ENUMS:
        return CType("enum", info=ENUMS[name])
    # clang spells a member type used inside its class unqualified; accept a unique short name
    rs = [r for k, r in RECORDS.items() if k.split("::")[-1] == name]
    es = [e for k, e in ENUMS.items() if k.split("::")[-1] == name]
    if len(rs) + len(es) == 1:
        return CType("record", info=rs[0]) if rs else CType("enum", info=es[0])
    if len(rs) + len(es) > 1 and CURRENT_UNIT[0] is not None:
        er = CURRENT_UNIT[0].enclosing_record(node)
        while er is not None:
            if er.cxx + "::" + name in RECORDS:
                return CType("record", info=RECORDS[er.cxx + "::" + name])
            if er.cxx + "::" + name in ENUMS:
                return CType("enum", info=ENUMS[er.cxx + "::" + name])
            er = er.parent
    if EKF_ARRAYS[0] and "::" in name and name.rsplit("::", 1)[0] in RECORDS:
        # `NavEKF_core_common::Matrix24` (`auto& nextP = KHP;`, AP_NavEKF3_core.cpp:1175): a typedef of a class
        owner, short = name.rsplit("::", 1)
        td = next((c for c in kids(RECORDS[owner].node) if c.get("kind") in ("TypedefDecl", "TypeAliasDecl") and c.get("name") == short), None)
        if td is not None:
            return parse_type_str(sugar, td["type"].get("desugaredQualType", td["type"]["qualType"]), node)
    if name in ENUM_AS_INT:
        return CType("int", 32, False)     # --enum-as-int: an enum with non-negative values, as clang's `unsigned int`
    if tag is not None or re.match(r"^[A-Za-z_][\w:]*$", name):
        raise Reject(node, "type `%s` (not translated: not defined in the translated files, not a --boundary or --param-class)" % sugar)
    raise Reject(node, "type `%s`" % sugar)


CANON_INTS = {"int8_t": "signed char", "uint8_t": "unsigned char", "int16_t": "short", "uint16_t": "unsigned short",
              "int32_t": "int", "uint32_t": "unsigned int", "int64_t": "long long", "uint64_t": "unsigned long long"}


def param_ext_name(name):
    """--param-ext, --front-ends: the registered name of a class template specialization written with
    typedefs or enumerators as its arguments: clang names the specializations of AP_ParamT, AP_ParamV,
    AP_ParamTBase by the values of their `ap_var_type` arguments (`AP_ParamT<float, 4>`), the types and
    bases by the enumerators (`AP_ParamT<float, AP_PARAM_FLOAT>`) and typedefs (`AP_ParamTBase<int8_t,
    1>`, `LowPassFilter2p<Vector3f>`)."""
    name = re.sub(r"\bAP_PARAM_(NONE|INT8|INT16|INT32|FLOAT|VECTOR3F|GROUP)\b", lambda m: str(
        ["NONE", "INT8", "INT16", "INT32", "FLOAT", "VECTOR3F", "GROUP"].index(m.group(1))), name)
    if name in RECORDS or "<" not in name or not name.endswith(">"):
        return name
    base, args = name[:name.index("<")], split_top(name[name.index("<") + 1:-1])
    out = []
    for a in args:
        a = a.strip()
        a = CANON_INTS.get(a, a)
        if re.match(r"^[A-Za-z_]\w*$", a) and a in TYPEDEFS and a not in RECORDS:
            a = norm_template_args(TYPEDEFS[a])
        out.append(param_ext_name(a) if "<" in a else a)
    cand = "%s<%s>" % (base, ", ".join(out))
    if cand not in RECORDS and cand.endswith(">>"):
        cand = cand[:-2] + "> >"
    return cand if cand in RECORDS else name


def world_ptr_type(text):
    """--world-pointers: CType("obj") of a pointer type `C *` (`const C *`, `C *const`) to a translated
    class C (not of a --lib-dir library), else None."""
    m = re.match(r"^(?:const\s+)?(?:class |struct )?([A-Za-z_][\w:<>, ]*?)\s*(?:const\s*)?\*\s*(?:const)?$", text.strip())
    if m is None:
        return None
    name = norm_template_args(m.group(1).strip())
    name = TYPEDEFS.get(name, name) if name not in RECORDS else name
    rec = RECORDS.get(name)
    if rec is None:
        rs = [r for k, r in RECORDS.items() if k.split("::")[-1] == name]
        rec = rs[0] if len(rs) == 1 else None
    if rec is None or (rec.lib and not (FRONT_ENDS[0] and (polymorphic_record(rec) or rec.cxx in WORLD_CLASSES))):
        return None
    return CType("obj", info=rec)


def polymorphic_record(rec, seen=()):
    """--front-ends: does the class have a virtual member function (itself or a base)? A pointer to a
    polymorphic class of a --lib-dir library (the front ends' `AP_Compass_Backend *_backends[]`) is a
    World pointer; pointers to value-like library classes stay what --pointer-params makes them."""
    d = rec.node
    if any(c.get("virtual") for c in kids(d) if c.get("kind") in ("CXXMethodDecl", "CXXDestructorDecl")):
        return True
    for b in d.get("bases", []):
        bt = b["type"]
        name = norm_template_args(strip_tag(bt.get("desugaredQualType", bt["qualType"]))[0])
        br = RECORDS.get(name)
        if br is not None and br.id not in seen and polymorphic_record(br, seen + (rec.id,)):
            return True
    return False


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
    ma = re.match(r"^(.*?) \(?(const )?&\)?((?:\[\d+\])+)$", q) if EKF_ARRAYS[0] else None
    if ma:
        # --ekf-arrays: a reference to an array, `double (&)[4][4]` (clang spells `auto &next = KHP;` `double &[4][4]`)
        base = ma.group(1) + ma.group(3)
        mb = re.match(r"^(.*?) \(?(?:const )?&\)?((?:\[\d+\])+)$", dq)
        based = mb.group(1) + mb.group(2) if mb else base
        is_const = bool(ma.group(2)) or ma.group(1).startswith("const ")
        return parse_type_str(base, based, node), ("const" if is_const else "mut")
    if q.endswith("&") and "*" not in q:
        base_q = q[:-1].strip()
        base_d = dq[:-1].strip() if dq.endswith("&") else dq
        ma = re.match(r"^(.*?) \((?:const )?&\)((?:\[\d+\])+)$", dq) if EKF_ARRAYS[0] else None
        if ma:
            base_d = ma.group(1) + ma.group(2)      # a reference to an array, `double (&)[24][24]`
        is_const = base_q.startswith("const ") or base_q.endswith(" const")
        return parse_type_str(base_q, base_d, node), ("const" if is_const else "mut")
    return parse_type_str(q, dq, node), None


def fn_return_type(fn):
    t = fn["type"]
    if TEXT_RESULTS and CURRENT_UNIT[0] is not None and fn.get("kind") == "CXXMethodDecl":
        try:
            qn = qualified_name(CURRENT_UNIT[0], fn)
        except Exception:
            qn = None
        if qn in TEXT_RESULTS:
            if not re.match(r"^const char ?\*", t["qualType"]):
                raise Reject(fn, "--text-results `%s` that does not return `const char *`" % qn)
            return TEXTBUF      # --text-results (Phase 5d): a text data member or the null pointer (`CText.null`)
    sugar = t["qualType"]
    desug = t.get("desugaredQualType", sugar)
    if sugar.startswith("typename ") and "desugaredQualType" not in t:
        # a template specialization whose return type clang spells only through the template's
        # dependent name (AP_Math's is_equal: `typename std::enable_if<..., bool>::type`): clang
        # has converted every returned expression to the return type, so it is their type
        ret = next((m for m in walk(fn) if m.get("kind") == "ReturnStmt" and kids(m)), None)
        if ret is not None and any(c.get("kind") == "TemplateArgument" for c in kids(fn)):
            return ctype_of(kids(ret)[0])
    if "..." in desug and not C_STRINGS[0]:
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
        elif ord(ch) < 256:
            out.append("\\x%02x" % ord(ch))      # (Phase 5c) Lean's escapes: `\xHH`, `\uHHHH` (`\u{...}` is not Lean)
        else:
            out.append("\\u%04x" % ord(ch))
    return '"%s"' % "".join(out)


def zero_of(t, node):
    """The value of a zero-filled object of type t (ArduPilot zero-fills its objects)."""
    if t.kind == "string" and FRONT_ENDS[0] and node.get("kind") == "FieldDecl":
        # --front-ends: a `const char *` data member that is null until assigned a string (AP_GPS's
        # initblob_state[i].blob, the UART configuration of serial GPS types): the empty string; the
        # translated paths do not read it while it is null (README.md "Phase 3: sensor front ends")
        return V('""', ATOM)
    if t.kind == "string":
        raise Reject(node, "`const char *` without a string literal (its zero value is a null pointer, which is not a string)")
    if t.kind == "textbuf":
        return V('CText.none', ATOM)     # --text-buffers: no text written (a zero-filled buffer: the empty string)
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
    if t.kind == "cstr":
        return V("#[0]", ATOM)          # (never read: a table of string literals has every element)
    if t.kind == "valist":
        return V("({} : VaList)", ATOM)
    if t.kind == "obj":
        return V("WPtr.null", ATOM)     # a zero-filled pointer is null
    if t.kind == "wfun":
        return V("WFun.null", ATOM)     # an empty functor
    raise Reject(node, "no zero value for `%s`" % t.cname)


C_ESCAPES = {"n": 10, "t": 9, "r": 13, "a": 7, "b": 8, "f": 12, "v": 11, "\\": 92, "'": 39, '"': 34, "?": 63, "e": 27}


def string_bytes(n):
    """--c-strings: the bytes of a string literal (clang's `value`, the literal as C spells it, with
    escapes), with its terminating zero, as many as its type `const char[N]` says."""
    v = n.get("value", "")
    if not (v.startswith('"') and v.endswith('"')):
        raise Reject(n, "string literal `%s` that is not a plain narrow literal" % v)
    body = v[1:-1]
    out = []
    i = 0
    while i < len(body):
        ch = body[i]
        if ch != "\\":
            out.extend(ch.encode("utf-8"))
            i += 1
            continue
        e = body[i + 1]
        if e == "x":
            j = i + 2
            while j < len(body) and body[j] in "0123456789abcdefABCDEF":
                j += 1
            out.append(int(body[i + 2:j], 16) & 0xff)
            i = j
        elif e in "01234567":
            j = i + 1
            while j < len(body) and j < i + 4 and body[j] in "01234567":
                j += 1
            out.append(int(body[i + 1:j], 8) & 0xff)
            i = j
        elif e in C_ESCAPES:
            out.append(C_ESCAPES[e])
            i += 2
        else:
            raise Reject(n, "string literal `%s` with the escape `\\%s`" % (v, e))
    out.append(0)
    m = re.match(r"^(?:const )?char ?\[(\d+)\]$", n.get("type", {}).get("qualType", ""))
    if m is None or int(m.group(1)) < len(out) - 1:
        raise Reject(n, "string literal `%s` whose bytes do not match its type `%s`" % (v, n.get("type", {}).get("qualType")))
    # (as the initializer of `char a[N]`, clang gives the literal the array's type: zeros after it)
    return (out + [0] * int(m.group(1)))[:int(m.group(1))]


def bytes_text(bs):
    return "(#[%s] : Array UInt8)" % ", ".join(str(b) for b in bs)


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
    "include", "set_option", "termination_by", "decreasing_by", "fun", "λ", "Σ", "Π", "to", "errors", "matches",
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


# NEG is below SHIFT: Lean's prefix `-` parses its operand at precedence 75, which takes in `<<<` and
# `>>>` (infixl 75), so `-a >>> b` is `-(a >>> b)`; C's `-a >> b` is emitted `(-a) >>> b`
ATOM, APP, NEG, SHIFT, MUL, ADD, BAND, BXOR, BOR, CMP, NOT, AND, OR, LOW = \
    1100, 1000, 74, 75, 70, 65, 60, 58, 55, 50, 40, 35, 30, 0


class V:
    """A translated expression: Lean text and the precedence at which it parses."""

    def __init__(self, text, prec):
        self.text, self.prec = text, prec

    def at(self, need):
        return self.text if self.prec >= need else "(" + self.text + ")"


def app(fn, *args):
    return V(fn + "".join(" " + a.at(ATOM) for a in args), APP)


def lit(text, t):
    if t.kind in ("float", "double"):
        return flit(Fraction(text), t, text)
    if t.name == "char":
        return V("(%d : UInt8)" % (int(text) % 256), ATOM)     # the byte of a `char` value
    return V("(%s : %s)" % (text, t.lean), ATOM)


def flit_bits(bits, t, shown):
    """A floating constant as its bit pattern (`Binary32.ofBits 0x3f800000`), with the C++ value it
    denotes in a comment. A decimal (`(1.5 : Binary32)`, FloatLib's `OfScientific`) would be rounded
    from its rational at every evaluation; the bit pattern costs nothing. The translator computes the
    bits exactly (`round_to_binary`), and the difftest checks each registered literal's decimal or
    conversion in compiled Lean against them (README.md, "Mapping")."""
    width = 8 if t.kind == "float" else 16
    return V("(%s.ofBits 0x%0*x /- %s -/)" % (t.lean, width, bits, comment_safe(shown)), ATOM)


def flit(fr, t, shown):
    return flit_bits(float_bits(fr, t), t, shown)


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
    # std::numeric_limits<T>::signaling_NaN() (AP_Math's fill_nanf): quiet bit clear, the next payload bit set
    "__builtin_nansf": ("float", 0x7fa00000), "__builtin_nans": ("double", 0x7ff4000000000000),
}


# ---------------------------------------------------------------------------------------------
# <cmath>: (name, parameter types, result type) -> Lean function. The float overloads without the
# f suffix are libc++'s std:: overloads, which compute the same function (__builtin_sinf, ...).
# The functions IEEE 754 defines exactly are FloatLib operations (CFloat.lean); the others are the
# translation of musl's C sources (LIBM_NS: README.md, "The C library").

def _sig(ps, r):
    return (tuple(ps), r)


LIBM_NS = "Musl"    # the translation of musl's C sources: function f of musl's f.c is Musl.f.f (module Musl.f)


def libm_fn(name):
    return "%s.%s.%s" % (LIBM_NS, name, name)

F, D = "float", "double"
CMATH = {}
for base, lf in [("sqrt", "sqrt"), ("fabs", "abs"), ("floor", "floor"), ("ceil", "ceil"), ("trunc", "trunc"),
                 ("round", "round")]:
    CMATH[(base + "f",) + _sig([F], F)] = "Binary32." + lf
    CMATH[(base,) + _sig([F], F)] = "Binary32." + lf
    CMATH[(base,) + _sig([D], D)] = "Binary64." + lf
CMATH[("abs",) + _sig([F], F)] = "Binary32.abs"
CMATH[("abs",) + _sig([D], D)] = "Binary64.abs"
for base in ["fmax", "fmin", "copysign"]:
    CMATH[(base + "f",) + _sig([F, F], F)] = "Binary32." + base
    CMATH[(base,) + _sig([F, F], F)] = "Binary32." + base
    CMATH[(base,) + _sig([D, D], D)] = "Binary64." + base
for base in ["scalbn", "ldexp"]:
    CMATH[(base + "f",) + _sig([F, "int32_t"], F)] = "Binary32.scalbn"
    CMATH[(base,) + _sig([F, "int32_t"], F)] = "Binary32.scalbn"
    CMATH[(base,) + _sig([D, "int32_t"], D)] = "Binary64.scalbn"
LIBM = ["sin", "cos", "tan", "asin", "acos", "atan", "exp", "log", "log2"]
LIBM2 = ["atan2", "pow", "fmod"]
for base in LIBM:
    CMATH[(base + "f",) + _sig([F], F)] = libm_fn(base + "f")
    CMATH[(base,) + _sig([F], F)] = libm_fn(base + "f")
    CMATH[(base,) + _sig([D], D)] = libm_fn(base)
for base in LIBM2:
    CMATH[(base + "f",) + _sig([F, F], F)] = libm_fn(base + "f")
    CMATH[(base,) + _sig([F, F], F)] = libm_fn(base + "f")
    CMATH[(base,) + _sig([D, D], D)] = libm_fn(base)
# libc++'s overloads of the two-argument functions for mixed float/double arguments
# (`fmod(double, float)`, ArduPilot's `fmod(angle, 360.0)` under -cl-single-precision-constant):
# both arguments are converted to double (exact) and the double function is called.
for base in ["atan2", "pow", "fmod", "fmax", "fmin", "copysign"]:
    lf = libm_fn(base) if base in LIBM2 else "Binary64." + base
    for ps in ([D, F], [F, D]):
        CMATH[(base,) + _sig(ps, D)] = (lf, "double")
for base in LIBM2:
    # libc++'s overload for integer arguments: both converted to double (exactly, for 32-bit integers)
    CMATH[(base,) + _sig(["int32_t", "int32_t"], D)] = (libm_fn(base), "double")
for base, lf in [("isnan", "isNaN"), ("isinf", "isInf"), ("isfinite", "isFinite")]:
    CMATH[(base,) + _sig([F], "bool")] = "Binary32." + lf
    CMATH[(base,) + _sig([D], "bool")] = "Binary64." + lf

COMPARISON_MACROS = {"isgreater": ">", "isgreaterequal": "≥", "isless": "<", "islessequal": "≤"}
# clang's classification builtins (C: int-valued), as libm/env/math.h defines isnan and signbit
BUILTIN_PREDICATES = {"__builtin_isnan": "isNaN", "__builtin_isinf": "isInf", "__builtin_isfinite": "isFinite",
                      "__builtin_signbit": "signbit"}

SUPPORT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "support")


# ---------------------------------------------------------------------------------------------
# Conversions: every cast node becomes the named Lean conversion.

def int_conv(v, s, d):
    """C++ integral conversion s -> d (both integer types, d != s): the value modulo 2^bits(d),
    as Lean's width conversions compute it (sign extension from a signed source, zero extension
    from an unsigned one, truncation when narrowing)."""
    if s.name == "char" or d.name == "char":
        # --c-strings: a `char` is its byte; as a value it is a signed char (sign extension on promotion)
        if {s.name, d.name} == {"char", None} and (s if d.name == "char" else d) == UINT8:
            return v                            # char <-> unsigned char: the same byte
        if s.name == "char":
            v, s = app("UInt8.toInt8", v), INT8
            if d == INT8:
                return v
        if d.name == "char":
            return app("Int8.toUInt8", int_conv(v, s, INT8) if s != INT8 else v)
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
        return app("Binary32.toBinary64", v)
    if s.kind == "double" and d.kind == "float":
        return app("Binary64.toBinary32", v)
    if s.is_int() and d.is_float():
        src = "USize" if s.usize else ("Int" if s.signed else "UInt") + str(s.bits)
        return app("%s.to%s" % (src, d.lean), v)
    if MISSION[0] and s.is_float() and d.is_int() and not d.usize and d.bits < 32:
        # --mission: to an 8- or 16-bit integer, what clang emits for the reference target (arm64): `fcvtzs w`, the
        # value truncated toward zero and saturated to int32 (NaN: 0), then its low bits (out of range: undefined in C;
        # `(uint8_t)-221.0f` is 35, not CFloat's saturation to the narrow range)
        return int_conv(app("%s.toInt32" % s.lean, v), CType("int", 32, True), d)
    if s.is_float() and d.is_int():
        return app("%s.to%s" % (s.lean, d.lean), v)
    if s.is_int() and d.is_int():
        return int_conv(v, s, d)
    raise Reject(node, "conversion from `%s` to `%s`" % (s.cname, d.cname))


FORMAT = {"float": (24, -126, 127), "double": (53, -1022, 1023)}


def const_number(n):
    """The exact value of a numeric constant expression (an integer or floating literal, negated or
    converted by clang's implicit casts), as C evaluates it, or None. Used to compute conversions of
    constants once, at translation time."""
    n = strip_parens(n)
    k = n.get("kind")
    t = ctype_of(n) if n.get("type") else None
    if k == "IntegerLiteral":
        return Fraction(int(n["value"]))
    if k == "FloatingLiteral" and t is not None and t.kind in FORMAT:
        val, _ = parse_c_float(n["value"])
        return None if val is None else round_to_binary(val, *FORMAT[t.kind])
    if k == "UnaryOperator" and n.get("opcode") == "-" and t is not None and (t.is_float() or (t.is_int() and t.signed)):
        v = const_number(kids(n)[0])
        return None if v is None or v == 0 else -v
    if k == "BinaryOperator" and n.get("opcode") in ("+", "-", "*", "/") and t is not None:
        a, b = (const_number(x) for x in kids(n))
        if a is None or b is None:
            return None
        op = n["opcode"]
        if op == "/" and b == 0:
            return None
        r = a + b if op == "+" else a - b if op == "-" else a * b if op == "*" else None
        if t.kind in FORMAT:
            # one IEEE operation on two values of the type: the exact result rounded once; a zero
            # result might be -0 (x - x is +0, but a product with a negative factor is not): not folded
            r = a / b if op == "/" else r
            return None if r == 0 else round_to_binary(r, *FORMAT[t.kind])
        if t.is_int() and t.signed and op != "/":
            lo, hi = -(1 << (t.bits - 1)), (1 << (t.bits - 1)) - 1
            return r if lo <= r <= hi else None     # no wrapping: signed overflow is not folded
        return None
    if k == "ImplicitCastExpr" and t is not None:
        ck = n.get("castKind")
        v = const_number(kids(n)[0])
        if v is None:
            return None
        if ck in ("NoOp", "LValueToRValue"):
            return v
        if ck == "IntegralCast" and t.is_int() and v.denominator == 1:
            lo, hi = (-(1 << (t.bits - 1)), (1 << (t.bits - 1)) - 1) if t.signed else (0, (1 << t.bits) - 1)
            return v if lo <= v <= hi else None
        if ck in ("FloatingCast", "IntegralToFloating") and t.kind in FORMAT:
            return round_to_binary(v, *FORMAT[t.kind])
    return None


CAST_KINDS = {"FloatingCast", "IntegralCast", "IntegralToFloating", "FloatingToIntegral",
              "IntegralToBoolean", "FloatingToBoolean", "NoOp", "LValueToRValue"}


# ---------------------------------------------------------------------------------------------
# AST helpers.

def kids(n):
    return n.get("inner", [])


def non_attr(ns):
    """The nodes that are not attributes (clang lists `VisibilityAttr`, ... among a declaration's children)."""
    return [c for c in ns if not c.get("kind", "").endswith("Attr")]


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
                  "*=": "mul_assign", "/=": "div_assign", "%=": "mod_assign", "[]": "index", "^": "xor", "=": "assign",
                  "&": "and", "|": "or", "!": "not"}


def operator_word(name):
    """The Lean name part of an overloaded operator (`operator*` is `op_mul`), or None."""
    if not name or not name.startswith("operator"):
        return None
    sym = name[len("operator"):].strip()
    if FRONT_ENDS[0] and sym in ("++", "--"):
        return "op_inc" if sym == "++" else "op_dec"       # --front-ends: typesafe_index (AP_Common/TSIndex.h)
    if FRONT_ENDS[0] and sym and (sym[0].isalpha() or sym[0] == "_") and sym not in ("new", "delete"):
        # --front-ends: a conversion function (`operator const float &`): `op_to_float`
        return "op_to_" + re.sub(r"\W+", "_", re.sub(r"\bconst\b|&", "", sym)).strip("_")
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
            if kind == "b":
                out = bits_view(V(out, ATOM), x).text
                continue
            if kind == "v":
                out = "({ %s } : %s)" % (", ".join("%s := %s.%s" % (th, out, mi) for th, mi in x[0]), x[1])
            elif kind == "bit":
                out = "(%s >>> %d &&& 1 != 0)" % (out, x[0])
            elif kind == "bitf":
                off, w, wt, ft = x
                raw = V("((%s >>> %d) &&& %d)" % (out, off, (1 << w) - 1), ATOM)
                if ft.kind == "enum":
                    out = "(%s.ofInt %s)" % (ft.info.lean, int_conv(raw, wt, ft.info.under).at(ATOM))
                else:
                    out = int_conv(raw, wt, ft).at(ATOM)
            elif kind == "av":
                out = av_value(out, x[0], x[1])
            elif kind == "opt":
                out = "(%s.getD default)" % out     # --mavlink: the object a non-null `const T *` points to
            elif kind == "ub":
                out = ub_read(out, x)               # --mission: a member of a byte union (its bytes at an offset)
            elif kind == "ubf":
                out = ubf_read(out, x)              # --mission: a bit-field viewed in a byte union's bytes
            elif kind == "fi":
                out = "(match %s with %s)" % (x[0].text, " ".join("| %s => %s.%s" % (str(j) if j < len(x[1]) - 1 else "_", out, f)
                                                                for j, f in enumerate(x[1])))
            elif kind == "fm":
                # --member-pointers: the member object a tag designates (the last one for any other tag: undefined in C++);
                # typed, since Lean's `do` elaborator fails on a `match` term whose type it has to infer after a `do` `match`
                out = "((match %s with %s) : %s)" % (x[0].text, " ".join("| %s => %s.%s" % ("." + c if j < len(x[1]) - 1 else "_", out, f)
                                                                       for j, (c, f) in enumerate(x[1])), x[2])
            else:
                out += ("." + x) if kind == "f" else ("[%s]!" % x.text)
        return out

    def extend(self, step, t):
        if self.steps and self.steps[-1][0] == "av" and step[0] == "v" and REACHABLE[0]:
            # --reachable: a layout-prefix view (`xy()`) of a struct view of an array (`stateStruct.position.xy()`,
            # AP_NavEKF3_PosVelFusion.cpp:42): the struct view of the same first elements
            st, b = self.steps[-1][1]
            lv = [(tuple(ls), lt.key()) for _, ls, lt in type_leaves(t, None)]
            if [x for x, _ in step[1][0]] != [f.lean for f in t.info.all_fields() if f.category == "state"] or \
                    any(dict(step[1][0])[f] != f for f in dict(step[1][0])):
                raise AssertionError("view of a struct view that is not a prefix of the same fields")
            return Path(self.root, self.root_text, self.steps[:-1] + [("av", (t, b))], t)
        if self.steps and self.steps[-1][0] == "av":
            # --ekf-types: a member of the struct view of an array (`stateStruct.velocity.y` is
            # `statesArray[5]`): its first element, an element if it is a scalar, else a view again
            st, b = self.steps[-1][1]
            if step[0] == "f":
                k = av_leaf_index(st, [step], None)
            elif step[0] == "fi":
                k0 = av_leaf_index(st, [("f", step[1][1][0])], None)
                if any(av_leaf_index(st, [("f", f)], None) != k0 + j for j, f in enumerate(step[1][1])):
                    raise AssertionError("runtime index over members that are not consecutive elements")
                idx = Body.md_add(V(str(b + k0), ATOM), step[1][0])
                return Path(self.root, self.root_text, self.steps[:-1] + [("i", idx)], t)
            else:
                raise AssertionError("step %r of an array view" % (step,))
            if t.is_scalar():
                return Path(self.root, self.root_text, self.steps[:-1] + [("i", V(str(b + k), ATOM))], t)
            return Path(self.root, self.root_text, self.steps[:-1] + [("av", (t, b + k))], t)
        if self.steps and self.steps[-1][0] == "v" and step[0] == "f":
            # a field of the view (`v.xy().x`) is the viewed field of the object
            mine = dict(self.steps[-1][1][0])[step[1]]
            return Path(self.root, self.root_text, self.steps[:-1] + [("f", mine)], t)
        return Path(self.root, self.root_text, self.steps + [step], t)


SIMPLE = re.compile(r"^[\w'.«»]+$")


class PtrVar:
    """--pointer-params: a pointer parameter or local into an array of the model: the array (a
    Path), the Lean name of its offset (a `Nat` variable) if the pointer moves, the element type, and
    its kind (`param`, `alias`: a local pointer into another array, `owned`: a local array)."""

    def __init__(self, base, off, elem, kind):
        self.base, self.off, self.elem, self.kind = base, off, elem, kind


class Splice:
    """--pointer-params: a slice `a + k` passed to a pointer parameter that the callee writes: after
    the call, the elements from offset `off` on are the callee's array."""

    def __init__(self, base, off):
        self.base, self.off = base, off


def object_pointer_params(d):
    """--c-strings: the parameters `C *p` of function d with C a class (not a number, `void` or `char`)."""
    out = []
    for p in kids(d):
        if p.get("kind") != "ParmVarDecl":
            continue
        q = p.get("type", {}).get("desugaredQualType", p.get("type", {}).get("qualType", "")).strip()
        m = re.match(r"^(?:class |struct )?([\w:<>, ]+?) ?\*$", q)
        if m and m.group(1) not in INT_TYPES and m.group(1) not in ("void", "char", "float", "double", "bool") and \
                (m.group(1) in RECORDS or m.group(1).split("::")[-1] in [k.split("::")[-1] for k, r in RECORDS.items() if r.kind == "class"]):
            out.append(p)
    return out


def pp_ret_param(d):
    """--c-strings: for a function returning `T *` each of whose `return`s returns one pointer
    parameter (possibly moved: `return s;` after `*s++ = ...`, utoa_invert.cpp), the index of that
    parameter; the Lean function returns the pointer's offset (`Nat`) into the array it is passed."""
    if not C_STRINGS[0]:
        return None
    q = d.get("type", {}).get("desugaredQualType", d.get("type", {}).get("qualType", "")).split("(")[0].strip()
    if not re.match(r"^(const )?[\w:<>, ]+? ?\*$", q):
        return None
    body = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
    ps = [p for p in kids(d) if p.get("kind") == "ParmVarDecl"]
    rets = [r for r in walk(body or {}) if r.get("kind") == "ReturnStmt"]
    found = set()
    for r in rets:
        e = strip_object(kids(r)[0]) if kids(r) else {}
        if e.get("kind") != "DeclRefExpr":
            return None
        idx = next((i for i, p in enumerate(ps) if p["id"] == e["referencedDecl"]["id"]), None)
        if idx is None:
            return None
        found.add(idx)
    return found.pop() if len(found) == 1 else None


def pp_fresh_return(u, d):
    """--pointer-params: for a function returning `T *` (T a number type) each of whose `return`s
    returns a local pointer initialized with `new T[k]` and never assigned again: the array type it
    returns (the caller's local pointer holds the array), else None."""
    q = d.get("type", {}).get("desugaredQualType", d.get("type", {}).get("qualType", "")).split("(")[0].strip()
    m = re.match(r"^([\w:<>, ]+?) ?\*$", q)
    if not m:
        return None
    try:
        et = parse_type_str(m.group(1), m.group(1), d)
    except Reject:
        return None
    if et.kind not in ("float", "double", "int"):
        return None
    body = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
    if body is None:
        return None
    rets = [r for r in walk(body) if r.get("kind") == "ReturnStmt"]
    if not rets:
        return None
    for r in rets:
        e = strip_object(kids(r)[0]) if kids(r) else {}
        if e.get("kind") != "DeclRefExpr":
            return None
        v = u.decl(e["referencedDecl"]["id"])
        init = strip_parens(kids(v)[0]) if v is not None and kids(v) else {}
        while init.get("kind") == "ImplicitCastExpr" and init.get("castKind") in ("NoOp", "BitCast"):
            init = strip_parens(kids(init)[0])
        if init.get("kind") != "CXXNewExpr":
            return None
        for m2 in walk(body):
            if m2.get("kind") == "BinaryOperator" and m2.get("opcode") == "=" and \
                    strip_object(kids(m2)[0]).get("referencedDecl", {}).get("id") == v["id"]:
                return None
    t = CType("array", elem=et, n=0)
    t.fresh = True
    return t


class UnionInfo:
    """A C union all of whose members are numbers of one width (musl's `union {float f; uint32_t i;}`):
    the variable holds the bit pattern, an unsigned integer of that width (`word`); a member is a view
    of it (README.md, "The C library")."""

    def __init__(self, word, members):
        self.word, self.members = word, members     # members: field id -> (name, CType)


def bits_view(v, t):
    """The member of type t of a union whose bit pattern is v (a word of t's width)."""
    if t.kind == "float":
        return app("Binary32.ofBits", v)
    if t.kind == "double":
        return app("Binary64.ofBits", v)
    return int_conv(v, CType("int", t.bits, False), t)


def bits_of(v, t):
    """The bit pattern (an unsigned word of t's width) of the value v of type t."""
    if t.kind == "float":
        return app("Binary32.toBits", v)
    if t.kind == "double":
        return app("Binary64.toBits", v)
    return int_conv(v, t, CType("int", t.bits, False))


# --c-strings: the C string runtime (support/CString.lean): argument kinds (w: destination pointer,
# r: source pointer, n: a size_t count, i: an int) and the result
CS_FUNCTIONS = {
    "strlen": (("r",), "size_t"), "strnlen": (("r", "n"), "size_t"), "strncpy": (("w", "r", "n"), None),
    "strcmp": (("r", "r"), "int"), "strncmp": (("r", "r", "n"), "int"), "strcasecmp": (("r", "r"), "int"),
    "strncasecmp": (("r", "r", "n"), "int"), "memcpy": (("w", "r", "n"), None), "memset": (("w", "i", "n"), None),
    "memcmp": (("r", "r", "n"), "int"),
}


# ---------------------------------------------------------------------------------------------
# Byte-level objects (--byte-objects, --c-strings; README.md "Phase 2b", PORT-PLAN.md 4.5, F5).
# The object representation of a value of the model is computed from its type: the record layout
# rules of the target's ABI (AAPCS64 and SysV x86-64 agree on these: each scalar aligned to its
# size, a struct aligned to its most aligned member and padded to a multiple of that, members in
# declaration order, bases first; `__attribute__((packed))`: alignment 1), little endian, a float as
# its bit pattern. A layout is a list of leaves (byte offset, path of fields and indices, scalar
# type); padding bytes are zeros when an object is written to bytes (C leaves them unspecified).

def byte_size_align(t, node):
    """(size, alignment) in bytes of an object of type t on the reference target."""
    if t.kind == "int":
        b = 8 if t.usize else t.bits // 8
        return b, b
    if t.kind == "float":
        return 4, 4
    if t.kind == "double":
        return 8, 8
    if t.kind == "bool":
        return 1, 1
    if t.kind == "enum":
        return byte_size_align(t.info.under, node)
    if t.kind == "array":
        if t.n <= 0:
            raise Reject(node, "size of an array of unknown length")
        sz, al = byte_size_align(t.elem, node)
        return sz * t.n, al
    if t.kind == "record":
        lay = record_layout(t.info, node)
        return lay[1], lay[2]
    raise Reject(node, "object representation of `%s`" % t.cname)


def record_layout(rec, node):
    """(leaves, size, alignment) of a translated plain struct or class: leaves are (offset, steps,
    scalar CType) with steps a list of ('f', lean field) / ('i', index). Rejected: virtual functions
    (a vtable pointer), bit-fields other than `bool : 1` handled as bytes, members outside the model."""
    cache = getattr(rec, "byte_layout", None)
    if cache is not None:
        return cache
    packed = any(c.get("kind") == "PackedAttr" for c in kids(rec.node))
    if any(m.get("virtual") for m in walk(rec.node) if m.get("kind") == "CXXMethodDecl"):
        raise Reject(node, "object representation of `%s`, which has virtual functions (a vtable pointer)" % rec.cxx)
    if MAVLINK[0]:
        return mav_record_layout(rec, node, packed)
    leaves, off, align = [], 0, 1
    for f in rec.all_fields():
        if f.decl.get("isBitfield"):
            raise Reject(f.decl, "object representation of a bit-field `%s`" % f.name)
        if f.category != "state":
            raise Reject(f.decl, "object representation of member `%s`, which is not state of the model" % f.name)
        sz, al = byte_size_align(f.t, f.decl)
        al = 1 if packed else al
        off = (off + al - 1) // al * al
        for lo, steps, lt in type_leaves(f.t, f.decl):
            leaves.append((off + lo, [("f", f.lean)] + steps, lt))
        off += sz
        align = max(align, al)
    size = (off + align - 1) // align * align
    rec.byte_layout = (leaves, size, align)
    return rec.byte_layout


def bitfield_width(c):
    """The width of bit-field declaration c (clang's ConstantExpr), else None."""
    if not c.get("isBitfield"):
        return None
    return next((int(x["value"]) for x in kids(c) if x.get("kind") == "ConstantExpr" and "value" in x), None)


def mav_record_layout(rec, node, packed):
    """--mavlink: record_layout with bit-fields (the Itanium C++ ABI of the reference targets, AAPCS64 and
    x86-64: a bit-field of declared type T and width w at the next bit, unless the struct is not packed and
    it would cross a boundary of an aligned unit of T, then at the next such unit; a non-bit-field member at
    the next byte its alignment allows). Leaves of bit-fields are ('bits', bit offset, width) entries in
    rec.bit_leaves; rec.field_layout lists (C++ member, byte offset or bit offset, size or width, is bit-field)
    for the cross-check against clang (ardupilot/check_layouts.py)."""
    if getattr(rec, "dropped", None) or len(rec.fields) != sum(1 for c in kids(rec.node) if c.get("kind") == "FieldDecl"):
        raise Reject(node, "object representation of `%s`, which has members outside the model" % rec.cxx)
    leaves, bits, flay, bit, align = [], [], [], 0, 1
    for f in rec.all_fields():
        if f.category != "state":
            raise Reject(f.decl, "object representation of member `%s`, which is not state of the model" % f.name)
        sz, al = byte_size_align(f.t, f.decl)
        al = 1 if packed else al
        w = bitfield_width(f.decl)
        if w is not None:
            unit = sz * 8
            if not packed and bit // unit != (bit + w - 1) // unit:
                bit = (bit + unit - 1) // unit * unit
            bits.append((bit, [("f", f.lean)], f.t, w))
            flay.append((f.name, bit, w, True))
            bit += w
            align = max(align, al)
            continue
        off = (bit + 7) // 8
        off = (off + al - 1) // al * al
        for lo, steps, lt in type_leaves(f.t, f.decl):
            leaves.append((off + lo, [("f", f.lean)] + steps, lt))
        flay.append((f.name, off, sz, False))
        bit = (off + sz) * 8
        align = max(align, al)
    off = (bit + 7) // 8
    size = (off + align - 1) // align * align
    rec.bit_leaves = bits
    rec.field_layout = flay
    rec.byte_layout = (leaves, size, align)
    if bits:
        rec.byte_layout = (leaves, size, align)
    return rec.byte_layout


def byte_runs(leaves):
    """--mavlink: leaves with each run of the elements of one member array of bytes (`char text[50]`) as one
    leaf (offset, steps of the array, "bytes")."""
    out = []
    for lo, steps, lt in leaves:
        if lt in (UINT8, CHAR, INT8) and lt != INT8 and steps and steps[-1][0] == "i":
            head = steps[:-1]
            if out and out[-1][2] == "bytes" and out[-1][1] == head:
                continue
            if steps[-1][1] == 0:
                out.append((lo, head, "bytes"))
                continue
        out.append((lo, steps, lt))
    return out


def bit_leaves(t, node):
    """--mavlink: the bit-field leaves of an object of type t: (bit offset, steps, CType, width)."""
    if t.kind == "array":
        sz, _ = byte_size_align(t.elem, node)
        return [(8 * i * sz + b, [("i", i)] + st, lt, w) for i in range(t.n) for b, st, lt, w in bit_leaves(t.elem, node)]
    if t.kind == "record":
        record_layout(t.info, node)
        out = list(getattr(t.info, "bit_leaves", []))
        for lo, steps, lt in []:
            pass
        for f in t.info.all_fields():
            if f.t.kind in ("record", "array") and f.category == "state":
                sub = [x for x in t.info.field_layout if x[0] == f.name] if hasattr(t.info, "field_layout") else []
                if sub:
                    out += [(8 * sub[0][1] + b, [("f", f.lean)] + st, lt, w) for b, st, lt, w in bit_leaves(f.t, node)]
        return out
    return []


def type_leaves(t, node):
    """The scalar leaves of an object of type t: (offset, steps, scalar CType)."""
    if t.kind == "array":
        sz, _ = byte_size_align(t.elem, node)
        return [(i * sz + lo, [("i", i)] + st, lt) for i in range(t.n) for lo, st, lt in type_leaves(t.elem, node)]
    if t.kind == "record":
        return record_layout(t.info, node)[0]
    byte_size_align(t, node)
    return [(0, [], t)]


def leaf_text(base, steps):
    out = base
    for k, x in steps:
        out = "%s.%s" % (out, x) if k == "f" else "%s[%d]!" % (out if out.endswith("!") is False else "(%s)" % out, x)
    return out


def scalar_to_bytes(v, t):
    """Lean text of the bytes (Array UInt8) of the scalar value v (text, atom) of type t."""
    if t.kind == "bool":
        return "#[if %s then 1 else 0]" % v
    if t.kind == "enum":
        return scalar_to_bytes("(%s.toInt %s)" % (t.info.lean, v), t.info.under)
    if t.kind == "float":
        return "CString.ofUInt32 (Binary32.toBits %s)" % v
    if t.kind == "double":
        return "CString.ofUInt64 (Binary64.toBits %s)" % v
    b = 64 if t.usize else t.bits
    w = int_conv(V(v, ATOM), t, CType("int", b, False)).at(ATOM)
    return "#[%s]" % w if b == 8 else "CString.ofUInt%d %s" % (b, w)


def scalar_from_bytes(a, off, t):
    """Lean text of the scalar of type t stored in the bytes of array a (text, atom) at offset off (text)."""
    if t.kind == "bool":
        return "(CString.get %s %s != 0)" % (a, off)
    if t.kind == "enum":
        t.info.used_ofInt = True
        return "(%s.ofInt %s)" % (t.info.lean, scalar_from_bytes(a, off, t.info.under))
    if t.kind == "float":
        return "(Binary32.ofBits (CString.toUInt32 %s %s))" % (a, off)
    if t.kind == "double":
        return "(Binary64.ofBits (CString.toUInt64 %s %s))" % (a, off)
    b = 64 if t.usize else t.bits
    raw = "(CString.get %s %s)" % (a, off) if b == 8 else "(CString.toUInt%d %s %s)" % (b, a, off)
    return "(%s)" % int_conv(V(raw, ATOM), CType("int", b, False), t).text


def value_to_bytes(v, t, node):
    """Lean text of the object representation (Array UInt8 of sizeof(t) bytes) of value v (text) of type t."""
    if MAVLINK[0] and t.kind == "array" and t.n == 0 and t.elem.is_scalar():
        # --mavlink: the elements of an array of unknown length (a pointer parameter): each one's bytes, in order
        return "((%s).foldl (fun a' x' => a' ++ %s) (#[] : Array UInt8))" % (v, scalar_to_bytes("x'", t.elem))
    size, _ = byte_size_align(t, node)
    leaves = type_leaves(t, node)
    if len(leaves) == 1 and leaves[0][0] == 0 and not leaves[0][1]:
        return scalar_to_bytes(v if SIMPLE.match(v) else "(%s)" % v, t)
    parts = ["(Array.replicate %d (0 : UInt8))" % size]
    out = parts[0]
    if MAVLINK[0]:
        # --mavlink: a member array of bytes is written whole (one `CString.write` of the array)
        leaves = byte_runs(leaves)
    for lo, steps, lt in leaves:
        if lt == "bytes":
            out = "CString.write %s %d (%s)" % ("(%s)" % out if " " in out else out, lo, leaf_text("(%s)" % v if not SIMPLE.match(v) else v, steps))
            continue
        out = "CString.write %s %d (%s)" % ("(%s)" % out if " " in out else out, lo, scalar_to_bytes(leaf_text("(%s)" % v if not SIMPLE.match(v) else v, steps), lt))
    for bit, steps, lt, w in bit_leaves(t, node):
        # --mavlink: a bit-field, w bits from bit `bit` (least significant first): ORed into the bytes it spans
        x = "(%s).toUInt64" % leaf_text("(%s)" % v if not SIMPLE.match(v) else v, steps)
        for k in range(bit // 8, (bit + w - 1) // 8 + 1):
            lo_b = max(bit, 8 * k)
            sh = lo_b - bit                 # the value's bits from sh go to byte k from bit lo_b - 8k
            nb = min(bit + w, 8 * k + 8) - lo_b
            piece = "((((%s >>> %d) &&& %d).toUInt8) <<< %d)" % (x, sh, (1 << nb) - 1, lo_b - 8 * k)
            out = "(let a' := %s; CString.put a' %d (CString.get a' %d ||| %s))" % (out, k, k, piece)
    return out


def value_from_bytes(a, off, t, node):
    """Lean text of the value of type t whose object representation is in array a (text) from offset off (text)."""
    if MAVLINK[0] and t.kind == "array" and t.n == 0 and t.elem.is_scalar():
        sz, _ = byte_size_align(t.elem, node)
        return "(Array.ofFn (n := (%s.size - %s) / %d) fun i' => %s)" % (a, off, sz, scalar_from_bytes(a, "(%s + i'.val * %d)" % (off, sz), t.elem))
    leaves = type_leaves(t, node)
    if len(leaves) == 1 and not leaves[0][1]:
        return scalar_from_bytes(a, off, t)
    def build(tt, steps_done, base_off):
        if tt.kind == "record":
            lay = record_layout(tt.info, node)[0]
            fs = [f for f in tt.info.all_fields()]
            items = []
            bits = {st[0][1]: (b, w) for b, st, _, w in getattr(tt.info, "bit_leaves", [])}
            for f in fs:
                if f.lean in bits:
                    # --mavlink: a bit-field: w bits from bit b (the 8 bytes from its first byte hold them)
                    b, w = bits[f.lean]
                    raw = "((CString.toUInt64 %s (%s + %d) >>> %d) &&& %d)" % (a, base_off, b // 8, b % 8, (1 << w) - 1)
                    items.append("%s := %s" % (f.lean, int_conv(V(raw, ATOM), CType("int", 64, False), f.t).text))
                    continue
                fl = [x for x in lay if x[1][0] == ("f", f.lean)]
                sub_off = min(x[0] for x in fl)
                items.append("%s := %s" % (f.lean, build(f.t, None, "%s + %d" % (base_off, sub_off))))
            return "({ %s } : %s)" % (", ".join(items), tt.lean)
        if tt.kind == "array":
            sz, _ = byte_size_align(tt.elem, node)
            if MAVLINK[0] and tt.elem in (UINT8, CHAR):
                return "(CString.slice %s (%s) %d)" % (a, base_off, tt.n)     # --mavlink: a member array of bytes
            return "#[%s]" % ", ".join(build(tt.elem, None, "%s + %d" % (base_off, i * sz)) for i in range(tt.n))
        return scalar_from_bytes(a, "(%s)" % base_off, tt)
    return build(t, None, off)


def held_member_type(c):
    """--c-strings: the type of a data member `T *const p` (T a number type), which the object holds
    as the array it points into (`Array T`, offset 0): `char *const _str` of AP_HAL's BufferPrinter.
    The member is never reseated (`const`); its constructor binds it to a pointer parameter, and
    an object of the class is a local variable constructed from a pointer variable of the function,
    which is the object's array again after each use of the object (Body.held). Else None."""
    if not C_STRINGS[0]:
        return None
    q = c.get("type", {}).get("desugaredQualType", c.get("type", {}).get("qualType", "")).strip()
    m = re.match(r"^(const )?([\w:<>, ]+?) ?\* ?const$", q)
    if not m:
        return None
    try:
        et = parse_type_str(m.group(2), m.group(2), c)
    except Reject:
        return None
    if et.kind not in ("int", "float", "double"):
        return None
    t = CType("array", elem=et, n=0)
    t.held = True
    return t


def same_storage(a, b):
    """Do arrays of element types a and b have the same Lean storage? (--c-strings: `char` and
    `unsigned char`/`uint8_t` are both bytes; a cast between their pointers is no conversion.)"""
    if a == b:
        return True
    return C_STRINGS[0] and a in (CHAR, UINT8) and b in (CHAR, UINT8)


def union_info(rec, node):
    """The UnionInfo of a union RecordDecl, or a rejection if its members are not numbers of one width."""
    members = {}
    width = None
    for f in kids(rec):
        if f.get("isImplicit") or f.get("kind") in ("FullComment",):
            continue                    # (C++: the implicit constructors and the injected class name)
        if f.get("kind") != "FieldDecl":
            raise Reject(f, "union member `%s`" % f.get("kind"))
        t = ctype_of(f)
        if t.kind not in ("float", "double", "int") or (t.kind == "int" and t.usize):
            raise Reject(f, "union member of type `%s` (only numbers of one width: a float and its bit pattern)" % t.cname)
        b = 32 if t.kind == "float" else 64 if t.kind == "double" else t.bits
        if width is not None and b != width:
            raise Reject(f, "union members of different widths")
        width = b
        members[f["id"]] = (f.get("name"), t)
    if width not in (32, 64):
        raise Reject(node, "union whose members are not 32 or 64 bits wide")
    return UnionInfo(CType("int", width, False), members)


def update_text(base, steps, value):
    """Lean text of `base` with the element at `steps` replaced by `value` (a V): nested fields
    with `{ b with f.g := v }`, array elements with `Array.set!`."""
    if not steps:
        return value.text
    if steps[-1][0] == "b":
        # a write of a union member: the union's bit pattern becomes the value's
        return update_text(base, steps[:-1], bits_of(value, steps[-1][1]))
    if steps[-1][0] == "av":
        # --ekf-types: the struct view of an array assigned: each element from its member
        arr = Path(None, base, steps[:-1], None).text()
        st, b = steps[-1][1]
        val = value.text if SIMPLE.match(value.text) else "(%s)" % value.text
        out = arr if SIMPLE.match(arr) else "(%s)" % arr
        for k, (off, lsteps, lt) in enumerate(type_leaves(st, None)):
            out = "(%s.set! %d %s)" % (out, b + k, leaf_text(val, lsteps))
        return update_text(base, steps[:-1], V(out, ATOM))
    if steps[-1][0] in ("ub", "ubf"):
        # --mission: a member of a byte union: its bytes written at its offset (a bit-field: the bytes it spans,
        # read, cleared and ORed with the value's low w bits)
        cur = Path(None, base, steps[:-1], None).text()
        return update_text(base, steps[:-1], V(ub_write(cur, steps[-1], value), APP))
    if steps[-1][0] == "bitf":
        # --front-ends: a field of w bits at bit off of a bit union: cleared, then the value's low w bits
        cur = Path(None, base, steps[:-1], None).text()
        off, w, wt, ft = steps[-1][1]
        v = V("(%s.toInt %s)" % (ft.info.lean, value.at(ATOM)), ATOM) if ft.kind == "enum" else value
        vw = int_conv(v, ft.info.under if ft.kind == "enum" else ft, wt)
        mask = "(%d : %s)" % ((1 << w) - 1, wt.lean)
        return update_text(base, steps[:-1], V("(%s &&& ~~~(%s <<< %d)) ||| ((%s &&& %s) <<< %d)" % (
            cur if SIMPLE.match(cur) else "(%s)" % cur, mask, off, vw.at(ATOM), mask, off), LOW))
    if steps[-1][0] == "bit":
        # --ekf-types: bit k of a bit union: cleared, then set if the value is true
        cur = Path(None, base, steps[:-1], None).text()
        k, wt = steps[-1][1]
        one = "(1 : %s)" % wt.lean
        return update_text(base, steps[:-1], V("(%s &&& ~~~(%s <<< %d)) ||| (if %s then %s <<< %d else 0)" % (
            cur if SIMPLE.match(cur) else "(%s)" % cur, one, k, value.text, one, k), LOW))
    if any(k == "fm" for k, _ in steps):
        # --member-pointers: through a member object selected by a tag: one structure update per member
        j = next(i for i, (k, _) in enumerate(steps) if k == "fm")
        pre, (tag, names, _), rest = steps[:j], steps[j][1], steps[j + 1:]
        pb = Path(None, base, pre, None).text()
        alts = []
        for m, (c, f) in enumerate(names):
            inner = update_text("%s.%s" % (pb, f), rest, value)
            alts.append("| %s => %s" % ("." + c if m < len(names) - 1 else "_", update_text(base, pre + [("f", f)], V(inner, ATOM)) if not rest
                                       else update_text(base, pre + [("f", f)], V("(%s)" % inner, ATOM))))
        return "(match %s with %s)" % (tag.text, " ".join(alts))
    if any(k == "fi" for k, _ in steps):
        # --ekf-arrays: through a member selected by a runtime index: one structure update per member
        j = next(i for i, (k, _) in enumerate(steps) if k == "fi")
        pre, (idx, names), rest = steps[:j], steps[j][1], steps[j + 1:]
        pb = Path(None, base, pre, None).text()
        alts = []
        for m, f in enumerate(names):
            inner = update_text("%s.%s" % (pb, f), rest, value)
            alts.append("| %s => %s" % (str(m) if m < len(names) - 1 else "_", update_text(base, pre + [("f", f)], V(inner, ATOM)) if not rest
                                       else update_text(base, pre + [("f", f)], V("(%s)" % inner, ATOM))))
        return "(match %s with %s)" % (idx.text, " ".join(alts))
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


def ub_read(a, x):
    """--mission: Lean text of the value of type t at byte offset off of the bytes a (a byte union's member)."""
    off, t = x
    a = a if SIMPLE.match(a) else "(%s)" % a
    if t.kind == "record" or t.kind == "array":
        return value_from_bytes(a, str(off), t, None)
    return scalar_from_bytes(a, str(off), t)


def ubf_read(a, x):
    """--mission: Lean text of the bit-field of width w at bit `bit` from byte off of the bytes a (sign-extended
    if its type is signed)."""
    off, bit, w, t = x
    a = a if SIMPLE.match(a) else "(%s)" % a
    raw = "((CString.toUInt64 %s %d >>> %d) &&& %d)" % (a, off + bit // 8, bit % 8, (1 << w) - 1)
    if t.kind == "int" and t.signed:
        sx = V("(((%s <<< %d).toInt64) >>> %d)" % (raw, 64 - w, 64 - w), ATOM)
        return "(%s)" % int_conv(sx, CType("int", 64, True), t).text
    if t.kind == "bool":
        return "(%s != 0)" % raw
    return "(%s)" % int_conv(V(raw, ATOM), CType("int", 64, False), t).text


def ub_write(cur, step, value):
    """--mission: Lean text of the bytes cur with the member at step (a ("ub", (off, t)) or ("ubf", (off, bit, w, t))
    step) replaced by value."""
    c = cur if SIMPLE.match(cur) else "(%s)" % cur
    v = value.text if SIMPLE.match(value.text) else "(%s)" % value.text
    if step[0] == "ub":
        off, t = step[1]
        if t.kind in ("record", "array"):
            return "CString.write %s %d %s" % (c, off, "(%s)" % value_to_bytes(v, t, None))
        return "CString.write %s %d (%s)" % (c, off, scalar_to_bytes(v, t))
    off, bit, w, t = step[1]
    b0, sh = off + bit // 8, bit % 8
    nb = (sh + w + 7) // 8
    mask = (1 << w) - 1
    if t.kind == "bool":
        x = "(if %s then (1 : UInt64) else 0)" % v
    else:
        x = int_conv(V(v, ATOM), t, CType("int", 64, False)).at(ATOM)
    word = "((CString.toUInt64 %s %d &&& ~~~((%d : UInt64) <<< %d)) ||| ((%s &&& %d) <<< %d))" % (c, b0, mask, sh, x, mask, sh)
    return "CString.write %s %d (CString.slice (CString.ofUInt64 %s) 0 %d)" % (c, b0, word, nb)


def inplace_wanted(steps):
    """--ekf-arrays (F15): does a write at these steps update an array held by an element of another
    array (`s.EKF[m].P[k]`)? Lean's compiler already updates an array held by structures in place
    (`{ s with P := s.P.set! k v }`, `{ s with a.P := ... }`: the projection's reference is reused
    when `s` is unique; lean/F15Bench.lean, 5 ns per write), but not one reached through an array
    element, which `s.EKF[m]!` shares (650 ns per write for 576 elements: a copy each time). Not
    through views or bit patterns."""
    if any(k in ("v", "b", "row", "fi", "fm", "av", "bit", "bitf", "ub", "ubf") for k, _ in steps):
        return False
    return sum(1 for k, _ in steps if k == "i") >= 2


def inplace_lines(base, steps, value, temp, mutable=True):
    """--ekf-arrays (PORT-PLAN.md F15): the lines that store value at base.steps with every array on
    the way updated in place: each array (and each element holding a further array) is taken out of
    its holder before `set!` and put back after, so that no other reference to it exists when `set!`
    runs (`{ s with P := s.P.set! k v }` would copy the array, which `s` still holds). The index and
    the value are evaluated first. base is a `let mut` variable (mutable) or a `let` temporary."""
    out = []
    assign = (lambda x, e: "%s := %s" % (x, e)) if mutable else (lambda x, e: "let %s := %s" % (x, e))
    if not SIMPLE.match(value.text) and not re.match(r"^\(?-?[\w.']+ : \w+\)?$", value.text):
        t = temp()
        out.append("let %s := %s" % (t, value.text))
        value = V(t, ATOM)
    k = next(i for i, (kind, _) in enumerate(steps) if kind == "i")
    fields = [x for _, x in steps[:k]]
    idx = steps[k][1]
    if not re.match(r"^[\w']+$", idx.text):
        t = temp()
        out.append("let %s := %s" % (t, idx.text))
        idx = V(t, ATOM)
    rest = steps[k + 1:]
    if fields:
        arr = temp()
        fp = ".".join(fields)
        out.append("let %s := %s.%s" % (arr, base, fp))
        out.append(assign(base, "{ %s with %s := #[] }" % (base, fp)))
    else:
        arr = base
    put = (lambda a, e: "let %s := %s" % (a, e)) if fields or not mutable else (lambda a, e: "%s := %s" % (a, e))
    if rest:
        el = temp()
        out.append("let %s := %s[%s]!" % (el, arr, idx.text))
        out.append(put(arr, "%s.set! %s default" % (arr, idx.text)))
        if any(kind == "i" for kind, _ in rest):
            out += inplace_lines(el, rest, value, temp, mutable=False)
        else:
            out.append("let %s := %s" % (el, update_text(el, rest, value)))
        new = V(el, ATOM)
    else:
        new = value
    if fields:
        out.append(assign(base, "{ %s with %s := %s.set! %s %s }" % (base, ".".join(fields), arr, idx.text, new.at(ATOM))))
    else:
        out.append(put(arr, "%s.set! %s %s" % (arr, idx.text, new.at(ATOM))))
    return out


class Body:
    """Translates one function, method or constructor body (or one constant initializer) into
    lines of a Lean do block. In a method of context `ctx`, `this` is the state `s`, the
    parameters `p` and the boundary inputs `inp`."""

    def __init__(self, unit, fn=None, ctx=None, home=None):
        if fn is not None and fn.get("id") in unit.goto_rejects:
            raise unit.goto_rejects[fn["id"]]
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
        self.wtouch = set()         # --world: the World objects this body reaches (also through its callees)
        self.uses_self = False      # --world-pointers: `this` as a value in a heap object's member function (`self'`)
        self.singleton_set = False  # --world: a constructor's `_singleton = this` has been translated
        self.rets = []              # value text of each `return`, filled in by finish()
        self.void = False
        self.deps = set()           # ids of free functions, constants and contexts used
        self.var_range = {}         # --reachable: loop counter id -> (lo, hi) of its values in the body
        self._assigned_fn = None
        self.boundary_type_of = {}  # --reachable: id(node) -> CType of a boundary read of an untranslated enum, converted
        self.param_vars = set()     # parameters of a --param-class type (their value is the scalar)
        self.discard_node = None    # the call of the expression statement being translated (its value is discarded)
        self.loop_only = set()      # counters declared before the `for` loops that initialize them
        self.array_views = set()    # `const T *` parameters read only by subscript (arrays in Lean)
        self.off_params = set()     # --array-offsets: array pointer parameters passed with their offset (`p'o : Nat`)
        self.boundary_locals = {}   # local references bound to boundary objects -> the object's name
        self.case_exited = False    # the switch case being translated has an `if (c) { ...; break; }` exit
        self.var_views = False      # resolve_path: a view (`v.xy()`) of a variable is a path (reference arguments of live reads)
        self.aliases = {}           # reference parameter id -> Path of the member of this object it is bound to (Context.method alias)
        self.ptr_aliases = {}       # --front-ends: local pointer id -> the Path of the object it points to (never reassigned)
        self.this_override = None   # --front-ends: the object `this` denotes while an accessor's return expression is inlined
        self.live_refs = {}         # local reference id -> the live boundary read it names (read again at each use)
        self.tagrefs = set()        # --member-pointers: reference parameters and locals bound to tagged member objects (their tag)
        self.nullable = {}          # nullable out-pointer parameter id -> the Lean name of its flag (`roll'given`)
        self.unions = {}            # C: union variable id -> UnionInfo (the variable holds the bit pattern)
        self.sel_ptrs = {}          # --mission: local pointer id -> [AST of each member it may point to] (its value: 0 null, k the k-th)
        self.ptr_scalars = set()    # C: pointer parameters used only as `*p` (in/out scalars)
        self.label_loops = {}       # C: label id -> depth of self.loops inside the loop of a backward goto
        self.local_union = None     # C: the union declared by the DeclStmt being translated
        self.ptrs = {}              # --pointer-params: pointer parameter or local id -> PtrVar
        self.held = {}              # --c-strings: local object id -> [(member, Path of the pointer variable whose array it holds)]
        self.held_by = {}           # --c-strings: pointer variable id -> [(object name, member)]
        self.prologue = []          # lines before the body (the offsets of moved pointer parameters)
        self.ret_ptr = None         # --c-strings: index of the pointer parameter whose pointer the function returns (pp_ret_param)
        self.hs_use = set()         # --hal-storage: "r", "w": the body (or a callee) reads / writes the HAL storage
        self.gl_use = {}            # --mavlink: id of a mutable file-scope variable -> {"r", "w"}: the body (or a callee) reads / writes it
        self.ptr_alias_ids = set()  # --mavlink: local struct pointers that alias an object (Body.aliases holds its Path)
        self.text_ptrs = set()      # --text-results (Phase 5d): local `const char *` texts (CText, `CText.null` for null)
        self.opt_vars = set()       # --mavlink: local `const T *` initialized by a call returning `Option T` (opt_return_type)
        self.counters = set()       # ids of the counters of the counted loops being translated (immutable per iteration)
        self.rb_params = set()      # --ring-buffers: `void *` parameters (the element the caller passes by `&x`)
        self.rb_alias = {}          # --ring-buffers: local pointer id -> Path of the element it points to

    def temp(self):
        self.ntemp += 1
        return "t'%d" % self.ntemp

    def fresh_local(self, name, rid):
        """--front-ends: a second variable of the name in the function (`for (Priority i(0); ...)` twice in
        AP_Compass.cpp, whose counters a loop without a constant trip count declares before it, then a
        counted `for (uint8_t i ...)`): a fresh name (Lean does not shadow a mutable variable)."""
        if not FRONT_ENDS[0] or not any(nm == name for r0, nm in self.declared if r0 != rid):
            return name
        k = 2
        while any(nm == "%s'%d" % (name, k) for _, nm in self.declared):
            k += 1
        return "%s'%d" % (name, k)

    def ident(self, name, node):
        if self.ctx is not None and name in RESERVED_IN_METHODS:
            if REACHABLE[0] or INS_GPS[0]:
                return lean_ident(name, node) + "'"     # `for (auto s=0; ...)` (AP_NavEKF3_core.cpp:1971), the parameter `s` of AP_GPS_Backend::velocity_to_speed_course (--ins-gps): renamed
            raise Reject(node, "identifier `%s` in a member function (reserved: the state, parameters and inputs)" % name)
        if FRONT_ENDS[0] and WORLD_PTRS[0] and any(w["name"] == name for w in self.u.world):
            return lean_ident(name, node) + "'"     # --front-ends: not the name of a `WPtr` constructor (`auto *sitl = AP::sitl();`)
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
            elif k == "VAArgExpr" and C_STRINGS[0]:
                targets.append(kids(m)[0])          # `va_arg(ap, T)` moves ap to the next argument
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
                if C_STRINGS[0] and k == "CallExpr" and args and strip_parens(kids(m)[0]).get("castKind") == "BuiltinFnToFnPtr" and \
                        (kids(strip_parens(kids(m)[0]))[0].get("referencedDecl") or {}).get("name") in ("__builtin_va_start", "__builtin_va_copy"):
                    targets.append(args[0])
                if callee is not None:
                    ps = [p for p in kids(callee) if p.get("kind") == "ParmVarDecl"]
                    for a, p in zip(args, ps):
                        q = p["type"]["qualType"].rstrip()
                        if q.endswith("&") and not q.endswith("&&") and not q.startswith("const "):
                            targets.append(a)
                        sa = rb_strip(a) if (RING_BUFFERS[0] or EKF_ARRAYS[0]) and q == "void *" else strip_object(a)
                        if q.endswith("*") and not q.startswith("const ") and sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&":
                            targets.append(kids(sa)[0])     # `&x` for a (nullable) out-pointer parameter
                        if (C_MODE[0] or (TEXT_BUFFERS[0] and re.match(r"^char ?\*$", q))) and q.endswith("*") and not q.startswith("const "):
                            # (--text-buffers: a `char` buffer for a `char *` parameter, which the callee fills)
                            sp = strip_parens(a)
                            while sp.get("kind") == "ImplicitCastExpr" and sp.get("castKind") in ("ArrayToPointerDecay", "LValueToRValue", "NoOp"):
                                sp = strip_parens(kids(sp)[0])
                            if sp.get("kind") == "DeclRefExpr":
                                targets.append(sp)          # an array (or a pointer parameter) for a pointer parameter
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

    def zero_init_list(self, init):
        """--mission: is init (`{}`) a value-initialization giving zero bytes: every node under it an implicit
        value-initialization, a nested list, or a default construction of a byte union (`Content`, whose default
        member initializer `Location location{}` runs Location's constructor, `zero()`: a memset of the bytes)
        or of a class whose default constructor gives zero?"""
        if init.get("kind") not in ("InitListExpr", "ParenListExpr"):
            return False
        for m in walk(init):
            if m is init or m.get("kind") in ("ImplicitValueInitExpr", "InitListExpr"):
                continue
            if m.get("kind") == "CXXConstructExpr" and not kids(m):
                ct = ctype_of(m)
                if ct.kind == "record" and (getattr(ct.info, "byte_union", False) or zero_default_ctor(self.u, ct)):
                    continue
            return False
        return True

    def e_InitListExpr(self, n):
        """`{a, b, c}` for a plain struct: its fields in declaration order (an element of a constant
        table such as AP_MotorsMatrix's `MotorDef motors[]`); an array member's initializer (C: musl's
        data tables, `.tab = {...}`)."""
        t = ctype_of(n)
        if t.kind == "array" and C_MODE[0]:
            return self.array_init(n, t)
        if MISSION[0] and t.kind == "record" and self.zero_init_list(n):
            return [], all_zero(t, n)       # --mission: `cmd = {};` (a value-initialized temporary assigned)
        if MISSION[0] and t.kind == "record" and not t.info.bases and not getattr(t.info, "byte_union", False) and \
                not any(m.get("virtual") for m in t.info.methods):
            # --mission: `packet = { seq: cmd.index, command: cmd.id, autocontinue: 1, };` (AP_Mission.cpp:1702): the
            # members in order, the ones not named value-initialized (ImplicitValueInitExpr: zero)
            fields = [f for f in t.info.all_fields() if f.category == "state"]
            if len(kids(n)) != len(fields):
                raise Reject(n, "initializer list for `%s` with %d values for %d members" % (t.cname, len(kids(n)), len(fields)))
            pre, vs = self.operands(kids(n))
            return pre, V("{ %s }" % ", ".join("%s := %s" % (f.lean, v.text) for f, v in zip(fields, vs)), ATOM)
        if t.kind != "record" or t.info.kind != "plain":
            raise Reject(n, self.describe(n))
        fields = [f for f in t.info.all_fields() if f.category == "state"]
        vals = kids(n)
        if n.get("array_filler") or len(vals) != len(fields):
            raise Reject(n, "initializer list for `%s` with %d values for %d members" % (t.cname, len(vals), len(fields)))
        if MEMBER_PTRS[0] and any(f.id in self.u.refptr_fields for f in fields):
            # --member-pointers: `{ dcm, dcm_estimates }` (AP_AHRS.h:1056): the references bound to member objects, their tags
            vs = []
            for f, a in zip(fields, vals):
                if f.id in self.u.refptr_fields:
                    v = self.mtag_member(a)
                    if v is None:
                        raise Reject(a, "reference member `%s` bound to something other than a member object of this object" % f.name)
                    vs.append(v)
                else:
                    vs.append(self.expr(a)[1])
            return [], V("{ %s }" % ", ".join("%s := %s" % (f.lean, v.text) for f, v in zip(fields, vs)), ATOM)
        pre, vs = self.operands(vals)
        return pre, V("{ %s }" % ", ".join("%s := %s" % (f.lean, v.text) for f, v in zip(fields, vs)), ATOM)

    def e_UnaryExprOrTypeTraitExpr(self, n):
        """--c-strings, --byte-objects: `sizeof(T)`, `sizeof(x)`: the size of the object
        representation on the reference target (byte_size_align), a `size_t` constant."""
        if not (C_STRINGS[0] or BYTE_OBJECTS[0] or RING_BUFFERS[0]) or n.get("name") != "sizeof":
            raise Reject(n, self.describe(n))
        k0 = strip_parens(kids(n)[0]) if kids(n) else {}
        mt = re.match(r"^char ?\[(\d+)\]$", k0.get("type", {}).get("desugaredQualType", k0.get("type", {}).get("qualType", ""))) if TEXT_BUFFERS[0] and k0 else None
        if mt:
            return [], lit(mt.group(1), ctype_of(n))       # --text-buffers: `sizeof(buffer)` of a `char buffer[N]`: N
        if k0.get("kind") == "DeclRefExpr" and k0["referencedDecl"]["id"] in self.unions:
            return [], lit(str(self.unions[k0["referencedDecl"]["id"]].word.bits // 8), ctype_of(n))     # a union of one width
        t = parse_type_str(n["argType"]["qualType"], n["argType"].get("desugaredQualType", n["argType"]["qualType"]), n) \
            if "argType" in n else ctype_of(kids(n)[0])
        if t.kind == "record" and t.info.cxx in SIZEOFS:
            return [], lit(str(SIZEOFS[t.info.cxx]), ctype_of(n))      # --sizeof (clang's value)
        size, _ = byte_size_align(t, n)
        return [], lit(str(size), ctype_of(n))

    def array_size(self, n):
        """`sizeof(a) / sizeof(a[0])` (ArduPilot's ARRAY_SIZE) for an array a: its length, else None."""
        n = strip_parens(n)
        if n.get("kind") != "BinaryOperator" or n.get("opcode") != "/":
            return None
        a, b = [strip_parens(x) for x in kids(n)]
        if not all(x.get("kind") == "UnaryExprOrTypeTraitExpr" and x.get("name") == "sizeof" and kids(x) for x in (a, b)):
            return None
        ta = ctype_of(kids(a)[0])
        if C_STRINGS[0] and ta.kind == "array" and ta.elem == CSTR and ta.n > 0:
            return ta.n                 # a table of string literals: its elements are pointers
        tb = ctype_of(kids(b)[0])
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

    def e_CharacterLiteral(self, n):
        """--c-strings: a character literal: its value, of clang's type (`char`: the byte)."""
        if not C_STRINGS[0]:
            raise Reject(n, "character literal")
        return [], lit(str(n["value"]), ctype_of(n))

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
        if "spellingLoc" not in rng and rng.get("file") and os.path.isfile(rng["file"]):
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
            self.u.literal(n, v.text, "%0*x" % (width, bits), text)
        else:
            dec = "(%s : %s)" % (lean_decimal(s), t.lean)
            v = flit_bits(bits, t, text)
            self.u.literal(n, dec, "%0*x" % (width, bits), text)
        return [], v

    def e_DeclRefExpr(self, n):
        ref = n["referencedDecl"]
        rid = ref["id"]
        if rid in self.aliases:
            return [], self.read_path(self.aliases[rid], n)
        if rid in self.live_refs:
            return self.expr(self.live_refs[rid])
        if rid in self.tagrefs:
            pre, p = self.resolve_path(n)       # --member-pointers: the value of the member object the tag designates
            return pre, self.read_path(p, n)
        if MAVLINK[0] and self.global_var(rid) is not None:
            rid = self.global_var(rid)
        if rid in self.vars:
            if rid in self.uninit and self.da is not DIVERGE and rid not in self.da and not UNINIT_READS[0]:
                raise Reject(n, "read of `%s`, which may be uninitialized" % ref["name"])
            self.read.add(rid)
            return [], V(self.vars[rid][0], ATOM)
        if WORLD_PTRS[0] and rid in self.u.heap_ptr:
            # `Store::_singleton` of a class without a file-scope object: a World field
            self.u.heap_ptr_used.add(self.u.heap_ptr[rid])
            return [], self.read_path(Path(("w",), "w", [("f", self.u.heap_ptr[rid])], ctype_of(n)), n)
        if (REACHABLE[0] or INS_GPS[0]) and rid in self.u.world_ids and any(w["name"] == self.u.world_ids[rid] and w.get("static") for w in self.u.world):
            return [], self.read_path(self.world_path(self.u.world_ids[rid], n), n)     # a static data member or static local
        if rid in self.u.extern_vars:
            defs = [cid for cid, c in self.u.consts.items() if c["decl"].get("name") == self.u.extern_vars[rid]]
            if len(defs) != 1:
                raise Reject(n, "`extern` constant `%s` without one definition in the translated files" % ref["name"])
            rid = defs[0]
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
            if e is None and ENUM_AS_INT:
                # --enum-as-int (Phase 5c): the enumerator's value, from its enumeration's declaration
                en = self.u.parent.get(rid)
                if en is not None and en.get("kind") == "EnumDecl" and en.get("name") in ENUM_AS_INT:
                    v = -1
                    for c in kids(en):
                        if c.get("kind") != "EnumConstantDecl":
                            continue
                        ce = next((x for x in walk(c) if x.get("kind") == "ConstantExpr" and "value" in x), None)
                        v = int(ce["value"]) if ce is not None else v + 1
                        if c.get("id") == rid:
                            if v < 0:
                                raise Reject(n, "enumerator `%s` with a negative value (--enum-as-int)" % ref["name"])
                            return [], V("(%d : UInt32)" % v, ATOM)
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
        if MAVLINK[0] and ck == "PointerToBoolean" and self.opt_ref(c):
            self.read.add(self.opt_ref(c))
            return [], V("%s.isSome" % self.vars[self.opt_ref(c)][0], ATOM)
        if MAVLINK[0] and ck == "PointerToBoolean" and self.is_struct_ptr(c):
            return [], V("true /- C++ `%s` (not null) -/" % comment_safe(self.u.text_of(c) or "p"), ATOM)
        if FRONT_ENDS[0] and ck == "PointerToBoolean" and self.nullable_ref(c) is not None:
            return [], V(self.nullable[self.nullable_ref(c)], ATOM)     # `if (scaling)`: the flag of a nullable pointer
        if AHRS_EXT[0] and ck == "PointerToBoolean" and strip_object(c).get("kind") == "MemberExpr" and \
                self.boundary_obj(kids(strip_object(c))[0]) is not None:
            # --ahrs-ext: `if (hal.opticalflow)` (AP_AHRS.cpp:645): whether the boundary's pointer is set, an input
            cm = strip_object(c)
            self.boundary_type_of[id(n)] = BOOL
            return [], self.boundary_read_value(n, self.boundary_obj(kids(cm)[0]), cm["name"] + "_set", False, [])
        if WORLD_PTRS[0]:
            r = self.wptr_cast(n, ck, c)
            if r is not None:
                return r
        if C_STRINGS[0] and ck == "ArrayToPointerDecay" and strip_parens(c).get("kind") == "StringLiteral":
            # --c-strings: a string literal as a pointer value (an element of a table of strings): its bytes
            return [], V(bytes_text(string_bytes(strip_parens(c))), ATOM)
        if ck == "ArrayToPointerDecay" and strip_parens(c).get("kind") == "StringLiteral" and ctype_of(n).kind == "string":
            return self.string_literal(strip_parens(c))     # a string literal as `const char *`
        if TEXT_BUFFERS[0] and ck == "ArrayToPointerDecay" and ctype_of(n).kind == "textbuf" and ctype_of(c).kind == "textbuf":
            return self.expr(c)     # --text-buffers: a local `char` buffer as a `char *` (the pending text itself)
        if ck == "ArrayToPointerDecay":
            raise Reject(n, "array used as a pointer")
        if ck == "UserDefinedConversion" or (ck == "LValueToRValue" and n.get("conversionFunc")):
            return self.expr(c)
        if ck == "ConstructorConversion" and FRONT_ENDS[0]:
            return self.expr(c)     # --front-ends: `Priority(i)`, an explicit constructor (the CXXConstructExpr inside)
        if ck in ("UncheckedDerivedToBase", "DerivedToBase"):
            raise Reject(n, "object converted to a base class (slicing)")
        if ck == "PointerToBoolean" and REACHABLE[0] and self.boundary_object_call(strip_object(c)):
            # `AP::wheelencoder()` tested for null: whether the boundary has that object, an input
            fld = self.ctx.input_field(self.u.text_of(strip_object(c)) or "boundary", "nonnull", False, [], BOOL,
                                       "%s != nullptr" % (self.u.text_of(strip_object(c)) or "?"), n)
            self.reads.add("inp")
            return [], V("inp.%s" % fld, ATOM)
        if ck == "PointerToBoolean" and RING_BUFFERS[0] and self.rb_is_buf(c):
            return [], self.read_path(self.rb_paths()[1], n)     # --ring-buffers: `if (buffer)`
        if ck not in CAST_KINDS:
            raise Reject(n, "cast `%s`" % ck)
        if REACHABLE[0] and ck == "IntegralCast" and ctype_of(n).kind == "int" and self.untranslated_type(c):
            # `(uint8_t)ahrs.get_vehicle_class()`: a boundary value of an enum type that is not translated,
            # read as the integer it is converted to
            self.boundary_type_of[id(strip_object(c))] = ctype_of(n)
            return self.expr(c)
        sc = strip_parens(c)
        if MISSION[0] and ck == "IntegralCast" and ctype_of(n).kind == "int" and sc.get("kind") in ("CStyleCastExpr", "CXXFunctionalCastExpr") and \
                ctype_of(sc).kind == "enum" and kids(sc) and sc.get("castKind") == "FloatingToIntegral":
            # --mission: `cmd.p1 = (NAV_VTOL_LAND_OPTIONS)packet.param1;` (AP_Mission.cpp:1415): the float converted to
            # the enum's underlying integer type (any value, not only an enumerator's), then to the integer
            fc = sc
            pre, v = self.expr(kids(fc)[0])
            ut = ctype_of(sc).info.under
            return pre, conv(conv(v, ctype_of(kids(fc)[0]), ut, fc), ut, ctype_of(n), n)
        pre, v = self.expr(c)
        if ck in ("NoOp", "LValueToRValue"):
            return pre, v
        s, d = ctype_of(c), ctype_of(n)
        if ck in ("IntegralToFloating", "FloatingCast") and not pre and d.kind in ("float", "double"):
            k = const_number(c)
            if k is not None:     # a zero here is +0: const_number never negates a zero
                # a conversion of a constant (`(float)2`, a double literal converted to float): its
                # bits, computed once here; the conversion as written is the registered check
                r = round_to_binary(k, *FORMAT[d.kind])
                if r is not None:
                    width = 8 if d.kind == "float" else 16
                    bits = float_bits(r, d)
                    check = conv(v, s, d, n)
                    shown = self.u.text_of(n) or ("(%s)%s" % (d.cname, k))
                    self.u.literal(n, check.text, "%0*x" % (width, bits), shown)
                    self.deps |= type_deps(s) | type_deps(d)
                    return [], flit_bits(bits, d, shown)
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

    def untranslated_decl(self, d):
        try:
            decl_type(d)
            return False
        except Reject:
            return True

    def only_dropped_uses(self, d):
        """Is every use of local d an argument of a call of a dropped function, or the left side of `=`
        (with a right side without effects)?"""
        body = next((c for c in kids(self.fn) if c.get("kind") == "CompoundStmt"), {}) if self.fn else {}
        for m in walk(body):
            if m.get("kind") != "DeclRefExpr" or m.get("referencedDecl", {}).get("id") != d["id"]:
                continue
            up, child = self.u.parent.get(m["id"]), m
            while up is not None:
                k = up.get("kind")
                if k == "BinaryOperator" and up.get("opcode") == "=" and kids(up)[0] is child and not self.has_effects(kids(up)[1]):
                    break
                if k in ("CallExpr", "CXXMemberCallExpr"):
                    c = strip_parens(kids(up)[0])
                    while c.get("kind") == "ImplicitCastExpr":
                        c = strip_parens(kids(c)[0])
                    cd = self.u.decl(c.get("referencedMemberDecl") or (c.get("referencedDecl") or {}).get("id"))
                    if cd is not None and (cd["id"] in self.u.dropped or qualified_name(self.u, cd) in DROP):
                        break
                    return False
                if k in ("CompoundStmt", "IfStmt", "ForStmt", "WhileStmt", "DoStmt", "ReturnStmt", "DeclStmt"):
                    return False
                up, child = self.u.parent.get(up["id"]), up
            else:
                return False
        return True

    def untranslated_type(self, c):
        try:
            ctype_of(c)
            return False
        except Reject:
            return True

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

    def world_path(self, name, n):
        """The Path of World object `name` (--world)."""
        if name.startswith("*"):
            return self.singleton_path(name[1:], n)
        w = next(x for x in self.u.world if x["name"] == name)
        if WORLD_PTRS[0] and self.ctx is not None and name == self.u.world_self.get(self.ctx.rec.id):
            # --world-pointers: this object itself (`AP::baro()` inside AP_Baro): its state is `s`
            return Path(("s",), "s", [], CType("record", info=w["rec"]))
        self.wtouch.add(name)
        if w.get("static"):
            return Path(("w",), "w", [("f", name)], w["t"])
        return Path(("w",), "w", [("f", name)], CType("record", info=w["rec"]))

    def singleton_path(self, hfld, n):
        """--world-pointers: the Path of the heap singleton whose heap field is hfld (`heap'AP_DAL`): the
        object the static singleton pointer points to (`*AP_DAL::_singleton`). A reference bound to the
        singleton at construction denotes it for good: the pointer is assigned only by `get_singleton()`
        while it is null."""
        rec = next(h for h in self.u.heap if heap_field(h) == hfld)
        sf = heap_singleton_field(self.u, rec)
        if self.ctx is not None and rec is self.ctx.rec:
            return Path(("s",), "s", [], CType("record", info=rec))     # the singleton's own member function
        self.u.wptr_index = True
        self.u.heap_ptr_used.add(sf)
        self.wtouch.add(hfld)
        self.reads.add("w")
        return Path(("w",), "w", [("f", hfld), ("i", V("(WPtr.index w.%s)" % sf, ATOM))], CType("record", info=rec))

    def this_field(self, n):
        """The FieldInfo of `this->f` (n a MemberExpr), or None if n is not a member of `this`."""
        if n.get("kind") != "MemberExpr" or self.this_override is not None:
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
        if EKF_ARRAYS[0] and ctype_of(idx).is_int():
            k = self.const_int(idx)
            if k is not None and k >= 0:
                return [], V(str(k), ATOM)      # --ekf-arrays: a constant index as a Nat literal
        pre_i, i = self.expr(idx)
        it = ctype_of(idx)
        if not it.is_int():
            raise Reject(idx, "array index of type `%s`" % it.cname)
        nat = app("%s.toNatClampNeg" % it.lean, i) if it.signed else app("%s.toNat" % it.lean, i)
        return pre_i, nat

    def inline_accessor_path(self, n):
        """--front-ends: (pre, Path) of a call of a non-virtual member function that returns a reference
        and whose body is one `return e;` (`RestrictIDTypeArray::operator[](const Priority &index) { return
        _priv_instance[index.get_int()]; }`, AP_Common/TSIndex.h:110; INS_PARAM_WRAPPER's `_gyro_id(uint8_t
        i) { return _gyro_id_old_param[i]; }` and its const twin `const_cast<AP_InertialSensor*>(this)->
        _gyro_id(i)`, AP_InertialSensor.h:654): e's path, with `this` the call's object and the parameters
        bound to the arguments' values (computed once, before), else None."""
        k = n.get("kind")
        if k == "CXXMemberCallExpr":
            callee = strip_parens(kids(n)[0])
            if callee.get("kind") != "MemberExpr":
                return None
            mdecl = self.u.decl(callee.get("referencedMemberDecl"))
            obj, args = kids(callee)[0], kids(n)[1:]
        elif k == "CXXOperatorCallExpr" and len(kids(n)) >= 2:
            c = strip_parens(kids(n)[0])
            while c.get("kind") == "ImplicitCastExpr":
                c = strip_parens(kids(c)[0])
            mdecl = self.u.decl((c.get("referencedDecl") or {}).get("id"))
            obj, args = kids(n)[1], kids(n)[2:]
        else:
            return None
        if mdecl is None or mdecl.get("kind") not in ("CXXMethodDecl", "CXXConversionDecl") or mdecl.get("virtual") or not returns_reference(mdecl):
            return None
        if AHRS_EXT[0] and not FRONT_ENDS[0] and self.u.parent_record(mdecl) is None:
            return None         # (--ahrs-ext: a member function of a class the translation does not hold, `AP_Vector3f::get`)
        body = self.u.body_of(mdecl) or mdecl
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None)
        if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
            return None
        e = kids(kids(cs)[0])[0]
        o = obj
        while True:
            o = strip_object(o)
            if o.get("kind") in ("CXXConstCastExpr", "ImplicitCastExpr", "UnaryOperator") and kids(o) and \
                    (o.get("kind") != "UnaryOperator" or o.get("opcode") == "*"):
                o = kids(o)[0]
                continue
            break
        if o.get("kind") == "CXXThisExpr":
            if self.this_override is not None:
                op, pre = self.this_override, []
            elif self.ctx is not None:
                op, pre = Path(("s",), "s", [], CType("record", info=self.ctx.rec)), []
            else:
                return None
        else:
            r = self.resolve_path(o)
            if r is None:
                return None
            pre, op = r
        if op.t is None or op.t.kind != "record":
            return None
        if AHRS_EXT[0] and self.ctx is not None and op.t.info not in self.ctx.rec.chain() and any(
                m.get("kind") == "CXXMemberCallExpr" and strip_parens(kids(m)[0]).get("kind") == "MemberExpr" and
                strip_object(kids(strip_parens(kids(m)[0]))[0]).get("kind") == "CXXThisExpr" for m in walk(e)):
            # (--ahrs-ext: an accessor of another class's object whose returned expression calls a member function of
            # that object, `compass.get_field()` -> `_get_state(Priority(i)).field` -> `_state[_get_state_id(priority)]`,
            # AP_Compass.h:639, from AP_AHRS_DCM.cpp:527: not inlined here; the caller reads it through the getter)
            return None
        params = [p for p in kids(body) if p.get("kind") == "ParmVarDecl"]
        pre = list(pre)
        bound = []
        for i, p in enumerate(params):
            a = args[i] if i < len(args) else None
            if a is None:
                return None
            if a.get("kind") == "CXXDefaultArgExpr":
                a = kids(a)[0] if kids(a) else a
            pa, v = self.expr(a)
            tmp = self.temp()
            pt, _ = decl_type(p)
            pre += pa + ["let %s := %s" % (tmp, v.text)]
            self.vars[p["id"]] = (tmp, pt)
            bound.append(p["id"])
        saved = self.this_override
        if not (AHRS_EXT[0] and saved is None and o.get("kind") == "CXXThisExpr"):
            self.this_override = op     # (--ahrs-ext: an accessor of this object itself: `this` stays this object)
        try:
            r = self.resolve_path(e)
        finally:
            self.this_override = saved
            for b in bound:
                self.vars.pop(b, None)
        if r is None:
            return None         # (a const accessor whose result is used as a value: translated as a function)
        return pre + r[0], r[1]

    def resolve_path(self, n):
        """(pre, Path) of an lvalue expression, or None if n is not a variable, a data member
        or an array element of one."""
        n = strip_object(n)
        k = n.get("kind")
        if MAVLINK[0] and k == "CallExpr" and self.gaccessor_of(n) is not None:
            return self.gaccessor_path(n)       # --mavlink: `mavlink_get_channel_status(chan)`: the element
        if MAVLINK[0] and k == "MemberExpr" and n.get("isArrow") and self.opt_ref(kids(n)[0]):
            # --mavlink: `e->crc_extra` of a non-null `const T *` (an `Option`): the member of the object
            rid = self.opt_ref(kids(n)[0])
            name, t = self.vars[rid]
            f = t.elem.info.field_by_id(n["referencedMemberDecl"])
            if f is None:
                raise Reject(n, "member `%s`" % n.get("name"))
            return [], Path(("var", rid), name, [("opt", None), ("f", f.lean)], f.t)
        if MAVLINK[0] and k == "MemberExpr" and n.get("isArrow") and strip_casts(kids(n)[0]).get("kind") == "UnaryOperator" and \
                strip_casts(kids(n)[0]).get("opcode") == "&":
            r = self.resolve_path(kids(strip_casts(kids(n)[0]))[0])     # --mavlink: `(&msg)->len`
            if r is None or r[1].t is None or r[1].t.kind != "record":
                return None
            f = r[1].t.info.field_by_id(n["referencedMemberDecl"])
            if f is None or f.category != "state":
                raise Reject(n, "member `%s`" % n.get("name"))
            return r[0], r[1].extend(("f", f.lean), f.t)
        if MAVLINK[0] and k == "UnaryOperator" and n.get("opcode") == "*" and self.is_struct_ptr(kids(n)[0]) and \
                strip_casts(kids(n)[0]).get("kind") in ("DeclRefExpr", "CallExpr"):
            return self.struct_ptr_target(kids(n)[0])     # --mavlink: `*p` of a struct pointer
        if (FRONT_ENDS[0] or AHRS_EXT[0]) and k == "ExprWithCleanups" and kids(n):
            return self.resolve_path(kids(n)[0])
        if FRONT_ENDS[0] and k == "InitListExpr" and len(kids(n)) == 1 and n.get("valueCategory") == "lvalue":
            return self.resolve_path(kids(n)[0])        # `const Vector3f &f { get_field() };` (AP_Compass.cpp:2174)
        if (FRONT_ENDS[0] and k in ("CXXOperatorCallExpr", "CXXMemberCallExpr")) or (AHRS_EXT[0] and k == "CXXMemberCallExpr"):
            r = self.inline_accessor_path(n)    # (--ahrs-ext: `get_gyro_drift()`, `return state.gyro_drift;`, AP_AHRS.h:95)
            if r is not None:
                return r
        if FRONT_ENDS[0] and k == "MemberExpr" and n.get("isArrow") and \
                strip_object(kids(n)[0]).get("kind") == "DeclRefExpr" and strip_object(kids(n)[0])["referencedDecl"]["id"] in self.ptr_aliases:
            op = self.ptr_aliases[strip_object(kids(n)[0])["referencedDecl"]["id"]]
            f = op.t.info.field_by_id(n.get("referencedMemberDecl"))
            if f is None or f.category != "state":
                raise Reject(n, "member `%s` through a local pointer, not a data member" % n.get("name"))
            return [], op.extend(("f", f.lean), f.t)
        if (FRONT_ENDS[0] or AHRS_EXT[0]) and k == "MemberExpr" and self.this_override is not None and \
                strip_object(kids(n)[0]).get("kind") == "CXXThisExpr":
            op = self.this_override
            f = op.t.info.field_by_id(n.get("referencedMemberDecl"))
            if AHRS_EXT[0] and f is not None and f.category == "param" and op.root == ("w",) and len(op.steps) == 1:
                # --ahrs-ext: a parameter of a World object read by an inlined accessor (`AP::ahrs().get_trim()`,
                # `return _trim.get();`, AP_AHRS.h:553): its Params field
                return [], Path(("w",), "w", [("f", op.steps[0][1] + "'p"), ("f", f.lean)], f.t)
            if f is None or f.category != "state":
                raise Reject(n, "member `%s` of an accessor's object that is not a data member of its state" % n.get("name"))
            return [], op.extend(("f", f.lean), f.t)
        if POINTER_PARAMS[0] and k in ("UnaryOperator", "ArraySubscriptExpr"):
            r = self.ptr_path(n)
            if r is not None:
                return r
        if MEMBER_PTRS[0] and self.u.mtags and ((k == "DeclRefExpr" and n["referencedDecl"]["id"] in self.tagrefs) or
                                                (k == "MemberExpr" and n.get("referencedMemberDecl") in self.u.refptr_fields)):
            pre, v, rec = self.mtag_ref(n)      # --member-pointers: the member object the tag designates
            return self.mtag_path(pre, v, rec, n)
        if MEMBER_OBJECTS[0] and k == "MemberExpr" and n.get("referencedMemberDecl") in self.u.world_ids and \
                not self.has_effects(kids(n)[0]):
            return [], self.world_path(self.u.world_ids[n["referencedMemberDecl"]], n)   # `ekf3.EKF3`: a static member object
        if k == "DeclRefExpr":
            rid = n["referencedDecl"]["id"]
            if rid in self.aliases:
                if self.aliases[rid].root == ("w",) and self.aliases[rid].steps:
                    self.wtouch.add(self.aliases[rid].steps[0][1])
                return [], self.aliases[rid]
            if WORLD_PTRS[0] and rid in self.u.heap_ptr:
                # `Store::_singleton` of a class without a file-scope object: a World field (a pointer)
                self.u.heap_ptr_used.add(self.u.heap_ptr[rid])
                return [], Path(("w",), "w", [("f", self.u.heap_ptr[rid])], ctype_of(n))
            if rid in self.u.world_ids:
                return [], self.world_path(self.u.world_ids[rid], n)
            if MAVLINK[0] and self.global_var(rid) is not None:
                rid = self.global_var(rid)
            if rid not in self.vars:
                return None
            name, t = self.vars[rid]
            return [], Path(("var", rid), name, [], t)
        if EKF_TYPES[0] and k == "MemberExpr" and strip_object(kids(n)[0]).get("kind") == "MemberExpr" and \
                strip_object(kids(n)[0]).get("referencedMemberDecl") in UNION_VIEWS:
            # --ekf-types: a member of the unnamed union of an array and a struct: the array, or the struct's view of it
            un = strip_object(kids(n)[0])
            aid, sid, st = UNION_VIEWS[un["referencedMemberDecl"]]
            r = self.resolve_path(kids(un)[0]) if strip_object(kids(un)[0]).get("kind") != "CXXThisExpr" else ([], Path(("s",), "s", [], None))
            if r is None:
                return None
            pre, bp = r
            rec = self.ctx.rec if bp.t is None else bp.t.info
            af = rec.field_by_id(aid)
            ap_ = Path(bp.root, bp.root_text, bp.steps + [("f", af.lean)], af.t)
            if n.get("referencedMemberDecl") == aid:
                return pre, ap_
            return pre, Path(ap_.root, ap_.root_text, ap_.steps + [("av", (st, 0))], st)
        if RING_BUFFERS[0] and k == "MemberExpr" and n.get("isArrow") and strip_object(kids(n)[0]).get("kind") == "DeclRefExpr" \
                and strip_object(kids(n)[0])["referencedDecl"]["id"] in self.rb_alias:
            bp = self.rb_alias[strip_object(kids(n)[0])["referencedDecl"]["id"]]     # --ring-buffers: `el->time_ms`
            f = bp.t.info.field_by_id(n["referencedMemberDecl"]) if bp.t.kind == "record" else None
            if f is None or f.category != "state":
                raise Reject(n, "member `%s` of a buffer element" % n.get("name"))
            return [], bp.extend(("f", f.lean), f.t)
        if RING_BUFFERS[0] and k == "UnaryOperator" and n.get("opcode") == "*" and strip_object(kids(n)[0]).get("kind") == "DeclRefExpr" \
                and strip_object(kids(n)[0])["referencedDecl"]["id"] in self.rb_alias:
            return [], self.rb_alias[strip_object(kids(n)[0])["referencedDecl"]["id"]]     # --ring-buffers: `*ret`
        if k == "MemberExpr" and WORLD_PTRS[0] and n.get("isArrow") and strip_object(kids(n)[0]).get("kind") != "CXXThisExpr":
            pt = self.obj_type(kids(n)[0])
            if pt is not None:
                # `frontend->gain`: the member of the object the pointer points to (one possible object)
                pre, bp = self.ptr_deref_path(kids(n)[0], pt, n)
                f = bp.t.info.field_by_id(n["referencedMemberDecl"])
                if f is None or f.category not in ("state", "param"):
                    raise Reject(n, "member `%s` through a pointer, which is not a data member of the object's state" % n.get("name"))
                if f.category == "param":
                    if len(bp.steps) != 1:
                        raise Reject(n, "parameter `%s` of a heap object" % n.get("name"))
                    return pre, Path(("w",), "w", [("f", bp.steps[0][1] + "'p"), ("f", f.lean)], f.t)
                return pre, bp.extend(("f", f.lean), f.t)
        if k == "MemberExpr":
            f = self.this_field(n)
            if f is not None:
                if f.category == "param":
                    return [], Path(("p",), "p", [("f", f.lean)], f.t)
                if f.category == "wpref":
                    return [], self.wpref_path(f, n)        # --ahrs-ext: a reference to the owner's parameter
                if f.category == "ref":
                    return [], Path(("r",), "r'", [("f", f.lean)], f.t)
                if f.category == "boundary":
                    return None
                if f.category == "wref":
                    target = self.u.wref.get((self.ctx.rec.id, f.id))
                    if target is None and WORLD_PTRS[0] and f.t.kind == "record":
                        # a heap object's reference to another object: the one file-scope object of that class
                        target = world_object_of_class(self.u, f.t.info)
                        if target is None and heap_singleton_field(self.u, f.t.info) is not None:
                            target = "*" + heap_field(f.t.info)     # or the class's heap singleton
                    if target is None:
                        raise Reject(n, "reference member `%s` whose object is not known (--world: a class with a World object binds it)" % f.name)
                    if isinstance(target, tuple) and target[0] == "elem":
                        # --ins-gps: an element of an array member of a World object, at the index this object holds
                        # (`state` of AP_GPS_Backend: `w.gps.state[s.state'i]!`, heap_elem_refs)
                        p_ = self.world_path(target[1], n)
                        for fl in target[2]:
                            g = next(x for x in p_.t.info.all_fields() if x.name == fl)
                            p_ = p_.extend(("f", g.lean), g.t)
                        self.reads.add("s")
                        return [], p_.extend(("i", V("s.%s'i" % f.lean, ATOM)), p_.t.elem)
                    if isinstance(target, tuple):
                        # --reachable: a member of a World object (`public_origin`, the front end's `common_EKF_origin`)
                        p_ = self.world_path(target[1], n)
                        for fl in target[2]:
                            g = next(x for x in p_.t.info.all_fields() if x.name == fl)
                            p_ = p_.extend(("f", g.lean), g.t)
                        return [], p_
                    return [], self.world_path(target, n)
                return [], Path(("s",), "s", [("f", f.lean)], f.t)
            r = self.resolve_path(kids(n)[0])
            if r is None:
                return None
            pre, bp = r
            if MISSION[0] and bp.t is not None and bp.t.kind == "record" and \
                    (getattr(bp.t.info, "byte_union", False) or (bp.steps and bp.steps[-1][0] == "ub")):
                return pre, self.byte_view_member(bp, n)     # --mission: a member of a byte union, or of a struct viewed in one
            if bp.t is not None and bp.t.kind == "int" and bp.root[0] == "var" and not bp.steps and bp.root[1] in self.unions:
                ui = self.unions[bp.root[1]]
                if n.get("referencedMemberDecl") not in ui.members:
                    raise Reject(n, "member `%s` of a union" % n.get("name"))
                return pre, Path(bp.root, bp.root_text, [("b", ui.members[n["referencedMemberDecl"]][1])],
                                 ui.members[n["referencedMemberDecl"]][1])
            if EKF_TYPES[0] and bp.t is not None and getattr(bp.t, "bu", None) is not None:
                bu, mid = bp.t.bu, n.get("referencedMemberDecl")
                if mid == bu.value_id:
                    return pre, Path(bp.root, bp.root_text, bp.steps, bu.word)      # `.value`: the integer
                if mid == bu.struct_id:
                    ft = CType("bits")
                    ft.bu = bu
                    return pre, Path(bp.root, bp.root_text, bp.steps, ft)           # `.flags`: its bits
                if mid in bu.bits and isinstance(bu.bits[mid], tuple):
                    off, w, ft = bu.bits[mid]
                    return pre, bp.extend(("bitf", (off, w, bu.word, ft)), ft)
                if mid in bu.bits:
                    return pre, bp.extend(("bit", (bu.bits[mid], bu.word)), BOOL)   # an anonymous struct's bit
                raise Reject(n, "member `%s` of a bit union" % n.get("name"))
            if EKF_TYPES[0] and bp.t is not None and bp.t.kind == "bits":
                mid = n.get("referencedMemberDecl")
                if mid not in bp.t.bu.bits:
                    raise Reject(n, "member `%s` of a bit union's flags" % n.get("name"))
                if isinstance(bp.t.bu.bits[mid], tuple):
                    off, w, ft = bp.t.bu.bits[mid]      # --front-ends: a field of w bits at bit off
                    if ft.kind == "enum":
                        ft.info.used_ofInt = True
                    return pre, bp.extend(("bitf", (off, w, bp.t.bu.word, ft)), ft)
                return pre, bp.extend(("bit", (bp.t.bu.bits[mid], bp.t.bu.word)), BOOL)
            if bp.t is None or bp.t.kind != "record":
                return None
            f = bp.t.info.field_by_id(n["referencedMemberDecl"])
            if f is None:
                raise Reject(n, "member `%s`" % n.get("name"))
            if f.category == "param" and bp.root == ("w",) and len(bp.steps) == 1:
                # a parameter of a World object: its Params field
                return pre, Path(("w",), "w", [("f", bp.steps[0][1] + "'p"), ("f", f.lean)], f.t)
            if WORLD_PTRS[0] and f.category == "param" and bp.root == ("s",) and not bp.steps:
                return pre, Path(("p",), "p", [("f", f.lean)], f.t)     # a parameter of this object, named through the World
            if f.category != "state":
                raise Reject(n, "member `%s` of a nested object, which is a parameter or a boundary member" % n.get("name"))
            return pre, bp.extend(("f", f.lean), f.t)
        if WORLD[0] and k in ("CallExpr", "UnaryOperator", "CXXMemberCallExpr") and self.u.accessors:
            t = accessor_target(self.u, n)
            if t is not None:
                return [], self.world_path(t, n)     # `AP::rtc()`, `*AP_RTC::get_singleton()`: the World object
            if WORLD_PTRS[0] and k in ("CallExpr", "CXXMemberCallExpr"):
                body = accessor_body(self.u, n)
                if body is not None:
                    return self.resolve_path(body)  # `AP::dal()`: `*AP_DAL::get_singleton()` (the call allocates on first use)
        if WORLD_PTRS[0] and k == "UnaryOperator" and n.get("opcode") == "*" and self.obj_type(kids(n)[0]) is not None:
            return self.ptr_deref_path(kids(n)[0], self.obj_type(kids(n)[0]), n)     # `*p` of a World pointer
        if k == "CXXOperatorCallExpr" and RING_BUFFERS[0]:
            r = self.rb_index_path(n)
            if r is not None:
                return r
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
        if EKF_ARRAYS[0] and k == "CXXConstCastExpr" and kids(n):
            return self.resolve_path(kids(n)[0])     # `const_cast<const Matrix24 &>(Pmut)` (EKF3's `P`): the object
        if k == "ArraySubscriptExpr" and EKF_ARRAYS[0]:
            r = self.md_subscript(n)
            if r is not None:
                return r
        if k == "ArraySubscriptExpr":
            base, idx = kids(n)
            sb = strip_object(base)
            if sb.get("kind") == "DeclRefExpr" and sb["referencedDecl"]["id"] in self.array_views:
                name, t = self.vars[sb["referencedDecl"]["id"]]
                pre_i, nat = self.nat_index(idx)
                return pre_i, Path(("var", sb["referencedDecl"]["id"]), name, [("i", nat)], t.elem)
            if WORLD_PTRS[0] and not (base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay"):
                pt = self.obj_type(base)
                if pt is not None:
                    # `core[i]` of a pointer into heap objects of one class (placement new into allocated
                    # memory): the object i places after the one it points to
                    return self.ptr_deref_path(base, pt, n, idx)
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

    def byte_view_member(self, bp, n):
        """--mission: the Path of member n of the object at bp, which is a byte union or is viewed in the bytes of one:
        the union's bytes at the member's offset (clang's record layout: mav_record_layout; a union's members at 0),
        a bit-field as its bits there; a byte-array member covering the whole union is the bytes themselves."""
        mid = n.get("referencedMemberDecl")
        rec = bp.t.info
        if bp.steps and bp.steps[-1][0] == "ub":
            off = bp.steps[-1][1][0]
            base = Path(bp.root, bp.root_text, bp.steps[:-1], None)
        else:
            off = 0
            if not rec.fields:
                raise Reject(n, "union `%s` without a layout" % rec.cxx)
            base = bp.extend(("f", "bytes"), rec.fields[0].t)
        if getattr(rec, "byte_union", False):
            f = rec.union_members.get(mid)
            if f is None:
                raise Reject(n, "member `%s` of a union" % n.get("name"))
            fo, bitf = 0, None
        else:
            f = rec.field_by_id(mid)
            if f is None or f.category != "state":
                raise Reject(n, "member `%s` of a struct viewed in a union's bytes" % n.get("name"))
            record_layout(rec, n)
            ent = next((x for x in getattr(rec, "field_layout", []) if x[0] == f.name), None)
            if ent is None:
                raise Reject(n, "member `%s` without a layout" % n.get("name"))
            fo, bitf = (0, ent) if ent[3] else (ent[1], None)
        if bitf is not None:
            return Path(base.root, base.root_text, base.steps + [("ubf", (off, bitf[1], bitf[2], f.t))], f.t)
        size = rec.union_size if getattr(rec, "byte_union", False) and off == 0 and not (bp.steps and bp.steps[-1][0] == "ub") else None
        if f.t.kind == "array" and f.t.elem in (UINT8, CHAR) and off + fo == 0 and size == f.t.n:
            return base     # `packed_content.bytes` (uint8_t[12] of a 12-byte union): the bytes themselves
        return Path(base.root, base.root_text, base.steps + [("ub", (off + fo, f.t))], f.t)

    def read_path(self, p, n, check_init=True):
        if p.steps and p.steps[-1][0] == "row":
            raise Reject(n, "row of a multidimensional array used as a value")
        if p.t is not None and p.t.kind == "bits":
            raise Reject(n, "the bit-fields of a bit union used as a value")
        root = p.root
        if root[0] == "bview":
            return V(p.text(), ATOM)        # --byte-objects: the bytes of an object, in a temporary
        if root[0] == "lit":
            return V(p.text(), ATOM)        # --c-strings: a pointer value's bytes (a string literal, a temporary)
        if root[0] == "var":
            rid = root[1]
            if check_init and rid in self.uninit and self.da is not DIVERGE and rid not in self.da and not UNINIT_READS[0]:
                raise Reject(n, "read of `%s`, which may be uninitialized" % p.root_text)
            self.read.add(rid)
        else:
            self.reads.add(root[0])
        return V(p.text(), APP if p.steps and p.steps[-1][0] == "b" else ATOM)

    def write_path(self, p, value, n):
        """The line that stores value at p."""
        if p.steps and p.steps[-1][0] == "row":
            raise Reject(n, "assignment to a row of a multidimensional array")
        root = p.root
        if root[0] == "lit":
            raise Reject(n, "write through a pointer to a string literal or a pointer value")
        if root[0] == "bview":
            # --byte-objects: the bytes, then the object they represent
            xp = root[2]
            back = self.write_path(xp, V(value_from_bytes(root[1], "0", xp.t, n), ATOM), n)
            return "%s := %s\n%s" % (p.root_text, update_text(p.root_text, p.steps, value), back)
        if root[0] == "var":
            rid = root[1]
            if MAVLINK[0] and rid in self.u.globals:
                self.mutable.add(rid)       # --mavlink: a file-scope variable written (returned to the caller)
                self.gl_use.setdefault(rid, set()).add("w")
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
        if any(k in ("v", "fi", "fm", "av") for k, _ in p.steps) and not SIMPLE.match(value.text):
            # a write through a view names the value once per viewed field: bind it first (one
            # entry of two lines; Body.finish indents the second like the first)
            t = self.temp()
            return "let %s := %s\n%s := %s" % (t, value.text, p.root_text, update_text(p.root_text, p.steps, V(t, ATOM))) + self.held_sync(root)
        if EKF_ARRAYS[0] and inplace_wanted(p.steps):
            return "\n".join(inplace_lines(p.root_text, p.steps, value, self.temp)) + self.held_sync(root)
        return "%s := %s" % (p.root_text, update_text(p.root_text, p.steps, value)) + self.held_sync(root)

    def held_sync(self, root):
        """--c-strings: the lines (each after a newline) that keep an object holding a pointer
        variable's array (held_member_type) and the variable in step after a write of either."""
        if root[0] != "var":
            return ""
        out = ""
        for fl, pth in self.held.get(root[1], []):
            self.read.add(root[1])
            out += "\n%s := %s.%s" % (pth.root_text, self.vars[root[1]][0], fl)
        for oname, fl in self.held_by.get(root[1], []):
            out += "\n%s := { %s with %s := %s }" % (oname, oname, fl, self.vars[root[1]][0])
        return out

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

    def union_literal_member(self, n):
        """`((union{float _f; uint32_t _i;}){f})._i` (musl's asuint, libm.h): the member read of a
        union compound literal initialized through another member: the bit-pattern conversion."""
        base = strip_parens(kids(n)[0])
        if base.get("kind") != "CompoundLiteralExpr" or not kids(base):
            return None
        init = strip_parens(kids(base)[0])
        if init.get("kind") != "InitListExpr" or "field" not in init or len(kids(init)) != 1:
            raise Reject(n, "compound literal")
        src_t = parse_type_str(init["field"]["type"]["qualType"], init["field"]["type"].get("desugaredQualType", init["field"]["type"]["qualType"]), init)
        dst_t = ctype_of(n)
        for t in (src_t, dst_t):
            if t.kind not in ("float", "double", "int") or (t.kind == "int" and t.usize):
                raise Reject(n, "union compound literal with a member of type `%s`" % t.cname)
        width = lambda t: 32 if t.kind == "float" else 64 if t.kind == "double" else t.bits
        if width(src_t) != width(dst_t):
            raise Reject(n, "union compound literal read through a member of another width")
        pre, v = self.expr(kids(init)[0])
        if src_t == dst_t:
            return pre, v
        return pre, bits_view(bits_of(v, src_t), dst_t)

    def e_MemberExpr(self, n):
        if strip_parens(kids(n)[0]).get("kind") == "CompoundLiteralExpr":
            return self.union_literal_member(n)
        f = self.this_field(n)
        if f is not None and f.category == "boundary":
            raise Reject(n, "boundary object `%s` used as a value" % n["name"])
        bo = self.boundary_obj(kids(n)[0])
        if bo is not None and FRONT_ENDS[0]:
            wv = self.boundary_world_ptr(n)
            if wv is not None:
                return [], wv
        if bo is not None:
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
        if POINTER_PARAMS[0]:
            r = self.byte_view(n)
            if r is not None:
                return r
        r = self.resolve_path(n)
        if r is not None:
            pre, p = r
            return pre, self.read_path(p, n)
        base = kids(n)[0]
        if base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay":
            arr = strip_parens(kids(base)[0])
            if (arr.get("kind") == "DeclRefExpr" and (arr["referencedDecl"]["id"] in self.u.consts or
                                                      (self.u.decl(arr["referencedDecl"]["id"]) or {}).get("previousDecl") in self.u.consts or
                                                      any(c["decl"].get("previousDecl") == arr["referencedDecl"]["id"] for c in self.u.consts.values()))) or \
                    (C_MODE[0] and arr.get("kind") in ("MemberExpr", "ArraySubscriptExpr")) or \
                    (arr.get("kind") == "ArraySubscriptExpr" and ctype_of(arr).kind == "array"):
                # (a row of a two-dimensional constant table: `declination_table[i][j]`)
                # (C: an array member of a constant table, musl's `__exp2f_data.tab[i]`)
                pre_a, a = self.expr(arr)
                pre_i, nat = self.nat_index(kids(n)[1])
                if arr.get("kind") == "ArraySubscriptExpr" and not C_MODE[0]:
                    a = V("(%s)" % a.text, ATOM)    # `(t[i]!)[j]!`: Lean does not chain `t[i]![j]!`
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
        if not m or (m.group(1).startswith("const ") and not FRONT_ENDS[0]) or body is None:
            return None
        if m.group(1).startswith("const ") and any(
                r.get("kind") == "DeclRefExpr" and r.get("referencedDecl", {}).get("id") == p["id"] and
                (self.u.parent.get(r["id"]) or {}).get("kind") == "UnaryOperator" and
                (self.u.parent.get((self.u.parent.get(r["id"]) or {}).get("id")) or {}).get("kind") == "BinaryOperator" and
                (self.u.parent.get((self.u.parent.get(r["id"]) or {}).get("id")) or {}).get("opcode") == "=" for r in walk(body)):
            return None
        try:
            pt = parse_type_str(m.group(1)[len("const "):] if m.group(1).startswith("const ") else m.group(1),
                                m.group(1)[len("const "):] if m.group(1).startswith("const ") else m.group(1), p)
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
            if FRONT_ENDS[0] and up.get("kind") == "ImplicitCastExpr" and up.get("castKind") == "PointerToBoolean":
                continue        # (--front-ends: `if (scaling)`, AP_Compass_Backend.cpp:173)
            return None
        return pt if uses else None

    def pointer_param(self, p, body):
        """C: for a parameter `T *p` (T a number) that the body uses only as `*p`, or only as `p[i]`
        and as an argument for a pointer parameter: ("scalar" or "array", T, whether the body may
        write through it), else None."""
        q = p.get("type", {}).get("qualType", "").strip()
        dq = p.get("type", {}).get("desugaredQualType", q).strip()
        m = re.match(r"^(const )?([\w ]+?) ?\*$", dq)
        if not m or body is None:
            return None
        try:
            et = parse_type_str(m.group(2), m.group(2), p)
        except Reject:
            return None
        if et.kind not in ("float", "double", "int"):
            return None
        modes, written = set(), False
        for r in walk(body):
            if r.get("kind") != "DeclRefExpr" or r.get("referencedDecl", {}).get("id") != p["id"]:
                continue
            up, child = self.u.parent.get(r["id"]), r
            while up is not None and (up.get("kind") == "ParenExpr" or (up.get("kind") == "ImplicitCastExpr" and up.get("castKind") in ("LValueToRValue", "NoOp"))):
                up, child = self.u.parent.get(up["id"]), up
            if up is None:
                return None
            if up.get("kind") == "UnaryOperator" and up.get("opcode") == "*":
                modes.add("scalar")
            elif up.get("kind") == "ArraySubscriptExpr" and kids(up)[0] is child:
                modes.add("array")
            elif up.get("kind") == "CallExpr" and child in kids(up)[1:]:
                modes.add("array")
                written = written or not m.group(1)
                continue
            else:
                return None
            lv, top = up, self.u.parent.get(up["id"])
            while top is not None and top.get("kind") == "ParenExpr":
                lv, top = top, self.u.parent.get(top["id"])
            if top is not None and ((top.get("kind") in ("BinaryOperator", "CompoundAssignOperator") and top.get("opcode", "").endswith("=")
                                     and top.get("opcode") not in ("==", "!=", "<=", ">=") and kids(top)[0] is lv)
                                    or (top.get("kind") == "UnaryOperator" and top.get("opcode") in ("++", "--"))):
                written = True
        if len(modes) != 1:
            return None
        if written and m.group(1):
            return None
        return modes.pop(), et, written

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
        if e.get("kind") == "DeclRefExpr" and (e["referencedDecl"]["id"] in self.nullable or e["referencedDecl"]["id"] in self.ptr_scalars):
            return e["referencedDecl"]["id"]
        return None

    # -- phase 2: pointers into arrays (--pointer-params, README.md "Phase 2") ----------------
    # A pointer parameter `T *p` / `const T *p` / `T p[]` (T a number type) is the array the caller
    # passes (`Array T`), returned after the result if the body writes through it, as for `T &`; a
    # parameter used only as `*p` is the scalar the caller passes as `&x`. A pointer that the body
    # moves (`p++`, `p += k`) and a local pointer into an array (`const uint8_t *pend = p + len`)
    # are an offset (`p'o : Nat`) into that array. A local pointer that holds only arrays of its own
    # (`new T[k]`, or the result of a function that returns such a pointer) is a local array.

    def pp_pointee(self, d, key="type"):
        """For a declaration or expression of type `T *` or `const T *`: (pointee CType, is const),
        T a number type, a plain struct or `void`; else None."""
        t = d.get(key) or {}
        q = t.get("qualType", "").strip()
        dq = t.get("desugaredQualType", q).strip()
        if C_STRINGS[0] and (q in ("va_list", "__builtin_va_list", "std::va_list") or "__va_list" in dq):
            return None                     # `va_list` (a `char *` on this target) is not a pointer of the model
        m = re.match(r"^(const )?(?:struct )?([\w:<>, ]+?) ?\*( ?const)?$" if C_STRINGS[0] else r"^(const )?(?:struct )?([\w:<>, ]+?) ?\*( const)?$", dq)
        if not m:
            return None
        if m.group(2) == "void":
            return VOID, bool(m.group(1))
        try:
            et = parse_type_str(m.group(2), m.group(2), d)
        except Reject:
            return None
        if not (et.kind in ("float", "double", "int") or (et.kind == "record" and et.info.kind == "plain")):
            return None
        if FRONT_ENDS[0] and et.kind == "record" and d.get("kind") == "VarDecl" and kids(d) and \
                strip_object(kids(d)[0]).get("kind") == "UnaryOperator" and strip_object(kids(d)[0]).get("opcode") == "&":
            return None     # --front-ends: a local pointer to one object (`dstate = &detect_state[instance]`): an alias (local_decl)
        return et, bool(m.group(1))

    def pp_climb(self, node):
        """(up, child): the node that uses the value of node, above parentheses and the casts that
        keep a pointer's value (lvalue to rvalue, added const, to `void *` for a library call)."""
        up, child = self.u.parent.get(node["id"]), node
        while up is not None and (up.get("kind") == "ParenExpr" or (up.get("kind") == "ImplicitCastExpr" and up.get("castKind") in ("LValueToRValue", "NoOp", "BitCast"))):
            up, child = self.u.parent.get(up["id"]), up
        return up, child

    def pp_callee_param(self, call, child):
        """The ParmVarDecl (or None for a library function without a declaration in the AST) that
        argument `child` of `call` binds, and the callee's name."""
        c = strip_parens(kids(call)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_parens(kids(c)[0])
        d = self.u.decl(c.get("referencedDecl", {}).get("id") or c.get("referencedMemberDecl"))
        args = kids(call)[1:]
        i = next((j for j, a in enumerate(args) if a is child), None)
        if d is None or i is None:
            return None, None
        ps = [p for p in kids(d) if p.get("kind") == "ParmVarDecl"]
        return (ps[i] if i < len(ps) else None), d.get("name")

    def pp_lv_written(self, lv):
        """Is the lvalue lv (`*p`, `p[i]`) written: assigned, stepped, bound to a non-const
        reference or passed by address to a non-const pointer parameter?"""
        up, c = self.u.parent.get(lv["id"]), lv
        while up is not None and (up.get("kind") == "ParenExpr" or (up.get("kind") == "ImplicitCastExpr" and up.get("castKind") == "NoOp")):
            up, c = self.u.parent.get(up["id"]), up
        if up is None:
            return False
        k = up.get("kind")
        if k == "BinaryOperator" and up.get("opcode") == "=" and kids(up)[0] is c:
            return True
        if k == "CompoundAssignOperator" and kids(up)[0] is c:
            return True
        if k == "UnaryOperator" and up.get("opcode") in ("++", "--"):
            return True
        if k == "MemberExpr":
            return self.pp_lv_written(up)
        if k == "UnaryOperator" and up.get("opcode") == "&":
            r = self.pp_uses(up)
            return bool(r and r[1])
        if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr") and c is not kids(up)[0]:
            p, _ = self.pp_callee_param(up, c)
            q = p["type"]["qualType"].strip() if p is not None else "&"
            return q.endswith("&") and not q.startswith("const ")
        return False

    def pp_uses(self, node):
        """How the pointer value `node` is used: (kinds, written, moved), kinds a set of `deref`
        (`*p`), `sub` (`p[i]`), `move` (`p++`, `p += k`, `p = q`), `cmp` (compared with another
        pointer), `arg` (passed to a pointer parameter), `alias` (initializes a local pointer),
        `cast` (an explicit cast to a byte pointer). Returns None if the pointer is compared with a
        null pointer (a nullable out-pointer, not an array). Raises Reject for any other use."""
        up, child = self.pp_climb(node)
        k = up.get("kind") if up is not None else None
        op = up.get("opcode") if up is not None else None
        if k == "UnaryOperator" and op == "*":
            return {"deref"}, self.pp_lv_written(up), False
        if k == "ArraySubscriptExpr" and kids(up)[0] is child:
            return {"sub"}, self.pp_lv_written(up), False
        if k == "UnaryOperator" and op in ("++", "--"):
            ou, _ = self.pp_climb(up)
            if ou is not None and ou.get("kind") in ("CompoundStmt", "ForStmt", "WhileStmt", "DoStmt", "IfStmt"):
                return {"move"}, False, True        # a statement (or a loop's step)
            r = self.pp_uses(up)                    # `*p++`: the value before (or after) the step is used
            if r is None:
                return None
            return r[0] | {"move"}, r[1], True
        if k == "CompoundAssignOperator" and op in ("+=", "-=") and kids(up)[0] is child:
            return {"move"}, False, True
        if k == "BinaryOperator" and op == "=" and kids(up)[0] is child:
            return {"move"}, False, True
        if k == "BinaryOperator" and op in ("+", "-") and self.pp_pointee(up) is not None:
            return self.pp_uses(up)                 # `p + k`: a pointer into the same array
        if k == "BinaryOperator" and op in ("==", "!=", "<", ">", "<=", ">="):
            if MAVLINK[0] and op in ("==", "!=") and any(self.is_null(x) for x in kids(up)):
                return {"nullcmp"}, False, False    # --mavlink: an array pointer tested for null (it never is: pp_null_param)
            if any(self.is_null(x) for x in kids(up)):
                return None
            return {"cmp"}, False, False
        if FRONT_ENDS[0] and k == "ImplicitCastExpr" and up.get("castKind") == "PointerToBoolean":
            return None             # --front-ends: `if (scale)`, a null test (a nullable pointer, not an array)
        if k in ("CallExpr", "CXXMemberCallExpr") and child in kids(up)[1:]:
            p, name = self.pp_callee_param(up, child)
            if name in ("memset", "memcpy") and child is kids(up)[1]:
                return {"arg"}, True, False
            q = p["type"].get("desugaredQualType", p["type"]["qualType"]).strip() if p is not None else ""
            return {"arg"}, q.endswith("*") and not q.startswith("const "), False
        if k == "CXXDeleteExpr":
            return {"delete"}, False, False
        if C_STRINGS[0] and k == "CXXCtorInitializer":
            # `_str(str)`: the pointer is held by a member of the object (held_member_type); the
            # constructor does not write through it
            f = self.u.decl(up.get("anyInit", {}).get("id"))
            if f is None or held_member_type(f) is None:
                raise Reject(node, "pointer `%s` stored in a data member that is not a `T *const` member" % (self.u.text_of(node) or "?"))
            return {"held"}, False, False
        if C_STRINGS[0] and k == "CXXConstructExpr" and child in kids(up):
            if self.held_param(up, kids(up).index(child)) is None:
                raise Reject(node, "pointer `%s` passed to a constructor that does not store it in a `T *const` member" % (self.u.text_of(node) or "?"))
            return {"arg"}, True, False         # the object holds the array, and may write it
        if k == "ReturnStmt":
            return {"return"}, False, False     # (only an array of the function's own: pp_fresh_return)
        if k == "VarDecl":
            w = False
            body = next((c for c in kids(self.fn or {}) if c.get("kind") == "CompoundStmt"), None)
            for r in walk(body or {}):
                if r.get("kind") == "DeclRefExpr" and r.get("referencedDecl", {}).get("id") == up["id"]:
                    ru = self.pp_uses(r)
                    w = w or (ru is not None and ru[1])
            return {"alias"}, w, False
        if k in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr") and self.pp_pointee(up) is not None:
            r = self.pp_uses(up)
            if r is None:
                return None
            return r[0] | {"cast"}, r[1], r[2]
        what = self.u.text_of(up) if up is not None else None
        raise Reject(node, "pointer `%s` used other than by `*p`, `p[i]`, a step (`p++`, `p += k`), a comparison with a pointer into the same array, as an argument for a pointer parameter, or as the initializer of a local pointer%s" %
                     (self.u.text_of(node) or "?", " (in `%s`)" % comment_safe(what) if what else ""))

    @staticmethod
    def off_name(name):
        """The Lean name of the offset of pointer `name` (`p'o`; `«end'o»` for an escaped identifier)."""
        return "«%s'o»" % name[1:-1] if name.startswith("«") else name + "'o"

    def pp_classify(self, d, body):
        """(mode, pointee, written, moved, const) for a pointer parameter or local d: mode `scalar`
        (only `*p`) or `array`; None if d is not a pointer to a number or plain struct, or is
        compared with a null pointer."""
        pe = self.pp_pointee(d)
        if pe is None or body is None:
            return None
        et, is_const = pe
        kinds, written, moved = set(), False, False
        for r in walk(body):
            if r.get("kind") != "DeclRefExpr" or r.get("referencedDecl", {}).get("id") != d["id"]:
                continue
            u = self.pp_uses(r)
            if u is None:
                return None
            kinds |= u[0]
            written = written or u[1]
            moved = moved or u[2]
        if et.kind == "void":
            # `const void *data` read as bytes: `(const uint8_t *)data` (crc8_dvb_s2_update)
            targets = set()
            for r in walk(body):
                if r.get("kind") == "DeclRefExpr" and r.get("referencedDecl", {}).get("id") == d["id"]:
                    up, _ = self.pp_climb(r)
                    if MAVLINK[0] and up is not None and (
                            (up.get("kind") == "CallExpr" and self.pp_callee_param(up, _)[1] in ("memcpy", "memset", "memcmp")) or
                            (up.get("kind") == "BinaryOperator" and up.get("opcode") in ("==", "!=") and any(self.is_null(x) for x in kids(up)))):
                        targets.add((CType("int", 8, False), False))    # --mavlink: `mav_array_memcpy(void *dest, const void *src, n)`
                        continue
                    if up is None or up.get("kind") not in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr"):
                        raise Reject(r, "`void *` parameter `%s` used other than through a cast to a byte pointer" % d.get("name"))
                    targets.add(self.pp_pointee(up))
            if len(targets) != 1 or next(iter(targets))[0] != CType("int", 8, False):
                raise Reject(d, "`void *` parameter `%s` not read as `uint8_t` bytes" % d.get("name"))
            et = CType("int", 8, False)
        mode = "scalar" if kinds == {"deref"} else "array"
        if MAVLINK[0] and kinds and kinds <= {"deref", "arg"} and "arg" in kinds and not moved and self.pp_args_scalar(d, body):
            mode = "scalar"     # --mavlink: also passed on to scalar pointer parameters (`crc_accumulate(*p++, crcAccum)`)
        return mode, et, written, moved, is_const

    def pp_args_scalar(self, d, body):
        """--mavlink: whether every call that pointer d is passed to binds it to a parameter of a translated
        function that is used only as `*p` (a scalar)."""
        for r in walk(body):
            if r.get("kind") != "DeclRefExpr" or r.get("referencedDecl", {}).get("id") != d["id"]:
                continue
            up, child = self.pp_climb(r)
            if up is None or up.get("kind") != "CallExpr":
                continue
            p, name = self.pp_callee_param(up, child)
            if p is None:
                return False
            c = strip_casts(kids(up)[0])
            fd = self.u.function_for(self.u.decl((c.get("referencedDecl") or {}).get("id")))
            fb = next((x for x in kids(fd or {}) if x.get("kind") == "CompoundStmt"), None)
            fp = next((x for x in kids(fd or {}) if x.get("kind") == "ParmVarDecl" and x.get("name") == p.get("name")), None)
            if fb is None or fp is None:
                return False
            c2 = Body(self.u, fd, None, home=self.home).pp_classify(fp, fb)
            if c2 is None or c2[0] != "scalar":
                return False
        return True

    def pp_param(self, p, body):
        """setup_params for a pointer parameter (--pointer-params): the entry (p, name, type, ref),
        or None if p is not such a parameter."""
        c = self.pp_classify(p, body)
        if c is None:
            return None
        mode, et, written, moved, is_const = c
        if "name" not in p:
            raise Reject(p, "unnamed parameter")
        if written and is_const:
            raise Reject(p, "write through `const` pointer `%s`" % p["name"])
        pn = self.ident(p["name"], p)
        pt = et if mode == "scalar" else CType("array", elem=et, n=0)
        self.vars[p["id"]] = (pn, pt)
        self.declared.append((p["id"], pn))
        if mode == "scalar":
            self.ptr_scalars.add(p["id"])
        elif ARRAY_OFFSETS[0]:
            # --array-offsets: the array the pointer points into and the offset of the element it points to
            # (`p'o : Nat`, a parameter after `p`): the caller passes its array whole, so writes are in place
            self.ptrs[p["id"]] = PtrVar(Path(("var", p["id"]), pn, [], pt), self.off_name(pn), et, "param")
            self.off_params.add(p["id"])
            if moved:
                self.prologue.append("let mut %s := %s  -- the offset of pointer `%s` moves" % (self.off_name(pn), self.off_name(pn), p["name"]))
            if not written:
                self.mutable.discard(p["id"])
        else:
            self.ptrs[p["id"]] = PtrVar(Path(("var", p["id"]), pn, [], pt), self.off_name(pn) if moved else None, et, "param")
            if moved:
                self.prologue.append("let mut %s : Nat := 0  -- the offset of pointer `%s` into the array passed" % (self.off_name(pn), p["name"]))
                if not written:
                    self.mutable.discard(p["id"])     # only its offset changes
            else:
                self.array_views.add(p["id"])
        if written:
            self.outs.append((p["id"], pn, pt))
            self.mutable.add(p["id"])
            return p, pn, pt, "mut"
        return p, pn, pt, "cptr"

    def pp_roots(self, e):
        """The ids of the variables a pointer-valued expression points into (syntactically)."""
        e = strip_parens(e)
        k = e.get("kind")
        if k in ("ImplicitCastExpr", "CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr") and kids(e):
            return self.pp_roots(kids(e)[0])
        if k == "BinaryOperator" and e.get("opcode") in ("+", "-"):
            return set().union(*[self.pp_roots(x) for x in kids(e) if self.pp_pointee(x) is not None or x.get("castKind") == "ArrayToPointerDecay"])
        if k == "UnaryOperator" and e.get("opcode") in ("++", "--"):
            return self.pp_roots(kids(e)[0])
        if k == "UnaryOperator" and e.get("opcode") == "&":
            r = lvalue_root(kids(e)[0])
            return {r["referencedDecl"]["id"]} if r is not None else set()
        if k == "DeclRefExpr":
            return {e["referencedDecl"]["id"]}
        if k in ("MemberExpr", "ArraySubscriptExpr"):
            r = lvalue_root(e)
            return {r["referencedDecl"]["id"]} if r is not None else set()
        return set()

    def pp_mutable(self, body):
        """Variables written through a pointer (`*q = v`, `q[i] = v`, an argument for a written pointer
        parameter, `memset`/`memcpy`) and, for a local pointer into another array, that array: they
        are `let mut` (Body.mutable, computed before the body is translated)."""
        out = set()
        alias = {}
        for m in walk(body or {}):
            if m.get("kind") == "VarDecl" and kids(m) and (self.pp_pointee(m) is not None or (
                    m["type"]["qualType"].rstrip().endswith("&") and not m["type"]["qualType"].startswith("const "))):
                alias[m["id"]] = self.pp_roots(kids(m)[0])
            k = m.get("kind")
            tgt = None
            if k == "BinaryOperator" and m.get("opcode") == "=" or k == "CompoundAssignOperator":
                tgt = kids(m)[0]
            elif k == "UnaryOperator" and m.get("opcode") in ("++", "--"):
                tgt = kids(m)[0]
            if tgt is not None:
                t = strip_object(tgt)
                while t.get("kind") == "MemberExpr":
                    t = strip_object(kids(t)[0])
                if t.get("kind") == "UnaryOperator" and t.get("opcode") == "*":
                    out |= self.pp_roots(kids(t)[0])
                elif t.get("kind") == "ArraySubscriptExpr" and kids(t)[0].get("castKind") != "ArrayToPointerDecay":
                    out |= self.pp_roots(kids(t)[0])
            if k == "CXXConstructExpr" and C_STRINGS[0]:
                for i, a in enumerate(kids(m)):
                    if self.pp_pointee(a) is not None and self.held_param(m, i) is not None:
                        out |= self.pp_roots(a)
            if k in ("CallExpr", "CXXMemberCallExpr"):
                for a in kids(m)[1:]:
                    if self.pp_pointee(a) is None and a.get("castKind") != "BitCast":
                        continue
                    p, name = self.pp_callee_param(m, a)
                    if name in ("memset", "memcpy") and a is kids(m)[1]:
                        out |= self.pp_roots(a)
                        continue
                    q = p["type"].get("desugaredQualType", p["type"]["qualType"]).strip() if p is not None else ""
                    if q.endswith("*") and not q.startswith("const "):
                        out |= self.pp_roots(a)
                    elif q.endswith("&") and not q.startswith("const "):
                        out |= self.pp_roots(a)
        changed = True
        while changed:
            changed = False
            for a, roots in alias.items():
                if a in out and not roots <= out:
                    out |= roots
                    changed = True
        return out

    def pp_fresh(self, e):
        """Is e a fresh array: `new T[k]`, or a call of a function that returns one?"""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("NoOp", "BitCast"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") == "CXXNewExpr":
            return True
        if e.get("kind") == "CallExpr":
            c = strip_parens(kids(e)[0])
            while c.get("kind") == "ImplicitCastExpr":
                c = strip_parens(kids(c)[0])
            d = self.u.decl(c.get("referencedDecl", {}).get("id"))
            target = self.u.function_for(d) if d is not None else None
            return target is not None and pp_fresh_return(self.u, target) is not None
        return False

    def sel_target(self, e):
        """--mission: the operand x of `&x` (x a member of a local object or a local scalar), else None."""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("NoOp",):
            e = strip_parens(kids(e)[0])
        if e.get("kind") != "UnaryOperator" or e.get("opcode") != "&":
            return None
        x = strip_parens(kids(e)[0])
        root = x
        while root.get("kind") == "MemberExpr" and not root.get("isArrow"):
            root = strip_parens(kids(root)[0])
        if root.get("kind") != "DeclRefExpr" or root["referencedDecl"]["id"] not in self.vars or root["referencedDecl"]["id"] in self.ptrs:
            return None
        return x

    def sel_local(self, d):
        """--mission: `float *selector = nullptr;` then `selector = &packet.param1;` ... and only `*selector` read and
        `selector != nullptr` tested (AP_Mission.cpp:1078): a pointer to one of the members of a local object (or a
        local scalar), held as which one (0: null, k: the k-th distinct target); `*selector` reads that member as it is
        when read. Lines, or None if d is not such a pointer."""
        q = d.get("type", {}).get("qualType", "")
        if not q.endswith("*") or q.startswith("const ") or q.count("*") != 1:
            return None
        body = next((c for c in kids(self.fn or {}) if c.get("kind") == "CompoundStmt"), None)
        init = kids(d)[0] if kids(d) else None
        if init is None or strip_object(init).get("kind") not in ("CXXNullPtrLiteralExpr", "GNUNullExpr") and \
                not (strip_object(init).get("kind") == "ImplicitCastExpr" and strip_object(init).get("castKind") == "NullToPointer"):
            if init is None or self.sel_target(init) is None:
                return None
        targets = []
        for m in walk(body or {}):
            if m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == d["id"]:
                up = self.u.parent.get(m["id"])
                while up is not None and up.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                    up = self.u.parent.get(up["id"])
                if up is None:
                    return None
                if up.get("kind") == "BinaryOperator" and up.get("opcode") == "=" and strip_object(kids(up)[0]) is m:
                    x = self.sel_target(kids(up)[1])
                    if x is None:
                        return None
                    txt = self.u.text_of(x)
                    if txt not in targets:
                        targets.append(txt)
                    continue
                if up.get("kind") == "UnaryOperator" and up.get("opcode") == "*":
                    continue
                if up.get("kind") == "BinaryOperator" and up.get("opcode") in ("!=", "==") and \
                        any(strip_object(k).get("kind") in ("CXXNullPtrLiteralExpr", "GNUNullExpr") or
                            (strip_object(k).get("kind") == "ImplicitCastExpr" and strip_object(k).get("castKind") == "NullToPointer") for k in kids(up)):
                    continue
                return None
        if not targets:
            return None
        rid = d["id"]
        name = self.fresh_local(self.ident(d["name"], d), rid)
        self.vars[rid] = (name, UINT8)
        self.sel_ptrs[rid] = targets
        self.declared.append((rid, name))
        mut = "let mut" if rid in self.mutable else "let"
        if self.sel_target(init) is not None:
            return ["%s %s : UInt8 := %d  -- C++ `%s`: which member it points to (0: null)" % (mut, name, targets.index(self.u.text_of(self.sel_target(init))) + 1, comment_safe(d["name"]))]
        return ["%s %s : UInt8 := 0  -- C++ pointer `%s`: which member it points to (0: null; %s)" % (
            mut, name, comment_safe(d["name"]), comment_safe(", ".join("%d: `&%s`" % (k + 1, x) for k, x in enumerate(targets))))]

    def sel_ref(self, e):
        """--mission: the id of the selector pointer (sel_local) e names, else None."""
        e = strip_object(e)
        while e.get("kind") == "ImplicitCastExpr":
            e = strip_object(kids(e)[0])
        if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in self.sel_ptrs:
            return e["referencedDecl"]["id"]
        return None

    def sel_deref(self, rid, n):
        """--mission: `*selector`: the member it points to, read now (a match on which one)."""
        name, _ = self.vars[rid]
        body = next((c for c in kids(self.fn or {}) if c.get("kind") == "CompoundStmt"), None)
        alts, t = [], ctype_of(n)
        for k, txt in enumerate(self.sel_ptrs[rid]):
            x = next(m for m in walk(body) if m.get("kind") == "UnaryOperator" and m.get("opcode") == "&" and
                     self.u.text_of(strip_parens(kids(m)[0])) == txt)
            pre, p = self.resolve_path(strip_parens(kids(x)[0]))
            if pre:
                raise Reject(n, "`*%s` of a member with a computed path" % name)
            alts.append("| %d => %s" % (k + 1, self.read_path(p, n).text))
        return V("(match %s with %s | _ => %s)" % (name, " ".join(alts), zero_of(t, n).text), ATOM)

    def pp_local(self, d):
        """local_decl for a local pointer variable (--pointer-params): lines, or None if d is not one."""
        if MISSION[0]:
            r = self.sel_local(d)
            if r is not None:
                return r
        pe = self.pp_pointee(d)
        if pe is None:
            return None
        et, is_const = pe
        body = next((c for c in kids(self.fn or {}) if c.get("kind") == "CompoundStmt"), None)
        init = kids(d)[0] if kids(d) else None
        values = [init] if init is not None else []
        moved = False
        for m in walk(body or {}):
            if m.get("kind") == "BinaryOperator" and m.get("opcode") == "=":
                l = strip_object(kids(m)[0])
                if l.get("kind") == "DeclRefExpr" and l["referencedDecl"]["id"] == d["id"]:
                    values.append(kids(m)[1])
            if m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == d["id"]:
                if self.pp_uses(m) is None:
                    raise Reject(m, "local pointer `%s` compared with a null pointer" % d["name"])
                up, child = self.pp_climb(m)
                if up is not None and ((up.get("kind") == "UnaryOperator" and up.get("opcode") in ("++", "--")) or
                                       (up.get("kind") == "CompoundAssignOperator" and kids(up)[0] is child)):
                    moved = True
        name = self.ident(d["name"], d)
        rid = d["id"]
        if values and all(self.pp_fresh(v) for v in values):
            if moved:
                raise Reject(d, "local pointer `%s` to an array of its own that is moved (`++`, `+=`)" % d["name"])
            t = CType("array", elem=et, n=0)
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            self.array_views.add(rid)
            self.ptrs[rid] = PtrVar(Path(("var", rid), name, [], t), None, et, "owned")
            mut = "let mut" if rid in self.mutable else "let"
            if init is None:
                self.uninit.add(rid)
                return ["%s %s : %s := #[]  -- uninitialized in C++; assigned an array before every use" % (mut, name, t.lean)]
            pre, v = self.expr(init)
            return pre + ["%s %s : %s := %s" % (mut, name, t.lean, v.text)]
        if C_STRINGS[0] and is_const and (init is None or len(values) > 1 or any(self.cs_valueish(v) for v in values)):
            return self.cs_copy_local(d, et, init, moved)
        if init is None:
            raise Reject(d, "local pointer `%s` without an initializer that does not hold an array of its own (`new T[k]`)" % d["name"])
        for v in values[1:]:
            if self.pp_fresh(v):
                raise Reject(v, "local pointer `%s` assigned both a pointer into another array and an array of its own" % d["name"])
        r = self.ptr_ref(init)
        if r is None:
            raise Reject(init, "local pointer `%s` initialized with something other than a pointer into an array" % d["name"])
        pre, base, off = r
        if base.root[0] == "bview":
            xp = base.root[2]
            if xp.root[0] != "var" or xp.root[1] in self.mutable or is_const is False and any(
                    self.pp_uses(m)[1] for m in walk(body or {}) if m.get("kind") == "DeclRefExpr" and m["referencedDecl"]["id"] == d["id"]):
                raise Reject(init, "local pointer `%s` to the bytes of an object that is assigned or written through it (only read-only views of variables that do not change are translated)" % d["name"])
        if base.t is None or base.t.kind != "array" or not same_storage(base.t.elem, et):
            raise Reject(init, "local pointer `%s` into an array of another element type" % d["name"])
        oname = self.off_name(name)
        reassigned = len(values) > 1
        self.ptrs[rid] = PtrVar(base, oname, et, "alias")
        self.declared.append((rid, oname))
        self.read.add(rid)
        return pre + ["%s %s : Nat := %s  -- pointer `%s`: an offset into `%s`" %
                      ("let mut" if moved or reassigned else "let", oname, off.text if off is not None else "0", d["name"], base.text())]

    def cs_call(self, n, name, args):
        """--c-strings, --byte-objects: a function of the C string runtime (CString.lean) on byte
        arrays: `strlen`, `strnlen`, `strncpy`, `strcmp`, `strncmp`, `strcasecmp`, `strncasecmp`,
        `memcpy`, `memset`, `memcmp`, each pointer as (array, offset), the array written back for the
        destination; byte counts are any `size_t` value. Returns None if the first pointer is not
        into a byte array of the model (then the element-wise forms of mem_call apply)."""
        spec = CS_FUNCTIONS[name]
        if len(args) != len(spec[0]):
            raise Reject(n, "`%s` with %d arguments" % (name, len(args)))
        pre, vals, dst = [], [], None
        for a, kind in zip(args, spec[0]):
            if kind in ("w", "r"):
                r = self.ptr_ref(a)
                if r is None or not same_storage(r[1].t.elem, UINT8):
                    if a is args[0]:
                        return None
                    raise Reject(a, "argument of `%s` that is not a pointer into a byte array" % name)
                p0, base, off = r
                if name == "memcmp" and base.root[0] == "bview":
                    xt = base.root[2].t
                    if byte_size_align(xt, n)[0] != sum(byte_size_align(lt, n)[0] for _, _, lt in type_leaves(xt, n)):
                        raise Reject(n, "`memcmp` of the object representation of `%s`, which has padding (unspecified bytes)" % xt.cname)
                pre += p0
                vals.append(self.read_path(base, a, check_init=kind == "r").at(ATOM))
                vals.append(off.at(ATOM) if off is not None else "0")
                if kind == "w":
                    dst = base
            else:
                p0, v = self.expr(a)
                pre += p0
                t = ctype_of(a)
                vals.append(conv(v, t, CType("int", 64, False, usize=True) if kind == "n" else CType("int", 32, True), a).at(ATOM))
        call = V("CString.%s %s" % (name, " ".join(vals)), APP)
        if dst is not None:
            up, _ = self.pp_climb(n)
            if self.discard_node is not n and not (up is not None and up.get("kind") in ("CompoundStmt", "IfStmt", "ForStmt", "WhileStmt", "DoStmt", "CaseStmt", "DefaultStmt")):
                raise Reject(n, "the result of `%s` used (only its effect on the destination is translated)" % name)
            return pre + [self.write_path(dst, call, n)], None
        return pre, call

    def object_pointer_spec(self, target, args, n):
        """--c-strings: a parameter `B *p` of a function (B a class) is translated for the class D
        of the object the call passes (`&buf`, a local object of class D): as a reference parameter
        of type D, so that virtual calls through p resolve to D's overriders (print_vprintf's
        `AP_HAL::BetterStream *s`, passed a `BufferPrinter`). D must have no derived class in the
        translation (the static type is the dynamic type), and every call of the function must pass
        D (one translation per function)."""
        ps = [p for p in kids(target) if p.get("kind") == "ParmVarDecl"]
        for i, (p, a) in enumerate(zip(ps, args)):
            q = p.get("type", {}).get("desugaredQualType", p.get("type", {}).get("qualType", "")).strip()
            m = re.match(r"^(?:class |struct )?([\w:<>, ]+?) ?\*$", q)
            if not m or m.group(1) in INT_TYPES or m.group(1) in ("void", "char", "float", "double", "bool"):
                continue
            base = None
            try:
                base = parse_type_str(m.group(1), m.group(1), p)
            except Reject:
                pass
            sa = strip_parens(a)
            while sa.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr") and sa.get("castKind") in ("NoOp", "DerivedToBase", "UncheckedDerivedToBase", "BitCast"):
                sa = strip_parens(kids(sa)[0])
            if not (sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&"):
                if base is not None and base.kind == "record" and base.info.kind == "class":
                    raise Reject(a, "argument for object pointer parameter `%s` other than `&x`" % p.get("name"))
                continue
            dt = ctype_of(kids(sa)[0])
            if dt.kind != "record" or dt.info.kind != "class":
                continue
            if any(dt.info in r.bases for r in self.u.records):
                raise Reject(a, "object of class `%s`, which has derived classes, passed to pointer parameter `%s` (its dynamic type is not known)" % (dt.info.cxx, p.get("name")))
            spec = self.u.obj_param_spec.setdefault(target["id"], {})
            if spec.get(i, dt.info.cxx) != dt.info.cxx:
                raise Reject(a, "function `%s` called with objects of classes `%s` and `%s` for parameter `%s` (one translation per function)" %
                             (target.get("name"), spec[i], dt.info.cxx, p.get("name")))
            spec[i] = dt.info.cxx

    def ptr_call(self, e):
        """--c-strings: a call of a function that returns a pointer into an array it is passed
        (utoa_invert's `return s;`, pp_ret_param): the call (its result is the offset relative to the
        argument), as (pre, the argument's array, the argument's offset + the result)."""
        c = strip_parens(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_parens(kids(c)[0])
        decl = self.u.decl(c.get("referencedDecl", {}).get("id"))
        target = self.u.function_for(decl) if decl is not None else None
        if target is None or pp_ret_param(target) is None:
            return None
        i = pp_ret_param(target)
        arg = kids(e)[1 + i]
        if self.has_effects(arg):
            raise Reject(arg, "argument with side effects for the pointer parameter whose pointer the function returns")
        pre, v = self.e_CallExpr(e)
        r = self.ptr_ref(arg)
        if r is None:
            raise Reject(arg, "argument for a returned pointer parameter that is not a pointer into an array")
        p0, base, off = r
        t = self.temp()
        return pre + p0 + ["let %s : Nat := %s" % (t, v.text)], base, V("%s + %s" % (off.at(ADD) if off is not None else "0", t), ADD)

    HS = "hal'storage"

    def hal_storage_call(self, n, mname, args):
        """--hal-storage: `hal.storage->read_block(dst, src, n)` and `->write_block(dst, src, n)` on the
        HAL storage's bytes (`hal'storage`, threaded through every function that reaches it, as a
        reference parameter; HalStorage in CString.lean, the reference HAL's semantics)."""
        hp = Path(("var", self.HS), self.HS, [], CType("array", elem=UINT8, n=0))
        self.mutable.add(self.HS)
        if mname == "read_block" and len(args) == 3:
            r = self.ptr_ref(args[0])
            if r is None or not same_storage(r[1].t.elem, UINT8):
                raise Reject(args[0], "destination of `hal.storage->read_block` that is not a pointer into a byte array")
            pre, base, off = r
            pre_s, src = self.expr(args[1])
            pre_n, cnt = self.expr(args[2])
            src = conv(src, ctype_of(args[1]), CType("int", 16, False), args[1])
            cnt = conv(cnt, ctype_of(args[2]), CType("int", 64, False, usize=True), args[2])
            self.hs_use.add("r")
            self.read.add(self.HS)
            call = V("HalStorage.read_block %s %s %s %s %s" % (self.HS, self.read_path(base, n, check_init=False).at(ATOM),
                                                              off.at(ATOM) if off is not None else "0", src.at(ATOM), cnt.at(ATOM)), APP)
            return pre + pre_s + pre_n + [self.write_path(base, call, n)], None
        if mname == "write_block" and len(args) == 3:
            pre_d, dst = self.expr(args[0])
            r = self.ptr_ref(args[1])
            if r is None or not same_storage(r[1].t.elem, UINT8):
                raise Reject(args[1], "source of `hal.storage->write_block` that is not a pointer into a byte array")
            pre, base, off = r
            pre_n, cnt = self.expr(args[2])
            dst = conv(dst, ctype_of(args[0]), CType("int", 16, False), args[0])
            cnt = conv(cnt, ctype_of(args[2]), CType("int", 64, False, usize=True), args[2])
            self.hs_use |= {"r", "w"}
            self.read.add(self.HS)
            call = V("HalStorage.write_block %s %s %s %s %s" % (self.HS, dst.at(ATOM), self.read_path(base, n).at(ATOM),
                                                               off.at(ATOM) if off is not None else "0", cnt.at(ATOM)), APP)
            return pre_d + pre + pre_n + ["%s := %s" % (self.HS, call.text)], None
        raise Reject(n, "`hal.storage->%s` (only read_block and write_block are part of the storage model)" % mname)

    def struct_pointee(self, q, dq, node):
        """--mavlink: (record CType, const) of a pointer type `T *` / `const T *` to a translated plain
        struct, else None."""
        q = (q or "").strip()
        dq = (dq or q).strip()
        if not q.endswith("*") or q[:-1].rstrip().endswith("*") or not dq.endswith("*"):
            return None
        bq, bd = q[:-1].strip(), dq[:-1].strip()
        const = bq.split()[0] == "const" if bq else False
        sq, bad = strip_quals(bq)
        sd, bad2 = strip_quals(bd)
        if bad or bad2 or not sq:
            return None
        try:
            t = parse_type_str(sq, sd, node)
        except Reject:
            return None
        if t is None or t.kind != "record" or t.info.kind != "plain":
            return None
        return t, const

    def pp_null_param(self, e):
        """--mavlink: whether e names a pointer parameter into an array (a byte pointer, `const char *param_id`)."""
        e = strip_casts(e, ("NoOp", "LValueToRValue", "BitCast"))
        return e.get("kind") == "DeclRefExpr" and (e["referencedDecl"]["id"] in self.ptrs or e["referencedDecl"]["id"] in self.array_views) \
            and e["referencedDecl"]["id"] not in self.u.struct_ptr_params

    def struct_memcpy(self, n, args):
        """--mavlink: `memcpy(r_message, rxmsg, sizeof(mavlink_message_t))` (mavlink_helpers.h:999): the whole
        object copied from one struct pointer (or `&x`) to another of the same type: an assignment; else None."""
        d, s_, cnt = strip_casts(args[0], ("NoOp", "LValueToRValue", "BitCast")), strip_casts(args[1], ("NoOp", "LValueToRValue", "BitCast")), args[2]
        if not (self.is_struct_ptr(d) and self.is_struct_ptr(s_)):
            return None
        for x in (d, s_):
            if x.get("kind") == "UnaryOperator":
                try:
                    t = ctype_of(kids(x)[0])
                except Reject:
                    return None
                if t.kind != "record":
                    return None
        pre_d, pd = self.struct_ptr_target(d)
        pre_s, ps_ = self.struct_ptr_target(s_)
        sz, _ = byte_size_align(pd.t, n)
        c = strip_casts(cnt)
        if pd.t != ps_.t or not (c.get("kind") == "UnaryExprOrTypeTraitExpr" and c.get("name") == "sizeof" and
                                 self.sizeof_value(c) == sz):
            return None
        if self.discard_node is not n:
            raise Reject(n, "result of `memcpy` used")
        return pre_d + pre_s + [self.write_path(pd, self.read_path(ps_, n), n)], None

    def struct_memset(self, n, args):
        """--mavlink: `memset(&x, 0, sizeof(x))` / `memset(p, 0, sizeof(T))` of a whole struct: x is the zero value
        (every byte zero: each member zero); else None."""
        d = strip_casts(args[0], ("NoOp", "LValueToRValue", "BitCast"))
        if not self.is_struct_ptr(d) or self.int_const(args[1]) != 0:
            return None
        if d.get("kind") == "UnaryOperator":
            try:
                if ctype_of(kids(d)[0]).kind != "record":
                    return None
            except Reject:
                return None
        pre, pd = self.struct_ptr_target(d)
        c = strip_casts(args[2])
        if not (c.get("kind") == "UnaryExprOrTypeTraitExpr" and c.get("name") == "sizeof"):
            return None
        try:
            st = parse_type_str(c["argType"]["qualType"], c["argType"].get("desugaredQualType", c["argType"]["qualType"]), c) \
                if "argType" in c else ctype_of(kids(c)[0])
        except Reject:
            return None
        if st != pd.t:          # sizeof the object's own type (also of a struct whose representation is not modeled:
            return None         # mavlink_status_t's null members, whose zero is the null pointer)
        if self.discard_node is not n:
            raise Reject(n, "result of `memset` used")
        return pre + [self.write_path(pd, zero_of(pd.t, n), n)], None

    def int_const(self, e):
        e = strip_casts(e)
        return int(e["value"]) if e.get("kind") == "IntegerLiteral" else None

    def sizeof_value(self, c):
        """The value of a `sizeof(T)` / `sizeof(x)` node (the layout's size), else None."""
        try:
            t = parse_type_str(c["argType"]["qualType"], c["argType"].get("desugaredQualType", c["argType"]["qualType"]), c) \
                if "argType" in c else ctype_of(kids(c)[0])
            return byte_size_align(t, c)[0]
        except Reject:
            return None

    def text_result_call(self, e):
        """--text-results (Phase 5d): whether e (casts stripped) is a call of a member function named by --text-results."""
        e = strip_casts(e, ("NoOp", "LValueToRValue"))
        if e.get("kind") != "CXXMemberCallExpr" or not kids(e):
            return False
        c = strip_parens(kids(e)[0])
        if c.get("kind") != "MemberExpr" or "referencedMemberDecl" not in c:
            return False
        m = self.u.decl(c["referencedMemberDecl"])
        return m is not None and qualified_name(self.u, m) in TEXT_RESULTS

    def text_ref(self, e):
        """--text-buffers: (pre, value, is a `char *` parameter) of a text used as a `const char *` (casts stripped): a
        text pointer local (--text-results), a local `char` buffer, a `char *` parameter, a `char` data member; else None."""
        e = strip_casts(e, ("NoOp", "LValueToRValue", "ArrayToPointerDecay"))
        if e.get("kind") == "DeclRefExpr":
            rid = e["referencedDecl"]["id"]
            if rid in self.vars and self.vars[rid][1] is TEXTBUF:
                pre, v = self.expr(e)
                return pre, v, (e["referencedDecl"].get("kind") == "ParmVarDecl")
            return None
        if e.get("kind") == "MemberExpr":
            try:
                t = ctype_of(e)
            except Reject:
                return None
            if t.kind == "textbuf":
                pre, v = self.expr(e)
                return pre, v, False
        return None

    def opt_call(self, e):
        """--mavlink: the `Option T` type if e is a call of a translated function returning `const T *`."""
        e = strip_casts(e)
        if e.get("kind") != "CallExpr":
            return None
        c = strip_casts(kids(e)[0])
        target = self.u.function_for(self.u.decl((c.get("referencedDecl") or {}).get("id")))
        if target is None:
            return None
        t = opt_return_type(target)
        return t

    def opt_ref(self, e):
        """--mavlink: the id of the `Option` local e names (casts stripped), else None."""
        e = strip_casts(e, ("NoOp", "LValueToRValue"))
        if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in self.opt_vars:
            return e["referencedDecl"]["id"]
        return None

    def is_struct_ptr(self, e):
        """--mavlink: whether e (casts stripped) is a struct pointer parameter, a local pointer aliasing an
        object, or a call of a global accessor (all non-null)."""
        e = strip_casts(e)
        if e.get("kind") == "DeclRefExpr":
            rid = e["referencedDecl"]["id"]
            return rid in self.u.struct_ptr_params or rid in self.ptr_alias_ids
        if e.get("kind") == "CallExpr":
            return self.gaccessor_of(e) is not None
        if e.get("kind") == "UnaryOperator" and e.get("opcode") == "&":
            return True
        return False

    def gaccessor_of(self, n):
        """--mavlink: (global id, parameter index) if n is a call of a global accessor (global_accessor)."""
        if n.get("kind") != "CallExpr" or not self.u.gaccessors:
            return None
        c = strip_casts(kids(n)[0])
        if c.get("kind") != "DeclRefExpr":
            return None
        d = self.u.decl(c["referencedDecl"]["id"])
        return self.u.gaccessors.get((d or {}).get("mangledName"))

    def gaccessor_path(self, n):
        """--mavlink: (pre, Path) of the element a global accessor call designates, its index in a temporary."""
        gid, pi = self.gaccessor_of(n)
        gid = self.global_var(gid)
        name, t = self.vars[gid]
        path = Path(("var", gid), name, [], t)
        if pi is None:
            return [], path
        pre, nat = self.nat_index(kids(n)[1 + pi])
        tmp = self.temp()
        return pre + ["let %s : Nat := %s" % (tmp, nat.text)], path.extend(("i", V(tmp, ATOM)), t.elem)

    def struct_ptr_target(self, a):
        """--mavlink: (pre, Path) of the object a pointer argument `&x`, `p` (a struct pointer parameter or an
        aliasing local) or an accessor call points to."""
        e = strip_casts(a)
        r = None
        if e.get("kind") == "UnaryOperator" and e.get("opcode") == "&":
            r = self.resolve_path(kids(e)[0])
        elif e.get("kind") == "DeclRefExpr":
            r = self.resolve_path(e)
        elif e.get("kind") == "CallExpr" and self.gaccessor_of(e) is not None:
            r = self.gaccessor_path(e)
        if r is None or r[1].t is None or r[1].t.kind != "record":
            raise Reject(a, "argument for a struct pointer parameter that is not `&x`, a struct pointer or an accessor call")
        return r

    def global_var(self, rid):
        """--mavlink: the id of the mutable file-scope variable that rid (it, or its `extern` declaration)
        names, registered as a variable of this body (a hidden reference parameter), else None."""
        gid = self.u.global_alias.get(rid, rid)
        g = self.u.globals.get(gid)
        if g is None:
            return None
        self.vars[gid] = (g["lean"], g["t"])
        self.gl_use.setdefault(gid, set()).add("r")
        return gid

    def global_params(self):
        """--mavlink: the parameter entries of the file-scope variables the body (or a callee) reaches, in
        definition order (appended after the body is translated); a written one is also returned."""
        out = []
        for gid in sorted(self.gl_use, key=lambda k: self.u.ast_order.get(k, 0)):
            g = self.u.globals[gid]
            w = "w" in self.gl_use[gid]
            entry = ({"kind": "Global", "id": gid, "name": g["lean"], "type": {"qualType": g["decl"]["type"]["qualType"]}},
                     g["lean"], g["t"], "mut" if w else "cptr")
            if w:
                self.outs.append((gid, g["lean"], g["t"]))
            out.append(entry)
        return out

    def hal_storage_param(self):
        """--hal-storage: the parameter entry of the HAL storage for a function whose body reaches it
        (appended after the body is translated), and whether it is written (then returned)."""
        if not self.hs_use:
            return None
        w = "w" in self.hs_use
        entry = ({"kind": "HalStorage", "id": self.HS, "name": self.HS, "type": {"qualType": "AP_HAL::Storage &"}},
                 self.HS, CType("array", elem=UINT8, n=0), "mut" if w else "cptr")
        if w:
            self.outs.append((self.HS, self.HS, entry[2]))
        return entry

    def held_param(self, construct, i):
        """--c-strings: the lean name of the held member (held_member_type) that argument i of the
        constructor call `construct` initializes, else None."""
        ctor = self.u.decl(construct.get("ctorDecl", {}).get("id")) if construct.get("ctorDecl") else None
        if ctor is None:
            t = ctype_of(construct)
            if t.kind != "record":
                return None
            ctor = t.info.find_ctor(construct.get("ctorType", {}).get("qualType", ""))
        if ctor is None:
            return None
        defn = self.u.body_of(ctor) or ctor
        ps = [p for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
        if i >= len(ps):
            return None
        for ini in kids(defn):
            if ini.get("kind") != "CXXCtorInitializer" or not kids(ini):
                continue
            f = self.u.decl(ini.get("anyInit", {}).get("id"))
            if f is None or held_member_type(f) is None:
                continue
            e = strip_object(kids(ini)[0])
            if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] == ps[i]["id"]:
                return lean_field(f["name"], f)
        return None

    def bo_ref(self, pre, xp, n):
        """--byte-objects: `&x` used as a byte pointer (`void *`, `uint8_t *`, `char *`; x a number,
        an enum, a plain struct or an array of them): a temporary holding x's object representation
        (value_to_bytes); a write through the pointer is stored back into x (value_from_bytes)."""
        t = xp.t
        byte_size_align(t, n)
        tmp = self.temp()
        v = self.read_path(xp, n, check_init=False)
        line = "let mut %s : Array UInt8 := %s  -- the bytes of `%s` (its object representation)" % (
            tmp, value_to_bytes(v.text, t, n), comment_safe(self.u.text_of(kids(n)[0]) or "x"))
        return list(pre) + [line], Path(("bview", tmp, xp), tmp, [], CType("array", elem=UINT8, n=0)), None

    def const_table_element(self, e):
        """Is e an element of a constant array (a `const` global or static data member: it never changes)?"""
        e = strip_object(e)
        if e.get("kind") != "ArraySubscriptExpr":
            return False
        b = strip_parens(kids(e)[0])
        if b.get("kind") != "ImplicitCastExpr" or b.get("castKind") != "ArrayToPointerDecay":
            return False
        a = strip_parens(kids(b)[0])
        if a.get("kind") != "DeclRefExpr":
            return False
        d = self.u.decl(a["referencedDecl"]["id"])
        return d is not None and d.get("kind") == "VarDecl" and d["type"]["qualType"].startswith("const ") and \
            (d.get("storageClass") == "static" or self.u.parent.get(d["id"], {}).get("kind") in ("TranslationUnitDecl", "CXXRecordDecl", "NamespaceDecl"))

    def cs_valueish(self, e):
        """Is e a byte pointer value with no variable behind it (a string literal, `va_arg`, a table element)?"""
        e = strip_parens(e)
        while e.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr") and e.get("castKind") in ("NoOp", "BitCast", "LValueToRValue"):
            e = strip_parens(kids(e)[0])
        k = e.get("kind")
        return k == "VAArgExpr" or k == "ArraySubscriptExpr" or \
            (k == "ImplicitCastExpr" and strip_parens(kids(e)[0]).get("kind") == "StringLiteral")

    def cs_copy_local(self, d, et, init, moved):
        """--c-strings: a local `const char *` assigned pointers into different arrays (string
        literals, local arrays, `va_arg`): it holds a copy of the array it points into, and an offset.
        Reading through it reads the copy, so the array must not change while the pointer is used
        (C allows that: the pointee is `const` only through this pointer; ArduPilot's uses point to
        literals and to buffers not written meanwhile; README.md, "Phase 2b")."""
        name = self.ident(d["name"], d)
        rid = d["id"]
        self.cs_copy_check(d)
        t = CType("array", elem=et, n=0)
        oname = self.off_name(name)
        self.vars[rid] = (name, t)
        self.declared.append((rid, name))
        self.declared.append((rid, oname))
        self.ptrs[rid] = PtrVar(Path(("var", rid), name, [], t), oname, et, "copy")
        mut = "let mut" if rid in self.mutable or init is None else "let"
        if init is None:
            self.mutable.add(rid)
            self.uninit.add(rid)
            return ["let mut %s : Array UInt8 := #[]  -- C `%s`: uninitialized; assigned before every use" % (name, comment_safe(self.u.text_of(d) or d["name"])),
                    "let mut %s : Nat := 0" % oname]
        r = self.ptr_ref(init)
        if r is None:
            raise Reject(init, "local pointer `%s` initialized with something other than a pointer into an array" % d["name"])
        pre, base, off = r
        return pre + ["%s %s : Array UInt8 := %s  -- C `%s`: a copy of the array it points into" % (mut, name, self.read_path(base, init).text, comment_safe(self.u.text_of(d) or d["name"])),
                      "%s %s : Nat := %s" % ("let mut" if moved or rid in self.mutable else "let", oname, off.text if off is not None else "0")]

    def cs_copy_check(self, d):
        """For a `const char *` that holds a copy of what it points to (cs_copy_local): no statement of
        the block that declares it, after the statement that makes it point into a variable's array,
        writes that array (checked statement by statement in that block; README.md, "Phase 2b")."""
        scope = self.u.parent.get(self.u.parent.get(d["id"], {}).get("id"))
        if scope is None or scope.get("kind") != "CompoundStmt":
            return
        stmts = kids(scope)
        sources = []
        for i, st in enumerate(stmts):
            for m in walk(st):
                v = None
                if m is d and kids(d):
                    v = kids(d)[0]
                elif m.get("kind") == "BinaryOperator" and m.get("opcode") == "=" and \
                        strip_object(kids(m)[0]).get("kind") == "DeclRefExpr" and strip_object(kids(m)[0])["referencedDecl"]["id"] == d["id"]:
                    v = kids(m)[1]
                if v is not None:
                    for rid in self.pp_roots(v):
                        sources.append((i, rid))
        for i, rid in sources:
            for st in stmts[i + 1:]:
                if rid in self.assigned(st) | self.pp_mutable(st):
                    raise Reject(st, "array `%s` written while `%s` (a `const char *` that holds a copy of it) may still point into it" %
                                 ((self.u.decl(rid) or {}).get("name", "?"), d["name"]))

    def union_bytes_ref(self, e):
        """--mission: (pre, bytes Path) of `&u` / `(void *)&u` with u a byte union (its bytes), else None."""
        se = strip_parens(e)
        while se.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr", "CXXStaticCastExpr") and se.get("castKind") in ("BitCast", "NoOp") and kids(se):
            se = strip_parens(kids(se)[0])
        if se.get("kind") != "UnaryOperator" or se.get("opcode") != "&":
            return None
        r = self.resolve_path(kids(se)[0])
        if r is None or r[1].t is None:
            return None
        if r[1].t.kind == "record" and getattr(r[1].t.info, "byte_union", False) and not (r[1].steps and r[1].steps[-1][0] in ("ub", "ubf")):
            return r[0], r[1].extend(("f", "bytes"), r[1].t.info.fields[0].t)
        if (r[1].t.is_scalar() or r[1].t.kind == "record") and not (r[1].steps and r[1].steps[-1][0] == "i"):
            return r[0], r[1]       # `(void*)&id` (AP_Mission.cpp:3067): an object, through its bytes (`&a[k]`: a pointer into a)
        return None

    def strip_void_cast(self, e):
        """--mission: e without a cast to `void *` (`(void*)&b[1]`)."""
        se = strip_parens(e)
        while se.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr") and se.get("castKind") in ("BitCast", "NoOp") and kids(se):
            se = strip_parens(kids(se)[0])
        return se

    def union_memcpy(self, n, args):
        """--mission: `memcpy((void *)&cmd.content, packed_content.bytes, 12)` and `memcpy(packed.bytes, &cmd.content, 12)`
        (AP_Mission.cpp:898, :974): bytes copied between a byte union and a byte array (CString.memcpy). Else None."""
        dr, sr = self.union_bytes_ref(args[0]), self.union_bytes_ref(args[1])
        if dr is None and sr is None:
            return None
        if dr is not None:
            pre_d, dbase, doff = dr[0], dr[1], None
        else:
            r = self.ptr_ref(self.strip_void_cast(args[0]))
            if r is None:
                return None
            pre_d, dbase, doff = r
        if sr is not None:
            pre_s, sbase, soff = sr[0], sr[1], None
        else:
            r = self.ptr_ref(self.strip_void_cast(args[1]))
            if r is None:
                return None
            pre_s, sbase, soff = r
        pre_n, cnt = self.expr(args[2])
        cnt = conv(cnt, ctype_of(args[2]), CType("int", 64, False, usize=True), args[2])
        def as_bytes(p):        # an object (not an array of bytes): its object representation
            if p.t.kind == "array" and same_storage(p.t.elem, UINT8):
                return self.read_path(p, n), False
            return V("(%s)" % value_to_bytes(self.read_path(p, n).text, p.t, n), ATOM), True
        dv, dobj = as_bytes(dbase)
        sv, _ = as_bytes(sbase)
        call = V("CString.memcpy %s %s %s %s %s" % (dv.at(ATOM), doff.at(ATOM) if doff is not None else "0",
                                                   sv.at(ATOM), soff.at(ATOM) if soff is not None else "0", cnt.at(ATOM)), APP)
        if dobj:
            t = self.temp()
            return pre_d + pre_s + pre_n + ["let %s := %s" % (t, call.text),
                                            self.write_path(dbase, V(value_from_bytes(t, "0", dbase.t, n), ATOM), n)], None
        return pre_d + pre_s + pre_n + [self.write_path(dbase, call, n)], None

    def ptr_ref(self, e):
        """(pre, base Path, offset V or None) of a pointer-valued expression into an array of the
        model: a pointer parameter or local, an array decayed to a pointer, `a + k`, `&a[k]`, a
        cast of a byte pointer, `p++` (the step happens in pre); else None."""
        e = strip_parens(e)
        k = e.get("kind")
        if MAVLINK[0]:
            se = strip_casts(e, ("NoOp", "LValueToRValue", "BitCast"))
            if se.get("kind") in ("DeclRefExpr", "CallExpr") and self.is_struct_ptr(se):
                # --mavlink: a struct pointer used as a byte pointer (`mavlink_msg_decode_target(msg, param_set, ...)`,
                # `(const char *)param_set`): the object's bytes, written back if the callee writes them
                pre, path = self.struct_ptr_target(se)
                byte_size_align(path.t, se)
                tmp = self.temp()
                v = self.read_path(path, se, check_init=False)
                line = "let mut %s : Array UInt8 := %s  -- the bytes of `*%s` (its object representation)" % (
                    tmp, value_to_bytes(v.text, path.t, se), comment_safe(self.u.text_of(se) or "p"))
                return list(pre) + [line], Path(("bview", tmp, path), tmp, [], CType("array", elem=UINT8, n=0)), None
        if C_STRINGS[0]:
            r = self.cs_ptr_value(e)
            if r is not None:
                return r
        if MAVLINK[0] and k in ("ImplicitCastExpr", "CStyleCastExpr") and e.get("castKind") == "BitCast":
            r = self.ptr_ref(kids(e)[0])
            pe = self.pp_pointee(e)
            if r is not None and r[1].t is not None and r[1].t.kind == "array" and r[1].t.elem.is_scalar() and \
                    pe is not None and pe[0] in (UINT8, CHAR, VOID) and not same_storage(r[1].t.elem, UINT8) and r[1].root[0] != "bview":
                # --mavlink: an array of wider numbers passed as bytes (`mav_array_memcpy(packet.voltages, voltages, ...)`,
                # `memcpy(value, &_MAV_PAYLOAD(msg)[ofs], n)` into a `uint16_t *`): the bytes of its elements from the
                # pointer's offset, written back if the callee writes them
                pre, base, off = r
                if off is not None:
                    raise Reject(e, "pointer into an array of `%s` at an offset, used as bytes" % base.t.elem.cname)
                tmp = self.temp()
                v = self.read_path(base, e, check_init=False)
                line = "let mut %s : Array UInt8 := %s  -- the bytes of the elements of `%s`" % (
                    tmp, value_to_bytes(v.text, base.t, e), comment_safe(self.u.text_of(kids(e)[0]) or "a"))
                return list(pre) + [line], Path(("bview", tmp, base), tmp, [], CType("array", elem=UINT8, n=0)), None
            if r is not None:
                return r
        if k == "ImplicitCastExpr" and e.get("castKind") in ("LValueToRValue", "NoOp", "BitCast"):
            return self.ptr_ref(kids(e)[0])
        if k == "ImplicitCastExpr" and e.get("castKind") == "ArrayToPointerDecay":
            r = self.resolve_path(kids(e)[0])
            if r is None or r[1].t is None or r[1].t.kind != "array":
                return None
            return r[0], r[1], None
        if k in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr") and e.get("castKind") in ("BitCast", "NoOp"):
            r = self.ptr_ref(kids(e)[0])
            pe = self.pp_pointee(e)
            if r is None or pe is None or not same_storage(r[1].t.elem, pe[0]):
                return None                 # a cast that changes the element type: a byte view
            return r
        if C_STRINGS[0] and k == "MemberExpr" and self.ctx is not None:
            f = self.this_field(e)
            if f is not None and getattr(f.t, "held", False):
                return [], Path(("s",), "s", [("f", f.lean)], f.t), None     # the array the object holds
        if k == "DeclRefExpr" and e["referencedDecl"]["id"] in self.ptrs:
            rid = e["referencedDecl"]["id"]
            pv = self.ptrs[rid]
            if pv.base.root == ("var", rid) and rid in self.uninit and self.da is not DIVERGE and rid not in self.da and not UNINIT_READS[0]:
                raise Reject(e, "use of `%s`, which may not hold an array yet" % e["referencedDecl"]["name"])
            self.read.add(rid)
            if pv.base.root[0] == "var":
                self.read.add(pv.base.root[1])
            return [], pv.base, (V(pv.off, ATOM) if pv.off else None)
        if k == "BinaryOperator" and e.get("opcode") in ("+", "-") and self.pp_pointee(e) is not None:
            a, b = kids(e)
            if self.pp_pointee(a) is None and a.get("castKind") != "ArrayToPointerDecay":
                if e["opcode"] == "-":
                    return None
                a, b = b, a
            r = self.ptr_ref(a)
            if r is None:
                return None
            pre, base, off = r
            pre_i, i = self.nat_index(b)
            sign = "+" if e["opcode"] == "+" else "-"
            return pre + pre_i, base, V("%s %s %s" % ((off.at(ADD) if off else "0"), sign, i.at(ADD + 1)), ADD)
        if k == "UnaryOperator" and e.get("opcode") == "&":
            r = self.resolve_path(kids(e)[0])
            if BYTE_OBJECTS[0] and r is not None and r[1].t is not None and r[1].t.kind != "array" and \
                    not (r[1].steps and r[1].steps[-1][0] == "i" and r[1].t in (UINT8, CHAR)):
                return self.bo_ref(r[0], r[1], e)
            if r is None or not r[1].steps or r[1].steps[-1][0] != "i":
                return None
            pre, p = r
            return pre, Path(p.root, p.root_text, p.steps[:-1], CType("array", elem=p.t, n=0)), p.steps[-1][1]
        if k == "UnaryOperator" and e.get("opcode") in ("++", "--"):
            d = strip_object(kids(e)[0])
            pv = self.ptrs.get(d.get("referencedDecl", {}).get("id")) if d.get("kind") == "DeclRefExpr" else None
            if pv is None or pv.off is None:
                return None
            sign = "+" if e["opcode"] == "++" else "-"
            if e.get("isPostfix"):
                t = self.temp()
                return ["let %s := %s" % (t, pv.off), "%s := %s %s 1" % (pv.off, pv.off, sign)], pv.base, V(t, ATOM)
            return ["%s := %s %s 1" % (pv.off, pv.off, sign)], pv.base, V(pv.off, ATOM)
        return None

    VA_GETTERS = {(32, True): "argInt32", (32, False): "argUInt32", (64, True): "argInt64", (64, False): "argUInt64"}

    def valist_ref(self, n):
        """(pre, Path) of the `va_list` variable a `va_arg`/`va_start`/`va_end` names."""
        r = self.resolve_path(kids(n)[0] if n.get("kind") == "VAArgExpr" else n)
        if r is None or r[1].t != VALIST or r[1].root[0] != "var":
            raise Reject(n, "`va_list` that is not a local variable or parameter")
        return r

    def e_VAArgExpr(self, n):
        """--c-strings: `va_arg(ap, T)` for T `int`, `unsigned`, `long`, `unsigned long`, `long long`,
        `unsigned long long`, `double` (`char *` as a pointer, cs_ptr_value): the next argument's slot
        read as T, and ap moves on (README.md, "Phase 2b")."""
        if not C_STRINGS[0]:
            raise Reject(n, "`va_arg`")
        t = ctype_of(n)
        if t.kind == "double":
            g = "argBinary64"
        elif t.is_int() and not t.usize and t.name is None and (t.bits, t.signed) in self.VA_GETTERS:
            g = self.VA_GETTERS[(t.bits, t.signed)]
        else:
            raise Reject(n, "`va_arg` of type `%s`" % t.cname)
        pre, ap = self.valist_ref(n)
        tmp = self.temp()
        apv = self.read_path(ap, n).text
        return pre + ["let %s := VaList.%s %s" % (tmp, g, apv), self.write_path(ap, V("VaList.next %s" % apv, APP), n)], V(tmp, ATOM)

    def va_builtin(self, n, name, args):
        """`va_start(ap, last)`: ap is the function's variadic arguments (its parameter `va'`);
        `va_end(ap)`: nothing; `va_copy(d, s)`: d := s."""
        if name == "__builtin_va_end":
            self.valist_ref(args[0])
            return ["pure ()  -- C `va_end`"], None
        if name == "__builtin_va_copy":
            pre, d = self.valist_ref(args[0])
            pre2, src = self.valist_ref(args[1])
            return pre + pre2 + [self.write_path(d, self.read_path(src, n), n)], None
        if self.fn is None or not self.fn.get("variadic"):
            raise Reject(n, "`va_start` outside a variadic function")
        self.read.add("va'")
        pre, ap = self.valist_ref(args[0])
        return pre + [self.write_path(ap, V("VaList.start va'", APP), n)], None

    def cs_ptr_value(self, e):
        """--c-strings: (pre, base Path, offset) of a byte pointer that is a value rather than a
        variable: a string literal (its bytes), an element of a table of string literals, `va_arg(ap,
        char *)`, the result of a function that returns a pointer into an array it is passed; else None."""
        e = strip_parens(e)
        k = e.get("kind")
        arr_t = CType("array", elem=CHAR, n=0)
        if k == "ImplicitCastExpr" and e.get("castKind") == "ArrayToPointerDecay" and strip_parens(kids(e)[0]).get("kind") == "StringLiteral":
            return [], Path(("lit",), bytes_text(string_bytes(strip_parens(kids(e)[0]))), [], arr_t), None
        if k == "ArraySubscriptExpr":
            try:
                et = ctype_of(e)
            except Reject:
                et = None
            b = strip_parens(kids(e)[0])
            if b.get("kind") == "ImplicitCastExpr" and b.get("castKind") == "ArrayToPointerDecay":
                try:
                    bt = ctype_of(kids(b)[0])
                except Reject:
                    bt = None
                if bt is not None and bt.kind == "array" and bt.elem == CSTR:
                    pre, v = self.expr(e)
                    t = self.temp()
                    return pre + ["let %s : Array UInt8 := %s" % (t, v.text)], Path(("lit",), t, [], arr_t), None
        if k == "VAArgExpr":
            pre, ap = self.valist_ref(e)
            t = self.temp()
            return pre + ["let %s := VaList.argPtr %s" % (t, ap.text()), self.write_path(ap, V("VaList.next %s" % ap.text(), APP), e)], \
                Path(("lit",), t + ".1", [], arr_t), V(t + ".2", ATOM)
        if k == "CallExpr":
            r = self.ptr_call(e)
            if r is not None:
                return r
        return None

    def ptr_path(self, n):
        """resolve_path for `*e` and `e[i]` where e is a pointer into an array of the model."""
        k = n.get("kind")
        if k == "UnaryOperator" and n.get("opcode") == "*":
            if self.nullable_ref(kids(n)[0]) is not None:
                return None
            r = self.ptr_ref(kids(n)[0])
            if r is None:
                return None
            pre, base, off = r
            return pre, base.extend(("i", off if off is not None else V("0", ATOM)), base.t.elem)
        if k == "ArraySubscriptExpr" and kids(n)[0].get("castKind") != "ArrayToPointerDecay":
            r = self.ptr_ref(kids(n)[0])
            if r is None:
                b = strip_parens(kids(n)[0])
                while b.get("kind") == "ImplicitCastExpr" and b.get("castKind") in ("LValueToRValue", "NoOp"):
                    b = strip_parens(kids(b)[0])
                if b.get("kind") in ("CStyleCastExpr", "CXXReinterpretCastExpr") and self.pp_lv_written(n):
                    raise Reject(n, "write through a byte view (`((uint8_t *)&x)[j] = v`: the object representation is not modeled)")
                return None
            pre, base, off = r
            idx = kids(n)[1]
            it = ctype_of(idx)
            if off is not None and it.is_int() and it.signed:
                # a signed index into a moved pointer may be negative: the sum as an integer
                pre_i, i = self.expr(idx)
                return pre + pre_i, base.extend(("i", V("(Int.ofNat %s + %s.toInt).toNat" % (off.at(ATOM), i.at(ATOM)), APP)), base.t.elem)
            pre_i, i = self.nat_index(idx)
            ix = i if off is None else V("%s + %s" % (off.at(ADD), i.at(ADD + 1)), ADD)
            return pre + pre_i, base.extend(("i", ix), base.t.elem)
        return None

    def ptr_cursor(self, target):
        """The PtrVar of a moved pointer named by target (a DeclRefExpr), else None."""
        t = strip_object(target)
        if t.get("kind") != "DeclRefExpr":
            return None
        pv = self.ptrs.get(t["referencedDecl"]["id"])
        return pv if pv is not None and pv.off is not None else None

    def ptr_step(self, n, want_value):
        """`p++`, `p--`, `p += k`, `p -= k`, `p = q` on a moved pointer: its offset changes."""
        k = n.get("kind")
        pv = self.ptr_cursor(kids(n)[0])
        if want_value:
            raise Reject(n, "the value of a pointer step used other than as `*p++` or an argument")
        if k == "UnaryOperator":
            return ["%s := %s %s 1" % (pv.off, pv.off, "+" if n["opcode"] == "++" else "-")], None
        if k == "CompoundAssignOperator":
            pre, i = self.nat_index(kids(n)[1])
            return pre + ["%s := %s %s %s" % (pv.off, pv.off, "+" if n["opcode"] == "+=" else "-", i.at(ADD + 1))], None
        r = self.ptr_ref(kids(n)[1])
        if pv.kind == "copy" and r is not None:
            # --c-strings: a `const char *` that holds a copy of the array it points into
            self.mark_assigned(pv.base.root[1])
            return r[0] + [self.write_path(pv.base, self.read_path(r[1], n), n), "%s := %s" % (pv.off, r[2].text if r[2] is not None else "0")], None
        if r is None or r[1].text() != pv.base.text():
            raise Reject(n, "pointer assigned a pointer into another array")
        return r[0] + ["%s := %s" % (pv.off, r[2].text if r[2] is not None else "0")], None

    def ptr_compare(self, n, as_prop, as_bool):
        """`p != q`, `p < q`, ...: pointers into the same array compare as their offsets."""
        a, b = kids(n)
        ra, rb = self.ptr_ref(a), self.ptr_ref(b)
        if ra is None or rb is None or ra[1].text() != rb[1].text():
            raise Reject(n, "comparison of pointers that are not into the same array")
        x = ra[2] if ra[2] is not None else V("0", ATOM)
        y = rb[2] if rb[2] is not None else V("0", ATOM)
        op = n["opcode"]
        if op in ("==", "!="):
            return ra[0] + rb[0], V("%s %s %s" % (x.at(CMP + 1), op, y.at(CMP + 1)), CMP)
        prop = "%s %s %s" % (x.at(CMP + 1), self.REL[op], y.at(CMP + 1))
        return ra[0] + rb[0], (V(prop, CMP) if as_prop else V("decide (%s)" % prop, APP))

    def ptr_arg(self, a, ref, roots):
        """call_args for an argument bound to an array pointer parameter: (pre, value, out) with out
        the Path (or Splice) to write the callee's array back to, if the callee writes it."""
        r = self.ptr_ref(a)
        if r is None:
            raise Reject(a, "argument for an array pointer parameter that is not an array, a pointer into one, `a + k` or `&a[k]`")
        pre, base, off = r
        key = base.text()
        for other, w in roots:
            if other == key and (w or ref == "mut"):
                raise Reject(a, "two pointer arguments into the same array `%s`, one of them written (aliasing)" % key)
        roots.append((key, ref == "mut"))
        v = self.read_path(base, a, check_init=ref != "mut")
        if ARRAY_OFFSETS[0]:
            # --array-offsets: the whole array and the offset (no copy); written back whole after the call
            return pre, v, (base if ref == "mut" else None), (off if off is not None else V("0", ATOM))
        if off is not None:
            # a slice `a + k`: the elements from k on (a copy); written back after the call
            t = v.at(ATOM)
            v = V("%s.extract %s %s.size" % (t, off.at(ATOM), t), APP)
        out = None
        if ref == "mut":
            out = base if off is None else Splice(base, off)
        return pre, v, out

    def out_line(self, p, value, n):
        """The line that writes a reference or pointer argument back after a call."""
        if isinstance(p, Splice):
            t = self.read_path(p.base, n).at(ATOM)
            return self.write_path(p.base, V("%s.extract 0 %s ++ %s" % (t, p.off.at(ATOM), value.at(ATOM)), ADD), n)
        return self.write_path(p, value, n)

    def pp_count(self, size, elem, n):
        """The element count k of a byte size written `k * sizeof(T)` (T the element type, or
        `sizeof(x[0])`): its Nat V; else Reject."""
        factors = []

        def flat(x):
            x = strip_parens(x)
            if x.get("kind") == "BinaryOperator" and x.get("opcode") == "*":
                flat(kids(x)[0])
                flat(kids(x)[1])
            else:
                factors.append(x)
        flat(size)
        sz = [f for f in factors if f.get("kind") == "UnaryExprOrTypeTraitExpr" and f.get("name") == "sizeof"]
        ok = False
        if len(sz) == 1:
            f = sz[0]
            st = parse_type_str(f["argType"]["qualType"], f["argType"].get("desugaredQualType", f["argType"]["qualType"]), f) \
                if "argType" in f else ctype_of(kids(f)[0])
            ok = st == elem
        if not ok:
            raise Reject(n, "byte count that is not `k * sizeof(T)` with T the element type `%s`" % elem.cname)
        rest = [f for f in factors if f is not sz[0]]
        pre, vals = self.operands(rest)
        if not vals:
            return pre, V("1", ATOM)
        terms = []
        for f, v in zip(rest, vals):
            ft = ctype_of(f)
            if not ft.is_int():
                raise Reject(n, "byte count with a factor of type `%s`" % ft.cname)
            terms.append("%s.toNat" % v.at(ATOM) if not ft.signed else "%s.toNatClampNeg" % v.at(ATOM))
        return pre, V(" * ".join(terms), MUL) if len(terms) > 1 else V(terms[0], APP)

    def splice_text(self, base_text, off, k, middle):
        """Lean text of array base_text with the k elements from offset off replaced by middle."""
        b = base_text if SIMPLE.match(base_text) else "(" + base_text + ")"
        o = off.at(ADD) if off is not None else None
        if o is None:
            return "%s ++ %s.extract %s %s.size" % (middle, b, k.at(ATOM), b)
        return "%s.extract 0 %s ++ %s ++ %s.extract (%s + %s) %s.size" % (b, off.at(ATOM), middle, b, o, k.at(ADD + 1), b)

    def mem_call(self, n, name, args):
        """`memset(p, 0, k * sizeof(T))`, `memcpy(p, q, k * sizeof(T))` on arrays of the model (k
        elements from the pointers' offsets); `memcmp(p, q, k * sizeof(T)) == 0` on integer arrays.
        Returns (pre, V) or None if the first argument is not such a pointer."""
        r0 = self.ptr_ref(args[0])
        if r0 is None:
            return None
        pre0, base, off = r0
        elem = base.t.elem
        if name == "memset":
            v = strip_parens(args[1])
            while v.get("kind") == "ImplicitCastExpr" and v.get("castKind") in ("IntegralCast", "FloatingToIntegral"):
                v = strip_parens(kids(v)[0])
            zero = (v.get("kind") == "IntegerLiteral" and v.get("value") == "0") or \
                (v.get("kind") == "FloatingLiteral" and float(v.get("value", "1")) == 0.0)
            if not zero:
                raise Reject(n, "`memset` of an array with a value other than 0")
            pre_k, k = self.pp_count(args[2], elem, n)
            if ARRAY_OFFSETS[0] and off is not None:
                # --array-offsets: the k elements written in place, one by one
                j = self.temp()
                el = base.extend(("i", V("%s + %s" % (off.at(ADD), j), ADD)), elem)
                return pre0 + pre_k + ["for %s in [0:%s] do  -- C++ `memset` of k elements" % (j, k.at(ATOM)),
                                       "  " + self.write_path(el, zero_of(elem, n), n)], None
            mid = "Array.replicate %s %s" % (k.at(ATOM), zero_of(elem, n).at(ATOM))
            old = self.read_path(base, n, check_init=False).text
            return pre0 + pre_k + [self.write_path(base, V(self.splice_text(old, off, k, mid), ADD), n)], None
        r1 = self.ptr_ref(args[1])
        if r1 is None:
            raise Reject(n, "`%s` whose second argument is not an array or a pointer into one" % name)
        pre1, base1, off1 = r1
        if base1.t.elem != elem:
            raise Reject(n, "`%s` between arrays of different element types" % name)
        pre_k, k = self.pp_count(args[2], elem, n)
        src = self.read_path(base1, n).at(ATOM)
        o1 = off1.at(ADD) if off1 is not None else "0"
        piece = "%s.extract %s (%s + %s)" % (src, off1.at(ATOM) if off1 is not None else "0", o1, k.at(ADD + 1))
        if name == "memcpy":
            if base1.text() == base.text():
                raise Reject(n, "`memcpy` within one array (overlap is undefined)")
            if ARRAY_OFFSETS[0] and (off is not None or off1 is not None):
                # --array-offsets: the k elements copied in place, one by one
                j = self.temp()
                el = base.extend(("i", V("%s + %s" % (off.at(ADD) if off is not None else "0", j), ADD)), elem)
                sel = base1.extend(("i", V("%s + %s" % (o1, j), ADD)), elem)
                return pre0 + pre1 + pre_k + ["for %s in [0:%s] do  -- C++ `memcpy` of k elements" % (j, k.at(ATOM)),
                                              "  " + self.write_path(el, self.read_path(sel, n), n)], None
            old = self.read_path(base, n, check_init=False).text
            return pre0 + pre1 + pre_k + [self.write_path(base, V(self.splice_text(old, off, k, "(%s)" % piece), ADD), n)], None
        # memcmp: only its comparison with 0 is modeled (equal bytes iff equal integer elements)
        up, _ = self.pp_climb(n)
        if not elem.is_int() or up is None or up.get("kind") != "BinaryOperator" or up.get("opcode") not in ("==", "!=") or \
                not any(self.const_int(x) == 0 for x in kids(up)):
            raise Reject(n, "`memcmp` other than `memcmp(p, q, k * sizeof(T)) == 0` (or `!= 0`) on integer arrays")
        dst = self.read_path(base, n).at(ATOM)
        o0 = off.at(ADD) if off is not None else "0"
        mine = "%s.extract %s (%s + %s)" % (dst, off.at(ATOM) if off is not None else "0", o0, k.at(ADD + 1))
        return pre0 + pre1 + pre_k, V("(if %s == %s then (0 : Int32) else 1)" % (mine, piece), ATOM)

    INT_SPELLINGS = set(INT_TYPES) | {"int8_t", "int16_t", "int32_t", "int64_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t", "size_t", "std::size_t"}

    # -- --world-pointers (Phase 3, F1/F2/F4; README.md, "Phase 3: World pointers") ---------------

    def obj_type(self, e):
        """The CType("obj") of a pointer expression to a translated class, else None."""
        try:
            t = ctype_of(strip_parens(e))
        except Reject:
            return None
        return t if t.kind == "obj" else None

    # -- --member-pointers (README.md, "Phase 3: AP_AHRS translated") -------------------------------

    def mtag_ctx_targets(self, rec, n):
        """The tagged member objects (member_tags) a pointer or reference of type `rec *` may designate, or
        None; they are members of the object whose member function this is (else rejected)."""
        if not (MEMBER_PTRS[0] and self.u.mtags) or rec is None:
            return None
        tgs = mtag_targets(self.u, rec)
        if not tgs:
            return None
        if self.ctx is None or any(tg["orec"] not in self.ctx.rec.chain() for tg in tgs):
            raise Reject(n, "pointer or reference to member objects of `%s` outside its own member functions" % tgs[0]["owner"])
        if ptr_targets(self.u, rec):
            raise Reject(n, "pointer to `%s`, which may point to member objects and to other objects" % rec.cxx)
        return tgs

    def mtag_ref(self, e):
        """(pre, V tag, RecordInfo of the static type) of the object e designates if e is `*p` of a pointer
        to tagged member objects, a reference parameter or local modeled as a tag, or a reference member of an
        unnamed struct (`be.backend`); else None."""
        if not (MEMBER_PTRS[0] and self.u.mtags):
            return None
        e = strip_object(e)
        k = e.get("kind")
        if k == "UnaryOperator" and e.get("opcode") == "*":
            pt = self.obj_type(kids(e)[0])
            if pt is not None and self.mtag_ctx_targets(pt.info, e):
                pre, v = self.expr(kids(e)[0])
                return pre, v, pt.info
            return None
        if k == "DeclRefExpr" and e["referencedDecl"]["id"] in self.tagrefs:
            rid = e["referencedDecl"]["id"]
            self.read.add(rid)
            return [], V(self.vars[rid][0], ATOM), self.vars[rid][1].info
        if k == "MemberExpr" and e.get("referencedMemberDecl") in self.u.refptr_fields:
            r = self.resolve_path(kids(e)[0])
            if r is None or r[1].t is None or r[1].t.kind != "record":
                raise Reject(e, "reference member `%s` of something other than a variable, member or element" % e.get("name"))
            f = r[1].t.info.field_by_id(e["referencedMemberDecl"])
            fp = r[1].extend(("f", f.lean), f.t)
            return r[0], self.read_path(fp, e), f.t.info
        return None

    def tagref_param(self, p, body):
        """A reference parameter `[const] T &x` of a member function of the owner of tagged member objects of
        class T, where T is abstract or the body takes x's address (`try_set_common_origin(const
        AP_AHRS_Backend &source_backend, const Estimates &source_estimates)`, AP_AHRS.cpp:493): the tag of
        the object (a `WPtr`, by value), else None."""
        try:
            pt, ref = decl_type(p)
        except Reject:
            return None
        if ref is None or pt.kind != "record" or self.ctx is None or "name" not in p:
            return None
        tgs = mtag_targets(self.u, pt.info)
        if not tgs or any(tg["orec"] not in self.ctx.rec.chain() for tg in tgs):
            return None
        taken = any(m.get("kind") == "UnaryOperator" and m.get("opcode") == "&" and strip_object(kids(m)[0]).get("kind") == "DeclRefExpr"
                    and strip_object(kids(m)[0])["referencedDecl"]["id"] == p["id"] for m in walk(body or {}))
        if not (pt.info.abstract or taken):
            return None
        pn = self.ident(p["name"], p)
        ot = CType("obj", info=pt.info)
        self.vars[p["id"]] = (pn, ot)
        self.declared.append((p["id"], pn))
        self.tagrefs.add(p["id"])
        return (p, pn, ot, "tag")

    def mtag_member(self, e):
        """The tag (V) of a tagged member object of this object named directly (`dcm`), else None."""
        if not (MEMBER_PTRS[0] and self.u.mtags) or self.ctx is None:
            return None
        e = strip_object(e)
        if e.get("kind") == "MemberExpr" and strip_object(kids(e)[0]).get("kind") == "CXXThisExpr":
            for tg in self.u.mtags:
                if tg["field"].id == e.get("referencedMemberDecl") and tg["orec"] in self.ctx.rec.chain():
                    return V("WPtr." + tg["name"], ATOM)
        return None

    def mtag_bind(self, pre, v):
        """(pre, V) with a tag that is not a simple name bound to a temporary first (it is named per arm)."""
        if SIMPLE.match(v.text):
            return pre, v
        t = self.temp()
        return pre + ["let %s := %s" % (t, v.text)], V(t, ATOM)

    def mtag_path(self, pre, v, rec, n):
        """(pre, Path) of the member object tag v designates, of type rec: a member selected by the tag (`fm`).
        Every member it may designate must be of one class (calls through other pointers dispatch)."""
        tgs = mtag_targets(self.u, rec)
        if any(tg["rec"] is None for tg in tgs) or len({id(tg["rec"]) for tg in tgs}) != 1:
            raise Reject(n, "access through a pointer or reference to member objects of different classes (`%s`; only member function calls dispatch)" % rec.cxx)
        pre, v = self.mtag_bind(pre, v)
        self.reads.add("s")
        t = CType("record", info=tgs[0]["rec"])
        return pre, Path(("s",), "s", [("fm", (v, [(tg["name"], tg["field"].lean) for tg in tgs], t.lean))], t)

    def mtag_call(self, n, pre0, v, rec, mdecl, mname, args):
        """A call of member function mdecl on the member object tag v designates: a `match` on the tag with one
        arm per member object the pointer's class allows, each the call on that member (its final overrider);
        the result in a variable the arms assign."""
        tgs = mtag_targets(self.u, rec)
        t = self.temp()     # (the tag in a variable of its own: a `match` on a field of a variable its arms assign
        pre0, v = list(pre0) + ["let %s := %s" % (t, v.text)], V(t, ATOM)   # makes Lean's `do` elaborator fail)
        rt = fn_return_type(mdecl) if mdecl is not None else VOID
        arms = []
        for tg in tgs:
            if tg["rec"] is not None:
                op = Path(("s",), "s", [("f", tg["field"].lean)], CType("record", info=tg["rec"]))
                al, av = self.path_call(n, [], op, mdecl, mname, args)
            else:
                al, av = self.mtag_boundary_call(n, tg, mdecl, mname, args)
            arms.append((tg, al, av))
        lines = list(pre0)
        res = None
        if rt.kind != "void" and any(av is not None for _, _, av in arms):
            res = self.temp()
            # (--text-log) a `const char *` result (`active_backend->shortname()`, AP_AHRS.cpp:633): every arm assigns
            # it; the initial value is the result only for no object (undefined in C++), the empty string
            z = V('""', ATOM) if rt.kind == "string" and TEXT_LOG[0] else zero_of(rt, n)
            lines.append("let mut %s : %s := %s" % (res, rt.lean, z.text))
        lines.append("match %s with" % v.text)
        for tg, al, av in arms:
            body = list(al) + (["%s := %s" % (res, av.text)] if res is not None and av is not None else [])
            lines.append("| .%s =>  -- C++ `%s`" % (tg["name"], tg["cxx"]))
            lines += ["    " + l for l in (body or ["pure ()"])]
        lines.append("| _ => pure ()  -- (no other object: undefined in C++)")
        return lines, (V(res, ATOM) if res is not None else None)

    def mtag_boundary_call(self, n, tg, mdecl, mname, args):
        """The arm of mtag_call for a member object of a --boundary class (`AP_AHRS_SIM sim`): its overrider of
        mdecl is a boundary call, or left out if it is --drop; one it inherits from a translated base class is
        that base's member function (which must not use the object's state)."""
        bd = boundary_record_decl(self.u, tg["bname"])
        key = method_sigkey(mdecl) if mdecl is not None else None
        ov = next((m for m in kids(bd or {}) if m.get("kind") == "CXXMethodDecl" and m.get("name") == mname and method_sigkey(m) == key), None)
        if ov is not None:
            qn = "%s::%s" % (tg["bname"], mname)
            if qn in DROP:
                return self.dropped(n, ov, qn)
            tb = self.trivial_body(ov, "%s::%s" % (tg["bname"], mname), n)
            if tb is not None:
                return tb       # `void update() override { }` (AP_AHRS_SIM.h): its body, nothing or a constant
            return self.boundary_call(n, tg["field"].name, ov, mname, args)
        base = self.u.parent_record(mdecl) if mdecl is not None else None
        target = None
        for r in (base.chain() if base is not None else []):
            target = next((m for m in r.methods if m.get("kind") == "CXXMethodDecl" and method_sigkey(m) == key and not m.get("pure")), None)
            if target is not None:
                break
        tb = self.trivial_body(target, "%s::%s" % (base.cxx, mname), n) if target is not None else None
        if tb is None:
            raise Reject(n, "call of `%s` on member `%s` of a boundary class, inherited from a translated class with a body that is not empty or a constant" % (mname, tg["field"].name))
        return tb       # `virtual bool set_origin(const Location &loc) { return false; }` (AP_AHRS_Backend.h), inherited

    def trivial_body(self, m, qn, n):
        """(lines, value) of a call of member function m whose body is empty, `return;` or `return c;` with c a
        literal (the overriders of a --boundary class's member object, and what they inherit), else None."""
        b = self.u.body_of(m) or m
        cs = next((c for c in kids(b) if c.get("kind") == "CompoundStmt"), None)
        if cs is None:
            return None
        note = "pure ()  -- C++ `%s`: an empty body" % qn
        if not kids(cs) or (len(kids(cs)) == 1 and kids(cs)[0].get("kind") == "ReturnStmt" and not kids(kids(cs)[0])):
            return [note], None
        if len(kids(cs)) == 1 and kids(cs)[0].get("kind") == "ReturnStmt":
            e = strip_parens(kids(kids(cs)[0])[0])
            while e.get("kind") == "ImplicitCastExpr":
                e = strip_parens(kids(e)[0])
            if e.get("kind") in ("CXXBoolLiteralExpr", "IntegerLiteral", "FloatingLiteral"):
                pre, v = self.expr(kids(kids(cs)[0])[0])
                return pre + ["pure ()  -- C++ `%s`: returns a constant" % qn], conv(v, ctype_of(kids(kids(cs)[0])[0]), fn_return_type(m), n)
        return None

    def my_world_field(self):
        """The World field of the object whose member function this is (its state is in `s`), or None."""
        if self.ctx is None:
            return None
        return self.u.world_self.get(self.ctx.rec.id)

    def sync_self(self, touched, writes_w, n):
        """Lines before and after a call that reaches, through the World, the object whose member
        function this is (the self-reach cycle): its state (and parameters) stored into the World
        before, reloaded after if the call may change the World."""
        me = self.my_world_field()
        if me is None:
            if self.ctx is not None and WORLD_PTRS[0] and heap_field(self.ctx.rec) in touched and self.ctx.rec in self.u.heap:
                if self.fn is not None and self.fn.get("kind") == "CXXConstructorDecl":
                    raise Reject(n, "call in a constructor that may reach the heap object being constructed (`%s`) through the World" % self.ctx.rec.cxx)
                # a heap object's member function: its state into its slot (named by its own pointer `self'`)
                fld = heap_field(self.ctx.rec)
                self.uses_self = True
                self.reads |= {"s", "w"}
                self.writes.add("w")
                before = ["w := { w with %s := w.%s.set! (WPtr.index self') s }  -- this object's state into the World: the call reaches it" % (fld, fld)]
                after = []
                if writes_w:
                    after.append("s := w.%s[(WPtr.index self')]!  -- this object's state as the call left it" % fld)
                    self.writes.add("s")
                return before, after
            return [], []
        if me not in touched:
            return [], []
        before, after = [], []
        comps = []
        if "s" in self.reads | self.writes or True:
            comps.append((me, "s"))
        if self.ctx.rec.has_params() and ("p" in self.reads | self.writes):
            comps.append((me + "'p", "p"))
        before.append("w := { w with %s }  -- this object's state into the World: the call reaches it" % ", ".join("%s := %s" % (f, x) for f, x in comps))
        self.reads |= {"s", "w"}
        self.writes.add("w")
        if writes_w:
            for f, x in comps:
                after.append("%s := w.%s  -- this object's state as the call left it" % (x, f))
                self.writes.add(x)
                self.reads.add(x)
        return before, after

    def world_param(self, p):
        """A parameter of a World pointer type (a tag, by value), or a reference to the class of one
        file-scope object (another name for it, not passed: `detect(AP_Baro &baro)` called with
        `*this`); else None."""
        try:
            pt, ref = decl_type(p)
        except Reject:
            return None
        if pt.kind == "obj" and ref is None:
            if "name" not in p:
                return (p, None, pt, None)
            pn = self.ident(p["name"], p)
            self.vars[p["id"]] = (pn, pt)
            self.declared.append((p["id"], pn))
            return (p, pn, pt, None)
        if ref is not None and pt.kind == "record" and pt.info.kind == "class":
            wname = world_object_of_class(self.u, pt.info)
            if wname is not None:
                w = next(x for x in self.u.world if x["name"] == wname)
                self.aliases[p["id"]] = Path(("w",), "w", [("f", wname)], CType("record", info=w["rec"]))
                return (p, None, pt, "world:" + wname)
            if heap_singleton_field(self.u, pt.info) is not None:
                # a reference to the class of a heap singleton (`NavEKF3_core(NavEKF3 *, AP_DAL &)`): that object
                self.aliases[p["id"]] = self.singleton_path(heap_field(pt.info), p)
                return (p, None, pt, "world:*" + heap_field(pt.info))
        return None

    def world_arg(self, a):
        """The World field an argument for a reference to a World object denotes, or None."""
        e = strip_object(a)
        if WORLD_PTRS[0]:
            hr = heap_singleton_of(self.u, e)
            if hr is not None:
                return "*" + heap_field(hr)
            f = self.this_field(e) if e.get("kind") == "MemberExpr" else None
            if f is not None and f.category == "wref":
                t = self.u.wref.get((self.ctx.rec.id, f.id))
                if t is None and f.t.kind == "record":
                    t = world_object_of_class(self.u, f.t.info)
                    if t is None and heap_singleton_field(self.u, f.t.info) is not None:
                        t = "*" + heap_field(f.t.info)
                return t
        if e.get("kind") == "UnaryOperator" and e.get("opcode") == "*":
            e2 = strip_object(kids(e)[0])
            if e2.get("kind") == "CXXThisExpr":
                return self.my_world_field()
        if e.get("kind") == "DeclRefExpr":
            rid = e["referencedDecl"]["id"]
            if rid in self.aliases and self.aliases[rid].root == ("w",) and len(self.aliases[rid].steps) == 1:
                return self.aliases[rid].steps[0][1]
        if self.u.accessors or self.u.world_ids:
            return accessor_target(self.u, e)
        return None

    def ptr_deref_path(self, pexpr, pt, n, idx=None):
        """(pre, Path) of `*p` (or `p[idx]`) for a World pointer p whose class has one possible
        object, or whose possible objects are the heap objects of one class (a null pointer, or one
        to another object, would be undefined behavior in C++)."""
        if MEMBER_PTRS[0] and self.mtag_ctx_targets(pt.info, n):
            if idx is not None:
                raise Reject(n, "subscript of a pointer to member objects")
            pre, v = self.expr(pexpr)
            return self.mtag_path(pre, v, pt.info, n)      # --member-pointers: the member object the tag designates
        targets = ptr_targets(self.u, pt.info)
        if len(targets) != 1:
            if os.environ.get("CPP2LEAN_DEBUG_TARGETS"):
                sys.stderr.write("targets of %s: %s\n" % (pt.info.cxx, [(k, f) for k, f, _ in targets]))
            raise Reject(n, "access through a pointer to `%s`, which may point to %d objects (only member function calls are dispatched)" % (pt.info.cxx, len(targets)))
        kind, fld, rec = targets[0]
        if kind == "w":
            if idx is not None:
                raise Reject(n, "subscript of a pointer to a file-scope object")
            pre, _ = self.expr(pexpr)
            return pre, self.world_path(fld, n)
        pre, v = self.expr(pexpr)
        if self.ctx is not None and rec is self.ctx.rec and self.ctx.rec in self.u.heap:
            # the pointer may point to the object whose member function this is (its state is in `s`)
            if self.fn is not None and self.fn.get("kind") == "CXXConstructorDecl":
                raise Reject(n, "access in a constructor through a pointer that may point to the heap object being constructed (`%s`)" % rec.cxx)
            if self.var_views:
                raise Reject(n, "write through a pointer that may point to the heap object whose member function this is (`%s`)" % rec.cxx)
            pre = pre + ["w := { w with %s := w.%s.set! (WPtr.index self') s }  -- this object's state into the World: the pointer may point to it" % (fld, fld)]
            self.uses_self = True
            self.reads |= {"s", "w"}
            self.writes.add("w")
        self.u.wptr_index = True
        it = "(WPtr.index %s)" % v.at(ATOM)
        if idx is not None:
            pre_i, i = self.nat_index(idx)
            pre = pre + pre_i
            it = "(%s + %s)" % (it, i.at(ATOM))
        if pre or not SIMPLE.match(v.text.replace(" ", "")):
            t = self.temp()
            pre = pre + ["let %s := %s" % (t, it)]
            it = t
        self.wtouch.add(fld)
        self.reads.add("w")
        return pre, Path(("w",), "w", [("f", fld), ("i", V(it, ATOM))], CType("record", info=rec))

    def wptr_cast(self, n, ck, c):
        """Casts of World pointers, or None."""
        if ck == "PointerToBoolean":
            if self.obj_type(c) is None:
                return None
            if INS_GPS[0] and WORLD[0] and self.singleton_ref(c):
                # --ins-gps: `if (_singleton)` (AP_InertialSensor.cpp:716), as `_singleton != nullptr` (singleton_value)
                v = self.singleton_value(n)
                return [], V("%s /- C++ `%s` -/" % ("true" if v else "false", comment_safe(self.u.text_of(c) or "_singleton")), ATOM)
            pre, v = self.expr(c)
            return pre, V("(%s != WPtr.null)" % v.text, ATOM)
        try:
            d = ctype_of(n)
        except Reject:
            return None
        if d.kind != "obj":
            return None
        if ck == "NullToPointer":
            return [], V("WPtr.null", ATOM)
        if ck == "BitCast":
            cc = strip_parens(c)
            while cc.get("kind") == "ImplicitCastExpr":
                cc = strip_parens(kids(cc)[0])
            if heap_alloc_call(cc):
                return self.heap_reserve(n, d.info, cc)
            raise Reject(n, "pointer cast to `%s` of something other than a pointer to its objects" % d.cname)
        if ck in ("NoOp", "LValueToRValue", "DerivedToBase", "UncheckedDerivedToBase", "BaseToDerived"):
            return self.expr(c)
        return None

    def e_CXXThisExpr(self, n):
        if WORLD_PTRS[0] and self.ctx is not None:
            me = self.my_world_field()
            if me is not None:
                return [], V("WPtr.%s" % me, ATOM)
            if self.ctx.rec in self.u.heap and not any(w["rec"] is self.ctx.rec for w in self.u.world):
                self.uses_self = True       # a heap object's own pointer, passed by the caller
                return [], V("self'", ATOM)
            raise Reject(n, "`this` used as a value in a member function of `%s`, which has neither one file-scope object nor heap objects" % self.ctx.rec.cxx)
        raise Reject(n, self.describe(n))

    def e_CXXNullPtrLiteralExpr(self, n):
        if WORLD_PTRS[0]:
            return [], V("WPtr.null", ATOM)
        raise Reject(n, self.describe(n))

    e_GNUNullExpr = e_CXXNullPtrLiteralExpr

    def heap_ctor(self, n, rec, ce):
        """(pre, V of the new state) of constructing an object of heap class rec with the
        construction expression ce (None: zero-initialized), threading the World if the constructor
        reaches it."""
        self.deps.add(("T", rec.id))
        if ce is None or (ce.get("kind") == "CXXConstructExpr" and rec.find_ctor(ce.get("ctorType", {}).get("qualType", "")) is None):
            if ce is not None and kids(ce):
                raise Reject(n, "construction of `%s` without a translated constructor" % rec.cxx)
            return [], V("({} : %s.State)" % rec.lean, ATOM)
        ctor = rec.find_ctor(ce.get("ctorType", {}).get("qualType", ""))
        sub = self.u.context(rec, n)
        res = sub.ctor(ctor, top=True, node=n)
        self.deps.add(res.bid)
        if res.has_params or res.uses_inp or ("o" in res.writes and not PARAM_SAVE_LOG[0]) or "r" in res.reads or res.uses_own or getattr(res, "uses_sp", False):
            raise Reject(n, "`new` of `%s`, whose constructor sets parameters or reaches the boundary (heap objects have state only)" % rec.cxx)
        pre, vals, outs = self.call_args(res.cparams, kids(ce), n)
        if outs:
            raise Reject(n, "constructor with reference parameters it writes")
        uses_w = "w" in res.reads | res.writes
        objargs = [V("w", ATOM)] if uses_w else []
        if "o" in res.writes:
            # --param-save-log: the constructor saves parameters (AP_Compass_SITL's `save_dev_id`): the log is passed
            objargs.append(V("o", ATOM))
            self.reads.add("o")
            self.writes.add("o")
        if getattr(res, "uses_self", False):
            # the new object's pointer (`FUNCTOR_BIND(this, ...)` in its constructor): the slot it will take
            objargs.append(V("(WPtr.%s w.%s.size)" % (heap_field(rec), heap_field(rec)), ATOM))
            self.reads.add("w")
        if uses_w:
            self.reads.add("w")
            self.wtouch |= res.wtouch
        call = app("%s.%s" % (rec.lean, res.lean), *(objargs + vals)) if objargs + vals else V("%s.%s" % (rec.lean, res.lean), ATOM)
        t = self.temp()
        if "o" in res.writes:
            to = self.temp()
            if "w" in res.writes:
                before, after = self.sync_self(res.wtouch, True, n)
                tw = self.temp()
                self.writes.add("w")
                return pre + before + ["let (%s, %s, %s) := %s" % (t, tw, to, call.text), "w := %s" % tw, "o := %s" % to] + after, V(t, ATOM)
            before, after = self.sync_self(res.wtouch, False, n) if uses_w else ([], [])
            return pre + before + ["let (%s, %s) := %s" % (t, to, call.text), "o := %s" % to], V(t, ATOM)
        if "w" in res.writes:
            before, after = self.sync_self(res.wtouch, True, n)
            tw = self.temp()
            self.writes.add("w")
            return pre + before + ["let (%s, %s) := %s" % (t, tw, call.text), "w := %s" % tw] + after, V(t, ATOM)
        before, after = self.sync_self(res.wtouch, False, n) if uses_w else ([], [])
        return pre + before + ["let %s := %s" % (t, call.text)], V(t, ATOM)

    def wptr_new(self, n):
        """`new C(args)`, `new (std::nothrow) C(args)`: the object is constructed and appended to the
        World's heap slots of C; the value is the pointer to it. Allocation never fails (as for
        `new T[k]`, README.md "Phase 2"). Placement new `new (&p[i]) C(args)` into memory a --heap-alloc
        function reserved: the object is constructed in that slot."""
        t = self.obj_type(n)
        if t is None:
            raise Reject(n, "`new` of something other than an object of a translated class")
        rec = t.info
        if rec not in self.u.heap:
            raise Reject(n, "`new` of `%s`, which has no heap slots" % rec.cxx)
        ce = next((c for c in kids(n) if c.get("kind") in ("CXXConstructExpr", "ExprWithCleanups", "InitListExpr")), None)
        if ce is not None and ce.get("kind") == "ExprWithCleanups":
            ce = kids(ce)[0]
        if ce is not None and ce.get("kind") != "CXXConstructExpr":
            raise Reject(n, "`new` with an initializer list")
        places = [c for c in kids(n) if c is not ce and c.get("kind") != "ExprWithCleanups"]
        op_t = (n.get("operatorNewDecl") or {}).get("type", {}).get("qualType", "")
        fld = heap_field(rec)
        if places and "nothrow_t" not in op_t:
            # placement new into memory a --heap-alloc function reserved: construct in that slot
            pl = strip_parens(places[0])
            while pl.get("kind") == "ImplicitCastExpr":
                pl = strip_parens(kids(pl)[0])
            if pl.get("kind") == "UnaryOperator" and pl.get("opcode") == "&":
                r = self.resolve_path(kids(pl)[0])
            elif self.obj_type(pl) is not None:
                r = self.ptr_deref_path(pl, self.obj_type(pl), n)
            else:
                r = None
            if r is None or r[1].root != ("w",) or len(r[1].steps) != 2 or r[1].steps[0][1] != fld:
                raise Reject(n, "placement `new` of `%s` somewhere other than a slot of its heap objects" % rec.cxx)
            pre0, path = r
            pre, v = self.heap_ctor(n, rec, ce)
            self.wtouch.add(fld)
            return pre0 + pre + [self.write_path(path, v, n)], None
        pre, v = self.heap_ctor(n, rec, ce)
        ti = self.temp()
        self.reads.add("w")
        self.writes.add("w")
        self.wtouch.add(fld)
        return pre + ["let %s := w.%s.size" % (ti, fld), "w := { w with %s := w.%s.push %s }" % (fld, fld, v.at(ATOM))], \
            V("(WPtr.%s %s)" % (fld, ti), ATOM)

    def heap_reserve(self, n, rec, call):
        """`(C *)f(sizeof(C) * k, ...)` of a --heap-alloc function: k zero-filled heap slots of C
        reserved for placement new; the value points to the first. Allocation never fails."""
        if rec not in self.u.heap:
            raise Reject(n, "memory for `%s`, which has no heap slots" % rec.cxx)
        args = kids(call)[1:]
        if strip_parens(kids(call)[0]).get("kind") == "MemberExpr":
            args = kids(call)[1:]
        if not args:
            raise Reject(n, "allocation without a size")
        sz = strip_parens(args[0])
        while sz.get("kind") == "ImplicitCastExpr":
            sz = strip_parens(kids(sz)[0])
        k = None
        if sz.get("kind") == "BinaryOperator" and sz.get("opcode") == "*":
            a, b = [strip_parens(x) for x in kids(sz)]
            for x, y in ((a, b), (b, a)):
                if x.get("kind") == "UnaryExprOrTypeTraitExpr" and x.get("name") == "sizeof" and \
                        rec.cxx in (x.get("argType") or {}).get("qualType", "") + (x.get("argType") or {}).get("desugaredQualType", ""):
                    k = y
        if k is None:
            raise Reject(n, "allocation whose size is not `sizeof(%s) * k`" % rec.cxx)
        pre, kv = self.nat_index(k)
        fld = heap_field(rec)
        ti = self.temp()
        self.reads.add("w")
        self.writes.add("w")
        self.wtouch.add(fld)
        return pre + ["let %s := w.%s.size" % (ti, fld),
                      "w := { w with %s := w.%s ++ Array.replicate %s ({} : %s.State) }  -- C++ `%s`: k slots, constructed by placement new" %
                      (fld, fld, kv.at(ATOM), rec.lean, comment_safe(self.u.text_of(n) or "alloc"))], V("(WPtr.%s %s)" % (fld, ti), ATOM)

    def functor_op(self, n, name, args):
        """--world-pointers: `f()` (the bound member function called on its object, `WFun.call`),
        `f == g`, `f != g`, `f = g` on `Functor<void>`s."""
        if name == "operator=" and len(args) == 2:
            pre0, path = self.lvalue(args[0], n)
            pre, v = self.expr(args[1])
            return pre0 + pre + [self.write_path(path, v, n)], None
        if name in ("operator==", "operator!=") and len(args) == 2:
            pre, (a, b) = self.operands(args)
            return pre, V("%s %s %s" % (a.at(CMP + 1), "==" if name == "operator==" else "!=", b.at(CMP + 1)), CMP)
        if name == "operator()" and len(args) == 1:
            pre, f = self.expr(args[0])
            h = self.wfun_call_helper(n)
            self.wtouch |= h["wtouch"]
            self.deps.add(("wfuncall",))
            self.reads.add("w")
            before, after = self.sync_self(h["wtouch"], True, n)
            return pre + before + ["w := WFun.call %s w" % f.at(ATOM)] + after, None
        raise Reject(n, "`%s` on a functor" % name)

    def wfun_call_helper(self, n):
        """`WFun.call`: a functor called, i.e. its member function on its object (the dispatch
        function of the method over the objects of its class)."""
        if self.u.wfun_call is not None:
            return self.u.wfun_call
        self.u.wfun_call = {"wtouch": set()}        # (a functor called inside a bound method: no recursion)
        lines = ["/-- C++ `f()` of a `Functor<void>` (--world-pointers): the member function it binds, called on the object",
                 "it is bound to; an empty functor (a null call in C++) changes nothing. -/",
                 "def WFun.call (f : WFun) (w : World) : World :=", "  match f with"]
        deps = {("wfun",), ("world",)}
        wtouch = set()
        for rec, m in self.u.funcs:
            targets = ptr_targets(self.u, rec)
            if not targets:
                continue
            h = self.dispatch_helper(n, CType("obj", info=rec), targets, m, m.get("name"))
            if h["o"] or h["ret"].kind != "void" or any(pn is not None for _, pn, _, _ in h["cparams"]):
                raise Reject(n, "functor of `%s::%s`, which takes arguments, returns a value or writes outputs" % (rec.cxx, m.get("name")))
            deps.add(h["id"])
            wtouch |= h["wtouch"]
            lines.append("  | .%s p => %s p w" % (functor_ctor(rec, m), h["name"]))
        lines.append("  | _ => w")
        self.u.wfun_call = {"wtouch": wtouch, "key": (10 ** 6, "", 0, 3), "lines": lines, "deps": deps, "id": ("wfuncall",)}
        return self.u.wfun_call

    def sem_object(self, obj):
        """--semaphores: is obj a semaphore member (or a semaphore-typed expression)?"""
        o = strip_object(obj)
        if o.get("kind") == "MemberExpr" and o.get("referencedMemberDecl") in self.u.sem_fields:
            return True
        try:
            return ctype_of(o).kind == "sem"
        except Reject:
            return False

    def sem_call(self, n, mname):
        """--semaphores: a member function of a semaphore: succeeds, does nothing (one thread)."""
        rt = ctype_of(n)
        note = comment_safe(self.u.text_of(n) or mname)
        if rt.kind == "void":
            return ["pure ()  -- C++ `%s`: a semaphore (no effect, --semaphores)" % note], None
        if rt.kind == "bool":
            return [], V("true /- C++ `%s`: a semaphore always succeeds (--semaphores) -/" % note, ATOM)
        raise Reject(n, "member function `%s` of a semaphore with a result of type `%s`" % (mname, rt.cname))

    def wptr_call(self, n, pexpr, pt, mdecl, mname, args):
        """`p->m(args)` through a World pointer: the final overrider of the object p points to. One
        possible file-scope object: a call on its path; heap objects of one class: on the slot p
        names; several classes or objects: a dispatch function (`match` on the tag)."""
        if MEMBER_PTRS[0] and self.mtag_ctx_targets(pt.info, n):
            pre0, pv = self.expr(pexpr)
            return self.mtag_call(n, pre0, pv, pt.info, mdecl, mname, args)    # --member-pointers: a member object of this object
        targets = ptr_targets(self.u, pt.info)
        if not targets and FRONT_ENDS[0]:
            # --front-ends: a pointer to a class without objects in the World is null (above), so the call is
            # not reached (it would be undefined behavior): the value of the result type's zero, no effect
            pre0, _ = self.expr(pexpr)
            rt = fn_return_type(mdecl) if mdecl is not None else VOID
            note = "pure ()  -- C++ `%s->%s(...)`: not reached (a pointer to `%s`, of which the World has no object, is null)" % (
                comment_safe(self.u.text_of(pexpr) or "p"), mname, pt.info.cxx)
            if rt.kind == "void":
                return pre0 + [note], None
            return pre0 + [note], zero_of(rt, n)
        if not targets:
            raise Reject(n, "call of `%s` through a pointer to `%s`, of which the program has no object" % (mname, pt.info.cxx))
        if len(targets) == 1:
            pre0, op = self.ptr_deref_path(pexpr, pt, n)
            return self.path_call(n, pre0, op, mdecl, mname, args)
        pre0, pv = self.expr(pexpr)
        h = self.dispatch_helper(n, pt, targets, mdecl, mname)
        self.deps.add(h["id"])
        self.wtouch |= h["wtouch"]
        self.reads.add("w")
        objargs = [pv, V("w", ATOM)]
        writes = {"w"}
        if h["o"]:
            objargs.append(V("o", ATOM))
            self.reads.add("o")
            writes.add("o")
        before, after = self.sync_self(h["wtouch"], True, n)
        setters = {"w": self.write_w, "o": lambda v: self.write_path(Path(("o",), "o", [], None), v, n)}
        pre, vals, outs = self.call_args(h["cparams"], args, n)
        p2, v = self.apply_call(h["name"], writes, objargs, vals, outs, h["ret"], n, setters)
        return pre0 + pre + before + p2 + after, v

    def dispatch_helper(self, n, pt, targets, mdecl, mname):
        """The dispatch function of a virtual call `p->m(...)` through a pointer of type `B *` that may
        point to several objects: one `match` arm per possible object, calling the final overrider of
        that object's class on its World field (or heap slot) and storing its state back."""
        key = (pt.info.id, mdecl["id"])
        if key in self.u.dispatch:
            return self.u.dispatch[key]
        arms = []
        for kind, fld, rec in targets:
            sub = self.u.context(rec, n)
            target = sub.resolve(mdecl, virtual_dispatch=True)
            if qualified_name(self.u, target) in DROP:
                raise Reject(n, "dispatch to `%s`, which is dropped" % qualified_name(self.u, target))
            res = sub.method(target, n)
            if "r" in res.reads or res.uses_own:
                raise Reject(n, "dispatch to `%s::%s`, which reads `const` reference members or a back-reference" % (rec.cxx, mname))
            if getattr(res, "uses_sp", False):
                raise Reject(n, "dispatch to `%s::%s`, which saves parameters of an object it does not name (--param-save-log)" % (rec.cxx, mname))
            if kind == "h" and ("p" in res.reads | res.writes or (res.uses_inp and not FRONT_ENDS[0]) or ("o" in res.writes and not OUTPUT_LOG[0])):
                raise Reject(n, "dispatch to `%s::%s` of a heap object, which has parameters or reaches the boundary" % (rec.cxx, mname))
            if kind == "w" and "o" in res.writes and not OUTPUT_LOG[0]:
                raise Reject(n, "dispatch to `%s::%s`, which writes boundary outputs (use --output-log)" % (rec.cxx, mname))
            arms.append((kind, fld, rec, res))
        shapes = {tuple((pt_.lean, ref, pn is None) for _, pn, pt_, ref in r.cparams) for _, _, _, r in arms}
        outsets = {tuple(pn for _, pn, _ in r.outs) for _, _, _, r in arms}
        rets = {r.ret.lean if r.ret.kind != "void" else "void" for _, _, _, r in arms}
        if len(shapes) != 1 or len(outsets) != 1 or len(rets) != 1:
            raise Reject(n, "dispatch of `%s` over overriders whose parameters, reference results or results differ" % mname)
        rep = arms[0][3]
        uses_o = any("o" in r.writes for _, _, _, r in arms)
        name = "WPtr.call'%s'%s" % (pt.info.lean.replace(".", "_"), lean_field(mname, mdecl))
        while any(d["name"] == name for d in self.u.dispatch.values()):
            name += "'"
        pnames = ["a%d" % i for i, (_, pn, _, _) in enumerate(rep.cparams) if pn is not None]
        binders = ["(ptr : WPtr)", "(w : World)"] + (["(o : Outputs)"] if uses_o else [])
        binders += ["(a%d : %s)" % (i, pt_.lean) for i, (_, pn, pt_, _) in enumerate(rep.cparams) if pn is not None]
        outs = [(pn, pt_) for _, pn, pt_ in rep.outs]
        rtys = ["World"] + (["Outputs"] if uses_o else []) + [pt_.lean_atom for _, pt_ in outs]
        if rep.ret.kind != "void":
            rtys.append(rep.ret.lean_atom)
        out_args = {pn: "a%d" % i for i, (_, pn, _, _) in enumerate(rep.cparams) if pn is not None}
        lines = ["/-- C++ `%s` through a pointer of type `%s *` (--world-pointers): the final overrider of the object it" % (comment_safe(mname), comment_safe(pt.info.cxx)),
                 "points to, called on that object; a null pointer (undefined behavior in C++) changes nothing. -/",
                 "def %s %s : %s :=" % (name, " ".join(binders), " × ".join(rtys)), "  match ptr with"]
        deps = {("world",), ("wptr",)}
        wtouch = set()
        for kind, fld, rec, res in arms:
            deps.add(res.bid)
            wtouch |= res.wtouch | {fld}
            if kind == "w":
                lines.append("  | .%s =>" % fld)
                spath, ppath = "w.%s" % fld, "w.%s'p" % fld
            else:
                lines.append("  | .%s %s =>" % (fld, "i" if "s" in res.reads | res.writes or getattr(res, "uses_self", False) else "_"))
                spath, ppath = "w.%s[i]!" % fld, None
            cargs = []
            if "p" in res.reads | res.writes:
                cargs.append(ppath)
            if "s" in res.reads | res.writes:
                cargs.append(spath if SIMPLE.match(spath) else "(%s)" % spath)
            if "w" in res.reads | res.writes:
                cargs.append("w")
            if "o" in res.writes:
                cargs.append("o")
            if res.uses_inp:
                cargs.append("w.%s'inp" % fld)
                if kind == "h":
                    self.u.heap_inp.add(fld)
            if getattr(res, "uses_self", False):
                cargs.append(".%s" % fld if kind == "w" else "(.%s i)" % fld)
            cargs += pnames
            comps = (["p'"] if "p" in res.writes else []) + (["s'"] if "s" in res.writes else []) + \
                (["w'"] if "w" in res.writes else []) + (["o'"] if "o" in res.writes else []) + ["x'%d" % i for i in range(len(outs))] + \
                (["r'"] if res.ret.kind != "void" else [])
            call = "%s.%s%s" % (rec.lean, res.lean, "".join(" " + a for a in cargs))
            if comps:
                lines.append("    let %s := %s" % (comps[0] if len(comps) == 1 else "(%s)" % ", ".join(comps), call))
            W = "w'" if "w" in res.writes else "w"
            upd = []
            if "s" in res.writes:
                upd.append("%s := %s" % (fld, "s'" if kind == "w" else "%s.%s.set! i s'" % (W, fld)))
            if "p" in res.writes:
                upd.append("%s'p := p'" % fld)
            wv = "{ %s with %s }" % (W, ", ".join(upd)) if upd else W
            items = [wv] + (["o'" if "o" in res.writes else "o"] if uses_o else []) + ["x'%d" % i for i in range(len(outs))] + \
                (["r'"] if res.ret.kind != "void" else [])
            lines.append("    " + (items[0] if len(items) == 1 else "(%s)" % ", ".join(items)))
        dflt = ["w"] + (["o"] if uses_o else []) + [out_args[pn] for pn, _ in outs] + (["default"] if rep.ret.kind != "void" else [])
        lines.append("  | _ => " + (dflt[0] if len(dflt) == 1 else "(%s)" % ", ".join(dflt)))
        if uses_o:
            deps.add(("outputs",))
        for _, pn, pt_, _ in rep.cparams:
            deps |= type_deps(pt_)
        deps |= type_deps(rep.ret)
        h = {"name": name, "id": ("disp",) + key, "wtouch": wtouch, "o": uses_o, "cparams": rep.cparams, "ret": rep.ret,
             "block": {"key": (10 ** 6, "", 0, 2) + (len(self.u.dispatch),), "lines": lines, "deps": deps, "id": ("disp",) + key}}
        self.u.dispatch[key] = h
        return h

    def e_CXXNewExpr(self, n):
        """`new (std::nothrow) T[k]` (only as the value of a local pointer that holds arrays of its own,
        or a function's result): an array of k zeros. The C++ elements are indeterminate until
        written (reading one is undefined); `new (std::nothrow)` returning a null pointer is not
        modeled (allocation succeeds)."""
        if WORLD_PTRS[0] and not n.get("isArray"):
            return self.wptr_new(n)
        if not POINTER_PARAMS[0]:
            raise Reject(n, "`new`")
        if not n.get("isArray"):
            raise Reject(n, "`new` of one object (only arrays `new T[k]`, held by a local pointer, are translated)")
        pe = self.pp_pointee(n)
        sizes = [c for c in kids(n) if (c.get("type") or {}).get("qualType", "").strip() in self.INT_SPELLINGS and ctype_of(c).is_int()]
        if pe is None or len(sizes) != 1 or pe[0].kind == "void":
            raise Reject(n, "`new` of something other than an array of numbers")
        pre, k = self.nat_index(sizes[0])
        note = "-- C++ `%s`: k elements, indeterminate until written (zeros here; reading one before it is written is undefined)" % \
            comment_safe(self.u.text_of(n) or "new")
        return pre + [note], V("Array.replicate %s %s" % (k.at(ATOM), zero_of(pe[0], n).at(ATOM)), APP)

    def e_CXXDeleteExpr(self, n):
        if WORLD_PTRS[0] and not n.get("isArray") and kids(n) and self.obj_type(kids(n)[0]) is not None:
            # `delete sensor;` of a heap object (a back end whose init failed): its slot stays, unused
            pre = self.effect(kids(n)[0], discard_pure=True)
            return pre + ["pure ()  -- C++ `%s`: the object's slot is left as it is (nothing refers to it again)" % comment_safe(self.u.text_of(n) or "delete")], None
        d = strip_object(kids(n)[0]) if kids(n) else {}
        pv = self.ptrs.get(d.get("referencedDecl", {}).get("id")) if d.get("kind") == "DeclRefExpr" else None
        if not POINTER_PARAMS[0] or pv is None or pv.kind != "owned" or not n.get("isArray"):
            raise Reject(n, "`delete`")
        return ["pure ()  -- C++ `%s`: the storage is not modeled" % comment_safe(self.u.text_of(n) or "delete[]")], None

    def byte_view(self, n):
        """`((uint8_t *)&x)[j]` (crc_crc64): byte j of the object representation of an integer
        variable x, read only, on this little-endian target (arm64): `(x >>> 8 j)` truncated to
        `UInt8`; j at or beyond the size of x reads outside the object (undefined in C++). Else None."""
        base = strip_parens(kids(n)[0])
        while base.get("kind") == "ImplicitCastExpr" and base.get("castKind") in ("LValueToRValue", "NoOp"):
            base = strip_parens(kids(base)[0])
        if base.get("kind") not in ("CStyleCastExpr", "CXXReinterpretCastExpr", "CXXStaticCastExpr"):
            return None
        pe = self.pp_pointee(base)
        a = strip_parens(kids(base)[0])
        while a.get("kind") == "ImplicitCastExpr" and a.get("castKind") in ("BitCast", "NoOp"):
            a = strip_parens(kids(a)[0])
        if pe is None or pe[0] != CType("int", 8, False) or a.get("kind") != "UnaryOperator" or a.get("opcode") != "&":
            return None
        r = self.resolve_path(kids(a)[0])
        if r is None or r[1].t is None or not r[1].t.is_int() or r[1].t.usize:
            raise Reject(n, "byte view of something other than an integer variable, member or element")
        if self.pp_lv_written(n):
            raise Reject(n, "write through a byte view")
        pre, p = r
        t = p.t
        x = self.read_path(p, n)
        if t.signed:
            x = V("%s.toUInt%d %s" % (t.lean, t.bits, x.at(ATOM)), APP)
        pre_j, j = self.nat_index(kids(n)[1])
        u = "UInt%d" % t.bits
        v = V("%s (%s >>> Nat.to%s (8 * %s))" % ("%s.toUInt8" % u if t.bits != 8 else "id", x.at(ATOM), u, j.at(ATOM)), APP)
        return pre + pre_j, v

    # -- phase 2: loops bounded by a runtime value (--runtime-loops, README.md "Phase 2") -------
    # A loop whose trip count is a value the loop does not change is a Lean `for` over that count,
    # computed before the loop; the C++ types must show that the counter reaches its bound without
    # wrapping, else the loop is rejected (or, with --general-loops, a fuel loop).

    @staticmethod
    def int_range(t):
        return (-(1 << (t.bits - 1)), (1 << (t.bits - 1)) - 1) if t.signed else (0, (1 << t.bits) - 1)

    @staticmethod
    def as_int(v, t):
        """Lean text of the value v of integer type t as an `Int`."""
        return "%s.toInt" % v.at(ATOM) if t.signed else "(Int.ofNat %s.toNat)" % v.at(ATOM)

    def rl_invariant(self, e, body):
        """Is e (an integer expression) unchanged by the loop body: no effects, and every variable it
        reads is not assigned in the body (a data member only in a const member function)?"""
        if AHRS_EXT[0] and self.boundary_input_call(e):
            return True         # --ahrs-ext: `i < _ins.get_accel_count()` (AP_AHRS_DCM.cpp:830): an input, fixed during the call
        if self.has_effects(e):
            return False
        written = self.assigned(body) | (self.pp_mutable(body) if POINTER_PARAMS[0] else set())
        for m in walk(e):
            k = m.get("kind")
            if k == "DeclRefExpr":
                rid = m["referencedDecl"]["id"]
                if rid in written:
                    return False
                if rid in self.ptrs or rid in self.unions:
                    return False
            elif k == "MemberExpr":
                if not (self.fn or {}).get("type", {}).get("qualType", "").endswith(" const") and \
                        not ((RING_BUFFERS[0] or EKF_ARRAYS[0]) and self.rb_member_invariant(m, body)) and \
                        not (REACHABLE[0] and self.member_chain_invariant(m, body)):
                    return False
            elif k in ("ArraySubscriptExpr", "UnaryOperator") and (k != "UnaryOperator" or m.get("opcode") == "*"):
                return False
        return True

    def memcmp_object(self, n, args):
        """--ahrs-ext: `memcmp(this, &x, sizeof(*this))` with x an object of this class (`Location::is_zero`,
        AP_Common/Location.cpp:15, x the constant `definitely_zero`): 0 if every member is equal, else 1 (memcmp's
        nonzero value has an unspecified sign; only its truth is used). Equal members are equal bytes when the
        padding bits are zero (Location's constructors zero the whole object); floating members are rejected
        (`-0.0 == 0.0` and NaN differ from byte equality)."""
        a0, a1 = strip_object(args[0]), strip_object(args[1])
        while a0.get("kind") == "ImplicitCastExpr":
            a0 = strip_object(kids(a0)[0])
        while a1.get("kind") == "ImplicitCastExpr":
            a1 = strip_object(kids(a1)[0])
        if self.ctx is None or a0.get("kind") != "CXXThisExpr" or a1.get("kind") != "UnaryOperator" or a1.get("opcode") != "&" or \
                ctype_of(kids(a1)[0]) != CType("record", info=self.ctx.rec):
            raise Reject(n, "`memcmp` other than `memcmp(this, &x, sizeof(*this))` with x an object of this class")
        a2 = strip_parens(args[2])
        while a2.get("kind") == "ImplicitCastExpr":
            a2 = strip_parens(kids(a2)[0])
        if not (a2.get("kind") == "UnaryExprOrTypeTraitExpr" and a2.get("name") == "sizeof" and kids(a2) and
                strip_object(kids(a2)[0]).get("kind") == "UnaryOperator" and strip_object(kids(strip_object(kids(a2)[0]))[0]).get("kind") == "CXXThisExpr"):
            raise Reject(n, "`memcmp` of a size other than `sizeof(*this)`")
        pre, other = self.expr(kids(a1)[0])
        b = self.temp()
        self.reads.add("s")
        conj = []

        def leaves(t, x, y):
            if t.kind == "record":
                for f in t.info.all_fields():
                    if f.category != "state":
                        raise Reject(n, "`memcmp` of an object with a member that is not state (`%s`)" % f.name)
                    leaves(f.t, "%s.%s" % (x, f.lean), "%s.%s" % (y, f.lean))
            elif t.kind == "array":
                for k in range(t.n):
                    leaves(t.elem, "%s[%d]!" % (x, k), "%s[%d]!" % (y, k))
            elif t.is_float():
                raise Reject(n, "`memcmp` of an object with a floating member")
            else:
                conj.append("%s == %s" % (x, y))
        leaves(CType("record", info=self.ctx.rec), "s", b)
        return pre + ["let %s := %s" % (b, other.text)], V("(if %s then (0 : Int32) else (1 : Int32))" % " && ".join(conj or ["true"]), ATOM)

    def wpref_path(self, f, n):
        """--ahrs-ext: the World path of the parameter a reference member f of a member object binds (`AP_Float
        &_kp_yaw` of AP_AHRS_DCM, bound by `AP_AHRS_DCM dcm{_kp_yaw, ...}` of AP_AHRS, AP_AHRS.h:1020: the parameter
        `_kp_yaw` of the World object `ahrs`, `w.ahrs'p._kp_yaw`): the owner's constructor parameter that f's
        initializer names, the owner's member initializer's argument at that position."""
        cls = f.owner
        k = None
        for m in cls.methods:
            if m.get("kind") != "CXXConstructorDecl":
                continue
            defn = self.u.body_of(m) or m
            ps = [p["id"] for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
            for ini in kids(defn):
                if ini.get("kind") == "CXXCtorInitializer" and ini.get("anyInit", {}).get("id") == f.id and kids(ini):
                    e = strip_object(kids(ini)[0])
                    if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in ps:
                        k = ps.index(e["referencedDecl"]["id"])
        hits = []
        for w in self.u.world:
            if w["rec"] is None or w.get("static"):
                continue
            for g in w["rec"].all_fields():
                if g.category == "state" and g.t.kind == "record" and g.t.info is cls and g.decl.get("hasInClassInitializer"):
                    e = strip_object(kids(g.decl)[-1])
                    while e.get("kind") in ("ExprWithCleanups", "MaterializeTemporaryExpr") and kids(e):
                        e = strip_object(kids(e)[0])
                    args = kids(e) if e.get("kind") in ("CXXConstructExpr", "InitListExpr") else []
                    a = strip_object(args[k]) if k is not None and k < len(args) else {}
                    h = w["rec"].field_by_id(a.get("referencedMemberDecl")) if a.get("kind") == "MemberExpr" else None
                    if h is not None and h.category == "param":
                        hits.append((w["name"], h))
        if len(hits) != 1:
            raise Reject(n, "reference member `%s` to a parameter that is not bound to one parameter of one World object" % f.name)
        wname, h = hits[0]
        self.wtouch.add(wname)
        self.reads.add("w")
        return Path(("w",), "w", [("f", wname + "'p"), ("f", h.lean)], h.t)

    def static_boundary_return(self, decl, seen=()):
        """--ahrs-ext: the returned expression of static member function decl if its body is one `return e;` and
        e reads a boundary object (a singleton accessor of a --boundary class, or another such function), else None."""
        d = self.u.body_of(decl) or decl
        if d.get("storageClass") != "static" and decl.get("storageClass") != "static" or decl["id"] in seen:
            return None
        if any(c.get("kind") == "ParmVarDecl" for c in kids(d)):
            return None
        cs = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
        if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
            return None
        e = kids(kids(cs)[0])[0]
        for m in walk(e):
            if m.get("kind") == "CallExpr" and self.boundary_object_call(m):
                return e
            if m.get("kind") == "CallExpr" and kids(m):
                c = strip_parens(kids(m)[0])
                while c.get("kind") == "ImplicitCastExpr":
                    c = strip_parens(kids(c)[0])
                d2 = self.u.decl((c.get("referencedDecl") or {}).get("id"))
                if d2 is not None and d2.get("kind") == "CXXMethodDecl" and self.static_boundary_return(d2, seen + (decl["id"],)) is not None:
                    return e
        return None

    def boundary_input_call(self, e):
        """--ahrs-ext: is e (without conversions) a call of a const member function without arguments on a
        boundary object (an input of this object, one value during the call)?"""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("IntegralCast", "LValueToRValue", "NoOp"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") != "CXXMemberCallExpr" or kids(e)[1:]:
            return False
        callee = strip_parens(kids(e)[0])
        d = self.u.decl(callee.get("referencedMemberDecl")) if callee.get("kind") == "MemberExpr" else None
        return d is not None and d["type"]["qualType"].rstrip().endswith("const") and self.boundary_obj(kids(callee)[0]) is not None

    def value_range(self, e):
        """--reachable: (lo, hi) of the values an integer expression can have, known beyond its type: a
        counter of an enclosing loop (its start to its bound), or a data member whose every write in the
        program assigns a constant (`stateIndexLim`, AP_NavEKF3: 9, 12, 15, 21, 23; and zero, the value
        of a zero-filled object); else None."""
        if not REACHABLE[0]:
            return None
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("IntegralCast", "LValueToRValue", "NoOp"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in self.var_range:
            return self.var_range[e["referencedDecl"]["id"]]     # (only while its loop's body is translated)
        if e.get("kind") == "MemberExpr" and strip_object(kids(e)[0]).get("kind") == "CXXThisExpr":
            return member_constant_range(self.u, e.get("referencedMemberDecl"))
        return None

    def assigned_anywhere(self):
        if self._assigned_fn is None:
            body = next((c for c in kids(self.fn) if c.get("kind") == "CompoundStmt"), {}) if self.fn else {}
            self._assigned_fn = self.assigned(body)
        return self._assigned_fn

    def rl_bound_type(self, e):
        """The type of the value e had before the integral promotions and conversions clang applied
        for the comparison (its range bounds the value)."""
        e = strip_parens(e)
        while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in ("IntegralCast", "LValueToRValue", "NoOp"):
            inner = strip_parens(kids(e)[0])
            it = ctype_of(inner)
            if not it.is_int():
                break
            e = inner
        return ctype_of(e)

    def runtime_for(self, n):
        """`for (T i = start; i op bound; step)` with step `i++`/`++i` (op `<`, `<=`) or `i--`/`--i`
        (op `>`, `>=`), start and bound any values the body does not change, and no assignment to i
        in the body: the counter takes the values start, start ± 1, ... while the test holds. The
        bound's type must keep the counter in its type: for `<` every value of the bound's type is at
        most max(T) + 1, for `<=` at most max(T) - 1, for `>` at least min(T) - 1, for `>=` at least
        min(T) + 1; the comparison's type must hold every value of T and of the bound's type."""
        init, condvar, cond, inc, body = (kids(n) + [{}] * 5)[:5]
        if condvar or not init or not cond or not inc:
            raise Reject(n, FOR_BAD)
        if init.get("kind") == "BinaryOperator" and init.get("opcode") == "=" and \
                strip_parens(kids(init)[0]).get("kind") == "DeclRefExpr" and \
                strip_parens(kids(init)[0])["referencedDecl"]["id"] in self.loop_only:
            d = self.u.decl(strip_parens(kids(init)[0])["referencedDecl"]["id"])
            start_n = kids(init)[1]
        elif init.get("kind") == "DeclStmt" and len(kids(init)) == 1 and kids(init)[0].get("kind") == "VarDecl" and kids(kids(init)[0]):
            d = kids(init)[0]
            start_n = kids(d)[0]
        else:
            raise Reject(n, FOR_BAD)
        t = ctype_of(d)
        rid = d["id"]
        step = self.loop_counter_step(inc, rid)
        if not t.is_int() or step not in (1, -1) or rid in self.assigned(body):
            raise Reject(n, FOR_BAD)
        c = strip_parens(cond)
        if c.get("kind") != "BinaryOperator" or c.get("opcode") not in ("<", "<=", ">", ">="):
            raise Reject(n, FOR_BAD)
        op = c["opcode"]
        if (op in ("<", "<=")) != (step == 1):
            raise Reject(n, FOR_BAD)
        lhs = strip_parens(kids(c)[0])
        while lhs.get("kind") == "ImplicitCastExpr" and lhs.get("castKind") in ("IntegralCast", "LValueToRValue"):
            lhs = strip_parens(kids(lhs)[0])
        if lhs.get("kind") != "DeclRefExpr" or lhs["referencedDecl"]["id"] != rid:
            raise Reject(n, FOR_BAD)
        bound_n = kids(c)[1]
        ct = ctype_of(kids(c)[0])           # the type of the comparison (the counter after promotion)
        bt = self.rl_bound_type(bound_n)
        if not (ct.is_int() and bt.is_int() and ctype_of(bound_n) == ct):
            raise Reject(n, FOR_BAD)
        tlo, thi = self.int_range(t)
        clo, chi = self.int_range(ct)
        bc = self.const_int(bound_n)
        blo, bhi = (bc, bc) if bc is not None else (self.value_range(bound_n) or self.int_range(bt))
        if not (clo <= tlo and thi <= chi and clo <= blo and bhi <= chi):
            raise Reject(n, FOR_BAD + " (the comparison's type does not hold every value of the counter and of the bound)")
        ok = {"<": bhi <= thi + 1, "<=": bhi <= thi - 1, ">": blo >= tlo - 1, ">=": blo >= tlo + 1}[op]
        if not ok:
            raise Reject(n, FOR_BAD + " (a bound of type `%s` may make the counter of type `%s` wrap)" % (bt.cname, t.cname))
        if not self.rl_invariant(bound_n, body):
            raise Reject(n, FOR_BAD + " (the bound may change in the loop)")
        pre_s, sv = self.expr(start_n)
        pre_b, bv = self.expr(bound_n)
        lo, b = self.temp(), self.temp()
        lines = pre_s + ["let %s : %s := %s" % (lo, t.lean, sv.text)] + pre_b + ["let %s : %s := %s" % (b, ct.lean, bv.text)]
        x, y = (self.as_int(V(b, ATOM), ct), self.as_int(V(lo, ATOM), t)) if step == 1 else \
            (self.as_int(V(lo, ATOM), t), self.as_int(V(b, ATOM), ct))
        trips = "(%s - %s%s).toNat" % (x, y, " + 1" if op in ("<=", ">=") else "")
        name = self.fresh_local(self.ident(d["name"], d), rid)
        if FRONT_ENDS[0]:
            self.declared.append((rid, name))
        self.vars[rid] = (name, t)
        if REACHABLE[0]:
            sc = self.const_int(start_n)
            slo, shi = (sc, sc) if sc is not None else (self.value_range(start_n) or (tlo, thi))
            # the counter's values in the body: from the start to the bound (`<=`) or one before it
            self.var_range[rid] = (min(slo, blo), max(shi, bhi - (1 if op == "<" else 0))) if step == 1 else (min(slo, blo + (1 if op == ">" else 0)), max(shi, bhi))
        used = rid in referenced_decls(body)
        saved = self.copy_da()
        self.loops.append("for")
        if REACHABLE[0]:
            self.counters.add(rid)      # immutable in each iteration (a local reference may index with it)
        body_lines, _ = self.stmt(body)
        if REACHABLE[0]:
            self.counters.discard(rid)
        self.loops.pop()
        self.var_range.pop(rid, None)
        self.da = saved
        if used:
            head = "for %s' in [0:%s] do  -- C++ loop bounded by a runtime value (--runtime-loops)" % (name, trips)
            pre_body = ["let %s : %s := %s %s Nat.to%s %s'" % (name, t.lean, lo, "+" if step == 1 else "-", t.lean, name)]
        else:
            head = "for _ in [0:%s] do  -- C++ loop bounded by a runtime value (--runtime-loops)" % trips
            pre_body = []
        return lines + [head] + ["  " + l for l in pre_body + (body_lines or ["pure ()"])], False

    def runtime_while(self, n):
        """`while (k--) body` with k an unsigned local or parameter that the body does not assign and
        no `break` in the body: k iterations, each first decrementing k (as the test does); the
        failing test decrements once more (k wraps to its maximum, as in C++)."""
        cond, body = kids(n)
        c = strip_parens(cond)
        while c.get("kind") == "ImplicitCastExpr" and c.get("castKind") in ("IntegralToBoolean", "IntegralCast"):
            c = strip_parens(kids(c)[0])
        if RING_BUFFERS[0] and not (c.get("kind") == "UnaryOperator" and c.get("opcode") == "--"):
            return self.countdown_while(n)
        if n.get("hasVar") or c.get("kind") != "UnaryOperator" or c.get("opcode") != "--" or not c.get("isPostfix"):
            raise Reject(n, WHILE_BAD)
        v = strip_parens(kids(c)[0])
        if v.get("kind") != "DeclRefExpr" or v["referencedDecl"]["id"] not in self.vars:
            raise Reject(n, WHILE_BAD)
        rid = v["referencedDecl"]["id"]
        name, t = self.vars[rid]
        if not t.is_int() or t.signed or rid in self.assigned(body) or rid not in self.mutable:
            raise Reject(n, "`while (k--)` loop with k not a variable of an unsigned type that the body does not assign")
        if any(m.get("kind") == "BreakStmt" for m in self.own_jumps(body)):
            raise Reject(n, "`while (k--)` loop with a `break`")
        self.read.add(rid)
        dec = "%s := %s - 1" % (name, name)
        saved = self.copy_da()
        self.loops.append("rwhile")
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        return ["for _ in [0:%s.toNat] do  -- C++ `while (%s--)` (--runtime-loops)" % (name, v["referencedDecl"]["name"])] + \
            ["  " + l for l in [dec] + body_lines] + [dec + "  -- the failing test decrements too"]

    def cursor_for(self, n):
        """`for (; p != q; p++)` with p and q pointers into the same array, the body moving neither:
        q's offset minus p's iterations (a C++ loop with p past q would leave the array: undefined)."""
        init, condvar, cond, inc, body = (kids(n) + [{}] * 5)[:5]
        if init or condvar or not cond or not inc:
            raise Reject(n, FOR_BAD)
        c = strip_parens(cond)
        pv = self.ptr_cursor(kids(inc)[0]) if inc.get("kind") == "UnaryOperator" and inc.get("opcode") == "++" else None
        if pv is None or c.get("kind") != "BinaryOperator" or c.get("opcode") not in ("!=", "<"):
            raise Reject(n, FOR_BAD)
        a, b = kids(c)
        if self.ptr_cursor(a) is not pv:
            raise Reject(n, FOR_BAD)
        rb = self.ptr_ref(b)
        if rb is None or rb[0] or rb[1].text() != pv.base.text():
            raise Reject(n, FOR_BAD)
        moved = set()
        for m in walk(body):
            if m.get("kind") in ("UnaryOperator", "CompoundAssignOperator", "BinaryOperator") and \
                    (m.get("opcode") in ("++", "--", "+=", "-=", "=")):
                t = strip_object(kids(m)[0])
                if t.get("kind") == "DeclRefExpr":
                    moved.add(t["referencedDecl"]["id"])
        if moved & set(self.ptrs):
            raise Reject(n, FOR_BAD + " (the body moves a pointer)")
        if any(m.get("kind") == "ContinueStmt" for m in self.own_jumps(body)):
            raise Reject(n, "`continue` in a pointer loop (it would skip the step)")
        end = rb[2].text if rb[2] is not None else "0"
        saved = self.copy_da()
        self.loops.append("rwhile")
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        return ["for _ in [0:%s - %s] do  -- C++ pointer loop (--runtime-loops)" % (end, pv.off)] + \
            ["  " + l for l in body_lines + ["%s := %s + 1" % (pv.off, pv.off)]], False

    def pp_arg(self, a, p, pt, ref, roots):
        """call_args (--pointer-params) for an argument bound to a pointer parameter of a translated
        function: (pre, value, out) with out the Path (or Splice) the callee's result is written back
        to; None if the parameter is not a pointer (a `T &`)."""
        q = p.get("type", {}).get("qualType", "").rstrip()
        if not q.endswith("*"):
            return None
        if pt.kind == "array" and pt.n == 0:
            return self.ptr_arg(a, ref, roots)
        sa = strip_object(a)
        if MAVLINK[0] and strip_casts(a).get("kind") == "DeclRefExpr" and strip_casts(a)["referencedDecl"]["id"] in self.ptr_scalars:
            # --mavlink: a scalar pointer parameter passed on (`crc_accumulate(*p++, crcAccum)`, checksum.h:89)
            rid = strip_casts(a)["referencedDecl"]["id"]
            name, t = self.vars[rid]
            path = Path(("var", rid), name, [], t)
            return [], self.read_path(path, a, check_init=ref == "cptr"), (path if ref == "mut" else None)
        if not (sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&"):
            raise Reject(a, "argument for a pointer parameter used only as `*p` (a scalar) other than `&x`")
        r = self.resolve_path(kids(sa)[0])
        if r is None:
            raise Reject(a, "argument `&x` for a pointer parameter where x is not a variable, member or element")
        pre, path = r
        return pre, self.read_path(path, a, check_init=ref == "cptr"), (path if ref == "mut" else None)

    def dropped_call(self, e):
        """The qualified name of the --drop function that e calls (its arguments without effects), else None."""
        e = strip_parens(e)
        while e.get("kind") in ("ImplicitCastExpr", "ExprWithCleanups"):
            e = strip_parens(kids(e)[0])
        if e.get("kind") != "CallExpr":
            return None
        c = strip_parens(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_parens(kids(c)[0])
        d = self.u.decl(c.get("referencedDecl", {}).get("id"))
        if d is None or d.get("kind") != "FunctionDecl":
            return None
        qn = qualified_name(self.u, d)
        if qn not in DROP or any(self.has_effects(a) for a in kids(e)[1:]):
            return None
        return qn

    def dropped_local(self, d):
        """`int old = fedisableexcept(...);` with fedisableexcept --drop: the variable holds a value
        outside the model; it is left out, and so must be every statement that reads it."""
        qn = self.dropped_call(kids(d)[0])
        self.u.dropped[d["id"]] = d["name"]
        return ["pure ()  -- C++ `%s`: left out (--drop `%s`)" % (comment_safe(self.u.text_of(d) or d["name"]), qn)]

    def has_kept_effects(self, n):
        """has_effects, except for calls of --drop functions whose arguments have no effects (their
        effect is outside the model: `feenableexcept`)."""
        if self.dropped_call(n) is not None:
            return False
        if any(self.has_kept_effects(c) for c in kids(n) if isinstance(c, dict)):
            return True
        return self.has_effects(dict(n, inner=[]))

    def written_first(self, d, t):
        """For a local array d of t.n elements without initializer: are all its elements assigned by
        statements `d[c] = e` (c a constant, e not reading d) of the enclosing block before any other
        statement uses d?"""
        ds = self.u.parent.get(d["id"])
        blk = self.u.parent.get(ds["id"]) if ds is not None else None
        if blk is None or blk.get("kind") != "CompoundStmt":
            return False
        stmts = kids(blk)
        i = next((j for j, s in enumerate(stmts) if s is ds), None)
        if i is None:
            return False
        done = set()
        for s in stmts[i + 1:]:
            if len(done) == t.n:
                return True
            if d["id"] not in referenced_decls(s):
                continue
            s2 = strip_parens(s)
            if s2.get("kind") == "BinaryOperator" and s2.get("opcode") == "=":
                lhs = strip_parens(kids(s2)[0])
                b = kids(lhs)[0] if lhs.get("kind") == "ArraySubscriptExpr" else {}
                if b.get("castKind") == "ArrayToPointerDecay" and strip_parens(kids(b)[0]).get("referencedDecl", {}).get("id") == d["id"] \
                        and d["id"] not in referenced_decls(kids(s2)[1]):
                    c = self.const_int(kids(lhs)[1])
                    if c is not None and 0 <= c < t.n:
                        done.add(c)
                        continue
            return False
        return len(done) == t.n

    def bit_builtin(self, n, name, a):
        """`__builtin_popcount(x)` (unsigned int: the number of one bits) and `__builtin_ffs(x)` (int:
        one plus the index of the lowest one bit, 0 for 0), as counts over the 32 bits."""
        t = ctype_of(a)
        if t != CType("int", 32, name == "__builtin_ffs"):
            raise Reject(n, "`%s` of `%s`" % (name, t.cname))
        pre, v = self.expr(a)
        if name == "__builtin_popcount":
            return pre, V("Nat.toInt32 ((List.range 32).countP (fun k'bit => (%s >>> Nat.toUInt32 k'bit) &&& 1 != 0))" % v.at(ATOM), APP)
        return pre, V("Option.elim ((List.range 32).find? (fun k'bit => (Int32.toUInt32 %s >>> Nat.toUInt32 k'bit) &&& 1 != 0)) (0 : Int32) (fun k'bit => Nat.toInt32 (k'bit + 1))" % v.at(ATOM), APP)

    def local_ref(self, d):
        """`T &qw = q1;` (QuaternionT::from_rotation_matrix): a local non-const reference bound to a
        data member of this object or of a local variable or parameter, through data members only
        (no element, which an index could move): another name for that member, read and written as
        it (README.md, "Phase 2")."""
        pre, p = None, None
        r = self.resolve_path(kids(d)[0])
        if r is not None:
            pre, p = r
        if EKF_ARRAYS[0] and p is not None and not pre and p.root[0] in ("s", "var", "w") and self.stable_steps(kids(d)[0], p):
            self.aliases[d["id"]] = p      # --ekf-arrays: through elements whose indices do not change while it is live
            return []
        if REACHABLE[0] and p is not None and p.root[0] in ("s", "var", "w") and self.stable_path(p):
            self.aliases[d["id"]] = p      # `auto &baro = dal.baro();`: through elements whose indices are fixed values
            return pre
        if FRONT_ENDS[0] and p is not None and p.root[0] in ("s", "var", "w") and pre and \
                all(re.match(r"^let t'\d+ := ", l) for l in pre) and all(k in ("f", "i") for k, _ in p.steps):
            # --front-ends: `Compass::mag_state &state = _compass._state[Compass::StateIndex(instance)];`
            # (AP_Compass_Backend.cpp:21): through an accessor whose index is computed once, before
            self.aliases[d["id"]] = p
            return pre
        if p is None or pre or any(k != "f" for k, _ in p.steps) or p.root[0] not in ("s", "var"):
            raise Reject(d, "local reference variable `%s` bound to something other than a data member (through data members only) of this object or of a local variable" % d["name"])
        self.aliases[d["id"]] = p
        return []

    def stable_steps(self, init, p):
        """--ekf-arrays: do the indices of path p (of the reference initializer init) read only
        variables that keep their value while a local reference to it is live: never assigned in
        the function, or the counter of an enclosing counted loop (immutable in each iteration)?"""
        if any(k not in ("f", "i", "fi") for k, _ in p.steps):
            return False
        idxs = []
        for m in walk(init):
            if m.get("kind") in ("CallExpr", "CXXMemberCallExpr") or (m.get("kind") == "CXXOperatorCallExpr" and operator_name(m) != "operator[]"):
                return False
            if m.get("kind") == "ArraySubscriptExpr":
                idxs.append(kids(m)[1])
            elif m.get("kind") == "CXXOperatorCallExpr" and len(kids(m)) == 3:
                idxs.append(kids(m)[2])
        for x in idxs:
            for m in walk(x):
                if m.get("kind") == "DeclRefExpr" and m["referencedDecl"]["id"] in self.vars:
                    rid = m["referencedDecl"]["id"]
                    if rid in self.mutable and rid not in self.counters and not (INS_GPS[0] and self.for_counter(rid, init)):
                        return False
        return True

    def for_counter(self, rid, node):
        """--ins-gps: is rid the variable a `for` loop around node declares and steps, which its body never
        assigns (`for (uint8_t i=0; i<ARRAY_SIZE(params); i++) { auto &rate_ms = params[i].rate_ms; ...`,
        AP_GPS.cpp:340, a loop of any kind): fixed in each iteration?"""
        up = self.u.parent.get(node["id"])
        while up is not None and up.get("kind") != "ForStmt":
            up = self.u.parent.get(up["id"])
        if up is None:
            return False
        init = kids(up)[0] if kids(up) else None
        if init is None or init.get("kind") != "DeclStmt" or not any(c.get("id") == rid for c in kids(init)):
            return self.for_counter(rid, up)
        body = kids(up)[-1]
        for m in walk(body):
            k = m.get("kind")
            t = kids(m)[0] if (k in ("BinaryOperator", "CompoundAssignOperator") and m.get("opcode", "").endswith("=") and
                               m.get("opcode") not in ("==", "!=", "<=", ">=")) or (k == "UnaryOperator" and m.get("opcode") in ("++", "--")) else None
            if t is not None and strip_object(t).get("kind") == "DeclRefExpr" and strip_object(t)["referencedDecl"]["id"] == rid:
                return False
            if k == "UnaryOperator" and m.get("opcode") == "&" and strip_object(kids(m)[0]).get("kind") == "DeclRefExpr" and \
                    strip_object(kids(m)[0])["referencedDecl"]["id"] == rid:
                return False
        return True

    def stable_path(self, p):
        """--reachable: is every index of path p a fixed value while a reference bound to it is live: a
        numeral, a `let` temporary, an immutable local or loop counter converted, or the index of a heap
        singleton (`WPtr.index w.AP_DAL'_singleton`, which never changes once it is allocated)?"""
        if any(k not in ("f", "i", "av") for k, _ in p.steps):
            return False
        names = {nm: rid for rid, (nm, _) in self.vars.items()}
        for k, x in p.steps:
            if k != "i":
                continue
            txt = x.text.strip()
            if re.match(r"^\(?WPtr\.index w\.[\w']+'_singleton\)?$", txt) or re.match(r"^(\d+|t'\d+)$", txt):
                continue
            m = re.match(r"^\(?(?:[\w.]+\.toNat(?:ClampNeg)? )?([\w']+)\)?$", txt)
            if m and m.group(1) in names and (names[m.group(1)] not in self.mutable or names[m.group(1)] in self.counters):
                continue
            return False
        return True

    def storage_size_check(self, s):
        """`do { assert_storage_size<T, N> x; (void)x; } while (false)` (AP_Common's ASSERT_STORAGE_SIZE):
        an object of a class template whose instantiation only static_asserts the size of T; no effect."""
        body = kids(s)[0] if kids(s) else {}
        c = strip_parens(kids(s)[1]) if len(kids(s)) > 1 else {}
        if body.get("kind") != "CompoundStmt" or c.get("kind") != "CXXBoolLiteralExpr" or c.get("value") or len(kids(body)) != 2:
            return False
        d, v = kids(body)
        vd = kids(d)[0] if d.get("kind") == "DeclStmt" and len(kids(d)) == 1 else {}
        if vd.get("kind") != "VarDecl" or not vd.get("type", {}).get("qualType", "").startswith("assert_storage_size<"):
            return False
        v = strip_parens(v)
        return v.get("kind") == "CStyleCastExpr" and ctype_of(v).kind == "void" and \
            strip_object(kids(v)[0]).get("referencedDecl", {}).get("id") == vd["id"]

    def call_args(self, params, args, n):
        """Translate the arguments of a call (default arguments expanded); returns (pre, values,
        outs) where outs lists the Paths of arguments bound to non-const reference parameters.
        params: (decl, lean name or None for a boundary parameter, CType, ref)."""
        res, outs = [], []
        roots = []                  # --pointer-params: the arrays passed to pointer parameters (aliasing check)
        for i, a in enumerate(args):
            if i >= len(params):
                raise Reject(a, "argument without a parameter")
            p, pn, pt, ref = params[i]
            if ref == "va":
                res.append(self.var_args(args[i:]))
                break
            if ref == "tbuf":
                # --text-buffers: the caller's buffer (a local `char buffer[N]` or its own `char *` parameter), written back
                sa = strip_parens(a)
                while sa.get("kind") == "ImplicitCastExpr" and sa.get("castKind") in ("ArrayToPointerDecay", "LValueToRValue", "NoOp"):
                    sa = strip_parens(kids(sa)[0])
                r = self.resolve_path(sa) if sa.get("kind") == "DeclRefExpr" else None
                if r is None or r[1].steps or r[1].t is None or r[1].t.kind != "textbuf":
                    raise Reject(a, "argument for a `char *` parameter that is not a local buffer or a `char *` parameter (--text-buffers)")
                outs.append(r[1])
                res.append((r[0], self.read_path(r[1], a, check_init=False)))
                continue
            if RING_BUFFERS[0] and p.get("type", {}).get("qualType", "").replace("const ", "", 1).strip() == "void *":
                # --ring-buffers: `&x` for an element parameter (`ekf_ring_buffer::recall(&element, t)`): x
                sa = rb_strip(a)
                if not (sa.get("kind") == "UnaryOperator" and sa.get("opcode") == "&"):
                    raise Reject(a, "argument for a `void *` element parameter other than `&x`")
                a = kids(sa)[0]
                if ref == "mut":
                    r = self.lvalue(a, a)
                    outs.append(r[1])
                    res.append((r[0], self.read_path(r[1], a, check_init=False)))
                else:
                    res.append(self.expr(a))
                continue
            if ref == "tag":
                # --member-pointers: a reference parameter modeled as a tag (tagref_param): the tag of the argument
                v = self.mtag_member(a)
                mr = ([], v, None) if v is not None else self.mtag_ref(a)
                if mr is None:
                    raise Reject(a, "argument for a reference to member objects that is not one of them")
                res.append((mr[0], mr[1]))
                continue
            if ref == "elem":
                # --ins-gps: the index of the element of a World object's array the argument names (heap_elem_refs)
                ea = strip_object(a)
                if ea.get("kind") == "DeclRefExpr" and ea["referencedDecl"]["id"] in self.vars and \
                        self.u.elem_params.get(ea["referencedDecl"]["id"]) == self.u.elem_params.get(p["id"]):
                    self.read.add(ea["referencedDecl"]["id"])
                    res.append(([], V(self.vars[ea["referencedDecl"]["id"]][0], ATOM)))
                    continue
                r = self.resolve_path(ea)
                tgt = self.u.elem_params.get(p["id"])
                if r is None or not r[1].steps or r[1].steps[-1][0] != "i" or tgt is None or \
                        [x for k, x in r[1].steps[:-1] if k == "f"][-len(tgt[2]):] != [lean_field(x, a) for x in tgt[2]]:
                    raise Reject(a, "argument for a reference to an element of `%s` that is not such an element" % ".".join(tgt[2] if tgt else ["?"]))
                res.append((r[0], r[1].steps[-1][1]))
                continue
            if pn is None:
                if isinstance(ref, str) and ref.startswith("world:") and self.world_arg(a) != ref[6:]:
                    # --world-pointers: a reference to the class of one file-scope object must be bound to it
                    raise Reject(a, "argument for a reference to `%s` that is not that object (`%s`)" % (pt.cname, ref[6:]))
                continue
            if MAVLINK[0] and p.get("id") in self.u.struct_ptr_params:
                # --mavlink: the object the argument points to, written back if the callee writes it
                pre_a, path = self.struct_ptr_target(a)
                if ref == "mut":
                    outs.append(path)
                    res.append((pre_a, self.read_path(path, a, check_init=False)))
                else:
                    res.append((pre_a, self.read_path(path, a)))
                continue
            if POINTER_PARAMS[0] and not C_MODE[0] and ref in ("mut", "cptr") and a.get("kind") != "CXXDefaultArgExpr":
                r = self.pp_arg(a, p, pt, ref, roots)
                if r is not None:
                    pre_a, v_a, out_a = r[:3]
                    if out_a is not None:
                        outs.append(out_a)
                    res.append((pre_a, v_a))
                    if len(r) > 3:
                        res.append(([], r[3]))      # --array-offsets: the offset after the array
                    continue
            if a.get("kind") == "CXXDefaultArgExpr" and not ((REACHABLE[0] or FRONT_ENDS[0]) and ref == "ptr"):
                res.append(self.expr(kids(a)[0]))
                continue
            if pt.kind == "array" and pt.n == 0 and ref == "mut":
                # C: an array (or an array pointer parameter) for a pointer parameter the callee
                # writes through: passed and written back, as a reference argument
                sa = strip_parens(a)
                while sa.get("kind") == "ImplicitCastExpr" and sa.get("castKind") in ("ArrayToPointerDecay", "LValueToRValue", "NoOp"):
                    sa = strip_parens(kids(sa)[0])
                r = self.resolve_path(sa) if sa.get("kind") == "DeclRefExpr" else None
                if r is None or r[1].steps or r[1].t.kind != "array":
                    raise Reject(a, "argument for an array pointer parameter that is not a local array or an array pointer parameter")
                outs.append(r[1])
                res.append((r[0], self.read_path(r[1], a, check_init=False)))
                continue
            if ref in ("mut", "cptr") and pt.kind != "array" and C_MODE[0] and strip_object(a).get("kind") == "UnaryOperator" \
                    and strip_object(a).get("opcode") == "&":
                # C: `&x` for a scalar pointer parameter (`__rem_pio2f(x, &y)`): x, written back if the callee writes it
                r = self.resolve_path(kids(strip_object(a))[0])
                if r is None:
                    raise Reject(a, "argument `&x` for a pointer parameter where x is not a variable, member or element")
                pre, path = r
                if ref == "mut":
                    outs.append(path)
                res.append((pre, self.read_path(path, a, check_init=ref == "cptr")))
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
                if (REACHABLE[0] or FRONT_ENDS[0]) and sa.get("kind") == "CXXDefaultArgExpr" and kids(sa):
                    sa = strip_parens(kids(sa)[0])      # the default null (`getYawData(yaw, var)`, `drain_accumulated_samples()`)
                cptr = FRONT_ENDS[0] and p.get("type", {}).get("qualType", "").lstrip().startswith("const ")
                if self.is_null(sa):
                    if not cptr:
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
                if not cptr:
                    outs.append(path)
                res.append(([], V("true", ATOM)))
                res.append((pre, self.read_path(path, a, check_init=False)))
                continue
            if ref == "mut":
                self.var_views = True       # also a view of a variable (`stopping_point_ned_m.xy()`, AC_WPNav.cpp:549)
                try:
                    r = self.resolve_path(a)
                finally:
                    self.var_views = False
                if r is None:
                    raise Reject(a, "argument for a reference parameter that is not a variable, member or element")
                pre, path = r
                outs.append(path)
                # an uninitialized variable may be passed to be written (its placeholder is passed)
                res.append((pre, self.read_path(path, a, check_init=False)))
            else:
                pre_a, v_a = self.expr(a)
                if (C_STRINGS[0] or BYTE_OBJECTS[0]) and pn is not None:
                    ta = ctype_of(a)
                    if ta.is_int() and pt.is_int() and ta.bits == pt.bits == 64 and ta.usize != pt.usize and not ta.signed and not pt.signed:
                        # `unsigned long` (clang drops the `size_t` sugar of `sizeof`) for a `size_t` parameter, or back
                        v_a = int_conv(v_a, ta, pt)
                res.append((pre_a, v_a))
        for p, pn, pt, ref in params[len(args):]:
            if ref == "va":
                res.append(([], V("#[]", ATOM)))        # no variadic arguments
            elif p.get("kind") == "Global":
                # --mavlink: the caller's file-scope variable, written back if the callee writes it
                gid = self.global_var(p["id"])
                self.read.add(gid)
                res.append(([], V(pn, ATOM)))
                if ref == "mut":
                    self.mutable.add(gid)
                    self.gl_use[gid].add("w")
                    outs.append(Path(("var", gid), pn, [], pt))
            elif p.get("kind") == "HalStorage":
                # --hal-storage: the caller's HAL storage, written back if the callee writes it
                self.mutable.add(self.HS)
                self.read.add(self.HS)
                self.hs_use |= {"r", "w"} if ref == "mut" else {"r"}
                res.append(([], V(self.HS, ATOM)))
                if ref == "mut":
                    outs.append(Path(("var", self.HS), self.HS, [], pt))
        pre, vals = self.sequence(res)
        return pre, vals, outs

    def var_args(self, args):
        """--c-strings: the variadic arguments of a call, after the default argument promotions
        clang made explicit: `#[CArg.ofInt32 x, CArg.dbl d, CArg.ptr a o, ...]` (README.md, "Phase 2b")."""
        pre, items = [], []
        for a in args:
            if self.pp_pointee(a) is not None:
                r = self.ptr_ref(a)
                if r is None or not same_storage(r[1].t.elem, CHAR):
                    raise Reject(a, "variadic argument that is a pointer other than into a byte array (`%%s`)")
                p0, base, off = r
                pre += p0
                items.append("CArg.ptr %s %s" % (self.read_path(base, a).at(ATOM), off.at(ATOM) if off is not None else "0"))
                continue
            t = ctype_of(a)
            p0, v = self.expr(a)
            if self.has_effects(a) and pre:
                pass
            pre += p0
            if t.kind == "double":
                items.append("CArg.dbl %s" % v.at(ATOM))
            elif t.is_int() and t.name is None and t.bits in (32, 64):
                if t.usize:
                    v = app("USize.toUInt64", v)
                items.append("CArg.of%s%d %s" % ("Int" if t.signed and not t.usize else "UInt", t.bits, v.at(ATOM)))
            else:
                raise Reject(a, "variadic argument of type `%s`" % t.cname)
        return pre, V("#[%s]" % ", ".join(items), ATOM)

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
        if "w" in writes:
            comps.append(("w", None))
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
            if (kind in ("p", "s", "w", "o") and setters.get(kind) is None) or (kind == "out" and p is None):
                return [], None             # the state of a temporary object, or a value for a null pointer: discarded
            return [setters[kind](call) if kind in ("p", "s", "w", "o") else self.out_line(p, call, n)], None
        # a component of a temporary object (setter None) is bound to `_`
        names = ["_" if (kind in ("p", "s", "w", "o") and setters.get(kind) is None) or (kind == "out" and p is None) else self.temp() for kind, p in comps]
        pre = ["let (%s) := %s" % (", ".join(names), call.text)]
        value = None
        # the callee's World first: the object's own parts are then stored into it (the callee's
        # World holds the object's state from before the call, which it does not reach)
        order = sorted(zip(comps, names), key=lambda x: 0 if x[0][0] == "w" else 1)
        for (kind, p), t in order:
            if kind in ("p", "s", "w", "o"):
                if t != "_":
                    pre.append(setters[kind](V(t, ATOM)))
            elif kind == "out":
                if p is not None:           # None: a null pointer argument, the value is discarded
                    pre.append(self.out_line(p, V(t, ATOM), n))
            else:
                value = V(t, ATOM)
        return pre, value

    def e_CallExpr(self, n):
        callee, args = kids(n)[0], kids(n)[1:]
        if WORLD_PTRS[0]:
            fb = functor_bind(self.u, n)
            if fb is not None:
                # `FUNCTOR_BIND(obj, &C::m, void)`: the functor of m bound to obj's pointer
                if len(args) != 1:
                    raise Reject(n, "`Functor::bind` with %d arguments" % len(args))
                pre, v = self.expr(args[0])
                self.deps.add(("wfun",))
                return pre, V("(WFun.%s %s)" % (functor_ctor(*fb), v.at(ATOM)), ATOM)
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
            if name == "__builtin_expect" and len(args) == 2:
                return self.expr(args[0])           # a branch-prediction hint: the value of its first argument
            if name in BUILTIN_PREDICATES and len(args) == 1:
                pre, v = self.builtin_predicate(n, name, args[0])
                return self.c_int(n, pre, v)
            if name in ("__builtin_fma", "__builtin_fmaf") and len(args) == 3:
                ts = [ctype_of(a) for a in args]
                t = DOUBLE if name == "__builtin_fma" else FLOAT
                if any(x != t for x in ts):
                    raise Reject(n, "`%s` on `%s`" % (name, ", ".join(x.cname for x in ts)))
                pre, vals = self.operands(args)
                return pre, app("%s.fma" % t.lean, *vals)
            if name in ("__builtin_popcount", "__builtin_ffs") and len(args) == 1:
                return self.bit_builtin(n, name, args[0])
            if C_STRINGS[0] and name in ("__builtin_va_start", "__builtin_va_end", "__builtin_va_copy"):
                return self.va_builtin(n, name, args)
            raise Reject(n, "builtin `%s`" % name)
        if not (callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "FunctionToPointerDecay"):
            raise Reject(n, "call through a function pointer or object")
        ref = strip_parens(kids(callee)[0])
        if ref.get("kind") == "MemberExpr":
            sd = self.u.decl(ref.get("referencedMemberDecl"))
            sd = self.u.canonical(sd) if sd is not None else None
            if sd is not None and sd.get("kind") == "CXXMethodDecl" and sd.get("storageClass") == "static" and \
                    not self.has_effects(kids(ref)[0]):
                return self.static_method_call(n, sd, args)
        if ref.get("kind") != "DeclRefExpr":
            raise Reject(n, "indirect call")
        decl = self.u.decl(ref["referencedDecl"]["id"])
        name = ref["referencedDecl"]["name"]
        if FRONT_ENDS[0] and WORLD_PTRS[0] and not args and ctype_of(n).kind == "obj":
            tgt = accessor_target(self.u, n)
            if tgt is not None:
                return [], V("WPtr.%s" % tgt, ATOM)     # `AP::sitl()`: a singleton accessor returning a pointer (--front-ends)
        if not args:
            v = self.constexpr_value(decl, n)
            if v is not None:
                return [], v
        if decl is not None and decl.get("kind") == "CXXMethodDecl":
            return self.static_method_call(n, self.u.canonical(decl), args)
        if C_MODE[0] and decl is not None and qualified_name(self.u, decl) in DROP:
            return self.dropped(n, decl, qualified_name(self.u, decl))
        if OUTPUT_FN and OUTPUT_LOG[0] and decl is not None and qualified_name(self.u, decl) in OUTPUT_FN:
            return self.output_fn_call(n, decl, name, args), None
        target = self.u.function_for(decl)
        if target is not None:
            if C_STRINGS[0]:
                self.object_pointer_spec(target, args, n)
            fr = self.u.free_result(target, n)
            self.deps.add(target["id"])
            pre, vals, outs = self.call_args(fr.cparams, args, n)
            return self.free_call(n, self.qual(self.u.ns, fr.lean), fr, pre, vals, outs)
        qn = qualified_name(self.u, decl) if decl is not None else name
        if qn in DROP:
            return self.dropped(n, decl, qn)
        if name == "memset" and len(args) == 3 and EKF_ARRAYS[0]:
            r = self.md_memset(n, args)
            if r is not None:
                return r
        if name == "memcpy" and len(args) == 3 and EKF_ARRAYS[0] and decl is not None and not self.u.in_set(decl):
            r = self.md_memcpy(n, args)
            if r is not None:
                return r
        if MISSION[0] and name == "memcpy" and len(args) == 3 and decl is not None and not self.u.in_set(decl):
            r = self.union_memcpy(n, args)
            if r is not None:
                return r
        if MAVLINK[0] and name == "memcpy" and len(args) == 3 and decl is not None and not self.u.in_set(decl):
            r = self.struct_memcpy(n, args)
            if r is not None:
                return r
        if MAVLINK[0] and name == "memset" and len(args) == 3 and decl is not None and not self.u.in_set(decl):
            r = self.struct_memset(n, args)
            if r is not None:
                return r
        if (C_STRINGS[0] or BYTE_OBJECTS[0]) and name in CS_FUNCTIONS and decl is not None and not self.u.in_set(decl):
            r = self.cs_call(n, name, args)
            if r is not None:
                return r
        if RING_BUFFERS[0] and self.rb_info() is not None and name in ("memset", "memcpy", "free", "calloc") \
                and decl is not None and not self.u.in_set(decl):
            return self.rb_call(n, name, args)
        if POINTER_PARAMS[0] and name in ("memset", "memcpy", "memcmp") and len(args) == 3:
            r = self.mem_call(n, name, args)
            if r is not None:
                return r
        if name == "memset" and len(args) == 3:
            return self.memset_zero(n, args)
        if name in ("isnan", "isinf", "isfinite") and len(args) == 1 and ctype_of(args[0]).is_int() and ctype_of(n).kind == "bool" \
                and not self.has_effects(args[0]):
            return [], V("true" if name == "isfinite" else "false", ATOM)
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
        if name in MODULE_FNS and C_MODE[0]:
            return self.module_call(n, name, args)
        if name in self.u.externs:
            lean_name, nargs = self.u.externs[name]
            used = [kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in args]
            pre, vals = self.operands(used[:nargs] if nargs is not None else used)
            return pre, app(lean_name, *vals)
        if self.u.in_set(decl):
            raise Reject(n, "call to `%s`, which has no definition in the translated files (see --extern)" % name)
        if name in ("abs", "labs", "llabs") and len(args) == 1 and ctype_of(args[0]).is_int() and ctype_of(args[0]) == ctype_of(n):
            pre, v = self.expr(args[0])
            t = ctype_of(n)
            return pre, V("(if %s < %s then -%s else %s)" % (v.at(CMP + 1), lit("0", t).text, v.at(NEG), v.text), ATOM)
        if AHRS_EXT[0] and name == "memcmp" and len(args) == 3:
            return self.memcmp_object(n, args)
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
        if f.startswith(LIBM_NS + "."):
            self.uses_libm = True
            self.u.libm_modules.add(f.rsplit(".", 1)[0])
        return pre, app(f, *vals)

    def module_call(self, n, name, args):
        """C: a call of a function translated in another module (--module-sig, that translation's
        signatures.json): its parameters as that translation took them (an array pointer parameter is
        the array, written back if the callee writes it)."""
        e = MODULE_FNS[name]
        ps = []
        for p in e["params"]:
            q = p["type"]
            pt = parse_type_str(q, q, n)
            ps.append(({"kind": "ParmVarDecl", "name": p["name"]}, lean_ident(p["name"], n), pt, p["ref"]))
        pre, vals, outs = self.call_args(ps, args, n)
        ret = parse_type_str(e["ret"], e["ret"], n) if e["ret"] != "void" else VOID
        self.u.libm_modules.add(e["lean"].rsplit(".", 1)[0])
        p2, v = self.apply_call(e["lean"], set(), [], vals, outs, ret, n, {})
        return pre + p2, v

    def builtin_predicate(self, n, name, a):
        """`__builtin_isnan(x)`, `__builtin_signbit(x)` (libm/env/math.h's isnan, signbit): the truth value."""
        t = ctype_of(a)
        if not t.is_float():
            raise Reject(n, "`%s` on `%s`" % (name, t.cname))
        pre, v = self.expr(a)
        return pre, app("%s.%s" % (t.lean, BUILTIN_PREDICATES[name]), v)

    def static_method_call(self, n, decl, args):
        qn = qualified_name(self.u, decl)
        if qn in DROP:
            return self.dropped(n, decl, qn)
        owner = self.u.decl(decl.get("parentDeclContextId")) or self.u.parent.get(decl["id"])
        if owner is not None and (owner.get("name") in BOUNDARY or qualified_name(self.u, owner) in BOUNDARY):
            return self.boundary_call(n, qualified_name(self.u, owner), decl, decl.get("name"), args, static=True)
        if AP_PARAM[0] and qn == "AP_Param::setup_object_defaults":
            return self.ap_param_defaults(n, args), None
        if PARAM_EXT[0] and qn == "AP_Param::set_default_by_name":
            return self.param_default_by_name(n, args)
        rec = self.u.parent_record(decl)
        if AHRS_EXT[0] and rec is not None and not args and self.ctx is not None:
            e = self.static_boundary_return(decl)
            if e is not None:
                # --ahrs-ext: a static member function without parameters whose body is `return e;` and which reads the
                # boundary (`AP_AHRS_Backend::get_EAS2TAS`, `return AP::baro().get_EAS2TAS();`, AP_AHRS_Backend.cpp:277;
                # `get_TAS2EAS`, `return 1.0/get_EAS2TAS();`): e, translated here (its boundary reads inputs of this object)
                return self.expr(e)
        if rec is None or decl.get("storageClass") != "static":
            raise Reject(n, "call of method `%s` without an object" % decl.get("name"))
        fr = self.u.static_result(rec, decl, n)
        self.deps.add(fr.key)
        pre, vals, outs = self.call_args(fr.cparams, args, n)
        return self.free_call(n, self.qual(rec.lean, fr.lean), fr, pre, vals, outs)

    def free_call(self, n, fname, fr, pre, vals, outs):
        """The call of a translated free function or static member function (with the World if it
        reaches it, --world-pointers)."""
        if not getattr(fr, "world_reads", False):
            p2, v = self.apply_call(fname, set(), [], vals, outs, fr.ret, n, {})
            return pre + p2, v
        self.reads.add("w")
        self.wtouch |= fr.wtouch
        before, after = self.sync_self(fr.wtouch, fr.world_writes, n)
        writes = {"w"} if fr.world_writes else set()
        p2, v = self.apply_call(fname, writes, [V("w", ATOM)], vals, outs, fr.ret, n, {"w": self.write_w})
        return pre + before + p2 + after, v

    def memset_zero(self, n, args):
        """`memset(&x, 0, sizeof(x))`: x becomes the all-zero value of its type."""
        a0, a1, a2 = [strip_parens(a) for a in args]
        while a0.get("kind") == "ImplicitCastExpr" or (REACHABLE[0] and a0.get("kind") == "CStyleCastExpr"):
            a0 = strip_parens(kids(a0)[0])      # (--reachable: also `memset((void*)this, ...)`, Matrix3::zero)
        if a0.get("kind") == "CXXThisExpr" and self.ctx is not None and self.const_int(a1) == 0 and \
                a2.get("kind") == "UnaryExprOrTypeTraitExpr" and a2.get("name") == "sizeof" and kids(a2) and \
                strip_parens(kids(a2)[0]).get("kind") == "UnaryOperator" and strip_object(kids(strip_parens(kids(a2)[0]))[0]).get("kind") == "CXXThisExpr":
            # `memset(this, 0, sizeof(*this))` (Location::zero): every data member of the object zero
            t = CType("record", info=self.ctx.rec)
            p = Path(("s",), "s", [], t)
            return [self.write_path(p, all_zero(t, n), n)], None
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

    def pure_expr(self, e, depth=0):
        """--reachable: has e no effect (no assignment, increment, allocation, call of a non-const member
        function or of a function other than a C math function)? The arguments of a dropped call."""
        for m in walk(e):
            k = m.get("kind")
            if k in ("CompoundAssignOperator", "CXXNewExpr", "CXXDeleteExpr") or (k == "BinaryOperator" and m.get("opcode") == "=") or \
                    (k == "UnaryOperator" and m.get("opcode") in ("++", "--")):
                return False
            if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr"):
                c = strip_parens(kids(m)[0])
                while c.get("kind") == "ImplicitCastExpr":
                    c = strip_parens(kids(c)[0])
                d = self.u.decl((c.get("referencedDecl") or {}).get("id") or c.get("referencedMemberDecl"))
                if d is None:
                    return False
                if d.get("kind") == "CXXMethodDecl" and d["type"]["qualType"].rstrip().endswith("const"):
                    continue
                if d.get("kind") == "FunctionDecl" and (d.get("name") in {k[0] for k in CMATH} or d.get("name") in LIBM or d.get("name").rstrip("fF") in LIBM or d.get("name") in ("fabs", "fabsf", "fabsF", "sqrtF")):
                    continue
                if d.get("kind") == "FunctionDecl" and self.pure_function(d, depth):
                    continue        # `degrees(x)`, `default_as_float(v)`: `return <pure expression>;` of its parameters
                if AHRS_EXT[0] and d.get("kind") == "FunctionDecl" and d.get("name") in ("degrees", "radians") and self.u.is_lib(d):
                    continue    # --ahrs-ext: AP_Math's unit conversions (DCM's GCS text, AP_AHRS_DCM.cpp:368)
                return False
        return True

    def pure_function(self, d, depth):
        """--reachable: a free function (or a function template's instantiation) whose body is `return e;` with
        e without effects and whose parameters are values or const references: a call of it has no effect."""
        if depth > 8:
            return False
        defn = self.u.body_of(d) or d
        for x in kids(defn):
            q = x.get("type", {}).get("qualType", "") if x.get("kind") == "ParmVarDecl" else ""
            if "*" in q or ("&" in q and not q.startswith("const ")):
                return False
        body = next((x for x in kids(defn) if x.get("kind") == "CompoundStmt"), None)
        if body is None or len(kids(body)) != 1 or kids(body)[0].get("kind") != "ReturnStmt" or not kids(kids(body)[0]):
            return False
        return self.pure_expr(kids(kids(body)[0])[0], depth + 1)

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
        table = getattr(owner, "var_info_by", {}).get(vd["id"]) or getattr(owner, "var_info_by", {}).get(vd.get("previousDecl")) or owner.var_info
        if PARAM_EXT[0]:
            return self.param_ext_defaults(n, owner, table)
        lines = []
        for entry in kids(kids(table)[0]):
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
            if REACHABLE[0] and any(x.get("kind") == "ArraySubscriptExpr" for x in walk(offset)):
                # `_source_set[0].posxy` (AP_NavEKF_Source.cpp, AP_GROUPINFO into an array of structs): parameters
                # this stage does not hold (AP_Param in arrays of structs; read only through --boundary-call members)
                continue        # (no statement: a run of `pure ()` lines makes Lean's `do` elaboration exponential)
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
                elif AHRS_EXT[0] and f.t.kind == "record":
                    # --ahrs-ext: an AP_Vector3f parameter: AP_Param::set_value sets each component to the default
                    c = conv(v0, ctype_of(e), FLOAT, entry)
                    v = V("({ x := %s, y := %s, z := %s } : %s)" % (c.text, c.text, c.text, f.t.lean), ATOM)
                else:
                    v = conv(v0, ctype_of(e), f.t, entry)
            else:
                raise Reject(entry, "var_info entry with `%s`" % uf)
            if f.t.kind == "enum":
                pass            # an AP_Enum default is converted to its enum by conv above (through the stored integer)
            lines.append(self.write_path(Path(("p",), "p", steps + [("f", f.lean)], f.t), v, entry))
        return lines

    def param_storage_call(self, n, obj, mname, args):
        """--param-ext: the calls on a parameter object that ask AP_Param's storage, which is outside the
        model: `p.configured()` (stored or in a defaults file) and `p.load()` (true if stored; the value is
        assumed to be the stored one already, as AP_Param::load_all made it at boot) are a boundary input of
        the calling object, one per parameter and call site's text; `p.set_default(v)` (AP_ParamT.cpp:45: set
        unless configured; its registration of the default is the defaults file's) sets `_value` unless
        that input says it is configured."""
        r = self.resolve_path(obj)
        if r is None or r[1].t is None or r[1].t.kind != "record":
            raise Reject(n, "`%s` of a parameter that is not a member or element" % mname)
        pre, p = r
        text = re.sub(r"\s+", "", self.u.text_of(strip_object(obj)) or "param")
        key = re.sub(r"\W+", "_", text).strip("_")
        fld = self.ctx.input_field("AP_Param", "%s.%s" % (key, "loaded" if mname == "load" else "configured"), True, [], BOOL,
                                   "%s.%s()" % (text, "load" if mname == "load" else "configured"), n)
        self.reads.add("inp")
        if mname in ("load", "configured"):
            return pre, V("inp.%s" % fld, ATOM)
        vf = next((g for rr in p.t.info.chain() for g in rr.fields if g.name == "_value"), None)
        if vf is None or len(args) != 1:
            raise Reject(n, "`set_default` of something other than a parameter")
        self.u.ensure_fields(p.t.info)
        pa, v = self.expr(args[0])
        v = conv(v, ctype_of(args[0]), vf.t, n)
        return pre + pa + ["if !inp.%s then  -- C++ `%s.set_default(...)`: set unless configured in storage (an input)" % (fld, comment_safe(text)),
                           "  " + self.write_path(p.extend(("f", vf.lean), vf.t), v, n)], None

    def param_default_by_name(self, n, args):
        """--param-ext: `AP_Param::set_default_by_name("COMPASS_SCALE", 1)` (AP_Param.cpp:2798: the parameter
        found by its name, then its `set_default`, AP_ParamT.cpp:45: set unless configured in storage) with
        the name's object given by --param-name NAME=object.member[k]...: its `_value` set to the value
        converted to the parameter's type. Storage is outside the model: no parameter is configured in it."""
        lit = next((m for m in walk(args[0]) if m.get("kind") == "StringLiteral"), None) if args else None
        if lit is None or len(args) != 2:
            raise Reject(n, "`AP_Param::set_default_by_name` with a name that is not a string literal")
        name = json.loads(lit["value"])
        if name not in PARAM_NAMES:
            raise Reject(n, "`AP_Param::set_default_by_name` of `%s`, a parameter without --param-name" % name)
        comps = PARAM_NAMES[name].split(".")
        if comps[0] not in self.u.world_ids.values():
            raise Reject(n, "--param-name %s: `%s` is not a World object" % (name, comps[0]))
        p = self.world_path(comps[0], n)
        for c in comps[1:]:
            m = re.match(r"^(\w+)((?:\[\d+\])*)$", c)
            if m is None or p.t is None or p.t.kind != "record":
                raise Reject(n, "--param-name %s: bad path" % name)
            f = next((g for g in p.t.info.all_fields() if g.name == m.group(1)), None)
            if f is None or f.category != "state":
                raise Reject(n, "--param-name %s: no data member `%s`" % (name, m.group(1)))
            p = p.extend(("f", f.lean), f.t)
            for k in re.findall(r"\[(\d+)\]", m.group(2)):
                if p.t.kind != "array":
                    raise Reject(n, "--param-name %s: `%s` is not an array" % (name, c))
                p = p.extend(("i", V(k, ATOM)), p.t.elem)
        vf = next((g for r in p.t.info.chain() for g in r.fields if g.name == "_value"), None) if p.t.kind == "record" else None
        if vf is None:
            raise Reject(n, "--param-name %s: not a parameter object" % name)
        self.u.ensure_fields(p.t.info)
        pre, v = self.expr(args[1])
        v = conv(v, ctype_of(args[1]), vf.t, n)
        self.reads.add("w")
        return pre + ["-- C++ `AP_Param::set_default_by_name(\"%s\", ...)`: not configured in storage (outside the model): set" % name,
                      self.write_path(p.extend(("f", vf.lean), vf.t), v, n)], V("true", ATOM)

    def param_ext_defaults(self, n, owner, table):
        """--param-ext: `AP_Param::setup_object_defaults(this, var_info)` (AP_Param.cpp:1524-1542) with the
        parameters as the objects they are (AP_ParamT, AP_ParamV: state, their `_value`): for each entry of
        a scalar type, in table order, `set_value(type, ptr, default)`, the float default converted to the
        entry's type (AP_PARAM_INT8/16/32, FLOAT: `((AP_Int8 *)ptr)->set(value)`, a float to integer
        conversion, stored in the member's `_value`); for AP_PARAM_VECTOR3F, the default in each component;
        nested groups are skipped. The member is named by the entry's offset, a path through data members
        and constant array indices (`sensors[0].ground_pressure`, `_state._priv_instance[1].offset`)."""
        lines = []
        codes = {1: INT8, 2: CType("int", 16, True), 3: CType("int", 32, True), 4: FLOAT}
        for entry in kids(kids(table)[0]):
            if entry.get("kind") != "InitListExpr" or len(kids(entry)) < 3:
                raise Reject(entry, "var_info entry")
            offset, union = kids(entry)[1], kids(entry)[2]
            uf = union.get("field", {}).get("name")
            if uf in ("group_info", "group_info_ptr"):
                continue
            member = next((m for m in walk(offset) if m.get("kind") == "MemberExpr"), None)
            if member is None:
                break                           # AP_GROUPEND
            chain = []
            # the whole member access is the operand of the entry's `sizeof(std::declval<C>().m...)` check
            # (AP_GROUPINFO_FLAGS): its outermost node may be a subscript (`compensation[0]`)
            so = next((x for x in walk(offset) if x.get("kind") == "UnaryExprOrTypeTraitExpr" and kids(x)), None)
            m = kids(so)[0] if so is not None and any(y is member for y in walk(so)) else member
            while True:
                m = strip_object(m)
                if m.get("kind") == "MemberExpr":
                    chain.append(("f", m))
                    m = kids(m)[0]
                elif m.get("kind") == "ArraySubscriptExpr":
                    k = self.const_int(kids(m)[1])
                    if k is None:
                        raise Reject(entry, "var_info entry with a variable index")
                    chain.append(("i", k))
                    b = kids(m)[0]
                    m = kids(b)[0] if b.get("castKind") == "ArrayToPointerDecay" else b
                elif m.get("kind") == "ImplicitCastExpr" and m.get("castKind") == "ArrayToPointerDecay":
                    m = kids(m)[0]
                else:
                    break
            chain.reverse()
            t, steps = CType("record", info=self.ctx.rec), []
            for kind, x in chain:
                if kind == "i":
                    if t.kind != "array" or not 0 <= x < t.n:
                        raise Reject(entry, "var_info entry with an index outside the array")
                    steps.append(("i", V(str(x), ATOM)))
                    t = t.elem
                    continue
                if t.kind != "record":
                    raise Reject(entry, "var_info entry through a member of something other than a class")
                f = t.info.field_by_id(x["referencedMemberDecl"])
                if f is None or f.category != "state":
                    raise Reject(entry, "var_info entry for `%s`, which is not a data member" % x.get("name"))
                steps.append(("f", f.lean))
                t = f.t
            if t.kind != "record":
                lit = next((m for m in walk(kids(entry)[0]) if m.get("kind") == "StringLiteral"), None)
                raise Reject(entry, "var_info entry %s for something other than a parameter object (`%s`)" % (lit and lit.get("value"), t.cname))
            pr = t.info
            code = None
            for r in pr.chain():
                mm = re.match(r"^AP_Param(?:T|TBase|V)<.*, (\d)>$", r.cxx)
                if mm:
                    code = int(mm.group(1))
                    break
            vf = next((g for r in pr.chain() for g in r.fields if g.name == "_value"), None)
            if code is None or vf is None:
                raise Reject(entry, "var_info entry for a member of class `%s`, which is not a parameter class" % pr.cxx)
            self.u.ensure_fields(pr)
            if uf != "def_value":
                raise Reject(entry, "var_info entry with `%s`" % uf)
            e = kids(union)[0]
            pre, v0 = self.expr(e)
            if pre:
                raise Reject(entry, "var_info default with side effects")
            dv = conv(v0, ctype_of(e), FLOAT, entry)        # GroupInfo::def_value is a float
            if code == 5:
                if vf.t.kind != "record":
                    raise Reject(entry, "AP_PARAM_VECTOR3F entry for a member of another type")
                tmp = self.temp()
                lines.append("let %s := %s" % (tmp, dv.text))
                v = V("({ x := %s, y := %s, z := %s } : %s)" % (tmp, tmp, tmp, vf.t.lean), ATOM)
            elif code in codes:
                st = codes[code]
                v = conv(dv, FLOAT, st, entry)
                if vf.t != st:
                    v = conv(v, st, vf.t, entry) if vf.t.kind != "enum" else conv(v, st, vf.t, entry)
            else:
                raise Reject(entry, "var_info entry of type %d" % code)
            lines.append(self.write_path(Path(("s",), "s", steps + [("f", vf.lean)], vf.t), v, entry))
        return lines

    def boundary_object_call(self, n):
        """Is n a call of a free function returning a reference to a boundary object (ArduPilot's
        singleton accessors, e.g. `AP::ahrs()`)?"""
        if n.get("kind") != "CallExpr" or kids(n)[1:]:
            return False
        name, _ = strip_tag(n["type"]["qualType"].replace("const ", "").strip())
        if REACHABLE[0] and name.endswith("*"):
            name = name[:-1].strip()        # `AP::vehicle()`: a pointer to a boundary object (`->` reads it)
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
            if WORLD_PTRS[0] and n.get("isArrow") and self.obj_type(base) is not None:
                # `frontend->sources`: a boundary member of the object a World pointer points to
                f = self.obj_type(base).info.field_by_id(n.get("referencedMemberDecl"))
                if f is not None and f.category == "boundary":
                    return "%s->%s" % (self.u.text_of(base) or "ptr", n["name"])
                return None
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


    def boundary_world_ptr(self, n):
        """--front-ends: a pointer member of a boundary object whose class the World has one object of
        (`hal.scheduler`, an `AP_HAL::Scheduler *`, is the scheduler stand-in `est_scheduler`): that
        object's tag, a constant (the HAL's drivers are fixed before the vehicle runs), else None."""
        if n.get("kind") != "MemberExpr":
            return None
        try:
            t = ctype_of(n)
        except Reject:
            return None
        if t.kind != "obj":
            return None
        targets = ptr_targets(self.u, t.info)
        if len(targets) != 1 or targets[0][0] != "w":
            return None
        return V("WPtr.%s" % targets[0][1], ATOM)

    def boundary_read(self, n, obj, member, method_args, node_args):
        if FRONT_ENDS[0] and WORLD_PTRS[0]:
            try:
                bt = ctype_of(n)
            except Reject:
                bt = None
            if os.environ.get("CPP2LEAN_DEBUG_TARGETS") and bt is not None:
                sys.stderr.write("boundary_read %s.%s: %s %s\n" % (obj, member, bt.kind, [(k, f) for k, f, _ in ptr_targets(self.u, bt.info)] if bt.kind == "obj" else ""))
            if INS_GPS[0] and bt is not None and bt.kind == "obj" and len(ptr_targets(self.u, bt.info)) == 1 and \
                    ptr_targets(self.u, bt.info)[0][0] == "w":
                # --ins-gps: a pointer the boundary returns to a class the World has one object of (the GPS port of
                # AP_SerialManager::find_serial, the port stand-in `est_uart`): that object or null, by an input flag
                # (per value of its one non-constant argument, `uart_idx`)
                tgt = ptr_targets(self.u, bt.info)[0][1]
                args0 = [kids(a)[0] if a.get("kind") == "CXXDefaultArgExpr" else a for a in node_args]
                nonconst = [(i, a) for i, a in enumerate(args0) if self.const_value(a) is None]
                if len(nonconst) > 1 or any(not ctype_of(a).is_int() for _, a in nonconst):
                    raise Reject(n, "pointer from the boundary with several non-constant arguments")
                if nonconst:
                    flag = self.indexed_read(n, obj, member + ".found", nonconst[0], [self.const_value(a) for i, a in enumerate(args0) if i != nonconst[0][0]], t=BOOL)
                else:
                    self.boundary_type_of[id(n)] = BOOL
                    flag = self.boundary_read_value(n, obj, member, method_args, node_args)
                self.wtouch.add(tgt)
                return V("(if %s then WPtr.%s else WPtr.null)" % (flag.text, tgt), ATOM)
            if bt is not None and bt.kind == "obj" and not ptr_targets(self.u, bt.info):
                # --front-ends: a pointer the boundary returns to a class without objects in the World (the
                # GPS UART of AP_SerialManager::find_serial): null in the model; the translated paths store it,
                # pass it on and compare it with null, and dereference it only where it is not null
                return V("WPtr.null /- C++ `%s.%s(...)`: a pointer to an object outside the World -/" % (comment_safe(obj), member), ATOM)
        return self.boundary_read_value(n, obj, member, method_args, node_args)

    def world_ptr_result(self, n):
        """Is the value of n a pointer to a class of which the World has one file-scope object?"""
        try:
            bt = ctype_of(n)
        except Reject:
            return False
        if bt.kind != "obj":
            return False
        tg = ptr_targets(self.u, bt.info)
        return len(tg) == 1 and tg[0][0] == "w"

    def boundary_read_value(self, n, obj, member, method_args, node_args):
        """A value read from a boundary object (a data member, or the result of a const method)
        is a field of Inputs: one per distinct read with constant arguments, else one per call
        site, which must not be inside a loop (it is executed at most once per call)."""
        if self.ctx is None:
            raise Reject(n, "boundary object used outside a member function")
        cargs = []
        site = None
        idx = self.input_index(node_args)
        if idx is not None:
            return self.indexed_read(n, obj, member, idx, self.index_consts(node_args, idx))
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
        t = self.boundary_type_of.get(id(n)) or ctype_of(n)
        if not (t.is_scalar() or t.kind == "record"):
            raise Reject(n, "boundary value of type `%s`" % t.cname)
        cxx = "%s.%s" % (obj, member) + ("(%s)" % ", ".join(str(c) for c in cargs) if method_args else "")
        if site is not None:
            cxx += " at %s" % site
        fld = self.ctx.input_field(obj, member, method_args, cargs if site is None else ("site", site), t, cxx, n)
        self.reads.add("inp")
        return V("inp.%s" % fld, ATOM)

    def input_index(self, node_args):
        """--indexed-inputs: (position, argument) of the one non-constant integer argument of a boundary
        call whose other arguments are constants, else None."""
        if not INDEXED_INPUTS[0]:
            return None
        found = None
        for i, a in enumerate(node_args):
            if a.get("kind") == "CXXDefaultArgExpr":
                a = kids(a)[0]
            if self.const_value(a) is not None:
                continue
            if found is not None or not ctype_of(a).is_int():
                return None
            found = (i, a)
        return found

    def index_consts(self, node_args, idx):
        """The constant arguments of an indexed boundary call, in order (part of its input's key and name)."""
        out = []
        for i, a in enumerate(node_args):
            if i == idx[0]:
                continue
            if a.get("kind") == "CXXDefaultArgExpr":
                a = kids(a)[0]
            out.append(self.const_value(a))
        return out

    def indexed_read(self, n, obj, member, idx, consts=(), t=None, node=None):
        """--indexed-inputs: the value a const boundary call `obj.member(..., i, ...)` returns (or writes
        into a reference parameter, member `m.p`), from the input array of that member function at index
        i: one array per member function and argument position, `#[]` until the caller sets it; an index
        beyond its end reads the zero value."""
        t = t or ctype_of(n)
        if not (t.is_scalar() or t.kind == "record"):
            raise Reject(n, "boundary value of type `%s`" % t.cname)
        at = CType("array", elem=t, n=0)
        at.indexed = True
        cxx = "%s.%s(%s) for each %s" % (obj, member.split(".")[0], "...", self.u.text_of(idx[1]) or "i")
        fld = self.ctx.input_field(obj, member, True, [("index", idx[0])] + list(consts), at, cxx, node or n)
        pre, iv = self.nat_index(idx[1])
        self.reads.add("inp")
        return V("(inp.%s.getD %s %s)" % (fld, iv.at(ATOM), zero_of(t, n).at(ATOM)), APP) if not pre else self._indexed_pre(pre, fld, iv, t, n)

    def _indexed_pre(self, pre, fld, iv, t, n):
        raise Reject(n, "index of a boundary input with effects")

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
            pt = (decl_type(p)[0] if p["type"]["qualType"].startswith("const ") and p["type"]["qualType"].rstrip().endswith("&") else ctype_of(p)) if p.get("type") else ctype_of(a)
            if not (pt.is_scalar() or pt.kind == "record"):
                raise Reject(a, "boundary output of type `%s`" % pt.cname)
            targs.append((p.get("name", "arg%d" % i), pt))
            vals[i] = conv(vals[i], ctype_of(a), pt, a)
        sig = "%s(%s)" % (mname if obj in ("this", None) else "%s.%s" % (obj, mname), ", ".join("%s %s" % (t.cname, nm) for nm, t in targs))
        name = self.u.output_ctor(obj, mname, targs, sig, n)
        self.writes.add("o")
        self.reads.add("o")
        return pre + ["o := o.push %s" % app("Output.%s" % name, *vals).at(ATOM)]

    def text_event(self, n, args):
        """--text-log (Phase 5c): `GCS::send_text(severity, fmt, ...)` (GCS_SEND_TEXT) on the boundary's GCS: an
        `Output.send_text severity fmt args` event, the severity as its number, the format the string literal, the variadic
        arguments after the default promotions clang made explicit, each tagged as the target passes it (arm64 Apple: one
        8-byte slot per argument): `.inl w` an integer sign- or zero-extended to 64 bits or a `double`'s bits, `.inr s` a
        `const char *` (a string). The vehicle's translated GCS::send_text formats them (the bridge's drain)."""
        if len(args) < 2:
            raise Reject(n, "GCS::send_text without a format")
        u64 = CType("int", bits=64, signed=False)
        u32 = CType("int", bits=32, signed=False)
        sev = None
        ref = next((m for m in walk(args[0]) if m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("kind") == "EnumConstantDecl"), None)
        if ref is not None:
            # the severity, an enumerator of MAV_SEVERITY (an enum the World does not translate): its value from the
            # enumeration's declaration, as EnumInfo computes it
            en = self.u.parent.get(ref["referencedDecl"]["id"])
            if en is not None and en.get("kind") == "EnumDecl":
                v = -1
                for c in kids(en):
                    if c.get("kind") != "EnumConstantDecl":
                        continue
                    ce = next((x for x in walk(c) if x.get("kind") == "ConstantExpr" and "value" in x), None)
                    v = int(ce["value"]) if ce is not None else v + 1
                    if c.get("id") == ref["referencedDecl"]["id"]:
                        sev = V("(%d : UInt32)" % v, ATOM)
        pre, vals = self.operands(args[1:])
        vals = [None] + vals
        args = list(args)
        if sev is None:
            p0, v0 = self.operands(args[:1])
            pre = p0 + pre
            sev = conv(v0[0], ctype_of(args[0]), u32, args[0])
        if ctype_of(args[1]).kind != "string":
            raise Reject(args[1], "GCS::send_text format that is not a string")
        if TEXT_BUFFERS[0] and any(ctype_of(a).kind == "textbuf" for a in args[2:]):
            # --text-buffers: `GCS_SEND_TEXT(sev, "%s", buffer)` (AP_GPS_Backend::broadcast_gps_type, GPS_Backend.cpp:149-154):
            # an `Output.send_text_snprintf severity fmt size ifmt iargs` event, the buffer as the snprintf that filled it
            # (size, format, arguments); the vehicle's drain formats it with the translated AP_HAL::Util::snprintf into a
            # buffer of that size and passes the buffer to the translated GCS::send_text
            if len(args) != 3:
                raise Reject(n, "GCS::send_text with a `char` buffer and other arguments (--text-buffers)")
            tr_ = self.text_ref(args[2])
            if tr_ is None or tr_[2]:
                # (Phase 5d) a `char *` parameter's text as the caller passed it is not in the translation (the bridge
                # passes `CText.none` and writes back what the call wrote): reading it is rejected
                raise Reject(args[2], "GCS::send_text of a `char *` parameter's buffer (its incoming text is the caller's, --text-buffers)")
            targs = [("severity", u32), ("fmt", STRING), ("text", TEXTBUF)]
            name = self.u.output_ctor("gcs", "send_text_snprintf", targs, "gcs().send_text(MAV_SEVERITY severity, const char *fmt, char *buffer) after hal.util->snprintf(buffer, size, ifmt, ...)", n)
            self.writes.add("o")
            self.reads.add("o")
            return pre + ["o := o.push %s" % app("Output.%s" % name, sev, vals[1], vals[2]).at(ATOM)]
        items = self.text_items(args[2:], vals[2:])
        targs = [("severity", u32), ("fmt", STRING), ("args", CType("textargs"))]
        name = self.u.output_ctor("gcs", "send_text", targs, "gcs().send_text(MAV_SEVERITY severity, const char *fmt, ...)", n)
        self.writes.add("o")
        self.reads.add("o")
        return pre + ["o := o.push %s" % app("Output.%s" % name, sev, vals[1], V("#[%s]" % ", ".join(items), ATOM)).at(ATOM)]

    def console_event(self, n, args):
        """--text-log (Phase 5c): `hal.console->printf(fmt, ...)` (DEV_PRINTF: AP_InertialSensor::_init_gyro's "Init Gyro",
        "*", "\\n") on the HAL's console: an `Output.console_printf fmt args` event (the arguments tagged as for
        GCS::send_text); the vehicle's drain passes it to the HAL's console `printf`, as the vehicle's own console texts."""
        if not args or ctype_of(args[0]).kind != "string":
            raise Reject(n, "BetterStream::printf format that is not a string")
        pre, vals = self.operands(args)
        items = self.text_items(args[1:], vals[1:])
        targs = [("fmt", STRING), ("args", CType("textargs"))]
        name = self.u.output_ctor("hal", "console_printf", targs, "hal.console->printf(const char *fmt, ...)", n)
        self.writes.add("o")
        self.reads.add("o")
        return pre + ["o := o.push %s" % app("Output.%s" % name, vals[0], V("#[%s]" % ", ".join(items), ATOM)).at(ATOM)]

    def text_items(self, args, vals):
        """--text-log: the variadic arguments of a formatted call, tagged (text_event)."""
        u64 = CType("int", bits=64, signed=False)
        items = []
        for a, v in zip(args, vals):
            t = ctype_of(a)
            if t.kind == "string":
                items.append(app("Sum.inr", v).text)
            elif t.kind == "double":
                items.append(app("Sum.inl", app("Binary64.toBits", v)).text)
            elif t.kind in ("int", "enum", "bool"):
                items.append(app("Sum.inl", conv(v, t, u64, a)).text)
            else:
                raise Reject(a, "GCS::send_text argument of type `%s`" % t.cname)
        return items

    def text_snprintf(self, n, args):
        """--text-buffers (Phase 5c): `hal.util->snprintf(buffer, size, fmt, ...)` (AP_GPS_Backend::_detection_message,
        GPS_Backend.cpp:129-146) into a local `char` buffer or a `char *` parameter, its result discarded: the buffer
        holds the call (size, format, the variadic arguments tagged as for --text-log), `CText.fmt size fmt args`, which
        the vehicle's translated AP_HAL::Util::snprintf formats where the text is used (text_event, the bridge's text
        sink). (Phase 5d) also `dal.snprintf` (AP_DAL::snprintf), into a `char` data member (NavEKF3_core::
        prearm_fail_string), and with a format that is itself a text (`dal.snprintf(failure_msg, failure_msg_len,
        failure)`, AP_NavEKF3.cpp:1202): `CText.text size src args`, the format the text of src (formatted first)."""
        if self.discard_node is not n:
            raise Reject(n, "AP_HAL::Util::snprintf whose result is used (--text-buffers)")
        if len(args) < 3:
            raise Reject(n, "AP_HAL::Util::snprintf without a format")
        sa = strip_parens(args[0])
        while sa.get("kind") == "ImplicitCastExpr" and sa.get("castKind") in ("ArrayToPointerDecay", "LValueToRValue", "NoOp"):
            sa = strip_parens(kids(sa)[0])
        if sa.get("kind") == "MemberExpr":
            r = self.lvalue(sa, n)      # (Phase 5d) a `char` data member
        else:
            r = self.resolve_path(sa) if sa.get("kind") == "DeclRefExpr" else None
        if r is None or r[1].t is None or r[1].t.kind != "textbuf" or (r[1].steps and sa.get("kind") != "MemberExpr"):
            raise Reject(args[0], "AP_HAL::Util::snprintf into something other than a local buffer, a `char *` parameter or a `char` data member (--text-buffers)")
        if ctype_of(args[2]).kind != "string":
            raise Reject(args[2], "AP_HAL::Util::snprintf format that is not a string")
        tf = self.text_ref(args[2])
        if tf is not None and tf[2]:
            raise Reject(args[2], "AP_HAL::Util::snprintf with a `char *` parameter's buffer as the format (its incoming text is the caller's, --text-buffers)")
        if tf is not None:
            pre0, src, _ = tf
            pre, vals = self.operands([args[1]] + list(args[3:]))
            vals = [vals[0], None] + vals[1:]
            pre = pre0 + pre
        else:
            pre, vals = self.operands(args[1:])
        u64 = CType("int", bits=64, signed=False)
        size = conv(vals[0], ctype_of(args[1]), u64, args[1])
        items = self.text_items(args[3:], vals[2:])
        if tf is not None:
            v = V("(CText.text %s %s #[%s])" % (size.at(ATOM), src.at(ATOM), ", ".join(items)), ATOM)
        else:
            v = V("(CText.fmt %s %s #[%s])" % (size.at(ATOM), vals[1].at(ATOM), ", ".join(items)), ATOM)
        return r[0] + pre + [self.write_path(r[1], v, n)]

    def output_fn_call(self, n, decl, name, args):
        """--output-fn (Phase 5c): a call of a free function outside the model whose effect is an output, MAVLink's
        `mavlink_msg_<m>_send(chan, ...)` / `mavlink_msg_<m>_send_struct(chan, &packet)` from an estimator class: an
        `Output.<name>` event with the arguments converted to the parameters' types; a `const T *` argument `&x` of a
        record is x's value (the callee reads the record through it). The memory translation replays the event as
        the call of the translated library function (Vehicle.json `world_outputs`)."""
        if ctype_of(n).kind != "void":
            raise Reject(n, "--output-fn `%s` with a result" % name)
        params = [p for p in kids(decl) if p.get("kind") == "ParmVarDecl"]
        uargs, uparams = [], []
        for i, a in enumerate(args):
            p = params[i] if i < len(params) else {}
            q = p.get("type", {}).get("qualType", "").replace(" ", "")
            if q.startswith("const") and q.endswith("*"):
                x = strip_parens(a)
                while x.get("kind") == "ImplicitCastExpr":
                    x = strip_parens(kids(x)[0])
                if not (x.get("kind") == "UnaryOperator" and x.get("opcode") == "&" and ctype_of(kids(x)[0]).kind == "record"):
                    raise Reject(a, "--output-fn `%s`: a pointer argument other than `&record`" % name)
                uargs.append(kids(x)[0])
                uparams.append({"name": p.get("name", "arg%d" % i)})
            else:
                uargs.append(a)
                uparams.append(p)
        return self.output_event(n, None, name, uargs, uparams)

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

    def write_w(self, v):
        self.writes.add("w")
        self.reads.add("w")
        return "w := %s" % v.text

    def object_setters(self):
        return {"s": lambda v: "s := %s" % v.text, "p": lambda v: "p := %s" % v.text, "o": lambda v: "o := %s" % v.text,
                "w": lambda v: "w := %s" % v.text}

    def this_call_args(self, res):
        """The leading p/s/inp arguments of a call of a method of the same object."""
        objargs = []
        if "p" in res.reads | res.writes:
            objargs.append(V("p", ATOM))
            self.reads.add("p")
        if "s" in res.reads | res.writes:
            objargs.append(V("s", ATOM))
            self.reads.add("s")
        if "w" in res.reads | res.writes:
            objargs.append(V("w", ATOM))
            self.reads.add("w")
            self.wtouch |= res.wtouch
        if "o" in res.writes:
            objargs.append(V("o", ATOM))
            self.reads.add("o")
        if "r" in res.reads:
            objargs.append(V("r'", ATOM))
            self.reads.add("r")
        if res.uses_inp:
            objargs.append(V("inp", ATOM))
            self.reads.add("inp")
        if res.uses_own:
            objargs.append(V("own", ATOM))
            self.reads.add("own")
        if getattr(res, "uses_self", False):
            objargs.append(V("self'", ATOM))
            self.uses_self = True
        if getattr(res, "uses_sp", False):
            objargs.append(self.cxx_path_text(Path(("s",), "s", [], None), None))     # this object's path
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
        if PARAM_SAVE_LOG[0] and mdecl is not None and qualified_name(self.u, mdecl) == "AP_Param::save":
            return self.param_save(n, obj, args)
        if PARAM_SAVE_LOG[0] and mdecl is not None and qualified_name(self.u, mdecl) == "AP_Param::notify":
            return self.param_save(n, obj, args, notify=True)
        if TEXT_LOG[0] and mdecl is not None and qualified_name(self.u, mdecl) == "GCS::send_text":
            return self.text_event(n, args), None
        if TEXT_LOG[0] and mdecl is not None and qualified_name(self.u, mdecl) in ("AP_HAL::BetterStream::printf", "BetterStream::printf"):
            return self.console_event(n, args), None
        if TEXT_BUFFERS[0] and mdecl is not None and qualified_name(self.u, mdecl) in ("AP_HAL::Util::snprintf", "Util::snprintf", "AP_DAL::snprintf"):
            # (Phase 5d) `dal.snprintf(...)` too: AP_DAL::snprintf is `hal.util->vsnprintf(str, size, format, ap)`
            # (AP_DAL.cpp:271-278), as AP_HAL::Util::snprintf (Util.cpp:18-25)
            return self.text_snprintf(n, args), None
        if mdecl is not None and qualified_name(self.u, mdecl) in DROP:
            if REACHABLE[0] and not all(self.pure_expr(a) for a in args):
                raise Reject(n, "call of `%s` (--drop) with arguments that have effects" % qualified_name(self.u, mdecl))
            return self.dropped(n, mdecl, qualified_name(self.u, mdecl))
        if REACHABLE[0] and mdecl is not None and obj.get("kind") != "CXXThisExpr" and self.u.is_boundary_call(mdecl):
            # a --boundary-call member function called on another object (`frontend->sources.getPosXYSource(i)`):
            # its result is an input of this object, as for a call on a boundary object
            return self.boundary_call(n, self.u.text_of(obj) or mname, mdecl, mname, args)
        if SEMAPHORES and (self.sem_object(obj) or (mdecl is not None and self.u.parent_record(mdecl) is not None and self.u.parent_record(mdecl).semaphore)):
            return self.sem_call(n, mname)
        if MEMBER_PTRS[0] and self.u.mtags:
            if obj.get("kind") == "CXXConstCastExpr" and kids(obj) and strip_object(kids(obj)[0]).get("kind") == "CXXThisExpr":
                obj = strip_object(kids(obj)[0])        # `const_cast<AP_AHRS*>(this)->backend_for_type(type)` (AP_AHRS.h:1098): this object
            mr = self.mtag_ref(obj) if not (callee is not None and callee.get("isArrow")) else None
            if mr is not None:
                # `be.backend.update()`, `source_backend.get_origin(o)`: the member object the tag designates
                return self.mtag_call(n, mr[0], mr[1], mr[2], mdecl, mname, args)
        if PARAM_EXT[0] and mname in ("set_default", "load", "configured") and mdecl is not None and \
                re.match(r"^AP_Param(TBase|T|V)?(<|$)", (self.u.parent_record(mdecl) or RecordInfo({"id": None}, "", "", None)).cxx):
            return self.param_storage_call(n, obj, mname, args)
        if obj.get("kind") == "DeclRefExpr" and obj["referencedDecl"]["id"] in self.param_vars:
            if (mname == "get" or mname.startswith("operator ")) and not args:
                v = self.e_DeclRefExpr(obj)[1]
                return [], self.param_conversion(v, self.vars[obj["referencedDecl"]["id"]][1], n)
            raise Reject(n, "method `%s` of a parameter-class value" % mname)
        of = self.this_field(obj) if obj.get("kind") == "MemberExpr" else None
        if of is not None and of.category == "param":
            return self.param_call(n, of, mname, args)
        if of is not None and of.category == "wpref":
            return self.param_call(n, of, mname, args, self.wpref_path(of, n))      # --ahrs-ext: the owner's parameter
        pp = self.ptr_param_path(obj) if WORLD_PTRS[0] else None
        if pp is not None:                  # `frontend->_param` converted, `frontend->_param.get()`
            pre, v = self.param_call(n, pp[2], mname, args, pp[1])
            return pp[0] + pre, v
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
        if AHRS_EXT[0] and bo is not None and mname.startswith("operator ") and not args and strip_object(obj).get("kind") == "MemberExpr" \
                and self.boundary_obj(kids(strip_object(obj))[0]) is not None:
            # --ahrs-ext: the value of a parameter member of a boundary object (`sitl->loop_time_jitter_us > 0`, AP_AHRS.cpp:663,
            # its conversion operator): an input named after the member
            om = strip_object(obj)
            return [], self.boundary_read_value(n, self.boundary_obj(kids(om)[0]), om["name"], False, [])
        if FRONT_ENDS[0] and bo is not None and callee is not None and callee.get("isArrow") and self.boundary_world_ptr(obj) is not None:
            return self.wptr_call(n, obj, ctype_of(obj), mdecl, mname, args)
        if HAL_STORAGE[0] and bo == "hal.storage":
            return self.hal_storage_call(n, mname, args)
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
        if obj.get("kind") == "CXXThisExpr" and mdecl is not None and boundary_static_name(qualified_name(self.u, mdecl)):
            # another --boundary-static member called by one (`AP_HAL::Util::snprintf` calls `vsnprintf`)
            return self.boundary_call(n, "this", mdecl, mname, args, static=True)
        if SEMAPHORES and (self.sem_object(obj) or (mdecl is not None and self.u.parent_record(mdecl) is not None and self.u.parent_record(mdecl).semaphore)):
            return self.sem_call(n, mname)
        if WORLD_PTRS[0] and mname == "operator bool" and not args and ctype_of(strip_object(obj)).kind == "wfun":
            pre, f = self.expr(obj)
            return pre, V("(%s != WFun.null)" % f.text, ATOM)
        if WORLD_PTRS[0] and callee is not None and callee.get("isArrow") and obj.get("kind") != "CXXThisExpr":
            pt = self.obj_type(obj)
            if pt is not None:
                return self.wptr_call(n, obj, pt, mdecl, mname, args)
        if INS_GPS[0] and obj.get("kind") == "ArraySubscriptExpr":
            base = kids(obj)[0]
            pt = self.obj_type(base) if not (base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay") else None
            if pt is not None and not ptr_targets(self.u, pt.info):
                # --ins-gps: `_imu._accel_calibrator[instance].get_status()` (AP_InertialSensor_Backend.cpp:548) through a
                # pointer to a class of which the World has no object: null, so not reached (as `p->m()` above)
                return self.wptr_call(n, base, pt, mdecl, mname, args)
        if mdecl is None or self.u.parent_record(mdecl) is None:
            raise Reject(n, "call of `%s`, a method of a class that is not translated" % mname)
        if obj.get("kind") == "CXXThisExpr" and RING_BUFFERS[0] and mdecl is not None and self.rb_info() is not None \
                and mdecl["id"] in self.rb_info()["acc"]:
            raise Reject(n, "element accessor `%s` of a type-erased container used other than in `memcpy`, a cast to an element pointer, or `return`" % mname)
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
        return self.path_call(n, pre0, op, mdecl, mname, args)

    def path_call(self, n, pre0, op, mdecl, mname, args):
        """A call of member function mdecl on the object at path op (a member, a local, a World
        object, a heap slot)."""
        if op.t is None or op.t.kind != "record" or op.t.info.kind != "class":
            raise Reject(n, "method call on `%s`" % (op.t.cname if op.t else "?"))
        sub = self.u.context(op.t.info, n)
        self.deps.add(("T", op.t.info.id))
        res = sub.method(sub.resolve(mdecl, virtual_dispatch=True), n)
        self.deps.add(res.bid)
        if res.noeffect:
            return pre0 + ["pure ()  -- C++ `%s`: no effect in the model" % mname], None
        member = op.root[0] == "s" and all(k == "f" for k, _ in op.steps)
        wobj = op.root == ("w",) and len(op.steps) == 1      # a method of a World object (--world)
        # --world-pointers: a method of a heap object (`w.heap'C[i]!`)
        hobj = WORLD_PTRS[0] and op.root == ("w",) and len(op.steps) == 2 and op.steps[0][1].startswith("heap'") and op.steps[1][0] == "i"
        # --reachable: a member object of a heap object (`dal.baro()`, the heap singleton's `_baro`)
        heapm = REACHABLE[0] and op.root == ("w",) and len(op.steps) > 2 and op.steps[0][1].startswith("heap'") and op.steps[1][0] == "i" \
            and all(k == "f" for k, _ in op.steps[2:])
        sync = ([], [])
        if heapm:
            if "p" in res.reads | res.writes or "r" in res.reads or res.uses_own:
                raise Reject(n, "call of `%s` on a member of a heap object, which reads parameters or references (heap objects have state only)" % mname)
            self.wtouch |= res.wtouch | {op.steps[0][1]}
            sync = self.sync_self(res.wtouch | {op.steps[0][1]}, "w" in res.writes or "s" in res.writes, n)
        if hobj:
            if "p" in res.reads | res.writes or (res.uses_inp and not (REACHABLE[0] or FRONT_ENDS[0])) or ("o" in res.writes and not OUTPUT_LOG[0] and not REACHABLE[0]) or "r" in res.reads or res.uses_own:
                raise Reject(n, "call of `%s` on a heap object, which reads parameters, the boundary or references (heap objects have state only)" % mname)
            self.wtouch |= res.wtouch | {op.steps[0][1]}
            sync = self.sync_self(res.wtouch | {op.steps[0][1]}, "w" in res.writes or "s" in res.writes, n)
        if wobj:
            me = self.u.world_self.get(self.ctx.rec.id) if self.ctx is not None else None
            if me is not None and (me == op.steps[0][1] or me in res.wtouch):
                if not WORLD_PTRS[0]:
                    raise Reject(n, "call of `%s` that reaches `%s` (this object) through the World: the caller's state is not stored there during its own call" % (mname, me))
                # --world-pointers: the self-reach cycle; this object's state goes into the World for the call
                sync = self.sync_self(res.wtouch | {op.steps[0][1]}, "w" in res.writes or "s" in res.writes or "p" in res.writes, n)
            elif WORLD_PTRS[0]:
                sync = self.sync_self(res.wtouch, "w" in res.writes, n)
            self.wtouch |= res.wtouch
        elif WORLD_PTRS[0] and not hobj and "w" in res.reads | res.writes:
            sync = self.sync_self(res.wtouch, "w" in res.writes, n)
            if MEMBER_REACH[0]:
                # --member-reach (Phase 5c): a call on a member object (`ekf3.resetHeightDatum()` in AP_AHRS, through the
                # member-pointer dispatch) reaches the World objects its callee reaches, so the caller's callers see
                # them in their self-reach cycle (AP_Baro::update_field_elevation's `AP::ahrs().resetHeightDatum()`
                # reaches AP_Baro::update_calibration through NavEKF3 and AP_DAL: the barometer's state goes into the
                # World before the call and is reloaded after it)
                self.wtouch |= res.wtouch
        objargs = []
        ppath = Path(("w",), "w", [("f", op.steps[0][1] + "'p")], None) if wobj else Path(("p",), "p", op.steps, None)
        # --world-pointers: a member object of a World object (`frontend->sources`): its parameters are in
        # the World object's Params
        wmember = WORLD_PTRS[0] and op.root == ("w",) and len(op.steps) > 1 and all(k == "f" for k, _ in op.steps) and \
            any(x["name"] == op.steps[0][1] and not x.get("static") for x in self.u.world)
        if wmember:
            ppath = Path(("w",), "w", [("f", op.steps[0][1] + "'p")] + list(op.steps[1:]), None)
        if "p" in res.reads | res.writes:
            if not (member or wobj or wmember):
                raise Reject(n, "method of a local object of class `%s`, which has parameters" % op.t.cname)
            objargs.append(self.read_path(ppath, n))
        s_arg = None
        if "s" in res.reads | res.writes:
            s_arg = len(objargs)
            objargs.append(self.read_path(op, n))
        if "w" in res.reads | res.writes:
            objargs.append(V("w", ATOM))
            self.reads.add("w")
        opath = None
        if "o" in res.writes and OUTPUT_LOG[0]:
            opath = Path(("o",), "o", [], None)     # one log for every object: the calls in order
            objargs.append(self.read_path(opath, n))
        elif "o" in res.writes and (hobj or heapm):
            # --reachable: the boundary outputs of the heap objects of a class (one record, `w.heap'C'o`)
            opath = Path(("w",), "w", [("f", op.steps[0][1] + "'o")] + [("f", x) for x in self.heap_sub_parts(op, sub, "o")], None)
            objargs.append(self.read_path(opath, n))
            self.u.heap_out.add(op.steps[0][1])
        elif "o" in res.writes and wobj:
            opath = Path(("w",), "w", [("f", op.steps[0][1] + "'o")], None)
            objargs.append(self.read_path(opath, n))
        elif "o" in res.writes:
            if not member or len(op.steps) != 1:
                raise Reject(n, "method of an object of class `%s` that is not a direct member, and writes boundary outputs" % op.t.cname)
            fld = self.ctx.sub_output(op.steps[0][1], sub)
            opath = Path(("o",), "o", [("f", fld)], None)
            objargs.append(self.read_path(opath, n))
        if wobj and ("r" in res.reads or res.uses_own):
            raise Reject(n, "method of World object `%s` that reads `const` reference members or a back-reference" % op.steps[0][1])
        if wobj and res.uses_inp:
            objargs.append(V("w.%s'inp" % op.steps[0][1], ATOM))
            self.reads.add("w")
        if (hobj or heapm) and res.uses_inp:
            # --reachable: the boundary inputs of the heap objects of a class (one record for all of them,
            # `w.heap'C'inp`, set by the caller; AP_DAL is a singleton)
            objargs.append(V(".".join(["w.%s'inp" % op.steps[0][1]] + self.heap_sub_parts(op, sub, "inp")), ATOM))
            self.reads.add("w")
            self.u.heap_inp.add(op.steps[0][1])
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
        if res.uses_inp and wmember and FRONT_ENDS[0] and len(op.steps) == 2:
            # --front-ends: a member object of a World object (`_compass._per_motor.compensate(...)` from a back
            # end, AP_Compass_Backend.cpp:116): its inputs are those of the World object's member
            wname = op.steps[0][1]
            wrec = next(x["rec"] for x in self.u.world if x["name"] == wname)
            objargs.append(V("w.%s'inp.%s" % (wname, self.u.context(wrec, n).sub_input(op.steps[1][1], sub)), ATOM))
            self.reads.add("w")
        elif res.uses_inp and not wobj and not hobj and not heapm:
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
        if getattr(res, "uses_self", False):
            # --world-pointers: the member function uses its object's pointer (`FUNCTOR_BIND_MEMBER`)
            if hobj:
                objargs.append(V("(WPtr.%s %s)" % (op.steps[0][1], op.steps[1][1].at(ATOM)), ATOM))
            elif wobj:
                objargs.append(V("WPtr.%s" % op.steps[0][1], ATOM))
            else:
                raise Reject(n, "call of `%s`, which uses its object's pointer, on an object that is not a World or heap object" % mname)
        if getattr(res, "uses_sp", False):
            # --param-save-log: the member function saves parameters of its object; their paths start with the object's
            objargs.append(self.cxx_path_text(op, n))
        setters = {"s": lambda v: self.write_path(op, v, n), "p": lambda v: self.write_path(ppath, v, n),
                   "o": lambda v: self.write_path(opath, v, n), "w": lambda v: self.write_w(v)}
        if MEMBER_PTRS[0] and sync[1] and op.root == ("s",):
            # --member-pointers: a member object of this object whose call reaches this object through the World (`dcm`'s
            # `AP::ahrs()`): this object's state is reloaded from the callee's World right after it is stored, before
            # the member's state and the reference arguments are stored into it (else the reload would undo them)
            after = list(sync[1])
            setters["w"] = lambda v: "\n".join([self.write_w(v)] + after)
            sync = (sync[0], [])
        pre, vals, outs = self.call_args(res.cparams, args, n)
        swap = self.swap_out(op, hobj, wobj, res, objargs, s_arg, vals, n)
        p2, v = self.apply_call("%s.%s" % (op.t.info.lean, res.lean), res.writes, objargs, vals, outs, res.ret, n, setters)
        return pre0 + pre + sync[0] + swap + p2 + sync[1], v

    def swap_out(self, op, hobj, wobj, res, objargs, s_arg, vals, n):
        """--swap-out (README.md, "Phase 3: AP_AHRS, and speed"): for a call that writes the state of a World
        object (`w.EKF3`) or of a heap object (`w.heap'C[i]!`), the lines that take the state out of the World
        before the call (its place holds `default` meanwhile), so that the callee holds the only reference to it
        and its arrays are updated in place (passed while still in the World, the state is shared and each of
        its arrays is copied on its first write); the call's result is stored back as before. Sound because the
        callee's World is read at that place only after the self-reach cycle has stored the callee's state there
        (Body.sync_self). objargs[s_arg] becomes the state taken out. Not when another argument reads the place."""
        if not SWAP_OUT[0] or s_arg is None or "s" not in res.writes or not (hobj or wobj):
            return []
        fld = op.steps[0][1]
        pat = re.compile(r"\bw\.%s(\[|(?![\w']))" % re.escape(fld))
        if any(pat.search(x.text) for i, x in enumerate(objargs) if i != s_arg) or any(pat.search(x.text) for x in vals):
            return []
        t = self.temp()
        self.reads.add("w")
        self.writes.add("w")
        objargs[s_arg] = V(t, ATOM)
        if hobj:
            idx = op.steps[1][1]
            return ["let %s := w.%s[%s]!  -- the object out of its slot for the call (--swap-out)" % (t, fld, idx.text),
                    "w := { w with %s := w.%s.set! %s default }" % (fld, fld, idx.at(ATOM))]
        return ["let %s := w.%s  -- the object out of the World for the call (--swap-out)" % (t, fld),
                "w := { w with %s := default }" % fld]

    def heap_sub_parts(self, op, sub, kind):
        """--reachable: for a member object of a heap object (Path `w.heap'C[i].m1.m2`), the fields of
        its Inputs (kind "inp") or Outputs ("o") record inside the heap class's record (`m1.m2`)."""
        parts = []
        hrec = next(h for h in self.u.heap if heap_field(h) == op.steps[0][1])
        cur = self.u.context(hrec, hrec.node)
        t = CType("record", info=hrec)
        for _, fl in op.steps[2:]:
            f = next(x for x in t.info.all_fields() if x.lean == fl)
            t = f.t
            nxt = self.u.context(t.info, t.info.node) if t is not op.t else sub
            parts.append(cur.sub_input(fl, nxt) if kind == "inp" else cur.sub_output(fl, nxt))
            cur = nxt
        return parts

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
        if res.noeffect or "p" in res.reads | res.writes or res.uses_inp or "r" in res.reads or "o" in res.writes or getattr(res, "uses_sp", False):
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
        if mdecl is not None and boundary_static_name(qualified_name(self.u, mdecl)):
            # `ahrs.calc_trig(rot, ...)` (AP_AHRS_View.cpp:80): a member function of the boundary class
            # that reads nothing of its object, translated as a function of its arguments
            fr = self.u.boundary_static_result(mdecl, n)
            self.deps.add(fr.key)
            pre, vals, outs = self.call_args(fr.cparams, args, n)
            p2, v = self.apply_call(self.qual(self.u.ns, fr.lean), set(), [], vals, outs, fr.ret, n, {})
            return pre + p2, v
        if self.ctx is None:
            raise Reject(n, "boundary object used outside a member function")
        params = [p for p in kids(mdecl) if p.get("kind") == "ParmVarDecl"] if mdecl else []
        refs = []
        for p in params:
            q = p["type"]["qualType"].rstrip()
            refs.append(q.endswith("&") and not q.endswith("&&") and not q.startswith("const "))
        is_const = mdecl is not None and (mdecl["type"]["qualType"].rstrip().endswith("const") or qualified_name(self.u, mdecl) in BOUNDARY_QUERY or (REACHABLE[0] and boundary_query_match(self.u, mdecl, obj)))
        if static and (self.boundary_type_of.get(id(n)) or ctype_of(n)).kind != "void" and self.discard_node is not n:
            is_const = True                 # a query of the environment
        count = []
        if AHRS_EXT[0] and mdecl is not None and not is_const and not OUTPUT_LOG[0] and not any(refs) and \
                (self.boundary_type_of.get(id(n)) or ctype_of(n)).kind != "void" and self.discard_node is not n:
            # --ahrs-ext: a non-const call whose result is used (`compass.read()`, AP_AHRS_DCM.cpp:678;
            # `AP::baro().get_climb_rate()`, :1487): its result an input, its calls counted (an output)
            t = CType("int", bits=32, signed=False)
            fld = self.ctx.output_field(obj, mname, "calls", t, "number of calls of `%s.%s()`" % (obj, mname), n)
            p_ = Path(("o",), "o", [("f", fld)], t)
            count = [self.write_path(p_, V("%s + 1" % self.read_path(p_, n).at(ATOM), APP), n)]
            is_const = True
        if mdecl is not None and not is_const:
            if OUTPUT_LOG[0]:
                if ((self.boundary_type_of.get(id(n)) or ctype_of(n)).kind != "void" and self.discard_node is not n) or any(refs):
                    raise Reject(n, "call of non-const `%s` on a boundary object whose result is used or with reference parameters (outputs are calls whose result is discarded)" % mname)
                return self.output_event(n, obj, mname, args, params), None
            if (self.boundary_type_of.get(id(n)) or ctype_of(n)).kind != "void" or any(refs):
                raise Reject(n, "call of non-const method `%s` on a boundary object with a result or reference parameters (only `void` outputs are translated)" % mname)
            if not args and REACHABLE[0]:
                # `AP::baro().update_calibration()`: the number of calls (a call without arguments writes nothing else)
                t = CType("int", bits=32, signed=False)
                fld = self.ctx.output_field(obj, mname, "calls", t, "number of calls of `%s.%s()`" % (obj, mname), n)
                p_ = Path(("o",), "o", [("f", fld)], t)
                return [self.write_path(p_, V("%s + 1" % self.read_path(p_, n).at(ATOM), APP), n)], None
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
        pre = []
        consts = []
        nonref = [a for i, a in enumerate(args) if not (i < len(refs) and refs[i])]
        idx = self.input_index(nonref)
        if idx is not None and EST_WORLD[0] and self.world_ptr_result(n):
            idx = None      # --est-world: `find_serial(GPS, uart_idx)` returns the port stand-in or null (boundary_read, --ins-gps)
        if idx is not None:
            consts = self.index_consts(nonref, idx)
            # --indexed-inputs: `ins.get_delta_velocity(i, dv, dt)`: the result and the values written into the
            # reference parameters, each from its input array at i
            for i, a in enumerate(args):
                if i < len(refs) and refs[i]:
                    r = self.resolve_path(a)
                    if r is None:
                        raise Reject(a, "argument for a reference parameter of a boundary call that is not a variable, member or element")
                    pre_a, path = r
                    pname = params[i].get("name", "arg%d" % i)
                    v = self.indexed_read(a, obj, mname + "." + pname, idx, consts, path.t, a)
                    pre += pre_a + [self.write_path(path, v, a)]
            if (self.boundary_type_of.get(id(n)) or ctype_of(n)).kind == "void":
                return pre, None
            return pre, self.indexed_read(n, obj, mname, idx, consts)
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
        if (self.boundary_type_of.get(id(n)) or ctype_of(n)).kind == "void":
            if not pre:
                raise Reject(n, "const `void` call on a boundary object without reference parameters (no effect)")
            return pre, None
        v = self.boundary_read(n, obj, mname, True, consts)
        return count + pre, v

    def param_conversion(self, v, pt, n):
        """A parameter's value v (of its scalar type pt) as the result of the conversion n:
        `explicit operator double ()` and `operator int ()` of AP_Float (AP_Param.h:1010-1016)
        convert it; `get()` and `operator const float &()` do not."""
        rt = ctype_of(n)
        if rt.is_scalar() and pt is not None and pt.is_scalar() and rt != pt:
            return conv(v, pt, rt, n)
        return v

    def ptr_param_path(self, obj):
        """--world-pointers: for `frontend->_gpsHorizVelNoise` (a parameter member of the object a
        pointer points to, one possible object): (pre, Path of the parameter in that object's Params,
        FieldInfo), else None."""
        if obj.get("kind") != "MemberExpr" or not obj.get("isArrow") or strip_object(kids(obj)[0]).get("kind") == "CXXThisExpr":
            return None
        pt = self.obj_type(kids(obj)[0])
        if pt is None:
            return None
        f = pt.info.field_by_id(obj.get("referencedMemberDecl"))
        if f is None or f.category != "param":
            return None
        pre, path = self.resolve_path(obj)
        return pre, path, f

    def param_value(self, n):
        """The value of an expression of a parameter class (a parameter member, a parameter passed
        by value, `c ? p1 : p2` of two of them), or None."""
        n = strip_object(n)
        if n.get("kind") == "MemberExpr":
            f = self.this_field(n)
            if f is not None and f.category == "param":
                return [], self.read_path(Path(("p",), "p", [("f", f.lean)], f.t), n)
            pp = self.ptr_param_path(n) if WORLD_PTRS[0] else None
            if pp is not None:
                return pp[0], self.read_path(pp[1], n)     # `frontend->_param`
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
            if r is None or r[0] or r[1].root[0] not in ("s", "w") or not all(k == "f" for k, _ in r[1].steps) or \
                    r[1].t is None or r[1].t.kind != "record" or r[1].t.info.kind != "class":
                return None
            ctx, steps = self.u.context(r[1].t.info, obj), list(r[1].steps)
            if r[1].root == ("w",):
                # a parameter of (a member object of) a World object: in its Params field
                steps = [("f", steps[0][1] + "'p")] + steps[1:]
                target = ctx.resolve(decl, virtual_dispatch=True)
                f = self.returned_param(ctx, target)
                return None if f is None else ([], Path(("w",), "w", steps + [("f", f.lean)], f.t), f)
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

    def returned_param(self, ctx, target):
        """The parameter member `f` of a member function whose body is `return f;`, else None."""
        body = self.u.body_of(target)
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None) if body else None
        if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
            return None
        e = strip_object(kids(kids(cs)[0])[0])
        if e.get("kind") != "MemberExpr" or strip_object(kids(e)[0]).get("kind") != "CXXThisExpr":
            return None
        f = ctx.rec.field_by_id(e.get("referencedMemberDecl"))
        return f if f is not None and f.category == "param" else None

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
        if n.get("kind") != "CXXMemberCallExpr" or self.ctx is None or (kids(n)[1:] and not (REACHABLE[0] and len(kids(n)) == 2)):
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
            heap_ok = REACHABLE[0] and r is not None and all(k in ("f", "i", "av") for k, _ in r[1].steps)     # through elements and views
            if r is None or r[1].root[0] not in (("s", "var", "w") if self.var_views else ("s", "w")) or not (heap_ok or all(k == "f" for k, _ in r[1].steps)) or \
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
        if kids(n)[1:]:
            # --reachable: `location(i)` whose body is `return tmp_location[instance];` (AP_DAL_GPS.h:19): that
            # element, its index evaluated once (a reference bound to it keeps it)
            ps = [p for p in kids(body) if p.get("kind") == "ParmVarDecl"]
            if e.get("kind") != "ArraySubscriptExpr" or len(ps) != 1:
                return None
            arr, ix = kids(e)
            ixs = strip_object(ix)
            while ixs.get("kind") == "ImplicitCastExpr":
                ixs = strip_object(kids(ixs)[0])
            arr = strip_object(arr)
            while arr.get("kind") == "ImplicitCastExpr":
                arr = strip_object(kids(arr)[0])
            if ixs.get("kind") != "DeclRefExpr" or ixs["referencedDecl"]["id"] != ps[0]["id"] or arr.get("kind") != "MemberExpr" or \
                    strip_object(kids(arr)[0]).get("kind") != "CXXThisExpr":
                return None
            f = ctx.rec.field_by_id(arr.get("referencedMemberDecl"))
            if f is None or f.category != "state" or f.t.kind != "array":
                return None
            a = kids(n)[1]
            pt = ctype_of(ps[0])
            pre_a, av = self.expr(a)
            av = conv(av, ctype_of(a), pt, a)
            ti = self.temp()
            pre = pre + pre_a + ["let %s := %s" % (ti, app("%s.toNat" % pt.lean, av).text if not pt.signed else app("%s.toNatClampNeg" % pt.lean, av).text)]
            base_p = root if root is not None else Path(("s",), "s", [], CType("record", info=ctx.rec))
            return pre, base_p.extend(("f", f.lean), f.t).extend(("i", V(ti, ATOM)), f.t.elem)
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
        if f.category == "param" and root is not None and root.root == ("w",) and all(k == "f" for k, _ in root.steps):
            return pre, Path(("w",), "w", [("f", root.steps[0][1] + "'p")] + list(root.steps[1:]) + [("f", f.lean)], f.t)
        if f.category == "param" and root is not None and root.root == ("w",):
            return None
        if f.category == "param":
            if root is not None and root.root[0] != "s":
                return None         # a parameter of a local or a reference parameter: not a path of this object
            steps = list(root.steps) if root is not None else []
            return pre, Path(("p",), "p", steps + [("f", f.lean)], f.t)
        if root is None:
            return pre, Path(("s",), "s", [("f", f.lean)], f.t)
        return pre, root.extend(("f", f.lean), f.t)

    def this_cxx_path(self, n):
        """--param-save-log: the C++ path of this object as parts of a Lean string: the name of its World
        object (a class with one World object), else the implicit argument `sp` (the caller names it)."""
        if self.ctx is None:
            raise Reject(n, "parameter save outside a member function (--param-save-log)")
        me = self.u.world_self.get(self.ctx.rec.id)
        if me is not None:
            w = next(x for x in self.u.world if x["name"] == me)
            return [("lit", w.get("cxx", w["decl"]["name"]))]
        self.reads.add("sp")
        return [("expr", "sp")]

    def cxx_path_text(self, op, n):
        """--param-save-log: the C++ member path of the object at Path op from its World object, as a Lean
        `String` expression built at run time with the actual array indices (`barometer.sensors[0].ground_pressure`,
        `compass._state._priv_instance[0].dev_id`): the names of the C++ data members, not the Lean fields'.
        A local, a reference parameter, a heap object or a view cannot be named: a Reject."""
        if op.root in (("s",), ("p",)):
            parts = self.this_cxx_path(n)
            t = CType("record", info=self.ctx.rec)
            steps = list(op.steps)
        elif op.root == ("w",) and op.steps and op.steps[0][0] == "f":
            wname = op.steps[0][1]
            wname = wname[:-2] if wname.endswith("'p") else wname
            w = next((x for x in self.u.world if x["name"] == wname and not x.get("static") and x.get("rec") is not None), None)
            if w is None:
                raise Reject(n, "save of a parameter of `%s`, which is not a World object of a translated class (--param-save-log)" % wname)
            parts = [("lit", w.get("cxx", w["decl"]["name"]))]
            t = CType("record", info=w["rec"])
            steps = list(op.steps[1:])
        elif op.root[0] == "var" and self.u.decl(op.root[1]) is not None and self.u.decl(op.root[1]).get("kind") == "VarDecl" \
                and not self.u.decl(op.root[1])["type"]["qualType"].rstrip().endswith(("&", "*")) and self.fn is not None:
            # a local object of the function (`mag_state swap_state;`, Compass::_reorder_compass_params, AP_Compass.cpp:847):
            # not a parameter of the vehicle's tree (C++ queues it, and save_sync finds no var_info for it); named as
            # `<local F::v>`, never an estimator_params.json path
            d = self.u.decl(op.root[1])
            parts = [("lit", "<local %s::%s>" % (qualified_name(self.u, self.fn), d["name"]))]
            t = ctype_of(d)
            steps = list(op.steps)
        else:
            raise Reject(n, "save of a parameter that is not a member of a World object or a local object (a reference parameter or a heap object; --param-save-log)")
        for kind, x in steps:
            if kind == "f" and t is not None and t.kind == "record":
                f = next((g for g in t.info.all_fields() if g.lean == x), None)
                if f is None:
                    raise Reject(n, "save of a parameter at a path through `%s`, not a data member of `%s` (--param-save-log)" % (x, t.info.cxx))
                parts.append(("lit", "." + f.name))
                t = f.t
            elif kind == "i" and t is not None and t.kind == "array":
                parts += [("lit", "["), ("expr", "toString %s" % x.at(ATOM)), ("lit", "]")]
                t = t.elem
            else:
                raise Reject(n, "save of a parameter at a path that is not data members and array elements (--param-save-log)")
        merged = []
        for k, v in parts:
            if k == "lit" and merged and merged[-1][0] == "lit":
                merged[-1] = ("lit", merged[-1][1] + v)
            else:
                merged.append((k, v))
        text = " ++ ".join(json.dumps(v) if k == "lit" else ("(%s)" % v if " " in v else v) for k, v in merged)
        return V(text if len(merged) == 1 else "(%s)" % text, ATOM)

    def param_save(self, n, obj, args, notify=False):
        """--param-save-log: `p.save(force_save)` (AP_Param.h:426, `force_save` false by default) on a parameter
        object, also `save(force)` inside AP_ParamTBase/AP_ParamV's `set_and_save`/`set_and_save_ifchanged` (on
        this object, whose path the caller passes as `sp`): `Output.AP_Param_save path force_save` appended to `o`
        (AP_Param::save queues the parameter for the IO thread's write to storage, outside the World)."""
        if not OUTPUT_LOG[0]:
            raise Reject(n, "parameter save without --output-log")
        if notify:
            # (Phase 5b) `p.notify()` (AP_Param.cpp:1129, also inside `set_and_notify`): the parameter's value sent to the
            # GCS at once (`send_parameter`), outside the World: `Output.AP_Param_notify path`
            if args:
                raise Reject(n, "call of `AP_Param::notify` with %d arguments" % len(args))
            pre, fv = [], None
        else:
            if len(args) != 1:
                raise Reject(n, "call of `AP_Param::save` with %d arguments" % len(args))
            a = kids(args[0])[0] if args[0].get("kind") == "CXXDefaultArgExpr" else args[0]
            pre, fv = self.expr(a)
            fv = conv(fv, ctype_of(a), BOOL, a)
        if obj.get("kind") == "CXXThisExpr":
            path = self.cxx_path_text(Path(("s",), "s", [], CType("record", info=self.ctx.rec)), n) if self.ctx is not None else None
        else:
            r = self.resolve_path(obj)
            if r is None:
                raise Reject(n, "save of a parameter that is not a variable, member or element (--param-save-log)")
            pre += r[0]
            path = self.cxx_path_text(r[1], n)
        if path is None:
            raise Reject(n, "parameter save outside a member function (--param-save-log)")
        self.writes.add("o")
        self.reads.add("o")
        if notify:
            name = self.u.output_ctor(None, "AP_Param_notify", [("path", STRING)],
                                      "AP_Param::notify() on the parameter object named by path", n)
            return pre + ["o := o.push %s" % app("Output.%s" % name, path).at(ATOM)], None
        name = self.u.output_ctor(None, "AP_Param_save", [("path", STRING), ("force_save", BOOL)],
                                  "AP_Param::save(bool force_save) on the parameter object named by path", n)
        return pre + ["o := o.push %s" % app("Output.%s" % name, path, fv).at(ATOM)], None

    def param_call(self, n, f, mname, args, path=None):
        path = path or Path(("p",), "p", [("f", f.lean)], f.t)
        if (mname == "get" or mname.startswith("operator ")) and not args:
            return [], self.param_conversion(self.read_path(path, n), f.t, n)
        if (mname == "set" or (AP_PARAM[0] and mname in ("set_and_save", "set_and_save_ifchanged", "set_and_notify", "set_and_default"))
                or (AHRS_EXT[0] and mname == "set_enable")) and len(args) == 1:
            # (--ahrs-ext: `_enable.set_enable(enable)`, AP_ParamT.cpp:33: the value set; its invalidation of AP_Param's
            # parameter count cache is outside the model)
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
        if WORLD_PTRS[0] and args and ctype_of(strip_object(args[0])).kind == "wfun":
            return self.functor_op(n, name, args)
        r = self.index_view_path(n)
        if r is not None:
            pre, p = r
            return pre, self.read_path(p, n)
        if name == "operator-" and len(args) == 1:
            f = self.this_field(strip_object(args[0])) if strip_object(args[0]).get("kind") == "MemberExpr" else None
            if f is not None and f.category == "param":
                v = self.read_path(Path(("p",), "p", [("f", f.lean)], f.t), n)
                return [], V("-" + v.at(ATOM), NEG)
            pp = self.ptr_param_path(strip_object(args[0])) if WORLD_PTRS[0] else None
            if pp is not None and pp[2].t.is_float():
                return pp[0], V("-" + self.read_path(pp[1], n).at(ATOM), NEG)     # `-frontend->_accBiasLim`
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
        if name == "operator=" and len(args) == 2 and (ctype_of(n).kind == "record" or REACHABLE[0]) and \
                (decl is None or decl.get("isImplicit") or decl.get("explicitlyDefaulted") or self.u.body_of(decl) is None):
            # (--reachable: also a union's implicit copy assignment, `status = filterStatus;`, AP_NavEKF3_Outputs.cpp:586)
            a1 = strip_object(args[1])
            while MEMBER_PTRS[0] and a1.get("kind") in ("MaterializeTemporaryExpr", "CXXBindTemporaryExpr", "ExprWithCleanups") and kids(a1):
                a1 = strip_object(kids(a1)[0])
            if MEMBER_PTRS[0] and value_init_list(a1) and ctype_of(n).kind == "record":
                # --member-pointers: `*configured_estimates = {};` (AP_AHRS.cpp:587): the value-initialized object
                # (each member value-initialized: numbers zero, members of class type by their default constructors)
                pre_l, p = self.lvalue(args[0], n)
                return pre_l + [self.write_path(p, V("({} : %s)" % ctype_of(n).lean, ATOM), n)], self.read_path(p, n)
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
        if getattr(t, "bu", None) is not None:
            if not args:
                return [], lit("0", t)      # --ekf-types: a bit union default-constructed (zero: static storage; ArduPilot zero-fills)
            if len(args) == 1:
                return self.expr(args[0])   # copied
        if t.kind == "wfun":
            # a functor: empty (`Functor()`, from nullptr) or a copy of another
            if not args or self.is_null(args[0]):
                return [], V("WFun.null", ATOM)
            if len(args) == 1:
                return self.expr(args[0])
            raise Reject(n, "construction of a functor from an object and a function pointer")
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
            pp = self.ptr_param_path(a) if WORLD_PTRS[0] else None
            if pp is not None:      # `sq(frontend->_magNoise)`: the front end's parameter, copied
                return pp[0], self.read_path(pp[1], n)
        if t.kind in ("boundary", "param"):
            raise Reject(n, "construction of an object of class `%s`" % t.name)
        if len(args) == 1:
            return self.expr(args[0])
        raise Reject(n, "construction of `%s`" % t.cname)

    # -- operators ---------------------------------------------------------------------------

    def e_UnaryOperator(self, n):
        op = n["opcode"]
        c = kids(n)[0]
        if op == "&" and MEMBER_PTRS[0] and self.u.mtags:
            v = self.mtag_member(c)
            if v is not None:
                return [], v                    # `&dcm`: the member object's tag (--member-pointers)
            mr = self.mtag_ref(c)
            if mr is not None:
                return mr[0], mr[1]             # `&be.backend`, `&source_estimates`: the tag
        t = ctype_of(n)
        if MISSION[0] and op == "*" and self.sel_ref(c) is not None:
            return [], self.sel_deref(self.sel_ref(c), n)     # --mission: `*selector`
        if op in ("++", "--"):
            return self.incdec(n, want_value=True)
        if op == "*" and strip_object(c).get("kind") == "CXXThisExpr" and self.ctx is not None:
            self.reads.add("s")
            return [], V("s", ATOM)             # `*this`: the object, i.e. the state
        if op == "*" and self.ctx is not None and strip_parens(c).get("kind") in ("CStyleCastExpr", "CXXReinterpretCastExpr") \
                and strip_parens(c).get("castKind") == "BitCast" and strip_object(kids(strip_parens(c))[0]).get("kind") == "CXXThisExpr":
            return [], self.prefix_view(n, t)
        if op == "*" and RING_BUFFERS[0] and strip_object(c).get("kind") == "DeclRefExpr" and strip_object(c)["referencedDecl"]["id"] in self.rb_alias:
            return [], self.read_path(self.rb_alias[strip_object(c)["referencedDecl"]["id"]], n)
        if op == "*" and self.nullable_ref(c) is not None:
            rid = self.nullable_ref(c)
            self.read.add(rid)
            return [], V(self.vars[rid][0], ATOM)       # the pointee of a nullable out-pointer
        if op == "*" and POINTER_PARAMS[0]:
            r = self.ptr_path(n)
            if r is not None:
                return r[0], self.read_path(r[1], n)
        if op in ("&", "*"):
            raise Reject(n, "pointer operation `%s`" % op)
        if op == "!" and C_MODE[0]:
            pre, v = self.truth(c)
            return self.c_int(n, pre, V("!" + v.at(ATOM), NOT))
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
        if k is None and EKF_ARRAYS[0]:
            # --ekf-arrays: a runtime index (`ret[r]`, EKFGSF_yaw.cpp:623): the member selected by a
            # `match` on it (an index outside [0, k) is undefined in C++: the last member)
            pre_i, nat = self.nat_index(kids(n)[2])
            obj = kids(n)[1]
            step = ("fi", (nat, [f.lean for f in fields]))
            if strip_object(obj).get("kind") == "CXXThisExpr":
                return pre_i, Path(("s",), "s", [step], fields[0].t)
            r = self.resolve_path(obj)
            if r is None:
                raise Reject(n, "`operator[]` on an object that is not a variable, member or element")
            return r[0] + pre_i, r[1].extend(step, fields[0].t)
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
        if POINTER_PARAMS[0] and self.ptr_cursor(kids(n)[0]) is not None:
            return self.ptr_step(n, want_value)
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

    def singleton_ref(self, e):
        e = strip_object(e)
        while e.get("kind") == "ImplicitCastExpr":
            e = strip_object(kids(e)[0])
        return e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in self.u.singleton_ptrs and \
            e["referencedDecl"]["id"] not in self.u.heap_ptr

    def singleton_value(self, n):
        """Whether the static `_singleton` pointer is set where n reads it: in the constructor of the
        class's one World object, after its `_singleton = this`; everywhere else (World.init runs the
        constructors before anything else is called), set."""
        in_ctor = self.fn is not None and self.fn.get("kind") == "CXXConstructorDecl"
        return self.singleton_set if in_ctor else True

    def assign(self, n, want_value):
        lhs, rhs = kids(n)
        if MISSION[0] and self.sel_ref(lhs) is not None and not want_value:
            rid = self.sel_ref(lhs)     # --mission: `selector = &packet.param3;`: which member
            x = self.sel_target(rhs)
            name, _ = self.vars[rid]
            self.mark_assigned(rid)
            return ["%s := %d  -- C++ `%s = &%s`" % (name, self.sel_ptrs[rid].index(self.u.text_of(x)) + 1, comment_safe(name),
                                                  comment_safe(self.u.text_of(x)))], None
        if WORLD[0] and self.singleton_ref(lhs):
            if want_value or strip_object(rhs).get("kind") != "CXXThisExpr" or self.fn is None or self.fn.get("kind") != "CXXConstructorDecl":
                raise Reject(n, "assignment to a static singleton pointer other than `_singleton = this;` in a constructor")
            if world_object_of_class(self.u, self.u.singleton_ptrs[strip_object(lhs)["referencedDecl"]["id"]]) is None:
                raise Reject(n, "singleton pointer of a class without exactly one World object")
            self.singleton_set = True
            return ["pure ()  -- C++ `%s`: the pointer is the class's one World object (--world)" % comment_safe(self.u.text_of(n) or "_singleton = this")], None
        if POINTER_PARAMS[0] and self.ptr_cursor(lhs) is not None:
            return self.ptr_step(n, want_value)
        if RING_BUFFERS[0] and self.rb_is_buf(lhs):
            return self.rb_alloc(n, rhs, want_value)
        sl = strip_object(lhs)
        if sl.get("kind") == "MemberExpr" and self.boundary_obj(kids(sl)[0]) is not None:
            # `AP_Notify::flags.armed = arm`: a write to a boundary object
            if AHRS_EXT[0] and not OUTPUT_LOG[0] and not want_value:
                # --ahrs-ext: an output field of this object, its last value (`AP_Notify::flags.gps_fusion = ...`,
                # AP_AHRS.cpp:671; `pd.home_lat = loc.lat` into the HAL's persistent data, AP_AHRS.cpp:1781)
                obj = self.boundary_obj(kids(sl)[0])
                pre, v = self.expr(rhs)
                t = ctype_of(sl)
                if not (t.is_scalar() or t.kind == "record"):
                    raise Reject(n, "boundary output of type `%s`" % t.cname)
                fld = self.ctx.output_field(obj, sl["name"], None, t, "%s.%s = ..." % (obj, sl["name"]), n)
                return pre + [self.write_path(Path(("o",), "o", [("f", fld)], t), conv(v, ctype_of(rhs), t, rhs), n)], None
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
        if MEMBER_PTRS[0] and value_init_list(strip_object(rhs)) and ctype_of(lhs).kind == "record":
            # --member-pointers: `*configured_estimates = {};` (AP_AHRS.cpp:587): the value-initialized object
            # (each member value-initialized: numbers zero, members of class type by their default constructors)
            pre, v = [], V("({} : %s)" % ctype_of(lhs).lean, ATOM)
        else:
            pre, v = self.expr(rhs)
        pre_l, p = self.lvalue(lhs, n)
        v = self.bit1_store(lhs, v, p.t)
        pre = pre + pre_l + [self.write_path(p, v, n)]
        return pre, (self.read_path(p, n) if want_value else None)

    def bit1_store(self, lhs, v, t):
        """The value stored into lhs: modulo 2 if lhs is a one-bit unsigned bit-field (C++ converts
        the value to the field's width, [conv.integral])."""
        sl = strip_object(lhs)
        if sl.get("kind") == "MemberExpr" and sl.get("referencedMemberDecl") in SBITFIELD_WIDTH:
            # --mission: a signed bit-field of w bits stores the value's low w bits, read back sign-extended
            sh = t.bits - SBITFIELD_WIDTH[sl["referencedMemberDecl"]]
            return V("((%s <<< %d) >>> %d)" % (v.at(ATOM), sh, sh), ATOM)
        if sl.get("kind") == "MemberExpr" and sl.get("referencedMemberDecl") in BITFIELD_WIDTH:
            # --mavlink: an unsigned bit-field of w bits stores the value modulo 2^w
            return V("%s &&& %s" % (v.at(BAND), lit(str((1 << BITFIELD_WIDTH[sl["referencedMemberDecl"]]) - 1), t).at(BAND + 1)), BAND)
        if sl.get("kind") == "MemberExpr" and sl.get("referencedMemberDecl") in BIT1_FIELDS:
            return V("%s &&& %s" % (v.at(BAND), lit("1", t).at(BAND + 1)), BAND)
        return v

    def compound(self, n, want_value):
        lhs, rhs = kids(n)
        if POINTER_PARAMS[0] and self.ptr_cursor(lhs) is not None:
            return self.ptr_step(n, want_value)
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

    def c_int(self, n, pre, v):
        """C: a comparison, `&&`, `||` or `!` has type int (1 or 0); v is its truth value (Bool)."""
        t = ctype_of(n)
        if C_MODE[0] and t.is_int():
            return pre, V("if %s then %s else %s" % (v.text, lit("1", t).text, lit("0", t).text), LOW)
        return pre, v

    @staticmethod
    def builtin_name(n):
        """The name of the clang builtin n calls, else None."""
        if n.get("kind") != "CallExpr":
            return None
        c = kids(n)[0]
        if c.get("kind") == "ImplicitCastExpr" and c.get("castKind") == "BuiltinFnToFnPtr":
            return strip_parens(kids(c)[0]).get("referencedDecl", {}).get("name")
        return None

    def truth(self, n):
        """(pre, Bool V) of n used as a truth value: in C an int (or float) is true if it is nonzero
        (`if (sign)`, `x && y`); a comparison, `&&`, `||` and `!` give their truth value directly."""
        s = strip_parens(n)
        if C_MODE[0]:
            k, op = s.get("kind"), s.get("opcode")
            b = self.builtin_name(s)
            if b == "__builtin_expect":
                # `if (predict_false(c))` (libm.h): the truth value of c (the hint's long conversion dropped)
                a = strip_parens(kids(s)[1])
                while a.get("kind") == "ImplicitCastExpr" and a.get("castKind") == "IntegralCast":
                    a = strip_parens(kids(a)[0])
                return self.truth(a)
            if b in BUILTIN_PREDICATES and len(kids(s)) == 2:
                return self.builtin_predicate(s, b, kids(s)[1])
            if k == "BinaryOperator" and op in ("<", ">", "<=", ">=", "==", "!="):
                return self.e_BinaryOperator(s, as_bool=True)
            if k == "BinaryOperator" and op in ("&&", "||"):
                return self.logical(s, as_bool=True)
            if k == "UnaryOperator" and op == "!":
                pre, v = self.truth(kids(s)[0])
                return pre, V("!" + v.at(ATOM), NOT)
            t = ctype_of(s)
            if t.kind in ("int", "float", "double", "enum"):
                pre, v = self.expr(s)
                return pre, conv(v, t, BOOL, s)
        return self.expr(n)

    def e_BinaryOperator(self, n, as_prop=False, as_bool=False):
        op = n["opcode"]
        if op == "=":
            return self.assign(n, True)
        if WORLD[0] and op in ("==", "!=") and self.u.singleton_ptrs:
            a, b = kids(n)
            if (self.singleton_ref(a) and self.is_null(b)) or (self.singleton_ref(b) and self.is_null(a)):
                v = self.singleton_value(n) == (op == "!=")
                return [], V("%s /- C++ `%s` -/" % ("true" if v else "false", comment_safe(self.u.text_of(n) or op)), ATOM)
        if MISSION[0] and op in ("==", "!=") and any(self.sel_ref(x) is not None for x in kids(n)) and any(self.is_null(x) for x in kids(n)):
            rid = next(self.sel_ref(x) for x in kids(n) if self.sel_ref(x) is not None)
            self.read.add(rid)
            return [], V("(%s %s 0)" % (self.vars[rid][0], op), ATOM)     # --mission: `selector != nullptr`
        if op == ",":
            return self.comma(n)
        if op in ("&&", "||"):
            return self.logical(n, as_bool)
        if POINTER_PARAMS[0] and op in ("==", "!=", "<", ">", "<=", ">=") and self.pp_pointee(kids(n)[0]) is not None \
                and not any(self.is_null(x) for x in kids(n)):
            return self.ptr_compare(n, as_prop, as_bool)
        if C_STRINGS[0] and op == "-" and all(self.pp_pointee(x) is not None for x in kids(n)):
            # --c-strings: `p - q` for pointers into one array: the difference of their offsets (ptrdiff_t)
            ra, rb = self.ptr_ref(kids(n)[0]), self.ptr_ref(kids(n)[1])
            if ra is None or rb is None or ra[1].text() != rb[1].text():
                raise Reject(n, "difference of pointers that are not into the same array")
            x = ra[2] if ra[2] is not None else V("0", ATOM)
            y = rb[2] if rb[2] is not None else V("0", ATOM)
            t = ctype_of(n)
            return ra[0] + rb[0], V("(%s.ofNat %s - %s.ofNat %s)" % (t.lean, x.at(ATOM), t.lean, y.at(ATOM)), ATOM)
        k = self.array_size(n)
        if k is not None:
            return [], lit(str(k), ctype_of(n))
        a_n, b_n = kids(n)
        if RING_BUFFERS[0] and op in ("==", "!=") and ((self.rb_is_buf(a_n) and self.is_null(b_n)) or (self.rb_is_buf(b_n) and self.is_null(a_n))):
            g = self.read_path(self.rb_paths()[1], n).text      # --ring-buffers: `buffer == nullptr`
            return [], V(g if op == "!=" else "!" + g, ATOM if op == "!=" else NOT)
        if TEXT_RESULTS and op in ("==", "!=") and (self.is_null(a_n) or self.is_null(b_n)):
            x = strip_casts(b_n if self.is_null(a_n) else a_n, ("NoOp", "LValueToRValue"))
            if x.get("kind") == "DeclRefExpr" and x["referencedDecl"]["id"] in self.text_ptrs:
                # --text-results (Phase 5d): a text pointer local compared with the null pointer
                pre, v = self.expr(x)
                return pre, V("%s(CText.isNull %s)" % ("!" if op == "!=" else "", v.at(ATOM)), NOT if op == "!=" else ATOM)
        if MAVLINK[0] and op in ("==", "!=") and ((self.is_null(b_n) and self.opt_ref(a_n)) or (self.is_null(a_n) and self.opt_ref(b_n))):
            rid = self.opt_ref(a_n) or self.opt_ref(b_n)
            self.read.add(rid)
            return [], V("%s.%s" % (self.vars[rid][0], "isSome" if op == "!=" else "isNone"), ATOM)
        if MAVLINK[0] and op in ("==", "!=") and ((self.is_null(b_n) and self.pp_null_param(a_n)) or (self.is_null(a_n) and self.pp_null_param(b_n))):
            # --mavlink: a byte pointer parameter (the callers pass arrays, never the null pointer) compared with null
            v = op == "!="
            return [], V("%s /- C++ `%s` -/" % ("true" if v else "false", comment_safe(self.u.text_of(n) or op)), ATOM)
        if MAVLINK[0] and op in ("==", "!=") and ((self.is_null(b_n) and self.is_struct_ptr(a_n)) or (self.is_null(a_n) and self.is_struct_ptr(b_n))):
            # --mavlink: a struct pointer (never null: the callers pass objects) compared with the null pointer
            v = op == "!="
            return [], V("%s /- C++ `%s` -/" % ("true" if v else "false", comment_safe(self.u.text_of(n) or op)), ATOM)
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
            v = V("%s %s %s" % (a.at(CMP + 1), op, b.at(CMP + 1)), CMP)
            return (pre, v) if as_prop or as_bool else self.c_int(n, pre, v)
        if op in self.REL:
            if ta.kind == "enum" and (REACHABLE[0] or INS_GPS[0]):
                # `status < AP_GPS_FixType::FIX_3D`: C++ compares the underlying values
                self.deps.add(("enum", ta.info.cxx))
                a = V("%s.toInt %s" % (ta.info.lean, a.at(ATOM)), APP)
                b = V("%s.toInt %s" % (ta.info.lean, b.at(ATOM)), APP)
            elif ta.kind == "enum":
                raise Reject(n, "ordering comparison of enum values")
            prop = "%s %s %s" % (a.at(CMP + 1), self.REL[op], b.at(CMP + 1))
            if as_prop:
                return pre, V(prop, CMP)
            v = V("decide (%s)" % prop, APP)
            return (pre, v) if as_bool else self.c_int(n, pre, v)
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
            return all(self.left_out(c) for c in kids(n))
        if k == "IfStmt":
            c = kids(n)[0]
            return not self.has_kept_effects(c) and any(self.dropped_ref(m) for m in walk(c) if m.get("kind") in ("MemberExpr", "DeclRefExpr")) \
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
        if REACHABLE[0] and strip_parens(n).get("kind") == "BinaryOperator" and self.left_out(n):
            return ["pure ()  -- C++ `%s`: an assignment to what is left out (--drop)" % comment_safe(self.u.text_of(n) or "...")]
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

    def logical(self, n, as_bool=False):
        op = n["opcode"]
        a_n, b_n = kids(n)
        pre_a, a = self.truth(a_n)
        saved = self.copy_da()
        pre_b, b = self.truth(b_n)
        self.da = saved        # assignments in the right operand may not happen
        sym, p = ("&&", AND) if op == "&&" else ("||", OR)
        if not pre_b:
            v = V("%s %s %s" % (a.at(p), sym, b.at(p + 1)), p)
            return (pre_a, v) if as_bool else self.c_int(n, pre_a, v)
        t = self.temp()
        lines = pre_a + ["let mut %s := %s" % (t, a.text),
                         "if %s then" % (t if op == "&&" else "!" + t)]
        lines += ["  " + l for l in pre_b + ["%s := %s" % (t, b.text)]]
        return (lines, V(t, ATOM)) if as_bool else self.c_int(n, lines, V(t, ATOM))

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
        return self.truth(n)

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
            if MAVLINK[0] and getattr(self, "ret_opt", None) is not None:
                # --mavlink: a returned `const T *`: `none` for the null pointer, `some x` for `&x`
                e = strip_casts(kids(n)[0], ("NoOp", "LValueToRValue", "NullToPointer"))
                self.da = DIVERGE
                if self.is_null(kids(n)[0]):
                    return [self.ret_line("none")], True
                if e.get("kind") != "UnaryOperator" or e.get("opcode") != "&":
                    raise Reject(n, "returned `const T *` other than the null pointer or `&x`")
                pre, v = self.expr(kids(e)[0])
                return pre + [self.ret_line("some %s" % v.at(ATOM))], True
            if getattr(self, "ret_text", False):
                # --text-results (Phase 5d): a returned `const char *` text: `CText.null` for the null pointer, else a
                # `char` buffer that is a text (a data member decayed to a pointer): its text
                self.da = DIVERGE
                if self.is_null(kids(n)[0]):
                    return [self.ret_line("CText.null")], True
                e = strip_casts(kids(n)[0], ("NoOp", "LValueToRValue", "ArrayToPointerDecay"))
                if ctype_of(e).kind != "textbuf":
                    raise Reject(n, "returned `const char *` other than the null pointer or a text buffer (--text-results)")
                pre, v = self.expr(e)
                return pre + [self.ret_line(v.text)], True
            if getattr(self, "ret_ptr", None) is not None:
                # --c-strings: a returned pointer parameter: its offset (pp_ret_param)
                r = self.ptr_ref(kids(n)[0])
                self.da = DIVERGE
                return r[0] + [self.ret_line(r[2].text if r[2] is not None else "0")], True
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
        if k == "CXXForRangeStmt" and (FRONT_ENDS[0] or MEMBER_PTRS[0]):
            return self.range_for(n)        # (--member-pointers: `for (auto &backend_and_estimates : backends_and_estimates)`)
        if k in ("WhileStmt", "DoStmt") and C_MODE[0]:
            return self.block([n])          # a loop as the body of an `if` (musl: `if (c) FORCE_EVAL(x);`)
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
        if k == "GotoStmt" and C_MODE[0]:
            return self.goto_stmt(n)
        if k == "LabelStmt" and C_MODE[0]:
            return self.block([n])
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
        if k in ("RecordDecl", "CXXRecordDecl") and d.get("tagUsed") == "union" and (C_MODE[0] or BYTE_OBJECTS[0]):
            # (C, and C++ with --byte-objects: a union of numbers of one width is their bit pattern)
            self.local_union = union_info(d, d)       # for the variables of this declaration
            return []
        if k != "VarDecl":
            if k in ("TypedefDecl", "TypeAliasDecl", "UsingDecl", "UsingDirectiveDecl", "StaticAssertDecl"):
                return []
            raise Reject(d, "local declaration `%s`" % k)
        if FRONT_ENDS[0] and d["type"]["qualType"].rstrip().endswith("&") and kids(d) and \
                kids(d)[0].get("kind") == "InitListExpr" and len(kids(kids(d)[0])) == 1:
            d = dict(d, inner=[kids(kids(d)[0])[0]])    # `const Vector3f &f { get_field() };`: as `= get_field()`
        if d["type"]["qualType"].startswith("union ") and getattr(self, "local_union", None) is not None:
            return self.union_decl(d)
        if MAVLINK[0] and d.get("storageClass") == "static" and self.fn is not None and "name" in d and kids(d) and \
                (d["type"]["qualType"].startswith("const ") or d.get("constexpr")):
            # --mavlink: `static const mavlink_msg_entry_t mavlink_message_crcs[] = MAVLINK_MESSAGE_CRCS;` (a constant
            # table of a function, mavlink_helpers.h:585): a constant of the file, named after the function
            if d["id"] not in self.u.consts:
                self.u.consts[d["id"]] = {"lean": "%s'%s" % (self.u.fn_names.get(self.fn["id"], lean_ident(self.fn["name"], self.fn)), d["name"]),
                                          "ns": self.u.ns, "t": ctype_of(d), "decl": d}
            self.u.const_item(d["id"])
            self.deps.add(d["id"])
            return []
        if d.get("storageClass") == "static" and self.fn is not None and "name" in d:
            qn = "%s::%s" % (qualified_name(self.u, self.fn), d["name"])
            if qn in DROP:
                # a static local left out of the model (--drop `Function::name`: SCurve::calculate_path's
                # logging latch `logged_scve`); a statement that reads it must be left out too
                if kids(d) and self.has_effects(kids(d)[0]):
                    raise Reject(d, "static local `%s` (--drop) whose initializer has effects" % d["name"])
                self.u.dropped[d["id"]] = qn
                return ["pure ()  -- C++ `%s`: left out (--drop)" % comment_safe(self.u.text_of(d) or d["name"])]
        if TEXT_RESULTS and kids(d) and "name" in d and re.match(r"^const char ?\*$", d["type"]["qualType"].strip()) and \
                self.text_result_call(kids(d)[0]):
            # --text-results (Phase 5d): `const char *failure = core[i].prearm_failure_reason();` (AP_NavEKF3.cpp:1200): a
            # `CText` (`CText.null` for the null pointer), never reassigned
            if any(m.get("kind") in ("BinaryOperator", "CompoundAssignOperator", "UnaryOperator") and
                   m.get("opcode") in ("=", "++", "--", "+=", "-=") and strip_casts(kids(m)[0]).get("kind") == "DeclRefExpr" and
                   strip_casts(kids(m)[0])["referencedDecl"]["id"] == d["id"] for m in walk(self.u.body_of(self.fn) or self.fn or {})):
                raise Reject(d, "text pointer `%s` that is reassigned (--text-results)" % d["name"])
            pre, v = self.expr(strip_casts(kids(d)[0], ("NoOp", "LValueToRValue")))
            name = self.ident(d["name"], d)
            self.vars[d["id"]] = (name, TEXTBUF)
            self.declared.append((d["id"], name))
            self.text_ptrs.add(d["id"])
            return pre + ["let %s : CText := %s" % (name, v.at(ATOM))]
        if AHRS_EXT[0] and kids(d) and d["type"]["qualType"].rstrip().endswith(("&", "*")) and not d["type"]["qualType"].rstrip().endswith("&&"):
            ini = strip_object(kids(d)[0])
            while ini.get("kind") in ("ImplicitCastExpr", "ExprWithCleanups") and kids(ini):
                ini = strip_object(kids(ini)[0])
            bo = self.boundary_obj(ini)
            if bo is not None and (d["type"]["qualType"].rstrip().endswith("&") or self.boundary_object_call(ini)):
                # --ahrs-ext: `AP_HAL::Util::PersistentData &pd = hal.util->persistent_data;` (AP_AHRS.cpp:1780, a type
                # the translation does not hold), `const auto *sitl = AP::sitl();` (AP_AHRS.cpp:662): another name for
                # the boundary object (reads are inputs, writes outputs)
                self.boundary_locals[d["id"]] = bo
                return []
        if kids(d) and self.dropped_call(kids(d)[0]) is not None:
            return self.dropped_local(d)
        if INS_GPS[0] and not non_attr(kids(d)) and self.in_static_false(d):
            # --ins-gps: `const uint8_t *rtcm_data;` (AP_GPS.cpp:971), used only in a branch that cannot run (static_false)
            self.u.dropped[d["id"]] = d.get("name", "?")
            return ["pure ()  -- C++ `%s`: used only where the code cannot run, left out" % comment_safe(self.u.text_of(d) or d.get("name", ""))]
        if REACHABLE[0] and self.untranslated_decl(d) and self.only_dropped_uses(d):
            # `MAV_SEVERITY severity = ...;` read only by a dropped call (GCS_SEND_TEXT): left out with its assignments
            self.u.dropped[d["id"]] = d.get("name", "?")
            return ["pure ()  -- C++ `%s`: read only by calls left out (--drop), left out" % comment_safe(self.u.text_of(d) or d.get("name", ""))]
        if RING_BUFFERS[0] and self.rb_info() is not None and kids(d) and d["type"]["qualType"].rstrip().endswith("*") \
                and self.rb_offset(kids(d)[0]) is not None:
            return self.rb_alias_decl(d)
        if MAVLINK[0] and kids(d) and "name" in d and self.opt_call(kids(d)[0]) is not None:
            # --mavlink: `const mavlink_msg_entry_t *e = mavlink_get_msg_entry(msgid);`: an `Option` (null or the entry)
            if any(m.get("kind") in ("BinaryOperator", "CompoundAssignOperator", "UnaryOperator") and
                   m.get("opcode") in ("=", "++", "--", "+=", "-=") and strip_casts(kids(m)[0]).get("kind") == "DeclRefExpr" and
                   strip_casts(kids(m)[0])["referencedDecl"]["id"] == d["id"] for m in walk(self.u.body_of(self.fn) or self.fn or {})):
                raise Reject(d, "`const T *` local `%s` that is reassigned" % d["name"])
            pre, v = self.expr(kids(d)[0])
            name = self.ident(d["name"], d)
            t = self.opt_call(kids(d)[0])
            self.vars[d["id"]] = (name, t)
            self.declared.append((d["id"], name))
            self.opt_vars.add(d["id"])
            return pre + ["let %s : %s := %s" % (name, t.lean, v.text)]
        if MAVLINK[0] and kids(d) and "name" in d and self.struct_pointee(d["type"]["qualType"], d["type"].get("desugaredQualType"), d) is not None:
            ini = strip_casts(kids(d)[0])
            if (ini.get("kind") == "UnaryOperator" and ini.get("opcode") == "&") or self.gaccessor_of(ini) is not None or \
                    (ini.get("kind") == "DeclRefExpr" and ini["referencedDecl"]["id"] in self.u.struct_ptr_params | self.ptr_alias_ids):
                # --mavlink: `mavlink_status_t *status = mavlink_get_channel_status(chan);`, a pointer to an object that is
                # never reassigned: another name for that object (its indices fixed when the pointer is initialized)
                if any(m.get("kind") in ("BinaryOperator", "CompoundAssignOperator", "UnaryOperator") and
                       m.get("opcode") in ("=", "++", "--", "+=", "-=") and strip_casts(kids(m)[0]).get("kind") == "DeclRefExpr" and
                       strip_casts(kids(m)[0])["referencedDecl"]["id"] == d["id"] for m in walk(self.u.body_of(self.fn) or self.fn or {})):
                    raise Reject(d, "struct pointer `%s` that is reassigned" % d["name"])
                pre, path = self.struct_ptr_target(kids(d)[0])
                self.aliases[d["id"]] = path
                self.ptr_alias_ids.add(d["id"])
                return list(pre)
        if FRONT_ENDS[0] and kids(d) and d["type"]["qualType"].rstrip().endswith("*") and not any(
                m.get("kind") in ("BinaryOperator", "CompoundAssignOperator", "UnaryOperator") and m.get("opcode") in ("=", "++", "--", "+=", "-=") and
                strip_object(kids(m)[0]).get("kind") == "DeclRefExpr" and strip_object(kids(m)[0])["referencedDecl"]["id"] == d["id"]
                for m in walk(self.u.body_of(self.fn) or self.fn or {})):
            # --front-ends: `struct detect_state *dstate = &detect_state[instance];` (AP_GPS.cpp:634), a pointer
            # to a member or element that is never reassigned, used as `p->m`: another name for the object
            ini = strip_object(kids(d)[0])
            if ini.get("kind") == "UnaryOperator" and ini.get("opcode") == "&":
                r = self.resolve_path(kids(ini)[0])
                if r is not None and r[1].t is not None and r[1].t.kind == "record" and \
                        all(re.match(r"^let t'\d+ := ", l) for l in r[0]) and all(k in ("f", "i") for k, _ in r[1].steps):
                    self.ptr_aliases[d["id"]] = r[1]
                    return list(r[0])
        wpt = None
        if WORLD_PTRS[0] or SEMAPHORES:
            try:
                wpt = decl_type(d)[0]
            except Reject:
                wpt = None
        if wpt is not None and wpt.kind == "sem":
            # --semaphores: `WITH_SEMAPHORE(sem)` (a local `WithSemaphore`): no effect, one thread (PORT-PLAN 4.11)
            return ["pure ()  -- C++ `%s`: a semaphore, which does nothing here (one thread, --semaphores)" % comment_safe(self.u.text_of(d) or d.get("name", ""))]
        if MISSION[0] and d.get("storageClass") != "static" and not (wpt is not None and wpt.kind == "obj"):
            r = self.sel_local(d)       # --mission: a local pointer to one of several members of a local object
            if r is not None:
                return r
        if POINTER_PARAMS[0] and not C_MODE[0] and d.get("storageClass") != "static" and not (wpt is not None and wpt.kind == "obj") \
                and self.pp_pointee(d) is not None:
            return self.pp_local(d)
        t, ref = decl_type(d)
        if MEMBER_PTRS[0] and self.u.mtags and ref is not None and t.kind == "record" and kids(d) and "name" in d:
            ini = kids(d)[0]
            v = self.mtag_member(ini)
            mr = ([], v, t.info) if v is not None else self.mtag_ref(ini)
            if mr is not None:
                # --member-pointers: `auto &backend = backend_and_estimates.backend;` (AP_AHRS.cpp:897): the tag
                name = self.ident(d["name"], d)
                self.vars[d["id"]] = (name, CType("obj", info=t.info))
                self.declared.append((d["id"], name))
                self.tagrefs.add(d["id"])
                return list(mr[0]) + ["let %s := %s" % (name, mr[1].text)]
        if t.kind == "boundary" and ref is not None and kids(d) and self.boundary_obj(kids(d)[0]) is not None:
            # `AP_BattMonitor &battery = AP::battery();`: another name for the boundary object
            self.boundary_locals[d["id"]] = self.boundary_obj(kids(d)[0])
            return []
        if ref == "mut" and (POINTER_PARAMS[0] or EKF_ARRAYS[0]) and kids(d):
            return self.local_ref(d)
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
            if r is not None and not r[0] and r[1].root == ("w",):
                # `const Vector3p& psc_pos_offset_ned_m = _pos_control.get_pos_offset_NED_m();` (AC_WPNav.cpp:572),
                # a getter returning a member of a World object: the reference is that member, which
                # calls made while it is live may change; each use reads it in the World as it is then
                self.aliases[d["id"]] = r[1]
                return []
            if REACHABLE[0] and r is not None and r[1].root[0] in ("s", "w", "var", "p") and (self.stable_steps(kids(d)[0], r[1]) or self.stable_path(r[1])):
                # --reachable: `const ftype &q0 = stateStruct.quat[0];` (AP_NavEKF3_MagFusion.cpp:967), `const Location
                # &gpsloc = gps.location(selected_gps);`: another name for the member or element (its indices
                # fixed when the reference is bound); each use reads it as it is then
                self.aliases[d["id"]] = r[1]
                return r[0]
            wr = self.resolve_path(kids(c0)[0]) if r is None and c0.get("kind") == "MemberExpr" and WORLD[0] else None
            if wr is not None and wr[1].root == ("w",) and i0.get("valueCategory") == "lvalue":
                # `const Vector3p& psc_pos_offset_ned_m = _pos_control.get_pos_offset_NED_m();` on a World
                # object (AC_WPNav.cpp:572): the reference names the member the getter returns, which the
                # calls made after it may change; each use calls the getter again, on the World as it is then
                if kids(i0)[1:]:
                    raise Reject(d, "local reference `%s` to the result of a call with arguments on a World object" % d["name"])
                self.live_refs[d["id"]] = kids(d)[0]
                return []
            if r is None and (C_STRINGS[0] or BYTE_OBJECTS[0]) and self.const_table_element(kids(d)[0]):
                pass        # `const StorageArea &area = StorageManager::layout[i];`: an element of a constant table, a copy
            elif r is None and c0.get("kind") == "MemberExpr" and self.boundary_obj(kids(c0)[0]) is not None:
                pass        # `const Vector3f &v = _attitude_control.get_att_target_euler_rad();`: a boundary read,
                            # which does not change while the member function runs (README, "Classes"): a copy
            elif FRONT_ENDS[0] and r is None and const_fn and not any(
                    m.get("kind") in ("CallExpr", "BinaryOperator", "CompoundAssignOperator") or
                    (m.get("kind") == "UnaryOperator" and m.get("opcode") in ("++", "--")) or
                    (m.get("kind") == "CXXMemberCallExpr" and not (self.u.decl(strip_parens(kids(m)[0]).get("referencedMemberDecl")) or {}).get(
                        "type", {}).get("qualType", "").rstrip().endswith("const"))
                    for m in walk(kids(d)[0])):
                pass        # --front-ends: in a const member function, a reference to a view of this object's data
                            # (`primary_mag_field.xy()`, AP_Compass.cpp:2175), which does not change: a copy
            elif (FRONT_ENDS[0] or AHRS_EXT[0]) and r is not None and r[1].root[0] in ("s", "var", "w") and \
                    all(re.match(r"^let t'\d+ := ", l) for l in r[0]) and all(k in ("f", "i") for k, _ in r[1].steps) and \
                    not ((r[1].root[0] == "var" and r[1].root[1] not in self.mutable) or (r[1].root[0] in ("s", "p") and const_fn)):
                # --front-ends: `const Vector3f &c = compensation[i].get();` (Compass_PerMotor.cpp:227), a reference
                # to a location that may change while it is live: another name for that location (each use
                # reads it as it is then, as C++ does); its indices computed once, before
                self.aliases[d["id"]] = r[1]
                return list(r[0])
            elif r is None or not ((r[1].root[0] == "var" and r[1].root[1] not in self.mutable) or (r[1].root[0] in ("s", "p") and const_fn)):
                raise Reject(d, "local reference `%s` to something that may change while it is live (only references into variables that are never assigned, into the object in a const member function, or to the result of a const call on a boundary object are translated, as copies)" % d["name"])
        quals = d["type"]["qualType"]
        is_const = quals.startswith("const ") or " const" in quals or d.get("constexpr")
        if d.get("storageClass") == "static" and not is_const and REACHABLE[0] and WORLD[0] and self.fn is not None:
            return self.static_local(d, t)
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
        name = self.fresh_local(name, rid)
        if t.kind == "array" and init is None and (C_MODE[0] or ((C_STRINGS[0] or BYTE_OBJECTS[0]) and t.elem in (CHAR, UINT8)) or EKF_ARRAYS[0] or MAVLINK[0]) and \
                (rid in self.mutable or MAVLINK[0]):
            # `double tx[3];` (musl): indeterminate elements, which the C code writes before it
            # reads them (reading an indeterminate value is undefined): zeros here
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            return ["%s %s : %s := %s  -- uninitialized in C; every element is written before it is read" %
                    (mut, name, t.lean, zero_of(t, d).text)]
        if t.kind == "array" and init is None and POINTER_PARAMS[0] and rid in self.mutable and self.written_first(d, t):
            # `T inv[16];` whose every element is assigned (constant indices) before any other use
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            return ["%s %s : %s := %s  -- uninitialized in C++; every element is assigned before any read (checked)" %
                    (mut, name, t.lean, zero_of(t, d).text)]
        if (INS_GPS[0] or AHRS_EXT[0]) and t.kind == "array" and init is not None and init.get("kind") == "CXXConstructExpr" and not kids(init) \
                and t.elem.kind == "record" and zero_default_ctor(self.u, t.elem):
            # --ins-gps: `Vector3f last_average[INS_MAX_INSTANCES];` (AP_InertialSensor.cpp:1712): each element
            # default-constructed by a constructor that gives zero
            self.vars[rid] = (name, t)
            self.declared.append((rid, name))
            return ["%s %s : %s := %s  -- each element default-constructed (zero)" % (mut, name, t.lean, zero_of(t, d).text)]
        if t.kind == "array":
            if init is None or (init.get("kind") != "InitListExpr" and not (C_STRINGS[0] and strip_parens(init).get("kind") == "StringLiteral")):
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
            if t.kind == "record" and (not kids(init) or ((C_STRINGS[0] or BYTE_OBJECTS[0] or FRONT_ENDS[0]) and t.info.kind == "plain" and
                                                         all(m.get("kind") in ("ImplicitValueInitExpr", "InitListExpr") for m in walk(init) if m is not init))):
                # (`T x{};`: value-initialization, every member zero; a plain struct's members have no initializers of their own)
                pre, v = [], V("{}", ATOM) if not kids(init) else all_zero(t, init)
            elif FRONT_ENDS[0] and t.kind == "record" and t.info.kind == "plain" and \
                    all(m.get("kind") in ("ImplicitValueInitExpr", "InitListExpr") or
                        (m.get("kind") == "CXXConstructExpr" and not kids(m) and zero_default_ctor(self.u, ctype_of(m)))
                        for m in walk(init) if m is not init and not (m.get("kind") == "CXXConstructExpr" and not kids(m))
                        or (m.get("kind") == "CXXConstructExpr" and not kids(m) and not zero_default_ctor(self.u, ctype_of(m)))):
                # --front-ends: `EstRecord r {};` with members of classes whose default construction is zero
                pre, v = [], all_zero(t, init)
            elif (FRONT_ENDS[0] or AHRS_EXT[0]) and (t.is_scalar() or getattr(t, "bu", None) is not None) and \
                    all(m.get("kind") in ("ImplicitValueInitExpr", "InitListExpr") for m in walk(init)):
                pre, v = [], zero_of(t, d)      # --front-ends: `union DeviceId d {};` (value-initialization: zero)
            elif MISSION[0] and t.kind == "record" and self.zero_init_list(init):
                # --mission: `Mission_Command home_cmd = {};`, `PackedContent packed {};` (value-initialization: every
                # member zero, a byte union's default construction zero)
                pre, v = [], all_zero(t, init)
            elif REACHABLE[0] and t.kind == "record" and t.info.kind == "plain" and init.get("kind") == "InitListExpr":
                # `struct log_REV3 pkt{ event : uint8_t(event), };` (AP_DAL.cpp:227): the members in order
                pre, v = self.e_InitListExpr(init)
                self.deps |= type_deps(t)
            else:
                raise Reject(d, "brace or parenthesized initializer list for a scalar or object")
        else:
            pre, v = self.expr(init)
        held = []
        ci = strip_object(init)
        if C_STRINGS[0] and t.kind == "record" and ci.get("kind") == "CXXConstructExpr":
            # --c-strings: an object that holds the array of a pointer variable (held_member_type):
            # after each write of the object the variable is the object's array, and conversely
            for i, a in enumerate(kids(ci)):
                fl = self.held_param(ci, i)
                if fl is None:
                    continue
                r = self.ptr_ref(a)
                if r is None or r[2] is not None or r[1].steps or r[1].root[0] != "var":
                    raise Reject(a, "pointer held by object `%s` that is not a pointer variable at offset 0" % d["name"])
                held.append((fl, r[1]))
            if held:
                mut = "let mut"
                self.mutable.add(rid)
        self.vars[rid] = (name, t)
        self.declared.append((rid, name))
        for fl, pth in held:
            self.held.setdefault(rid, []).append((fl, pth))
            self.held_by.setdefault(pth.root[1], []).append((name, fl))
        return pre + ["%s %s : %s := %s" % (mut, name, t.lean, v.text)]

    def static_local(self, d, t):
        """--reachable --world: a mutable static local (`static uint64_t lastUnhealthyTime_us = 0;`,
        AP_NavEKF3.cpp:965; fill_nanf's NaN table, AP_Math.cpp:466) is a World field `Function'name`,
        zero at the start (a constant zero initializer or none: static storage is zero-filled, and C++
        initializes it before the first use); every use is that field."""
        if d["id"] in self.u.world_ids:
            return []
        if not (t.is_scalar() or (t.kind == "array" and t.elem.is_scalar())):
            raise Reject(d, "static local variable `%s` of type `%s` (numbers and arrays of numbers only)" % (d["name"], t.cname))
        init = non_attr(kids(d))
        if init:
            v = self.const_value(init[0]) if t.is_scalar() else None
            if v is None or float(v) != 0:
                raise Reject(d, "static local variable `%s` with an initializer other than zero" % d["name"])
        qn = qualified_name(self.u, self.fn)

        class Owner:
            cxx = qn
        name = "%s'%s" % (re.sub(r"\W+", "_", qn.replace("::", ".")), lean_field(d["name"], d))
        self.u.world.append({"name": name, "decl": d, "rec": None, "t": t, "static": Owner(), "ctor": None, "args": [], "local": True})
        self.u.world_ids[d["id"]] = name
        return ["pure ()  -- C++ `%s`: a World field (a static local)" % comment_safe(self.u.text_of(d) or d["name"])]

    def union_decl(self, d):
        """`union {float f; uint32_t i;} u = {x};`: u holds the bit pattern of its value; the
        initializer sets the member it names (the first)."""
        ui = self.local_union
        name = self.ident(d["name"], d)
        rid = d["id"]
        init = kids(d)[0] if kids(d) else None
        if init is not None and init.get("kind") == "CXXConstructExpr" and not kids(init):
            init = None                 # C++: the trivial default constructor (no initialization)
        mut = "let mut" if rid in self.mutable else "let"
        if init is None:
            if rid not in self.mutable:
                raise Reject(d, "union `%s` declared without an initializer and never assigned" % d["name"])
            self.vars[rid] = (name, ui.word)
            self.unions[rid] = ui
            self.declared.append((rid, name))
            self.uninit.add(rid)
            return ["%s %s : %s := %s  -- uninitialized in C; assigned before every read" % (mut, name, ui.word.lean, zero_of(ui.word, d).text)]
        if init.get("kind") != "InitListExpr" or len(kids(init)) != 1 or init.get("field", {}).get("id") not in ui.members:
            raise Reject(d, "union initializer other than `{value}`")
        mt = ui.members[init["field"]["id"]][1]
        pre, v = self.expr(kids(init)[0])
        self.vars[rid] = (name, ui.word)
        self.unions[rid] = ui
        self.declared.append((rid, name))
        return pre + ["%s %s : %s := %s" % (mut, name, ui.word.lean, bits_of(v, mt).text)]

    def array_init(self, init, t):
        si = strip_parens(init)
        if C_STRINGS[0] and si.get("kind") == "StringLiteral" and t.elem in (CHAR, UINT8, INT8):
            # `char buf[N] = "abc";`: the literal's bytes, then zeros
            bs = string_bytes(si)
            if len(bs) > t.n + 1 or (len(bs) == t.n + 1 and bs[-1] != 0):
                raise Reject(init, "string literal longer than the array `%s`" % t.cname)
            bs = (bs + [0] * t.n)[:t.n]
            return [], V(bytes_text(bs), ATOM)
        elems = kids(init)
        filler = init.get("array_filler")
        if filler is not None:
            if not all(f.get("kind") == "ImplicitValueInitExpr" or (FRONT_ENDS[0] and const_number(f) == 0) for f in filler):
                raise Reject(init, "array initializer with a non-zero filler")
        elif len(elems) != t.n:
            raise Reject(init, "array initializer with %d elements for `%s`" % (len(elems), t.cname))
        if t.elem.kind == "array":
            if filler is not None or any(e.get("kind") != "InitListExpr" for e in elems):
                raise Reject(init, "initializer of a two-dimensional table other than a full list of rows")
            rows = [self.array_init(e, t.elem) for e in elems]
            if any(p for p, _ in rows):
                raise Reject(init, "array initializer with side effects")
            return [], V("#[%s]" % ", ".join(v.text for _, v in rows), ATOM)
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
        k = self.const_int(c_n) if C_MODE[0] else None
        if k is not None:
            # a constant condition (`if (sizeof(x) == sizeof(float))`, musl's FORCE_EVAL): only the
            # branch it selects is translated, as only it can run
            taken = then_n if k else else_n
            note = "-- C `if (%s)`: constant, %s" % (comment_safe(self.u.text_of(c_n) or "..."), "true" if k else "false")
            if taken is None:
                return [note.replace("--", "pure ()  --", 1)], False
            lines, div = self.stmt(taken)
            return [note] + lines, div
        if INS_GPS[0] and self.static_false(c_n):
            # --ins-gps: `if (drivers[instance]->get_RTCMV3(rtcm_data, rtcm_len))` (AP_GPS.cpp:974): every object the
            # pointer can point to (closed world) has an overrider `{ return false; }`, so the branch is not taken
            note = "-- C++ `if (%s)`: false (every overrider the call can reach returns `false`; --ins-gps)" % comment_safe(self.u.text_of(c_n) or "...")
            if else_n is None:
                return [note.replace("--", "pure ()  --", 1)], False
            lines, div = self.stmt(else_n)
            return [note] + lines, div
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

    def static_false(self, c_n):
        """--ins-gps: is c_n a call `p->m(args)` through a World pointer whose every possible object's final
        overrider of m is `{ return false; }`, with arguments that are variables (no effects)?"""
        c = strip_object(c_n)
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_object(kids(c)[0])
        if c.get("kind") != "CXXMemberCallExpr":
            return False
        callee = strip_parens(kids(c)[0])
        if callee.get("kind") != "MemberExpr" or not callee.get("isArrow"):
            return False
        if not all(strip_object(a).get("kind") == "DeclRefExpr" for a in kids(c)[1:]):
            return False
        pt = self.obj_type(kids(callee)[0])
        mdecl = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
        if pt is None or mdecl is None or self.has_effects(kids(callee)[0]):
            return False
        targets = ptr_targets(self.u, pt.info)
        if not targets:
            return False
        for _, _, rec in targets:
            t = self.u.context(rec, c).resolve(mdecl, virtual_dispatch=True)
            body = next((x for x in kids(self.u.body_of(t) or t) if x.get("kind") == "CompoundStmt"), None)
            st = kids(body) if body is not None else []
            if len(st) != 1 or st[0].get("kind") != "ReturnStmt" or not kids(st[0]):
                return False
            v = strip_object(kids(st[0])[0])
            if v.get("kind") != "CXXBoolLiteralExpr" or v.get("value") is not False:
                return False
        return True

    def in_static_false(self, d):
        """--ins-gps: is every use of local d inside the condition or the `then` branch of an `if` whose condition is
        static_false (code that cannot run)?"""
        body = self.u.body_of(self.fn) if self.fn is not None else None
        uses = [m for m in walk(body or {}) if m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == d["id"]]
        if not uses:
            return False
        for m in uses:
            up, child = self.u.parent.get(m["id"]), m
            while up is not None and not (up.get("kind") == "IfStmt" and child is not (kids(up)[2] if up.get("hasElse") else None)
                                          and self.static_false(kids(up)[0])):
                up, child = self.u.parent.get(up["id"]), up
            if up is None:
                return False
        return True

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
                if s.get("kind") == "CaseStmt" and MISSION[0] and len(kids(s)) == 3:
                    # --mission: `case 0 ... 1:` (GNU case range, AP_Mission.cpp:1144): each value of the range
                    lo, hi = (kids(s)[j].get("value") or self.const_int(kids(s)[j]) for j in (0, 1))
                    if lo is None or hi is None or not 0 <= int(hi) - int(lo) <= 256:
                        raise Reject(s, "`case` range that is not constant or longer than 256 values")
                    labels += list(range(int(lo), int(hi) + 1))
                    s = kids(s)[2]
                    continue
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
        if k == "CharacterLiteral" and C_STRINGS[0]:
            return int(n["value"])
        if k == "ConstantExpr" and C_STRINGS[0]:
            return self.const_int(kids(n)[0])
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
        if k == "BinaryOperator" and n.get("opcode") == "/" and REACHABLE[0] and self.array_size(n) is not None:
            return self.array_size(n)       # ArduPilot's ARRAY_SIZE(a): the length of a
        if k == "BinaryOperator" and n.get("opcode") in ("==", "!=") and C_MODE[0]:
            # `sizeof(x) == sizeof(float)` (musl's FORCE_EVAL): C's int-valued comparison
            a, b = self.const_int(kids(n)[0]), self.const_int(kids(n)[1])
            if a is None or b is None:
                return None
            return int((a == b) == (n["opcode"] == "=="))
        if k == "UnaryExprOrTypeTraitExpr" and n.get("name") == "sizeof":
            # the size of a number type on this target (arm64: float 4, double 8, the integer types)
            t = parse_type_str(n["argType"]["qualType"], n["argType"].get("desugaredQualType", n["argType"]["qualType"]), n) \
                if "argType" in n else ctype_of(kids(n)[0])
            if t.kind in ("float", "double", "int"):
                return 4 if t.kind == "float" else 8 if t.kind == "double" else t.bits // 8
            if t.kind == "record" and t.info.cxx in SIZEOFS:
                return SIZEOFS[t.info.cxx]
            if C_STRINGS[0] or BYTE_OBJECTS[0]:
                try:
                    return byte_size_align(t, n)[0]
                except Reject:
                    return None
            return None
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

    LOOP_BOUND = "2^64"

    def general_loop(self, n, kind):
        """--general-loops: a `for`, `while` or `do` loop whose trip count the translator does not
        compute (musl's `for (k=1; iq[jk-k]==0; k++);`): a Lean loop of at most 2^64 iterations that
        tests the condition where C tests it and leaves by `break` when it is false. The C loop must
        end within 2^64 iterations (no execution reaches that bound; C++ may assume that a loop without
        side effects terminates). A `continue` in a `for` or `do` body is rejected (it would skip the
        step or the test)."""
        out = []
        if kind == "for":
            init, condvar, cond, inc, body = (kids(n) + [{}] * 5)[:5]
            if condvar:
                raise Reject(n, "`for` with a condition variable")
            if init:
                if init.get("kind") == "DeclStmt":
                    for d in kids(init):
                        out += self.local_decl(d)
                else:
                    out += self.effect(init)
        elif kind == "while":
            if n.get("hasVar"):
                raise Reject(n, "`while` with a condition variable")
            cond, body = kids(n)
            inc = None
        else:
            body, cond = kids(n)
            inc = None
        rotate = FRONT_ENDS[0] and kind == "for" and any(m.get("kind") == "ContinueStmt" for m in self.own_jumps(body))
        if kind in ("for", "do") and any(m.get("kind") == "ContinueStmt" for m in self.own_jumps(body)) and not rotate:
            raise Reject(n, "`continue` in a `%s` loop without a constant trip count" % kind)
        saved = self.copy_da()
        test = []
        if cond:
            pre_c, c = self.truth(cond)
            test = pre_c + ["if !%s then break" % c.at(ATOM)]
        self.loops.append("g" + kind)
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        step = self.effect(inc) if inc else []
        self.da = saved
        if rotate:
            # --front-ends: a `continue` in the body: the step runs at the top of every iteration but the
            # first (where C runs it after the body and after a `continue`), then the test
            first = self.temp()
            lines = ["if %s then" % first, "  %s := false" % first, "else"] + ["  " + l for l in (step or ["pure ()"])] + test + body_lines
            return out + ["let mut %s := true" % first,
                          "for _ in [0:%s] do  -- C loop without a constant trip count (--general-loops)" % self.LOOP_BOUND] + \
                ["  " + l for l in lines]
        lines = (body_lines + test) if kind == "do" else (test + body_lines + step)
        return out + ["for _ in [0:%s] do  -- C loop without a constant trip count (--general-loops)" % self.LOOP_BOUND] + \
            ["  " + l for l in (lines or ["pure ()"])]

    def own_jumps(self, body):
        """The break and continue statements of body that leave or continue the loop around it
        (not those of loops and switches inside it)."""
        out = []

        def visit(m, depth_loop, depth_switch):
            k = m.get("kind")
            if k == "ContinueStmt" and depth_loop == 0:
                out.append(m)
            if k == "BreakStmt" and depth_loop == 0 and depth_switch == 0:
                out.append(m)
            for c in kids(m):
                if isinstance(c, dict):
                    visit(c, depth_loop + (k in ("ForStmt", "WhileStmt", "DoStmt")), depth_switch + (k == "SwitchStmt"))
        visit(body, 0, 0)
        return out

    def for_stmt(self, n):
        try:
            return self.counted_for(n)
        except Reject as r:
            if r.node is not n:
                raise
            if RUNTIME_LOOPS[0]:
                try:
                    return self.runtime_for(n) if kids(n)[0] else self.cursor_for(n)
                except Reject as r2:
                    if r2.node is not n or not GENERAL_LOOPS[0]:
                        raise
            if not GENERAL_LOOPS[0]:
                raise
            return self.general_loop(n, "for"), False

    def range_for(self, n):
        """--front-ends: `for (auto &x : a)` over an array a of constant size N that the translator has a
        path for (a data member: `for (auto &sensor : sensors)`, AP_Baro.cpp:617): N iterations, x the
        element of the iteration (a reference: another name for it; a value: a copy)."""
        ds = [c for c in kids(n) if c.get("kind") == "DeclStmt"]
        body = kids(n)[-1]
        rng = next((kids(c)[0] for c in ds if kids(c) and kids(c)[0].get("name", "").startswith("__range")), None)
        lv = next((kids(c)[0] for c in ds if kids(c) and kids(c)[0].get("kind") == "VarDecl" and
                   not kids(c)[0].get("name", "").startswith("__")), None)
        if rng is None or lv is None or not kids(rng):
            raise Reject(n, "range-based `for` other than over an array")
        r = self.resolve_path(kids(rng)[0])
        if r is None or r[0] or r[1].t is None or r[1].t.kind != "array" or getattr(r[1].t, "dims", None):
            raise Reject(n, "range-based `for` over something other than an array member or variable")
        p = r[1]
        i = self.temp()
        elem = p.extend(("i", V(i, ATOM)), p.t.elem)
        q = lv.get("type", {}).get("qualType", "")
        pre_body = []
        if q.rstrip().endswith("&"):
            self.aliases[lv["id"]] = elem
        else:
            name = self.ident(lv["name"], lv)
            t = ctype_of(lv)
            self.vars[lv["id"]] = (name, t)
            pre_body = ["let %s := %s" % (name, self.read_path(elem, n).text)]
        saved = self.copy_da()
        self.loops.append("for")
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        return ["for %s in [0:%d] do" % (i, p.t.n)] + ["  " + l for l in pre_body + (body_lines or ["pure ()"])], False

    def counted_for(self, n):
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
        name = self.fresh_local(self.ident(d["name"], d), rid)
        if FRONT_ENDS[0]:
            self.declared.append((rid, name))
        self.vars[rid] = (name, t)
        used = rid in referenced_decls(body)
        saved = self.copy_da()
        self.loops.append("for")
        self.counters.add(rid)
        body_lines, _ = self.stmt(body)
        self.counters.discard(rid)
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
        if INS_GPS[0] and d.get("kind") == "VarDecl" and not kids(d):
            try:
                ctype_of(d)
            except Reject:
                return False        # (a pointer: local_decl decides, e.g. in_static_false)
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

    def label_tail(self, label_id, n):
        """C: the statements from the label to the end of its block (the label's statement and the
        statements after it), which a `goto` translation needs: they must leave the function by
        `return` on every path (no `break`, `continue`, or end of block), declare nothing and
        contain no other `goto`."""
        if self.fn is None:
            raise Reject(n, "`goto` outside a function")
        found = None
        for m in walk(self.fn):
            if m.get("kind") == "CompoundStmt":
                for j, c in enumerate(kids(m)):
                    if c.get("kind") == "LabelStmt" and c.get("declId") == label_id:
                        found = [kids(c)[0]] + kids(m)[j + 1:]
        if found is None:
            raise Reject(n, "`goto` to a label that is not a statement of a block")
        tail = {"kind": "CompoundStmt", "inner": found}
        if self.own_jumps(tail) or not self.ends_in_jump(tail) or \
                any(m.get("kind") in ("DeclStmt", "LabelStmt") for m in walk(tail) if m is not tail) or \
                any(m.get("kind") == "BreakStmt" or m.get("kind") == "ContinueStmt" for m in self.own_jumps(tail)):
            raise Reject(n, "`goto` to a label whose statements do not all end in `return` (or declare variables or labels)")
        return found

    def goto_stmt(self, n):
        """C `goto L`. Backward, inside the statements that follow L (musl's `goto recompute`,
        __rem_pio2_large.c:363): L's statements are the body of a loop and the goto is `continue`.
        Forward (`goto medium`, __rem_pio2.c:61): the statements of L, which end in `return`, are
        translated in place of the goto."""
        target = n.get("targetLabelDeclId")
        if target in self.label_loops:
            if len(self.loops) != self.label_loops[target]:
                raise Reject(n, "backward `goto` from inside a loop or `switch`")
            self.da = DIVERGE
            return ["continue  -- C `goto` to the label (the loop's next iteration)"], True
        tail = self.label_tail(target, n)
        if any(m.get("kind") == "GotoStmt" for t in tail for m in walk(t)):
            raise Reject(n, "forward `goto` to a label whose statements contain a `goto`")
        lines, div = self.block(tail)
        return ["-- C `goto %s`: the statements from the label on, which end in `return`" % self.label_name(target)] + lines, True

    def label_name(self, label_id):
        for m in walk(self.fn or {}):
            if m.get("kind") == "LabelStmt" and m.get("declId") == label_id:
                return m.get("name")
        return "?"

    def block(self, stmts):
        """Translate a statement list; returns (lines, diverges). Statements after a return,
        break or continue are unreachable and are not emitted. Counted while and do loops are
        recognized here, since they need the declaration of their counter."""
        out = []
        stmts = list(stmts)
        for i, s in enumerate(stmts):
            if s.get("kind") == "LabelStmt" and C_MODE[0]:
                label_id = s.get("declId")
                rest = [kids(s)[0]] + stmts[i + 1:]
                backward = [m for t in rest for m in walk(t) if m.get("kind") == "GotoStmt" and m.get("targetLabelDeclId") == label_id]
                if not backward:
                    stmts[i] = kids(s)[0]       # only forward gotos (translated at the goto) or none: a marker
                    s = stmts[i]
                else:
                    self.label_tail(label_id, s)
                    others = [m for m in walk(self.fn or {}) if m.get("kind") == "GotoStmt" and m.get("targetLabelDeclId") == label_id
                              and not any(m is x for t in rest for x in walk(t))]
                    if others:
                        raise Reject(s, "label `%s` with both forward and backward `goto`" % s.get("name"))
                    self.loops.append("label")
                    self.label_loops[label_id] = len(self.loops)
                    lines, _ = self.block(rest)
                    self.loops.pop()
                    del self.label_loops[label_id]
                    self.da = DIVERGE
                    rt = fn_return_type(self.fn) if self.fn is not None else VOID
                    after = [self.ret_line(None if rt.kind == "void" else zero_of(rt, s).text) +
                             "  -- not reached: every path of the label's statements returns (after 2^64 iterations, a zero)"]
                    return out + ["for _ in [0:%s] do  -- C label `%s`: each backward `goto` starts the next iteration (--general-loops)" %
                                  (self.LOOP_BOUND, s.get("name"))] + ["  " + l for l in lines] + after, True
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
            if s.get("kind") == "DoStmt" and self.storage_size_check(s):
                out.append("pure ()  -- C++ `%s`: a compile-time size check (AP_Common's ASSERT_STORAGE_SIZE)" % comment_safe(self.u.text_of(s) or "do"))
                continue
            if s.get("kind") == "DoStmt" and (self.const_int(kids(s)[1]) == 0 or (strip_parens(kids(s)[1]).get("kind") == "CXXBoolLiteralExpr"
                                                                               and not strip_parens(kids(s)[1]).get("value"))
                                              or (AHRS_EXT[0] and strip_parens(kids(s)[1]).get("castKind") == "IntegralToBoolean"
                                                  and self.const_int(kids(strip_parens(kids(s)[1]))[0]) == 0)):
                # (--ahrs-ext: `IGNORE_RETURN(x)`, `do {if (x) {}} while(0)` in C++, AP_Common.h:64)
                # `do { ... } while (0)` (musl's statement macros, GET_FLOAT_WORD): the body once; a
                # `break` or `continue` in it leaves the statement, as in a loop of one iteration
                saved = self.copy_da()
                self.loops.append("once")
                body_lines, div = self.stmt(kids(s)[0])
                self.loops.pop()
                if not div:
                    self.da = saved if self.da is DIVERGE else self.da
                out += ["for _ in [0:1] do"] + ["  " + l for l in (body_lines or ["pure ()"])]
                continue
            if s.get("kind") in ("WhileStmt", "DoStmt") and GENERAL_LOOPS[0]:
                kind = "while" if s.get("kind") == "WhileStmt" else "do"
                try:
                    out += self.counted_loop(s, kind, stmts, i)
                except Reject as r:
                    if r.node is not s:
                        raise
                    out += self.general_loop(s, kind)
                continue
            if s.get("kind") == "WhileStmt" and RUNTIME_LOOPS[0]:
                try:
                    out += self.counted_loop(s, "while", stmts, i)
                except Reject as r:
                    if r.node is not s:
                        raise
                    out += self.runtime_while(s)
                continue
            if s.get("kind") == "WhileStmt":
                out += self.counted_loop(s, "while", stmts, i)
                continue
            if s.get("kind") == "DoStmt":
                out += self.counted_loop(s, "do", stmts, i)
                continue
            if SURVEY[0] is not None:
                # --survey: report the statement's rejection and go on with the next statement (its
                # local variables declared with their types, so that later uses are translated)
                try:
                    lines, div = self.stmt(s)
                except Reject as e:
                    SURVEY[0](e)
                    self.survey_hit = True
                    if self.da is not DIVERGE:
                        self.da |= self.assigned(s) & self.uninit     # no cascade of "may be uninitialized"
                    for d in (kids(s) if s.get("kind") == "DeclStmt" else []):
                        if d.get("kind") == "VarDecl" and d["id"] not in self.vars and "name" in d:
                            try:
                                self.vars[d["id"]] = (self.ident(d["name"], d), decl_type(d)[0])
                                self.mutable.add(d["id"])
                            except Reject:
                                pass
                    lines, div = ["pure ()  -- (survey) rejected statement"], False
            else:
                lines, div = self.stmt(s)
            out += lines
            if div:
                return out, True
        return out, False

    # -- --ekf-arrays (README.md, "Phase 3: EKF data structures") ------------------------------

    def md_subscript(self, n):
        """`a[i]` where a is a flat multidimensional array (or a row of one): (pre, Path) of the row
        (a step ('row', offset) with the row's type) or, for the last dimension, of the element at
        the flat index; None if a is not such an array."""
        base, idx = kids(n)
        if not (base.get("kind") == "ImplicitCastExpr" and base.get("castKind") == "ArrayToPointerDecay"):
            return None
        r = self.resolve_path(kids(base)[0])
        if r is None:
            return None
        pre, bp = r
        dims = getattr(bp.t, "dims", None) if bp.t is not None and bp.t.kind == "array" else None
        row = bp.steps[-1][1] if bp.steps and bp.steps[-1][0] == "row" else None
        if not dims and row is None:
            return None
        pre_i, nat = self.nat_index(idx)
        if dims:
            stride = 1
            for d in dims[1:]:
                stride *= d
            off = self.md_mul(nat, stride)
        else:
            off = nat
        if row is not None:
            off = self.md_add(row, off)
            steps = bp.steps[:-1]
        else:
            steps = bp.steps
        if dims and len(dims) > 1:
            rt = CType("array", elem=bp.t.elem, n=bp.t.n // dims[0])
            if len(dims) > 2:
                rt.dims = dims[1:]
            return pre + pre_i, Path(bp.root, bp.root_text, steps + [("row", off)], rt)
        return pre + pre_i, Path(bp.root, bp.root_text, steps + [("i", off)], bp.t.elem)

    @staticmethod
    def md_mul(v, k):
        if k == 1:
            return v
        if re.match(r"^\d+$", v.text):
            return V(str(int(v.text) * k), ATOM)
        return V("%s * %d" % (v.at(MUL), k), MUL)

    @staticmethod
    def md_add(a, b):
        if re.match(r"^\d+$", a.text) and re.match(r"^\d+$", b.text):
            return V(str(int(a.text) + int(b.text)), ATOM)
        if a.text == "0":
            return b
        if b.text == "0":
            return a
        return V("%s + %s" % (a.at(ADD), b.at(ADD + 1)), ADD)

    def md_whole(self, e):
        """--ekf-arrays: the object a `memset` target names: `&x`, `(void *)&x`, an array `a`
        (decayed), `&a[0]`, `&a[0][0]` (the whole array): (pre, Path), else None."""
        e = rb_strip(e)
        if e.get("kind") == "UnaryOperator" and e.get("opcode") == "&":
            t = strip_parens(kids(e)[0])
            while t.get("kind") == "ArraySubscriptExpr" and self.const_int(kids(t)[1]) == 0:
                b = kids(t)[0]
                if not (b.get("kind") == "ImplicitCastExpr" and b.get("castKind") == "ArrayToPointerDecay"):
                    break
                t = strip_parens(kids(b)[0])
            r = self.resolve_path(t)
            return (r, t) if r is not None else None
        r = self.resolve_path(e)
        return (r, e) if r is not None and r[1].t is not None and r[1].t.kind == "array" else None

    def md_memset(self, n, args):
        """--ekf-arrays: `memset(T, 0, sizeof(x))` with T one of md_whole's forms naming x: x zero."""
        a0, a1, a2 = args
        w = self.md_whole(a0)
        sz = strip_parens(a2)
        if w is None or self.const_int(a1) != 0 or sz.get("kind") != "UnaryExprOrTypeTraitExpr" or sz.get("name") != "sizeof":
            return None
        (pre, p), tnode = w
        if "argType" in sz:
            st = parse_type_str(sz["argType"]["qualType"], sz["argType"].get("desugaredQualType", sz["argType"]["qualType"]), sz)
            if st != p.t:
                raise Reject(n, "`memset` whose size `sizeof(%s)` is not that of its target" % st.cname)
        elif self.u.text_of(strip_parens(kids(sz)[0])) != self.u.text_of(tnode):
            raise Reject(n, "`memset` whose size is not `sizeof` of its target")
        if p.steps and p.steps[-1][0] == "row":
            raise Reject(n, "`memset` of a row of an array")
        return pre + [self.write_path(p, all_zero(p.t, n), n)], None

    def md_memcpy(self, n, args):
        """--ekf-arrays: `memcpy(&x, &y, sizeof(z))` (md_whole's forms) between objects whose scalar
        leaves in the first sizeof(z) bytes have the same offsets and types (EKFGSF_yaw.cpp:535 copies
        the first two rows of a `Matrix3F` into `ftype R_prev[2][3]`): each such leaf of x becomes the
        leaf of y at its offset; x's other leaves keep their values."""
        a0, a1, a2 = args
        wd, ws = self.md_whole(a0), self.md_whole(a1)
        sz = strip_parens(a2)
        if wd is None or ws is None or sz.get("kind") != "UnaryExprOrTypeTraitExpr" or sz.get("name") != "sizeof":
            return None
        (pre_d, pd), _ = wd
        (pre_s, ps), _ = ws
        zt = parse_type_str(sz["argType"]["qualType"], sz["argType"].get("desugaredQualType", sz["argType"]["qualType"]), sz) \
            if "argType" in sz else ctype_of(kids(sz)[0])
        nbytes, _ = byte_size_align(zt, n)
        dl, sl = type_leaves(pd.t, n), type_leaves(ps.t, n)
        if nbytes > byte_size_align(pd.t, n)[0] or nbytes > byte_size_align(ps.t, n)[0]:
            raise Reject(n, "`memcpy` of more bytes than its source or destination holds")
        src = {}
        for off, steps, lt in sl:
            if off < nbytes:
                if off + byte_size_align(lt, n)[0] > nbytes:
                    raise Reject(n, "`memcpy` that copies part of a scalar")
                src[off] = (steps, lt)
        dst = {}
        for off, steps, lt in dl:
            if off < nbytes:
                if off not in src or src[off][1] != lt or off + byte_size_align(lt, n)[0] > nbytes:
                    if BYTE_OBJECTS[0]:
                        return None         # a copy of bits between types (`memcpy(&u, &f, 4)`): --byte-objects
                    raise Reject(n, "`memcpy` between objects whose scalars in the bytes copied differ in offset or type")
                dst[off] = steps
        if len(dst) != len(src):
            if BYTE_OBJECTS[0]:
                return None
            raise Reject(n, "`memcpy` between objects whose scalars in the bytes copied differ in offset or type")
        sv = self.read_path(ps, n)
        dv = self.read_path(pd, n, check_init=False)
        lines = pre_d + pre_s
        if not SIMPLE.match(sv.text):
            t = self.temp()
            lines.append("let %s := %s" % (t, sv.text))
            sv = V(t, ATOM)
        by_steps = {tuple(map(tuple, st)): off for off, st in dst.items()}

        def build(tt, steps):
            key = tuple(map(tuple, steps))
            if key in by_steps:
                return leaf_text(sv.text, src[by_steps[key]][0])
            if tt.kind == "record":
                fs = [f for f in tt.info.all_fields() if f.category == "state"]
                return "({ %s } : %s)" % (", ".join("%s := %s" % (f.lean, build(f.t, steps + [("f", f.lean)])) for f in fs), tt.lean)
            if tt.kind == "array":
                return "#[%s]" % ", ".join(build(tt.elem, steps + [("i", i)]) for i in range(tt.n))
            return leaf_text(dv.at(ATOM), steps)
        return lines + [self.write_path(pd, V(build(pd.t, []), ATOM), n)], None

    # -- --ring-buffers (README.md, "Phase 3: EKF data structures"; monomorphize_buffers) ---------

    def rb_info(self):
        """The monomorphized storage of the type-erased base of this context's class (a dict: elem,
        buf, alloc, E, acc), or None."""
        if not RING_BUFFERS[0] or self.ctx is None:
            return None
        for r in self.ctx.rec.chain():
            rb = getattr(r, "rb", None)
            if rb is not None:
                return rb
        return None

    def rb_is_buf(self, n):
        """Is n `this->B`, the storage member (through casts)?"""
        if self.rb_info() is None:
            return False
        e = rb_strip(n)
        f = self.this_field(e) if e.get("kind") == "MemberExpr" else None
        return f is not None and getattr(f, "rb_role", None) == "buf"

    def rb_is_elsize(self, n):
        e = rb_strip(n)
        f = self.this_field(e) if e.get("kind") == "MemberExpr" else None
        return f is not None and f.id == self.rb_info()["E"].id

    def rb_paths(self):
        """Paths of the elements (`B`) and of the flag `B'alloc`."""
        rb = self.rb_info()
        return Path(("s",), "s", [("f", rb["buf"].lean)], rb["buf"].t), Path(("s",), "s", [("f", rb["alloc"].lean)], BOOL)

    def rb_offset(self, n):
        """(pre, Nat index) for a call of an element accessor on this object (`get_offset(i)`,
        `ekf_imu_buffer::get(index)`; the index converted to the accessor's parameter type), or None."""
        rb = self.rb_info()
        if rb is None:
            return None
        e = rb_strip(n)
        if e.get("kind") != "CXXMemberCallExpr" or len(kids(e)) != 2:
            return None
        callee = strip_parens(kids(e)[0])
        if callee.get("kind") != "MemberExpr" or strip_object(kids(callee)[0]).get("kind") != "CXXThisExpr":
            return None
        m = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
        if m is None or m["id"] not in rb["acc"]:
            return None
        return self.nat_index(kids(e)[1])

    def rb_elem(self, n):
        """(pre, Path) of the element an accessor call n points to, or None."""
        r = self.rb_offset(n)
        if r is None:
            return None
        pre, nat = r
        return pre, self.rb_paths()[0].extend(("i", nat), self.rb_info()["elem"])

    def rb_param(self, p, body):
        """A `void *` (`const void *`) parameter of the type-erased class: the element the caller
        passes as `&x`, by reference if the body copies into it (`memcpy(element, ...)`, `memset`)."""
        if "name" not in p:
            raise Reject(p, "unnamed parameter")
        pt = self.rb_info()["elem"]
        written = not p["type"]["qualType"].startswith("const ") and any(
            m.get("kind") == "CallExpr" and len(kids(m)) == 4 and
            (strip_parens(kids(m)[0]).get("kind") == "ImplicitCastExpr" and
             strip_parens(kids(strip_parens(kids(m)[0]))[0]).get("referencedDecl", {}).get("name") in ("memcpy", "memset")) and
            rb_strip(kids(m)[1]).get("kind") == "DeclRefExpr" and rb_strip(kids(m)[1])["referencedDecl"]["id"] == p["id"]
            for m in walk(body or {}))
        pn = self.ident(p["name"], p)
        self.vars[p["id"]] = (pn, pt)
        self.declared.append((p["id"], pn))
        self.rb_params.add(p["id"])
        if written:
            self.outs.append((p["id"], pn, pt))
            self.mutable.add(p["id"])
            return (p, pn, pt, "mut")
        return (p, pn, pt, "const")

    def rb_param_path(self, n):
        """The Path of a `void *` parameter (n, through casts), or None."""
        e = rb_strip(n)
        if e.get("kind") != "DeclRefExpr" or e["referencedDecl"]["id"] not in self.rb_params:
            return None
        name, t = self.vars[e["referencedDecl"]["id"]]
        return Path(("var", e["referencedDecl"]["id"]), name, [], t)

    def rb_call(self, n, name, args):
        """`memcpy(element, get_offset(i), elsize)` and back (an element assigned), `memset(element,
        0, elsize)` (the zero element), `memset(B, 0, k*uint32_t(elsize))` (the first k elements
        zero), `free(B)` (directly before `B = calloc(...)`: no effect)."""
        rb = self.rb_info()
        if name == "free" and len(args) == 1 and self.rb_is_buf(args[0]):
            if not any(m.get("kind") == "BinaryOperator" and m.get("opcode") == "=" and self.rb_is_buf(kids(m)[0])
                       and rb_strip(kids(m)[1]).get("kind") == "CallExpr" for m in walk(self.fn or {})):
                raise Reject(n, "`free` of the storage of a type-erased container in a function that does not allocate it again")
            return ["pure ()  -- C++ `free(%s)`: the storage is allocated again below (--ring-buffers)" % rb["buf"].name], None
        if name == "memcpy" and len(args) == 3 and self.rb_is_elsize(args[2]):
            de, se = self.rb_elem(args[0]), self.rb_elem(args[1])
            dp, sp = self.rb_param_path(args[0]), self.rb_param_path(args[1])
            if de is not None and sp is not None:
                return de[0] + [self.write_path(de[1], self.read_path(sp, n), n)], None
            if dp is not None and se is not None:
                return se[0] + [self.write_path(dp, self.read_path(se[1], n), n)], None
            raise Reject(n, "`memcpy` in a type-erased container other than between an element and a `void *` parameter")
        if name == "memset" and len(args) == 3 and self.const_int(args[1]) == 0:
            dp = self.rb_param_path(args[0])
            if dp is not None and self.rb_is_elsize(args[2]):
                return [self.write_path(dp, all_zero(rb["elem"], n), n)], None
            cnt = rb_strip(args[2])
            if self.rb_is_buf(args[0]) and cnt.get("kind") == "BinaryOperator" and cnt.get("opcode") == "*" and self.rb_is_elsize(kids(cnt)[1]):
                pre, k = self.expr(kids(cnt)[0])
                kt = ctype_of(kids(cnt)[0])
                if not kt.is_int():
                    raise Reject(n, "`memset` of a type-erased container with a count of type `%s`" % kt.cname)
                bp = self.rb_paths()[0]
                z = all_zero(rb["elem"], n)
                t = self.temp()
                v = V("%s.mapIdx (fun i x => if i < %s then %s else x)" % (self.read_path(bp, n).at(ATOM), t, z.at(ATOM)), APP)
                return pre + ["let %s := %s" % (t, app("%s.toNat" % kt.lean, k).text), self.write_path(bp, v, n)], None
        raise Reject(n, "`%s` in a type-erased container other than the forms of README.md \"Phase 3: EKF data structures\"" % name)

    def rb_alloc(self, n, rhs, want_value):
        """`B = calloc(k, elsize)`: k zero elements, `B'alloc` true (the allocation is assumed to
        succeed, as `new (std::nothrow)`; calloc(0, n) is not a null pointer on the reference target)."""
        rb = self.rb_info()
        c = rb_strip(rhs)
        callee = strip_parens(kids(c)[0]) if c.get("kind") == "CallExpr" and kids(c) else {}
        fname = strip_parens(kids(callee)[0]).get("referencedDecl", {}).get("name") if callee.get("kind") == "ImplicitCastExpr" and kids(callee) else None
        if want_value or fname != "calloc" or len(kids(c)) != 3 or not self.rb_is_elsize(kids(c)[2]):
            raise Reject(n, "assignment to the storage of a type-erased container other than `B = calloc(k, elsize);`")
        a = kids(c)[1]
        pre, k = self.expr(a)
        kt = ctype_of(a)
        if not kt.is_int():
            raise Reject(n, "`calloc` with a count of type `%s`" % kt.cname)
        bp, ap_ = self.rb_paths()
        z = all_zero(rb["elem"], n)
        return pre + [self.write_path(bp, V("Array.replicate %s %s" % (app("%s.toNat" % kt.lean, k).at(ATOM), z.at(ATOM)), APP), n),
                      self.write_path(ap_, V("true", ATOM), n)], None

    def rb_alias_decl(self, d):
        """`T *el = (T *)get_offset(i);` (T the element type or one of its bases): el names element i."""
        rb = self.rb_info()
        if d["id"] in self.mutable:
            raise Reject(d, "pointer to an element of a type-erased container that is assigned")
        q = d["type"].get("desugaredQualType", d["type"]["qualType"]).rstrip()[:-1].strip()
        pt = parse_type_str(q, q, d)
        el = rb["elem"]
        if not (pt == el or (pt.kind == "record" and el.kind == "record" and pt.info in el.info.chain())):
            raise Reject(d, "pointer of type `%s` to an element of type `%s`" % (pt.cname, el.cname))
        pre, path = self.rb_elem(kids(d)[0])
        idx = path.steps[-1][1]
        if not SIMPLE.match(idx.text):
            t = self.temp()
            pre = pre + ["let %s := %s" % (t, idx.text)]
            path = Path(path.root, path.root_text, path.steps[:-1] + [("i", V(t, ATOM))], path.t)
        self.rb_alias[d["id"]] = path
        return pre

    def rb_index_path(self, n):
        """--ring-buffers: `buf[i]` where buf's class is a monomorphized wrapper whose `operator[]` is
        `T *ret = (T *)Base::get(index); return *ret;` (EKF_IMU_buffer_t, EKF_Buffer.h:191-194; a call
        of it is the element itself, as C++'s reference: `storedOutput[i].quat = q`): (pre, Path of
        the element), else None."""
        if operator_name(n) != "operator[]" or len(kids(n)) != 3:
            return None
        callee = strip_parens(kids(n)[0])
        if callee.get("kind") == "ImplicitCastExpr":
            callee = strip_parens(kids(callee)[0])
        decl = self.u.canonical(self.u.decl(callee.get("referencedDecl", {}).get("id")))
        rec = self.u.parent_record(decl) if decl is not None else None
        rb = next((getattr(x, "rb", None) for x in rec.chain() if getattr(x, "rb", None) is not None), None) if rec else None
        body = self.u.body_of(decl) if rb is not None else None
        cs = next((c for c in kids(body) if c.get("kind") == "CompoundStmt"), None) if body else None
        st = kids(cs) if cs else []
        if len(st) != 2 or st[0].get("kind") != "DeclStmt" or st[1].get("kind") != "ReturnStmt" or not kids(st[1]):
            return None
        v = kids(st[0])[0] if kids(st[0]) else {}
        init = rb_strip(kids(v)[0]) if v.get("kind") == "VarDecl" and kids(v) else {}
        if init.get("kind") != "CXXMemberCallExpr" or len(kids(init)) != 2:
            return None
        acc = self.u.canonical(self.u.decl(strip_parens(kids(init)[0]).get("referencedMemberDecl")))
        ret = strip_parens(kids(st[1])[0])
        if acc is None or acc["id"] not in rb["acc"] or not (ret.get("kind") == "UnaryOperator" and ret.get("opcode") == "*"
                                                            and strip_object(kids(ret)[0]).get("referencedDecl", {}).get("id") == v["id"]):
            return None
        ap = [p for p in kids(acc) if p.get("kind") == "ParmVarDecl"]
        r = self.resolve_path(kids(n)[1])
        if r is None:
            return None
        pre, bp = r
        pre_i, iv = self.expr(kids(n)[2])
        it = ctype_of(kids(n)[2])
        pt = decl_type(ap[0])[0]                # the accessor's parameter type (the index is converted to it)
        nat = app("%s.toNat" % pt.lean, conv(iv, it, pt, n))
        bf = bp.t.info.field_by_id(rb["buf"].id) if bp.t is not None and bp.t.kind == "record" else None
        if bf is None:
            return None
        return pre + pre_i, bp.extend(("f", bf.lean), bf.t).extend(("i", nat), rb["elem"])

    @staticmethod
    def this_chain(e):
        """The data members of `this->f1.f2...` (subscripts end the chain: `_RBRI[i].x` is [_RBRI]), else None."""
        e = strip_object(e)
        chain = []
        while True:
            k = e.get("kind")
            if k == "MemberExpr":
                chain.append(e.get("referencedMemberDecl"))
                e = strip_object(kids(e)[0])
            elif k == "ArraySubscriptExpr":
                chain = []
                e = strip_object(kids(e)[0])
                while e.get("kind") == "ImplicitCastExpr":
                    e = strip_object(kids(e)[0])
            elif k == "CXXThisExpr":
                return list(reversed(chain))
            else:
                return None

    def member_chain_invariant(self, m, body):
        """--reachable: is m (`this->_RBRH.num_instances`, a member of a member) unchanged by body? No
        write in body to a prefix or an extension of its chain of members (through an assignment, an
        increment, `&`, a non-const local reference bound into this object), no call of a non-const
        member function on this object or on a member of it."""
        mine = self.this_chain(m)
        if not mine:
            return False
        refs = {}
        for x in walk(body):
            if x.get("kind") == "VarDecl" and kids(x) and x["type"]["qualType"].rstrip().endswith("&") and \
                    not x["type"]["qualType"].startswith("const "):
                c = self.this_chain(kids(x)[0])
                if c is None:
                    return False
                refs[x["id"]] = c

        def overlaps(c):
            return c is None or c[:len(mine)] == mine[:len(c)]
        for x in walk(body):
            k = x.get("kind")
            tgt = None
            if (k == "BinaryOperator" and x.get("opcode") == "=") or k == "CompoundAssignOperator":
                tgt = kids(x)[0]
            elif k == "UnaryOperator" and x.get("opcode") in ("++", "--", "&"):
                tgt = kids(x)[0]
            elif k in ("CXXMemberCallExpr", "CXXOperatorCallExpr"):
                callee = strip_parens(kids(x)[0])
                md = self.u.decl(callee.get("referencedMemberDecl") or (callee.get("referencedDecl") or {}).get("id"))
                if md is not None and md.get("kind") == "CXXMethodDecl" and not md["type"]["qualType"].rstrip().endswith("const"):
                    obj = kids(callee)[0] if callee.get("kind") == "MemberExpr" else (kids(x)[1] if kids(x)[1:] else {})
                    ob = strip_object(obj)
                    if ob.get("kind") == "DeclRefExpr" and ob["referencedDecl"]["id"] in refs and overlaps(refs[ob["referencedDecl"]["id"]]):
                        return False
                    c = self.this_chain(obj)
                    if c is not None and overlaps(c):
                        return False
            if tgt is not None:
                t2 = strip_object(tgt)
                base = t2
                while base.get("kind") in ("MemberExpr", "ArraySubscriptExpr"):
                    base = strip_object(kids(base)[0])
                    while base.get("kind") == "ImplicitCastExpr":
                        base = strip_object(kids(base)[0])
                if base.get("kind") == "DeclRefExpr" and base["referencedDecl"]["id"] in refs:
                    if overlaps(refs[base["referencedDecl"]["id"]]):
                        return False
                    continue
                if base.get("kind") == "CXXThisExpr" and overlaps(self.this_chain(t2)):
                    return False
        return True

    def rb_member_invariant(self, m, body):
        """Is m `this->f` for a data member f that body does not write (no assignment, increment or
        address of it, no call of a non-const member function on this object other than an element
        accessor)?"""
        f = self.this_field(m) if m.get("kind") == "MemberExpr" else None
        if f is None or f.category != "state" or not f.t.is_scalar():
            return False
        rb = self.rb_info() or {"acc": {}}
        for x in walk(body):
            k = x.get("kind")
            tgt = None
            if (k == "BinaryOperator" and x.get("opcode") == "=") or k == "CompoundAssignOperator":
                tgt = kids(x)[0]
            elif k == "UnaryOperator" and x.get("opcode") in ("++", "--", "&"):
                tgt = kids(x)[0]
            elif k == "CXXMemberCallExpr":
                callee = strip_parens(kids(x)[0])
                md = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
                if strip_object(kids(callee)[0]).get("kind") == "CXXThisExpr" and md is not None and md["id"] not in rb["acc"] \
                        and not md["type"]["qualType"].rstrip().endswith("const"):
                    return False
            if tgt is not None:
                t2 = strip_object(tgt)
                if t2.get("kind") == "MemberExpr" and t2.get("referencedMemberDecl") == f.id:
                    return False
        return True

    def countdown_while(self, n):
        """`while (x > 0)` (or `while (x)`, `while (x != 0)`) with x an unsigned local or data member
        whose only write in the body is a statement `x--;` (`--x;`, `x -= 1;`) at the top level of the
        body, and no `continue`: every iteration that completes decrements x once and the test fails
        when x reaches 0, so the loop runs at most x's initial value times (EKF_Buffer.cpp:55,
        `while (count > 0)`): `for _ in [0:x0] do if !test then break; body`."""
        cond, body = kids(n)
        c = strip_parens(cond)
        while c.get("kind") == "ImplicitCastExpr" and c.get("castKind") in ("IntegralToBoolean", "IntegralCast", "LValueToRValue"):
            c = strip_parens(kids(c)[0])
        xv = c
        if c.get("kind") == "BinaryOperator" and c.get("opcode") in (">", "!=") and self.const_int(kids(c)[1]) == 0:
            xv = strip_parens(kids(c)[0])
            while xv.get("kind") == "ImplicitCastExpr" and xv.get("castKind") in ("IntegralCast", "LValueToRValue"):
                xv = strip_parens(kids(xv)[0])
        xv = strip_object(xv)
        if n.get("hasVar") or xv.get("kind") not in ("DeclRefExpr", "MemberExpr"):
            raise Reject(n, WHILE_BAD)
        r = self.resolve_path(xv)
        if r is None or r[0] or r[1].steps and r[1].root != ("s",) or not r[1].t.is_int() or r[1].t.signed:
            raise Reject(n, WHILE_BAD)
        xp = r[1]
        same = (lambda e: strip_object(e).get("kind") == xv.get("kind") and
                (strip_object(e).get("referencedMemberDecl") == xv.get("referencedMemberDecl") if xv.get("kind") == "MemberExpr"
                 else strip_object(e).get("referencedDecl", {}).get("id") == xv["referencedDecl"]["id"]))
        stmts = kids(body) if body.get("kind") == "CompoundStmt" else [body]
        decs = [s for s in stmts if (s.get("kind") == "UnaryOperator" and s.get("opcode") == "--" and same(kids(s)[0])) or
                (s.get("kind") == "CompoundAssignOperator" and s.get("opcode") == "-=" and same(kids(s)[0]) and self.const_int(kids(s)[1]) == 1)]
        writes = [x for x in walk(body) if ((x.get("kind") == "BinaryOperator" and x.get("opcode") == "=") or x.get("kind") == "CompoundAssignOperator"
                                            or (x.get("kind") == "UnaryOperator" and x.get("opcode") in ("++", "--", "&"))) and same(kids(x)[0])]
        if len(decs) != 1 or len(writes) != 1 or any(m.get("kind") == "ContinueStmt" for m in self.own_jumps(body)):
            raise Reject(n, WHILE_BAD + " (or `while (x > 0)` whose body decrements x once, at its top level)")
        if xp.root == ("s",) and not self.rb_member_invariant_calls(body):
            raise Reject(n, WHILE_BAD + " (the body calls a non-const member function, which may write the counter)")
        x0 = self.temp()
        lines = ["let %s := %s.toNat" % (x0, self.read_path(xp, n).at(ATOM))]
        pre_c, cv = self.truth(cond)
        saved = self.copy_da()
        self.loops.append("for")
        body_lines, _ = self.stmt(body)
        self.loops.pop()
        self.da = saved
        return lines + ["for _ in [0:%s] do  -- C++ `while (%s)`, which decrements its counter once per iteration (--ring-buffers)" %
                        (x0, comment_safe(self.u.text_of(cond) or "..."))] + \
            ["  " + l for l in pre_c + ["if !%s then break" % cv.at(ATOM)] + body_lines]

    def rb_member_invariant_calls(self, body):
        rb = self.rb_info() or {"acc": {}}
        for x in walk(body):
            if x.get("kind") == "CXXMemberCallExpr":
                callee = strip_parens(kids(x)[0])
                md = self.u.canonical(self.u.decl(callee.get("referencedMemberDecl")))
                if strip_object(kids(callee)[0]).get("kind") == "CXXThisExpr" and md is not None and md["id"] not in rb["acc"] \
                        and not md["type"]["qualType"].rstrip().endswith("const"):
                    return False
        return True

    # -- functions --------------------------------------------------------------------------

    def setup_params(self, params, body, exclude=()):
        """Declare the parameters; returns [(decl, lean name, CType, ref)], lean name None for a
        boundary-typed parameter or one in exclude (not passed in Lean)."""
        self.mutable = self.assigned(body) if body is not None else set()
        if POINTER_PARAMS[0] and body is not None:
            self.mutable |= self.pp_mutable(body)
        ps = []
        ospec = self.u.obj_param_spec.get((self.fn or {}).get("id"), {}) if C_STRINGS[0] else {}
        if FRONT_ENDS[0]:
            # --front-ends: an unnamed parameter (`typesafe_index operator++(int)`, AP_Common/TSIndex.h:47) is
            # named after its position (nothing reads it)
            params = [dict(p, name="unnamed'%d" % i) if "name" not in p and p.get("kind") == "ParmVarDecl" else p
                      for i, p in enumerate(params)]
        for pi, p in enumerate(params):
            if INS_GPS[0] and self.u.elem_params.get(p["id"]) is not None:
                # --ins-gps: a reference parameter bound to an element of an array member of a World object
                # (`AP_GPS::GPS_State &_state`, heap_elem_refs): the element's index
                pn = self.ident(p.get("name") or "unnamed'%d" % pi, p) + "'i"
                self.vars[p["id"]] = (pn, NAT)
                self.declared.append((p["id"], pn))
                ps.append((p, pn, NAT, "elem"))
                continue
            if INS_GPS[0] and p.get("kind") == "ParmVarDecl" and dead_pointer_param(self.u, p):
                # --ins-gps: a pointer parameter that nothing reads (`const uint16_t sample_rates[]` of the IMU
                # stand-in's constructor and `detect`, which only passes it on to the constructor): not passed
                ps.append((p, None, VOID, "dead"))
                continue
            if RING_BUFFERS[0] and self.rb_info() is not None and \
                    p.get("type", {}).get("qualType", "").replace("const ", "", 1).strip() == "void *":
                ps.append(self.rb_param(p, body))
                continue
            if MEMBER_PTRS[0] and self.u.mtags and p["id"] not in exclude:
                tp = self.tagref_param(p, body)
                if tp is not None:
                    ps.append(tp)
                    continue
            if TEXT_BUFFERS[0] and p["id"] not in exclude and "name" in p and \
                    re.match(r"^char ?\*$", p["type"].get("desugaredQualType", p["type"]["qualType"]).strip()):
                # --text-buffers: a `char *` parameter (the caller's buffer): the pending text, passed and returned
                pn = self.ident(p["name"], p)
                self.vars[p["id"]] = (pn, TEXTBUF)
                self.declared.append((p["id"], pn))
                ps.append((p, pn, TEXTBUF, "tbuf"))
                self.outs.append((p["id"], pn, TEXTBUF))
                self.mutable.add(p["id"])
                if OUTPUT_LOG[0]:
                    # (Phase 5d) the event by which a caller outside the translation (the vehicle's estimator bridge)
                    # receives the text written to its buffer: `Output.text_sink buffer text`, never pushed by the
                    # translation itself (gen_bridge.py pushes it after the call, the vehicle's drain formats it)
                    self.u.output_ctor("bridge", "text_sink", [("buf", CType("int", bits=64, signed=False)), ("text", TEXTBUF)],
                                       "the text written to a `char *` parameter's buffer, for a caller outside the translation", p)
                continue
            if WORLD_PTRS[0] and p["id"] not in exclude:
                wp = self.world_param(p)
                if wp is not None:
                    ps.append(wp)
                    continue
            if pi in ospec:
                # --c-strings: an object pointer parameter, translated for the class of the object passed
                # (object_pointer_spec): as a reference parameter of that class
                pt = CType("record", info=RECORDS[ospec[pi]])
                pn = self.ident(p["name"], p)
                self.vars[p["id"]] = (pn, pt)
                self.declared.append((p["id"], pn))
                ps.append((p, pn, pt, "mut"))
                self.outs.append((p["id"], pn, pt))
                self.mutable.add(p["id"])
                continue
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
            if MAVLINK[0] and p["id"] not in exclude and "name" in p:
                sp = self.struct_pointee(p["type"].get("qualType", ""), p["type"].get("desugaredQualType"), p)
                if sp is not None:
                    # --mavlink: `mavlink_message_t *msg`, `const mavlink_param_set_t *param_set`: the object the
                    # caller points to, by reference (returned if not const); the caller passes a non-null pointer
                    pt, const = sp
                    pn = self.ident(p["name"], p)
                    self.vars[p["id"]] = (pn, pt)
                    self.declared.append((p["id"], pn))
                    self.u.struct_ptr_params.add(p["id"])
                    if const:
                        ps.append((p, pn, pt, None))
                    else:
                        ps.append((p, pn, pt, "mut"))
                        self.outs.append((p["id"], pn, pt))
                        self.mutable.add(p["id"])
                    continue
            if POINTER_PARAMS[0] and not C_MODE[0] and p["id"] not in exclude:
                e = self.pp_param(p, body)
                if e is not None:
                    ps.append(e)
                    continue
            pm = self.pointer_param(p, body) if C_MODE[0] else None
            if pm is not None:
                # C: `T *p` used only as `*p` (an in/out scalar, musl's `__rem_pio2f(float, double *y)`)
                # or only as `p[i]` (an in/out array, `__rem_pio2_large(double *x, double *y, ...)`):
                # the value or array the caller passes, returned (as for `T &`) if the body writes it
                mode, et, written = pm
                if "name" not in p:
                    raise Reject(p, "unnamed parameter")
                pn = self.ident(p["name"], p)
                pt = et if mode == "scalar" else CType("array", elem=et, n=0)
                self.vars[p["id"]] = (pn, pt)
                self.declared.append((p["id"], pn))
                if mode == "scalar":
                    self.ptr_scalars.add(p["id"])
                else:
                    self.array_views.add(p["id"])
                if written:
                    ps.append((p, pn, pt, "mut"))
                    self.outs.append((p["id"], pn, pt))
                    self.mutable.add(p["id"])
                else:
                    ps.append((p, pn, pt, "cptr"))
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
                if FRONT_ENDS[0] and p["type"]["qualType"].lstrip().startswith("const "):
                    continue        # --front-ends: a nullable `const T *` (`drain_accumulated_samples(const Vector3f *scaling)`): read only
                self.outs.append((p["id"], pn, npt))
                self.mutable.add(p["id"])
                continue
            if MISSION[0] and p["id"] in exclude and "Functor<" in TYPEDEFS.get(strip_quals(p["type"]["qualType"])[0], p["type"].get("desugaredQualType", "")):
                ps.append((p, None, VOID, None))    # --mission: a functor parameter that only initializes a dropped member
                continue
            pt, ref = decl_type(p)
            if p["id"] in exclude:
                ps.append((p, None, pt, ref))
                continue
            if pt.kind == "array" and not (EKF_ARRAYS[0] and ref is not None):
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
        self.world_reads = False    # --world-pointers: takes the World
        self.world_writes = False   # --world-pointers: returns the World
        self.wtouch = set()


def translate_free(u, d, home, lean_name, defn=None):
    """A free function or a static method: its parameters, its result, its body."""
    defn = defn or d
    b = Body(u, defn, None, home=home)
    r = FreeResult()
    r.lean = lean_name
    params = [p for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
    body = next((c for c in kids(defn) if c.get("kind") == "CompoundStmt"), None)
    ret_param = pp_ret_param(defn)
    ret = NAT if ret_param is not None else (pp_fresh_return(u, defn) if POINTER_PARAMS[0] else None) or \
        (MAVLINK[0] and opt_return_type(d)) or fn_return_type(d)
    b.ret_ptr = ret_param
    b.ret_opt = ret if ret.kind == "opt" else None
    if ret.kind in ("array", "boundary", "param") and not getattr(ret, "fresh", False):
        raise Reject(d, "function returning `%s`" % ret.cname)
    b.void = ret.kind == "void"
    ps = b.setup_params(params, body)
    if any(pn is None and not (isinstance(ref, str) and ref.startswith("world:")) and ref != "dead" for _, pn, _, ref in ps):
        raise Reject(d, "boundary object as a parameter of a free function")
    if defn.get("variadic") or d.get("variadic"):
        if not C_STRINGS[0]:
            raise Reject(d, "variadic function")
        # --c-strings: the variadic arguments, as tagged slots (`va_start` makes the `va_list` of them)
        ps.append(({"kind": "Variadic", "id": "va'", "name": "...", "type": {"qualType": "..."}}, "va'", VARARGS, "va"))
        b.declared.append(("va'", "va'"))
    lines = []
    for p, pn, pt, ref in ps:
        if p["id"] in b.mutable:
            lines.append("let mut %s := %s" % (pn, pn))
    lines += b.prologue
    body_lines, div = b.block(kids(body))
    if not div:
        if ret.kind != "void" and not getattr(b, "survey_hit", False):
            raise Reject(d, "control may reach the end of non-void function `%s`" % d["name"])
        body_lines.append(b.ret_line(None))
    hs = b.hal_storage_param()
    if hs is not None:
        ps.append(hs)
        if hs[3] == "mut":
            lines.insert(0, "let mut %s := %s" % (b.HS, b.HS))
    if MAVLINK[0]:
        for g in b.global_params():
            ps.append(g)
            if g[3] == "mut":
                lines.insert(0, "let mut %s := %s" % (g[1], g[1]))
    comps = [pn for _, pn, _ in b.outs]
    r.world_reads = WORLD_PTRS[0] and "w" in b.reads | b.writes     # --world-pointers: the function reaches the World
    r.world_writes = WORLD_PTRS[0] and "w" in b.writes
    r.wtouch = set(b.wtouch)
    if r.world_writes:
        comps = ["w"] + comps
        lines.insert(0, "let mut w := w")
    elif ("w" in b.reads | b.writes or "s" in b.reads | b.writes or "p" in b.reads | b.writes) and not r.world_reads:
        pass
    if not comps and ret.kind == "void":
        raise Reject(d, "function `%s` returning void without reference parameters (no observable result)" % d["name"])
    r.lines = b.finish(lines + body_lines, comps)
    if MAVLINK[0]:
        for _, vt in list(b.vars.values()):
            b.deps |= type_deps(vt)     # --mavlink: the types of the locals (a struct declared before its first use)
    r.cparams, r.outs, r.ret = ps, list(b.outs), ret
    r.unused = b.unused()
    decl_params = [p for p in kids(d) if p.get("kind") == "ParmVarDecl"]
    groups = []
    for i, (p, pn, pt, ref) in enumerate(ps):
        if pn is None:
            continue        # --world-pointers: a reference to a file-scope object, not passed
        dp = decl_params[i] if i < len(decl_params) else p
        dflt = default_text(u, dp, home, b.deps) or default_text(u, p, home, b.deps)
        if ref == "ptr":
            groups.append(([pn + "'given"], BOOL, None))     # a nullable out-pointer's flag
            groups.append(([pn], pt, None))
            continue
        if p.get("id") in b.off_params:
            groups.append(([pn], pt, dflt))
            groups.append(([Body.off_name(pn)], NAT, None))     # --array-offsets: the pointer's offset
            continue
        if dflt is None and groups and groups[-1][1] == pt and groups[-1][2] is None and groups[-1][0][-1][-6:] != "'given":
            groups[-1][0].append(pn)
        else:
            groups.append(([pn], pt, dflt))
    r.binders = "".join(" (%s : %s%s)" % (" ".join(g), t.lean, "" if df is None else " := " + df) for g, t, df in groups)
    if r.world_reads:
        r.binders = " (w : World)" + r.binders
    rtys = (["World"] if r.world_writes else []) + [pt.lean_atom for _, _, pt in b.outs]
    if ret.kind != "void":
        rtys.append(ret.lean_atom if rtys else ret.lean)
    r.ret_lean = " × ".join(rtys)
    u.uses_libm |= b.uses_libm
    r.deps = b.deps | ({("world",)} if r.world_reads else set())
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
        self.semaphore = False  # --semaphores: a semaphore class (no state, no effect)
        self.functor = False    # --world-pointers: `Functor<...>` (modeled as `WFun`, not translated)
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
        def norm(t):        # `const class AP_Motors &` in a declaration is `const AP_Motors &` at a call
            if INS_GPS[0]:
                t = t.replace(" noexcept(false)", "")     # (--ins-gps: an inheriting constructor's type)
            return re.sub(r"\b(class|struct|enum) ", "", t.replace(" noexcept", "")).strip()
        want = norm(ctor_type)
        for m in self.methods:
            if m.get("kind") == "CXXConstructorDecl" and norm(m["type"]["qualType"]) == want:
                return m
        return None


def ctype_kind_record_ref(d):
    """Does member function d return a non-const reference to a class object?"""
    q = d.get("type", {}).get("qualType", "")
    ret = q.split("(")[0].strip()
    name = ret[:-1].strip() if ret.endswith("&") else ""
    if name in PARAM_CLASSES or name.split("::")[-1] in PARAM_CLASSES:
        return False                # a parameter: its value is read (Body.member_call), it is not an object
    if INS_GPS[0] and (name in BOUNDARY or name.split("::")[-1] in BOUNDARY):
        return True                 # --ins-gps: `AP_DAL_Compass &AP_DAL::compass()`, a member of a boundary object that is a boundary class
    return ret.endswith("&") and not ret.startswith("const ") and not re.match(r"^(float|double|bool|u?int\d+_t|int|unsigned|AP_\w+) ?&$", ret)


def zeroing_call(u, rec, st):
    """--reachable: is statement st a call `zero()` on this of a member function whose body is
    `memset(this, 0, sizeof(*this));`?"""
    st = strip_parens(st)
    if st.get("kind") != "CXXMemberCallExpr" or kids(st)[1:]:
        return False
    c = strip_parens(kids(st)[0])
    if c.get("kind") != "MemberExpr" or strip_object(kids(c)[0]).get("kind") != "CXXThisExpr":
        return False
    m = u.canonical(u.decl(c.get("referencedMemberDecl")))
    b = u.body_of(m) if m is not None else None
    cs = next((x for x in kids(b) if x.get("kind") == "CompoundStmt"), None) if b else None
    if cs is None or len(kids(cs)) != 1:
        return False
    call = strip_parens(kids(cs)[0])
    if call.get("kind") != "CallExpr" or len(kids(call)) != 4:
        return False
    f = strip_parens(kids(call)[0])
    while f.get("kind") == "ImplicitCastExpr":
        f = strip_parens(kids(f)[0])
    if (f.get("referencedDecl") or {}).get("name") != "memset":
        return False
    a0 = strip_parens(kids(call)[1])
    while a0.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr"):
        a0 = strip_parens(kids(a0)[0])
    a1 = strip_parens(kids(call)[2])
    while a1.get("kind") == "ImplicitCastExpr":
        a1 = strip_parens(kids(a1)[0])
    a2 = strip_parens(kids(call)[3])
    return a0.get("kind") == "CXXThisExpr" and a1.get("kind") == "IntegerLiteral" and a1.get("value") == "0" and \
        a2.get("kind") == "UnaryExprOrTypeTraitExpr" and any(x.get("kind") == "CXXThisExpr" for x in walk(a2))


def inherited_ctor(c):
    """--ins-gps: is c an inheriting constructor (implicit, `using B::B;` in the class: one base initializer
    `CXXInheritedCtorInitExpr`)?"""
    return c.get("kind") == "CXXConstructorDecl" and any(
        x.get("kind") == "CXXCtorInitializer" and "baseInit" in x and kids(x) and kids(x)[0].get("kind") == "CXXInheritedCtorInitExpr"
        for x in kids(c))


def heap_elem_refs(u, reject):
    """--ins-gps: a reference member of a heap class bound by its constructor to an element of an array member
    of a World object (`AP_GPS_Backend::state`, bound to `_state`, for which `AP_GPS::_detect_instance` passes
    `state[instance]`, AP_GPS.cpp:730, and `params[instance]`): the heap object holds the element's index (a
    field `state'i : Nat`), and the member is that element of the World object's array. The constructor
    parameter (and the inheriting constructor's) carries the index (u.elem_params); the construction sites
    pass the index of the element. u.wref[(class, member)] = ("elem", World object, [fields to the array])."""
    cand = {}       # ctor parameter id -> (heap class, field)
    for rec in u.heap:
        for b in rec.chain():
            for c in b.methods:
                if c.get("kind") != "CXXConstructorDecl":
                    continue
                defn = u.body_of(c) or c
                for ini in kids(defn):
                    if ini.get("kind") != "CXXCtorInitializer" or "anyInit" not in ini or not kids(ini):
                        continue
                    f = b.field_by_id(ini["anyInit"]["id"])
                    if f is None or f.category != "wref" or f.t is None or f.t.kind != "record" or world_object_of_class(u, f.t.info) is not None:
                        continue
                    if heap_singleton_field(u, f.t.info) is not None:
                        continue        # `AP_DAL &dal` of the EKF3 cores: the heap singleton (--ekf-types with --world-pointers)
                    e = strip_object(kids(ini)[0])
                    if e.get("kind") == "DeclRefExpr" and e["referencedDecl"].get("kind") == "ParmVarDecl":
                        cand[e["referencedDecl"]["id"]] = (rec, f)
    if not cand:
        return
    # inheriting constructors: their parameters by position are the base constructor's
    pos = {}        # constructor parameter id -> [(heap class, field)]
    for rec in u.heap:
        for c in rec.methods:
            if c.get("kind") != "CXXConstructorDecl":
                continue
            cps = [x for x in kids(c) if x.get("kind") == "ParmVarDecl"]
            if inherited_ctor(c) and rec.bases:
                bc = rec.bases[0].find_ctor(c["type"]["qualType"])
                bdef = (u.body_of(bc) or bc) if bc is not None else None
                bps = [x for x in kids(bdef) if x.get("kind") == "ParmVarDecl"] if bdef is not None else []
                for i, x in enumerate(cps):
                    if i < len(bps) and bps[i]["id"] in cand:
                        pos.setdefault(x["id"], []).append(cand[bps[i]["id"]])
                        u.elem_params[x["id"]] = None
            defn = u.body_of(c) or c
            dps = [x for x in kids(defn) if x.get("kind") == "ParmVarDecl"]
            for x in dps:
                if x["id"] in cand:
                    pos.setdefault(x["id"], []).append(cand[x["id"]])
    targets = {}    # (heap class id, field id) -> ("elem", World object, fields)
    for n in u.ids.values():
        if n.get("kind") != "CXXNewExpr":
            continue
        ce = next((c for c in kids(n) if c.get("kind") == "CXXConstructExpr"), None)
        rec = RECORDS.get(norm_template_args(strip_tag(n.get("type", {}).get("qualType", "")[:-1].strip())[0]))
        if ce is None or rec is None or rec not in u.heap:
            continue
        ctor = rec.find_ctor(ce.get("ctorType", {}).get("qualType", ""))
        if ctor is None:
            continue
        cps = [x for x in kids(ctor) if x.get("kind") == "ParmVarDecl"]
        cdef = u.body_of(ctor) or ctor
        dps = [x for x in kids(cdef) if x.get("kind") == "ParmVarDecl"]
        for i, a in enumerate(kids(ce)):
            hits = pos.get(cps[i]["id"] if i < len(cps) else None) or pos.get(dps[i]["id"] if i < len(dps) else None)
            if not hits:
                continue
            e = strip_object(a)
            if e.get("kind") != "ArraySubscriptExpr":
                reject(Reject(a, "argument for a reference member of a heap object that is not an element of an array member of a World object"))
                continue
            arr = strip_object(kids(e)[0])
            while arr.get("kind") == "ImplicitCastExpr":
                arr = strip_object(kids(arr)[0])
            fields = []
            while arr.get("kind") == "MemberExpr" and strip_object(kids(arr)[0]).get("kind") != "CXXThisExpr":
                fields.append(arr.get("name"))
                arr = strip_object(kids(arr)[0])
            if arr.get("kind") != "MemberExpr":
                reject(Reject(a, "argument for a reference member of a heap object that is not an element of an array member of a World object"))
                continue
            fields.append(arr.get("name"))
            fn = n
            while fn is not None and fn.get("kind") not in ("CXXMethodDecl", "CXXConstructorDecl"):
                fn = u.parent.get(fn["id"])
            owner = u.parent_record(fn) if fn is not None else None
            wname = u.world_self.get(owner.id) if owner is not None else None
            if wname is None:
                reject(Reject(a, "argument for a reference member of a heap object: an element of an array member of an object that is not a World object"))
                continue
            t = ("elem", wname, list(reversed(fields)))
            for hrec, f in hits:
                if targets.get((hrec.id, f.id), t) != t:
                    reject(Reject(a, "reference member `%s` bound to elements of different arrays" % f.name))
                targets[(hrec.id, f.id)] = t
    for (rid, fid), t in targets.items():
        u.wref[(rid, fid)] = t
    for pid, hits in pos.items():
        ts = {tuple(targets.get((r.id, f.id), (None,))[:2]) for r, f in hits}
        if len(ts) == 1 and None not in next(iter(ts)):
            u.elem_params[pid] = targets[(hits[0][0].id, hits[0][1].id)]
        else:
            u.elem_params.pop(pid, None)
    for pid in cand:
        if pid not in u.elem_params:
            r, f = cand[pid]
            if (r.id, f.id) in targets:
                u.elem_params[pid] = targets[(r.id, f.id)]


def int_lit_zero(n):
    """Is n (casts stripped) the integer literal 0?"""
    n = strip_object(n)
    while n.get("kind") in ("ImplicitCastExpr", "ConstantExpr", "ParenExpr"):
        n = strip_object(kids(n)[0])
    return n.get("kind") == "IntegerLiteral" and n.get("value") == "0"


def zeroing_default_ctor(u, t, seen=()):
    """--ins-gps: does the default constructor of t, run on zero-filled storage (a file-scope object, or memory
    from ArduPilot's zeroing `new`), leave it zero? zero_default_ctor, or a body of only `memset(&m, 0, ...)` and
    `m = T()` with T's default construction zero, and members whose classes' default constructors do the same."""
    if zero_default_ctor(u, t) and (t.kind != "record" or t.info.find_ctor("void ()") is not None or not t.info.fields):
        return True
    if t.kind != "record" or t.info.id in seen:
        return t.kind != "record" and t.is_scalar()
    ctor = t.info.find_ctor("void ()")
    if ctor is not None:
        body = u.body_of(ctor) or ctor
        for c in kids(body):
            if c.get("kind") == "CXXCtorInitializer":
                e = kids(c)[0] if kids(c) else None
                while e is not None and e.get("kind") in ("ImplicitCastExpr", "ConstantExpr", "ParenExpr", "ExprWithCleanups"):
                    e = kids(e)[0]
                if e is None or (e.get("kind") in ("IntegerLiteral", "FloatingLiteral") and float(e.get("value", "1")) == 0):
                    continue
                if e.get("kind") == "CXXConstructExpr" and not kids(e):
                    continue        # a member default-constructed (checked below)
                return False
            if c.get("kind") != "CompoundStmt":
                continue
            for st in kids(c):
                st = strip_object(st)
                while st.get("kind") == "ExprWithCleanups":
                    st = strip_object(kids(st)[0])
                fe = kids(st)[0] if st.get("kind") == "CallExpr" else {}
                while fe.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                    fe = kids(fe)[0]
                if st.get("kind") == "CallExpr" and len(kids(st)) == 4 and \
                        (fe.get("referencedDecl") or {}).get("name") == "memset" and int_lit_zero(kids(st)[2]):
                    continue        # `memset(&_params, 0, sizeof(_params))`
                if st.get("kind") in ("BinaryOperator", "CXXOperatorCallExpr") and (st.get("opcode") == "=" or operator_name(st) == "operator="):
                    rhs = strip_object(kids(st)[-1])
                    while rhs.get("kind") in ("ImplicitCastExpr", "MaterializeTemporaryExpr", "CXXBindTemporaryExpr", "ExprWithCleanups"):
                        rhs = strip_object(kids(rhs)[0])
                    if rhs.get("kind") in ("CXXTemporaryObjectExpr", "CXXConstructExpr", "CXXScalarValueInitExpr") and not kids(rhs):
                        try:
                            rt = ctype_of(rhs)
                        except Reject:
                            return False
                        if zeroing_default_ctor(u, rt, seen + (t.info.id,)):
                            continue    # `_delay_element_1 = T();`
                    return False
                return False
    for f in t.info.all_fields():
        if f.category != "state":
            continue
        ft = f.t.elem if f.t.kind == "array" else f.t
        if ft.kind == "record" and not zeroing_default_ctor(u, ft, seen + (t.info.id,)):
            return False
    return True


def dead_pointer_param(u, p, seen=()):
    """--ins-gps: is p a pointer parameter whose every use is as the argument of a dead pointer parameter
    of another function or constructor (none at all: dead)? Such a parameter is not passed (its argument
    must be without effects: a constant array, another dead parameter)."""
    q = p.get("type", {}).get("desugaredQualType", p.get("type", {}).get("qualType", "")).strip()
    if not q.endswith("*") or p["id"] in seen:
        return p["id"] in seen
    fn = u.parent.get(p["id"])
    body = u.body_of(fn) if fn is not None else None
    if fn is None or body is None or fn.get("kind") not in ("CXXConstructorDecl", "CXXMethodDecl", "FunctionDecl") or inherited_ctor(fn):
        return False        # a declaration without a definition: nothing is known (an inheriting constructor passes them on)
    if body is not fn:
        # the parameter of a declaration: the definition's parameter at its position
        k = [x["id"] for x in kids(fn) if x.get("kind") == "ParmVarDecl"].index(p["id"])
        p = [x for x in kids(body) if x.get("kind") == "ParmVarDecl"][k]
        if p["id"] in seen:
            return True
    for r in walk(body):
        if r.get("kind") != "DeclRefExpr" or r.get("referencedDecl", {}).get("id") != p["id"]:
            continue
        up, child = u.parent.get(r["id"]), r
        while up is not None and up.get("kind") in ("ImplicitCastExpr", "ParenExpr") and up.get("castKind", "NoOp") in ("LValueToRValue", "NoOp"):
            up, child = u.parent.get(up["id"]), up
        if up is None or up.get("kind") not in ("CXXConstructExpr", "CallExpr") or child not in kids(up):
            return False
        args = kids(up) if up.get("kind") == "CXXConstructExpr" else kids(up)[1:]
        i = next(j for j, a in enumerate(args) if a is child)
        if up.get("kind") == "CXXConstructExpr":
            rec = RECORDS.get(norm_template_args(strip_tag(up.get("type", {}).get("qualType", ""))[0]))
            callee = rec.find_ctor(up.get("ctorType", {}).get("qualType", "")) if rec is not None else None
        else:
            c = strip_parens(kids(up)[0])
            while c.get("kind") == "ImplicitCastExpr":
                c = strip_parens(kids(c)[0])
            callee = u.decl((c.get("referencedDecl") or {}).get("id") or c.get("referencedMemberDecl"))
        if callee is None:
            return False
        cb = u.body_of(callee) or callee
        cps = [x for x in kids(cb) if x.get("kind") == "ParmVarDecl"]
        if i >= len(cps) or not dead_pointer_param(u, cps[i], seen + (p["id"],)):
            return False
    return True


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
        if c.get("kind") == "CompoundStmt" and kids(c) and REACHABLE[0] and len(kids(c)) == 1 and zeroing_call(u, t.info, kids(c)[0]):
            continue        # `Location() { zero(); }` with `zero()` `memset(this, 0, sizeof(*this))` (AP_Common/Location.cpp:18)
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
        self.wtouch = set()     # --world: the World objects the method reaches
        self.uses_self = False  # --world-pointers: takes its own pointer `self'` (a heap object using `this` as a value)


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
                if MEMBER_PTRS[0] and key[2]:
                    twin = next((x for x in r.methods if x is not m and method_sigkey(x) == (key[0], key[1], False)), None)
                    if twin is not None and const_cast_forward(self.u.body_of(m) or m, twin):
                        # --member-pointers: `const AP_AHRS_Backend *backend_for_type(EKFType type) const { return
                        # const_cast<AP_AHRS*>(this)->backend_for_type(type); }` (AP_AHRS.h:1097): the non-const one
                        self.aliases[m["id"]] = twin
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
        if RING_BUFFERS[0] or EKF_TYPES[0]:
            # a member function of a base class whose Lean name is that of one of a more derived class
            # (C++ hides a base's member by name: `EKF_IMU_buffer_t::get_oldest_index()` hides
            # `ekf_imu_buffer::get_oldest_index() const`): `Base.name`
            owner = {m["id"]: depth for depth, r in enumerate(chain) for m in r.methods}
            for depth, r in enumerate(chain):
                for m in r.methods:
                    nm = names.get(m["id"])
                    if nm is None or "." in nm or m.get("kind") == "CXXConstructorDecl":
                        continue
                    if any(names.get(x) == nm and owner[x] < depth for x in owner if x != m["id"]):
                        names[m["id"]] = "%s.%s" % (r.name, nm)
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
                    q = p["type"].get("desugaredQualType", p["type"]["qualType"]).strip()
                    if RING_BUFFERS[0] and q in ("void *", "const void *"):
                        out.append(q.replace(" *", "_ptr").replace(" ", "_"))   # (a typedef of `void *` is no name for it)
                        continue
                    out.append(name_part(q))
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
        if isinstance(cargs, tuple) and cargs[:1] == ("site",):
            # one input per call site (non-constant arguments): the member's name, then with the line
            base = member.replace(".", "_")
            if any(nm == lean_field(base, node) for _, nm, _, _, _ in self.inputs):
                base += "_%s" % cargs[1].split(":")[-2]
        elif cargs and isinstance(cargs[0], tuple) and cargs[0][:1] == ("index",):
            base = member.replace(".", "_") + "".join("_" + re.sub(r"\W+", "_", str(c)).strip("_") for c in cargs[1:]) + \
                "_at" + (str(cargs[0][1]) if cargs[0][1] else "")    # --indexed-inputs: an array
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
        b.ret_text = ret.kind == "textbuf"      # --text-results (Phase 5d)
        ref_params = {}
        if ctor:
            for ini in kids(defn):
                if ini.get("kind") == "CXXCtorInitializer" and "anyInit" in ini:
                    f = self.rec.field_by_id(ini["anyInit"]["id"])
                    if f is not None and f.category in ("ref", "owner", "wref", "wpref"):
                        e = strip_object(kids(ini)[0]) if kids(ini) else {}
                        if f.category == "wref" and ((WORLD_PTRS[0] and heap_singleton_of(u, e) is not None) or
                                                     (FRONT_ENDS[0] and accessor_target(u, e) is not None)):
                            continue        # `dal{AP::dal()}` (the heap singleton; ctor_inits evaluates the accessor), --front-ends:
                                            # `_compass(AP::compass())` (AP_Compass_Backend.cpp:14), the World object
                        if REACHABLE[0] and f.category == "wref" and isinstance(u.wref.get((self.rec.id, f.id)), tuple):
                            continue        # `public_origin(frontend->common_EKF_origin)`: a path (heap_member_refs)
                        if INS_GPS[0] and f.category == "wref" and isinstance(u.wref.get((self.rec.id, f.id)), tuple) and \
                                u.wref[(self.rec.id, f.id)][0] == "elem":
                            continue        # --ins-gps: `state(_state)`, an element of a World object's array: its index (heap_elem_refs)
                        if e.get("kind") != "DeclRefExpr" or e["referencedDecl"].get("kind") != "ParmVarDecl":
                            raise Reject(defn, "reference member `%s` bound to something other than a constructor parameter" % f.name)
                        ref_params[e["referencedDecl"]["id"]] = f.lean
        if MISSION[0] and ctor:
            # --mission: a functor parameter that only initializes a data member left out (--drop: AP_Mission's
            # `_cmd_start_fn`, `_cmd_verify_fn`, `_mission_complete_fn`, the callbacks into the vehicle's mode code)
            for p_ in params:
                pq = p_.get("type", {}).get("desugaredQualType", p_.get("type", {}).get("qualType", ""))
                if "Functor<" not in pq and "Functor<" not in TYPEDEFS.get(strip_quals(pq)[0], ""):
                    continue
                uses = [ini for ini in kids(defn) if ini.get("kind") == "CXXCtorInitializer" and
                        any(m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == p_["id"] for m in walk(ini))]
                inbody = any(m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == p_["id"] for m in walk(body or {}))
                if uses and not inbody and all(ini.get("anyInit", {}).get("id") in u.dropped for ini in uses):
                    ref_params.setdefault(p_["id"], None)
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
        lines += b.prologue
        if ctor:
            lines += self.ctor_inits(b, defn, owner, top)
        if body is not None:
            body_lines, div = b.block(kids(body))
            if not div:
                if ret.kind != "void" and not getattr(b, "survey_hit", False):
                    raise Reject(mdecl, "control may reach the end of non-void member function `%s`" % mdecl.get("name"))
                body_lines.append(b.ret_line(None))
            lines += body_lines
        else:
            lines.append(b.ret_line(None))
        hs = b.hal_storage_param()
        if hs is not None:
            ps.append(hs)
            res.outs = list(b.outs)
            if hs[3] == "mut":
                lines.insert(0, "let mut %s := %s" % (b.HS, b.HS))
        res.reads, res.writes = set(b.reads) - {"inp", "own", "sp"}, set(b.writes)
        res.uses_inp = "inp" in b.reads
        res.uses_own = "own" in b.reads
        res.uses_sp = "sp" in b.reads       # --param-save-log: the C++ path of this object, given by the caller
        res.uses_self = b.uses_self
        if ctor and top:
            res.reads -= {"s", "p"}
        if ctor and "o" in res.writes and not (PARAM_SAVE_LOG[0] and top and self.rec in u.heap):
            # (--param-save-log: a heap object's constructor that saves parameters, AP_Compass_SITL's
            # `register_compass`/`save_dev_id`: `new` passes the log, heap_ctor)
            raise Reject(mdecl, "constructor that writes outputs to the boundary")
        if "w" in res.reads | res.writes:
            if ctor and not (WORLD_PTRS[0] and (top or (INS_GPS[0] and self.rec in u.heap)) and (self.rec in u.heap or self.rec.id in u.world_self)):
                raise Reject(mdecl, "constructor that reaches other World objects (--world)")
            me = u.world_self.get(self.rec.id)
            if me is not None and me in b.wtouch and not WORLD_PTRS[0]:
                raise Reject(mdecl, "member function that reaches its own object `%s` through the World" % me)
        res.wtouch = set(b.wtouch)
        comps = (["p"] if "p" in res.writes else []) + (["s"] if "s" in res.writes else []) + \
            (["w"] if "w" in res.writes else []) + (["o"] if "o" in res.writes else []) + [pn for _, pn, _ in b.outs]
        if not comps and ret.kind == "void":
            # no effect in the model (e.g. it only saves parameters or logs): not emitted, and a
            # call of it is no statement
            res.noeffect = True
        lines = b.finish(lines, comps)
        if ctor and top:
            pre = (["let mut p : Params := {}"] if "p" in res.writes else []) + ["let mut s : State := {}"] + \
                (["let mut w := w"] if "w" in res.writes else []) + \
                (["let mut o := o"] if "o" in res.writes else [])      # --world-pointers: a heap object's constructor
        else:
            pre = (["let mut p := p"] if "p" in res.writes else []) + (["let mut s := s"] if "s" in res.writes else []) + \
                (["let mut w := w"] if "w" in res.writes else []) + (["let mut o := o"] if "o" in res.writes else [])
        res.lines = pre + lines
        res.has_params = ctor and "p" in res.writes
        binders = []
        if ctor and top and "w" in res.reads | res.writes:
            binders.append("(w : World)")       # --world-pointers: a heap object's constructor reaches the World
        if ctor and top and "o" in res.writes:
            binders.append("(o : Outputs)")     # --param-save-log: a heap object's constructor saves parameters
        if not (ctor and top):
            if "p" in res.reads | res.writes:
                binders.append("(p : Params)")
            if "s" in res.reads | res.writes:
                binders.append("(s : State)")
            if "w" in res.reads | res.writes:
                binders.append("(w : World)")
            if "o" in res.writes:
                binders.append("(o : Outputs)")
        if "r" in res.reads:
            binders.append("(r' : Refs)")
        if res.uses_inp:
            binders.append("(inp : Inputs)")
        if res.uses_own:
            binders.append("(own : Owner)")
        if res.uses_self:
            binders.append("(self' : WPtr)")    # --world-pointers: this heap object's own pointer
        if res.uses_sp:
            binders.append("(sp : String)")     # --param-save-log: the C++ path of this object (param_save)
        for i, (p_, pn, pt, ref) in enumerate(ps):
            if pn is None:
                continue
            dp = decl_params[i] if i < len(decl_params) else p_
            dflt = default_text(u, dp, self.rec.lean, b.deps) or default_text(u, p_, self.rec.lean, b.deps)
            if ref == "ptr":
                binders.append("(%s'given : Bool)" % pn)
            binders.append("(%s : %s%s)" % (pn, pt.lean, "" if dflt is None else " := " + dflt))
            if p_.get("id") in b.off_params:
                binders.append("(%s : Nat)" % Body.off_name(pn))     # --array-offsets: the pointer's offset
        rtys = (["Params"] if "p" in res.writes else []) + (["State"] if "s" in res.writes else []) + \
            (["World"] if "w" in res.writes else []) + (["Outputs"] if "o" in res.writes else [])
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
        res.deps = set(b.deps) | {("T", self.rec.id)} | ({("world",)} if "w" in res.reads | res.writes else set())
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
                if INS_GPS[0] and base is not None and e is not None and e.get("kind") == "CXXInheritedCtorInitExpr":
                    # --ins-gps: an inheriting constructor (`using AP_GPS_Backend::AP_GPS_Backend;`, AP_GPS_SITL.h:29):
                    # the base's constructor with this constructor's parameters; the class's own members zero
                    ctor = base.find_ctor(defn["type"]["qualType"])
                    if ctor is None:
                        raise Reject(ini, "inheriting constructor without the base's constructor")
                    params = [x for x in kids(defn) if x.get("kind") == "ParmVarDecl"]
                    res = self.ctor(ctor, top=False, node=ini)
                    b.deps.add(res.bid)
                    if res.uses_inp:
                        raise Reject(ini, "base constructor that reads boundary inputs")
                    objargs = b.this_call_args(res)
                    fake = [{"kind": "DeclRefExpr", "id": "inh'%s'%d" % (p_["id"], i), "referencedDecl": {"id": p_["id"], "kind": "ParmVarDecl", "name": p_.get("name", "")},
                             "type": p_["type"], "valueCategory": "lvalue"} for i, p_ in enumerate(params)]
                    pre, vals, outs = b.call_args(res.cparams, fake, ini)
                    p2, _ = b.apply_call(res.lean, res.writes, objargs, vals, outs, VOID, ini, b.object_setters())
                    lines += pre + p2
                    continue
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
            if f is None and ini["anyInit"]["id"] in self.u.sem_fields:
                continue        # --semaphores: a semaphore member is not state
            if f is None:
                raise Reject(defn, "initializer of member `%s`, which is not translated" % ini["anyInit"].get("name"))
            if e is not None and e.get("kind") == "CXXDefaultInitExpr" and f.category == "state" and deferred_init(f) is not None:
                e = deferred_init(f)    # the default member initializer, run by this constructor
            elif WORLD_PTRS[0] and f.category == "wref" and e is not None and heap_singleton_of(self.u, e) is not None:
                # `dal{AP::dal()}`: the reference is the heap singleton (a path); evaluating the initializer
                # allocates it on first use (`AP_DAL::get_singleton()`)
                while e.get("kind") == "InitListExpr" and len(kids(e)) == 1:
                    e = kids(e)[0]
                r = b.resolve_path(e)
                lines += r[0] if r is not None else []
                continue
            elif INS_GPS[0] and f.category == "wref" and isinstance(self.u.wref.get((self.rec.id, f.id)), tuple) and \
                    self.u.wref[(self.rec.id, f.id)][0] == "elem" and e is not None:
                # --ins-gps: `state(_state)`: the index of the element the parameter is bound to (heap_elem_refs)
                pe = strip_object(e)
                if pe.get("kind") != "DeclRefExpr" or pe["referencedDecl"]["id"] not in b.vars:
                    raise Reject(ini, "reference member `%s` bound to something other than a constructor parameter" % f.name)
                lines.append(b.write_path(Path(("s",), "s", [("f", f.lean + "'i")], NAT), V(b.vars[pe["referencedDecl"]["id"]][0], ATOM), ini))
                b.read.add(pe["referencedDecl"]["id"])
                continue
            elif e is None or e.get("kind") == "CXXDefaultInitExpr" or f.category in ("boundary", "ref", "owner", "wref", "wpref"):
                continue        # the field's default is its member initializer; references are not state
            if f.category == "param":
                if e.get("kind") == "CXXConstructExpr" and not kids(e):
                    continue
                raise Reject(ini, "initializer of parameter member `%s`" % f.name)
            spath = Path(("s",), "s", [("f", f.lean)], f.t)
            if getattr(f, "rb_role", None) == "buf":
                # --ring-buffers: `buffer(nullptr)`
                if not b.is_null(e):
                    raise Reject(ini, "initializer of the storage of a type-erased container other than a null pointer")
                lines += [b.write_path(spath, V("#[]", ATOM), ini), b.write_path(b.rb_paths()[1], V("false", ATOM), ini)]
                continue
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
                if outs:
                    # a constructor with non-const reference parameters (`AP_AHRS_DCM(AP_Float &kp_yaw, ...)`, AP_AHRS_DCM.h:34,
                    # from `dcm{_kp_yaw, ...}`, AP_AHRS.h:1020): it returns them after its state; each is stored back
                    names = ([b.temp()] if res.has_params else []) + [b.temp()] + [b.temp() for _ in outs]
                    lines += pre + ["let (%s) := %s" % (", ".join(names), call.text)]
                    if res.has_params:
                        lines.append(b.write_path(Path(("p",), "p", [("f", f.lean)], None), V(names[0], ATOM), ini))
                    k0 = 1 if res.has_params else 0
                    lines.append(b.write_path(spath, V(names[k0], ATOM), ini))
                    for op_, t_ in zip(outs, names[k0 + 1:]):
                        if op_ is not None:
                            lines.append(b.out_line(op_, V(t_, ATOM), ini))
                    continue
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
            if INS_GPS[0] and e.get("kind") == "CXXConstructExpr" and f.t.kind == "array" and not kids(e) and f.t.elem.kind == "record" \
                    and not zeroing_default_ctor(self.u, f.t.elem) and f.t.elem.info.find_ctor("void ()") is not None:
                # --ins-gps: `AP_GPS::Params params[GPS_MAX_RECEIVERS]` (AP_GPS.h), each element default-constructed by its
                # class's constructor (`AP_Param::setup_object_defaults(this, var_info)`): the same value n times
                ector = f.t.elem.info.find_ctor("void ()")
                sub = self.u.context(f.t.elem.info, ini)
                b.deps.add(("T", f.t.elem.info.id))
                res = sub.ctor(ector, top=True, node=ini)
                b.deps.add(res.bid)
                if res.uses_inp or res.has_params or "w" in res.reads | res.writes or res.cparams:
                    raise Reject(ini, "array member whose elements' constructor has parameters or reaches the World or the boundary")
                lines.append(b.write_path(spath, V("(Array.replicate %d %s.%s)" % (f.t.n, f.t.elem.info.lean, res.lean), ATOM), ini))
                continue
            if INS_GPS[0] and e.get("kind") == "CXXConstructExpr" and f.t.kind == "array" and not kids(e) and zeroing_default_ctor(self.u, f.t.elem):
                continue        # --ins-gps: `LowPassFilter2pVector3f _accel_filter[3]` (AP_InertialSensor.h:590), elements whose
                                # default constructor zeroes them (`memset(&_params, 0, ...)`, `x = T()`): the field's default
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
        if any(m["id"] in getattr(x, "rb", {}).get("acc", {}) for x in self.rec.chain()):
            return              # --ring-buffers: an element accessor (`get_offset`), its calls are element indices
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

# ---------------------------------------------------------------------------------------------
# --gotos (README.md, "Phase 2b"): before translation, a function body with forward `goto`s,
# `continue` in a `do` loop, or a `switch` case that falls through into a non-empty case is
# rewritten, on clang's AST, into one without them, with the same behavior:
# - a case that falls through gets the statements of the cases it falls into appended (copies);
# - `continue` in a `do` loop is `goto` to a label at the end of the loop's body;
# - for each label L with forward `goto`s: a flag `goto'L` (false at the start of the innermost
#   block, `if` or `switch` holding L and its gotos); the statements from the first that holds a
#   goto to the one before L's are a one-iteration loop (`do { ... } while (0)`), each `goto L` is
#   `goto'L = true; break;` (and `if (goto'L) break;` after each loop or switch between it and
#   that loop); a `break`/`continue` in it for an enclosing loop leaves it the same way and is
#   repeated after it; the statement holding L is "entered" at L when the flag is set: in a block
#   the statements before L's are skipped (`if (!goto'L) ...`), in an `if` the branch holding L is
#   taken (the condition is not evaluated), in a `switch` the statements from L to the case's
#   final `break` run after the switch (`if (goto'L) { ... }`, the switch skipped); a goto from one
#   branch of an `if` into the other evaluates the condition once (`cond'L`).
# Rejected: backward gotos, gotos into a loop body, a label in a `switch` case whose statements from
# the label do not end in `break`, a fallthrough into statements with labels or declarations.

class GotoReject(Exception):
    def __init__(self, node, construct):
        self.node, self.construct = node, construct


GOTO_IDS = [0]
LOOPS = ("ForStmt", "WhileStmt", "DoStmt", "CXXForRangeStmt")


class GotoRewriter:
    def __init__(self, u, fn):
        self.u, self.fn = u, fn
        self.near = fn

    def nid(self):
        GOTO_IDS[0] += 1
        return "0xc2l%x" % GOTO_IDS[0]

    def mk(self, kind, **kw):
        n = {"id": self.nid(), "kind": kind, "range": self.near.get("range"), "loc": self.near.get("loc")}
        n.update(kw)
        return n

    def bool_lit(self, v):
        return self.mk("CXXBoolLiteralExpr", type={"qualType": "bool"}, valueCategory="prvalue", value=v)

    def var(self, name, init):
        return self.mk("VarDecl", name=name, type={"qualType": "bool"}, init="c", inner=[init])

    def decl_stmt(self, vd):
        return self.mk("DeclStmt", inner=[vd])

    def ref(self, vd):
        return self.mk("DeclRefExpr", type={"qualType": "bool"}, valueCategory="lvalue",
                       referencedDecl={"id": vd["id"], "kind": "VarDecl", "name": vd["name"], "type": {"qualType": "bool"}})

    def rv(self, vd):
        return self.mk("ImplicitCastExpr", type={"qualType": "bool"}, valueCategory="prvalue", castKind="LValueToRValue", inner=[self.ref(vd)])

    def assign(self, vd, v):
        return self.mk("BinaryOperator", type={"qualType": "bool"}, valueCategory="lvalue", opcode="=", inner=[self.ref(vd), self.bool_lit(v)])

    def assign_expr(self, vd, e):
        return self.mk("BinaryOperator", type={"qualType": "bool"}, valueCategory="lvalue", opcode="=", inner=[self.ref(vd), e])

    def not_(self, e):
        return self.mk("UnaryOperator", type={"qualType": "bool"}, valueCategory="prvalue", opcode="!", isPostfix=False, inner=[e])

    def binop(self, op, a, b):
        return self.mk("BinaryOperator", type={"qualType": "bool"}, valueCategory="prvalue", opcode=op, inner=[a, b])

    def if_(self, c, then, els=None):
        n = self.mk("IfStmt", inner=[c, then] + ([els] if els is not None else []))
        if els is not None:
            n["hasElse"] = True
        return n

    def block(self, stmts):
        return self.mk("CompoundStmt", inner=list(stmts))

    def brk(self):
        return self.mk("BreakStmt")

    def cont(self):
        return self.mk("ContinueStmt")

    def once(self, stmts):
        return self.mk("DoStmt", inner=[self.block(stmts), self.mk("IntegerLiteral", type={"qualType": "int"}, valueCategory="prvalue", value="0")])

    # -- tree helpers

    @staticmethod
    def contains(n, pred):
        return any(pred(m) for m in walk(n))

    def path_to(self, root, target):
        """The list of nodes from root down to target (inclusive), or None."""
        if root is target:
            return [root]
        for c in kids(root):
            if isinstance(c, dict):
                p = self.path_to(c, target)
                if p is not None:
                    return [root] + p
        return None

    def copy(self, n, remap=None):
        """A deep copy of a statement with fresh ids (declarations in it are rejected)."""
        if isinstance(n, list):
            return [self.copy(x, remap) for x in n]
        if not isinstance(n, dict):
            return n
        if n.get("kind") in ("VarDecl", "LabelStmt"):
            raise GotoReject(n, "`switch` case that falls through into statements that declare variables or labels")
        out = dict(n)
        if "id" in n:
            out["id"] = self.nid()
        if "inner" in n:
            out["inner"] = [self.copy(c, remap) for c in n["inner"]]
        return out

    # -- step 0: fallthrough and continue in `do`

    def ends_in_jump(self, stmts):
        if not stmts:
            return False
        s = stmts[-1]
        k = s.get("kind")
        if k in ("BreakStmt", "ReturnStmt", "ContinueStmt", "GotoStmt"):
            return True
        if k == "CompoundStmt":
            return self.ends_in_jump(kids(s))
        if k == "IfStmt" and s.get("hasElse"):
            return self.ends_in_jump([kids(s)[1]]) and self.ends_in_jump([kids(s)[2]])
        if k in ("CaseStmt", "DefaultStmt", "LabelStmt", "AttributedStmt"):
            return self.ends_in_jump([kids(s)[-1]])
        return False

    def strip_fallthrough(self, n):
        for m in walk(n):
            for i, c in enumerate(kids(m)):
                if isinstance(c, dict) and c.get("kind") == "AttributedStmt" and \
                        any(a.get("kind") == "FallThroughAttr" for a in kids(c)) :
                    m["inner"][i] = self.mk("NullStmt")

    def segments(self, body):
        """A switch body's children split into segments: (labels list of the nested case labels
        (outermost first), statements)."""
        segs = []
        for c in kids(body):
            if c.get("kind") in ("CaseStmt", "DefaultStmt"):
                labels, s = [c], kids(c)[-1]
                while s.get("kind") in ("CaseStmt", "DefaultStmt"):
                    labels.append(s)
                    s = kids(s)[-1]
                segs.append([labels, [s]])
            elif segs:
                segs[-1][1].append(c)
        return segs

    def fix_fallthrough(self, sw):
        body = kids(sw)[-1]
        if body.get("kind") != "CompoundStmt":
            return
        segs = self.segments(body)
        changed = False
        for i, (labels, stmts) in enumerate(segs):
            real = [x for x in stmts if x.get("kind") != "NullStmt"]
            if not real or self.ends_in_jump(real) or i + 1 == len(segs):
                continue
            extra = []
            j = i + 1
            while j < len(segs):
                extra += [self.copy(x) for x in segs[j][1]]
                if self.ends_in_jump([x for x in segs[j][1] if x.get("kind") != "NullStmt"]):
                    break
                j += 1
            segs[i][1] = stmts + extra
            changed = True
        if not changed:
            return
        inner = []
        for labels, stmts in segs:
            innermost = labels[-1]
            innermost["inner"] = kids(innermost)[:-1] + [stmts[0]]
            inner.append(labels[0])
            inner += stmts[1:]
        body["inner"] = inner

    def own_continues(self, loop_body):
        out = []

        def visit(m):
            for c in kids(m):
                if not isinstance(c, dict):
                    continue
                if c.get("kind") == "ContinueStmt":
                    out.append((m, c))
                elif c.get("kind") not in LOOPS:
                    visit(c)
        visit(loop_body)
        return out

    def fix_do_continue(self, do):
        body = kids(do)[0]
        conts = self.own_continues(body)
        if not conts:
            return
        if body.get("kind") != "CompoundStmt":
            body = self.block([body])
            do["inner"][0] = body
        self.near = do
        lab = self.mk("LabelStmt", name="cont'%x" % GOTO_IDS[0], inner=[self.mk("NullStmt")])
        lab["declId"] = lab["id"] + "d"
        body["inner"] = kids(body) + [lab]
        for parent, c in conts:
            g = self.mk("GotoStmt", targetLabelDeclId=lab["declId"])
            parent["inner"][[x is c for x in kids(parent)].index(True)] = g

    # -- step 1: one label

    def gotos_to(self, root, label_id):
        return [m for m in walk(root) if m.get("kind") == "GotoStmt" and m.get("targetLabelDeclId") == label_id]

    def replace_in_parent(self, parent, old, new_list):
        """Replace child old of parent by the statements new_list (spliced into a block, else wrapped)."""
        i = [x is old for x in kids(parent)].index(True)
        if parent.get("kind") == "CompoundStmt":
            parent["inner"] = kids(parent)[:i] + new_list + kids(parent)[i + 1:]
        else:
            parent["inner"][i] = new_list[0] if len(new_list) == 1 else self.block(new_list)

    def jump_out(self, region, flag, node, _unused):
        """Replace jump statement node (in region) by `flag = true; break;` and add `if (flag)
        break;` after each loop or switch between it and region."""
        path = self.path_to(region, node)
        parent = path[-2]
        self.replace_in_parent(parent, node, [self.assign(flag, True), self.brk()])
        # the loops and switches the break must leave, innermost first
        for depth in range(len(path) - 2, 0, -1):
            a = path[depth]
            if a.get("kind") in LOOPS + ("SwitchStmt",):
                ap = path[depth - 1]
                self.replace_in_parent(ap, a, [a, self.if_(self.rv(flag), self.brk())])

    def region(self, stmts, flag, label_id):
        """The one-iteration loop around stmts, the gotos to label_id in them leaving it with flag
        set; returns (statements before it, the loop, statements after it)."""
        hoisted, body = [], []
        for s in stmts:
            if s.get("kind") == "DeclStmt" and all(not kids(d) for d in kids(s)):
                hoisted.append(s)       # (a declaration without initializer: kept outside, for the code after)
            elif s.get("kind") == "DeclStmt":
                raise GotoReject(s, "declaration with an initializer between a `goto` and its label")
            else:
                body.append(s)
        loop = self.once(body)
        gotos = self.gotos_to(loop, label_id)
        after = []
        # break/continue in the region for an enclosing loop: leave the region, then repeat it
        for kind in ("BreakStmt", "ContinueStmt"):
            crossing = []

            def visit(m, in_loop, in_switch):
                for c in kids(m):
                    if not isinstance(c, dict):
                        continue
                    k = c.get("kind")
                    if k == kind and not in_loop and not (kind == "BreakStmt" and in_switch):
                        crossing.append(c)
                    visit(c, in_loop or k in LOOPS, in_switch or k == "SwitchStmt")
            visit(kids(loop)[0], False, False)
            if crossing:
                f = self.var("%s'%x" % ("break" if kind == "BreakStmt" else "continue", GOTO_IDS[0] + 1), self.bool_lit(False))
                hoisted.append(self.decl_stmt(f))
                for c in crossing:
                    self.jump_out(loop, f, c, None)
                after.append(self.if_(self.rv(f), self.brk() if kind == "BreakStmt" else self.cont()))
        for g in gotos:
            self.jump_out(loop, flag, g, None)
        return hoisted, loop, after

    def enter(self, x, flag, label, entered):
        """x (a statement holding label) transformed: it handles the gotos to label inside it and,
        if entered, starts at label when flag is set. Returns a list of statements."""
        k = x.get("kind")
        lid = label["declId"]
        if x is label:
            return [kids(x)[0]]
        if k == "CompoundStmt":
            ch = kids(x)
            ki = next(i for i, c in enumerate(ch) if self.path_to(c, label) is not None)
            for c in ch[ki + 1:]:
                if self.gotos_to(c, lid):
                    raise GotoReject(self.gotos_to(c, lid)[0], "backward `goto`")
            first = next((i for i, c in enumerate(ch[:ki]) if self.gotos_to(c, lid)), None)
            out = []
            pre_stmts = ch[:ki] if first is None else ch[:first]
            for c in pre_stmts:
                if entered and c.get("kind") != "DeclStmt" and c.get("kind") != "NullStmt":
                    out.append(self.if_(self.not_(self.rv(flag)), c))
                else:
                    out.append(c)
            if first is not None:
                hoisted, loop, after = self.region(ch[first:ki], flag, lid)
                out += hoisted
                out.append(self.if_(self.not_(self.rv(flag)), loop) if entered else loop)
                out += after
            out += self.enter(ch[ki], flag, label, entered or first is not None)
            out += ch[ki + 1:]
            x["inner"] = out
            return [x]
        if k == "IfStmt":
            if x.get("hasInit") or x.get("hasVar"):
                raise GotoReject(x, "`goto` into an `if` with an initializer or a condition variable")
            cond, then = kids(x)[0], kids(x)[1]
            els = kids(x)[2] if x.get("hasElse") else None
            in_then = self.path_to(then, label) is not None
            b, o = (then, els) if in_then else (els, then)
            o_gotos = o is not None and bool(self.gotos_to(o, lid))
            if not o_gotos:
                if in_then:
                    c = self.binop("||", self.rv(flag), cond) if entered else cond
                else:
                    c = self.binop("&&", self.not_(self.rv(flag)), cond) if entered else cond
                bb = self.enter_stmt(b, flag, label, entered)
                x["inner"] = [c, bb] + ([o] if o is not None else []) if in_then else [c, o, bb]
                if not in_then:
                    x["hasElse"] = True
                return [x]
            # a goto from one branch into the other: the condition once, then each branch
            cv = self.var("cond'%x" % (GOTO_IDS[0] + 1), (self.binop("||", self.rv(flag), cond) if in_then else self.binop("&&", self.not_(self.rv(flag)), cond)) if entered else cond)
            hoisted, loop, after = self.region([o], flag, lid)
            o_cond = self.not_(self.rv(cv)) if in_then else self.rv(cv)
            b_cond = self.binop("||", self.rv(flag), self.rv(cv) if in_then else self.not_(self.rv(cv)))
            return [self.decl_stmt(cv)] + hoisted + [self.if_(o_cond, self.block([loop] + after))] + \
                [self.if_(b_cond, self.enter_stmt(b, flag, label, True))]
        if k == "SwitchStmt":
            body = kids(x)[-1]
            if body.get("kind") != "CompoundStmt" or not any(c is label for c in kids(body)):
                raise GotoReject(label, "label inside a `switch` other than among the statements of a case")
            ch = kids(body)
            li = [c is label for c in ch].index(True)
            end = li + 1
            while end < len(ch) and ch[end].get("kind") not in ("CaseStmt", "DefaultStmt"):
                end += 1
            tail = [kids(label)[0]] + ch[li + 1:end]
            if not tail or tail[-1].get("kind") != "BreakStmt":
                raise GotoReject(label, "label in a `switch` case whose statements from the label do not end in `break`")
            tail = tail[:-1]
            for s in tail:
                for m in walk(s):
                    if m.get("kind") == "BreakStmt" and not any(a.get("kind") in LOOPS + ("SwitchStmt",) for a in self.path_to(s, m)[:-1]):
                        raise GotoReject(m, "`break` in the statements of a `switch` label other than the last")
            self.near = label
            body["inner"] = ch[:li] + [self.assign(flag, True), self.brk()] + ch[end:]
            for g in self.gotos_to(x, lid):
                self.jump_out(x, flag, g, None)
            sw = self.if_(self.not_(self.rv(flag)), x) if entered else x
            return [sw, self.if_(self.rv(flag), self.block(tail))]
        if k == "LabelStmt":
            return self.label_wrap(x, flag, label, entered)
        if k in LOOPS:
            raise GotoReject(label, "`goto` into a loop body")
        raise GotoReject(label, "`goto` to a label inside a `%s`" % k)

    def label_wrap(self, x, flag, label, entered):
        inner = self.enter_stmt(kids(x)[0], flag, label, entered)
        x["inner"] = [inner]
        return [x]

    def enter_stmt(self, s, flag, label, entered):
        out = self.enter(s, flag, label, entered)
        return out[0] if len(out) == 1 else self.block(out)

    def eliminate(self, label):
        lid = label["declId"]
        gotos = self.gotos_to(self.fn, lid)
        if not gotos:
            # a label without gotos: its statement
            path = self.path_to(self.fn, label)
            self.replace_in_parent(path[-2], label, [kids(label)[0]])
            return
        # the innermost block, `if` or `switch` holding the label and every goto to it
        paths = [self.path_to(self.fn, x) for x in gotos + [label]]
        lca = None
        for depth in range(min(len(p) for p in paths)):
            if all(p[depth] is paths[0][depth] for p in paths):
                lca = paths[0][depth]
            else:
                break
        lpath = paths[-1]
        i = lpath.index(lca)
        if lca.get("kind") == "CompoundStmt" and i > 0 and lpath[i - 1].get("kind") == "SwitchStmt":
            i -= 1                      # gotos between the cases of a switch: the switch holds them
            lca = lpath[i]
        while lca.get("kind") not in ("CompoundStmt", "IfStmt", "SwitchStmt"):
            if lca.get("kind") in LOOPS:
                raise GotoReject(gotos[0], "backward `goto` or `goto` into a loop body")
            i -= 1
            if i < 0:
                raise GotoReject(gotos[0], "`goto` outside a function body")
            lca = lpath[i]
        self.near = label
        flag = self.var("goto'%s" % label.get("name", "L"), self.bool_lit(False))
        parent = lpath[i - 1] if i > 0 else None
        out = self.enter(lca, flag, label, False)
        new = [self.decl_stmt(flag)] + out
        if lca.get("kind") == "CompoundStmt" and len(out) == 1 and out[0] is lca:
            lca["inner"] = [self.decl_stmt(flag)] + kids(lca)
        elif parent is None:
            raise GotoReject(label, "`goto` whose label and gotos are not inside a block")
        else:
            self.replace_in_parent(parent, lca, [self.block(new)])

    def run(self):
        body = next((c for c in kids(self.fn) if c.get("kind") == "CompoundStmt"), None)
        if body is None:
            return False
        if not any(m.get("kind") in ("GotoStmt", "SwitchStmt", "DoStmt") for m in walk(body)):
            return False
        before = json.dumps(body, sort_keys=True)
        self.strip_fallthrough(body)
        for m in list(walk(body)):
            if m.get("kind") == "SwitchStmt":
                self.fix_fallthrough(m)
        for m in list(walk(body)):
            if m.get("kind") == "DoStmt":
                self.fix_do_continue(m)
        while True:
            labels = [m for m in walk(body) if m.get("kind") == "LabelStmt"]
            if not labels:
                break
            # innermost first: a label whose statements hold no other label
            lab = next((l for l in labels if not any(m.get("kind") == "LabelStmt" for m in walk(kids(l)[0]))), labels[0])
            self.eliminate(lab)
        return json.dumps(body, sort_keys=True) != before


class NullFold:
    """--null-member (with --mavlink): pointer data members that are always null (nothing in the reduced
    vehicle assigns them: `mavlink_status_t::signing` and `signing_streams` with AP_MAVLINK_SIGNING_ENABLED 0,
    GCS_Signing.cpp compiled out). Before translation, in every function body that reads one, the read is
    the null pointer and what it decides is folded on clang's AST:
    - `p` as a condition is false, `p == NULL` true, `p != NULL` false;
    - `!c`, `a && b`, `a || b` and `c ? x : y` with a constant operand (an operand dropped by the folding
      must not have effects: no calls, assignments, increments);
    - a local initialized with a constant (a `bool`, or an integer literal) and assigned nowhere else is
      that constant at each read;
    - a call `f(..., null, ...)` of a function whose first statement is `if (q == NULL) return <literal>;`
      for the parameter q the null pointer is passed for (`mavlink_signature_check(status->signing, ...)`,
      mavlink_helpers.h:186) is the literal, if no other argument has effects;
    - `if (c)` with a constant condition is the branch taken; this is repeated until nothing changes.
    A read through the null pointer (`status->signing->flags`) that the folding leaves in reachable code
    is rejected by the translator (it is no expression of the subset); an assignment to the member is
    rejected here."""

    def __init__(self, u):
        self.u = u
        self.null_ids = set()
        for d in u.ids.values():
            if d.get("kind") == "FieldDecl" and "name" in d:
                rec = u.parent.get(d["id"])
                rname = (rec or {}).get("name")
                if rname and "%s::%s" % (rname, d["name"]) in NULL_MEMBERS:
                    self.null_ids.add(d["id"])

    def mk(self, kind, near, **kw):
        GOTO_IDS[0] += 1
        n = {"id": "0xc2n%x" % GOTO_IDS[0], "kind": kind, "range": near.get("range"), "loc": near.get("loc")}
        n.update(kw)
        return n

    def bool_lit(self, v, near):
        n = self.mk("CXXBoolLiteralExpr", near, type={"qualType": "bool"}, valueCategory="prvalue", value=v)
        n["folded"] = v
        return n

    @staticmethod
    def is_null(n):
        n = strip_parens(n)
        while n.get("kind") == "ImplicitCastExpr" and n.get("castKind") in ("NullToPointer", "NoOp", "LValueToRValue", "BitCast") and kids(n):
            n = strip_parens(kids(n)[0])
        return n.get("kind") in ("CXXNullPtrLiteralExpr", "GNUNullExpr") or n.get("nullmember") or \
            (n.get("kind") == "IntegerLiteral" and n.get("value") == "0" and False)

    @staticmethod
    def const_of(n):
        """True/False for a folded boolean constant or a boolean literal (parentheses and casts to bool
        stripped), else None."""
        n = strip_parens(n)
        while n.get("kind") == "ImplicitCastExpr" and n.get("castKind") in ("NoOp", "LValueToRValue", "IntegralToBoolean") and kids(n):
            n = strip_parens(kids(n)[0])
        if "folded" in n:
            return n["folded"]
        if n.get("kind") == "CXXBoolLiteralExpr":
            return bool(n.get("value"))
        return None

    @staticmethod
    def int_of(n):
        n = strip_parens(n)
        while n.get("kind") == "ImplicitCastExpr" and n.get("castKind") in ("NoOp", "LValueToRValue", "IntegralCast") and kids(n):
            n = strip_parens(kids(n)[0])
        if n.get("kind") == "IntegerLiteral":
            return int(n["value"])
        return None

    @staticmethod
    def pure(n):
        for m in walk(n):
            k = m.get("kind")
            if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr", "CompoundAssignOperator") or \
                    (k == "BinaryOperator" and m.get("opcode") == "=") or \
                    (k == "UnaryOperator" and m.get("opcode") in ("++", "--")):
                return False
        return True

    def run(self, fn):
        body = next((c for c in kids(fn) if c.get("kind") == "CompoundStmt"), None)
        if body is None or not any(m.get("kind") == "MemberExpr" and m.get("referencedMemberDecl") in self.null_ids for m in walk(body)):
            return False
        self.fn = fn
        for _ in range(20):
            self.changed = False
            self.consts = self.local_consts(body)
            fn["inner"] = [self.x(c) for c in kids(fn)]
            body = next(c for c in kids(fn) if c.get("kind") == "CompoundStmt")
            if not self.changed:
                break
        return True

    def local_consts(self, body):
        """{VarDecl id: its constant initializer} for the locals of body assigned nowhere but at their
        declaration, whose initializer is a folded constant or an integer literal."""
        decls = {}
        for m in walk(body):
            if m.get("kind") == "VarDecl" and kids(m) and m.get("init") == "c":
                ini = kids(m)[0]
                if self.const_of(ini) is not None or (self.int_of(ini) is not None and m["type"]["qualType"] != "bool"):
                    decls[m["id"]] = ini
        for m in walk(body):
            k = m.get("kind")
            tgt = None
            if (k == "BinaryOperator" and m.get("opcode") == "=") or k == "CompoundAssignOperator" or \
                    (k == "UnaryOperator" and m.get("opcode") in ("++", "--", "&")):
                tgt = strip_casts(kids(m)[0])
            if tgt is not None and tgt.get("kind") == "DeclRefExpr" and tgt["referencedDecl"]["id"] in decls:
                ini = decls[tgt["referencedDecl"]["id"]]
                if k == "BinaryOperator" and self.const_of(ini) is not None and self.const_of(kids(m)[1]) == self.const_of(ini):
                    continue        # `sig_ok = true;` of a local that starts true: it stays that constant
                decls.pop(tgt["referencedDecl"]["id"], None)
        return decls

    def callee_null_return(self, call):
        """The literal f returns when the null pointer is passed for its parameter q (the first statement of
        f is `if (q == NULL) return <literal>;`), if call passes the null pointer for q, else None."""
        c = strip_casts(kids(call)[0])
        if c.get("kind") != "DeclRefExpr":
            return None
        d = self.u.decl(c["referencedDecl"]["id"])
        if d is None:
            return None
        defn = d if any(x.get("kind") == "CompoundStmt" for x in kids(d)) else next(
            (x for x in self.u.ids.values() if x.get("kind") == "FunctionDecl" and x.get("mangledName") == d.get("mangledName")
             and any(y.get("kind") == "CompoundStmt" for y in kids(x))), None)
        if defn is None:
            return None
        params = [p["id"] for p in kids(defn) if p.get("kind") == "ParmVarDecl"]
        body = next(x for x in kids(defn) if x.get("kind") == "CompoundStmt")
        if not kids(body) or kids(body)[0].get("kind") != "IfStmt" or kids(body)[0].get("hasElse"):
            return None
        cond, then = kids(kids(body)[0])[0], kids(kids(body)[0])[1]
        cond = strip_parens(cond)
        q = None
        if cond.get("kind") == "BinaryOperator" and cond.get("opcode") == "==":
            a, b = kids(cond)
            if self.is_null(b) and strip_casts(a).get("kind") == "DeclRefExpr":
                q = strip_casts(a)["referencedDecl"]["id"]
        elif cond.get("kind") == "UnaryOperator" and cond.get("opcode") == "!":
            a = strip_casts(kids(cond)[0])
            while a.get("kind") == "ImplicitCastExpr" and a.get("castKind") == "PointerToBoolean":
                a = strip_casts(kids(a)[0])
            if a.get("kind") == "DeclRefExpr":
                q = a["referencedDecl"]["id"]
        if q not in params:
            return None
        if then.get("kind") == "CompoundStmt" and len(kids(then)) == 1:
            then = kids(then)[0]
        if then.get("kind") != "ReturnStmt" or not kids(then):
            return None
        rv = strip_parens(kids(then)[0])
        if rv.get("kind") != "CXXBoolLiteralExpr":
            return None
        args = kids(call)[1:]
        i = params.index(q)
        if i >= len(args) or not self.is_null(args[i]) or not all(self.pure(a) for a in args):
            return None
        return bool(rv.get("value"))

    def x(self, n):
        """n with the null member's reads replaced and the constants folded (children first)."""
        if not isinstance(n, dict):
            return n
        k = n.get("kind")
        if k == "BinaryOperator" and n.get("opcode") == "=" and strip_casts(kids(n)[0]).get("kind") == "MemberExpr" and \
                strip_casts(kids(n)[0]).get("referencedMemberDecl") in self.null_ids:
            self.u.goto_rejects[self.fn["id"]] = Reject(n, "assignment to `%s`, a --null-member" % strip_casts(kids(n)[0]).get("name"))
            return n
        if k == "MemberExpr" and n.get("referencedMemberDecl") in self.null_ids:
            m = self.mk("CXXNullPtrLiteralExpr", n, type=n.get("type"), valueCategory="prvalue")
            m["nullmember"] = n.get("name")
            self.changed = True
            return m
        if "inner" in n:
            n["inner"] = [self.x(c) for c in kids(n)]
        if k == "ImplicitCastExpr" and n.get("castKind") == "PointerToBoolean" and self.is_null(kids(n)[0]):
            self.changed = True
            return self.bool_lit(False, n)
        if k == "DeclRefExpr" and n["referencedDecl"]["id"] in self.consts:
            ini = self.consts[n["referencedDecl"]["id"]]
            self.changed = True
            if self.const_of(ini) is not None:
                return self.bool_lit(self.const_of(ini), n)
            return copy.deepcopy(ini)
        if k == "ImplicitCastExpr" and n.get("castKind") == "LValueToRValue" and kids(n) and \
                (strip_parens(kids(n)[0]).get("kind") == "CXXBoolLiteralExpr" or self.int_of(kids(n)[0]) is not None):
            return kids(n)[0]
        if k == "UnaryOperator" and n.get("opcode") == "!" and self.const_of(kids(n)[0]) is not None:
            self.changed = True
            return self.bool_lit(not self.const_of(kids(n)[0]), n)
        if k == "BinaryOperator" and n.get("opcode") in ("==", "!=") and self.is_null(kids(n)[0]) and self.is_null(kids(n)[1]):
            self.changed = True
            return self.bool_lit(n["opcode"] == "==", n)
        if k == "BinaryOperator" and n.get("opcode") in ("==", "!=", "<", ">", "<=", ">=") and \
                self.int_of(kids(n)[0]) is not None and self.int_of(kids(n)[1]) is not None:
            a, b = self.int_of(kids(n)[0]), self.int_of(kids(n)[1])
            self.changed = True
            return self.bool_lit({"==": a == b, "!=": a != b, "<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b}[n["opcode"]], n)
        if k == "BinaryOperator" and n.get("opcode") in ("&&", "||"):
            a, b = kids(n)
            ca, cb = self.const_of(a), self.const_of(b)
            absorb = n["opcode"] == "||"        # the value that decides the operator
            if ca is not None:
                self.changed = True
                return self.bool_lit(absorb, n) if ca == absorb else self.as_bool(b)
            if cb is not None and self.pure(a):
                self.changed = True
                return self.bool_lit(absorb, n) if cb == absorb else self.as_bool(a)
        if k == "ConditionalOperator" and self.const_of(kids(n)[0]) is not None:
            self.changed = True
            return kids(n)[1] if self.const_of(kids(n)[0]) else kids(n)[2]
        if k == "ParenExpr" and self.const_of(kids(n)[0]) is not None:
            return kids(n)[0]
        if k == "CallExpr":
            v = self.callee_null_return(n)
            if v is not None:
                self.changed = True
                return self.bool_lit(v, n)
        if k == "IfStmt" and not n.get("hasInit") and not n.get("hasVar") and self.const_of(kids(n)[0]) is not None:
            self.changed = True
            if self.const_of(kids(n)[0]):
                return kids(n)[1]
            if n.get("hasElse"):
                return kids(n)[2]
            return self.mk("NullStmt", n)
        return n

    def as_bool(self, e):
        """e as the operand of `&&`/`||` that is left: its value converted to bool (it already is one)."""
        return e


def merge_late_inits(u):
    """--mavlink: `uint8_t *ck; ... ck = buf + header_len + length;` (mavlink_msg_to_send_buffer,
    mavlink_helpers.h:533-544): a local pointer declared without initializer, whose first use in its block
    is an assignment statement and which is assigned nowhere else, is declared there with that initializer
    (the same program: nothing reads it before)."""
    def refs(n, vid):
        return any(m.get("kind") == "DeclRefExpr" and m.get("referencedDecl", {}).get("id") == vid for m in walk(n))

    for fn in list(u.ids.values()):
        if fn.get("kind") not in ("FunctionDecl", "CXXMethodDecl") or not any(c.get("kind") == "CompoundStmt" for c in kids(fn)):
            continue
        changed = False
        for blk in [m for m in walk(fn) if m.get("kind") == "CompoundStmt"]:
            st = kids(blk)
            i = 0
            while i < len(st):
                d = st[i]
                vd = kids(d)[0] if d.get("kind") == "DeclStmt" and len(kids(d)) == 1 else None
                if vd is None or vd.get("kind") != "VarDecl" or non_attr(kids(vd)) or not vd["type"]["qualType"].rstrip().endswith("*"):
                    i += 1
                    continue
                j = next((j for j in range(i + 1, len(st)) if refs(st[j], vd["id"])), None)
                a = st[j] if j is not None else None
                ok = a is not None and a.get("kind") == "BinaryOperator" and a.get("opcode") == "=" and \
                    strip_parens(kids(a)[0]).get("kind") == "DeclRefExpr" and strip_parens(kids(a)[0])["referencedDecl"]["id"] == vd["id"] and \
                    not refs(kids(a)[1], vd["id"])
                if ok:
                    writes = [m for m in walk(fn) if (m.get("kind") == "BinaryOperator" and m.get("opcode") == "=" or
                                                       m.get("kind") == "CompoundAssignOperator" or
                                                       (m.get("kind") == "UnaryOperator" and m.get("opcode") in ("++", "--", "&")))
                              and strip_casts(kids(m)[0]).get("kind") == "DeclRefExpr" and strip_casts(kids(m)[0])["referencedDecl"]["id"] == vd["id"]]
                    ok = len(writes) == 1
                if not ok:
                    i += 1
                    continue
                vd["inner"] = [kids(a)[1]]
                vd["init"] = "c"
                st[j] = d
                del st[i]
                changed = True
            blk["inner"] = st
        if changed:
            u.index(fn, u.parent.get(fn["id"]))


def fold_null_members(u):
    """--null-member: NullFold on every function body that reads a null member."""
    nf = NullFold(u)
    if not nf.null_ids:
        return
    for d in list(u.ids.values()):
        if d.get("kind") in ("FunctionDecl", "CXXMethodDecl") and any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            if nf.run(d):
                u.index(d, u.parent.get(d["id"]))


def rewrite_gotos(u):
    """--gotos: rewrite every function body of the unit that needs it (GotoRewriter); a function
    the rewrite rejects is rejected when it is translated (u.goto_rejects)."""
    for d in list(u.ids.values()):
        if d.get("kind") not in ("FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl"):
            continue
        if not any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            continue
        rw = GotoRewriter(u, d)
        try:
            changed = rw.run()
        except GotoReject as e:
            u.goto_rejects[d["id"]] = Reject(e.node, e.construct)
            continue
        if changed:
            u.index(d, u.parent.get(d["id"]))


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
        self.world = []         # --world: [{name, decl, rec}] the file-scope objects, in definition order
        self.world_ids = {}     # VarDecl id -> World field name
        self.wref = {}          # (record id of the object's class, field id) -> World field name it refers to
        self.world_self = {}    # record id -> the World field of the one object of that class
        self.singleton_ptrs = {}    # --world: static `C *_singleton` member id -> RecordInfo of C
        self.accessors = {}     # --world: id -> the accessor functions (`AP::rtc()`, `get_singleton()`), not translated
        self.heap = []          # --world-pointers: the classes of the objects `new` creates (heap slots of the World), in AST order
        self.heap_placement = set()     # --world-pointers: ids of heap classes constructed by placement new into --heap-alloc memory
        self.heap_out = set()   # --reachable: heap fields whose objects write boundary outputs (`heap'C'o`)
        self.heap_inp = set()   # --reachable, --front-ends: heap fields whose objects read boundary inputs (`heap'C'inp`)
        self.heap_ptr_used = set()  # --front-ends: the heap_ptr World fields the translation reads or writes
        self.heap_ptr = {}      # --world-pointers: static pointer member id (`Store::_singleton` of a class without a file-scope object) -> World field
        self.sem_fields = set() # --semaphores: ids of the data members that are semaphores (not state)
        self.dispatch = {}      # --world-pointers: key -> dispatch helper {name, lines, deps, wtouch, ...}
        self.wptr_index = False # --world-pointers: `WPtr.index` is used
        self.funcs = []         # --world-pointers: the (class, method decl) pairs bound into `Functor<void>`s (FUNCTOR_BIND), in AST order
        self.wfun_call = None   # --world-pointers: the block of `WFun.call` once a functor is called
        self.refptr_fields = set()  # --member-pointers: ids of reference members of unnamed structs, modeled as tags
        self.mtags = []         # --member-pointers: the tagged member objects of World objects (member_tags), in field order
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
        self.obj_param_spec = {}    # --c-strings: function id -> {parameter index: class of the object its calls pass}
        self.static_results = {}
        self.uses_libm = False
        self.libm_modules = set()   # the C library's modules the translation calls (Musl.sinf, ...)
        self.extern_vars = {}       # C: id of an `extern` declaration of a constant -> its name (the definition is a constant)
        self.ctx_deps = {}
        self.method_bodies = {}  # mangled name -> out-of-line definition
        self.dropped = {}       # decl id -> qualified name: data members and member functions left out (--drop)
        self.boundary_globals = {}  # `extern` references to boundary objects (`hal`): decl id -> name
        self.out_ctors = {}     # --output-log: Lean constructor name -> ([(param name, CType)], C++ text, node)
        self.out_keys = {}      # (object, member) -> constructor name
        self.goto_rejects = {}  # --gotos: function id -> Reject of its rewrite (GotoRewriter)
        self.static_vars = []   # --ekf-types --world: (record, VarDecl) of mutable static data members (World fields)
        self.static_used = set()    # --front-ends: ids of the records some of whose static data members a translated file names
        self.elem_params = {}       # --ins-gps: constructor parameter id -> ("elem", World object, fields): passes an element's index (heap_elem_refs)
        self.globals = {}           # --mavlink: id of a mutable file-scope variable -> {lean, t, decl, ns} (state threaded through the functions)
        self.global_alias = {}      # --mavlink: id of an `extern` declaration of such a variable -> the definition's id
        self.gaccessors = {}        # --mavlink: mangled name of a function `return &g[i];` / `return &g;` -> (global id, parameter index or None)
        self.byte_fields = set()    # --mavlink: ids of integer array members used only as bytes (byte_view_fields): stored as bytes
        self.struct_ptr_params = set()  # --mavlink: ids of `T *` / `const T *` parameters to plain structs (references to the object)
        if MAVLINK[0] and NULL_MEMBERS:
            fold_null_members(self)
        if MAVLINK[0]:
            merge_late_inits(self)
        if GOTOS[0] and not C_MODE[0]:
            rewrite_gotos(self)

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
        if decl is None or decl.get("kind") != "FunctionDecl":
            return None
        if not self.in_set(decl):
            # C: a prototype in a header outside the files (musl's libm.h `hidden float __sindf(double)`)
            # of a function defined in them
            d = self.defs_by_mangled.get(decl.get("mangledName")) if C_MODE[0] or MAVLINK[0] else None
            return d if d is not None and self.in_set(d) else None
        return self.defs_by_mangled.get(decl.get("mangledName"))

    def parent_record(self, d):
        if d is None:
            return None
        p = self.decl(d.get("parentDeclContextId")) if d.get("parentDeclContextId") else self.parent.get(d["id"])
        if p is None:
            return None
        if FRONT_ENDS[0] and p.get("kind") == "FunctionTemplateDecl":
            p = self.decl(p.get("parentDeclContextId")) if p.get("parentDeclContextId") else self.parent.get(p["id"])
            if p is None:
                return None     # (--front-ends: a specialization of a member template is a member function of the class)
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
                if f.category == "erased":
                    continue        # --ring-buffers: only the wrappers' copies of the class are translated
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
        t, init = c["t"], non_attr(kids(d))[0]
        if t.kind == "array":
            if init.get("kind") != "InitListExpr":
                raise Reject(d, "array `%s` without an initializer list" % d["name"])
            pre, v = tr.array_init(init, t)
        else:
            pre, v = tr.expr(init)
        if pre:
            raise Reject(d, "constant initializer with side effects")
        self.uses_libm |= tr.uses_libm
        item = {"key": srckey_node(self, d), "kind": "const", "id": rid, "payload": (d, c, v), "deps": tr.deps}
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
                up = self.parent.get(m["id"])
                while up is not None and up.get("kind") == "ImplicitCastExpr":
                    up = self.parent.get(up["id"])
                if up is not None and up.get("kind") == "MemberExpr" and \
                        boundary_static_name(qualified_name(self, d).rsplit("::", 1)[0] + "::" + up.get("name", "")):
                    continue        # a call of another --boundary-static member (`snprintf` -> `vsnprintf`)
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


# ---------------------------------------------------------------------------------------------
# Reading clang's AST (PORT-PLAN.md 4.12, decision D13). clang writes its JSON dump to a temporary
# file. A small dump is read whole. A large one (a translation unit with ArduPilot's real headers:
# about 1 GB, mostly MAVLink's generated inline functions) is read in two passes over the file:
# pass 1 cuts the document into declarations (the children of the TranslationUnitDecl and, inside
# namespaces and `extern "C"` blocks, their children) and notes, for each, its byte span, its file,
# the location state clang's elision carries into it, and the declarations nested in it; pass 2
# decodes only the declarations of the translated and --lib-dir files and those they reach by id,
# transitively. The tree it builds is the whole tree with the other declarations left out, in
# document order, with the locations fill_locations would give them; the typedefs (TYPEDEFS,
# REV_TYPEDEFS) are collected from the whole document. CPP2LEAN_AST=whole or =stream forces a reader.

AST_STREAM_MIN = 64 << 20   # dumps of at least this many bytes are streamed (below, reading whole is as fast)
AST_BLOCK = 32 << 20        # pass 1 reads the dump in blocks of this size
AST_MARGIN = 4 << 20        # ... and looks this far past a node's start for its attributes
AST_NODE = re.compile(rb'\{\n( *)"id": "(0x[0-9a-f]+)",\n *"kind": "(\w+)"')
AST_FILE = re.compile(rb'"file": ("[^"\\\n]*(?:\\.[^"\\\n]*)*"),\n *"line": ')   # not `"includedFrom": {"file": ...}`
AST_LINE = re.compile(rb'"line": (\d+),\n')
AST_ID = re.compile(rb'"(0x[0-9a-f]+)"')
AST_PREV = re.compile(rb'"previousDecl": "(0x[0-9a-f]+)"')
AST_CONTAINERS = (b"TranslationUnitDecl", b"NamespaceDecl", b"LinkageSpecDecl")
AST_TYPEDEFS = (b"TypedefDecl", b"TypeAliasDecl")


class AstLayoutError(Exception):
    """The dump is not laid out as the streaming reader expects (it is then read whole)."""


def run_clang(path, extra=(), keep=None):
    """clang's AST of path, with its locations filled in, and the typedefs of the unit for
    collect_typedefs (None: collect them from the tree). keep = (main file, --header files,
    --lib-dir directories): the declarations the streaming reader must keep."""
    if C_MODE[0]:
        cmd = [CC] + C_FLAGS + list(extra) + ["-Xclang", "-ast-dump=json", "-fsyntax-only", path]
    else:
        cmd = [CLANG] + CLANG_FLAGS + list(extra) + ["-Xclang", "-ast-dump=json", "-fsyntax-only", path]
    with tempfile.TemporaryFile() as out:
        p = subprocess.run(cmd, stdout=out, stderr=subprocess.PIPE)
        if p.returncode != 0:
            sys.stderr.write(p.stderr.decode())
            sys.stderr.write("cpp2lean: clang failed on %s\n" % path)
            sys.exit(1)
        size = out.seek(0, 2)
        mode = os.environ.get("CPP2LEAN_AST") or ("stream" if size >= AST_STREAM_MIN else "whole")
        if mode == "stream" and keep is not None:
            try:
                return read_ast_stream(out, keep)
            except AstLayoutError as e:
                sys.stderr.write("cpp2lean: %s; reading the whole AST (%d bytes)\n" % (e, size))
        out.seek(0)
        tree = json.loads(out.read())
    fill_locations(tree)
    return tree, None


class AstDecl:
    """A declaration of pass 1: a child of the TranslationUnitDecl, of a namespace or of an
    `extern "C"` block (a container: its header, the attributes before `inner`), or the root."""
    __slots__ = ("start", "end", "hdr_end", "indent", "parent", "state", "file", "container", "header",
                 "has_inner", "whole")

    def __init__(self, start, indent, parent, state, file, container, header, has_inner):
        self.start, self.end, self.hdr_end, self.indent, self.parent = start, None, None, indent, parent
        self.state, self.file, self.container, self.header = state, file, container, header
        self.has_inner, self.whole = has_inner, False


def ast_header(buf, s, k, nxt):
    """The attributes of the node starting at buf[s] (indentation k): the node without `inner`,
    and whether it has `inner`. Its `inner` key, else its end, comes before the next node (nxt)."""
    inner_key = b"\n" + b" " * (k + 2) + b'"inner": ['
    end = b"\n" + b" " * k + b"}"
    for hi in (nxt, len(buf)):
        i, e = buf.find(inner_key, s, hi), buf.find(end, s, hi)
        if i != -1 and (e == -1 or i < e):
            if buf[i - 1:i] != b",":
                raise AstLayoutError("unexpected attributes at byte %d" % s)
            return json.loads(buf[s:i - 1] + b"\n}"), True
        if e != -1:
            return json.loads(buf[s:e + len(end)]), False
    raise AstLayoutError("node attributes past the reading margin at byte %d" % s)


def ast_cut(buf, lo):
    """A position at or after lo where pass 1 may cut the text: the newline before a line that
    closes an object or array (no node start and no location key spans it)."""
    i = len(buf)
    while True:
        i = buf.rfind(b"\n", lo, i)
        j = buf.find(b"\n", i + 1) if i != -1 else -1
        if i == -1:
            raise AstLayoutError("no place to cut the dump after byte %d" % lo)
        if j != -1 and buf[i + 1:j].strip() in (b"}", b"},", b"]", b"],"):
            return i


def ast_advance(state, buf, a, b):
    """The location state after the text buf[a:b] (fill_locations' replay, on the text): the last
    "file" of a location, and the last "line" (a location's "file" is followed by its "line")."""
    i = buf.rfind(b'"line": ', a, b)
    if i == -1:
        return
    m = None
    for m in AST_FILE.finditer(buf, a, i + 8):
        pass
    if m is not None:
        state["file"] = json.loads(m.group(1))
    m = AST_LINE.match(buf, i, b)
    if m is None:
        raise AstLayoutError("unexpected location at byte %d" % i)
    state["line"] = int(m.group(1))


def ast_scan(f):
    """Pass 1 over the dump in f: the declarations (AstDecl, in document order), decl id ->
    the declarations whose text holds that declaration node, previousDecl id -> the declarations
    redeclaring it, and the typedef nodes with whether each is at namespace scope."""
    decls, nested, redecl, typedefs = [], {}, {}, []
    stack = []                  # open declarations: containers, then the current leaf
    state = {"file": None, "line": None}
    base, buf, cursor, eof = 0, b"", 0, False
    f.seek(0)
    while True:
        chunk = f.read(AST_BLOCK)
        eof = not chunk
        buf = buf[cursor:] + chunk if cursor else buf + chunk
        base += cursor
        cursor = 0
        if not eof and len(buf) < 2 * AST_MARGIN:
            continue
        limit = len(buf) if eof else len(buf) - AST_MARGIN
        ms = [m for m in AST_NODE.finditer(buf) if buf[m.start() - 2:m.start()] != b": "]  # not a reference `"decl": {`
        prevs = [(m.start(), m.group(1)) for m in AST_PREV.finditer(buf)]
        pi = 0
        cut = None
        for j, m in enumerate(ms):
            s = m.start()
            if s >= limit:
                cut = s
                break
            k = len(m.group(1)) - 2
            nid, kind = m.group(2), m.group(3)
            nxt = ms[j + 1].start() if j + 1 < len(ms) else len(buf)
            while stack and decls[stack[-1]].indent >= k:
                decls[stack.pop()].end = base + s
            top = decls[stack[-1]] if stack else None
            if top is None or top.container:
                if top is not None and k != top.indent + 4 or top is None and decls:
                    raise AstLayoutError("unexpected node layout at byte %d" % (base + s))
                ast_advance(state, buf, cursor, s)
                cursor = s
                header, has_inner = ast_header(buf, s, k, nxt)
                fill_locations(header, dict(state))
                loc = expansion(header.get("loc"))
                container = kind in AST_CONTAINERS
                d = AstDecl(base + s, k, stack[-1] if stack else None, (state["file"], state["line"]),
                            loc.get("file") if loc else None, container, header if container else None, has_inner)
                if top is not None and top.hdr_end is None:
                    top.hdr_end = base + s
                stack.append(len(decls))
                decls.append(d)
                if kind in AST_TYPEDEFS:
                    typedefs.append((header, True))
            elif kind in AST_TYPEDEFS:
                typedefs.append((ast_header(buf, s, k, nxt)[0], False))
            if kind.endswith(b"Decl"):
                ds = nested.setdefault(nid, [])
                if not ds or ds[-1] != stack[-1]:
                    ds.append(stack[-1])
            while pi < len(prevs) and prevs[pi][0] < s:
                pi += 1
            while pi < len(prevs) and prevs[pi][0] < nxt:     # a redeclaration in this node's attributes
                ds = redecl.setdefault(prevs[pi][1], [])
                if not ds or ds[-1] != stack[-1]:
                    ds.append(stack[-1])
                pi += 1
        if eof:
            break
        if cut is None:
            cut = ast_cut(buf, limit)
        ast_advance(state, buf, cursor, cut)
        cursor = cut
    for i in stack:
        decls[i].end = base + len(buf)
    for d in decls:
        if d.hdr_end is None:
            d.hdr_end = d.end
    return decls, nested, redecl, typedefs


def ast_closure(f, decls, nested, redecl, keep):
    """The declarations pass 2 decodes: those of the translated and --lib-dir files (a namespace
    there with everything in it), every declaration whose text holds a declaration node whose id a
    kept declaration's text holds (a reference, or another listing of a node it holds), every
    redeclaration of a kept one (an out-of-line definition), and the containers of kept ones."""
    main, headers, lib_dirs = keep
    files = {os.path.realpath(x) for x in [main] + list(headers)}
    libs = [os.path.realpath(x) + os.sep for x in lib_dirs]
    real = {}

    def wanted(fn):
        if fn is None:
            return False
        if fn not in real:
            rf = os.path.realpath(fn)
            real[fn] = rf in files or any(rf.startswith(x) for x in libs)
        return real[fn]

    kept = bytearray(len(decls))
    work = []

    def add(i):
        while i is not None and not kept[i]:
            kept[i] = 1
            work.append(i)
            i = decls[i].parent

    for i, d in enumerate(decls):
        if d.parent is None:
            add(i)
        elif decls[d.parent].whole or wanted(d.file):
            d.whole = d.container
            add(i)
    seen = set()
    while work:
        d = decls[work.pop()]
        f.seek(d.start)
        text = f.read((d.end if not d.container or d.whole else d.hdr_end) - d.start)
        for x in set(AST_ID.findall(text)):
            if x in seen:
                continue
            seen.add(x)
            for j in nested.get(x, ()):
                add(j)
            for j in redecl.get(x, ()):
                add(j)
    return kept


def read_ast_stream(f, keep):
    """Pass 2: the tree of the kept declarations (each decoded on its own, its locations filled in
    from the state before it), and the typedefs of the whole unit for collect_typedefs."""
    decls, nested, redecl, typedefs = ast_scan(f)
    kept = ast_closure(f, decls, nested, redecl, keep)
    decoder = json.JSONDecoder()
    nodes = {}
    root = None
    for i, d in enumerate(decls):
        if not kept[i]:
            continue
        if d.container:
            n = d.header
            if d.has_inner:
                n["inner"] = []
        else:
            f.seek(d.start)
            n = decoder.raw_decode(f.read(d.end - d.start).decode("utf-8", "surrogatepass"))[0]
            fill_locations(n, {"file": d.state[0], "line": d.state[1]})
        nodes[i] = n
        if d.parent is None:
            root = n
        else:
            nodes[d.parent]["inner"].append(n)
    if root is None:
        raise AstLayoutError("no translation unit")
    if os.environ.get("CPP2LEAN_AST_STATS"):
        size = sum(d.end - d.start for i, d in enumerate(decls) if kept[i] and not d.container)
        sys.stderr.write("cpp2lean: AST %d bytes, %d declarations; decoded %d declarations, %d bytes\n" %
                         (decls[0].end, len(decls), sum(kept), size))
    return root, typedefs


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


_REALPATHS = {}     # find_file: os.path.realpath of each file name seen (the same few names on every node)


def find_file(tree, path):
    real = os.path.realpath(path)
    for n in walk(tree):
        loc = expansion(n.get("loc")) if n.get("loc") else None
        if loc and loc.get("file"):
            f = loc["file"]
            r = _REALPATHS.get(f)
            if r is None:
                r = _REALPATHS[f] = os.path.realpath(f)
            if r == real:
                return f
    return None


def cpp_signature(fn, ps):
    """The C++ declaration as clang spells its types."""
    ret = fn["type"]["qualType"].split("(")[0].strip()
    return "%s %s(%s)" % (ret, fn["name"], ", ".join("..." if p.get("kind") == "Variadic" else "%s %s" % (p["type"]["qualType"], p["name"]) for p, pn, pt, ref in ps))


def cpp_var_decl(d, name=None):
    q = d["type"]["qualType"]
    name = name or d["name"]
    m = re.match(r"^(.*?)\s*((?:\[\d+\])+)$", q)
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


def boundary_static_name(qn):
    """Is qn (a qualified name, possibly without the namespace of a class declared as
    `class AP_HAL::Util {`) a --boundary-static member function?"""
    return qn in BOUNDARY_STATIC or any(x.endswith("::" + qn) for x in BOUNDARY_STATIC)


_MEMBER_RANGES = {}


def member_constant_range(u, fid):
    """--reachable: (0, max) if every occurrence of data member fid in the program is a read or the
    left side of `=` with an integer constant (`stateIndexLim = 23;`), with max the largest such
    constant (and 0, the value of the zero-filled object); else None."""
    if fid in _MEMBER_RANGES:
        return _MEMBER_RANGES[fid]
    vals = [0]
    ok = True
    stack = [(u.tree, None)]
    while stack and ok:
        nd, parent = stack.pop()
        if not isinstance(nd, dict):
            continue
        if nd.get("kind") == "MemberExpr" and nd.get("referencedMemberDecl") == fid:
            pk = parent.get("kind") if parent else None
            if pk == "ImplicitCastExpr" and parent.get("castKind") == "LValueToRValue":
                pass
            elif pk == "BinaryOperator" and parent.get("opcode") == "=" and kids(parent)[0] is nd:
                rhs = strip_parens(kids(parent)[1])
                while rhs.get("kind") == "ImplicitCastExpr":
                    rhs = strip_parens(kids(rhs)[0])
                if rhs.get("kind") == "IntegerLiteral":
                    vals.append(int(rhs["value"]))
                else:
                    ok = False
            else:
                ok = False
        for c in nd.get("inner", []):
            stack.append((c, nd))
    _MEMBER_RANGES[fid] = (min(vals), max(vals)) if ok else None
    return _MEMBER_RANGES[fid]


def boundary_query_match(u, mdecl, obj):
    """--reachable: is mdecl a --boundary-query member function, named by its class's last component
    (a declaration of a header outside the translation may not carry its enclosing namespaces)?"""
    qn = qualified_name(u, mdecl)
    return any(q == qn or q.endswith("::" + qn) or (q.split("::")[-1] == mdecl.get("name") and "::" not in qn) for q in BOUNDARY_QUERY)


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
                    if td is None and FRONT_ENDS[0]:
                        return          # --front-ends: not registered (a use of one of its enumerators is rejected)
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
            elif k in ("CXXRecordDecl", "ClassTemplateSpecializationDecl", "RecordDecl") and d.get("completeDefinition") and not d.get("isImplicit"):
                # (RecordDecl: a C struct, musl's `struct exp2f_data`)
                if d["id"] in u.records_by_id:
                    return
                anon_field = None
                td_name = None
                if MISSION[0] and d.get("tagUsed") == "union":
                    register_byte_union(u, d, parent_rec)     # --mission: the bytes of its size, its members views
                    return
                if EKF_TYPES[0] and d.get("tagUsed") == "union" and (register_bitunion(u, d) or array_view_union(u, d)):
                    return
                if "name" not in d:
                    anon_field = anonymous_member(u, d)
                    if EKF_TYPES[0] and anon_field is None:
                        # --ekf-types: `typedef struct { ... } EKF_obs_element_t;` (EKF_Buffer.h:9): named by the typedef
                        td = next((c for c in kids(u.parent.get(d["id"]) or {}) if c.get("kind") == "TypedefDecl" and
                                   any(x.get("ownedTagDecl", {}).get("id") == d["id"] for x in walk(c))), None)
                        td_name = td["name"] if td is not None else None
                    if td_name is None and anon_field is None and parent_rec is None and FRONT_ENDS[0]:
                        # --front-ends: `static const struct { ... } atmospheric_1976_consts[] = {...};`
                        # (AP_Baro_atmosphere.cpp:76): the struct named after the variable it is the type of
                        loc = expansion(d.get("loc")) or {}
                        spell = "(unnamed %s at %s:%d:%d)" % (d.get("tagUsed", "struct"), loc.get("file"), loc.get("line", 0), loc.get("col", 0))
                        var = next((x for x in kids(u.parent.get(d["id"]) or {}) if x.get("kind") == "VarDecl" and
                                    spell in x.get("type", {}).get("qualType", "")), None)
                        if var is not None:
                            r = RecordInfo(d, spell, lean_record_name(var["name"] + "_t"), None)
                            r.name = var["name"] + "_t"
                            r.lib = u.is_lib(d)
                            RECORDS[spell] = r
                            u.records.append(r)
                            u.records_by_id[r.id] = r
                            return
                    if td_name is None and (anon_field is None or parent_rec is None):
                        raise Reject(d, "anonymous struct or class (other than the type of one data member of a class)")
                if d.get("tagUsed") == "union":
                    if EKF_TYPES[0] and (register_bitunion(u, d) or array_view_union(u, d)):
                        return
                    raise Reject(d, "union `%s`" % d.get("name", "(anonymous)"))
                if anon_field is not None:
                    # `struct { ... } member;`: the type is named after the member (`AP_Motors._motor_pwm_scaled_t`)
                    loc = expansion(d.get("loc")) or {}
                    cxx = "%s::(unnamed %s at %s:%d:%d)" % (parent_rec.cxx, d.get("tagUsed", "struct"), loc.get("file"), loc.get("line", 0), loc.get("col", 0))
                    r = RecordInfo(d, cxx, parent_rec.lean + "." + anon_field + "_t", parent_rec)
                    r.name = anon_field + "_t"
                    r.lib = u.is_lib(d)
                    RECORDS[cxx] = r
                    if C_MODE[0]:
                        # C has no nested scopes for types: clang names it without the enclosing struct
                        # (and desugars it as `logf_data::(unnamed at ...)`)
                        RECORDS[cxx.split("::", 1)[1]] = r
                        RECORDS["%s::(unnamed at %s:%d:%d)" % (parent_rec.cxx, loc.get("file"), loc.get("line", 0), loc.get("col", 0))] = r
                    u.records.append(r)
                    u.records_by_id[r.id] = r
                    return
                if td_name is not None:
                    owner = u.parent.get(d["id"])
                    cxx = (qualified_name(u, owner) + "::" if owner is not None and owner.get("kind") in ("CXXRecordDecl", "NamespaceDecl") else "") + td_name
                    r = RecordInfo(d, cxx, lean_record_name(cxx), parent_rec)
                    r.name = td_name
                    r.lib = u.is_lib(d)
                    RECORDS[cxx] = r
                    u.records.append(r)
                    u.records_by_id[r.id] = r
                    return
                cxx = qualified_name(u, d)
                if cxx in BOUNDARY or d["name"] in BOUNDARY or cxx in PARAM_CLASSES or d["name"] in PARAM_CLASSES:
                    return
                if AP_PARAM[0] and not PARAM_EXT[0] and re.match(r"^AP_(ParamT|Enum|Enum16)<", cxx):
                    return          # (--param-ext: AP_ParamT, AP_ParamV, AP_Enum are library classes translated from AP_Param.h, AP_ParamT.cpp)
                lean = lean_record_name(cxx)
                r = RecordInfo(d, cxx, lean, parent_rec)
                if "<" in cxx:
                    r.name = lean.split(".")[-1]
                r.lib = u.is_lib(d)
                RECORDS[cxx] = r
                u.records.append(r)
                u.records_by_id[r.id] = r
                for c in kids(d):
                    if c.get("kind") in ("CXXRecordDecl", "EnumDecl", "RecordDecl"):
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


def register_byte_union(u, d, parent_rec):
    """--mission: register union d (`AP_Mission::Content`, `PackedContent`, or an anonymous union member of a
    struct, `union { Packed_Location_Option_Flags flags; uint8_t options; };` of PackedLocation) as a byte union:
    a structure holding the bytes of its size (`bytes : Array UInt8`), each member a view of them at offset 0
    (fill_records sets the size and the members; resolve_path reads and writes the views)."""
    loc = expansion(d.get("loc")) or {}
    if "name" in d:
        cxx = qualified_name(u, d)
        lean = lean_record_name(cxx)
    else:
        # an anonymous union: named after its line; its implicit member (no name in clang's AST) gets that name
        if parent_rec is None:
            raise Reject(d, "anonymous union outside a struct")
        cxx = "%s::(anonymous union at %s:%d:%d)" % (parent_rec.cxx, loc.get("file"), loc.get("line", 0), loc.get("col", 0))
        lean = parent_rec.lean + ".union'%d_t" % loc.get("line", 0)
        for c in kids(parent_rec.node):
            if c.get("kind") == "FieldDecl" and "name" not in c and c.get("type", {}).get("qualType", "").endswith(
                    "(anonymous union at %s:%d:%d)" % (loc.get("file"), loc.get("line", 0), loc.get("col", 0))):
                c["name"] = "union'%d" % loc.get("line", 0)
    r = RecordInfo(d, cxx, lean, parent_rec)
    if "name" not in d:
        r.name = "union'%d_t" % loc.get("line", 0)
    r.lib = u.is_lib(d)
    r.byte_union = True
    RECORDS[cxx] = r
    u.records.append(r)
    u.records_by_id[r.id] = r


def fill_byte_union(u, r):
    """--mission: the members (views) and the one field `bytes` (the union's size) of byte union r."""
    r.union_members = {}
    size, align = 0, 1
    for c in kids(r.node):
        if c.get("kind") != "FieldDecl":
            continue
        t, ref = decl_type(c)
        if ref is not None or c.get("isBitfield"):
            raise Reject(c, "union member `%s` that is a reference or a bit-field" % c.get("name", ""))
        f = FieldInfo(c, r, t, "state")
        r.union_members[c["id"]] = f
        sz, al = byte_size_align(t, c)
        size, align = max(size, sz), max(align, al)
    if not r.union_members:
        raise Reject(r.node, "union without members")
    size = (size + align - 1) // align * align
    fake = {"id": "bytes'%s" % r.id, "name": "bytes", "kind": "FieldDecl", "type": {"qualType": "uint8_t[%d]" % size}}
    fake["loc"], fake["range"] = r.node.get("loc"), r.node.get("range")
    bf = FieldInfo(fake, r, CType("array", elem=UINT8, n=size), "state")
    bf.lean = "bytes"
    bf.rb_doc = "/-- The %d bytes of the union `%s` (each member a view of them at offset 0, --mission). -/" % (size, comment_safe(r.cxx))
    r.fields = [bf]
    r.union_size, r.union_align = size, align
    r.field_layout = [(f.name, 0, byte_size_align(f.t, f.decl)[0], False) for f in r.union_members.values()]
    r.bit_leaves = []
    r.byte_layout = ([(i, [("f", "bytes"), ("i", i)], UINT8) for i in range(size)], size, align)


def anonymous_member(u, d):
    """The name of the data member whose type is the anonymous struct d (`struct { ... } m;`), or None."""
    parent = u.parent.get(d["id"])
    loc = expansion(d.get("loc")) or {}
    key = "unnamed %s at %s:%d:%d)" % (d.get("tagUsed", "struct"), loc.get("file"), loc.get("line", 0), loc.get("col", 0))
    fields = [c for c in kids(parent or {}) if c.get("kind") == "FieldDecl" and re.sub(r"\[\d+\]$", "", c["type"]["qualType"]).endswith(key)]
    return fields[0]["name"] if len(fields) == 1 else None


def drop_match(r, c):
    """Is member c of record r named by --drop: `Class::name` (every overload) or `Class::name(T1, T2)`
    (the overload with these parameter types, as written or as clang desugars them)?"""
    qn = "%s::%s" % (r.cxx, c["name"])
    if qn in DROP:
        return True
    ps = [p for p in kids(c) if p.get("kind") == "ParmVarDecl"]
    for x in DROP:
        if x.startswith(qn + "("):
            want = [norm_param_type(y) for y in split_top(x[len(qn) + 1:-1])]
            if len(want) == len(ps) and all(w in {norm_param_type(p["type"]["qualType"]), norm_param_type(p["type"].get("desugaredQualType", p["type"]["qualType"]))}
                                            for w, p in zip(want, ps)):
                return True
    return False


def fill_records(u, reject):
    """Bases, fields, member functions and kinds of the registered records."""
    for r in u.records:
        d = r.node
        if FRONT_ENDS[0] and r.id in BITFIELD_VIEWS:
            continue        # --front-ends: the bit-fields of a bit union's struct (`struct DeviceStructure`): the union's bits
        if SEMAPHORES and (r.cxx in SEMAPHORES or r.name in SEMAPHORES):
            r.semaphore = True      # --semaphores: no state, no member functions (one thread)
            continue
        if WORLD_PTRS[0] and (r.cxx == "Functor" or r.cxx.startswith("Functor<")):
            r.functor = True        # --world-pointers: functors are `WFun` (AP_HAL/utility/functor.h)
            continue
        if getattr(r, "byte_union", False):
            continue                # --mission: filled after the other records (fill_byte_union), whose layouts it needs
        try:
            for b in d.get("bases", []):
                if b.get("isVirtual"):
                    raise Reject(d, "virtual base class")
                bt = b["type"]
                name, _ = strip_tag(bt.get("desugaredQualType", bt["qualType"]))
                name = norm_template_args(name)
                if (PARAM_EXT[0] or FRONT_ENDS[0]) and name not in RECORDS:
                    name = param_ext_name(name)
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
            if k in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl") and "name" in c and drop_match(r, c):
                u.dropped[c["id"]] = "%s::%s" % (r.cxx, c["name"])
            if k == "FriendDecl" and c.get("type"):
                continue                # `friend class X;`: access control only, no effect on the model
            if MAVLINK[0] and k == "FieldDecl" and "name" in c and NULL_MEMBERS and \
                    ("%s::%s" % (r.cxx, c["name"]) in NULL_MEMBERS or "%s::%s" % (r.node.get("name"), c["name"]) in NULL_MEMBERS):
                u.dropped[c["id"]] = "%s::%s" % (r.cxx, c["name"])      # --null-member: always null, not state (NullFold)
                r.dropped.append(c)
                continue
            try:
                if k == "FieldDecl":
                    if c.get("mutable"):
                        raise Reject(c, "mutable member `%s`" % c.get("name", ""))
                    if "name" not in c and EKF_TYPES[0]:
                        uf = union_view_field(u, r, c)
                        if uf is not None:
                            r.fields.append(uf)
                            continue
                    if "name" not in c:
                        raise Reject(c, "unnamed member")
                    if RING_BUFFERS[0] and erased_member(c):
                        # --ring-buffers: `void *buffer` of a type-erased container; each typed wrapper
                        # deriving from the class gets a copy of it with the element type (monomorphize_buffers)
                        r.fields.append(FieldInfo(c, r, None, "erased"))
                        continue
                    ht = held_member_type(c)
                    if ht is not None:
                        # --c-strings: `char *const _str` bound by the constructor to an array the
                        # caller passes: the object holds that array (README.md, "Phase 2b")
                        r.fields.append(FieldInfo(c, r, ht, "state"))
                        continue
                    t, ref = decl_type(c)
                    if MAVLINK[0] and c["id"] in u.byte_fields and t.kind == "array" and t.elem.is_int():
                        # --mavlink: `uint64_t payload64[33]` used only as `(char *)&payload64[0]`: its 264 bytes
                        bt = CType("array", elem=UINT8, n=t.n * (t.elem.bits // 8))
                        bt.bytes_of = t
                        t = bt
                    if t.kind == "sem":
                        u.sem_fields.add(c["id"])   # --semaphores: a semaphore member is not state
                        continue
                    if c.get("isBitfield") and t.kind != "bool":
                        width = next((int(x["value"]) for x in kids(c) if x.get("kind") == "ConstantExpr" and "value" in x), None)
                        if MAVLINK[0] and t.kind == "int" and not t.signed and width is not None and 1 < width < t.bits:
                            BITFIELD_WIDTH[c["id"]] = width     # --mavlink: `uint32_t msgid:24` (mavlink_message_t): writes masked
                            width = 1
                        elif MISSION[0] and t.kind == "int" and t.signed and width is not None and 1 < width < t.bits:
                            SBITFIELD_WIDTH[c["id"]] = width    # --mission: `int32_t alt:24` (PackedLocation): writes sign-extend the low bits
                            BITFIELD_WIDTH[c["id"]] = width
                            width = 1
                        elif not (t.kind == "int" and not t.signed and width == 1):
                            raise Reject(c, "bit-field `%s` of type `%s` (only bool bit-fields are translated)" % (c["name"], t.cname))
                        if c["id"] not in BITFIELD_WIDTH:
                            BIT1_FIELDS.add(c["id"])     # `uint8_t f : 1` (AC_WPNav::wpnav_flags): its declared type, writes masked
                    if t.kind == "boundary":
                        cat = "boundary"
                    elif AHRS_EXT[0] and t.kind == "param" and ref is not None:
                        # --ahrs-ext: `AP_Float &_kp_yaw` of AP_AHRS_DCM (AP_AHRS_DCM.h:142), bound by AP_AHRS's member
                        # initializer `dcm{_kp_yaw, _kp, ...}` to the parameter of the World object it is a member of:
                        # that parameter in the World (`w.ahrs'p._kp_yaw`), read and written there (wpref_path)
                        pt = PARAM_CLASSES.get(t.name) or PARAM_CLASSES.get(t.name.split("::")[-1])
                        r.fields.append(FieldInfo(c, r, parse_type_str(pt, pt, c), "wpref"))
                        continue
                    elif t.kind == "param":
                        pt = PARAM_CLASSES.get(t.name) or PARAM_CLASSES.get(t.name.split("::")[-1])
                        storage = PARAM_STORAGE.get(t.name) or PARAM_STORAGE.get(t.name.split("::")[-1])
                        t, cat = parse_type_str(pt, pt, c), "param"
                    elif MEMBER_PTRS[0] and ref is not None and t.kind == "record" and "(unnamed " in r.cxx:
                        # --member-pointers: a reference member of an unnamed struct (`AP_AHRS_Backend &backend` of
                        # AP_AHRS's `backends_and_estimates[]`, AP_AHRS.h:1051) bound to a member object of the
                        # enclosing class: the object's tag (as a pointer that never changes)
                        t, cat = CType("obj", info=t.info), "state"
                        u.refptr_fields.add(c["id"])
                        r.fields.append(FieldInfo(c, r, t, cat))
                        r.fields[-1].refptr = True
                        continue
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
                    if c.get("isImplicit") and not (INS_GPS[0] and inherited_ctor(c)):
                        continue        # (--ins-gps: an inheriting constructor, `using AP_GPS_Backend::AP_GPS_Backend;`, is one)
                    if k == "CXXConversionDecl" and not FRONT_ENDS[0]:
                        raise Reject(c, "conversion operator")
                    r.methods.append(c)
                elif k == "VarDecl":
                    q = c["type"]["qualType"]
                    if AP_PARAM[0] and "GroupInfo" in q:
                        continue        # the AP_Param table: read by setup_object_defaults
                    if MISSION[0] and SEMAPHORES and (strip_quals(q)[0].split("::")[-1] in {x.split("::")[-1] for x in SEMAPHORES} or
                                                      strip_quals(c["type"].get("desugaredQualType", q))[0].split("::")[-1] in {x.split("::")[-1] for x in SEMAPHORES}):
                        u.sem_fields.add(c["id"])   # --mission: `static HAL_Semaphore _rsem;` (AP_Mission.h:973): a semaphore, no state
                        continue
                    if (q.startswith("const ") or c.get("constexpr")) and not kids(c) and c["id"] in u.static_defs:
                        r.statics.append(c)     # its initializer is that of its out-of-line definition
                        continue
                    mq = re.match(r"^(?:class |struct )?([\w:<>, ]+?) \*$", q)
                    if FRONT_ENDS[0] and WORLD[0] and mq and norm_template_args(mq.group(1).strip()) not in RECORDS and \
                            r.cxx.split("::")[-1] == mq.group(1).strip():
                        u.singleton_ptrs[c["id"]] = r       # --front-ends: `static SIM *_singleton;` inside `namespace SITL`
                        continue
                    if WORLD[0] and mq and norm_template_args(mq.group(1).strip()) in RECORDS:
                        # `static AP_RTC *_singleton;` (AP_RTC.h:76): the class's one World object (--world)
                        u.singleton_ptrs[c["id"]] = RECORDS[norm_template_args(mq.group(1).strip())]
                        continue
                    if MEMBER_OBJECTS[0] and WORLD[0] and not (q.startswith("const ") or c.get("constexpr")) and \
                            static_object_class(c) is not None:
                        continue        # --member-objects: a static data member of a translated class, a World object (its definition)
                    if EKF_TYPES[0] and WORLD[0] and not (q.startswith("const ") or c.get("constexpr")):
                        # --ekf-types --world: a mutable static data member (NavEKF_core_common's shared scratch
                        # arrays `KHP`, `Kfusion`): a field of the World (world_statics)
                        u.static_vars.append((r, c))
                        continue
                    if not (q.startswith("const ") or c.get("constexpr")) or not kids(c):
                        if FRONT_ENDS[0] and r.lib:
                            continue    # --front-ends: a static member of a library class (a use of it is rejected)
                        raise Reject(c, "static data member `%s` that is mutable or has no constant initializer" % c["name"])
                    r.statics.append(c)
                elif k in ("FunctionTemplateDecl", "ClassTemplateDecl"):
                    if k == "FunctionTemplateDecl" and drop_match(r, c):
                        for x in kids(c):
                            u.dropped[x["id"]] = "%s::%s" % (r.cxx, c["name"])
                        continue
                    if FRONT_ENDS[0] and r.lib and k == "FunctionTemplateDecl":
                        # --front-ends: the specializations of a member function template of a library class
                        # (`template<bool X = true> operator const float &()` of AP_ParamT<float>) are its
                        # member functions
                        for x in kids(c):
                            if x.get("kind") in ("CXXMethodDecl", "CXXConversionDecl") and any(y.get("kind") == "CompoundStmt" for y in kids(x)):
                                r.methods.append(x)
                        continue
                    if (r.lib or r.node.get("kind") == "ClassTemplateSpecializationDecl") and not instantiated(c):
                        continue        # a member template of a library class template that nothing instantiates
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
        if r.methods or (r.bases and not (EKF_TYPES[0] and plain_bases(r))):
            r.kind = "class"
    for r in u.records:
        if any(b.kind == "class" for b in r.chain()):
            r.kind = "class"
    if MISSION[0]:
        # --mission: byte unions, inner ones first (a union member of a struct member of a union)
        pending = [r for r in u.records if getattr(r, "byte_union", False)]
        for _ in range(len(pending) + 1):
            left = []
            for r in pending:
                try:
                    fill_byte_union(u, r)
                except Reject as e:
                    left.append((r, e))
            if not left:
                break
            pending = [r for r, _ in left]
        else:
            for r, e in left:
                r.failed = True         # (a use of a member is rejected: "union ... without a layout")
                if not r.lib:
                    reject(e)
    if EKF_TYPES[0]:
        check_union_views(u, reject)
    for r in u.records:
        # a reference member to a class is the owner's back-reference (`AP_Motors &motors` of
        # Thrust_Linearization) only if a class holds an object of r as a member and passes `*this`
        # to its constructor (`Thrust_Linearization thr_lin {*this}`); otherwise it is rejected
        for f in [f for f in r.fields if f.category == "owner"]:
            if not any(owner_binds(u, o, g) for o in u.records for g in o.fields if g.t is not None and g.t.kind == "record" and g.t.info is r):
                if WORLD[0]:
                    f.category = "wref"     # a reference to another object of the World, resolved by resolve_world
                    continue
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


def av_leaf_index(st, steps, node):
    """The index (in elements) of the first scalar leaf of st at steps (a struct whose leaves are
    elements of one array, UNION_VIEWS)."""
    leaves = type_leaves(st, node)
    for k, (off, lsteps, lt) in enumerate(leaves):
        if [tuple(x) for x in lsteps[:len(steps)]] == [tuple(x) for x in steps]:
            return k
    raise AssertionError("no leaf at %r" % (steps,))


def av_value(arr, st, b):
    """Lean text of the value of struct type st viewed in array arr (text) from element b on."""
    a = arr if SIMPLE.match(arr) else "(%s)" % arr
    k = [b]

    def build(t):
        if t.kind == "record":
            fs = [f for f in t.info.all_fields() if f.category == "state"]
            return "({ %s } : %s)" % (", ".join("%s := %s" % (f.lean, build(f.t)) for f in fs), t.lean)
        if t.kind == "array":
            return "#[%s]" % ", ".join(build(t.elem) for _ in range(t.n))
        k[0] += 1
        return "%s[%d]!" % (a, k[0] - 1)
    return build(st)


def array_view_union(u, d):
    """--ekf-types: is union d `union { T a[N]; S s; }` with S a struct of N scalars of type T
    (AP_NavEKF3_core.h:587, `statesArray` and `stateStruct`)? Checked again with the types at the member."""
    fields = [c for c in kids(d) if c.get("kind") == "FieldDecl"]
    return len(fields) == 2 and any(re.search(r"\[\d+\]$", f["type"].get("desugaredQualType", f["type"]["qualType"])) for f in fields)


def union_view_field(u, r, c):
    """--ekf-types: the FieldInfo of the array member of the unnamed union member c of record r
    (the array is canonical; the struct member is a view of it, UNION_VIEWS), or None."""
    q = c["type"].get("qualType", "")
    m = re.search(r"\((?:unnamed|anonymous) union at ([^():`]+):(\d+):(\d+)\)", q)
    if not m:
        return None
    ud = next((x for x in kids(r.node) if x.get("kind") in ("CXXRecordDecl", "RecordDecl") and x.get("tagUsed") == "union"
               and (expansion(x.get("loc")) or {}).get("line") == int(m.group(2))
               and (expansion(x.get("loc")) or {}).get("col") == int(m.group(3))), None)
    if ud is None:
        return None
    fs = [x for x in kids(ud) if x.get("kind") == "FieldDecl"]
    if len(fs) != 2:
        return None
    ts = [decl_type(f)[0] for f in fs]
    ai = next((i for i, t in enumerate(ts) if t.kind == "array" and t.elem.is_scalar() and not getattr(t, "dims", None)), None)
    if ai is None or ts[1 - ai].kind != "record":
        return None
    at, st = ts[ai], ts[1 - ai]
    UNION_VIEWS[c["id"]] = (fs[ai]["id"], fs[1 - ai]["id"], st)
    f = FieldInfo(fs[ai], r, at, "state")
    f.union_view = (c, st)          # checked when every record is filled (check_union_views)
    return f


def check_union_views(u, reject):
    """--ekf-types: the struct of each array view has exactly the array's elements as its scalar leaves, in order."""
    for r in u.records:
        for f in r.fields:
            if getattr(f, "union_view", None) is None:
                continue
            c, st = f.union_view
            at = f.t
            try:
                leaves = type_leaves(st, c)
                esz = byte_size_align(at.elem, c)[0]
                if len(leaves) != at.n or any(lt != at.elem or off != k * esz for k, (off, _, lt) in enumerate(leaves)) or \
                        byte_size_align(st, c)[0] != at.n * esz:
                    raise Reject(c, "union of `%s` and `%s` whose members are not the array's elements in order" % (at.cname, st.cname))
            except Reject as e:
                reject(e)
                r.failed = True
                UNION_VIEWS.pop(c["id"], None)


class BitUnion:
    """--ekf-types: `union { struct { bool a : 1; bool b : 1; ... } flags; uint32_t value; }`
    (AP_Nav_Common.h:48 nav_filter_status, AP_NavEKF3_core.h:1621 with an anonymous struct): the
    union is its integer member (`value`); the k-th one-bit field is bit k of it (bit-fields are
    allocated from the least significant bit on the little-endian targets)."""

    def __init__(self, word, value_id, struct_id, bits, value_name="value"):
        self.word, self.value_id, self.struct_id, self.bits = word, value_id, struct_id, bits   # bits: field id -> index
        self.value_name = value_name


def register_bitunion(u, d):
    """Register union d as a BitUnion if it has that shape (else False)."""
    fields = [c for c in kids(d) if c.get("kind") == "FieldDecl"]
    recs = {c["id"]: c for c in kids(d) if c.get("kind") in ("CXXRecordDecl", "RecordDecl") and c.get("completeDefinition")}
    if len(fields) != 2:
        return False
    word = sf = None
    for f in fields:
        q = f["type"].get("desugaredQualType", f["type"]["qualType"])
        if q in INT_TYPES and not INT_TYPES[q][1] and "name" in f:
            word = (f, CType("int", INT_TYPES[q][0], False))
        else:
            sf = f
    if word is None or sf is None:
        return False
    st = next((r for r in recs.values() if r.get("tagUsed") == "struct"), None)
    if st is None and FRONT_ENDS[0]:
        # --front-ends: `union DeviceId { struct DeviceStructure devid_s; uint32_t devid; }` (AP_HAL/Device.h:378):
        # a named struct of bit-fields and bytes, laid out as the Itanium ABI allocates them
        sq = strip_tag(sf["type"].get("desugaredQualType", sf["type"]["qualType"]))[0]
        short = sq.split("::")[-1]
        st = next((x for x in u.ids.values() if x.get("kind") == "CXXRecordDecl" and x.get("completeDefinition") and
                   x.get("tagUsed") == "struct" and x.get("name") == short and ("::" + sq).endswith("::" + qualified_name(u, x))), None)
        lay = bitfield_layout(u, st, word[1]) if st is not None else None
        if lay is None:
            return False
        bu = BitUnion(word[1], word[0]["id"], sf["id"], lay, word[0]["name"])
        for k in [d.get("name"), qualified_name(u, d)] if d.get("name") else []:
            BITUNIONS[k] = bu
        BITFIELD_VIEWS.add(st["id"])
        return True
    if st is None:
        return False
    bits = {}
    for i, b in enumerate(c for c in kids(st) if c.get("kind") == "FieldDecl"):
        q = b["type"].get("desugaredQualType", b["type"]["qualType"])
        width = next((int(x["value"]) for x in kids(b) if x.get("kind") == "ConstantExpr" and "value" in x), None)
        if not b.get("isBitfield") or width != 1 or q not in ("bool", "uint8_t", "unsigned char", "uint16_t", "uint32_t", "unsigned int"):
            return False
        bits[b["id"]] = i
    if not bits or len(bits) > word[1].bits:
        return False
    bu = BitUnion(word[1], word[0]["id"], sf["id"], bits, word[0]["name"])
    loc = expansion(d.get("loc")) or {}
    keys = []
    if d.get("name"):
        keys += [d["name"], qualified_name(u, d)]
    owner = u.parent.get(d["id"])
    for how in ("unnamed", "anonymous"):
        keys.append("(%s union at %s:%d:%d)" % (how, loc.get("file"), loc.get("line", 0), loc.get("col", 0)))
        if owner is not None and owner.get("kind") in ("CXXRecordDecl", "ClassTemplateSpecializationDecl"):
            keys.append("%s::(%s union at %s:%d:%d)" % (qualified_name(u, owner), how, loc.get("file"), loc.get("line", 0), loc.get("col", 0)))
    for k in keys:
        BITUNIONS[k] = bu
    return True


def bitfield_layout(u, st, word):
    """--front-ends: {field id: (bit offset, width, CType)} of a struct of integer and enum fields and
    bit-fields as the Itanium C++ ABI lays them out (a bit-field starts at the next unit of its declared
    type when it would straddle one; other fields at their alignment), or None if a field is of another
    type or the struct does not fit in the union's word."""
    out, off = {}, 0
    for b in (c for c in kids(st) if c.get("kind") == "FieldDecl"):
        try:
            t = ctype_of(b)
        except Reject:
            return None
        if t.kind == "enum":
            size = t.info.under.bits
        elif t.kind == "int":
            size = t.bits
        else:
            return None
        if b.get("isBitfield"):
            w = next((int(x["value"]) for x in kids(b) if x.get("kind") == "ConstantExpr" and "value" in x), None)
            if w is None or w <= 0:
                return None
            if off % size + w > size:
                off += size - off % size
        else:
            w = size
            off += (-off) % size
        out[b["id"]] = (off, w, t)
        off += w
    return out if off <= word.bits else None


def plain_bases(r):
    """--ekf-types: a struct without member functions whose bases have none either (`struct
    gps_elements : EKF_obs_element_t`, AP_NavEKF3_core.h:608): a plain struct whose fields are its
    bases' fields, then its own (as C++ lays them out)."""
    return all(not b.methods and not any(c.get("kind") in ("CXXMethodDecl", "CXXConstructorDecl") and not c.get("isImplicit")
                                         for c in kids(b.node)) for b in r.chain())


def erased_member(c):
    """--ring-buffers: is FieldDecl c a `void *` data member (the storage of a type-erased container)?"""
    q = c.get("type", {})
    return q.get("desugaredQualType", q.get("qualType", "")).strip() == "void *" and not c.get("isBitfield")


def rb_strip(n):
    """An expression without parentheses and casts (implicit and explicit)."""
    while n.get("kind") in ("ParenExpr", "ConstantExpr", "ImplicitCastExpr", "CStyleCastExpr", "CXXStaticCastExpr",
                            "CXXFunctionalCastExpr", "ExprWithCleanups", "MaterializeTemporaryExpr") and kids(n):
        n = kids(n)[0]
    return n


def monomorphize_buffers(u, reject):
    """--ring-buffers (PORT-PLAN.md F12): a class C with a `void *` data member B (its storage) and a
    `const uint8_t` member E that its constructor sets from its parameter (the element size), used
    only through class template specializations W<T> deriving from it whose constructor passes
    `sizeof(T)`: each W<T> gets a copy of C in which B is an `Array T` with a flag `B'alloc` (B is not
    a null pointer). C's member functions are then translated for W<T> (as inherited member
    functions are), and the forms below are recognized in them (Body.rb_*); any other use of B, of a
    `void *` parameter or of an accessor is rejected. Accessors: member functions of C returning
    `void *` whose body is `return (void*)(((uint8_t*)B)+i*uint32_t(E));` or `return acc(i);` for
    an accessor acc (i their one parameter): a call is the element at index i."""
    erased = {r.id: r for r in u.records if any(f.category == "erased" for f in r.fields)}
    for c in erased.values():
        c.rb_acc = {}
        try:
            ef = [f for f in c.fields if f.category == "erased"]
            if len(ef) != 1:
                raise Reject(c.node, "type-erased class `%s` with %d `void *` members (one is translated)" % (c.cxx, len(ef)))
            B = ef[0]
            E = None
            for m in c.methods:
                if m.get("kind") != "CXXConstructorDecl":
                    continue
                ps = [p for p in kids(u.body_of(m) or m) if p.get("kind") == "ParmVarDecl"]
                for ini in kids(u.body_of(m) or m):
                    if ini.get("kind") == "CXXCtorInitializer" and kids(ini) and len(ps) == 1:
                        e = rb_strip(kids(ini)[0])
                        if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] == ps[0]["id"]:
                            f = c.field_by_id(ini.get("anyInit", {}).get("id"))
                            if f is not None and f.category == "state" and f.t.kind == "int" and f.t.bits == 8 and not f.t.signed:
                                E = f
            if E is None:
                raise Reject(c.node, "type-erased class `%s` without a `uint8_t` member set from its constructor's parameter (the element size)" % c.cxx)
            c.rb_E = E
            vms = [m for m in c.methods if m.get("kind") == "CXXMethodDecl" and m["type"]["qualType"].split("(")[0].strip() == "void *"]
            # the accessors that forward to another (in any order of declaration): until none is added
            for m in sorted(vms, key=lambda m: 0 if re.sub(r"\s+", "", u.text_of(kids(next((x for x in kids(u.body_of(m) or {}) if x.get("kind") == "CompoundStmt"), {"inner": [{}]}))[0]) or "").startswith("return(void*)") else 1):
                body = u.body_of(m)
                ps = [p for p in kids(body or m) if p.get("kind") == "ParmVarDecl"]
                cs = next((x for x in kids(body or {}) if x.get("kind") == "CompoundStmt"), None)
                st = kids(cs) if cs else []
                if len(ps) != 1 or len(st) != 1 or st[0].get("kind") != "ReturnStmt" or not kids(st[0]):
                    raise Reject(m, "member function `%s` of type-erased class `%s` returning `void *` that is not an element accessor" % (m.get("name"), c.cxx))
                text = re.sub(r"\s+", "", u.text_of(kids(st[0])[0]) or "")
                if text == "(void*)(((uint8_t*)%s)+%s*uint32_t(%s))" % (B.name, ps[0]["name"], E.name):
                    c.rb_acc[m["id"]] = "offset"
                    continue
                e = rb_strip(kids(st[0])[0])
                if e.get("kind") == "CXXMemberCallExpr" and len(kids(e)) == 2:
                    tgt = u.canonical(u.decl(strip_parens(kids(e)[0]).get("referencedMemberDecl")))
                    a = rb_strip(kids(e)[1])
                    if tgt is not None and tgt["id"] in c.rb_acc and a.get("kind") == "DeclRefExpr" and a["referencedDecl"]["id"] == ps[0]["id"]:
                        c.rb_acc[m["id"]] = "offset"
                        continue
                raise Reject(m, "member function `%s` of type-erased class `%s` returning `void *` that is not an element accessor (`return (void*)(((uint8_t*)%s)+i*uint32_t(%s));` or a call of one)" % (m.get("name"), c.cxx, B.name, E.name))
        except Reject as e:
            reject(e)
            c.failed = True
    for r in u.records:
        if not r.bases or r.bases[0].id not in erased or getattr(r.bases[0], "failed", False):
            continue
        c = r.bases[0]
        try:
            targs = [x for x in kids(r.node) if x.get("kind") == "TemplateArgument" and x.get("type")]
            if r.node.get("kind") != "ClassTemplateSpecializationDecl" or len(targs) != 1:
                raise Reject(r.node, "class `%s` derived from type-erased class `%s` that is not a class template specialization with one type argument" % (r.cxx, c.cxx))
            tq = targs[0]["type"]
            T = parse_type_str(tq["qualType"], tq.get("desugaredQualType", tq["qualType"]), r.node)
            if not (T.is_scalar() or T.kind == "record"):
                raise Reject(r.node, "type-erased container of `%s`" % T.cname)
            ok = False
            for m in r.methods:
                if m.get("kind") != "CXXConstructorDecl":
                    continue
                for ini in kids(u.body_of(m) or m):
                    if ini.get("kind") == "CXXCtorInitializer" and "baseInit" in ini and kids(ini):
                        e = rb_strip(kids(ini)[0])
                        if e.get("kind") == "CXXConstructExpr" and len(kids(e)) == 1:
                            a = rb_strip(kids(e)[0])
                            if a.get("kind") == "UnaryExprOrTypeTraitExpr" and a.get("name") == "sizeof" and "argType" in a:
                                at = a["argType"]
                                if parse_type_str(at["qualType"], at.get("desugaredQualType", at["qualType"]), a) == T:
                                    ok = True
            if not ok:
                raise Reject(r.node, "class `%s` derived from type-erased class `%s` without a constructor passing `sizeof(%s)`" % (r.cxx, c.cxx, T.cname))
            cl = copy.copy(c)
            cl.fields = []
            buf = alloc = None
            for f in c.fields:
                g = copy.copy(f)
                g.owner = cl
                if f.category == "erased":
                    g.category, g.t, g.rb_role = "state", CType("array", elem=T, n=0), "buf"
                    g.rb_doc = "/-- `%s` of `%s` (`%s`): the elements (`calloc(size, elsize)`), as `%s` (--ring-buffers). -/" % (
                        comment_safe(cpp_var_decl(f.decl)), comment_safe(c.cxx), comment_safe(where_of(u, f.decl)), comment_safe(T.cname))
                    buf = g
                    a = copy.copy(f)
                    a.owner, a.category, a.t, a.rb_role = cl, "state", BOOL, "alloc"
                    a.lean, a.id, a.name = f.lean + "'alloc", "%s'alloc" % f.id, f.name + " != nullptr"
                    a.rb_doc = "/-- `%s != nullptr` (--ring-buffers): the elements are allocated. -/" % comment_safe(f.name)
                    alloc = a
                    cl.fields += [g, a]
                    continue
                cl.fields.append(g)
            cl.rb = {"elem": T, "buf": buf, "alloc": alloc, "E": next(g for g in cl.fields if g.id == c.rb_E.id), "acc": c.rb_acc}
            cl.fields_ready = False
            r.bases = [cl] + r.bases[1:]
        except Reject as e:
            reject(e)
            r.failed = True


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
        # (an absolute `-I` directory that does not exist, such as the reference build's
        # modules/lwip/src/include without the submodule, is made portable too)
        if arg.startswith(pre) and len(arg) > len(pre) and \
                (os.path.exists(arg[len(pre):]) or (pre == "-I" and os.path.isabs(arg[len(pre):]))):
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


def strip_casts(e, kinds=("NoOp", "LValueToRValue", "ArrayToPointerDecay", "IntegralCast", "FunctionToPointerDecay")):
    """e without parentheses and the implicit casts of the given kinds."""
    e = strip_parens(e)
    while e.get("kind") == "ImplicitCastExpr" and e.get("castKind") in kinds and kids(e):
        e = strip_parens(kids(e)[0])
    return e


def byte_view_fields(u):
    """--mavlink: the ids of array data members of wider integers that the code uses only as bytes:
    every reference is `(char *)&x.f[0]` (`_MAV_PAYLOAD(msg)` = `(const char *)(&((msg)->payload64[0]))`,
    mavlink_types.h): the member is stored as its bytes (`Array UInt8` of its size), little endian, so the
    byte pointer is (the bytes, offset 0)."""
    uses = {}
    for m in list(u.ids.values()):
        if m.get("kind") != "MemberExpr" or not m.get("referencedMemberDecl"):
            continue
        f = u.decl(m["referencedMemberDecl"])
        if f is None or f.get("kind") != "FieldDecl":
            continue
        q = f["type"].get("desugaredQualType", f["type"]["qualType"])
        mm = re.match(r"^(unsigned long long|unsigned long|unsigned int|unsigned short|long long|long|int|short|uint\d+_t|int\d+_t)\s*\[(\d+)\]$", q.strip())
        if not mm or mm.group(1) in ("uint8_t", "int8_t"):
            continue
        ok = False
        up = u.parent.get(m["id"])
        if up is not None and up.get("kind") == "ImplicitCastExpr" and up.get("castKind") == "ArrayToPointerDecay":
            sub = u.parent.get(up["id"])
            if sub is not None and sub.get("kind") == "ArraySubscriptExpr" and kids(sub)[0] is up and \
                    strip_casts(kids(sub)[1]).get("kind") == "IntegerLiteral" and strip_casts(kids(sub)[1]).get("value") == "0":
                amp = u.parent.get(sub["id"])
                while amp is not None and amp.get("kind") == "ParenExpr":
                    amp = u.parent.get(amp["id"])
                if amp is not None and amp.get("kind") == "UnaryOperator" and amp.get("opcode") == "&":
                    cst = u.parent.get(amp["id"])
                    while cst is not None and cst.get("kind") == "ParenExpr":
                        cst = u.parent.get(cst["id"])
                    ok = cst is not None and cst.get("kind") in ("CStyleCastExpr", "CXXReinterpretCastExpr") and \
                        re.match(r"^(const )?(char|unsigned char|uint8_t) \*$", cst["type"]["qualType"].strip()) is not None
        uses.setdefault(f["id"], []).append(ok)
    return {fid for fid, oks in uses.items() if oks and all(oks)}


def opt_return_type(d):
    """--mavlink: the `Option T` type of a function returning `const T *` (T a translated plain struct): each
    `return` returns the null pointer (`none`) or `&x` of a constant (`some x`), else None."""
    q = d["type"]["qualType"].split("(")[0].strip()
    dq = d["type"].get("desugaredQualType", d["type"]["qualType"]).split("(")[0].strip()
    sp = Body(CURRENT_UNIT[0]).struct_pointee(q, dq, d) if CURRENT_UNIT[0] is not None else None
    if sp is None or not sp[1]:
        return None
    t = CType("opt", elem=sp[0])
    return t


def global_accessor(u, d):
    """--mavlink: (global id, index of the parameter that indexes it, or None) if d's body is `return &g[p];`
    or `return &g;` for a mutable file-scope variable g (registered in u.globals) and a parameter p."""
    body = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
    if body is None or len(kids(body)) != 1 or kids(body)[0].get("kind") != "ReturnStmt" or not kids(kids(body)[0]):
        return None
    e = strip_casts(kids(kids(body)[0])[0])
    if e.get("kind") != "UnaryOperator" or e.get("opcode") != "&":
        return None
    e = strip_casts(kids(e)[0])
    params = [p["id"] for p in kids(d) if p.get("kind") == "ParmVarDecl"]
    if e.get("kind") == "DeclRefExpr" and e["referencedDecl"]["id"] in u.globals:
        return e["referencedDecl"]["id"], None
    if e.get("kind") == "ArraySubscriptExpr":
        g, i = strip_casts(kids(e)[0]), strip_casts(kids(e)[1])
        if g.get("kind") == "DeclRefExpr" and g["referencedDecl"]["id"] in u.globals and \
                i.get("kind") == "DeclRefExpr" and i["referencedDecl"]["id"] in params:
            return g["referencedDecl"]["id"], params.index(i["referencedDecl"]["id"])
    return None


def translate(path, ns, headers=(), externs=None, clang_extra=(), options="", lib_dirs=()):
    ROOT_NS[0] = ns
    tree, typedefs = run_clang(path, clang_extra, keep=(path, headers, lib_dirs))
    collect_typedefs(tree, typedefs)
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
    if FRONT_ENDS[0]:
        # --front-ends: the declarations inside a named namespace of a translated file are translated as
        # those at file scope (the stand-ins' `namespace SITL { class SIM ... }`, `SIM::SIM()` defined
        # inside it, `namespace AP { SITL::SIM *sitl() }`); their names keep the namespace
        def flat(ds):
            for d in ds:
                if d.get("kind") == "NamespaceDecl" and d.get("name") and d.get("name") != "std":
                    yield from flat([c for c in kids(d) if u.in_set(c)])
                else:
                    yield d
        top = list(flat(top))
    if MAVLINK[0] or OUTPUT_FN:
        # --mavlink: the declarations of `extern "C" { ... }` blocks (the generated MAVLink headers, checksum.h)
        # are translated as those at file scope; also with --output-fn (Phase 5c: the MAVLink enumerations and
        # message structs of an estimator class's sender, `EKF_STATUS_FLAGS`, `mavlink_ekf_status_report_t`)
        def unlink(ds):
            for d in ds:
                if d.get("kind") == "LinkageSpecDecl" and not d.get("isImplicit"):
                    yield from unlink([c for c in kids(d) if u.in_set(c)])
                else:
                    yield d
        top = list(unlink(top))
    if SURVEY[0] is not None:
        SURVEY[0] = reject
    collect_types(u, top, reject)
    # the out-of-line definitions of static data members, by the in-class declaration they define
    u.static_defs = {d["previousDecl"]: d for d in top if d.get("kind") == "VarDecl" and d.get("parentDeclContextId")
                     and d.get("previousDecl") and non_attr(kids(d))}
    if MAVLINK[0]:
        u.byte_fields = byte_view_fields(u)
    fill_records(u, reject)
    for r in u.records:
        if r.lean == ns:
            reject(Reject(r.node, "class `%s` has the name of the file's namespace (pass another --namespace)" % r.cxx))
    for d in top:
        if d.get("kind") in ("CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl") and \
                any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            u.method_bodies[d.get("mangledName")] = d
    if RING_BUFFERS[0]:
        monomorphize_buffers(u, reject)

    # free functions (and specializations of function templates), constants, names
    defs, consts, names = [], [], {}

    def add_function(d):
        if not any(c.get("kind") == "CompoundStmt" for c in kids(d)):
            return
        if d.get("variadic") and not C_STRINGS[0] and REACHABLE[0]:
            return          # --reachable: rejected only if called (`rprintf`, AP_DAL.cpp:576, is not)
        if d.get("variadic") and not C_STRINGS[0]:
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
            if k == "FunctionDecl" and WORLD[0] and accessor_shape(d):
                u.accessors[d["id"]] = d
            elif k == "FunctionDecl":
                add_function(d)
            elif k == "FunctionTemplateDecl" and (lib or instantiated(d)):
                for c in kids(d):
                    if c.get("kind") == "FunctionDecl" and c.get("mangledName"):
                        add_function(u.decl(c["id"]))
            elif k == "VarDecl" and C_MODE[0] and d.get("storageClass") == "extern" and not non_attr(kids(d)):
                # C: `extern hidden const struct exp2f_data __exp2f_data;` (musl's exp2f_data.h): a
                # declaration of a constant defined in the translated files; uses resolve to the definition
                u.extern_vars[d["id"]] = d["name"]
            elif k == "VarDecl" and d.get("storageClass") == "extern" and not kids(d) and not lib and WORLD[0] and \
                    not d["type"]["qualType"].startswith("const ") and not d["type"]["qualType"].rstrip().endswith(("&", "*")) and \
                    ctype_of(d).kind == "record" and ctype_of(d).info.kind == "class":
                continue        # `extern Back back_obj;`: a declaration of a World object defined below (its definition names it)
            elif k == "VarDecl" and d.get("storageClass") == "extern" and not kids(d) and (not lib or FRONT_ENDS[0]):
                if lib:
                    try:
                        t, ref = decl_type(d)
                    except Reject:
                        continue
                    if t.kind == "boundary":
                        u.boundary_globals[d["id"]] = d["name"]     # (--front-ends: also declared in a library file)
                    continue
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
                        if not hasattr(rec, "var_info_by"):
                            rec.var_info_by = {}
                        rec.var_info_by[d.get("previousDecl", d["id"])] = d     # (NavEKF3 has two: var_info, var_info2)
                    continue
                if MEMBER_OBJECTS[0] and WORLD[0] and not lib and d.get("parentDeclContextId") and static_object_class(d) is not None:
                    # --member-objects: the out-of-line definition of a static data member of a translated class
                    # (`NavEKF3 AP_AHRS_NavEKF3::EKF3;`, AP_AHRS_NavEKF3.cpp:13) is a World object named after the member
                    u.world.append({"name": lean_field(d["name"], d), "decl": d, "rec": static_object_class(d),
                                    "cxx": qualified_name(u, d)})
                    u.world_ids[d["id"]] = u.world[-1]["name"]
                    if d.get("previousDecl"):
                        u.world_ids[d["previousDecl"]] = u.world[-1]["name"]    # the declaration in the class
                    continue
                if d.get("parentDeclContextId"):
                    continue                    # the out-of-line definition of a static member
                if not lib and qualified_name(u, d) in DROP:
                    u.dropped[d["id"]] = qualified_name(u, d)
                    continue                    # a file-scope object left out (--drop: a singleton's instance)
                q = d["type"]["qualType"]
                if MAVLINK[0] and not lib and not (q.startswith("const ") or d.get("constexpr")) and d.get("storageClass") != "extern" and \
                        not (MISSION[0] and WORLD[0] and ctype_of(d).kind == "record" and ctype_of(d).info.kind == "class"):
                    # (--mission --world: an object of a class is a World object, below)
                    # --mavlink: a mutable file-scope variable (the channel buffers and status, `mavlink_system`): state,
                    # a hidden reference parameter of every function that reaches it, starting at its initializer or zero
                    u.globals[d["id"]] = {"lean": lean_ident(d["name"], d), "t": ctype_of(d), "decl": d, "ns": ns}
                    if d.get("previousDecl"):
                        u.global_alias[d["previousDecl"]] = d["id"]     # its `extern` declaration (GCS_MAVLink.h)
                    continue
                if WORLD[0] and not lib and not q.startswith("const ") and d.get("storageClass") != "extern":
                    wt = ctype_of(d)
                    if wt.kind == "record" and wt.info.kind == "class":
                        u.world.append({"name": lean_field(d["name"], d), "decl": d, "rec": wt.info})
                        u.world_ids[d["id"]] = u.world[-1]["name"]
                        if d.get("previousDecl"):
                            u.world_ids[d["previousDecl"]] = u.world[-1]["name"]    # its `extern` declaration
                        continue
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
                    if WORLD[0] and accessor_shape(c):
                        u.accessors[c["id"]] = c        # `AP::rtc()`: its calls are the World object it returns
                        continue
                    if WORLD_PTRS[0] and c.get("kind") == "FunctionDecl" and any(x.get("kind") == "CompoundStmt" for x in kids(c)):
                        add_function(c)         # --world-pointers: a function of a namespace (the HAL stand-in's `AP_HAL::micros64()`)
                        continue
                    for x in walk(c):
                        if any(y.get("kind") == "CompoundStmt" for y in kids(x)) or x.get("kind") in ("VarDecl", "CXXRecordDecl", "EnumDecl"):
                            raise Reject(x, "definition inside namespace `%s` (file-scope definitions only)" % d.get("name", ""))
            elif k == "LinkageSpecDecl" and d.get("isImplicit"):
                continue                        # clang's implicit declaration of a builtin it was asked to call
            elif k == "LinkageSpecDecl":
                raise Reject(d, "`extern \"C\"` block")
            else:
                raise Reject(d, "declaration `%s`" % k)
        except Reject as r:
            reject(r)
    if MAVLINK[0]:
        # --mavlink: `mavlink_status_t *mavlink_get_channel_status(uint8_t chan) { return &chan_status[chan]; }`:
        # not translated; a call is the element of the file-scope array (an lvalue)
        for d in list(defs):
            acc = global_accessor(u, d)
            if acc is not None:
                u.gaccessors[d.get("mangledName")] = acc
                defs.remove(d)
    u.fn_by_name = names
    plain = {lean_ident(nm, ds[0]) for nm, ds in names.items() if len(ds) == 1}
    for nm, ds in names.items():
        taken = set()
        for d in ds:
            name = lean_ident(nm, d) + ("_" + Context.sig_suffix(d) if len(ds) > 1 else "")
            while name in taken or (len(ds) > 1 and name in plain):
                name += "_"
            taken.add(name)
            u.fn_names[d["id"]] = name
    for r in u.records:
        for c in r.statics:
            try:
                dc = u.static_defs.get(c["id"], c) if not non_attr(kids(c)) else c
                u.consts[c["id"]] = {"lean": lean_field(c["name"], c), "ns": r.lean, "t": ctype_of(dc), "decl": dc}
            except Reject as e:
                if FRONT_ENDS[0] and r.lib:
                    continue    # --front-ends: a constant of a library class of a type outside the subset (a use is rejected)
                reject(e)
    deferring[0] = False
    if MEMBER_PTRS[0] and WORLD_PTRS[0]:
        member_tags(u, reject)      # (before the field defaults: `backends_and_estimates[]`'s names the tags)
    for r in u.records:
        if not r.lib:
            try:
                u.ensure_fields(r)
            except Reject as e:
                reject(e)

    if WORLD[0] and EKF_TYPES[0]:
        if FRONT_ENDS[0]:
            svars = {c["id"]: r for r, c in u.static_vars}
            for d in top:
                if not u.is_lib(d):
                    for n in walk(d):
                        rid = (n.get("referencedDecl") or {}).get("id") if n.get("kind") == "DeclRefExpr" else \
                            n.get("referencedMemberDecl") if n.get("kind") == "MemberExpr" else None
                        if rid in svars:
                            u.static_used.add(svars[rid].id)
                elif INS_GPS[0] and d.get("kind") == "VarDecl" and d.get("previousDecl") in svars and zero_initializer(d):
                    # --ins-gps: `uint8_t AP_InertialSensor_SITL::bus_id = 0;` (the IMU stand-in, a library file): the
                    # out-of-line definition of a mutable static member of a library class, zero: a World field
                    u.static_used.add(svars[d["previousDecl"]].id)
        world_statics(u, reject)
    if WORLD_PTRS[0]:
        prescan_heap(u)
    if WORLD[0]:
        resolve_world(u, reject)
    if FRONT_ENDS[0] and WORLD[0]:
        # --front-ends: a reference to the out-of-line definition of a singleton pointer (`SIM *SIM::_singleton
        # = nullptr;` and its uses in `SIM::SIM()`, defined in the same file) is the pointer
        for x in list(u.ids.values()):
            if x.get("kind") == "VarDecl" and x.get("previousDecl") in u.singleton_ptrs and x["id"] not in u.singleton_ptrs:
                u.singleton_ptrs[x["id"]] = u.singleton_ptrs[x["previousDecl"]]
                if x["previousDecl"] in u.heap_ptr:
                    u.heap_ptr[x["id"]] = u.heap_ptr[x["previousDecl"]]
    for d in consts + [c for r in u.records if not r.lib for c in r.statics]:
        if d["id"] in u.consts:
            try:
                u.const_item(d["id"])
            except Reject as r:
                reject(r)
    # (--c-strings: a function with a pointer parameter to a class is translated for the class of the
    # object its calls pass, object_pointer_spec: after the functions that call it)
    later = [d for d in defs if C_STRINGS[0] and object_pointer_params(d)]
    for d in ([] if REACHABLE[0] else [x for x in defs if x not in later] + later):     # (--reachable: on first call)
        try:
            if d in later and d["id"] not in u.obj_param_spec and d["id"] not in u.free_results:
                p0 = object_pointer_params(d)[0]
                raise Reject(p0, "pointer parameter `%s` to a class, in a function that no translated function calls (it is translated for the class of the object its calls pass)" % p0.get("name"))
            u.free_result(d, d)
        except Reject as r:
            reject(r)
    for r in u.records:
        if r.lib:
            continue
        for m in r.methods:
            if WORLD[0] and m.get("storageClass") == "static" and u.body_of(m) is not None and accessor_shape(u.body_of(m)):
                u.accessors[m["id"]] = u.body_of(m)     # `static AP_RTC *get_singleton()`: not translated, its calls are paths
                continue
            if AHRS_EXT[0] and m.get("storageClass") == "static" and Body(u).static_boundary_return(m) is not None:
                continue        # --ahrs-ext: translated at each call, in the caller (`AP_AHRS_Backend::get_EAS2TAS`)
            if m.get("storageClass") == "static" and u.body_of(m) is not None and m["id"] not in u.dropped:
                try:
                    u.static_result(r, m, m)
                except Reject as e:
                    reject(e)
    for r in u.records:
        if r.lib:
            continue
        if WORLD[0] and r.id not in u.world_self and any(f.category == "wref" for f in r.all_fields()) and not (KEEP_GOING[0] and EKF_TYPES[0]):
            continue        # references to World objects: translated only as the class of a World object (in a --keep-going survey with --ekf-types: also alone, to list what its member functions need)
        if any(f.category == "erased" for f in r.fields):
            continue        # --ring-buffers: a type-erased container, translated only for its typed wrappers
        if r.kind == "class" and not r.abstract and (KEEP_GOING[0] or not any(x.failed for x in r.chain())):
            if REACHABLE[0]:
                continue        # --reachable: the --use entry points below, and what they call, only
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

    if REACHABLE[0] and WORLD[0]:
        # the constructors of the file-scope objects (World.init calls them; nothing else may)
        for w in u.world:
            if w.get("static") or w.get("ctor") is None:
                continue
            try:
                u.context(w["rec"], w["decl"]).ctor(w["ctor"], top=True, node=w["decl"])
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
        if SURVEY[0] is not None and os.environ.get("CPP2LEAN_SURVEY_METHODS"):
            # --survey: the translated member functions as they are (rejected statements left out), for
            # measurements on functions that translate but for a few statements (not a translation)
            with open(os.environ["CPP2LEAN_SURVEY_METHODS"], "w") as fh:
                for ctx in u.contexts.values():
                    for res in ctx.results.values():
                        if res.lines:
                            fh.write("-- %s.%s\n%s\n%s\n\n" % (ctx.rec.lean, res.lean, res.header, "\n".join("  " + l for l in res.lines)))
        sys.exit(2)
    return emit(u, ns, shown, list(u.const_items.values()), options)


def static_object_class(d):
    """--member-objects: the RecordInfo of a static data member (or its out-of-line definition) whose type is
    a translated class (not a pointer, reference, array or const object), else None."""
    if d.get("storageClass") != "static" and not d.get("parentDeclContextId"):
        return None
    q = d.get("type", {}).get("qualType", "")
    if q.startswith("const ") or "*" in q or "&" in q or "[" in q:
        return None
    try:
        t = ctype_of(d)
    except Reject:
        return None
    return t.info if t.kind == "record" and t.info.kind == "class" else None


def world_statics(u, reject):
    """--ekf-types --world: each mutable static data member of a translated class whose type is a
    number or an array of numbers is a field of the World named `Class'member`, zero at the start (its
    definition has no initializer: static storage is zero-filled); a use of it in a member function
    is that field."""
    for r, c in u.static_vars:
        if FRONT_ENDS[0] and r.lib and r.id not in u.static_used:
            continue        # --front-ends: a static member of a library class that no translated code names
        try:
            t = ctype_of(c)
            if not (t.is_scalar() or (t.kind == "array" and t.elem.is_scalar())):
                raise Reject(c, "mutable static data member `%s` of type `%s` (numbers and arrays of numbers only)" % (c["name"], t.cname))
            dd = u.static_defs.get(c["id"])
            if dd is not None and non_attr(kids(dd)) and not (FRONT_ENDS[0] and zero_initializer(dd)):
                raise Reject(dd, "mutable static data member `%s` with an initializer" % c["name"])
            name = "%s'%s" % (r.name, lean_field(c["name"], c))
            u.world.append({"name": name, "decl": c, "rec": None, "t": t, "static": r, "ctor": None, "args": []})
            u.world_ids[c["id"]] = name
            for x in u.ids.values():        # its out-of-line definition (with or without an initializer)
                if x.get("kind") == "VarDecl" and x.get("previousDecl") == c["id"]:
                    if non_attr(kids(x)) and not (FRONT_ENDS[0] and zero_initializer(x)):
                        raise Reject(x, "mutable static data member `%s` with an initializer" % c["name"])
                    u.world_ids[x["id"]] = name
        except Reject as e:
            reject(e)


def accessor_shape(d):
    """A function without parameters whose body is one `return e;` and whose result is a reference
    or a pointer to a class: a candidate singleton accessor (--world)."""
    if d.get("kind") not in ("FunctionDecl", "CXXMethodDecl") or any(c.get("kind") == "ParmVarDecl" for c in kids(d)):
        return False
    rt = d.get("type", {}).get("qualType", "").split("(")[0].strip()
    if not (rt.endswith("&") or rt.endswith("*")):
        return False
    cs = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
    return cs is not None and len(kids(cs)) == 1 and kids(cs)[0].get("kind") == "ReturnStmt" and kids(kids(cs)[0])


def world_object_of_class(u, rec):
    """The one World object whose class is rec or derives from it, else None."""
    hits = [w["name"] for w in u.world if w["rec"] is not None and rec in w["rec"].chain()]
    return hits[0] if len(hits) == 1 else None


def lazy_singleton_getter(u, d):
    """--est-world: the class C if d is `static C *get_singleton() { if (!_singleton) { _singleton = new C(); } return
    _singleton; }` (AP_InertialSensor.cpp:738-744) with `_singleton` a static singleton pointer of C, else None. With a
    file-scope object of C, whose constructor sets `_singleton = this` before anything runs, the branch is never taken:
    the getter is an accessor of that object, and its `new` is not a heap allocation."""
    if d is None or d.get("kind") != "CXXMethodDecl" or any(c.get("kind") == "ParmVarDecl" for c in kids(d)):
        return None
    cs = next((c for c in kids(d) if c.get("kind") == "CompoundStmt"), None)
    if cs is None or len(kids(cs)) != 2 or kids(cs)[0].get("kind") != "IfStmt" or kids(cs)[1].get("kind") != "ReturnStmt":
        return None

    def sptr(e):
        e = strip_object(e)
        while e.get("kind") == "ImplicitCastExpr":
            e = strip_object(kids(e)[0])
        if e.get("kind") != "DeclRefExpr":
            return None
        rid = e["referencedDecl"]["id"]
        if rid not in u.singleton_ptrs:
            rid = (u.decl(rid) or {}).get("previousDecl")      # the out-of-line definition `C *C::_singleton = nullptr;`
        return rid if rid in u.singleton_ptrs else None
    ifs = kids(kids(cs)[0])
    if len(ifs) != 2 or not kids(kids(cs)[1]):
        return None
    pid = sptr(kids(kids(cs)[1])[0])
    cond = strip_object(ifs[0])
    if pid is None or cond.get("kind") != "UnaryOperator" or cond.get("opcode") != "!" or sptr(kids(cond)[0]) != pid:
        return None
    body = ifs[1]
    if body.get("kind") == "CompoundStmt":
        if len(kids(body)) != 1:
            return None
        body = kids(body)[0]
    body = strip_object(body)
    if body.get("kind") != "BinaryOperator" or body.get("opcode") != "=" or sptr(kids(body)[0]) != pid:
        return None
    rec = u.singleton_ptrs[pid]
    nw = strip_object(kids(body)[1])
    while nw.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
        nw = strip_object(kids(nw)[0])
    return rec if heap_class_of_alloc(nw) is rec else None


def lazy_singleton_new(u, n):
    """--est-world: is n the `new C()` of a lazy singleton getter (lazy_singleton_getter) of a class with a
    file-scope object?"""
    f = u.parent.get(n["id"])
    while f is not None and f.get("kind") not in ("CXXMethodDecl", "FunctionDecl", "CXXConstructorDecl"):
        f = u.parent.get(f["id"])
    rec = lazy_singleton_getter(u, f) if f is not None else None
    return rec is not None and any(w["rec"] is not None and rec in w["rec"].chain() for w in u.world)


def accessor_target(u, e, seen=()):
    """The World object a singleton accessor expression denotes: a file-scope object, `*p` or `p`
    of a static `_singleton` pointer, or a call of an accessor; else None."""
    e = strip_object(e)
    k = e.get("kind")
    if k == "UnaryOperator" and e.get("opcode") == "*":
        return accessor_target(u, kids(e)[0], seen)
    if k == "ImplicitCastExpr" and e.get("castKind") in ("NoOp", "LValueToRValue", "UncheckedDerivedToBase", "DerivedToBase"):
        return accessor_target(u, kids(e)[0], seen)
    if k == "DeclRefExpr":
        rid = e["referencedDecl"]["id"]
        if rid in u.world_ids:
            return u.world_ids[rid]
        if rid in u.singleton_ptrs:
            return world_object_of_class(u, u.singleton_ptrs[rid])
        return None
    if k in ("CallExpr", "CXXMemberCallExpr") and not kids(e)[1:]:
        c = strip_object(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_object(kids(c)[0])
        did = (c.get("referencedDecl") or {}).get("id") or c.get("referencedMemberDecl")
        d = u.accessors.get(did)
        if d is None:
            d0 = u.decl(did) if did else None
            d = u.accessors.get(d0.get("previousDecl")) if d0 else None
            if d is None and d0 is not None:
                d = next((a for a in u.accessors.values() if a.get("mangledName") and a.get("mangledName") == d0.get("mangledName")), None)
            if d is None and d0 is not None and FRONT_ENDS[0] and u.is_lib(d0):
                b = u.body_of(d0) if d0.get("kind") == "CXXMethodDecl" else None
                if b is not None and accessor_shape(b):
                    d = b       # --front-ends: `static SIM *get_singleton() { return _singleton; }` of a library class
                if EST_WORLD[0] and b is not None and d is None:
                    lz = lazy_singleton_getter(u, b)
                    if lz is not None and world_object_of_class(u, lz) is not None and did not in seen:
                        return world_object_of_class(u, lz)
        if d is None or did in seen:
            return None
        cs = next(c for c in kids(d) if c.get("kind") == "CompoundStmt")
        return accessor_target(u, kids(kids(cs)[0])[0], seen + (did,))
    return None


def heap_class_of_alloc(e):
    """--world-pointers: the RecordInfo of the class a `new C(...)` (not an array `new`, not placement)
    or a `(C *)f(...)` of a --heap-alloc function allocates, else None."""
    k = e.get("kind")
    if k == "CXXNewExpr" and not e.get("isArray"):
        t = world_ptr_type(e.get("type", {}).get("desugaredQualType", e.get("type", {}).get("qualType", "")))
        return t.info if t is not None else None
    if k in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr") and kids(e):
        c = strip_parens(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_parens(kids(c)[0])
        if heap_alloc_call(c):
            t = world_ptr_type(e.get("type", {}).get("desugaredQualType", e.get("type", {}).get("qualType", "")))
            return t.info if t is not None else None
    return None


def heap_alloc_call(c):
    """--world-pointers: is c a call of a --heap-alloc function (`malloc(...)`, `dal.malloc_type(...)`)?"""
    if c.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or not kids(c):
        return False
    f = strip_parens(kids(c)[0])
    while f.get("kind") == "ImplicitCastExpr":
        f = strip_parens(kids(f)[0])
    name = (f.get("referencedDecl") or {}).get("name") or f.get("name")
    if name is None:
        return False
    return any(h == name or h.endswith("::" + name) for h in HEAP_ALLOC)


def prescan_heap(u):
    """--world-pointers: the classes of the objects created by `new` (and by placement new into
    memory of a --heap-alloc function) anywhere in the translated program: each gets a heap slot
    array in the World. And the static pointer members of classes without a file-scope object
    (`static Store *_singleton`, assigned the object a `get_singleton()` allocates): World fields."""
    seen = set()
    for n in walk(u.tree):
        if not isinstance(n, dict):
            continue
        rec = heap_class_of_alloc(n)
        if rec is not None and EST_WORLD[0] and n.get("kind") == "CXXNewExpr" and lazy_singleton_new(u, n):
            continue        # --est-world: the never-taken allocation of AP_InertialSensor::get_singleton (lazy_singleton_getter)
        if rec is not None and n.get("kind") != "CXXNewExpr":
            u.heap_placement.add(rec.id)
        if rec is not None and rec.id not in seen and not rec.semaphore:
            seen.add(rec.id)
            u.heap.append(rec)
    seenf = set()
    for n in walk(u.tree):
        if isinstance(n, dict) and n.get("kind") == "CallExpr":
            fb = functor_bind(u, n)
            if fb is not None and (fb[0].id, fb[1]["id"]) not in seenf:
                seenf.add((fb[0].id, fb[1]["id"]))
                u.funcs.append(fb)
    for pid, rec in u.singleton_ptrs.items():
        if world_object_of_class(u, rec) is None:
            u.heap_ptr[pid] = "%s'_singleton" % rec.lean.replace(".", "_")


def functor_bind(u, n):
    """--world-pointers: (class RecordInfo, method decl) of a call `Functor<void>::bind<T, &T::m>(obj)`
    (FUNCTOR_BIND, FUNCTOR_BIND_MEMBER), else None."""
    if n.get("kind") != "CallExpr" or n.get("type", {}).get("qualType") != "Functor<void>" or not kids(n):
        return None
    f = strip_parens(kids(n)[0])
    while f.get("kind") == "ImplicitCastExpr":
        f = strip_parens(kids(f)[0])
    ref = f.get("referencedDecl") or {}
    if ref.get("name") != "bind":
        return None
    d = u.decl(ref.get("id"))
    if d is None:
        return None
    targs = [c for c in kids(d) if c.get("kind") == "TemplateArgument"]
    if len(targs) != 2 or "decl" not in targs[1]:
        return None
    tname = norm_template_args(strip_tag(targs[0].get("type", {}).get("qualType", ""))[0])
    rec = RECORDS.get(tname)
    if rec is None:
        rs = [r for k, r in RECORDS.items() if k.split("::")[-1] == tname]
        rec = rs[0] if len(rs) == 1 else None
    m = u.decl(targs[1]["decl"]["id"])
    if rec is None or m is None:
        return None
    return rec, u.canonical(m) or m


def functor_ctor(rec, m):
    """--world-pointers: the `WFun` constructor of functors bound to method m of class rec."""
    return "%s_%s" % (rec.lean.replace(".", "_"), m.get("name"))


def wfun_block(u, wns):
    """--world-pointers: `inductive WFun`, the functors of the program (AP_HAL::MemberProc): empty, or
    one of the (class, member function) pairs that FUNCTOR_BIND binds, with the object's pointer."""
    lines = ["/-- A `Functor<void>` (AP_HAL::MemberProc) of the program (--world-pointers): empty, or a member function",
             "of a class bound to an object, one constructor per `FUNCTOR_BIND` of the program (closed world). -/",
             "inductive WFun where", "  | null"]
    for rec, m in u.funcs:
        lines.append("  | %s (obj : WPtr)" % functor_ctor(rec, m))
    lines.append("  deriving DecidableEq, Inhabited")
    lines += ["", "/-- A name of the functor (for the difftest: `null`, or the constructor `@` the object's name). -/",
              "def WFun.name : WFun → String", "  | .null => \"null\""]
    for rec, m in u.funcs:
        lines.append("  | .%s o => \"%s@\" ++ o.name" % (functor_ctor(rec, m), functor_ctor(rec, m)))
    return {"key": (-2, "", 0, 1), "ns": wns, "lines": lines, "deps": {("wptr",)}, "id": ("wfun",)}


def heap_field(rec):
    """--world-pointers: the World field holding the heap objects of class rec."""
    return "heap'" + rec.lean.replace(".", "_")


def heap_singleton_field(u, rec):
    """--world-pointers: the World field of the static singleton pointer of rec (`AP_DAL::_singleton`) if
    rec is a heap class without a file-scope object whose objects are reached through it, else None."""
    if rec is None or rec not in u.heap or world_object_of_class(u, rec) is not None:
        return None
    for pid, fld in u.heap_ptr.items():
        if u.singleton_ptrs.get(pid) is rec:
            return fld
    return None


def heap_singleton_of(u, e, seen=()):
    """--world-pointers: the RecordInfo of the heap singleton an expression denotes (`AP::dal()`,
    `*AP_DAL::get_singleton()`: an accessor, then `*` of a call of a static member function returning a
    pointer to a class with a heap singleton pointer), else None."""
    e = strip_object(e)
    while e.get("kind") == "InitListExpr" and len(kids(e)) == 1:
        e = strip_object(kids(e)[0])        # `dal{AP::dal()}`
    k = e.get("kind")
    if k == "UnaryOperator" and e.get("opcode") == "*":
        c = strip_object(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_object(kids(c)[0])
        if c.get("kind") == "CallExpr" and not kids(c)[1:]:
            t = world_ptr_type(c.get("type", {}).get("qualType", ""))
            if t is not None and heap_singleton_field(u, t.info) is not None:
                return t.info
        return None
    if k in ("CallExpr", "CXXMemberCallExpr") and not kids(e)[1:]:
        c = strip_object(kids(e)[0])
        while c.get("kind") == "ImplicitCastExpr":
            c = strip_object(kids(c)[0])
        did = (c.get("referencedDecl") or {}).get("id") or c.get("referencedMemberDecl")
        d = u.accessors.get(did)
        if d is None and did:
            d0 = u.decl(did)
            d = u.accessors.get(d0.get("previousDecl")) if d0 else None
            if d is None and d0 is not None:
                d = next((a for a in u.accessors.values() if a.get("mangledName") and a.get("mangledName") == d0.get("mangledName")), None)
        if d is None or did in seen:
            return None
        cs = next(x for x in kids(d) if x.get("kind") == "CompoundStmt")
        return heap_singleton_of(u, kids(kids(cs)[0])[0], seen + (did,))
    return None


def accessor_body(u, e):
    """The returned expression of the accessor a call e calls (`AP::dal()`: `*AP_DAL::get_singleton()`), else None."""
    if e.get("kind") not in ("CallExpr", "CXXMemberCallExpr") or kids(e)[1:]:
        return None
    c = strip_object(kids(e)[0])
    while c.get("kind") == "ImplicitCastExpr":
        c = strip_object(kids(c)[0])
    did = (c.get("referencedDecl") or {}).get("id") or c.get("referencedMemberDecl")
    d = u.accessors.get(did)
    if d is None and did:
        d0 = u.decl(did)
        d = u.accessors.get(d0.get("previousDecl")) if d0 else None
        if d is None and d0 is not None:
            d = next((a for a in u.accessors.values() if a.get("mangledName") and a.get("mangledName") == d0.get("mangledName")), None)
    if d is None:
        return None
    cs = next(x for x in kids(d) if x.get("kind") == "CompoundStmt")
    return kids(kids(cs)[0])[0]


def ptr_targets(u, rec):
    """--world-pointers: the objects a pointer of static type `rec *` may point to (closed world: an
    object of rec or of a class derived from it): [("w", World field, class)] for file-scope objects,
    [("h", heap field, class)] for heap slots."""
    out = []
    for w in u.world:
        if w["rec"] is not None and rec in w["rec"].chain():
            out.append(("w", w["name"], w["rec"]))
    for h in u.heap:
        if rec in h.chain() and not h.abstract:
            out.append(("h", heap_field(h), h))
    return out


def zero_initializer(d):
    """--front-ends: the initializer of a static data member's definition is the constant 0 (as the
    zero-filled static storage it initializes: `uint8_t AP_InertialSensor_SITL::bus_id = 0;`)."""
    ini = non_attr(kids(d))
    if len(ini) != 1:
        return False
    v = const_number(ini[0])
    return v is not None and v == 0


def resolve_world(u, reject):
    """--world: which World object each reference member refers to. For every file-scope object
    the constructor it is built with binds its reference members (through its base constructors)
    to its arguments; an argument that names another file-scope object is that object. A class
    with two objects whose references differ, and a reference the translator cannot follow, are
    rejected."""
    def target_of(e, env):
        e = strip_object(e)
        while e.get("kind") == "UnaryOperator" and e.get("opcode") == "*":
            e = strip_object(kids(e)[0])        # `*pos_control` of a pointer: not followed
            return None
        if e.get("kind") == "DeclRefExpr":
            rid = e["referencedDecl"]["id"]
            if rid in env:
                return env[rid]
            if rid in u.world_ids:
                return u.world_ids[rid]
        if WORLD_PTRS[0]:
            hr = heap_singleton_of(u, e)
            if hr is not None:
                return "*" + heap_field(hr)     # `dal{AP::dal()}`: the heap singleton (AP_DAL::get_singleton())
        return None

    def bind(rec, ctor_def, targets, out, node):
        params = [p for p in kids(ctor_def) if p.get("kind") == "ParmVarDecl"]
        env = {p["id"]: targets[i] for i, p in enumerate(params) if i < len(targets) and targets[i] is not None}
        for ini in kids(ctor_def):
            if ini.get("kind") != "CXXCtorInitializer":
                continue
            if "anyInit" in ini:
                f = rec.field_by_id(ini["anyInit"]["id"])
                if f is not None and f.category == "wref":
                    t = target_of(kids(ini)[0], env) if kids(ini) else None
                    if t is None:
                        raise Reject(ini, "reference member `%s` bound to something other than a file-scope object (--world)" % f.name)
                    out[f.id] = t
            elif "baseInit" in ini and kids(ini):
                ce = strip_object(kids(ini)[0])
                while ce.get("kind") in ("ExprWithCleanups",) and kids(ce):
                    ce = kids(ce)[0]
                if ce.get("kind") != "CXXConstructExpr":
                    continue
                bname, _ = strip_tag(ini["baseInit"].get("desugaredQualType", ini["baseInit"]["qualType"]))
                brec = RECORDS.get(norm_template_args(bname))
                bctor = brec.find_ctor(ce.get("ctorType", {}).get("qualType", "")) if brec else None
                bdef = u.body_of(bctor) if bctor is not None else None
                if bdef is None:
                    continue
                bind(rec, bdef, [target_of(a, env) for a in kids(ce)], out, ce)

    seen = {}
    for w in u.world:
        d, rec = w["decl"], w["rec"]
        if w.get("static"):
            continue
        try:
            ce = strip_object(kids(d)[-1]) if non_attr(kids(d)) else None
            while ce is not None and ce.get("kind") in ("ExprWithCleanups",) and kids(ce):
                ce = kids(ce)[0]
            out = {}
            if ce is not None and ce.get("kind") == "CXXConstructExpr":
                ctor = rec.find_ctor(ce.get("ctorType", {}).get("qualType", ""))
                cdef = u.body_of(ctor) if ctor is not None else None
                if cdef is not None:
                    bind(rec, cdef, [target_of(a, {}) for a in kids(ce)], out, ce)
                w["ctor"], w["args"] = ctor, kids(ce)
            else:
                w["ctor"], w["args"] = None, []
            for f in rec.all_fields():
                if f.category == "wref" and f.id not in out:
                    raise Reject(d, "reference member `%s` of `%s` not bound to a file-scope object (--world)" % (f.name, d["name"]))
            if rec.id in seen and seen[rec.id] != out:
                raise Reject(d, "two objects of class `%s` whose reference members refer to different objects (--world)" % rec.cxx)
            seen[rec.id] = out
            for fid, t in out.items():
                u.wref[(rec.id, fid)] = t
            u.world_self[rec.id] = w["name"] if rec.id not in u.world_self else None
        except Reject as e:
            reject(e)
    if MEMBER_OBJECTS[0] and AHRS_EXT[0] and PARAM_EXT[0]:
        member_object_refs(u, bind, reject)
    if REACHABLE[0]:
        heap_member_refs(u)
    if INS_GPS[0] and WORLD_PTRS[0]:
        heap_elem_refs(u, reject)


def member_object_refs(u, bind, reject):
    """--ahrs-ext with --param-ext and --member-objects: the reference members of a World object's member object bound by
    the owner's in-class initializer to the owner's own data members (`AP_AHRS_DCM dcm{_kp_yaw, _kp, gps_gain, beta,
    _gps_use, _gps_minsats};`, AP_AHRS.h:1020, with `AP_Float &_kp_yaw` ... of AP_AHRS_DCM, AP_AHRS_DCM.h:110-118):
    under --param-ext the parameters are state objects of the owner, so each reference is that member of the World
    object, ("member", object, [field]) as heap_member_refs (`w.ahrs._kp_yaw`). (Without --param-ext they are `wpref`.)"""
    for w in u.world:
        rec = w["rec"]
        if rec is None or w.get("static"):
            continue
        for f in rec.all_fields():
            if f.category != "state" or f.t is None or f.t.kind != "record" or \
                    not any(g.category == "wref" for g in f.t.info.all_fields()):
                continue
            mrec = f.t.info
            ini = next((x for x in kids(f.decl) if x.get("kind") in ("CXXConstructExpr", "InitListExpr", "ExprWithCleanups")), None)
            while ini is not None and ini.get("kind") == "ExprWithCleanups" and kids(ini):
                ini = kids(ini)[0]
            if ini is None or ini.get("kind") != "CXXConstructExpr":
                continue
            ctor = mrec.find_ctor(ini.get("ctorType", {}).get("qualType", ""))
            cdef = u.body_of(ctor) if ctor is not None else None
            if cdef is None:
                continue

            def target(a):
                a = strip_object(a)
                fields = []
                while a.get("kind") == "MemberExpr" and not a.get("isArrow"):
                    fields.append(a.get("name"))
                    a = strip_object(kids(a)[0])
                if a.get("kind") == "MemberExpr" and a.get("isArrow") and strip_object(kids(a)[0]).get("kind") == "CXXThisExpr":
                    fields.append(a.get("name"))
                    return ("member", w["name"], list(reversed(fields)))
                return None
            out = {}
            try:
                bind(mrec, cdef, [target(a) for a in kids(ini)], out, ini)
            except Reject as e:
                reject(e)
                continue
            for fid, t in out.items():
                if u.wref.get((mrec.id, fid), t) != t:
                    reject(Reject(f.decl, "two objects of class `%s` whose reference members refer to different objects (--world)" % mrec.cxx))
                    continue
                u.wref[(mrec.id, fid)] = t


def const_cast_forward(m, twin):
    """--member-pointers: is the body of const member function m `return const_cast<C *>(this)->twin(its
    parameters, in order);`?"""
    cs = next((c for c in kids(m) if c.get("kind") == "CompoundStmt"), None)
    if cs is None or len(kids(cs)) != 1 or kids(cs)[0].get("kind") != "ReturnStmt" or not kids(kids(cs)[0]):
        return False
    e = strip_object(kids(kids(cs)[0])[0])
    while e.get("kind") in ("ImplicitCastExpr", "ExprWithCleanups") and kids(e):
        e = strip_object(kids(e)[0])
    if e.get("kind") != "CXXMemberCallExpr" or strip_parens(kids(e)[0]).get("kind") != "MemberExpr":
        return False
    callee = strip_parens(kids(e)[0])
    obj = strip_object(kids(callee)[0])
    if obj.get("kind") != "CXXConstCastExpr" or strip_object(kids(obj)[0]).get("kind") != "CXXThisExpr" or \
            callee.get("referencedMemberDecl") != twin["id"]:
        return False
    params = [p["id"] for p in kids(m) if p.get("kind") == "ParmVarDecl"]
    args = [strip_object(a) for a in kids(e)[1:]]
    return len(args) == len(params) and all(a.get("kind") == "DeclRefExpr" and a["referencedDecl"]["id"] == pid for a, pid in zip(args, params))


def value_init_list(e):
    """--member-pointers: is e `{}` for a struct (an InitListExpr whose every member is value-initialized: clang's
    ImplicitValueInitExpr, or a default constructor call; or the construction by an implicit default constructor,
    as clang gives `AP_AHRS_Backend::Estimates{}`, whose members have default member initializers)? Its value is
    the structure's default (`({} : T)`): numbers zero, members by their default member initializers, members of
    class type by their default constructors, as the translated field defaults."""
    if e.get("kind") == "CXXConstructExpr" and not kids(e):
        try:
            t = ctype_of(e)
        except Reject:
            return False
        ctor = t.info.find_ctor(e.get("ctorType", {}).get("qualType", "")) if t.kind == "record" else None
        return t.kind == "record" and (ctor is None or ctor.get("isImplicit") or ctor.get("explicitlyDefaulted"))
    return e.get("kind") == "InitListExpr" and not e.get("array_filler") and all(
        c.get("kind") in ("ImplicitValueInitExpr", "CXXDefaultInitExpr") or (c.get("kind") == "CXXConstructExpr" and not kids(c)) for c in kids(e))


def member_tags(u, reject):
    """--member-pointers (README.md, "Phase 3: AP_AHRS translated"): the member objects of World objects that
    pointers or references may designate: a data member of class (or struct) type of the class of a World
    object (the class's only one) whose address the program takes (`&dcm`, `&dcm_estimates`: AP_AHRS.cpp:250,
    :864), or to which a reference member of an unnamed struct is bound (`{ dcm, dcm_estimates }` of
    `backends_and_estimates[]`, AP_AHRS.h:1056). Each gets a `WPtr` constructor `<object>'<member>`; a
    member of a --boundary class (`AP_AHRS_SIM sim`) too (its calls are boundary calls or dropped)."""
    taken = set()
    skip = set()        # `memset(&yaw_reset_data, 0, sizeof(yaw_reset_data))` (AP_NavEKF3.cpp:901): not a pointer to the object
    for n in walk(u.tree):
        if isinstance(n, dict) and n.get("kind") == "CallExpr" and kids(n):
            c = strip_parens(kids(n)[0])
            while c.get("kind") == "ImplicitCastExpr":
                c = strip_parens(kids(c)[0])
            if (c.get("referencedDecl") or {}).get("name") in ("memset", "memcpy", "memcmp"):
                for a in kids(n)[1:]:
                    while a.get("kind") in ("ImplicitCastExpr", "CStyleCastExpr", "ParenExpr") and kids(a):
                        a = kids(a)[0]
                    skip.add(a.get("id"))
    for n in walk(u.tree):
        if not isinstance(n, dict):
            continue
        k = n.get("kind")
        if k == "UnaryOperator" and n.get("opcode") == "&" and n.get("id") in skip:
            continue
        if k == "UnaryOperator" and n.get("opcode") == "&":
            cands = [kids(n)[0]]
        elif k == "InitListExpr" and "unnamed struct" in n.get("type", {}).get("qualType", ""):
            cands = kids(n)
        else:
            continue
        for c in cands:
            m = strip_object(c)
            if m.get("kind") == "MemberExpr" and strip_object(kids(m)[0]).get("kind") == "CXXThisExpr":
                taken.add(m.get("referencedMemberDecl"))
    for w in u.world:
        rec = w["rec"]
        if rec is None or w.get("static") or sum(1 for x in u.world if x["rec"] is rec and not x.get("static")) != 1:
            continue
        for f in rec.all_fields():
            if f.id not in taken:
                continue
            if f.category == "state" and f.t.kind == "record":
                u.mtags.append({"name": "%s'%s" % (w["name"], f.lean), "owner": w["name"], "orec": rec, "field": f,
                                "rec": f.t.info, "bname": None, "cxx": "%s.%s" % (w.get("cxx") or w["name"], f.name)})
            elif f.category == "boundary":
                u.mtags.append({"name": "%s'%s" % (w["name"], f.lean), "owner": w["name"], "orec": rec, "field": f,
                                "rec": None, "bname": f.t.name, "cxx": "%s.%s" % (w.get("cxx") or w["name"], f.name)})


def boundary_record_decl(u, name):
    """--member-pointers: the definition (CXXRecordDecl) of a --boundary class, else None."""
    for d in u.ids.values():
        if d.get("kind") == "CXXRecordDecl" and d.get("name") == name.split("::")[-1] and d.get("completeDefinition"):
            return d
    return None


def boundary_derives(u, name, rec):
    """--member-pointers: does --boundary class `name` derive from translated class rec (its bases, by name)?"""
    d = boundary_record_decl(u, name)
    seen = set()
    while d is not None and d["id"] not in seen:
        seen.add(d["id"])
        bs = d.get("bases") or []
        if not bs:
            return False
        bname = norm_template_args(strip_tag(bs[0].get("type", {}).get("desugaredQualType", bs[0].get("type", {}).get("qualType", "")))[0])
        if bname == rec.cxx or bname.split("::")[-1] == rec.cxx.split("::")[-1]:
            return True
        if bname in RECORDS:
            return rec in RECORDS[bname].chain()
        d = boundary_record_decl(u, bname)
    return False


def mtag_targets(u, rec):
    """--member-pointers: the tagged member objects a pointer or reference of type `rec *` may designate."""
    out = []
    for tg in u.mtags:
        if tg["rec"] is not None and rec in tg["rec"].chain():
            out.append(tg)
        elif tg["rec"] is None and boundary_derives(u, tg["bname"], rec):
            out.append(tg)
    return out


def heap_member_refs(u):
    """--reachable: a reference member of a heap class bound by its constructors to a data member of the
    object a pointer points to (`public_origin(frontend->common_EKF_origin)`, AP_NavEKF3_core.cpp:16, with
    `frontend` the one NavEKF3 object): that member's path in the World, ("member", object, [fields])."""
    for rec in u.heap:
        for c in rec.methods:
            if c.get("kind") != "CXXConstructorDecl":
                continue
            defn = u.body_of(c) or c
            for ini in kids(defn):
                if ini.get("kind") != "CXXCtorInitializer" or "anyInit" not in ini or not kids(ini):
                    continue
                f = rec.field_by_id(ini["anyInit"]["id"])
                if f is None or f.category != "wref":
                    continue
                e = strip_object(kids(ini)[0])
                fields = []
                while e.get("kind") == "MemberExpr" and not e.get("isArrow"):
                    fields.append(e.get("name"))
                    e = strip_object(kids(e)[0])
                if e.get("kind") != "MemberExpr" or not e.get("isArrow"):
                    continue
                fields.append(e.get("name"))
                base = strip_object(kids(e)[0])
                while base.get("kind") == "ImplicitCastExpr":
                    base = strip_object(kids(base)[0])
                try:
                    pt = ctype_of(base)
                except Reject:
                    continue
                if pt.kind != "obj":
                    continue
                targets = ptr_targets(u, pt.info)
                if len(targets) != 1 or targets[0][0] != "w":
                    continue
                t = ("member", targets[0][1], list(reversed(fields)))
                if u.wref.get((rec.id, f.id), t) != t:
                    continue
                u.wref[(rec.id, f.id)] = t


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
    if FRONT_ENDS[0] and f.decl.get("hasInClassInitializer") and kids(f.decl) and f.t.is_scalar() and \
            any(m.get("kind") == "CXXThisExpr" for m in walk(kids(f.decl)[-1])):
        e = strip_parens(kids(f.decl)[-1])
        return kids(e)[0] if e.get("kind") == "InitListExpr" and len(kids(e)) == 1 else e   # (`uint8_t c{_index};`)
    if not f.decl.get("hasInClassInitializer") or f.t.kind != "record" or f.t.info.kind != "class":
        return None
    e = strip_parens(kids(f.decl)[-1])
    while e.get("kind") in ("ExprWithCleanups", "MaterializeTemporaryExpr", "CXXBindTemporaryExpr") and kids(e):
        e = kids(e)[0]
    if e.get("kind") != "CXXConstructExpr":
        return None
    if f.t.info.has_params() or any(g.category == "owner" for g in f.t.info.all_fields()) or any(is_star_this(a) for a in kids(e)):
        return e
    if FRONT_ENDS[0] and any(m.get("kind") == "CXXThisExpr" for m in walk(e)):
        return e        # --front-ends: `SITL::CompassSim _compass_sim{sitl_instance};` (AP_Compass_SITL.h:26) reads another member
    return None


def field_default(u, r, f):
    """The default of a field (its member initializer, else zero), and the items it uses."""
    if f.category in ("boundary", "ref", "owner", "wref", "erased", "wpref"):
        return
    if getattr(f, "rb_role", None) == "buf":
        f.default = V("#[]", ATOM)      # --ring-buffers: a null pointer (with `'alloc` false)
        return
    if deferred_init(f) is not None:
        f.default = zero_of(f.t, f.decl)
        return
    if (REACHABLE[0] or FRONT_ENDS[0]) and not f.decl.get("hasInClassInitializer"):
        # --reachable, --front-ends: a member of a class whose default constructor does not give zero
        # (`Quaternion quat;` of AP_DAL's `log_REPH`, `Quaternion quaternion` of `struct sitl_fdm`: QuaternionT()
        # : q1(1), quaternion.h), default-initialized by that constructor (--front-ends: also an array of them)
        et = f.t.elem if FRONT_ENDS[0] and f.t.kind == "array" and not getattr(f.t, "dims", None) else f.t
        if et.kind == "record" and not zero_default_ctor(u, et):
            res = u.context(et.info, f.decl).ctor(et.info.find_ctor("void ()"), top=True, node=f.decl)
            if res.cparams or res.has_params or res.uses_inp or "w" in res.reads | res.writes:
                if FRONT_ENDS[0]:
                    raise Reject(f.decl, "member `%s` of a class whose default constructor needs arguments or the World" % f.name)
                f.default = zero_of(f.t, f.decl)    # (a member with parameters: its holder's constructor constructs it)
                return
            v = V("%s.%s" % (et.info.lean, res.lean), ATOM)
            f.default = V("Array.replicate %d %s" % (f.t.n, v.text), APP) if et is not f.t else v
            f.deps = {res.bid, ("T", et.info.id)}
            return
    if f.decl.get("hasInClassInitializer"):
        init = kids(f.decl)[-1]
        et = f.t.elem if f.t.kind == "array" else f.t
        refs = MEMBER_PTRS[0] and et.kind == "record" and any(g.id in u.refptr_fields for g in et.info.all_fields())
        # (--member-pointers: `backends_and_estimates[] { { dcm, dcm_estimates }, ... }` names this object's members)
        tr = Body(u, None, u.context(r, f.decl) if refs else None, home=r.lean)
        if f.t.kind == "array" and init.get("kind") == "InitListExpr":
            pre, v = tr.array_init(init, f.t)
        elif init.get("kind") == "InitListExpr":
            if kids(init) and EKF_TYPES[0] and len(kids(init)) == 1 and f.t.is_scalar():
                pre, v = tr.expr(kids(init)[0])     # --ekf-types: `const ftype EKFGSF_gyroNoise{1.0e-1};` (EKFGSF_yaw.h:62)
            elif kids(init):
                raise Reject(init, "brace initializer with values for member `%s`" % f.name)
            else:
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
    if getattr(f, "rb_doc", None):
        return f.rb_doc
    loc = expansion(f.decl.get("loc"))
    where = line_range(u.shown_path(loc.get("file")), loc["line"], loc["line"])
    bit = (" : %d" % BITFIELD_WIDTH.get(f.decl["id"], 1)) if f.decl.get("isBitfield") else ""
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
    if INS_GPS[0]:
        # --ins-gps: a reference member bound to an element of a World object's array: the element's index (heap_elem_refs)
        fields += [(f.lean + "'i", "Nat", "0", "/-- The index of the element `%s` refers to: `%s` (--ins-gps). -/" % (
            comment_safe(f.name), comment_safe("%s.%s[i]" % (u.wref[(r.id, f.id)][1], ".".join(u.wref[(r.id, f.id)][2]))))) for f in r.all_fields()
            if f.category == "wref" and isinstance(u.wref.get((r.id, f.id)), tuple) and u.wref[(r.id, f.id)][0] == "elem"]
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
    if t.kind in ("array", "opt"):
        return type_deps(t.elem)
    if t.kind == "obj":
        return {("wptr",)}
    if t.kind == "wfun":
        return {("wfun",)}
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
        if r.kind == "plain" and not r.semaphore and not r.functor:
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
    if MAVLINK[0]:
        # --mavlink: the initial value of each file-scope variable a translated function reaches (its initializer,
        # else zero: C's static storage), which a caller of the functions passes at the start
        used = {p["id"] for fr in u.free_results.values() if fr is not None for p, _, _, _ in fr.cparams if p.get("kind") == "Global"}
        for gid in sorted(used, key=lambda k: u.ast_order.get(k, 0)):
            g = u.globals[gid]
            d = g["decl"]
            tr = Body(u, None, None, home=ns)
            init = non_attr(kids(d))
            if init and d.get("init") and not (init[0].get("kind") == "InitListExpr" and not kids(init[0])) and \
                    not (init[0].get("kind") == "CXXConstructExpr" and not kids(init[0])):
                pre, v = tr.array_init(init[0], g["t"]) if g["t"].kind == "array" else tr.expr(init[0])
                if pre:
                    raise Reject(d, "initializer of `%s` with side effects" % d["name"])
            else:
                v = zero_of(g["t"], d)
            lines = ["/-- The initial value of C++ `%s`, `%s`. -/" % comment_safe_pair(cpp_var_decl(d), where_of(u, d)),
                     "def %s'init : %s := %s" % (g["lean"], g["t"].lean, v.text)]
            blocks.append({"key": srckey_node(u, d), "ns": ns, "lines": lines, "deps": set(tr.deps) | type_deps(g["t"]), "id": ("ginit", gid)})
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
            if f.category not in ("owner", "wref"):     # the referenced object is not part of this object
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
        lines = []
        if TEXT_BUFFERS[0]:
            lines += ["/-- (--text-buffers) The text a `char` buffer holds, as the formatted write that made it (the formatting is",
                      "the vehicle's translated AP_HAL::Util::snprintf, where the text leaves the translation): `none` never written",
                      "(a zero-filled buffer: the empty string; a caller's buffer: unchanged), `null` the null pointer (a",
                      "`const char *` result, --text-results), `fmt size fmt args` `snprintf(buf, size, fmt, args...)` (the",
                      "arguments tagged as for --text-log), `text size src args` the same with the text of the buffer `src` as",
                      "the format. -/",
                      "inductive CText where",
                      "  | none",
                      "  | null",
                      "  | fmt (size : UInt64) (fmt : String) (args : Array (Sum UInt64 String))",
                      "  | text (size : UInt64) (src : CText) (args : Array (Sum UInt64 String))",
                      "deriving Inhabited",
                      "",
                      "/-- (--text-results) whether a `const char *` text is the null pointer -/",
                      "def CText.isNull : CText → Bool",
                      "  | .null => true",
                      "  | _ => false",
                      ""]
        lines += ["/-- What the translated classes write to objects outside the translation (--boundary, --boundary-call):",
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
    wb = world_blocks(u, ns) if u.world and FRONT_ENDS[0] else []    # (--front-ends: first, so that the member functions
    #                                                                   the constructors of library classes call are emitted)
    for rid, ctx in list(u.contexts.items()):
        blocks += context_blocks(rid, ctx)
    if u.world:
        blocks += wb or world_blocks(u, ns)     # the classes of the objects follow from the deps (below)
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

    out = ["import CFloat"]
    if C_STRINGS[0] or BYTE_OBJECTS[0] or HAL_STORAGE[0]:
        out.append("import CString")
    out += ["import %s" % m for m in sorted(u.libm_modules)] + ["import %s" % m for m in IMPORTS]
    out += ["", "/-!"]
    out.append("Generated by cpp2lean from `%s`. Do not edit; regenerate with" % comment_safe(shown))
    out.append("`python3 cpp2lean.py %s -o <dir> --namespace %s%s`." % (comment_safe(shown), ns, comment_safe(options)))
    out.append("")
    out.append("Each `def` is the C++ function of the same name, translated node by node from clang's AST")
    out.append("(`%s`)." % (" ".join(["clang"] + C_FLAGS) if C_MODE[0] else " ".join(["clang++"] + CLANG_FLAGS)))
    out.append("Under the compilation assumptions of cpp2lean/README.md, each computes the same result as the")
    out.append("C++ bit for bit (checked by cpp2lean/difftest.py). C's `float` and `double` are FloatLib's")
    out.append("`Binary32` and `Binary64`; `CFloat.lean` names the conversions and exact functions used.")
    out.append("-/")
    out += ["", "open FloatLib.Floats (Binary32 Binary64)"]
    if REACHABLE[0]:
        # the long straight-line bodies (NavEKF3_core::CovariancePrediction's 520 `let`s) and the constructors
        # of large states nest beyond Lean's default recursion depth (elaboration and code generation)
        out += ["", "set_option maxRecDepth 200000",
                "-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`",
                "-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++",
                "set_option linter.unusedVariables false"]
    elif MAVLINK[0]:
        # --mavlink: the object representations of the large message structs (FILE_TRANSFER_PROTOCOL's 254 bytes)
        # nest beyond Lean's default recursion depth
        out += ["", "set_option maxRecDepth 20000"]
    elif INS_GPS[0]:
        # --ins-gps: bindings the C++ does not read either (`(void)fft_enabled;`, AP_InertialSensor.cpp:1012), and the index of
        # a heap object's slot a dispatch computes for an overrider that reads no state (`get_lag` of AP_GPS_SITL)
        out += ["", "set_option linter.unusedVariables false"]
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
    text = "\n".join(out) + "\n"
    if C_MODE[0]:
        # a C translation unit (musl): the comments name C, not C++
        text = text.replace("C++ `", "C `").replace("uninitialized in C++;", "uninitialized in C;") \
            .replace("Each `def` is the C++ function", "Each `def` is the C function").replace("\nC++ bit for bit", "\nC bit for bit")
    if MISSION[0]:
        # (--mission) clang names an anonymous union by its absolute file path: shown relative to --src-root, so the
        # output does not depend on where the reference build lives
        text = re.sub(r"\(anonymous union at ([^:)]+):", lambda m: "(anonymous union at %s:" % u.shown_path(m.group(1)), text)
    return text, signatures(u, ns, shown), u.uses_libm, u.literals


def world_parts(u, w):
    """The World fields of object w: (field, Lean type, what) for its state, parameters, boundary
    inputs and outputs."""
    if w.get("static"):
        return [(w["name"], w["t"].lean, "static data member of `%s`" % w["static"].cxx)]
    rec = w["rec"]
    ctx = u.context(rec, w["decl"])
    out = [(w["name"], rec.lean + ".State", "state")]
    if rec.has_params():
        out.append((w["name"] + "'p", rec.lean + ".Params", "parameters"))
    if ctx.inputs or ctx.sub_inputs:
        out.append((w["name"] + "'inp", rec.lean + ".Inputs", "boundary inputs"))
    if not OUTPUT_LOG[0] and (ctx.outputs or ctx.sub_outputs):
        out.append((w["name"] + "'o", rec.lean + ".Outputs", "boundary outputs"))
    return out


def world_blocks(u, ns):
    """--world: `structure World` (one field per file-scope object and part) and `World.init`, which
    constructs the objects in definition order, as C++ initializes them."""
    lines = ["/-- The file-scope objects of the program (--world): for each, its state, its parameters, the",
             "values it reads from the boundary (set by the caller) and what it writes to the boundary. A",
             "reference member of one object to another is the other's field here. -/", "structure World where"]
    deps = set()
    for w in u.world:
        rec = w["rec"]
        if w.get("static"):
            deps |= type_deps(w["t"])
        else:
            deps.add(("T", rec.id))
        for fld, ty, what in world_parts(u, w):
            lines.append("  /-- C++ `%s` (%s), %s. -/" % (comment_safe(cpp_var_decl(w["decl"])), comment_safe(where_of(u, w["decl"])), what))
            lines.append("  %s : %s := %s" % (fld, ty, zero_of(w["t"], w["decl"]).text if w.get("static") else "{}"))
    for h in u.heap:
        # --world-pointers: the objects of class h created at run time (`new`, placement new), in creation order
        deps.add(("T", h.id))
        lines.append("  /-- The objects of C++ class `%s` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.%s i`). -/" % (comment_safe(h.cxx), heap_field(h)))
        lines.append("  %s : Array %s.State := #[]" % (heap_field(h), h.lean))
        if heap_field(h) in u.heap_inp:
            lines.append(("  /-- What the objects of C++ class `%s` read from the boundary (--front-ends: one set of values for the class, set by the caller). -/"
                          if FRONT_ENDS[0] else
                          "  /-- What the heap objects of C++ class `%s` read from the boundary (one record for all of them, set by the caller). -/") % comment_safe(h.cxx))
            lines.append("  %s'inp : %s.Inputs := {}" % (heap_field(h), h.lean))
        if heap_field(h) in u.heap_out:
            lines.append("  /-- What the heap objects of C++ class `%s` wrote to the boundary (one record for all of them). -/" % comment_safe(h.cxx))
            lines.append("  %s'o : %s.Outputs := {}" % (heap_field(h), h.lean))
    emitted = set()
    for pid, fld in u.heap_ptr.items():
        if FRONT_ENDS[0] and (fld in emitted or fld not in u.heap_ptr_used):
            continue        # --front-ends: one field per pointer, and only those the translation uses
        emitted.add(fld)
        d = u.decl(pid)
        lines.append("  /-- C++ `%s` (a static pointer member of a class without a file-scope object), its value. -/" % comment_safe(cpp_var_decl(d) if d else fld))
        lines.append("  %s : WPtr := WPtr.null" % fld)
        deps.add(("wptr",))
    lines.append("  deriving Inhabited")
    wns = ns if NEST[0] else None
    out = [{"key": (10 ** 6, "", 0, 0), "ns": wns, "lines": lines, "deps": deps, "id": ("world",)}]
    if WORLD_PTRS[0]:
        out.append(wptr_block(u, wns))
        out.append(wfun_block(u, wns))
        out += [dict(d["block"], ns=wns) for d in u.dispatch.values()]
        if u.wfun_call is not None and "lines" in u.wfun_call:
            out.append({"key": u.wfun_call["key"], "ns": wns, "lines": u.wfun_call["lines"], "deps": u.wfun_call["deps"], "id": ("wfuncall",)})
    init = ["/-- The construction of the file-scope objects, in definition order (C++ static initialization). -/",
            "def World.init : World := Id.run do", "  let mut w : World := {}"]
    ideps = {("world",)}
    b = Body(u, None, None, home=ns)
    for w in u.world:
        rec, d = w["rec"], w["decl"]
        if w.get("ctor") is None:
            continue                        # zero-initialized and trivially constructed: the defaults
        sub = u.context(rec, d)
        res = sub.ctor(w["ctor"], top=True, node=d)
        ideps.add(res.bid)
        if (res.uses_inp and not AHRS_EXT[0]) or ("w" in res.reads and not WORLD_PTRS[0]):
            raise Reject(d, "constructor of World object `%s` that reads the boundary or other objects" % w["name"])
        pre, vals, outs = b.call_args(res.cparams, w["args"], d)
        if res.uses_inp:
            # --ahrs-ext: a constructor that reads the boundary (AP_AHRS's selects its backends, AP_AHRS.cpp:227): the
            # object's inputs as they are in the World at static initialization (their defaults, unless set before)
            vals = [V("w.%s'inp" % w["name"], ATOM)] + vals
        if outs or pre:
            raise Reject(d, "constructor arguments of World object `%s` that are not values" % w["name"])
        if "w" in res.reads | res.writes:
            # --world-pointers: a constructor that reaches the World (`dal{AP::dal()}` allocates the heap singleton)
            call = app("%s.%s" % (rec.lean, res.lean), *([V("w", ATOM)] + vals))     # (vals: --ahrs-ext's inputs first)
            outs_w = ["t'p"] if res.has_params else []
            outs_w += ["t's"] + (["t'w"] if "w" in res.writes else [])
            init.append("  let (%s) := %s" % (", ".join(outs_w), call.text) if len(outs_w) > 1 else "  let %s := %s" % (outs_w[0], call.text))
            init.append("  w := { %s with %s }" % ("t'w" if "w" in res.writes else "w", ", ".join((["%s'p := t'p" % w["name"]] if res.has_params else []) + ["%s := t's" % w["name"]])))
            continue
        call = app("%s.%s" % (rec.lean, res.lean), *vals) if vals else V("%s.%s" % (rec.lean, res.lean), ATOM)
        if res.has_params:
            init.append("  let (t'p, t's) := %s" % call.text)
            init.append("  w := { w with %s'p := t'p, %s := t's }" % (w["name"], w["name"]))
        else:
            init.append("  w := { w with %s := %s }" % (w["name"], call.text))
    init.append("  return w")
    ideps |= b.deps
    out.append({"key": (10 ** 6, "", 0, 1), "ns": wns, "lines": init, "deps": ideps, "id": ("world_init",)})
    return out


def wptr_block(u, wns):
    """--world-pointers: `inductive WPtr`, the pointers of the program: null, one constructor per
    file-scope object of a translated class, one per heap slot array (with the object's index);
    `WPtr.index` (the index of a heap object) and `WPtr.name` (for the difftest)."""
    lines = ["/-- A pointer to an object of the program (--world-pointers): null, a file-scope object, or the object",
             "with index `i` among those of a class that `new` creates (closed world: every object a pointer can",
             "point to is one of these; README.md, \"Phase 3: World pointers\"). -/", "inductive WPtr where", "  | null"]
    for w in u.world:
        if w.get("static") and (REACHABLE[0] or INS_GPS[0]):
            continue        # a static data member or static local: not an object a pointer can point to
        lines.append("  | %s" % w["name"])
    for h in u.heap:
        lines.append("  | %s (i : Nat)" % heap_field(h))
    for tg in u.mtags:
        lines.append("  | %s  -- the member object `%s` (--member-pointers)" % (tg["name"], tg["cxx"]))
    lines.append("  deriving DecidableEq, Inhabited")
    lines += ["", "/-- The index of a heap object among those of its class (0 for the others). -/", "def WPtr.index : WPtr → Nat"]
    for h in u.heap:
        lines.append("  | .%s i => i" % heap_field(h))
    lines.append("  | _ => 0")
    lines += ["", "/-- A name of the object (for the difftest: `null`, the field, `heap'C#i`). -/", "def WPtr.name : WPtr → String",
              "  | .null => \"null\""]
    for w in u.world:
        if w.get("static") and (REACHABLE[0] or INS_GPS[0]):
            continue
        lines.append("  | .%s => \"%s\"" % (w["name"], w["name"]))
    for h in u.heap:
        lines.append("  | .%s i => \"%s#\" ++ toString i" % (heap_field(h), heap_field(h)))
    for tg in u.mtags:
        lines.append("  | .%s => \"%s\"" % (tg["name"], tg["name"]))
    return {"key": (-2, "", 0, 0), "ns": wns, "lines": lines, "deps": set(), "id": ("wptr",)}


def leaf_fields(t, lean, cxx):
    """The scalar leaves of a value of type t: (Lean access, C++ access, C++ type, enum)."""
    out = []
    if t.kind == "record" and getattr(t.info, "byte_union", False):
        # --mission: a byte union's bytes, in C++ the object representation of the union (`bytes'`: difftest.py reads
        # `x.bytes'[k]` as `((const unsigned char *)&x)[k]`)
        return [("%s.bytes[%d]!" % (lean, k), "%s.bytes'[%d]" % (cxx, k), "uint8_t", None) for k in range(t.info.union_size)]
    if t.kind == "record":
        for f in t.info.all_fields():
            if f.category == "state" and getattr(f, "refptr", False):
                # --member-pointers: a reference member bound to a member object, printed as the object's address
                out.append((lean + "." + f.lean, cxx + "." + f.name, f.t.info.cxx + " &", None))
            elif f.category == "state":
                out += leaf_fields(f.t, lean + "." + f.lean, cxx + "." + f.name)
    elif t.kind == "array":
        dims = getattr(t, "dims", None)
        for k in range(t.n):
            if dims:        # --ekf-arrays: element k of a flat multidimensional array is `a[i][j]` in C++
                idx, r = [], k
                for d in reversed(dims):
                    idx.append(r % d)
                    r //= d
                out += leaf_fields(t.elem, "%s[%d]!" % (lean, k), cxx + "".join("[%d]" % i for i in reversed(idx)))
                continue
            out += leaf_fields(t.elem, "%s[%d]!" % (lean, k), "%s[%d]" % (cxx, k))
    elif t.kind == "enum":
        out.append((lean, cxx, t.info.under.cname, t.info.lean))
    elif getattr(t, "bu", None) is not None:
        out.append((lean, cxx + "." + t.bu.value_name, t.cname, None))     # --ekf-types: a bit union is its integer member
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
        elif f.category == "param" and f.t.kind == "record" and AHRS_EXT[0]:
            # --ahrs-ext: an AP_Vector3f parameter, by its components
            out += [(lean + f.lean + a, cxx + f.name + ".get()" + b, c, e) for a, b, c, e in leaf_fields(f.t, "", "")]
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
    """An Inputs field in signatures.json."""
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
            if p.get("kind") == "HalStorage":
                params[-1]["hidden"] = {"kind": "hal_storage", "size": HAL_STORAGE[0]}    # not a C++ parameter
            elif p.get("kind") == "Global":
                params[-1]["hidden"] = {"kind": "global", "init": "%s.%s'init" % (ns, pn)}     # --mavlink: a file-scope variable
            elif POINTER_PARAMS[0] and pt.kind == "array" and pt.n == 0 and ref in ("mut", "cptr"):
                params[-1]["array_elem"] = pt.elem.cname       # a pointer parameter: the caller's array
            elif POINTER_PARAMS[0] and ref in ("mut", "cptr") and p.get("type", {}).get("qualType", "").rstrip().endswith("*"):
                params[-1]["by_pointer"] = True                # a scalar pointer parameter: `&x`
        return params

    def ret_entries(ret):
        return {"ret": ret.cname, "ret_enum": pre + ret.info.lean if ret.kind == "enum" else None,
                "ret_under": ret.info.under.cname if ret.kind == "enum" else None,
                "ret_scalar": ret.kind in scalar or ret.kind == "enum", "ret_leaves": record_leaves(ret)}

    free = []
    for key in sorted(u.free_results, key=lambda k: srckey_node(u, u.decl(k))):
        fr = u.free_results[key]
        if fr is None or getattr(fr, "world_reads", False):
            continue        # (--world-pointers: a function of the World is driven through the World objects)
        f = u.decl_file(fr.decl) or ""
        e = {"cxx": fr.decl["name"], "cxx_call": template_call_name(fr.decl), "lean": "%s.%s" % (ns, fr.lean),
             "file_static": fr.decl.get("storageClass") == "static" and not f.endswith((".h", ".hpp")),
             "kind": "free", "top": False, "owner": None, "access": "public", "reads": [], "writes": [],
             "uses_inp": False, "params": param_entries(fr.cparams)}
        e.update(ret_entries(fr.ret))
        free.append(e)
    for key, sr in u.static_results.items():
        if getattr(sr, "world_reads", False):
            continue
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
        if fr.outs or fr.ret.kind not in scalar or any(pt.kind not in scalar for _, _, pt, _ in fr.cparams) or getattr(fr, "world_reads", False):
            continue
        d = fr.decl
        rng = d["range"]
        sigs.append({"name": d["name"], "lean": "%s.%s" % (ns, fr.lean),
                     "params": [[p["name"], pt.cname] for p, pn, pt, ref in fr.cparams], "ret": fr.ret.cname,
                     "source": line_range(shown, expansion(rng["begin"])["line"], expansion(rng["end"])["line"])})
    classes = []
    # (in source order: the order in which the contexts were created can differ from run to run)
    for rid, ctx in sorted(u.contexts.items(), key=lambda kv: (srckey_node(u, kv[1].rec.node), kv[1].rec.cxx)):
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
            if getattr(res, "uses_sp", False):
                e["uses_sp"] = True     # --param-save-log: `(sp : String)`, the C++ path of the object, last of the implicit arguments
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
    out = {"functions": sigs, "classes": classes, "enums": enums, "free": free, "output_log": out_log,
            "output_ns": pre if OUTPUT_LOG[0] else None, "var_info": var_info,
            "world": [dict({"name": w["name"], "cxx": w.get("cxx", w["decl"]["name"]), "class": w["rec"].cxx if w["rec"] else None, "lean": w["rec"].lean if w["rec"] else None,
                       "parts": [(f, t, what) for f, t, what in world_parts(u, w)]},
                      **({"static": w["static"].cxx, "leaves": [{"root": "w", "lean": a, "cxx": b, "type": c, "enum": e}
                                                                for a, b, c, e in leaf_fields(w["t"], "", "")]} if w.get("static") else {}),
                      **({"local": True} if w.get("local") else {}))
                      for w in u.world]}
    if MAVLINK[0]:
        # --mavlink: every record layout the translation used (an object representation, a byte view), for the
        # cross-check against clang's (ardupilot/check_layouts.py)
        for r in u.records:
            if r.kind == "plain" and r.fields and not r.dropped and getattr(r, "field_layout", None) is None and \
                    all(f.category == "state" for f in r.fields):
                try:
                    record_layout(r, r.node)    # (also the records only held as values: mavlink_message_t's bit-field)
                except Reject:
                    pass
        out["layouts"] = [{"record": r.node.get("name") or r.cxx, "cxx": r.cxx, "size": r.byte_layout[1], "align": r.byte_layout[2],
                           "fields": [list(x) for x in r.field_layout], **({"union": True} if getattr(r, "byte_union", False) else {})}
                          for r in sorted(u.records, key=lambda r: r.cxx) if getattr(r, "field_layout", None) is not None and
                          not (MISSION[0] and ("name" not in r.node or r.node.get("kind") == "ClassTemplateSpecializationDecl"))]     # (--mission: an anonymous union has no name for `sizeof`;
                                                                            # its struct's layout places it)
    if WORLD_PTRS[0]:
        # --world-pointers: the heap slot arrays, for the difftest (README.md, "Phase 3: World pointers")
        out["heap"] = [{"field": heap_field(h), "class": h.cxx, "lean": h.lean, "placement": h.id in u.heap_placement,
                        **({"inputs": True} if heap_field(h) in u.heap_inp else {})}
                       for h in u.heap]
        out["funcs"] = [{"ctor": functor_ctor(r, m), "class": r.cxx, "method": m.get("name")} for r, m in u.funcs]
        if u.mtags:
            # --member-pointers: the tagged member objects (their `WPtr.name` and C++ object)
            out["mtags"] = [{"name": tg["name"], "cxx": tg["cxx"]} for tg in u.mtags]
    return out


def main():
    if "--param-memory" in sys.argv[1:]:
        # README.md, "Phase 4: AP_Param": C++ over one byte memory (cpp2lean_mem.py); the argument after the option
        # is its configuration, the rest (-o DIR, --namespace NS) is passed on
        args = list(sys.argv[1:])
        i = args.index("--param-memory")
        cfg = args[i + 1]
        del args[i:i + 2]
        import cpp2lean_mem
        sys.exit(cpp2lean_mem.main([cfg] + args))
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
    ap.add_argument("--output-fn", action="append", default=[], help="with --output-log: qualified name of a free function outside the model (MAVLink's mavlink_msg_*_send) whose calls are `Output` events with their arguments (a `const T *` argument `&x` of a record: x's value)")
    ap.add_argument("--src-root", action="append", default=[], help="show source paths relative to this directory (e.g. ArduPilot's libraries/)")
    ap.add_argument("--keep-going", action="store_true", help="survey mode: also translate the member functions of a class some of whose data members were rejected (to list every rejection)")
    ap.add_argument("--survey", action="store_true", help="with --keep-going: report every rejected statement of a function, not only its first rejection (the translation goes on after a rejected statement; the output is not usable)")
    ap.add_argument("--clang-arg", action="append", default=[], help="an extra clang argument for the AST (e.g. -DNAME=1, -include file, -cl-single-precision-constant)")
    ap.add_argument("--use", action="append", default=[], help="a library function, member function or constructor to translate as if a translated file called it: `name`, `Class<args>::member`, optionally with parameter types `(T1, T2)`; or @file with one per line")
    ap.add_argument("--array-params", action="store_true", help="a `const T *` parameter read only by subscript (`motors[i]`) is the array the caller passes (AP_MotorsMatrix::add_motors)")
    ap.add_argument("--site-inputs", action="store_true", help="a const boundary call with non-constant arguments, outside loops, is one input per call site")
    ap.add_argument("--world", action="store_true", help="the mutable file-scope objects of translated classes are fields of one `World` structure; reference members bound to them are paths in it (README.md, \"The World\")")
    ap.add_argument("--output-log", action="store_true", help="outputs to the boundary are the calls in order (`Output` events in an `Array`), not the last values written")
    ap.add_argument("--enum-as-int", action="append", default=[], help="an enum outside the translated files whose values are used: its type `unsigned int`, its enumerators their values (Phase 5c: MAV_SEVERITY with --text-log)")
    ap.add_argument("--text-buffers", action="store_true", help="with --text-log: a local `char buf[N]` or a `char *` parameter is the pending text of the `hal.util->snprintf(buf, size, fmt, ...)` that fills it (size, format, arguments), and `GCS::send_text(sev, fmt, buf)` an `Output.send_text_snprintf` event that the vehicle formats with the translated AP_HAL::Util::snprintf (Phase 5c)")
    ap.add_argument("--text-results", action="append", default=[], help="with --text-buffers: a `const char *` member function (`Class::f`) returning a `char` data member that is a text or the null pointer (NavEKF3_core::prearm_failure_reason): its result and the locals it initializes are `CText`s, `CText.null` the null pointer (Phase 5d)")
    ap.add_argument("--text-log", action="store_true", help="with --output-log: `GCS::send_text(severity, fmt, ...)` appends `Output.send_text severity fmt args` (the variadic arguments tagged: `Sum.inl` a 64-bit slot, `Sum.inr` a string) instead of being dropped (Phase 5c)")
    ap.add_argument("--param-save-log", action="store_true", help="with --output-log: every `AP_Param::save(force)` of a parameter (also the save inside `set_and_save`, `set_and_save_ifchanged`) appends `Output.AP_Param_save path force`, path the C++ member path of the parameter object from its World object, built at run time with the actual array indices (a local object: `<local F::v>`)")
    ap.add_argument("--boundary-query", action="append", default=[], help="Class::member: a non-const member function of a boundary class that does not change the object (a getter not marked const, e.g. AC_AttitudeControl::get_bf_feedforward): its calls are inputs, as for a const member function")
    ap.add_argument("--boundary-static", action="append", default=[], help="Class::member: a member function of a boundary class that reads nothing of its object (AP_AHRS::calc_trig): translated as a function of its arguments")
    ap.add_argument("--boundary-call", action="append", default=[], help="Class::member: a member function of a translated class that is part of the boundary (not translated; calls are boundary calls), e.g. AP_Motors::rc_write")
    ap.add_argument("--nest", action="store_true", help="emit the classes inside the file's namespace too (several translations in one Lean package)")
    ap.add_argument("--type-name", action="append", default=[], help="CXX=Lean: the Lean name of a class template specialization (when its typedef is not unique, e.g. Vector2<double>=Vector2p)")
    ap.add_argument("--general-loops", action="store_true", help="loops without a constant trip count are translated as loops of at most 2^64 iterations (README.md, \"The C library\")")
    ap.add_argument("--import", dest="imports", action="append", default=[], help="a Lean module the translation imports (the module of an --extern function)")
    ap.add_argument("--pointer-params", action="store_true", help="pointer parameters and local pointers into arrays: `T *p` read or written by `*p`, `p[i]`, moved by `p++`, passed on, `new T[k]` locals (README.md, \"Phase 2\")")
    ap.add_argument("--runtime-loops", action="store_true", help="loops bounded by a runtime value that the loop does not change: `for (T i = a; i < n; i++)`, `while (k--)`, `for (; p != q; p++)` (README.md, \"Phase 2\")")
    ap.add_argument("--c-strings", action="store_true", help="`char` (a byte), `char[N]`, string literals and `char *` as byte arrays with offsets; the C string functions as CString.lean; variadic functions and `va_list` (README.md, \"Phase 2b\")")
    ap.add_argument("--gotos", action="store_true", help="forward `goto`, `continue` in `do` loops and `switch` fallthrough, rewritten with flags before translation (README.md, \"Phase 2b\")")
    ap.add_argument("--byte-objects", action="store_true", help="object representations: `&x` passed as bytes (`void *`, `uint8_t *`), `memcpy` between objects and bytes, unions of numbers in C++ (README.md, \"Phase 2b\")")
    ap.add_argument("--ekf-arrays", action="store_true", help="multidimensional arrays as flat row-major arrays, references to arrays, `memset` of whole arrays and objects, element writes in place (README.md, \"Phase 3: EKF data structures\")")
    ap.add_argument("--ekf-types", action="store_true", help="the type forms of EKF3's data members: structs named by a typedef, structs with base structs as plain structs (README.md, \"Phase 3: EKF data structures\")")
    ap.add_argument("--ring-buffers", action="store_true", help="type-erased containers (`void *buffer` + `elsize`, AP_NavEKF's ekf_ring_buffer/ekf_imu_buffer) monomorphized for each typed wrapper `W<T> : C` that passes `sizeof(T)`: the buffer is an `Array T` (README.md, \"Phase 3: EKF data structures\")")
    ap.add_argument("--hal-storage", type=int, default=0, metavar="SIZE", help="`hal.storage->read_block/write_block` on the HAL storage bytes (SIZE of them, HAL_STORAGE_SIZE), an `Array UInt8` threaded through the functions that reach it (README.md, \"Phase 2b\")")
    ap.add_argument("--uninit-reads", action="store_true", help="accept reads that the definite-assignment check cannot prove are preceded by an assignment (musl's `if (big) sign = ...; ... if (big) return sign ? ...`): the variable starts at zero; the C reads it only after an assignment (README.md, \"The C library\")")
    ap.add_argument("--world-pointers", action="store_true", help="(with --world) pointers to classes are tags of the closed set of World objects and init-time heap objects: calls through them dispatch over the objects of the pointer's class, `new` fills a heap slot of the World (README.md, \"Phase 3: World pointers\")")
    ap.add_argument("--semaphores", action="append", default=[], help="classes (comma-separated) whose objects are semaphores: members and locals of them are not state, `take`/`give` succeed and do nothing (one thread, PORT-PLAN 4.11)")
    ap.add_argument("--heap-alloc", action="append", default=[], help="a function (qualified name) returning raw memory for `(T *)f(sizeof(T) * n, ...)`, in which placement new constructs objects (default: malloc, calloc)")
    ap.add_argument("--indexed-inputs", action="store_true", help="a const call on a boundary object with one non-constant integer argument (`ins.use_accel(i)`, also with reference parameters it writes) reads an input array at that argument: one array per member function, an index beyond the array reads the zero value (README.md, \"Phase 3: AP_DAL and NavEKF3\")")
    ap.add_argument("--sizeof", action="append", default=[], help="C=N: `sizeof(C)` is N, the size clang computes for class C on the reference target (a class whose object representation the model does not hold: pointer and reference members, e.g. `sizeof(NavEKF3_core)` in AP_NavEKF3.cpp:842)")
    ap.add_argument("--reachable", action="store_true", help="the member functions of the translated classes are translated only as far as the --use entry points (and the constructors of the objects) reach them, not all of them (README.md, \"Phase 3: AP_DAL and NavEKF3\")")
    ap.add_argument("--array-offsets", action="store_true", help="(with --pointer-params) a pointer into an array is passed as the whole array and an offset (`p'o : Nat`), and written back whole; `memset`/`memcpy` through a pointer write element by element: no slices, no copies (README.md, \"Phase 3: AP_AHRS, and speed\")")
    ap.add_argument("--member-pointers", action="store_true", help="(with --world-pointers) a member object of a World object whose address is taken, or to which a reference member of an unnamed struct is bound, has a `WPtr` tag; pointers to it and such references are the tag; calls, reads and writes through them select the running object's own member (README.md, \"Phase 3: AP_AHRS translated\")")
    ap.add_argument("--ahrs-ext", action="store_true", help="(Phase 3, AP_AHRS) AP_AHRS's and DCM's other constructs: AP_Vector3f parameters (without --param-ext), set_enable, writes to boundary objects as outputs, boundary locals of untranslated types and boundary pointers, non-const boundary calls with results as inputs, loops bounded by boundary inputs, `do { } while (0)`, local arrays of class type, Location::is_zero's memcmp, static member functions reading the boundary as inputs (README.md, \"Phase 3: AP_AHRS translated\")")
    ap.add_argument("--member-objects", action="store_true", help="(with --world) a static data member of a translated class (`static NavEKF3 EKF3;` of AP_AHRS_NavEKF3) is a World object named after the member; `EKF3.f()` and `ekf3.EKF3.f()` are calls on it (README.md, \"Phase 3: AP_AHRS, and speed\")")
    ap.add_argument("--member-reach", action="store_true", help="(with --world-pointers) a call on a member object adds the World objects its callee reaches to the caller's, so that the self-reach cycle of the caller's callers sees paths through member objects (AP_AHRS's `ekf3` to AP_DAL and AP_Baro; README.md, \"Phase 5c\")")
    ap.add_argument("--swap-out", action="store_true", help="(with --world-pointers) a call that writes the state of a World object or a heap object takes the state out of the World for the call and stores the result back, so that its arrays are updated in place (README.md, \"Phase 3: AP_AHRS, and speed\")")
    ap.add_argument("--front-ends", action="store_true", help="(Phase 3) the constructs of the sensor front ends and their stand-ins (README.md, \"Phase 3: sensor front ends and AP_Param\")")
    ap.add_argument("--world-class", action="append", default=[], help="(with --front-ends) library classes (comma-separated) whose pointers are World pointers: tags of their objects or null")
    ap.add_argument("--param-name", action="append", default=[], help="(with --param-ext) NAME=object.member[k]...: the parameter that AP_Param::set_default_by_name(\"NAME\", v) sets")
    ap.add_argument("--param-ext", action="store_true", help="(with --ap-param, Phase 3, part of F13) AP_Vector3f parameters, arrays of parameters, parameters in structs and arrays of structs, nested var_info groups (README.md, \"Phase 3: sensor front ends and AP_Param\")")
    ap.add_argument("--est-world", action="store_true", help="(with --front-ends --ins-gps --reachable, Phase 3) the sensor front ends and NavEKF3 in one World: a front end's singleton getter that allocates the object when the pointer is null (`AP_InertialSensor::get_singleton`) is an accessor of its World object (README.md, \"Phase 3: the estimator World and the EKF3 replay\")")
    ap.add_argument("--ins-gps", action="store_true", help="(with --front-ends, Phase 3) the constructs of AP_InertialSensor, AP_GPS and their stand-ins (README.md, \"Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source\")")
    ap.add_argument("--mavlink", action="store_true", help="(Phase 4) the MAVLink C library's constructs: `extern \"C\"` blocks, mutable file-scope variables as state threaded through the functions that reach them, pointers to structs, packed structs and bit-fields, the payload's byte view, constant tables with lookups (README.md, \"Phase 4: the MAVLink C library\")")
    ap.add_argument("--mission", action="store_true", help="(with --mavlink, Phase 4) AP_Mission's constructs: a union of members of different types (`Mission_Command::Content`, `PackedContent`, anonymous unions in structs) as the bytes of its size with each member a view at its offset, signed bit-fields, `case a ... b`, `x = {}` of a class, a local pointer to a member of a local object (`float *selector`) as the member it designates, `memcmp` of objects with padding (README.md, \"Phase 4: AP_Mission\")")
    ap.add_argument("--null-member", action="append", default=[], help="(with --mavlink) Class::member: a pointer data member that is always null (nothing assigns it): read as the null pointer, and conditions, locals and calls it decides are folded before translation (README.md, \"Phase 4: the MAVLink C library\")")
    ap.add_argument("--module-sig", action="append", default=[], help="(C) the signatures.json of another translation: calls of its functions use its translations (README.md, \"The C library\")")
    a = ap.parse_args()
    C_MODE[0] = a.file.endswith(".c")
    GENERAL_LOOPS[0] = a.general_loops
    POINTER_PARAMS[0] = a.pointer_params
    RUNTIME_LOOPS[0] = a.runtime_loops
    C_STRINGS[0] = a.c_strings
    GOTOS[0] = a.gotos
    BYTE_OBJECTS[0] = a.byte_objects
    HAL_STORAGE[0] = a.hal_storage       # (the size; 0: off)
    RING_BUFFERS[0] = a.ring_buffers
    EKF_TYPES[0] = a.ekf_types
    EKF_ARRAYS[0] = a.ekf_arrays
    if (a.c_strings or a.byte_objects or a.hal_storage) and not a.pointer_params:
        ap.error("--c-strings, --byte-objects and --hal-storage need --pointer-params")
    UNINIT_READS[0] = a.uninit_reads
    IMPORTS.extend(a.imports)
    for path in a.module_sig:
        with open(path) as f:
            for e in json.load(f)["free"]:
                if not e["file_static"]:
                    MODULE_FNS[e["cxx"]] = e
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
    if a.survey:
        if not a.keep_going:
            ap.error("--survey needs --keep-going")
        SURVEY[0] = True
    AP_PARAM[0] = a.ap_param
    SRC_ROOTS.extend(os.path.realpath(x) + os.sep for x in a.src_root)
    for x in a.drop:
        DROP.update(y for y in x.split(",") if y)
    for x in a.boundary_fn:
        BOUNDARY_FN.update(y for y in x.split(",") if y)
    for x in a.output_fn:
        OUTPUT_FN.update(y for y in x.split(",") if y)
    if OUTPUT_FN and not a.output_log:
        ap.error("--output-fn needs --output-log")
    for x in a.use:
        if x.startswith("@"):
            with open(x[1:]) as f:
                USE.extend(l.strip() for l in f if l.strip() and not l.lstrip().startswith("#"))
        else:
            USE.append(x)
    NEST[0] = a.nest
    OUTPUT_LOG[0] = a.output_log
    TEXT_LOG[0] = getattr(a, "text_log", False)
    TEXT_BUFFERS[0] = getattr(a, "text_buffers", False)
    TEXT_RESULTS.update(x for v in getattr(a, "text_results", []) for x in v.split(","))
    ENUM_AS_INT.update(getattr(a, "enum_as_int", []))
    PARAM_SAVE_LOG[0] = a.param_save_log
    if a.param_save_log and not a.output_log:
        ap.error("--param-save-log needs --output-log")
    WORLD[0] = a.world
    WORLD_PTRS[0] = a.world_pointers
    REACHABLE[0] = a.reachable
    INDEXED_INPUTS[0] = a.indexed_inputs
    ARRAY_OFFSETS[0] = a.array_offsets
    SWAP_OUT[0] = a.swap_out
    MEMBER_REACH[0] = getattr(a, "member_reach", False)
    MEMBER_OBJECTS[0] = a.member_objects
    MEMBER_PTRS[0] = a.member_pointers
    AHRS_EXT[0] = a.ahrs_ext
    if a.ahrs_ext and not a.param_ext:
        PARAM_CLASSES["AP_Vector3f"] = "Vector3f"     # (with --ap-param, not --param-ext: a vector parameter's value;
                                                      # under --param-ext an AP_Vector3f is its AP_ParamV object, state)
    for x in a.sizeof:
        k, _, v = x.partition("=")
        SIZEOFS[k.strip()] = int(v)
    if a.reachable and not a.use:
        print("cpp2lean: --reachable needs --use entry points")
        sys.exit(2)
    FRONT_ENDS[0] = a.front_ends
    for x in a.param_name:
        k, _, v = x.partition("=")
        PARAM_NAMES[k.strip()] = v.strip()
    for x in a.world_class:
        WORLD_CLASSES.update(y.strip() for y in x.split(",") if y.strip())
    PARAM_EXT[0] = a.param_ext
    INS_GPS[0] = a.ins_gps
    EST_WORLD[0] = a.est_world
    MAVLINK[0] = a.mavlink
    MISSION[0] = a.mission
    if a.mission and not a.mavlink:
        print("cpp2lean: --mission needs --mavlink")
        sys.exit(2)
    for x in a.null_member:
        NULL_MEMBERS.update(y.strip() for y in x.split(",") if y.strip())
    if NULL_MEMBERS and not a.mavlink:
        print("cpp2lean: --null-member needs --mavlink")
        sys.exit(2)
    if a.ins_gps and not a.front_ends:
        print("cpp2lean: --ins-gps needs --front-ends")
        sys.exit(2)
    if a.world_pointers and not a.world:
        print("cpp2lean: --world-pointers needs --world")
        sys.exit(2)
    for x in a.semaphores:
        SEMAPHORES.update(y.strip() for y in x.split(",") if y.strip())
    for x in a.heap_alloc:
        HEAP_ALLOC.update(y.strip() for y in x.split(",") if y.strip())
    ARRAY_PARAMS[0] = a.array_params
    SITE_INPUTS[0] = a.site_inputs
    for x in a.boundary_call:
        if x.startswith("@"):
            with open(x[1:]) as f:
                BOUNDARY_CALL.update(y for y in re.split(r"[\s,]+", f.read()) if y)
            continue
        BOUNDARY_CALL.update(y for y in x.split(",") if y)
    for x in a.boundary_query:
        BOUNDARY_QUERY.update(y for y in x.split(",") if y)
    for x in a.boundary_static:
        BOUNDARY_STATIC.update(y for y in x.split(",") if y)
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
    opts += ["--drop " + x for x in a.drop] + ["--boundary-fn " + x for x in a.boundary_fn] + ["--output-fn " + x for x in a.output_fn]
    opts += ["--boundary-call " + portable_arg(x) for x in a.boundary_call]
    opts += ["--boundary-query " + x for x in a.boundary_query]
    opts += ["--boundary-static " + x for x in a.boundary_static]
    if a.output_log:
        opts.append("--output-log")
    if a.param_save_log:
        opts.append("--param-save-log")
    if getattr(a, "text_log", False):
        opts.append("--text-log")
    if getattr(a, "text_buffers", False):
        opts.append("--text-buffers")
    for x in sorted(TEXT_RESULTS):
        opts.append("--text-results %s" % x)
    opts += ["--enum-as-int " + x for x in getattr(a, "enum_as_int", [])]
    if a.array_params:
        opts.append("--array-params")
    if a.site_inputs:
        opts.append("--site-inputs")
    opts += ["--use " + portable_arg(x) for x in a.use]
    if a.nest:
        opts.append("--nest")
    opts += ["--type-name " + x for x in a.type_name]
    if a.general_loops:
        opts.append("--general-loops")
    if a.uninit_reads:
        opts.append("--uninit-reads")
    if a.pointer_params:
        opts.append("--pointer-params")
    if a.runtime_loops:
        opts.append("--runtime-loops")
    for flag, on in (("--c-strings", a.c_strings), ("--gotos", a.gotos), ("--byte-objects", a.byte_objects)):
        if on:
            opts.append(flag)
    if a.hal_storage:
        opts.append("--hal-storage %d" % a.hal_storage)
    if a.ekf_arrays:
        opts.append("--ekf-arrays")
    if a.ekf_types:
        opts.append("--ekf-types")
    if a.ring_buffers:
        opts.append("--ring-buffers")
    if a.reachable:
        opts.append("--reachable")
    if a.indexed_inputs:
        opts.append("--indexed-inputs")
    if a.array_offsets:
        opts.append("--array-offsets")
    if a.swap_out:
        opts.append("--swap-out")
    if getattr(a, "member_reach", False):
        opts.append("--member-reach")
    if a.member_objects:
        opts.append("--member-objects")
    if a.member_pointers:
        opts.append("--member-pointers")
    if a.ahrs_ext:
        opts.append("--ahrs-ext")
    opts += ["--sizeof " + x for x in a.sizeof]
    if a.front_ends:
        opts.append("--front-ends")
    opts += ["--world-class " + x for x in a.world_class]
    opts += ["--param-name " + x for x in a.param_name]
    if a.param_ext:
        opts.append("--param-ext")
    if a.ins_gps:
        opts.append("--ins-gps")
    if a.mavlink:
        opts.append("--mavlink")
    if a.mission:
        opts.append("--mission")
    opts += ["--null-member " + x for x in a.null_member]
    opts += ["--import " + x for x in a.imports]
    opts += ["--module-sig " + portable_path(x) for x in a.module_sig]
    opts += ["-I" + portable_path(i) for i in a.includes] + ["--clang-arg " + portable_arg(c) for c in a.clang_arg]
    text, sigs, uses_libm, lits = translate(a.file, ns, a.header, externs, ["-I" + i for i in a.includes] + a.clang_arg,
                                            (" " + " ".join(opts)) if opts else "", a.lib_dir)
    # a dotted namespace (Musl.sinf) is the module Musl.sinf, the file Musl/sinf.lean
    base = os.path.join(a.out, *ns.split("."))
    os.makedirs(os.path.dirname(base), exist_ok=True)
    with open(base + ".lean", "w") as f:
        f.write(text)
    with open(base + ".signatures.json", "w") as f:
        json.dump({"namespace": ns, "source": portable_path(a.file), "functions": sigs["functions"], "classes": sigs["classes"],
                   "enums": sigs["enums"], "free": sigs["free"], "output_log": sigs["output_log"],
                   "output_ns": sigs["output_ns"], "literals": lits, "var_info": sigs["var_info"],
                   "world": sigs["world"], **({"heap": sigs["heap"], "funcs": sigs["funcs"]} if "heap" in sigs else {}),
                   **({"mtags": sigs["mtags"]} if "mtags" in sigs else {}),
                   **({"layouts": sigs["layouts"]} if "layouts" in sigs else {})}, f, indent=1)
        f.write("\n")
    for name in ["CFloat.lean"] + (["CString.lean"] if C_STRINGS[0] or BYTE_OBJECTS[0] or HAL_STORAGE[0] else []):
        with open(os.path.join(SUPPORT_DIR, name)) as src, open(os.path.join(a.out, name), "w") as f:
            f.write(src.read())


if __name__ == "__main__":
    main()
