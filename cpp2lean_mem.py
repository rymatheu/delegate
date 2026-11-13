"""`cpp2lean.py --param-memory CONFIG`: C++ over one byte memory (README.md, "Phase 4: AP_Param").

AP_Param treats parameters as raw memory: its tables hold the addresses of objects and the `offsetof`
offsets of their members, and its code computes `base + offset`, casts the result to `AP_Param *` or
`AP_Float *`, compares addresses, and reads storage blocks straight into objects. This back end
translates such code faithfully, as C's abstract machine: one byte memory (`support/ParamMemory.lean`)
holds the constant data (the `var_info` tables and their strings, as clang evaluated their initializers:
`memir.py`), the static objects the tables point into, the static members of the translated classes, a
heap and a stack. Every pointer, reference and `ptrdiff_t` is an address (`UInt64`); every struct or
array object, and every scalar local whose address is taken (or that is bound to a reference), lives in
memory, at the offsets of clang's record layouts (`-fdump-record-layouts-complete`); the other scalar
locals are Lean variables. Each function is a `partial def` in `PMem.M` (a state monad over the memory)
translated statement by statement from clang's JSON AST; calls follow the AST's declarations (methods
of template specializations included). The value model of the rest of cpp2lean (values, paths, the
World) does not apply here: a function translated by this back end sees only addresses.

The configuration (JSON) names the units and AST filters to read, the root table, the entry functions,
the boundary (HAL) members and the statics' dynamic initializers; see ardupilot/param/AP_Param.json.
"""
import json
import os
import re
import subprocess
import sys
from fractions import Fraction

import memir

HERE = os.path.dirname(os.path.abspath(__file__))


def zlib_crc(text):
    import zlib
    return zlib.crc32(text.encode())


class Reject(Exception):
    pass


# ---------------------------------------------------------------------------------------------
# Inputs: clang's flags of a unit of the reference build, its filtered JSON AST, IR, record layouts.

def load_build(root):
    import importlib.util
    spec = importlib.util.spec_from_file_location("cpp2lean_reference_build", os.path.join(root, "reference", "build.py"))
    b = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(b)
    return b


class Units:
    def __init__(self, root, cache):
        self.b = load_build(root)
        self.units, self.template = self.b.units()
        self.cc = {self.b.rel(x["file"]): x["file"] for x in json.loads((self.b.WAF / "compile_commands.json").read_text())}
        self.srcs = {r: os.path.join(str(self.b.AP), r) for r, _ in self.units}
        for h in self.b.HAL_SOURCES:
            self.srcs["reference/hal/" + h] = str(self.b.HERE / "hal" / h)
        self.cache = cache
        os.makedirs(cache, exist_ok=True)

    def flags(self, rel):
        if rel.startswith("reference/hal/"):
            first = next(r for r, _ in self.units if r.startswith("ArduCopter/"))
            fl = self.b.flags_of(self.template, self.cc[first])
        else:
            fl = self.b.flags_of(next(a for r, a in self.units if r == rel), self.cc[rel])
        return [f for f in fl if not f.startswith("-O")] + ["-Wno-everything"]

    def run(self, rel, extra, out, src=None):
        path = os.path.join(self.cache, out)
        if not os.path.exists(path):
            p = subprocess.run(["clang++"] + self.flags(rel) + extra + [src or self.srcs[rel]], cwd=str(self.b.WAF),
                               capture_output=True, text=True)
            if p.returncode != 0:
                raise Reject("clang failed on %s: %s" % (rel, p.stderr[-2000:]))
            with open(path + ".tmp", "w") as f:
                f.write(p.stdout)
            os.replace(path + ".tmp", path)
        with open(path) as f:
            return f.read()

    def ir(self, rel):
        path = os.path.join(self.cache, rel.replace("/", "__") + ".ll")
        if not os.path.exists(path):
            p = subprocess.run(["clang++"] + self.flags(rel) + ["-O0", "-S", "-emit-llvm", "-o", path, self.srcs[rel]],
                               cwd=str(self.b.WAF), capture_output=True, text=True)
            if p.returncode != 0:
                raise Reject("clang -emit-llvm failed on %s: %s" % (rel, p.stderr[-2000:]))
        with open(path) as f:
            return memir.Module(f.read())

    def ast(self, rel, flt):
        text = self.run(rel, ["-fsyntax-only", "-Xclang", "-ast-dump=json", "-Xclang", "-ast-dump-filter=" + flt],
                        rel.replace("/", "__") + "." + flt.replace(":", "_") + ("~lc" if not any(c.isupper() for c in flt) else "") + ".json")
        dec, i, objs = json.JSONDecoder(), 0, []
        while i < len(text):
            while i < len(text) and text[i] in " \n\r\t":
                i += 1
            if i >= len(text):
                break
            if text[i] != "{":
                i = text.index("\n", i) + 1
                continue
            o, i = dec.raw_decode(text, i)
            objs.append(o)
        return objs

    def layouts(self, rel):
        return parse_layouts(self.run(rel, ["-fsyntax-only", "-Xclang", "-fdump-record-layouts-complete"],
                                      rel.replace("/", "__") + ".layouts"), getattr(self, "primary_base", False))


def parse_layouts(text, primary_base=False):
    """clang's record layout dump -> {record name: Rec}. primary_base (vehicle configuration): a polymorphic class's
    `(primary base)` is a base too (before: a field named `base)`)."""
    recs = {}
    for block in text.split("*** Dumping AST Record Layout")[1:]:
        lines = [ln for ln in block.split("\n") if "|" in ln]
        if not lines:
            continue
        head = lines[0].split("|", 1)[1].strip()
        name = re.sub(r"^(struct|class|union) ", "", head.replace(" (empty)", ""))
        rec = {"fields": [], "size": None, "align": None}
        stack = [(0, rec)]
        for ln in lines[1:]:
            left, right = ln.split("|", 1)
            if right.strip().startswith("["):
                m = re.search(r"sizeof=(\d+).*?align=(\d+)", right)
                if m and rec["size"] is None:
                    rec["size"], rec["align"] = int(m.group(1)), int(m.group(2))
                continue
            m = re.search(r"sizeof=(\d+)", right)
            if not left.strip():
                continue
            depth = (len(right) - len(right.lstrip(" "))) // 2
            text_ = right.strip()
            pos = left.strip()
            if ":" in pos:
                byte, bits = pos.split(":")
                lo, hi = bits.split("-")
                off, bitoff, width = int(byte), int(byte) * 8 + int(lo), int(hi) - int(lo) + 1
            else:
                off, bitoff, width = int(pos), None, None
            fname = None
            is_base = text_.endswith("(base)") or text_.endswith("(base) (empty)") or "(primary virtual base)" in text_ or "(virtual base)" in text_ or \
                (primary_base and (text_.endswith("(primary base)") or text_.endswith("(primary base) (empty)")))
            ftext = text_.replace(" (empty)", "")
            if ftext.endswith(")") and ("(anonymous at" in ftext or "(unnamed at" in ftext):
                fname, ftype = "", ftext
            elif is_base:
                fname, ftype = "(base)", re.sub(r" \((primary )?(virtual )?base\)$", "", ftext)
            else:
                parts = ftext.rsplit(" ", 1)
                if len(parts) == 2:
                    ftype, fname = parts
                else:
                    ftype, fname = ftext, ""
            node = {"name": fname, "type": re.sub(r"^(struct|class|union) ", "", ftype), "off": off, "bitoff": bitoff,
                    "width": width, "base": is_base, "fields": []}
            while stack and stack[-1][0] >= depth:
                stack.pop()
            stack[-1][1]["fields"].append(node)
            stack.append((depth, node))
        recs.setdefault(norm_rec(name), rec)
    return recs


# (vehicle configuration, Phase 5c: `packed_records`) clang's `-fdump-record-layouts` prints the layout of a record that
# MAVPACKED (`typedef struct S {...} __attribute__((packed)) T;`, mavlink_types.h) declares as it was before the
# attribute after the closing brace was applied: `struct __mavlink_gps_global_origin_t` with `time_usec` at 16 and sizeof
# 24, where the compiled code (offsetof 12, sizeof 20; the AST's RecordDecl carries PackedAttr) and the wire format have
# 12 and 20. The message structs of the MAVLink headers named by the key are laid out packed: each member at the byte
# after the previous one, alignment 1, in declaration order (as the dump lists them). Bit-fields are rejected.
SCALAR_SIZES = {"char": 1, "signed char": 1, "unsigned char": 1, "int8_t": 1, "uint8_t": 1, "_Bool": 1, "bool": 1,
                "short": 2, "unsigned short": 2, "int16_t": 2, "uint16_t": 2, "int": 4, "unsigned int": 4, "int32_t": 4,
                "uint32_t": 4, "float": 4, "long": 8, "unsigned long": 8, "long long": 8, "unsigned long long": 8,
                "int64_t": 8, "uint64_t": 8, "double": 8}


def repack_layout(rec, name):
    off = 0
    for f in rec["fields"]:
        if f["base"] or f["width"] is not None or f["fields"]:
            raise Reject("packed record `%s`: member `%s` is not a scalar or an array of scalars" % (name, f["name"]))
        m = re.match(r"^(.*?)((?:\[\d+\])*)$", f["type"].strip())
        base, dims = m.group(1).strip(), re.findall(r"\[(\d+)\]", m.group(2))
        if base not in SCALAR_SIZES:
            raise Reject("packed record `%s`: member type `%s`" % (name, f["type"]))
        n = SCALAR_SIZES[base]
        for d in dims:
            n *= int(d)
        f["off"] = off
        off += n
    rec["size"], rec["align"] = off, 1


# ---------------------------------------------------------------------------------------------
# Types.

INTS = {"char": (8, True), "signed char": (8, True), "unsigned char": (8, False), "short": (16, True),
        "unsigned short": (16, False), "int": (32, True), "unsigned int": (32, False), "long": (64, True),
        "unsigned long": (64, False), "long long": (64, True), "unsigned long long": (64, False),
        "_Bool": None, "bool": None, "wchar_t": (32, True), "char16_t": (16, False), "char32_t": (32, False),
        "int8_t": (8, True), "uint8_t": (8, False), "int16_t": (16, True), "uint16_t": (16, False),
        "int32_t": (32, True), "uint32_t": (32, False), "int64_t": (64, True), "uint64_t": (64, False),
        "size_t": (64, False), "ssize_t": (64, True), "ptrdiff_t": (64, True), "intptr_t": (64, True), "uintptr_t": (64, False)}


def strip_cv(s):
    s = s.strip()
    while True:
        t = re.sub(r"^(const|volatile)\s+", "", s)
        t = re.sub(r"(\s+|(?<=\*))(const|volatile)$", "", t)
        if t == s:
            return s
        s = t


def norm_rec(s):
    s = strip_cv(s)
    s = re.sub(r"\b(struct|class|union|enum)\s+(?![^(]*\))", "", s)
    for a, b in (("int8_t", "signed char"), ("uint8_t", "unsigned char"), ("int16_t", "short"), ("uint16_t", "unsigned short"),
                 ("int32_t", "int"), ("uint32_t", "unsigned int"), ("Vector3f", "Vector3<float>")):
        s = re.sub(r"(?<=[<, ])%s(?=[>,])" % a, b, s)
    return s.strip()


class T:
    """kind: void bool int float double ptr rec arr enum fn"""

    def __init__(self, kind, bits=0, signed=False, name=None, elem=None, n=0):
        self.kind, self.bits, self.signed, self.name, self.elem, self.n = kind, bits, signed, name, elem, n

    def __repr__(self):
        return "T(%s,%s,%s,%s)" % (self.kind, self.bits, self.signed, self.name)

    @property
    def lean(self):
        k = self.kind
        if k == "bool":
            return "Bool"
        if k in ("int", "enum"):
            return ("Int" if self.signed else "UInt") + str(self.bits)
        if k == "float":
            return "Binary32"
        if k == "double":
            return "Binary64"
        if k in ("ptr", "ref"):
            return "UInt64"
        if k == "void":
            return "Unit"
        raise Reject("no Lean type for %r" % self)

    def scalar(self):
        return self.kind in ("bool", "int", "enum", "float", "double", "ptr")

    def suffix(self):
        """the load/store suffix of PMem"""
        k = self.kind
        if k == "bool":
            return "B"
        if k in ("int", "enum"):
            return ("I" if self.signed else "U") + str(self.bits)
        if k == "float":
            return "F32"
        if k == "double":
            return "F64"
        if k == "ptr":
            return "U64"
        raise Reject("no memory access for %r" % self)


BOOL = T("bool")
VOID = T("void")
FLOAT = T("float")
DOUBLE = T("double")
U64 = T("int", 64, False)
I64 = T("int", 64, True)
I32 = T("int", 32, True)
PTR = T("ptr")


# ---------------------------------------------------------------------------------------------
# The translator.

PREC_ATOM = 100


def par(s):
    s = s.strip()
    if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*|\([^()]*\)|-?\d+", s):
        return s
    depth = 0
    if s.startswith("(") and s.endswith(")"):
        ok = True
        for i, c in enumerate(s):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(s) - 1:
                ok = False
                break
        if ok:
            return s
    return "(" + s + ")"


def _walk(n):
    """(Phase 5c) every node of a tree, pre-order."""
    yield n
    for c in kids(n):
        if isinstance(c, dict):
            yield from _walk(c)


def kids(n):
    return n.get("inner", [])


ID_KEYS = ("id", "previousDecl", "referencedMemberDecl", "parentDeclContextId")


def prefix_ids(n, p):
    """Make the declaration ids of one AST dump distinct from another's (ids are addresses of one clang run)."""
    if isinstance(n, dict):
        for k in ID_KEYS:
            v = n.get(k)
            if isinstance(v, str) and v.startswith("0x"):
                n[k] = p + v
        for v in n.values():
            if isinstance(v, (dict, list)):
                prefix_ids(v, p)
    elif isinstance(n, list):
        for v in n:
            prefix_ids(v, p)


def parse_fn_type(sig):
    """`void (void *, int)` -> ("void", ["void *", "int"]); (None, None) if not a function type."""
    sig = sig.strip()
    if not sig.endswith(")") or "(" not in sig:
        return None, None
    depth = 0
    for i in range(len(sig) - 1, -1, -1):
        if sig[i] == ")":
            depth += 1
        elif sig[i] == "(":
            depth -= 1
            if depth == 0:
                break
    ret, inner = sig[:i].strip(), sig[i + 1:-1]
    ps, depth, cur = [], 0, ""
    for ch in inner:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == "," and depth == 0:
            ps.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip() and cur.strip() != "void":
        ps.append(cur.strip())
    return ret, ps


def mark_pattern(n):
    if isinstance(n, dict):
        if n.get("kind") in ("FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl", "CXXDestructorDecl"):
            n["_pattern"] = True
        for c in n.get("inner", []):
            if c.get("kind") in ("FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl", "CXXDestructorDecl",
                                 "CXXRecordDecl", "FunctionTemplateDecl"):
                mark_pattern(c)


def split_scope(q):
    """`A::B<C::D>::f` -> ["A", "B<C::D>", "f"] (`::` outside template arguments)."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(q):
        c = q[i]
        if c == "<" and not cur.startswith("operator"):
            depth += 1
        elif c == ">" and depth > 0:
            depth -= 1
        if depth == 0 and q.startswith("::", i) and not cur.startswith("operator"):
            out.append(cur)
            cur = ""
            i += 2
            continue
        cur += c
        i += 1
    out.append(cur)
    return out


def strip_targs(q):
    return "::".join(c if c.startswith("operator") else re.sub(r"<.*>$", "", c) for c in split_scope(q))


def base_name(d):
    """A demangled function name without its parameter list (and `const`): `Vector3<float>::length() const` ->
    `Vector3<float>::length`; a data symbol's name unchanged."""
    d = re.sub(r"\s+const$", "", d.strip())
    if not d.endswith(")"):
        return d
    depth = 0
    for i in range(len(d) - 1, -1, -1):
        if d[i] == ")":
            depth += 1
        elif d[i] == "(":
            depth -= 1
            if depth == 0:
                d = d[:i]
                break
    # a template function's demangled name starts with its result type: the name is after the last space at
    # template depth 0
    depth, cut = 0, 0
    for i, c in enumerate(d):
        if c == "<":
            depth += 1
        elif c == ">":
            depth -= 1
        elif c == " " and depth == 0 and not d[:i].endswith("operator"):
            cut = i + 1
    return d[cut:]


def lean_name(s):
    s = s.replace("::", ".").replace("~", "dtor_")
    s = re.sub(r"<([^<>]*(?:<[^<>]*>[^<>]*)*)>", lambda m: "'" + re.sub(r"[^A-Za-z0-9_]+", "_", m.group(1)).strip("_"), s)
    return re.sub(r"[^A-Za-z0-9_.']", "_", s)


class Fn:
    def __init__(self, node, qual, parent_rec):
        self.node, self.qual, self.parent_rec = node, qual, parent_rec
        self.static = node.get("storageClass") == "static" or node["kind"] == "FunctionDecl"
        self.ctor = node["kind"] == "CXXConstructorDecl"
        self.params = [k for k in kids(node) if k["kind"] == "ParmVarDecl"]
        self.body = next((k for k in kids(node) if k["kind"] == "CompoundStmt"), None)
        self.lean = None


class Translator:
    def __init__(self, cfg, units):
        self.cfg, self.U = cfg, units
        units.primary_base = bool(cfg.get("vehicle"))
        self.layouts = {}
        self.layout_loaded = set(cfg["layout_units"])
        for u in cfg["layout_units"]:
            for k, v in units.layouts(u).items():
                self.layouts.setdefault(k, v)
        self.idx = {}        # id -> node
        self.parent = {}     # id -> parent node
        self.qual = {}       # id -> qualified name of a decl
        self.fns = {}        # canonical id -> Fn (with body)
        self.enums = {}      # enum name -> (bits, signed)
        self.enum_consts = {}  # id -> int value
        self.statics = {}    # id of static VarDecl -> qualified name
        self.static_nodes = {}
        self.enum_by_name = {}
        self.enum_by_qual = {}   # (Phase 5b) (qualified enumeration, constant) -> value
        self.anon_names = {}
        self.enum_ids = {}
        self.typedefs = {}
        self.recnodes = {}
        self.decls = {}      # (vehicle configuration) qualified name -> declarations (with or without a body)
        self._probed = set()
        self._ensured = set()
        self.fn_addrs = {}       # mangled name -> address (functions whose address is taken)
        self.fnptr_sigs = {}     # function type -> {"targets": {address: Fn}}
        self.vdispatch = {}      # (class, name, signature) -> dispatcher (calls through Mode * on copter's members)
        self._irmods, self._irdem, self._scanned = {}, {}, set()
        dump = 0
        self.dumped = set()
        for rel, filters in cfg["asts"].items():
            for flt in filters:
                self._dump_unit = rel.split("#")[0]
                self.dumped.add((self._dump_unit, flt))
                for o in units.ast(rel.split("#")[0], flt):
                    prefix_ids(o, "d%d:" % dump)
                    self.index(o, None, [])
                dump += 1
        self.ndumps = dump
        # out-of-line definitions whose class declaration is not in any dump (`AP_HAL::Storage::erase` in Storage.cpp):
        # the qualified name from the mangled name
        lone = [f for f in set(self.fns.values()) if "::" not in f.qname and (f.node.get("mangledName") or "").startswith("__ZN")]
        if lone:
            out = subprocess.run(["c++filt"], input="\n".join(f.node["mangledName"] for f in lone), capture_output=True,
                                 text=True).stdout.split("\n")
            for f, d in zip(lone, out):
                d = d.strip()
                if "(" in d and "<" not in d:
                    f.qname = d[:d.index("(")]
        if cfg.get("dynamic"):
            # (GCS configuration) the same definition in several dumps (overlapping filters, several units): one Fn
            canon = {}
            for k2, g in list(self.fns.items()):
                key = (g.qname, g.node.get("type", {}).get("qualType"))
                if cfg.get("vehicle"):
                    key += (g.node.get("mangledName"),)     # template instances share name and type
                self.fns[k2] = canon.setdefault(key, g)
            self._canon = canon
        self.used = {}       # canonical fn id -> Fn, in translation order
        self.order = []
        self.names = {}
        self.static_addr = {}   # qualified static name -> address (filled by the image)
        self.static_syms = {}   # (Phase 5b) a discriminated static local's name -> (IR symbol, unit)
        self.literals = {}      # string literal bytes -> address
        self.hal_ref_params = set()   # (Phase 5d) HAL calls' reference parameters passed by address (key/index)
        self.boundary = cfg.get("boundary", {})
        self.fn_by_mangled = {}
        self.vehicle_log = []
        self.bridge_calls = {}   # (vehicle configuration) estimator function -> {"sig", "sites"}
        self.bridge_fields = {}  # estimator data member -> sites
        self.bridge_field_adapters = {}  # (Phase 5b) estimator data member read through an adapter -> its description
        self.bridge_adapters = {}  # (bridge_module) (function, arity) -> the adapter's signature (<ns>.bridge.json)
        self.hal_calls = {}      # HAL member outside the configured boundary -> sites
        self.rejected = []       # (qualified name, location, reason): functions emitted as stubs
        self.musl_imports = set()
        self.bridge_re = re.compile(cfg["bridge_classes"]) if cfg.get("vehicle") and cfg.get("bridge_classes") else None
        if cfg.get("vehicle"):
            for g in set(self.fns.values()):
                if g.node.get("mangledName"):
                    self.fn_by_mangled.setdefault(g.node["mangledName"], g)

    # -- indexing
    def index(self, n, parent, scope):
        k = n.get("kind", "")
        for where in (n.get("loc", {}), n.get("range", {}).get("begin", {})):
            if isinstance(where, dict):
                if "file" in where:
                    self._cur_file = where["file"]
                sp = where.get("spellingLoc") or where.get("expansionLoc")
                if isinstance(sp, dict) and "file" in sp:
                    self._cur_file = sp["file"]
        if k == "CXXConversionDecl" and self.cfg.get("dynamic"):
            k = "CXXMethodDecl"     # (GCS configuration) `operator const T &()` of AP_ParamT: a member function
        if k in ("CXXMethodDecl", "FunctionDecl", "CXXConstructorDecl"):
            n["_file"] = getattr(self, "_cur_file", None)
            n["_unit"] = getattr(self, "_dump_unit", None)
        if "id" in n:
            if n["id"] in self.idx and self.idx[n["id"]] is not n:
                # the same declaration in several filter outputs: keep the one with a body
                old = self.idx[n["id"]]
                if any(x.get("kind") == "CompoundStmt" for x in kids(old)):
                    return
            self.idx[n["id"]] = n
            self.parent[n["id"]] = parent
        name = n.get("name")
        sc = scope
        if k in ("NamespaceDecl", "CXXRecordDecl", "ClassTemplateSpecializationDecl") and name:
            sc = scope + [name]
            if k == "ClassTemplateSpecializationDecl":
                tas = [self.targ_text(a) for a in kids(n) if a.get("kind") == "TemplateArgument"]
                if self.cfg.get("vehicle"):
                    tas = [x for x in tas if x != ""]
                sc = scope + [name + "<" + ", ".join(tas) + ">"]
        if k in ("CXXMethodDecl", "FunctionDecl", "CXXConstructorDecl") and name:
            q = "::".join(scope + [name]) if not n.get("previousDecl") or "::" not in name else name
            body = any(x.get("kind") == "CompoundStmt" for x in kids(n))
            if body:
                canon = n.get("previousDecl") or n["id"]
                # out-of-line definitions: the class scope is in the AST's parent chain of the declaration
                self.fns[canon] = Fn(n, None, None)
                self.fns[n["id"]] = self.fns[canon]
                cq = self.qual.get(canon) if canon != n["id"] else None
                self.fns[canon].qname = cq or "::".join(scope + [name])
                decl = self.idx.get(canon) or n
                self.fns[canon].is_static = decl.get("storageClass") == "static" or n.get("storageClass") == "static" or k == "FunctionDecl"
            self.qual[n["id"]] = self.qual.get(n.get("previousDecl"), None) or "::".join(scope + [name])
            if self.cfg.get("vehicle"):
                self.decls.setdefault(self.qual[n["id"]], []).append(n)
        if k == "CXXRecordDecl" and n.get("completeDefinition") and self.cfg.get("dynamic"):
            # (GCS configuration) record definitions, for the default member initializers of member objects
            loc = n.get("loc", {})
            if name:
                self.recnodes.setdefault("::".join(scope + [name]), n)
            if "line" in loc or "col" in loc:
                f0 = os.path.basename(getattr(self, "_cur_file", "") or "")
                ln = loc.get("line", getattr(self, "_last_line", "?"))
                self.recnodes.setdefault("%s:%s:%s" % (f0, ln, loc.get("col")), n)
                lc = self.recnodes.setdefault(("lc", ln, loc.get("col")), [])
                if all(x.get("id") != n.get("id") and x is not n for x in lc) and not any(
                        [y.get("name") for y in kids(x) if y.get("kind") == "FieldDecl"] == [y.get("name") for y in kids(n) if y.get("kind") == "FieldDecl"] for x in lc):
                    lc.append(n)
        if isinstance(n.get("loc"), dict) and "line" in n["loc"]:
            self._last_line = n["loc"]["line"]
        if k == "CXXConstructorDecl" and n.get("isImplicit") and name and "line" in n.get("loc", {}):
            # the implicit constructor of an unnamed struct named by a typedef (`typedef struct {...} ParamToken`)
            self.anon_names.setdefault(name, (n["loc"]["line"], n["loc"]["col"]))
        if k == "EnumDecl":
            ut = n.get("fixedUnderlyingType", {}).get("desugaredQualType") or n.get("fixedUnderlyingType", {}).get("qualType")
            vals = []
            for c in kids(n):
                if c.get("kind") == "EnumConstantDecl":
                    ek = [x for x in kids(c) if "Comment" not in x.get("kind", "")]
                    v = self.const_int(ek[0]) if ek else (vals[-1] + 1 if vals else 0)
                    vals.append(v)
                    self.enum_consts[c["id"]] = v
                    self.enum_by_name[c["name"]] = v
                    if self.cfg.get("vehicle"):
                        # (Phase 5b) by the enumeration's qualified name too: a constant whose declaration is in another
                        # unit's dump (another id) is not found by its name alone when names collide (`AP_Arming::Method::
                        # MAVLINK` is 1; the last `MAVLINK` indexed was 3)
                        for nm in ["::".join(scope + [name or ""]), name]:
                            if nm:
                                self.enum_by_qual[(nm, c["name"])] = v
            if ut:
                bits, signed = INTS[strip_cv(ut)]
            else:
                bits, signed = 32, any(v < 0 for v in vals)
            for nm in ["::".join(scope + [name or ""]), name]:
                if nm:
                    self.enums[nm] = (bits, signed)
            self.enum_ids[n["id"]] = (bits, signed)
        if k == "TypedefDecl" and name and self.cfg.get("dynamic"):
            # (GCS configuration) `typedef struct __mavlink_status {...} mavlink_status_t;`: the record's name
            dq = n.get("type", {}).get("desugaredQualType") or n.get("type", {}).get("qualType")
            if dq:
                self.typedefs.setdefault(name, norm_rec(dq))
        if k == "TypedefDecl" and name:
            # `typedef enum : int16_t {...} Function;`
            def enum_ref(x):
                if x.get("kind") == "EnumType" and isinstance(x.get("decl"), dict):
                    return x["decl"].get("id")
                if isinstance(x.get("ownedTagDecl"), dict) and x["ownedTagDecl"].get("kind") == "EnumDecl":
                    return x["ownedTagDecl"].get("id")
                for y in kids(x):
                    r = enum_ref(y)
                    if r:
                        return r
                return None
            eid = enum_ref(n)
            if eid in self.enum_ids:
                self.enums["::".join(scope + [name])] = self.enum_ids[eid]
                dq = n.get("type", {}).get("desugaredQualType")
                if dq:
                    self.enums[norm_rec(dq)] = self.enum_ids[eid]
        if k == "VarDecl" and n.get("storageClass") == "static" or (k == "VarDecl" and parent is not None and parent.get("kind") in ("CXXRecordDecl", "ClassTemplateSpecializationDecl")):
            self.statics[n["id"]] = "::".join(scope + [name])
            self.static_nodes.setdefault("::".join(scope + [name]), []).append(n)
        elif k == "VarDecl" and self.cfg.get("static_construction") and n.get("name") and \
                (parent is None or parent.get("kind") in ("TranslationUnitDecl", "NamespaceDecl")) and not n.get("previousDecl"):
            # (static construction) a global's declaration or definition (`Copter copter;`): its initializer
            self.static_nodes.setdefault("::".join(scope + [name]), []).append(n)
        if k == "VarDecl" and n.get("previousDecl") and parent is None:
            # out-of-line definition of a static member (AP_Param.cpp's `StorageAccess AP_Param::_storage(...)`)
            pd = n["previousDecl"]
            self.static_nodes.setdefault(("def", pd), []).append(n)
        if self.cfg.get("vehicle") and k in ("FunctionTemplateDecl", "ClassTemplateDecl"):
            # (vehicle configuration) the template's pattern (the first function or record child): dependent types,
            # never translated; the instances follow it
            for c in kids(n):
                if c.get("kind") in ("FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl", "CXXRecordDecl"):
                    mark_pattern(c)
                    break
        for c in kids(n):
            self.index(c, n, sc)

    def targ_text(self, a):
        if self.cfg.get("vehicle") and "value" in a and re.fullmatch(r"'(\\.|[^\\])'", str(a["value"])):
            return str(decode_c_string('"' + str(a["value"])[1:-1] + '"')[0])     # a char-valued argument: its number
        if self.cfg.get("vehicle") and not a.get("type") and "value" not in a and not a.get("decl"):
            # (vehicle configuration) a pack: its elements (`Functor<void>`: an empty pack)
            return ", ".join(self.targ_text(x) for x in kids(a) if x.get("kind") == "TemplateArgument")
        t = a.get("type", {})
        if t:
            return t.get("qualType", "?")
        if "value" in a:
            return str(a["value"])
        return "?"

    def const_int(self, n):
        k = n.get("kind")
        if k == "ConstantExpr" and "value" in n:
            return int(n["value"])
        if k == "IntegerLiteral":
            return int(n["value"])
        if k in ("ImplicitCastExpr", "ParenExpr", "CStyleCastExpr", "ConstantExpr", "CXXStaticCastExpr"):
            return self.const_int(kids(n)[0])
        if k == "UnaryOperator" and n["opcode"] == "-":
            return -self.const_int(kids(n)[0])
        if k == "UnaryOperator" and n["opcode"] == "~":
            return ~self.const_int(kids(n)[0])
        if k == "BinaryOperator":
            a, b = (self.const_int(x) for x in kids(n))
            op = n["opcode"]
            return {"<<": lambda: a << b, ">>": lambda: a >> b, "|": lambda: a | b, "&": lambda: a & b,
                    "+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b}[op]()
        if k == "DeclRefExpr" and n["referencedDecl"]["kind"] == "EnumConstantDecl":
            rd = n["referencedDecl"]
            if rd["id"] not in self.enum_consts and self.cfg.get("vehicle"):
                et = re.sub(r"^(enum|const|class|struct)\s+", "", ((rd.get("type") or {}).get("qualType") or "").strip())
                if (et, rd["name"]) in self.enum_by_qual:
                    return self.enum_by_qual[(et, rd["name"])]
            return self.enum_consts.get(rd["id"], self.enum_by_name.get(rd["name"]))
        if k == "CharacterLiteral":
            return int(n["value"])
        raise Reject("not a constant integer: %s" % k)

    # -- types
    def ty(self, tj):
        """A clang JSON type object -> T"""
        if tj is None:
            return VOID
        s = tj.get("desugaredQualType") or tj.get("qualType")
        return self.ty_str(s, tj.get("qualType"))

    def ty_str(self, s, sugar=None):
        s = strip_cv(s)
        m = re.match(r"^typename std::enable_if<.*, (\w+)>::type$", s)
        if m:
            s = m.group(1)
        if s.endswith("&") or s.endswith("&&"):
            return T("ref", name=s.rstrip("&").strip())
        if self.cfg.get("vehicle"):
            m = re.match(r"^typename (?:std::(?:__1::)?)?__promote<(.*)>::type$", s)
            if m:
                # libc++'s promotion of <cmath>'s mixed overloads: float if every argument is float, else double
                return FLOAT if all(x.strip() == "float" for x in m.group(1).split(",")) else DOUBLE
            if re.search(r"\(\*\s*(const|volatile)\s*\)", s):
                return T("ptr", name=re.sub(r"\(\*\s*(const|volatile)\s*\)", "(*)", s))     # `void (*const)(void *)`
            if re.search(r"\(unnamed enum at ", s) or re.search(r"\(anonymous enum at ", s):
                return T("enum", 32, False, name=s)
        m = re.match(r"^(.*?)\s*\(&&?\)\s*(\[\d+\])$", s)
        if m and self.cfg.get("dynamic"):
            return T("ref", name="%s %s" % (m.group(1), m.group(2)))      # (GCS configuration) `T (&)[N]`
        if "(*)" in s or s.endswith("*") or s == "std::nullptr_t" or s == "nullptr_t":
            return T("ptr", name=s[:-1].strip() if s.endswith("*") else s)
        m = re.match(r"^(.*?)\s*\[(\d+)\]$", s)
        if m:
            return T("arr", elem=self.ty_str(m.group(1)), n=int(m.group(2)))
        if s == "void":
            return VOID
        if s in ("bool", "_Bool"):
            return BOOL
        if s == "float":
            return FLOAT
        if s == "double":
            return DOUBLE
        if s in INTS and INTS[s]:
            b, sg = INTS[s]
            return T("int", b, sg)
        e = norm_rec(s)
        if e not in self.enums and "::" in e and self.cfg.get("dynamic") and e.split("::")[-1] in self.enums:
            e = e.split("::")[-1]       # (GCS configuration) an enum of a class dumped alone (`AP_SerialManager::SerialProtocol`)
        if e in self.enums:
            b, sg = self.enums[e]
            return T("enum", b, sg, name=e)
        if s.startswith("enum "):
            return T("enum", 32, False, name=e)
        if self.cfg.get("dynamic") and s in getattr(self, "typedefs", {}) and self.typedefs[s] != s:
            return self.ty_str(self.typedefs[s], sugar)     # (GCS configuration) a typedef of a number
        r = norm_rec(s)
        if "(" in r and ")" in r and "unnamed" not in r and "anonymous" not in r:
            return T("fn", name=r)
        if self.cfg.get("vehicle") and "::" not in r and r not in self.layouts and r not in self._probed and \
                re.fullmatch(r"\w+", r) and getattr(self, "_cur_unit", None):
            # (vehicle configuration) a typedef of a number or an enum not dumped yet (`ftype`, `NAV_TAKEOFF_FLAGS`)
            self._probed.add(r)
            try:
                self.rec_layout(r)
            except Reject:
                self.add_dump(self._cur_unit, r)
                if r in self.enums or (r in self.typedefs and self.typedefs[r] != r):
                    return self.ty_str(s, sugar)
        if self.cfg.get("vehicle") and "::" in r and r not in self.layouts and r not in self._probed:
            # (vehicle configuration) a nested type that has no record layout: an enum of a class not dumped yet
            self._probed.add(r)
            try:
                self.rec_layout(r)
            except Reject:
                u = getattr(self, "_cur_unit", None)
                comps = split_scope(r)
                if u and len(comps) >= 2:
                    self.add_dump(u, re.sub(r"<.*>$", "", comps[-2]))
                    if r in self.enums or (r.split("::")[-1] in self.enums):
                        return self.ty_str(s, sugar)
        return T("rec", name=r)

    def rec_layout(self, name):
        rec = self.rec_layout_dumped(name)
        pr = self.cfg.get("packed_records")
        if pr and not rec.get("_packed_checked"):
            rec["_packed_checked"] = True
            if re.match(pr, norm_rec(name)) or any(re.match(pr, k) for k, v in self.layouts.items() if v is rec):
                repack_layout(rec, norm_rec(name))
        return rec

    def rec_layout_dumped(self, name):
        name = norm_rec(name)
        if name in self.layouts:
            return self.layouts[name]
        # a name of the enclosing class's scope (`const struct GroupInfo *` inside AP_Param): the unique qualified match
        c = [k for k in self.layouts if k.endswith("::" + name)]
        if len(c) == 1:
            return self.layouts[c[0]]
        if name in self.typedefs and self.typedefs[name] != name:
            return self.rec_layout(self.typedefs[name])
        m = re.search(r"\((?:unnamed|anonymous)(?: struct| union)? at (.*):(\d+):(\d+)\)$", name)
        if m and self.cfg.get("dynamic"):
            # (GCS configuration) an unnamed record (a static table's element, an anonymous union): by its place
            suf = "%s:%s:%s)" % (os.path.basename(m.group(1)), m.group(2), m.group(3))
            c = [k for k in self.layouts if k.endswith(suf) and ("unnamed" in k or "anonymous" in k)]
            if c:
                return self.layouts[sorted(c, key=len)[0]]
        if self.cfg.get("vehicle"):
            alt = name.replace("bool", "_Bool")
            if alt in self.layouts:
                return self.layouts[alt]
            # (vehicle configuration) the layouts of the unit being translated, of the units configured, of a unit
            # that defines the class's members
            cu = []
            try:
                cu = self.class_units(name)[:1]
            except Exception:
                cu = []
            for u in [getattr(self, "_cur_unit", None)] + list(self.cfg.get("more_layout_units", [])) + cu:
                if u and u not in self.layout_loaded:
                    self.layout_loaded.add(u)
                    for k, v in self.U.layouts(u).items():
                        self.layouts.setdefault(k, v)
                    return self.rec_layout(name)
        short = name.split("::")[-1]
        if short in self.anon_names:
            ln, col = self.anon_names[short]
            c = [k for k in self.layouts if k.endswith(":%d:%d)" % (ln, col)) and "(unnamed at" in k]
            if len(c) > 1 and len(set(os.path.basename(k.split(" at ")[1]) for k in c)) == 1:
                c = c[:1]
            if len(c) == 1:
                return self.layouts[c[0]]
        raise Reject("no record layout for `%s`" % name)

    def size_of(self, t):
        k = t.kind
        if k == "bool":
            return 1
        if k in ("int", "enum"):
            return t.bits // 8
        if k == "float":
            return 4
        if k in ("double", "ptr"):
            return 8
        if k == "arr":
            return t.n * self.size_of(t.elem)
        if k == "rec":
            return self.rec_layout(t.name)["size"]
        raise Reject("sizeof %r" % t)

    def field(self, recname, fname):
        """(byte offset, bit offset or None, width) of field fname of record recname, searching bases."""
        rec = self.rec_layout(recname)

        def find(node, base_off):
            for f in node["fields"]:
                if not f["base"] and f["name"] == fname:
                    return f, base_off
            for f in node["fields"]:
                if f["base"]:
                    r = find(f, 0)
                    if r:
                        return r
            # anonymous unions/structs: their members
            for f in node["fields"]:
                if not f["base"] and ("anonymous" in f["type"] or "unnamed" in f["type"]):
                    r = find(f, 0)
                    if r:
                        return r
            return None
        r = find(rec, 0)
        if r is None:
            raise Reject("no field `%s` in the layout of `%s`" % (fname, recname))
        return r[0]

    # -- functions
    def fn_of(self, did, qname=None, ftype=None):
        f = self.fns.get(did)
        if f is None:
            n = self.idx.get(did)
            q = self.qual.get(did) or qname
            ty = (n or {}).get("type", {}).get("qualType") if n else ftype
            if q and "<" in q and self.cfg.get("vehicle"):
                # (vehicle configuration) a char-valued template argument printed as a character (`'\a'`): its number
                q = re.sub(r"(?<=[<, ])'(\\.|[^\\'])'(?=[>,])", lambda m: str(decode_c_string('"' + m.group(1) + '"')[0]), q)
            if q and "<" in q:
                # template arguments spelled as enumerators (`AP_ParamTBase<short, AP_PARAM_INT16>`): their values
                q = re.sub(r"(?<=[<, ])([A-Za-z_]\w*)(?=[>,])", lambda m: str(self.enum_by_name[m.group(1)])
                           if m.group(1) in self.enum_by_name else m.group(1), q)
            cands = [g for g in set(self.fns.values()) if g.qname == q]
            if not cands and q and "::" not in q:
                cands = [g for g in set(self.fns.values()) if g.qname.endswith("::" + q)]
            if self.cfg.get("vehicle"):
                cands = [g for g in cands if not g.node.get("_pattern")]
                if ty and cands and "<" not in (q or "") and not any(g.node.get("type", {}).get("qualType") == ty for g in cands) and \
                        not getattr(self, "_resolving", False):
                    # (vehicle configuration) no instance of exactly the callee's type: the caller's unit has it
                    self._resolving = True
                    try:
                        self.resolve_fn(did, q, force_hint=True)
                    finally:
                        self._resolving = False
                    cands = [g for g in set(self.fns.values()) if g.qname == q and not g.node.get("_pattern")] or cands
                    cands = [g for g in cands if g.node.get("type", {}).get("qualType") == ty] or cands
            if len(cands) > 1 and ty:
                c0 = cands
                cands = [g for g in cands if g.node.get("type", {}).get("qualType") == ty]
                if not cands and self.cfg.get("dynamic"):
                    cands = [g for g in c0 if len(g.params) == len(re.findall(r"[^,()]+", ty[ty.find("(") + 1:ty.rfind(")")]))]
            if len(cands) == 0 and ty and self.cfg.get("dynamic") and q:
                c0 = [g for g in set(self.fns.values()) if g.qname == q]
                nps = len([x for x in ty[ty.find("(") + 1:ty.rfind(")")].split(",") if x.strip()])
                cands = [g for g in c0 if len(g.params) == nps]
            if len(cands) > 1 and not ty and self.cfg.get("dynamic") and getattr(self, "_call_nargs", None) is not None:
                cands = [g for g in cands if len(g.params) == self._call_nargs]
            if self.cfg.get("vehicle") and getattr(self, "_call_args", None) is not None and cands:
                self._imperfect = False
                c0 = cands
                cands = self.score_overloads(cands, self._call_args)
                if self._imperfect and not getattr(self, "_resolving", False):
                    # no instance with exactly the arguments' types: dump the caller's unit for more instances
                    self._resolving = True
                    try:
                        more = self.resolve_fn(did, self.qual.get(did) or qname, force_hint=True)
                    finally:
                        self._resolving = False
                    if more:
                        c1 = [g for g in set(self.fns.values()) if g.qname == q and not g.node.get("_pattern")]
                        if ty:
                            c1 = [g for g in c1 if g.node.get("type", {}).get("qualType") == ty] or c1
                        cands = self.score_overloads(c1, self._call_args)
            if len(cands) == 1:
                f = cands[0]
                self.fns[did] = f
        if f is None and self.cfg.get("vehicle"):
            mg = (self.idx.get(did) or {}).get("mangledName")
            if mg and mg in self.fn_by_mangled:
                f = self.fns[did] = self.fn_by_mangled[mg]
            elif not getattr(self, "_resolving", False):
                self._resolving = True
                try:
                    again = self.resolve_fn(did, self.qual.get(did) or qname)
                finally:
                    self._resolving = False
                if again:
                    return self.fn_of(did, qname, ftype)
        if f is None:
            n = self.idx.get(did)
            raise Reject("no body for function %s (%s, %s)" % (self.qual.get(did, did), qname, ftype))
        return f

    # -- (vehicle configuration) definitions in further units, found on demand
    def sym_index(self):
        """The reference build's objects (`build/reference/obj`): every defined symbol, mangled and demangled (base
        name: without the parameter list), -> the units that define it, text and data apart. Cached."""
        if getattr(self, "_symidx", None) is not None:
            return self._symidx
        path = os.path.join(self.U.cache, "vehicle_symbols.json")
        if not os.path.exists(path):
            objdir = os.path.join(str(self.U.b.OUT), "obj")
            by_obj = {r.replace("/", "__") + ".o": r for r, _ in self.U.units}
            files = [os.path.join(objdir, o) for o in sorted(by_obj) if os.path.exists(os.path.join(objdir, o))]
            rows = []
            for i in range(0, len(files), 200):
                out = subprocess.run(["nm", "-A", "-U"] + files[i:i + 200], capture_output=True, text=True).stdout
                for ln in out.split("\n"):
                    m = re.match(r"^(.*?):\s+[0-9a-f]+\s+([A-Za-z])\s+(\S+)$", ln)
                    if m:
                        rows.append((by_obj[os.path.basename(m.group(1))], m.group(2), m.group(3)))
            dem = subprocess.run(["c++filt"], input="\n".join(r[2] for r in rows), capture_output=True,
                                 text=True).stdout.split("\n")
            idx = {"fn": {}, "data": {}}
            for (u, k, sym), d in zip(rows, dem):
                kind = "fn" if k in "Tt" else "data" if k in "DdSsBb" else None
                if kind is None:
                    continue
                b = base_name(d.strip())
                for key in (sym, b, strip_targs(b)):
                    lst = idx[kind].setdefault(key, [])
                    if u not in lst:
                        lst.append(u)
            with open(path + ".tmp", "w") as fh:
                json.dump(idx, fh)
            os.replace(path + ".tmp", path)
        with open(path) as fh:
            self._symidx = json.load(fh)
        return self._symidx

    def add_dump(self, unit, flt):
        """(vehicle configuration) index one more AST dump (unit, filter)."""
        if (unit, flt) in self.dumped:
            return False
        self.dumped.add((unit, flt))
        d = self.ndumps
        self.ndumps += 1
        before = set(self.fns)
        self._dump_unit = unit
        for o in self.U.ast(unit, flt):
            prefix_ids(o, "d%d:" % d)
            self.index(o, None, [])
        new = [i for i in self.fns if i not in before]
        lone = [self.fns[i] for i in new if (self.fns[i].node.get("mangledName") or "").startswith("__Z")]
        lone = list({id(f): f for f in lone}.values())
        if lone:
            out = subprocess.run(["c++filt"], input="\n".join(f.node["mangledName"] for f in lone), capture_output=True,
                                 text=True).stdout.split("\n")
            for f, dm in zip(lone, out):
                b = base_name(dm.strip())
                # a scope the filter cut off (`Mode::AutoYaw::f` dumped as `AutoYaw::f`): the demangled name
                if "::" in b and len(split_scope(b)) > len(split_scope(f.qname)) and \
                        strip_targs(b).endswith("::" + strip_targs(f.qname)):
                    if "<" not in b or "<" in f.qname:
                        f.qname = b
                    else:
                        f.qname = "::".join(split_scope(strip_targs(b))[:-len(split_scope(f.qname))] + [f.qname])
        for i in new:
            g = self.fns[i]
            self.fns[i] = self._canon.setdefault((g.qname, g.node.get("type", {}).get("qualType"), g.node.get("mangledName")), g)
            mg = g.node.get("mangledName")
            if mg:
                self.fn_by_mangled.setdefault(mg, self.fns[i])
        self.vehicle_log.append("dump %s %s" % (unit, flt))
        return True

    def resolve_fn(self, did, q, force_hint=False):
        """(vehicle configuration) a function without a body in the dumps so far: dump its unit(s) (the defining
        object's unit from the symbol index, else the caller's unit, where an inline or template function used by
        the caller has its body) with the class's name (a member) or the function's name as the filter."""
        if not self.cfg.get("vehicle") or not q:
            return False
        node = self.idx.get(did) or {}
        mg = node.get("mangledName")
        comps = split_scope(q)
        strip = [c if c.startswith("operator") else re.sub(r"<.*>$", "", c) for c in comps]
        is_member = node.get("kind") in ("CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl", "CXXDestructorDecl") or \
            (not node and len(comps) >= 2 and strip[-2][:1].isupper() and strip[-2] not in ("AP", "AP_HAL", "std"))
        if node.get("kind") == "FunctionDecl":
            is_member = False
        flt = strip[-2] if is_member and len(strip) >= 2 else "::".join(strip)
        si = self.sym_index()["fn"]
        units = []
        for key in ([mg] if mg else []) + [q, "::".join(strip)]:
            for u in si.get(key, []):
                if u not in units:
                    units.append(u)
        if not units and "::" not in q:
            # a namespace's function named without it (`AP::scheduler()` called as `scheduler()`)
            if getattr(self, "_lastcomp", None) is None:
                self._lastcomp = {}
                for key in si:
                    if not key.startswith("__Z") and key.count("::") == 1 and "<" not in key and "(" not in key:
                        self._lastcomp.setdefault(key.split("::")[1], []).append(key)
            for key in self._lastcomp.get(q, []):
                for u in si.get(key, []):
                    if u not in units:
                        units.append(u)
        hint = getattr(self, "_cur_unit", None)
        if force_hint:
            units = [hint] if hint else []
        if hint and hint not in units:
            units.append(hint)
        added = False
        for u in units[:4]:
            if self.add_dump(u, flt):
                added = True
                if self.find_body(did, q) is not None:
                    break
        return added

    def ret_rec(self, f):
        """(vehicle configuration) the record type f returns by value, or None."""
        if not hasattr(f, "_ret_rec"):
            try:
                rt = FnTranslator(self, f).ret_type()
            except Reject:
                rt = None
            f._ret_rec = rt if rt is not None and rt.kind == "rec" else None
        return f._ret_rec

    def is_bridge(self, q):
        """(vehicle configuration) a function of the estimator (a member of a class matched by `bridge_classes`, or
        one of `bridge_functions`): reached through the bridge."""
        if self.bridge_re is None or not q:
            return False
        if q in self.cfg.get("bridge_functions", []):
            return True
        comps = split_scope(q)
        if len(comps) < 2:
            return False
        cls = "::".join(c if c.startswith("operator") else re.sub(r"<.*>$", "", c) for c in comps[:-1])
        return bool(self.bridge_re.fullmatch(cls))

    def is_bridge_class(self, rec):
        return self.bridge_re is not None and bool(self.bridge_re.fullmatch(re.sub(r"<.*>$", "", norm_rec(rec or ""))))

    def class_units(self, cls):
        """(vehicle configuration) the units whose objects define members of class cls (template arguments removed)."""
        if getattr(self, "_clsu", None) is None:
            self._clsu = {}
            for key, us in self.sym_index()["fn"].items():
                if "::" in key and not key.startswith("__Z") and "<" not in key:
                    c = "::".join(split_scope(key)[:-1])
                    lst = self._clsu.setdefault(c, [])
                    for u in us:
                        if u not in lst:
                            lst.append(u)
        return self._clsu.get(strip_targs(cls), [])

    def ensure_class(self, cls):
        """(vehicle configuration) the declarations of cls's members: a dump of cls in a unit that defines its members
        (else the current unit)."""
        if cls in self._ensured or "(" in cls:
            return
        self._ensured.add(cls)
        us = self.class_units(cls)
        hint = getattr(self, "_cur_unit", None)
        u = us[0] if us else hint
        if u:
            self.add_dump(u, re.sub(r"<.*>$", "", split_scope(cls)[-1]))

    def bases(self, cls):
        """the base classes of cls by clang's layout (most derived first: cls, its base, ...)."""
        out = [norm_rec(cls)]
        seen = set(out)
        while True:
            try:
                rec = self.rec_layout(out[-1])
            except Reject:
                break
            bs = [f["type"] for f in rec["fields"] if f["base"]]
            if not bs or norm_rec(bs[0]) in seen:
                break
            out.append(norm_rec(bs[0]))
            seen.add(out[-1])
        return out

    def final_overrider(self, cls, name, sig, nargs):
        """(vehicle configuration) the definition a virtual call of `name` with parameter types `sig` calls on an
        object of dynamic class cls: the first class of its base chain that declares it with a body."""
        for c in self.bases(cls):
            self.ensure_class(c)
            ds = [d for d in self.decls.get(c + "::" + name, []) if d.get("kind") in ("CXXMethodDecl", "CXXConversionDecl")]
            if sig:
                ds = [d for d in ds if (lambda t: t[t.index("("):] if "(" in t else t)(d.get("type", {}).get("qualType", "")) == sig] or \
                    [d for d in ds if len([k for k in kids(d) if k.get("kind") == "ParmVarDecl"]) == nargs]
            if not ds:
                continue
            if all(d.get("pure") for d in ds):
                return None
            try:
                return self.use(ds[0]["id"], c + "::" + name, ds[0].get("type", {}).get("qualType"))
            except Reject:
                continue
        return None

    def fn_address(self, f):
        """(vehicle configuration) the address of a function whose address is taken: a fixed address outside the
        memory per function (by its mangled name), the function a target of the dispatcher of its type."""
        mg = f.node.get("mangledName") or f.lean
        if mg not in self.fn_addrs:
            self.fn_addrs[mg] = 0x7f000000 + 16 * len(self.fn_addrs)
        sig = re.sub(r"\s+", " ", f.node.get("type", {}).get("qualType", "")).replace(" noexcept", "")
        d = self.fnptr_sigs.setdefault(sig, {"targets": {}})
        d["targets"][self.fn_addrs[mg]] = f
        return self.fn_addrs[mg]

    def score_overloads(self, cands, args):
        """(vehicle configuration) overloads of one name: those whose parameter count admits the call's arguments,
        then those whose parameter types match the arguments' types best; the non-const one first."""
        n = len(args)
        def admits(g):
            req = len([p for p in g.params if not kids(p)])
            return req <= n <= len(g.params)
        c1 = [g for g in cands if admits(g)] or cands
        if len(c1) <= 1:
            return c1
        def deref(t):
            return self.ty_str(t.name) if t.kind == "ref" else t
        def sig(t):
            return (t.kind, t.bits, t.signed, norm_rec(t.name) if t.kind in ("rec", "ptr", "enum") and t.name else None)
        def score(g):
            sc = 0
            for p, a in zip(g.params, args):
                try:
                    pt, at = deref(self.ty(p.get("type"))), deref(self.ty(a.get("type")))
                except Reject:
                    continue
                if sig(pt) == sig(at):
                    sc += 2
                elif pt.kind == at.kind:
                    sc += 1
            return sc
        best = max(score(g) for g in c1)
        c2 = [g for g in c1 if score(g) == best]
        if best < 2 * min(n, min(len(g.params) for g in c2)) and not getattr(self, "_rescored", False):
            self._imperfect = True      # no exact match: the caller may dump more instances
        c2.sort(key=lambda g: (g.node.get("type", {}).get("qualType", "").endswith(" const"), g.node.get("id")))
        return c2[:1]

    def find_body(self, did, q):
        f = self.fns.get(did)
        if f is not None:
            return f
        mg = (self.idx.get(did) or {}).get("mangledName")
        if mg and mg in self.fn_by_mangled:
            return self.fn_by_mangled[mg]
        if any(g.qname == q for g in self._canon.values()):
            return True
        return None

    def bound_address(self, f):
        """(vehicle configuration, static construction) the address a FUNCTOR_BIND_MEMBER stores for member function f
        (in place of `method_wrapper<T, f>`'s): a fixed address per function; the dispatchers of the functors' pointer
        types call f on the bound object (their first argument)."""
        bm = self.__dict__.setdefault("bound_methods", {})
        for a, g in bm.items():
            if g is f:
                return a
        a = 0x7e000000 + 16 * len(bm)
        bm[a] = f
        return a

    def fn_by_qname(self, q):
        cands = [g for g in set(self.fns.values()) if g.qname == q]
        if len(cands) != 1:
            raise Reject("function %s: %d definitions" % (q, len(cands)))
        return self.use(cands[0].node["id"])

    def ctor_fn(self, recname, cty):
        rec = norm_rec(recname)
        short = re.sub(r"<.*$", "", rec.split("::")[-1])
        if self.cfg.get("static_construction"):
            # (static construction) template arguments with `::` (`ObjectBuffer<GCS_MAVLINK::pending_param_request>`),
            # spacing of nested template arguments, `noexcept`
            short = re.sub(r"<.*$", "", split_scope(rec)[-1])
            nz = lambda x: re.sub(r"\s+", "", re.sub(r"\b(class|struct|enum) ", "", re.sub(r"\s*noexcept(\([^)]*\))?$", "", x or "")))
            cands = [g for g in set(self.fns.values()) if nz(g.qname) == nz(rec + "::" + short) and g.ctor and
                     nz(g.node.get("type", {}).get("qualType")) == nz(cty)]
        else:
            cands = [g for g in set(self.fns.values()) if g.qname == rec + "::" + short and g.ctor and
                     g.node.get("type", {}).get("qualType") == cty]
        if not cands:
            return None
        g = cands[0]
        return self.use(g.node["id"])

    def use(self, did, qname=None, ftype=None):
        f = self.fn_of(did, qname, ftype)
        key = id(f)
        if key not in self.used:
            self.used[key] = f
            q = f.qname
            base = lean_name(q)
            if self.cfg.get("vehicle"):
                targs = [a for a in kids(f.node) if a.get("kind") == "TemplateArgument"]
                if targs and "<" not in split_scope(q)[-1]:
                    # a function template's instance: its arguments in the name (`method_wrapper'Copter_rc_loop`)
                    ta = [(a.get("decl") or {}).get("name") or self.targ_text(a) for a in targs]
                    base = lean_name(q + "<" + ", ".join(ta) + ">")
            nm = base
            k = 1
            while nm in self.names and self.names[nm] is not f:
                k += 1
                nm = "%s'%d" % (base, k)
            self.names[nm] = f
            f.lean = nm
            f.qual = q
            self.order.append(f)
        return f

    def translate_all(self, roots):
        for r in roots:
            ids = [i for i, f in self.fns.items() if f.qname == r]
            if not ids:
                raise Reject("entry function %s not found" % r)
            for i in ids:
                self.use(i)
        out = []
        i = 0
        while True:
            self._translate_from(i, out)
            i = len(self.order)
            if not (self.cfg.get("vehicle") and self.static_fn_closure()):
                break
        if os.environ.get("CPP2LEAN_MEM_SURVEY"):
            with open(os.environ.get("CPP2LEAN_MEM_SURVEY_LIST", os.devnull), "w") as fh:
                fh.write("\n".join("%s\t%s" % (f.qname, FnTranslator(self, f).loc()) for f in self.order) + "\n")
        if getattr(self, "survey_rejects", 0):
            raise Reject("survey: %d functions rejected" % self.survey_rejects)
        return out

    def ir_mod(self, u):
        if u not in self._irmods:
            self._irmods[u] = self.U.ir(u)
        return self._irmods[u]

    def static_loc(self, q):
        """(vehicle configuration) (unit, IR symbol) of the definition of static q."""
        units = list(self.sym_index()["data"].get(q, [])) + list(self.cfg.get("static_units", []))
        for u in units:
            m = self.ir_mod(u)
            if u not in self._irdem:
                syms = [x for x in m.raw if not x.startswith("@.") and not x.startswith('@"')]
                dem = subprocess.run(["c++filt"], input="\n".join("_" + x.lstrip("@") for x in syms), capture_output=True,
                                     text=True).stdout.split("\n")
                self._irdem[u] = {d.strip(): x for x, d in zip(syms, dem)}
                if self.cfg.get("static_construction"):
                    # (static construction) C names (`copter`, `hal`) are not mangled
                    for x in syms:
                        if not x.lstrip("@").startswith("_Z"):
                            self._irdem[u].setdefault(x.lstrip("@"), x)
            x = self._irdem[u].get(q)
            if x and m.get(x) and m.get(x)["defined"]:
                return u, x
        return None

    def static_fn_closure(self):
        """(vehicle configuration) the functions whose addresses the statics' constant data holds (the scheduler's
        task tables: `method_wrapper<T, method>` of each FUNCTOR_BIND): translated and made targets of the
        dispatcher of their type. True if functions were added."""
        added = False
        todo = []
        for q in list(self.static_addr):
            if q in self._scanned or "(...)::" in q:
                continue
            self._scanned.add(q)
            loc = self.static_loc(q)
            if loc:
                todo.append(loc)
        seen = set()
        while todo:
            u, sym = todo.pop()
            if (u, sym) in seen:
                continue
            seen.add((u, sym))
            m = self.ir_mod(u)
            g = m.get(sym)
            if g is None:
                continue
            for off, t, add in g["relocs"]:
                if t in m.raw:
                    if t.startswith("@."):
                        todo.append((u, t))
                    continue
                mg = "_" + t.lstrip("@").strip('"')
                f = self.fn_by_mangled.get(mg)
                if f is None:
                    dm = subprocess.run(["c++filt"], input=mg, capture_output=True, text=True).stdout.strip()
                    b = base_name(dm)
                    comps = split_scope(strip_targs(b))
                    self.add_dump(u, comps[-2] if len(comps) >= 2 else comps[-1])
                    f = self.fn_by_mangled.get(mg)
                if f is None:
                    self.vehicle_log.append("no definition for the function pointer %s in %s" % (mg, u))
                    continue
                if id(f) not in self.used:
                    added = True
                self.use(f.node["id"])
                self.fn_address(f)
        return added

    def _translate_from(self, i, out):
        while i < len(self.order):
            f = self.order[i]
            try:
                out.append(FnTranslator(self, f).translate())
            except Reject as e:
                if self.cfg.get("vehicle"):
                    # (vehicle configuration) a function the back end does not translate yet: a stub that records its
                    # name (`PMem.unreached "rejected ..."`) and gives the type's default; listed in the survey
                    loc = FnTranslator(self, f).loc()
                    self.rejected.append((f.qname, loc, str(e)))
                    print("survey: %s [in %s, %s]" % (e, f.qname, loc), file=sys.stderr)
                    out.append(FnTranslator(self, f).stub(str(e)))
                    i += 1
                    continue
                if not os.environ.get("CPP2LEAN_MEM_SURVEY"):
                    raise Reject("%s [in %s]" % (e, f.qname))
                # survey (environment CPP2LEAN_MEM_SURVEY=1): every function's first rejection, the output not usable
                print("survey: %s [in %s, %s]" % (e, f.qname, FnTranslator(self, f).loc()), file=sys.stderr)
                self.survey_rejects = getattr(self, "survey_rejects", 0) + 1
            i += 1


class LV:
    """An lvalue: a register (Lean variable) or memory at an address (with a bit-field position)."""

    def __init__(self, kind, t, text, bitoff=None, width=None):
        self.kind, self.t, self.text, self.bitoff, self.width = kind, t, text, bitoff, width


class FnTranslator:
    def __init__(self, tr, f):
        self.tr, self.f = tr, f
        self.lines = []
        self.ind = 1
        self.frame = 0
        self.locals = {}       # VarDecl id -> ("reg", lean name, T) | ("mem", offset, T) | ("refreg", lean name, T)
        self.tmp = 0
        self.addr_taken = set()
        self.names = set()

    # -- emission helpers
    def emit(self, s):
        self.lines.append("  " * self.ind + s)

    def fresh(self, base="t"):
        self.tmp += 1
        return "%s'%d" % (base, self.tmp)

    def slot(self, size, align=8):
        a = max(1, min(align, 16))
        self.frame = (self.frame + a - 1) // a * a
        off = self.frame
        self.frame += max(size, 1)
        return off

    def var_name(self, name):
        nm = re.sub(r"[^A-Za-z0-9_]", "_", name or "v")
        if nm in ("fun", "do", "then", "else", "if", "let", "mut", "for", "in", "return", "break", "continue", "match", "with",
                  "end", "where", "def", "set", "get", "open", "namespace", "at", "from", "have", "show", "by", "type", "ptr", "info"):
            nm = nm + "'"
        elif self.tr.cfg.get("dynamic") and nm in ("instance", "variable", "theorem", "section", "example", "structure", "class",
                                                   "inductive", "axiom", "deriving", "extends", "local", "private", "protected",
                                                   "partial", "unsafe", "mutual", "macro", "syntax", "attribute", "universe",
                                                   "notation", "abbrev", "opaque", "where", "fun", "λ", "Type", "Prop", "Sort",
                                                   "errors"):
            nm = nm + "'"
        base, k = nm, 1
        while nm in self.names:
            k += 1
            nm = "%s'%d" % (base, k)
        self.names.add(nm)
        return nm

    # -- analysis: which locals need memory
    def scan_addr(self, n, parent=None):
        k = n.get("kind")
        if k == "DeclRefExpr":
            rd = n.get("referencedDecl", {})
            if rd.get("kind") in ("VarDecl", "ParmVarDecl"):
                pk = parent.get("kind") if parent else None
                ok = (pk == "ImplicitCastExpr" and parent.get("castKind") == "LValueToRValue") or \
                     (pk in ("BinaryOperator", "CompoundAssignOperator") and parent.get("opcode") in ("=", "+=", "-=", "|=", "&=", "*=", "/=", "<<=", ">>=", "^=", "%=") and kids(parent)[0] is n) or \
                     (pk == "UnaryOperator" and parent.get("opcode") in ("++", "--"))
                if not ok:
                    self.addr_taken.add(rd["id"])
        for c in kids(n):
            self.scan_addr(c, n)

    # -- main
    def translate(self):
        f, tr = self.f, self.tr
        node = f.node
        if f.body is None:
            raise Reject("no body: " + f.qual)
        if tr.cfg.get("vehicle"):
            tr._cur_unit = node.get("_unit")
        if tr.cfg.get("goto_rewrite") and any(m.get("kind") == "GotoStmt" for m in _walk(f.body)):
            # (Phase 5c, configuration `goto_rewrite`) a body with forward `goto`s: cpp2lean's GotoRewriter (README.md
            # "Phase 2b", "Gotos") on clang's AST first, so that the back end sees structured code with the same behavior
            import cpp2lean as C
            try:
                C.GotoRewriter(None, node).run()
            except C.GotoReject as e:
                raise Reject("goto: %s" % e.construct)
            f.body = next(c for c in kids(node) if c.get("kind") == "CompoundStmt")
        self.scan_addr(f.body)
        ftype = node["type"]["qualType"]
        ret = self.ret_type()
        params = []
        is_method = node["kind"] in ("CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl") and not f.is_static
        self.is_method = is_method
        if is_method:
            params.append("(this : UInt64)")
            self.names.add("this")
        if ret.kind == "rec" and tr.cfg.get("vehicle"):
            # (vehicle configuration) a record returned by value: the caller passes the address of the result
            params.append("(sret : UInt64)")
            self.names.add("sret")
        prologue = []
        for p in f.params:
            pt = tr.ty(p["type"])
            nm = self.var_name(p.get("name") or "arg")
            if pt.kind == "rec":
                # by-value struct: the caller passes the address of its copy
                params.append("(%s : UInt64)" % nm)
                self.locals[p["id"]] = ("memaddr", nm, pt)
                continue
            if pt.kind == "ref":
                params.append("(%s : UInt64)" % nm)
                self.locals[p["id"]] = ("refreg", nm, tr.ty_str(pt.name))
                continue
            params.append("(%s : %s)" % (nm, pt.lean))
            if p["id"] in self.addr_taken:
                off = self.slot(tr.size_of(pt), tr.size_of(pt))
                self.locals[p["id"]] = ("mem", off, pt)
                prologue.append("PMem.st%s (fp + %d) %s" % (pt.suffix(), off, nm))
            else:
                self.locals[p["id"]] = ("reg", nm, pt)
                prologue.append("let mut %s := %s" % (nm, nm))
        if tr.cfg.get("varargs") and node.get("variadic"):
            # (Phase 5c, configuration `varargs`) C varargs as on the target (arm64 Apple: `va_list` is `char *`, each
            # variadic argument in its own 8-byte slot after the default promotions): the caller writes the variadic
            # arguments into a block of 8-byte slots and passes its address, the hidden last parameter `va'`
            params.append("(va' : UInt64)")
            self.names.add("va'")
        self.ret = ret
        body_lines_start = len(self.lines)
        for s in prologue:
            self.emit(s)
        if f.ctor:
            rec = self.tr.qual.get(node.get("previousDecl"), f.qname).rsplit("::", 1)[0]
            for ci in kids(node):
                if ci.get("kind") != "CXXCtorInitializer":
                    continue
                if "anyInit" not in ci and "baseInit" in ci and self.tr.cfg.get("dynamic"):
                    # (GCS configuration) a base class's constructor (single inheritance: the base at offset 0)
                    ini = kids(ci)[0]
                    bt = self.tr.ty(ci["baseInit"])
                    if ini.get("kind") == "CXXConstructExpr":
                        if self.tr.cfg.get("static_construction") and self.tr.is_bridge_class(bt.name):
                            continue
                        g = self.tr.ctor_fn(bt.name, ini.get("ctorType", {}).get("qualType", ""))
                        if g is None and not kids(ini) and self.tr.cfg.get("static_construction"):
                            self.construct_default("this", bt.name)
                            continue
                        if g is None and not kids(ini):
                            continue
                        if g is None:
                            raise Reject("base constructor %s in %s" % (bt.name, f.qname))
                        avs = self.call_args(g, kids(ini))
                        self.emit("%s this%s" % (g.lean, "".join(" " + par(a) for a in avs)))
                        continue
                    raise Reject("base initializer in %s" % f.qname)
                if "anyInit" not in ci and "baseInit" not in ci and self.tr.cfg.get("dynamic") and kids(ci) and \
                        kids(ci)[0].get("kind") == "CXXConstructExpr":
                    # (GCS configuration) a delegating constructor (`AC_PID(const Defaults &d) : AC_PID(d.p, ...)`)
                    ini = kids(ci)[0]
                    g = self.tr.ctor_fn(rec, ini.get("ctorType", {}).get("qualType", ""))
                    if g is None:
                        raise Reject("delegated constructor of %s" % rec)
                    avs = self.call_args(g, kids(ini))
                    self.emit("%s this%s" % (g.lean, "".join(" " + par(a) for a in avs)))
                    continue
                if "anyInit" not in ci:
                    raise Reject("base initializer in %s" % f.qname)
                if "%s::%s" % (rec, ci["anyInit"]["name"]) in self.tr.cfg.get("skip_members", []):
                    continue        # (GCS configuration) a member left out of the model (AP_Mission's callbacks into ModeAuto)
                fl = self.tr.field(rec, ci["anyInit"]["name"])
                ft = self.tr.ty_str(fl["type"])
                ini = kids(ci)[0]
                if ini.get("kind") == "CXXDefaultInitExpr" and self.tr.cfg.get("dynamic"):
                    # (GCS configuration) the member's default member initializer (clang's rewritten copy, else the
                    # field's own)
                    fd = self.tr.idx.get(ci["anyInit"]["id"]) or {}
                    fk = [x for x in kids(ini) if "Comment" not in x.get("kind", "")] or \
                        [x for x in kids(fd) if "Comment" not in x.get("kind", "")]
                    if not fk:
                        raise Reject("default member initializer of %s not in the dump" % ci["anyInit"]["name"])
                    ini = fk[0]
                if ft.kind in ("rec", "arr") and self.tr.cfg.get("static_construction") and \
                        self.tr.is_bridge_class(ft.name if ft.kind == "rec" else (ft.elem.name if ft.elem.kind == "rec" else "")):
                    # (static construction) a member object of the estimator (AP_AHRS, AP_InertialSensor, AP_Baro,
                    # Compass, AP_GPS, ...): constructed by the estimator World (`World.init`), not here
                    self.emit("-- %s: constructed by the estimator World" % ci["anyInit"]["name"])
                    continue
                if ft.kind in ("rec", "arr") and ini.get("kind") == "CXXConstructExpr" and not kids(ini) and \
                        self.tr.cfg.get("static_construction"):
                    # (static construction) a member object's default constructor, translated (user-provided) or
                    # implicit (its bases' and members' construction, its default member initializers)
                    self.init_mem("(this + %d)" % fl["off"], ft, ini)
                    continue
                if ft.kind in ("rec", "arr") and ini.get("kind") == "CXXConstructExpr" and not kids(ini):
                    # a member object's default constructor: the members' own constructors (their
                    # setup_object_defaults) are the harness's static construction, not this constructor's
                    if ft.kind == "rec" and self.tr.cfg.get("dynamic"):
                        self.default_member_inits("(this + %d)" % fl["off"], ft.name)
                    continue
                if ft.kind == "ref" and self.tr.cfg.get("dynamic"):
                    # (GCS configuration) a reference member: the address of the object it is bound to
                    self.emit("PMem.stU64 (this + %d) %s" % (fl["off"], par(self.addr_of(ini))))
                    continue
                if fl["bitoff"] is not None:
                    v = self.rv(ini, ft)
                    self.emit("PMem.stBits this %d %d %s" % (fl["bitoff"], fl["width"], par(self.to_u64(v, ft))))
                    continue
                self.init_mem("(this + %d)" % fl["off"], ft, ini)
        self.stmt(f.body)
        if not always_returns(f.body):
            self.emit("return ()" if ret.kind == "void" else "return default  -- (no return in C: not reached)")
        body = self.lines
        rt = "UInt64" if ret.kind in ("ref",) else "Unit" if ret.kind == "rec" and tr.cfg.get("vehicle") else ret.lean
        doc = "/-- C++ `%s`, `%s`. -/" % (f.qual + " : " + ftype, self.loc())
        sig_params = " ".join(params)
        name = f.lean
        out = [doc]
        if self.frame:
            out.append("partial def %s.body (fp : UInt64) %s : PMem.M %s := do" % (name, sig_params, rt))
            out += body
            out.append("")
            out.append("partial def %s %s : PMem.M %s := do" % (name, sig_params, rt))
            out.append("  let fp ← PMem.enter %d" % self.frame)
            args = " ".join(re.match(r"\((\S+) :", p).group(1) for p in params)
            out.append("  let r ← %s.body fp %s" % (name, args))
            out.append("  PMem.leave fp")
            out.append("  return r")
        else:
            out.append("partial def %s %s : PMem.M %s := do" % (name, sig_params, rt))
            out += body
        return "\n".join(out)

    def stub(self, reason):
        """(vehicle configuration) a rejected function: its signature as callers call it, a body that records the
        rejection and returns the result type's default."""
        f, tr = self.f, self.tr
        node = f.node
        params = []
        if node["kind"] in ("CXXMethodDecl", "CXXConstructorDecl", "CXXConversionDecl") and not f.is_static:
            params.append("(this : UInt64)")
            self.names.add("this")
        ret = self.ret_type()
        if ret.kind == "rec":
            params.append("(sret : UInt64)")
            self.names.add("sret")
        for p in f.params:
            pt = tr.ty(p["type"])
            nm = self.var_name(p.get("name") or "arg")
            params.append("(%s : %s)" % (nm, "UInt64" if pt.kind in ("rec", "ref") else pt.lean))
        if tr.cfg.get("varargs") and node.get("variadic"):
            params.append("(va' : UInt64)")     # (Phase 5c) the variadic arguments' block, as translate()
        try:
            rt = "UInt64" if ret.kind == "ref" else "Unit" if ret.kind in ("rec", "void", "fn") else ret.lean
        except Reject:
            rt = "Unit"
        doc = "/-- C++ `%s : %s`, `%s`. NOT TRANSLATED (the back end rejects: %s): a stub. -/" % (
            f.qual, node["type"]["qualType"], self.loc(), reason.replace("-/", "- /").replace("`", "'"))
        body = ["  PMem.unreached %s" % json.dumps("rejected " + f.qual)]
        body.append("  return ()" if rt == "Unit" else "  return default")
        return "\n".join([doc, "partial def %s %s : PMem.M %s := do" % (f.lean, " ".join(params), rt)] + body)

    def default_of(self, t):
        """(vehicle configuration) the default result of a boundary call: zero, or a zeroed temporary for a record."""
        if t.kind == "void":
            return "()"
        if t.kind in ("rec", "arr"):
            off = self.slot(self.tr.size_of(t))
            self.emit("discard <| PMem.memset (fp + %d) 0 %d" % (off, self.tr.size_of(t)))
            return "(fp + %d)" % off
        return "(default : %s)" % ("UInt64" if t.kind in ("ref", "ptr") else t.lean)

    def site(self, n):
        ln = (n.get("range", {}).get("begin", {}) or {}).get("line") or (n.get("loc", {}) or {}).get("line")
        return "%s (%s%s)" % (self.f.qual, self.loc().split(":")[0], ":%s" % ln if ln else "")

    def bridge_call(self, n, q, did, dref, t, member=None, args=None):
        """(vehicle configuration) a call of an estimator function. Without `bridge_module`: recorded (`PMem.bridge`),
        the result the type's default. With `bridge_module` (README.md "Phase 5: the estimator bridge"): a call of the
        function's adapter in that module (`bridge_adapter_call`), which marshals the arguments between the memory and
        the World and calls the World's translation."""
        decl = self.tr.idx.get(did) or {}
        sig = (decl.get("type") or {}).get("qualType") or (dref.get("type") or {}).get("qualType") or "?"
        e = self.tr.bridge_calls.setdefault(q, {"sig": sig, "sites": []})
        if e["sig"] == "?" and sig != "?":
            e["sig"] = sig
        e["sites"].append(self.site(n))
        if self.tr.cfg.get("bridge_module") and args is not None:
            r = self.bridge_adapter_call(n, q, did, dref, t, member, args, decl, sig)
            if r is not None:
                return r
        self.emit("PMem.bridge %s" % json.dumps(q))
        return self.default_of(t)

    def bridge_describe(self, t, depth=0):
        """(bridge) a type as the adapter generator needs it: scalars by their Lean type and size; records by clang's
        layout (size and the scalar leaves: path, byte offset, bit offset and width of a bit-field, type)."""
        tr = self.tr
        if t.kind == "rec":
            rec = tr.rec_layout(t.name)
            leaves = []

            def walk(node, path):
                for f in node["fields"]:
                    if f["base"]:
                        walk(f, path)
                        continue
                    ft = f["type"]
                    nm = path + ([f["name"]] if f["name"] else [])
                    if f["fields"]:
                        walk(f, nm)
                        continue
                    leaves.append({"path": ".".join(nm), "off": f["off"], "bitoff": f["bitoff"], "width": f["width"], "type": ft})
            walk(rec, [])
            return {"kind": "rec", "name": norm_rec(t.name), "size": rec["size"], "leaves": leaves}
        if t.kind == "arr":
            return {"kind": "arr", "n": t.n, "elem": self.bridge_describe(t.elem, depth + 1)}
        return {"kind": t.kind, "lean": t.lean, "size": tr.size_of(t) if t.kind != "void" else 0, "signed": t.signed,
                "name": t.name}

    def bridge_adapter_call(self, n, q, did, dref, t, member, args, decl, sig):
        """(bridge) `VehicleBridge.<function>'<arity> [this] [sret] args... [vehicle inputs]`: the object's address for a
        member function; for a record result (by value, or a `const T &` of a record that is not an estimator object) the
        address of a temporary of the caller's frame, which the adapter fills and which is the call's value; the
        arguments in the translator's convention (scalars as values, references and records as addresses); the
        configured vehicle inputs (`bridge_inputs`: a translated vehicle function, passed unevaluated as an action, which
        the adapter runs before the World call). The signature of each adapter is written to `<ns>.bridge.json` for the
        generator (ardupilot/vehicle/gen_bridge.py). On a construct it cannot pass, nothing is emitted (None)."""
        tr = self.tr
        import types as _types
        params = [k for k in kids(decl) if k.get("kind") == "ParmVarDecl"]
        if sig == "?" or (not params and args):
            # the declaration is in no dump yet: from a dump of its class (or of the accessor), chosen by the number
            # of arguments of the call (default arguments are in the call as CXXDefaultArgExpr)
            comps = split_scope(q)
            try:
                if len(comps) >= 2:
                    tr.ensure_class("::".join(comps[:-1]))
                elif tr.sym_index()["fn"].get("AP::" + q):
                    tr.add_dump(tr.sym_index()["fn"]["AP::" + q][0], "AP::" + q)
            except Reject:
                pass
            ds = [d for d in (tr.decls.get(q, []) or tr.decls.get("AP::" + q, [])) if d.get("kind") != "CXXRecordDecl" and
                  len([k for k in kids(d) if k.get("kind") == "ParmVarDecl"]) == len(args)]
            if not ds:
                if os.environ.get("CPP2LEAN_BRIDGE_DEBUG"):
                    sys.stderr.write("bridge %s: no declaration with %d parameters\n" % (q, len(args)))
                return None
            decl = ds[0]
            sig = (decl.get("type") or {}).get("qualType") or "?"
            params = [k for k in kids(decl) if k.get("kind") == "ParmVarDecl"]
        sig0 = re.sub(r"\s+(const|volatile|&|&&)$", "", sig.strip())
        rtxt, ptxt = parse_fn_type(sig0) if sig0 != "?" else (None, None)
        if rtxt is None or len(ptxt) != len(params):
            if os.environ.get("CPP2LEAN_BRIDGE_DEBUG"):
                sys.stderr.write("bridge %s: signature %r, %d parameters in the declaration\n" % (q, sig, len(params)))
            return None
        saved = (list(self.lines), self.frame, self.tmp, dict(self.locals), set(self.names))
        try:
            pdesc = []
            for p in params:
                pt = tr.ty(p["type"])
                if pt.kind == "ref":
                    pdesc.append({"pass": "ref", "type": self.bridge_describe(tr.ty_str(pt.name)), "const": p["type"]["qualType"].startswith("const ")})
                elif pt.kind == "rec":
                    pdesc.append({"pass": "rec", "type": self.bridge_describe(pt)})
                else:
                    pdesc.append({"pass": "value", "type": self.bridge_describe(pt)})
            fake = _types.SimpleNamespace(params=params, qual=q)
            avs = self.call_args(fake, args)
            is_method = (decl.get("kind") in ("CXXMethodDecl", "CXXConversionDecl") or member is not None) and \
                decl.get("storageClass") != "static" and "::" in q
            pre = []
            if is_method:
                if member is None:
                    pre = ["this"]
                else:
                    base = kids(member)[0]
                    pre = [self.rv(base) if member.get("isArrow") else self.addr_of(base)]
            rt = rtxt.strip()
            rref = rt.endswith("&")
            rbase = strip_cv(rt.rstrip("&").strip())
            if t.kind == "void":
                rdesc = {"pass": "void"}
            elif t.kind == "rec" and rref and tr.is_bridge_class(rbase):
                rdesc = {"pass": "object", "type": {"kind": "rec", "name": norm_rec(rbase)}}
            elif t.kind in ("rec", "arr"):
                rdesc = {"pass": "sret", "type": self.bridge_describe(t), "ref": rref}
                off = self.slot(tr.size_of(t))
                pre = pre + ["(fp + %d)" % off]
            elif rref:
                return None
            elif t.kind == "ptr" and q in tr.cfg.get("bridge_pointer_results", []):
                # (Phase 5c) `const T *f() const` of an estimator class, a pointer to a record of the World
                # (`AP_AHRS::get_secondary_estimates`): the adapter copies the record into a temporary of the caller's
                # frame (clang's layout) and returns its address, or null for the World's null pointer
                pt = tr.ty_str(t.name)
                if pt.kind != "rec":
                    raise Reject("bridge pointer result of %s: not a record" % q)
                rdesc = {"pass": "copy", "type": self.bridge_describe(pt)}
                off = self.slot(tr.size_of(pt))
                pre = pre + ["(fp + %d)" % off]
            else:
                rdesc = {"pass": "value", "type": self.bridge_describe(t)}
            inputs = []
            for nm, fq, obj in tr.cfg.get("bridge_inputs", {}).get(q, []):
                if not any(g.qname == fq for g in set(tr.fns.values())):
                    tr.ensure_class(fq.rsplit("::", 1)[0])
                f = tr.fn_by_qname(fq)
                # `this`: the call's own object (a member function of the estimator class that the World's translation
                # leaves out and the memory translates, run by the adapter: `pre_` inputs, Phase 5b)
                # `{k}` (Phase 5c): the call's k-th argument (an object passed by reference: `send_ekf_status_report(*this)`'s
                # link, whose GCS_MAVLINK::get_chan is a boundary input of the World's translation)
                arg = pre[0] if obj == "this" else (avs[int(obj[1:-1])] if re.fullmatch(r"\{\d+\}", obj) else self.static_ref(obj))
                inputs.append((nm, fq, "(%s %s)" % (f.lean, par(arg) if re.fullmatch(r"\{\d+\}", obj) else arg)))
            arity = len(params)
            name = "VehicleBridge.%s'%d" % (lean_name(q), arity)
            key = (q, arity)
            ent = tr.bridge_adapters.get(key)
            desc = {"q": q, "adapter": name, "sig": sig, "method": is_method, "params": pdesc, "ret": rdesc,
                    "inputs": [[nm, fq] for nm, fq, _ in inputs]}
            if ent is not None and (ent["method"] != is_method or json.dumps(ent["ret"]) != json.dumps(rdesc)):
                raise Reject("bridge adapter %s: call sites with different conventions" % name)
            if ent is not None and json.dumps(ent["params"]) != json.dumps(pdesc):
                name = name + "'" + "%08x" % (zlib_crc(json.dumps(pdesc)))
                desc["adapter"] = name
                key = (q, arity, name)
            tr.bridge_adapters.setdefault(key, desc)
            text = name + "".join(" " + par(a) for a in pre + avs + [i for _, _, i in inputs])
            # (Phase 5b, `world_outputs`) the World's output events of the call (AP_Param saves, GCS sends, the mission's
            # home record), replayed on the memory right after it: `worldOutputs'drain`
            drain = "worldOutputs'drain" if tr.cfg.get("world_outputs") else None
            if rdesc["pass"] == "void":
                self.emit(text)
                if drain:
                    self.emit(drain)
                return "()"
            if rdesc["pass"] == "sret":
                self.emit(text)
                if drain:
                    self.emit(drain)
                return pre[-1]
            v = self.bind(text)
            if drain:
                self.emit(drain)
            return v
        except Reject as e:
            if os.environ.get("CPP2LEAN_BRIDGE_DEBUG"):
                sys.stderr.write("bridge %s: %s\n" % (q, e))
            self.lines, self.frame, self.tmp, self.locals, self.names = saved
            return None

    def construct_default(self, addr, recname, depth=0):
        """(static construction) the implicit default constructor of class recname at addr: its bases' default
        constructors, then each member's (a default member initializer, a member object's default constructor, an
        array of class objects element by element); scalars without an initializer stay as they are (static storage
        is zero). An estimator class is constructed by the World."""
        tr = self.tr
        rn = norm_rec(recname)
        if tr.is_bridge_class(rn):
            self.emit("-- %s: constructed by the estimator World" % rn)
            return
        if depth > 16:
            raise Reject("construction of %s too deep" % rn)
        try:
            tr.ensure_class(rn)
        except Reject:
            pass
        short = re.sub(r"<.*$", "", rn.split("::")[-1])
        cands = [g for g in set(tr.fns.values()) if g.qname == rn + "::" + short and g.ctor and
                 not [p for p in g.params if not kids(p)]]
        if cands:
            g = tr.use(sorted(cands, key=lambda g: len(g.params))[0].node["id"])
            avs = self.call_args(g, [])
            self.emit("%s %s%s" % (g.lean, addr, "".join(" " + par(a) for a in avs)))
            return
        if tr.cfg.get("ctor_from_class"):
            # (Phase 5c) a user-provided default constructor defined in the class (inline, never called by name, so not
            # among the functions found so far: `CANIface_Params() { AP_Param::setup_object_defaults(this, var_info); }`,
            # AP_CANManager.h:106, 138, the elements of AP_CANManager's `_interfaces[]`/`_drv_param[]`): from the class's
            # declaration
            cn = tr.recnodes.get(rn)
            uc = [c for c in kids(cn or {}) if c.get("kind") == "CXXConstructorDecl" and not c.get("isImplicit") and
                  not [p for p in kids(c) if p.get("kind") == "ParmVarDecl"] and
                  any(x.get("kind") == "CompoundStmt" for x in kids(c))]
            if uc:
                g = tr.use(uc[0]["id"])
                avs = self.call_args(g, [])
                self.emit("%s %s%s" % (g.lean, addr, "".join(" " + par(a) for a in avs)))
                return
        try:
            rec = tr.rec_layout(rn)
        except Reject:
            return
        node = tr.recnodes.get(rn)
        if node is None:
            # an unnamed record (`struct { ...; const uint16_t interval_ms = 10000; } _timesync_request;`): by its place
            m = re.search(r"\((?:unnamed|anonymous)(?: struct| union)? at (.*):(\d+):(\d+)\)$", rn)
            if m:
                node = tr.recnodes.get("%s:%s:%s" % (os.path.basename(m.group(1)), m.group(2), m.group(3)))
                if node is None:
                    lc = tr.recnodes.get(("lc", int(m.group(2)), int(m.group(3))), [])
                    if len(lc) == 1:
                        node = lc[0]
        node = node or {}
        inits = {}
        for fd in kids(node):
            if fd.get("kind") == "FieldDecl" and fd.get("name"):
                ini = [x for x in kids(fd) if "Comment" not in x.get("kind", "")]
                if ini:
                    inits[fd["name"]] = ini[0]
        for f in rec["fields"]:
            if "vtable" in (f.get("type") or "") or "vtable" in (f.get("name") or ""):
                continue
            try:
                ft = tr.ty_str(f["type"])
            except Reject:
                continue
            a = "(%s + %d)" % (addr, f["off"]) if f["off"] else addr
            if f["base"]:
                self.construct_default(a, f["type"], depth + 1)
                continue
            nm = f.get("name")
            if nm in inits:
                # the default member initializer: `this` in it is the object being constructed
                saved = getattr(self, "_this", None)
                self._this = addr if addr != "this" else saved
                try:
                    if f["bitoff"] is not None:
                        v = self.rv(inits[nm], ft)
                        self.emit("PMem.stBits %s %d %d %s" % (addr, f["bitoff"], f["width"], par(self.to_u64(v, ft))))
                    else:
                        self.init_mem(a, ft, inits[nm])
                finally:
                    self._this = saved
            elif ft.kind == "rec":
                self.construct_default(a, ft.name, depth + 1)
            elif ft.kind == "arr" and ft.elem.kind == "rec":
                es = tr.size_of(ft.elem)
                for i in range(ft.n):
                    self.construct_default("(%s + %d)" % (addr, f["off"] + i * es), ft.elem.name, depth + 1)

    def default_member_inits(self, addr, recname, depth=0):
        """(GCS configuration) the implicit default constructor of a member object: its fields' default member
        initializers (`struct { uint32_t last_sent_ms; const uint16_t interval_ms = 10000; } _timesync_request;`),
        recursively into member objects without one."""
        tr = self.tr
        rn = norm_rec(recname)
        node = tr.recnodes.get(rn)
        if node is None:
            m = re.search(r"\((?:unnamed|anonymous)(?: struct| union)? at (.*):(\d+):(\d+)\)$", rn)
            if m:
                node = tr.recnodes.get("%s:%s:%s" % (os.path.basename(m.group(1)), m.group(2), m.group(3)))
                if node is None:
                    lc = tr.recnodes.get(("lc", int(m.group(2)), int(m.group(3))), [])
                    if len(lc) == 1:
                        node = lc[0]       # the place alone (the dump's file tracking can be stale)
        if node is None or depth > 6:
            return
        if any(c.get("kind") == "CXXConstructorDecl" and not c.get("isImplicit") for c in kids(node)):
            return      # a user-provided constructor: not modelled here (its own translation)
        for fd in kids(node):
            if fd.get("kind") != "FieldDecl" or not fd.get("name"):
                continue
            try:
                fl = tr.field(rn, fd["name"])
            except Reject:
                continue
            ft = tr.ty_str(fl["type"])
            init = [x for x in kids(fd) if "Comment" not in x.get("kind", "")]
            if init:
                if fl["bitoff"] is not None:
                    v = self.rv(init[0], ft)
                    self.emit("PMem.stBits %s %d %d %s" % (addr, fl["bitoff"], fl["width"], par(self.to_u64(v, ft))))
                else:
                    self.init_mem("(%s + %d)" % (addr, fl["off"]), ft, init[0])
            elif ft.kind == "rec":
                self.default_member_inits("(%s + %d)" % (addr, fl["off"]), ft.name, depth + 1)

    def loc(self):
        r = self.f.node.get("range", {})
        b = r.get("begin", {})
        e = r.get("end", {})
        loc = self.f.node.get("loc", {})
        fl = self.f.node.get("_file") or b.get("file") or loc.get("file") or "?"
        # clang's JSON omits a line or file equal to the previous location's: the declaration's own location
        return "%s:%s-%s" % (os.path.basename(fl) if fl else "?", b.get("line", loc.get("line", "?")), e.get("line", "?"))

    def ret_type(self):
        q = self.f.node["type"]["qualType"]
        if self.f.ctor:
            return VOID
        if q.startswith("auto "):
            # a trailing return type: the type of the returned expression
            def first_ret(n):
                if n.get("kind") == "ReturnStmt" and kids(n):
                    return kids(n)[0]
                for c in kids(n):
                    r = first_ret(c)
                    if r is not None:
                        return r
                return None
            r = first_ret(self.f.body)
            if r is not None and self.tr.cfg.get("dynamic") and "-> decltype(" in q and r.get("valueCategory") == "lvalue":
                # (GCS configuration) `auto MIN(const T &one, const U &two) -> decltype(one < two ? one : two)`:
                # the decltype of an lvalue is a reference
                return T("ref", name=strip_cv(r["type"].get("qualType")))
            return self.tr.ty(r["type"]) if r is not None else VOID
        # the result type: the text before the parameter list
        depth, cut = 0, None
        for i in range(len(q) - 1, -1, -1):
            c = q[i]
            if c == ")":
                depth += 1
            elif c == "(":
                depth -= 1
                if depth == 0:
                    cut = i
                    break
        rt = q[:cut].strip()
        m = re.match(r"^typename std::enable_if<.*, (\w+)>::type$", rt)
        if m:
            rt = m.group(1)
        rt = re.sub(r"\s*(const)?\s*$", "", rt) if rt.endswith(" const") else rt
        if self.tr.cfg.get("vehicle") and re.fullmatch(r"\w+", rt) and "::" in self.f.qname:
            # (Phase 5b) an enumeration of the member's class named without its class in the declaration's type
            # (`SubMode ModeGuided::submode() const`): the class's (another class's `SubMode` has another width)
            cq = self.f.qname.rsplit("::", 1)[0] + "::" + rt
            if cq in self.tr.enums:
                return self.tr.ty_str(cq)
        return self.tr.ty_str(rt)

    # -- statements
    def stmt(self, n):
        k = n.get("kind")
        if k == "CompoundStmt":
            for c in kids(n):
                self.stmt(c)
            return
        if k == "NullStmt":
            return
        if k == "DeclStmt":
            for d in kids(n):
                self.decl(d)
            return
        if k == "ReturnStmt":
            if kids(n):
                e = kids(n)[0]
                if self.ret.kind == "rec" and self.tr.cfg.get("vehicle"):
                    self.init_mem("sret", self.ret, e)
                    self.emit("return ()")
                    return
                if self.ret.kind == "ref":
                    v = self.addr_of(e)
                else:
                    v = self.rv(e, self.ret)
                self.emit("return %s" % v)
            else:
                self.emit("return ()")
            return
        if k == "IfStmt":
            ks = kids(n)
            if n.get("hasInit") or n.get("hasVar"):
                raise Reject("if with init")
            c = self.cond(ks[0])
            self.emit("if %s then" % c)
            self.block(ks[1])
            if len(ks) > 2:
                self.emit("else")
                self.block(ks[2])
            return
        if k == "WhileStmt":
            self.emit("repeat")
            self.ind += 1
            c = self.cond(kids(n)[0])
            self.emit("if !(%s) then break" % c)
            self.stmt(kids(n)[1])
            self.ind -= 1
            return
        if k == "DoStmt":
            first = self.fresh("first")
            self.emit("let mut %s := true" % first)
            self.emit("repeat")
            self.ind += 1
            self.emit("if !%s then" % first)
            self.ind += 1
            c = self.cond(kids(n)[1])
            self.emit("if !(%s) then break" % c)
            self.ind -= 1
            self.emit("%s := false" % first)
            self.stmt(kids(n)[0])
            self.ind -= 1
            return
        if k == "ForStmt":
            ks = kids(n)
            init, _, cond, inc, body = ks[0], ks[1], ks[2], ks[3], ks[4]
            if init:
                self.stmt(init) if init.get("kind") == "DeclStmt" else self.expr_stmt(init)
            first = self.fresh("first")
            self.emit("let mut %s := true" % first)
            self.emit("repeat")
            self.ind += 1
            if inc:
                self.emit("if !%s then" % first)
                self.ind += 1
                self.expr_stmt(inc)
                self.emit("pure ()")
                self.ind -= 1
            self.emit("%s := false" % first)
            if cond:
                c = self.cond(cond)
                self.emit("if !(%s) then break" % c)
            self.stmt(body)
            self.ind -= 1
            return
        if k == "CXXForRangeStmt" and self.tr.cfg.get("dynamic"):
            # (GCS configuration) `for (auto *p : array)`: clang's desugaring (the range, begin and end
            # variables, the condition `__begin != __end`, the increment, the loop variable), as a `for`
            ks = kids(n)
            for d in ks[1:4]:
                if d:
                    self.stmt(d)
            cond, inc, var, body = ks[4], ks[5], ks[6], ks[7]
            first = self.fresh("first")
            self.emit("let mut %s := true" % first)
            self.emit("repeat")
            self.ind += 1
            self.emit("if !%s then" % first)
            self.ind += 1
            self.expr_stmt(inc)
            self.emit("pure ()")
            self.ind -= 1
            self.emit("%s := false" % first)
            c = self.cond(cond)
            self.emit("if !(%s) then break" % c)
            self.stmt(var)
            self.stmt(body)
            self.ind -= 1
            return
        if k == "BreakStmt":
            self.emit("break")
            return
        if k == "ContinueStmt":
            self.emit("continue")
            return
        if k == "SwitchStmt":
            self.switch(n)
            return
        if k == "LabelStmt" and self.tr.cfg.get("goto_rewrite"):
            self.stmt(kids(n)[0])       # (Phase 5c) a label without gotos
            return
        if k == "AttributedStmt":
            for c in kids(n):
                if not c.get("kind", "").endswith("Attr"):
                    self.stmt(c)
            return
        # an expression statement
        self.expr_stmt(n)

    def block(self, n):
        self.ind += 1
        start = len(self.lines)
        self.stmt(n)
        if len(self.lines) == start:
            self.emit("pure ()")
        self.ind -= 1

    def switch(self, n):
        if self.tr.cfg.get("dynamic"):
            # (GCS configuration) a `break` nested in a section (`case X: if (c) { ...; break; } ...`): the switch
            # inside a `repeat` that its end leaves, so that a nested `break` leaves the switch (a `continue` of an
            # enclosing loop inside the switch would be captured: rejected)
            def nested(m, top):
                k = m.get("kind")
                if k in ("ForStmt", "WhileStmt", "DoStmt", "CXXForRangeStmt", "SwitchStmt"):
                    return False
                if k == "BreakStmt" and not top:
                    return True
                return any(nested(c, False) for c in kids(m))
            def cont(m):
                k = m.get("kind")
                if k in ("ForStmt", "WhileStmt", "DoStmt", "CXXForRangeStmt"):
                    return False
                return k == "ContinueStmt" or any(cont(c) for c in kids(m))
            body = kids(kids(n)[1]) if kids(n)[1].get("kind") == "CompoundStmt" else [kids(n)[1]]
            flat = []
            for b in body:
                while b.get("kind") in ("CaseStmt", "DefaultStmt"):
                    b = kids(b)[-1]
                flat.append(b)
            if any(nested(b, True) for b in flat):
                if cont(kids(n)[1]):
                    raise Reject("continue inside a switch with a nested break")
                self.emit("repeat")
                self.ind += 1
                self._switch(n, True)
                self.emit("break")
                self.ind -= 1
                return
        self._switch(n, False)

    def _switch(self, n, wrapped):
        self._sw_stack = getattr(self, "_sw_stack", []) + [wrapped]
        try:
            self._switch1(n)
        finally:
            self._sw_stack = self._sw_stack[:-1]

    def _switch1(self, n):
        ks = kids(n)
        cv = self.rv(ks[0], self.tr.ty(ks[0]["type"]))
        t = self.fresh("sw")
        self.emit("let %s := %s" % (t, cv))
        body = kids(ks[1]) if ks[1].get("kind") == "CompoundStmt" else [ks[1]]
        sections = []   # [labels or None for default, stmts]
        for s in body:
            sk = s.get("kind")
            if sk in ("CaseStmt", "DefaultStmt"):
                labels = []
                cur = s
                while cur.get("kind") in ("CaseStmt", "DefaultStmt"):
                    if cur["kind"] == "CaseStmt":
                        labels.append(self.tr.const_int(kids(cur)[0]))
                        cur = kids(cur)[-1]
                    else:
                        labels.append(None)
                        cur = kids(cur)[-1]
                sections.append([labels, [cur]])
            else:
                if not sections:
                    continue
                sections[-1][1].append(s)

        def ends(stmts):
            return stmts and stmts[-1].get("kind") in ("BreakStmt", "ReturnStmt")
        # fallthrough: a section without break or return runs into the next
        full = []
        for i, (labels, stmts) in enumerate(sections):
            st = list(stmts)
            j = i
            while not ends(st) and j + 1 < len(sections):
                j += 1
                st += sections[j][1]
            full.append((labels, st))
        default = None
        first = True
        typ = self.tr.ty(ks[0]["type"])
        for labels, st in full:
            if None in labels:
                default = st
                if len(labels) == 1:
                    continue
            vals = [l for l in labels if l is not None]
            if not vals:
                continue
            c = " || ".join("%s == %s" % (t, self.int_lit(v, typ)) for v in vals)
            self.emit(("if %s then" if first else "else if %s then") % c)
            first = False
            self.section(st)
        if default is not None:
            if first:
                self.section_inline(default)
            else:
                self.emit("else")
                self.section(default)
        elif not first:
            self.emit("else")
            self.ind += 1
            self.emit("pure ()")
            self.ind -= 1

    def section(self, st):
        self.ind += 1
        start = len(self.lines)
        self.section_inline(st)
        if len(self.lines) == start:
            self.emit("pure ()")
        self.ind -= 1

    def section_inline(self, st):
        for s in st:
            if s.get("kind") == "BreakStmt":
                break
            if not (getattr(self, "_sw_stack", None) or [False])[-1]:
                self.check_no_break(s)
            self.stmt(s)

    def check_no_break(self, n):
        k = n.get("kind")
        if k == "BreakStmt":
            raise Reject("break nested in a switch section")
        if k in ("ForStmt", "WhileStmt", "DoStmt", "SwitchStmt"):
            return
        for c in kids(n):
            self.check_no_break(c)

    def decl(self, d):
        tr = self.tr
        if d.get("kind") in ("TypedefDecl", "TypeAliasDecl", "UsingDecl", "StaticAssertDecl", "CXXRecordDecl", "EnumDecl"):
            return
        if d.get("kind") != "VarDecl":
            raise Reject("declaration %s" % d.get("kind"))
        t = tr.ty(d["type"])
        if t.kind == "rec" and re.match(r"^(WithSemaphore|HAL_Semaphore)", t.name):
            return      # WITH_SEMAPHORE: one thread (PORT-PLAN.md 4.11)
        if d.get("storageClass") == "static" and tr.cfg.get("dynamic"):
            # (GCS configuration) a static constant local (`static const mavlink_msg_entry_t mavlink_message_crcs[]`):
            # a static object of the unit, placed with its initial value from the IR (`f(...)::name`)
            q = "%s(...)::%s" % (self.f.qname, d["name"])
            mn = d.get("mangledName") or ""
            if tr.cfg.get("vehicle") and re.search(r"E\d+%s_\d+$" % re.escape(d["name"]), mn):
                # (vehicle configuration, Phase 5b) one of several static locals of the same name in one function
                # (`static const MotorDef motors[]` in each case of AP_MotorsMatrix::setup_quad_matrix): clang's
                # discriminated symbol (`..._0`, `..._1`; the demangled names are equal), placed by that symbol
                sym = "@" + (mn[1:] if mn.startswith("__Z") else mn)
                q = "%s(...)::%s%s" % (self.f.qname, d["name"], mn[mn.rindex("_"):])
                tr.static_syms[q] = (sym, self.f.node.get("_unit"))
            self.locals[d["id"]] = ("static", q, t)
            self.tr.static_addr.setdefault(q, None)
            return
        if d.get("storageClass") == "static":
            raise Reject("static local %s" % d.get("name"))
        kd = kids(d)
        if tr.cfg.get("vehicle"):
            kd = [x for x in kd if not x.get("kind", "").endswith("Attr")]     # `UNUSED_RESULT`, `__attribute__((unused))`
        init = kd[0] if kd else None
        nm = self.var_name(d["name"])
        if t.kind == "ref":
            pt = tr.ty_str(t.name)
            a = self.addr_of(init)
            self.emit("let %s : UInt64 := %s" % (nm, a))
            self.locals[d["id"]] = ("refreg", nm, pt)
            return
        if t.kind in ("rec", "arr") or d["id"] in self.addr_taken:
            off = self.slot(tr.size_of(t), 8)
            self.locals[d["id"]] = ("mem", off, t)
            if init is not None:
                self.init_mem("(fp + %d)" % off, t, init)
            return
        self.locals[d["id"]] = ("reg", nm, t)
        if init is not None:
            v = self.rv(init, t)
            self.emit("let mut %s : %s := %s" % (nm, t.lean, v))
        else:
            self.emit("let mut %s : %s := default  -- uninitialized in C" % (nm, t.lean))

    def init_mem(self, addr, t, init):
        """Initialize the object at addr (text) of type t from init."""
        k = init.get("kind")
        if t.kind == "ref" and self.tr.cfg.get("static_construction"):
            # (static construction) a reference member in an aggregate (`const struct { const char *n; AC_P &p; } ps[] =
            # {{"ANG_PIT", get_angle_pitch_p()}, ...}`): the address it is bound to
            self.emit("PMem.stU64 %s %s" % (addr, par(self.ref_arg(init, self.tr.ty_str(t.name)))))
            return
        if k == "ImplicitValueInitExpr":
            self.emit("discard <| PMem.memset %s 0 %d" % (addr, self.tr.size_of(t)))
            return
        while k in ("ExprWithCleanups", "ConstantExpr") and t.kind in ("rec", "arr"):
            init = kids(init)[0]
            k = init.get("kind")
        if t.kind in ("rec", "arr"):
            if k == "InitListExpr":
                elems = kids(init)
                if not elems and init.get("array_filler") and self.tr.cfg.get("dynamic"):
                    # (GCS configuration) clang's JSON puts the explicit elements after the filler in `array_filler`
                    # when there is a filler (`deferred_message[3] = { { MSG_HEARTBEAT, }, { MSG_NEXT_PARAM, }, }`)
                    fill = init["array_filler"]
                    elems = fill[1:]
                    zero = lambda x: x.get("kind") == "ImplicitValueInitExpr" or (x.get("kind") == "InitListExpr" and all(
                        zero(y) for y in kids(x) + x.get("array_filler", [])))
                    if not zero(fill[0]):
                        raise Reject("array filler %s" % fill[0].get("kind"))
                if t.kind == "arr":
                    es = self.tr.size_of(t.elem)
                    for i, e in enumerate(elems):
                        self.init_mem("(%s + %d)" % (addr, i * es), t.elem, e)
                    return
                if not elems:
                    return      # `{}`: zero (the frame is zeroed)
                # members in declaration order
                rec = self.tr.rec_layout(t.name)
                flds = [f for f in rec["fields"] if not f["base"]]
                for f, e in zip(flds, elems):
                    if f["bitoff"] is not None:
                        v = self.rv(e, self.tr.ty_str(f["type"]))
                        self.emit("PMem.stBits %s %d %d (%s)" % (addr, f["bitoff"], f["width"], self.to_u64(v, self.tr.ty_str(f["type"]))))
                    else:
                        self.init_mem("(%s + %d)" % (addr, f["off"]), self.tr.ty_str(f["type"]), e)
                return
            if k == "CXXConstructExpr" and t.kind == "arr" and self.tr.cfg.get("dynamic"):
                # (GCS configuration) an array of class objects, each default-constructed
                es = self.tr.size_of(t.elem)
                for i in range(t.n):
                    self.init_mem("(%s + %d)" % (addr, i * es), t.elem, init)
                return
            if k in ("CXXConstructExpr", "CXXTemporaryObjectExpr") and self.tr.cfg.get("static_construction") and \
                    t.kind == "rec" and self.tr.is_bridge_class(t.name):
                self.emit("-- %s: constructed by the estimator World" % t.name)
                return
            if k in ("CXXConstructExpr", "CXXTemporaryObjectExpr"):
                args = [a for a in kids(init) if a.get("kind") != "CXXDefaultArgExpr" or True]
                cty = init.get("ctorType", {}).get("qualType", "")
                if len(args) == 1 and cty.startswith("void (const ") and cty.endswith("&)") and \
                        self.tr.ty(args[0]["type"]).kind == "rec" and not (self.tr.cfg.get("dynamic") and
                        norm_rec(self.tr.ty(args[0]["type"]).name) != norm_rec(t.name)):
                    # the copy constructor of a trivially copyable struct
                    src = self.addr_of(args[0])
                    self.emit("discard <| PMem.memcpy %s %s %d" % (addr, src, self.tr.size_of(t)))
                    return
                if self.tr.cfg.get("vehicle") and len(args) == 1 and self.tr.ty(args[0]["type"]).kind == "rec" and \
                        (norm_rec(self.tr.ty(args[0]["type"]).name) == norm_rec(t.name) or (
                            re.sub(r"<.*", "", norm_rec(self.tr.ty(args[0]["type"]).name)).split("::")[-1] == re.sub(r"<.*", "", norm_rec(t.name)).split("::")[-1]
                            and self.tr.size_of(self.tr.ty(args[0]["type"])) == self.tr.size_of(t))) and \
                        re.match(r"^void \((const )?.*&&?\)( noexcept)?$", cty) and self.tr.ctor_fn(t.name, cty) is None:
                    # (vehicle configuration) the implicit copy or move constructor: the bytes
                    src = self.addr_of(args[0])
                    self.emit("discard <| PMem.memcpy %s %s %d" % (addr, src, self.tr.size_of(t)))
                    return
                inh = self.tr.cfg.get("static_construction") and self.tr.cfg.get("inherited_ctors", {}).get(norm_rec(t.name))
                f = self.tr.ctor_fn(t.name, cty) if not inh else None
                if inh:
                    # (static construction) `using Base::Base;`: the base's constructor (the class adds no members)
                    bn = self.tr.cfg["inherited_ctors"][norm_rec(t.name)]
                    self.tr.ensure_class(bn)
                    g = self.tr.ctor_fn(bn, cty)
                    if g is None:
                        raise Reject("inherited constructor %s %s" % (bn, cty))
                    f = g
                if f is None and self.tr.cfg.get("vehicle") and args:
                    self.tr.ensure_class(norm_rec(t.name))      # (vehicle configuration) the class's constructors
                    f = self.tr.ctor_fn(t.name, cty)
                if f is None and self.tr.cfg.get("dynamic"):
                    if t.name.startswith("std::atomic<") and len(args) == 1:
                        # `std::atomic<uint32_t> x{v}` (one thread): the value
                        at = self.tr.ty(args[0]["type"])
                        self.emit("PMem.st%s %s %s" % (at.suffix(), addr, par(self.rv(args[0], at))))
                        return
                    base = self.tr.cfg.get("inherited_ctors", {}).get(norm_rec(t.name))
                    if base:
                        # `using Base::Base;` (GCS_MAVLINK_Copter): the base's constructor, the class adding no members
                        f = self.tr.ctor_fn(base, re.sub(r"\s*noexcept(\([^)]*\))?$", "", cty))
                if f is None and not args and self.tr.cfg.get("static_construction"):
                    self.tr.ensure_class(norm_rec(t.name))
                    f = self.tr.ctor_fn(t.name, cty)
                    if f is None:
                        self.construct_default(addr, t.name)
                        return
                if f is None:
                    if not args:
                        return      # a trivial default constructor: uninitialized (the frame is zeroed)
                    raise Reject("constructor %s %s" % (t.name, cty))
                avs = self.call_args(f, args)
                self.emit("%s %s%s" % (f.lean, addr, "".join(" " + par(a) for a in avs)))
                return
            # a struct value (a call returning a struct is not supported): copy from an lvalue
            src = self.addr_of(init)
            self.emit("discard <| PMem.memcpy %s %s %d" % (addr, src, self.tr.size_of(t)))
            return
        v = self.rv(init, t)
        self.emit("PMem.st%s %s %s" % (t.suffix(), addr, par(v)))

    def expr_stmt(self, n):
        k = n.get("kind")
        if k in ("ExprWithCleanups", "ParenExpr"):
            return self.expr_stmt(kids(n)[0])
        if k == "ImplicitCastExpr" and n.get("castKind") == "ToVoid" or k == "CStyleCastExpr" and n.get("castKind") == "ToVoid":
            return self.expr_stmt(kids(n)[0])
        t = self.tr.ty(n.get("type"))
        if k in ("BinaryOperator",) and n["opcode"] == "=":
            self.assign(n)
            return
        if k == "CompoundAssignOperator":
            self.compound(n)
            return
        if k == "UnaryOperator" and n["opcode"] in ("++", "--"):
            self.incdec(n)
            return
        if k == "BinaryOperator" and n["opcode"] == ",":
            self.expr_stmt(kids(n)[0])
            self.expr_stmt(kids(n)[1])
            return
        v = self.expr(n)
        if v is None or v == "()":
            return
        self.emit("discard <| pure (%s)" % v if not v.startswith("(←") else "discard %s" % v[2:-1].strip() if False else "let _ := %s" % v)

    # -- expressions: rvalues
    def rv(self, n, want=None):
        """The value of n (pure text, after emitting what it needs), converted to want if given."""
        v = self.expr(n)
        t = self.tr.ty(n.get("type"))
        if want is not None and t.kind != want.kind and not (t.kind in ("int", "enum") and want.kind in ("int", "enum")) \
                and not (t.kind in ("ptr",) and want.kind == "ptr"):
            if t.kind == "ref":
                return v
            return self.convert(v, t, want)
        if want is not None and t.kind in ("int", "enum") and (t.bits != want.bits or t.signed != want.signed):
            return self.convert(v, t, want)
        return v

    def bind(self, text, t=None):
        """Bind a monadic or long text to a fresh name."""
        nm = self.fresh()
        self.emit("let %s ← %s" % (nm, text))
        return nm

    def letv(self, text):
        nm = self.fresh()
        self.emit("let %s := %s" % (nm, text))
        return nm

    def int_lit(self, v, t):
        if t.kind == "bool":
            return "true" if v else "false"
        if t.kind in ("float", "double"):
            return self.float_lit(Fraction(v), t)
        if t.kind == "ptr":
            return "(%d : UInt64)" % (v % (1 << 64))
        bits, signed = t.bits, t.signed
        if signed and v < 0:
            return "(%d : %s)" % (v, t.lean)
        return "(%d : %s)" % (v % (1 << bits) if not signed else v, t.lean)

    def float_lit(self, fr, t):
        import cpp2lean as C
        ct = C.FLOAT if t.kind == "float" else C.DOUBLE
        return C.flit(fr, ct, str(fr)).text

    def convert(self, v, s, d):
        import cpp2lean as C
        if s.kind == d.kind and s.kind in ("ptr",):
            return v
        if d.kind == "void":
            return "()"
        if s.kind == "ptr" and d.kind in ("int", "enum"):
            return self.convert(v, U64, d)
        if d.kind == "ptr" and s.kind in ("int", "enum"):
            return self.convert(v, s, U64)
        if d.kind == "ptr" and s.kind == "ptr":
            return v
        if d.kind == "bool" and s.kind == "ptr":
            return "(%s != 0)" % v
        cs, cd = self.ctype(s), self.ctype(d)
        if cs == cd:
            return v
        return C.conv(C.V(par(v), PREC_ATOM), cs, cd, None).text

    def ctype(self, t):
        import cpp2lean as C
        if t.kind == "bool":
            return C.BOOL
        if t.kind == "float":
            return C.FLOAT
        if t.kind == "double":
            return C.DOUBLE
        if t.kind in ("int", "enum"):
            return C.CType("int", t.bits, t.signed)
        if t.kind == "ptr":
            return C.CType("int", 64, False)
        raise Reject("conversion of %r" % t)

    def to_u64(self, v, t):
        if t.kind == "bool":
            return "(if %s then (1 : UInt64) else 0)" % v
        if t.kind in ("int", "enum"):
            return self.convert(v, t, U64)
        raise Reject("bit-field of %r" % t)

    def cond(self, n):
        t = self.tr.ty(n.get("type"))
        v = self.rv(n)
        if t.kind == "bool":
            return v
        return self.convert(v, t, BOOL)

    def expr(self, n):
        k = n.get("kind")
        tr = self.tr
        t = tr.ty(n.get("type"))
        if k in ("ParenExpr", "ExprWithCleanups"):
            return self.expr(kids(n)[0])
        if k == "ConstantExpr":
            if "value" in n and t.kind in ("int", "enum", "bool"):
                return self.int_lit(int(n["value"]) if t.kind != "bool" else n["value"] in ("true", "1"), t)
            return self.expr(kids(n)[0])
        if k == "IntegerLiteral":
            return self.int_lit(int(n["value"]), t)
        if k == "VAArgExpr" and tr.cfg.get("varargs"):
            # (Phase 5c, `varargs`) `va_arg(ap, T)`: T read from the slot ap points to, ap moved to the next slot
            lv = self.lvalue(kids(n)[0])
            ap = self.bindv(self.load(lv))
            if t.kind not in ("int", "enum", "double", "ptr", "bool"):
                raise Reject("va_arg of type %r" % t)
            v = self.bind("PMem.ld%s %s" % (t.suffix(), ap))
            self.store(lv, "(%s + 8)" % ap)
            return v
        if k == "CharacterLiteral":
            return self.int_lit(int(n["value"]), t)
        if k == "CXXBoolLiteralExpr":
            return "true" if n["value"] else "false"
        if k in ("CXXNullPtrLiteralExpr", "GNUNullExpr"):
            return "(0 : UInt64)"
        if k == "FloatingLiteral":
            import cpp2lean as C
            val, _ = C.parse_c_float(n["value"])
            return self.float_lit(val, t)
        if k == "StringLiteral":
            return self.string_addr(n)
        if k == "UnaryExprOrTypeTraitExpr":
            if n.get("name") != "sizeof":
                raise Reject("%s" % n.get("name"))
            if "argType" in n:
                st = tr.ty(n["argType"])
            else:
                st = tr.ty(kids(n)[0]["type"])
            return self.int_lit(tr.size_of(st), t)
        if k == "ImplicitCastExpr" or k in ("CStyleCastExpr", "CXXStaticCastExpr", "CXXReinterpretCastExpr",
                                             "CXXFunctionalCastExpr", "CXXConstCastExpr"):
            return self.cast(n)
        if k == "DeclRefExpr" or k == "MemberExpr" or k == "ArraySubscriptExpr" or \
                (k == "UnaryOperator" and n["opcode"] == "*"):
            # an lvalue used as a value of class type, or an enum constant / function
            rd = n.get("referencedDecl", {}) if k == "DeclRefExpr" else {}
            if rd.get("kind") == "EnumConstantDecl":
                v = tr.enum_consts.get(rd["id"])
                if v is None and tr.cfg.get("vehicle"):
                    # (Phase 5b) a constant whose declaration is in another unit's dump: by its enumeration's qualified
                    # name, then by its name (which collides: `AP_Arming::Method::MAVLINK` is 1, another MAVLINK 3)
                    v = tr.const_int(n)
                if v is None:
                    v = tr.enum_by_name.get(rd["name"])
                if v is None and tr.cfg.get("vehicle") and getattr(tr, "_cur_unit", None):
                    et = re.sub(r"^enum ", "", strip_cv((rd.get("type") or {}).get("qualType", "")))
                    tr.add_dump(tr._cur_unit, split_scope(et)[-1] if et else rd["name"])
                    v = tr.enum_consts.get(rd["id"], tr.enum_by_name.get(rd["name"]))
                if v is None:
                    raise Reject("enum constant %s" % rd["name"])
                return self.int_lit(v, t)
            if rd.get("kind") in ("FunctionDecl", "CXXMethodDecl") and tr.cfg.get("vehicle"):
                # (vehicle configuration) a function designator (decayed to its address): the function's address
                g = tr.use(rd["id"], tr.qual.get(rd["id"]) or rd.get("name"), (rd.get("type") or {}).get("qualType"))
                return "(0x%x : UInt64)" % tr.fn_address(g)
            if t.kind in ("rec", "arr"):
                return self.addr_of(n)
            return self.load(self.lvalue(n))
        if k == "UnaryOperator":
            return self.unary(n, t)
        if k == "BinaryOperator":
            return self.binary(n, t)
        if k == "CompoundAssignOperator":
            return self.compound(n)
        if k == "ConditionalOperator":
            c = self.cond(kids(n)[0])
            res = self.fresh("c")
            if t.kind in ("rec", "arr") and tr.cfg.get("vehicle"):
                # (vehicle configuration) a record value: the arm taken, into a temporary
                off = self.slot(tr.size_of(t))
                self.emit("if %s then" % c)
                self.ind += 1
                self.init_mem("(fp + %d)" % off, t, kids(n)[1])
                self.emit("pure ()")
                self.ind -= 1
                self.emit("else")
                self.ind += 1
                self.init_mem("(fp + %d)" % off, t, kids(n)[2])
                self.emit("pure ()")
                self.ind -= 1
                return "(fp + %d)" % off
            if t.kind in ("rec", "arr"):
                raise Reject("?: of a struct")
            self.emit("let mut %s : %s := default" % (res, t.lean))
            self.emit("if %s then" % c)
            self.ind += 1
            a = self.rv(kids(n)[1], t)
            self.emit("%s := %s" % (res, a))
            self.ind -= 1
            self.emit("else")
            self.ind += 1
            b = self.rv(kids(n)[2], t)
            self.emit("%s := %s" % (res, b))
            self.ind -= 1
            return res
        if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr"):
            return self.call(n)
        if k == "CXXThisExpr":
            return getattr(self, "_this", None) or "this"
        if k == "MaterializeTemporaryExpr":
            return self.expr(kids(n)[0])
        if k == "CXXDefaultArgExpr":
            raise Reject("default argument outside a call")
        if k == "SubstNonTypeTemplateParmExpr":
            return self.expr(kids(n)[-1])
        if k in ("CXXConstructExpr", "CXXTemporaryObjectExpr") and t.kind in ("rec",):
            off = self.slot(tr.size_of(t))
            self.init_mem("(fp + %d)" % off, t, n)
            return "(fp + %d)" % off
        if k == "InitListExpr" and t.kind in ("rec", "arr"):
            off = self.slot(tr.size_of(t))
            self.init_mem("(fp + %d)" % off, t, n)
            return "(fp + %d)" % off
        if k == "InitListExpr" and len(kids(n)) == 1:
            return self.rv(kids(n)[0], t)
        if k == "InitListExpr" and not kids(n):
            return "default"
        if k == "CXXDeleteExpr" and tr.cfg.get("dynamic"):
            # (GCS configuration) `delete p`: nothing (the heap is not reused; PORT-PLAN.md 4.10)
            return "()"
        if k == "CXXNewExpr":
            # `new T` / `NEW_NOTHROW T`: the heap (never fails in the model; PORT-PLAN.md 4.10)
            if n.get("isArray") and tr.cfg.get("vehicle"):
                # (vehicle configuration) `new T[n]`: n objects in the heap (zeros; never fails, never freed)
                et = tr.ty_str(re.sub(r"\s*\*$", "", t.name or ""))
                cnt = [c for c in kids(n) if tr.ty(c.get("type")).kind in ("int", "enum")]
                if not cnt:
                    raise Reject("new[] without a count")
                cv = self.rv(cnt[0], U64)
                return self.bind("PMem.alloc (%s.toNat * %d)" % (par(cv), tr.size_of(et)))
            if n.get("isArray"):
                raise Reject("new[]")
            et = tr.ty_str(t.name)
            a = self.bind("PMem.alloc %d" % tr.size_of(et))
            for c in kids(n):
                if c.get("kind") in ("CXXConstructExpr", "InitListExpr", "ParenListExpr") and et.kind == "rec":
                    self.init_mem(a, et, c)
            return a
        if k == "PredefinedExpr":
            return self.string_addr(kids(n)[0])
        if k in ("CXXScalarValueInitExpr", "ImplicitValueInitExpr"):
            return self.int_lit(0, t)
        raise Reject("expression %s in %s" % (k, self.f.qual))

    def string_addr(self, n):
        # a string literal's bytes in the constant data (a fresh copy per literal text)
        v = n["value"]
        bs = decode_c_string(v) + b"\x00"
        tr = self.tr
        if bs not in tr.literals:
            tr.literals[bs] = None
        return "(PMem'lit %s)" % json.dumps(bs.hex())

    def unary(self, n, t):
        op = n["opcode"]
        e = kids(n)[0]
        if op == "&":
            return self.addr_of(e)
        if op in ("++", "--"):
            return self.incdec(n)
        if op == "!":
            return "!%s" % par(self.cond(e))
        if op == "-":
            v = self.rv(e, t)
            if t.kind in ("float", "double"):
                return "-%s" % par(v)
            return "(0 - %s)" % par(v) if not t.signed else "-%s" % par(v)
        if op == "+":
            return self.rv(e, t)
        if op == "~":
            return "~~~%s" % par(self.rv(e, t))
        if op == "__extension__":
            return self.expr(e)
        raise Reject("unary %s" % op)

    def binary(self, n, t):
        op = n["opcode"]
        a, b = kids(n)
        if op == "=":
            return self.assign(n)
        if op == ",":
            self.expr_stmt(a)
            return self.expr(b)
        if op in ("&&", "||"):
            x = self.cond(a)
            # the right side's statements run only when needed
            mark = len(self.lines)
            saved = self.lines
            self.lines = []
            ind0 = self.ind
            self.ind = 0
            y = self.cond(b)
            pre = self.lines
            self.lines = saved
            self.ind = ind0
            if not pre:
                return "(%s %s %s)" % (par(x), op, par(y))
            res = self.fresh("sc")
            self.emit("let mut %s := %s" % (res, x))
            self.emit(("if %s then" if op == "&&" else "if !%s then") % res)
            self.ind += 1
            for ln in pre:
                self.emit(ln)
            self.emit("%s := %s" % (res, y))
            self.ind -= 1
            return res
        ta = self.tr.ty(a["type"])
        tb = self.tr.ty(b["type"])
        if op in ("==", "!=", "<", ">", "<=", ">="):
            # operands have a common type after clang's conversions (pointers: addresses)
            x = self.rv(a)
            y = self.rv(b)
            if ta.kind == "ptr" or tb.kind == "ptr":
                if ta.kind != "ptr":
                    x = self.convert(x, ta, PTR)
                if tb.kind != "ptr":
                    y = self.convert(y, tb, PTR)
            lop = {"==": "==", "!=": "!=", "<": "<", ">": ">", "<=": "≤", ">=": "≥"}[op]
            if ta.kind in ("float", "double") and op in ("==", "!="):
                return "(%s %s %s)" % (par(x), op, par(y))
            if ta.kind in ("int", "enum") and ta.signed and op in ("<", ">", "<=", ">="):
                return "(decide (%s %s %s))" % (par(x), lop, par(y))
            if ta.kind in ("float", "double") and op in ("<", ">", "<=", ">="):
                return "(decide (%s %s %s))" % (par(x), lop, par(y))
            if op in ("==", "!="):
                return "(%s %s %s)" % (par(x), op, par(y))
            return "(decide (%s %s %s))" % (par(x), lop, par(y))
        if t.kind == "ptr":
            # pointer arithmetic: p + i (scaled by the pointee's size)
            if ta.kind == "ptr":
                p, i, ti = self.rv(a), self.rv(b), tb
            else:
                p, i, ti = self.rv(b), self.rv(a), ta
            sz = self.tr.size_of(self.tr.ty_str(ta.name if ta.kind == "ptr" else tb.name))
            iv = self.convert(i, ti, I64) if ti.kind != "int" or ti.bits != 64 or not ti.signed else i
            off = "(%s * %d).toUInt64" % (par(iv), sz)
            return "(%s %s %s)" % (par(p), "+" if op == "+" else "-", off)
        if op == "-" and ta.kind == "ptr" and tb.kind == "ptr":
            sz = self.tr.size_of(self.tr.ty_str(ta.name))
            return "((%s - %s).toInt64 / %d)" % (par(self.rv(a)), par(self.rv(b)), sz)
        x = self.rv(a, t if op not in ("<<", ">>") else ta)
        y = self.rv(b, t if op not in ("<<", ">>") else tb)
        if op in ("<<", ">>"):
            # the result has the left operand's (promoted) type; the count is converted to it
            y = self.convert(y, tb, t) if (tb.bits, tb.signed) != (t.bits, t.signed) else y
            return "(%s %s %s)" % (par(x), "<<<" if op == "<<" else ">>>", par(y))
        lop = {"+": "+", "-": "-", "*": "*", "/": "/", "%": "%", "&": "&&&", "|": "|||", "^": "^^^"}[op]
        if op == "%" and t.kind == "int" and t.signed:
            return "(%s.tmod %s)" % (par(x), par(y)) if False else "(%s %% %s)" % (par(x), par(y))
        return "(%s %s %s)" % (par(x), lop, par(y))

    # -- lvalues
    def lvalue(self, n):
        k = n.get("kind")
        tr = self.tr
        t = tr.ty(n.get("type"))
        if k in ("ParenExpr",):
            return self.lvalue(kids(n)[0])
        if k == "ImplicitCastExpr" and n.get("castKind") == "UserDefinedConversion" and tr.cfg.get("dynamic"):
            # (GCS configuration) `AP_Int16` read as its value: the conversion operator's call (a reference)
            return self.lvalue(kids(n)[0])
        if k == "ImplicitCastExpr" and n.get("castKind") in ("NoOp", "UncheckedDerivedToBase", "DerivedToBase", "BaseToDerived"):
            lv = self.lvalue(kids(n)[0])
            if n.get("castKind") != "NoOp":
                return LV("mem", t, lv.text)
            return LV(lv.kind, t if t.kind not in ("rec",) else lv.t, lv.text, lv.bitoff, lv.width)
        if k == "DeclRefExpr":
            rd = n["referencedDecl"]
            did = rd["id"]
            if did in self.locals:
                kind, x, lt = self.locals[did]
                if kind == "reg":
                    return LV("reg", lt, x)
                if kind == "mem":
                    return LV("mem", lt, "(fp + %d)" % x)
                if kind in ("refreg", "memaddr"):
                    return LV("mem", lt, x)
                if kind == "static":
                    return LV("mem", lt, self.static_ref(x))
            if n.get("nonOdrUseReason") == "constant" and did not in tr.idx:
                key = "%s:%s" % (self.f.qname, rd.get("name"))
                if key in tr.cfg.get("constants", {}):
                    return LV("reg", t, tr.cfg["constants"][key])
                raise Reject("constant %s (clang folds it; give its value in the configuration's constants)" % key)
            # a static data member or a global
            q = self.static_name(did, rd, n)
            if q is not None:
                c = self.static_const(q, t)
                if c is not None:
                    return LV("reg", t, c)
                return LV("mem", t, "%s" % self.static_ref(q))
            raise Reject("reference to %s (%s) in %s" % (rd.get("name"), rd.get("kind"), self.f.qual))
        if k == "MemberExpr":
            base = kids(n)[0]
            fname = n["name"]
            # a static member through an object (`hal.storage`): a static
            md = tr.idx.get(n.get("referencedMemberDecl"))
            if md is not None and md.get("kind") == "VarDecl":
                q = tr.statics.get(md["id"])
                if q is None and tr.cfg.get("vehicle"):
                    bt0 = tr.ty(base.get("type"))
                    bt0 = tr.ty_str(bt0.name) if bt0.kind in ("ptr", "ref") else bt0
                    q = "%s::%s" % (norm_rec(bt0.name or ""), fname)
                c = self.static_const(q, t)
                if c is not None:
                    return LV("reg", t, c)
                return LV("mem", t, self.static_ref(q))
            if n.get("isArrow"):
                bt = tr.ty(base["type"])
                addr = self.rv(base)
                rec = bt.name
            else:
                bt = tr.ty(base["type"])
                if bt.kind == "ref":
                    bt = tr.ty_str(bt.name)
                addr = self.addr_of(base)
                rec = bt.name
            raw = (base.get("type") or {}).get("qualType", "")
            if raw.lstrip("const ").startswith("union ") and ("(anonymous" in raw or "(unnamed" in raw):
                return LV("mem", t, addr)       # a member of an anonymous union: at the union's address
            if tr.cfg.get("vehicle") and tr.is_bridge_class(rec):
                tr.bridge_fields.setdefault("%s::%s" % (norm_rec(rec), fname), []).append(self.site(n))
                fq = "%s::%s" % (norm_rec(rec), fname)
                if fq in tr.cfg.get("bridge_field_reads", []) and t.kind in ("float", "double", "int", "bool"):
                    # (Phase 5b) a scalar data member of an estimator object, read (`_ahrs.yaw` of AP_AHRS_View in
                    # AC_AttitudeControl::reset_yaw_target_and_rate): the object lives in the World, the value comes from
                    # its adapter `VehicleBridge.<Class>.<member>'field` (the object's memory address is not its storage)
                    name = "VehicleBridge.%s'field" % lean_name(fq)
                    tr.bridge_field_adapters[fq] = {"q": fq, "adapter": name, "type": self.bridge_describe(t)}
                    return LV("reg", t, self.bind("%s %s" % (name, par(addr))))
            if tr.cfg.get("vehicle"):
                try:
                    tr.field(rec, fname)
                except Reject:
                    # (vehicle configuration) a static data member whose declaration is in no dump (`Mode::auto_yaw`)
                    for c in tr.bases(rec):
                        q2 = "%s::%s" % (norm_rec(c), fname)
                        if q2 in tr.sym_index()["data"]:
                            return LV("mem", t, self.static_ref(q2))
            f = tr.field(rec, fname)
            ft = t
            if tr.cfg.get("dynamic") and tr.ty_str(f["type"]).kind == "ref":
                # (GCS configuration) a reference member (`AP_Mission &mission`): its cell holds the object's address
                cell = "(%s + %d)" % (par(addr), f["off"]) if f["off"] else addr
                return LV("mem", ft, self.bind("PMem.ldU64 %s" % par(cell)))
            if f["bitoff"] is not None:
                return LV("bits", ft, addr, f["bitoff"], f["width"])
            return LV("mem", ft, "(%s + %d)" % (par(addr), f["off"]) if f["off"] else addr)
        if k == "ArraySubscriptExpr":
            a, i = kids(n)
            ta = tr.ty(a["type"])
            ti = tr.ty(i["type"])
            if ta.kind != "ptr":
                a, i, ta, ti = i, a, ti, ta
            p = self.rv(a)
            iv = self.rv(i)
            es = tr.size_of(t)
            iv64 = self.convert(iv, ti, I64) if not (ti.kind == "int" and ti.bits == 64 and ti.signed) else iv
            return LV("mem", t, "(%s + (%s * %d).toUInt64)" % (par(p), par(iv64), es))
        if k == "UnaryOperator" and n["opcode"] == "*":
            return LV("mem", t, self.rv(kids(n)[0]))
        if k in ("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr"):
            # a function returning a reference: its result is the address
            return LV("mem", t, self.bindv(self.call(n)))
        if k == "MaterializeTemporaryExpr" or k in ("CXXConstructExpr", "CXXTemporaryObjectExpr") or k == "InitListExpr":
            inner = kids(n)[0] if k == "MaterializeTemporaryExpr" else n
            it = tr.ty(inner.get("type"))
            if it.kind in ("rec", "arr"):
                if inner.get("kind") in ("CXXConstructExpr", "CXXTemporaryObjectExpr", "InitListExpr"):
                    return LV("mem", it, self.expr(inner))
                return LV("mem", it, self.addr_of(inner))
            off = self.slot(tr.size_of(it), tr.size_of(it))
            v = self.rv(inner, it)
            self.emit("PMem.st%s (fp + %d) %s" % (it.suffix(), off, par(v)))
            return LV("mem", it, "(fp + %d)" % off)
        if k == "StringLiteral":
            return LV("mem", t, self.string_addr(n))
        if k == "ConditionalOperator" and tr.cfg.get("dynamic"):
            # (GCS configuration) `c ? a : b` of two lvalues, as an lvalue: the address of the arm taken
            c = self.cond(kids(n)[0])
            res = self.fresh("c")
            self.emit("let mut %s : UInt64 := 0" % res)
            for arm, kw in ((kids(n)[1], "if %s then" % c), (kids(n)[2], "else")):
                self.emit(kw)
                self.ind += 1
                self.emit("%s := %s" % (res, par(self.addr_of(arm))))
                self.ind -= 1
            return LV("mem", t, res)
        if k == "CompoundAssignOperator" or (k == "BinaryOperator" and n["opcode"] == "="):
            lv = self.lvalue(kids(n)[0])
            if k == "CompoundAssignOperator":
                self.compound(n)
            else:
                self.assign(n)
            return lv
        if k == "UnaryOperator" and n["opcode"] in ("++", "--") and n.get("isPostfix") is False:
            lv = self.lvalue(kids(n)[0])
            self.incdec(n)
            return lv
        if k == "CXXFunctionalCastExpr" and n.get("castKind") == "NoOp" and tr.cfg.get("dynamic"):
            lv = self.lvalue(kids(n)[0])
            return LV(lv.kind, t, lv.text)
        if k == "CStyleCastExpr" and n.get("castKind") in ("NoOp", "LValueBitCast"):
            lv = self.lvalue(kids(n)[0])
            return LV(lv.kind, t, lv.text)
        if tr.cfg.get("vehicle") and k in ("CXXStaticCastExpr", "CXXConstCastExpr", "CXXFunctionalCastExpr", "CXXReinterpretCastExpr",
                                           "ImplicitCastExpr") and n.get("castKind") in ("NoOp", "LValueBitCast"):
            lv = self.lvalue(kids(n)[0])
            return LV(lv.kind, t if t.kind not in ("rec",) else lv.t, lv.text, lv.bitoff, lv.width)
        raise Reject("lvalue %s%s in %s" % (k, " (%s, line %s)" % (n.get("castKind"), n.get("range", {}).get("begin", {}).get("line", "?")) if os.environ.get("CPP2LEAN_MEM_SURVEY") else "", self.f.qual))

    def bindv(self, text):
        if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*", text):
            return text
        return self.letv(text)

    def addr_of(self, n):
        lv = self.lvalue(n)
        if lv.kind != "mem":
            raise Reject("address of a register variable (%s) in %s" % (lv.text, self.f.qual))
        return lv.text

    def written_qualified(self, member, name):
        """(vehicle configuration, Phase 5b) is the member call written with a class qualifier (`GCS_MAVLINK::
        vfr_hud_alt()` in GCS_MAVLINK_Copter::vfr_hud_alt, whose qualifier has the name's length, so the token length
        does not tell): the source text at the call's begin."""
        if not self.tr.cfg.get("vehicle"):
            return False
        b = (member or {}).get("range", {}).get("begin", {})
        off, fl = b.get("offset"), self.f.node.get("_file")
        if off is None or not fl or "spellingLoc" in b or "file" in b:
            return False
        try:
            with open(fl, "rb") as fh:
                fh.seek(off)
                src = fh.read(len(name) + 2)
        except OSError:
            return False
        return not (src.startswith(name.encode()) and (len(src) == len(name) or not (chr(src[len(name)]).isalnum() or src[len(name)] == 95)))

    def qualifier_text(self, n, name):
        """(vehicle configuration, Phase 5b) the class qualifier written before `name` in the source (`X::name`), read
        from the expression's range in the function's file (clang's JSON gives the declaration without its class)."""
        b = (n or {}).get("range", {}).get("begin", {})
        off, fl = b.get("offset"), self.f.node.get("_file")
        if off is None or not fl or b.get("tokLen") in (None, len(name)) or "spellingLoc" in b or "file" in b:
            return None
        try:
            src = open(fl, "rb").read()
        except OSError:
            return None
        m = re.match(rb"([A-Za-z_][A-Za-z_0-9]*(?:\s*::\s*[A-Za-z_][A-Za-z_0-9]*)*)\s*::\s*" + re.escape(name.encode()) + rb"\b", src[off:off + 400])
        return re.sub(r"\s+", "", m.group(1).decode()) if m else None

    def static_name(self, did, rd, ref=None):
        tr = self.tr
        if did in tr.statics:
            return tr.statics[did]
        n = tr.idx.get(did)
        if n is not None and n.get("kind") == "VarDecl":
            pd = n.get("previousDecl")
            if pd in tr.statics:
                return tr.statics[pd]
            # a global (`hal`, `copter`): by name
            return rd.get("name")
        if rd.get("kind") == "VarDecl":
            # a static member declared in another dump: by its name, if unique
            c = sorted(set(q for q in tr.statics.values() if q.split("::")[-1] == rd.get("name")))
            if len(c) == 1:
                return c[0]
            if tr.cfg.get("dynamic") and not c:
                return rd.get("name")       # (GCS configuration) a global declared `extern` in a header not dumped
            if tr.cfg.get("dynamic") and len(c) == 2 and rd.get("name") in c:
                return [x for x in c if x != rd.get("name")][0]     # a static member dumped also without its class
            if tr.cfg.get("static_construction") and len(c) > 1:
                # (vehicle configuration) several static members of that name: the one of the reference's type
                # (`const struct AP_Param::GroupInfo[26]`), if unique
                rt = (rd.get("type") or {}).get("qualType")
                c2 = [q for q in c if any((nd.get("type") or {}).get("qualType") == rt for nd in tr.static_nodes.get(q, []))]
                if len(c2) == 1:
                    return c2[0]
            if tr.cfg.get("vehicle") and len(c) > 1:
                # (Phase 5b) several static members of that name: the one the source names (`AC_AttitudeControl_Multi::
                # var_info` in Copter::allocate_motors was taken for AP_MotorsMulticopter's by static_refs below)
                qual = self.qualifier_text(ref, rd.get("name") or "")
                if qual and "%s::%s" % (qual, rd.get("name")) in c:
                    return "%s::%s" % (qual, rd.get("name"))
            if tr.cfg.get("static_refs"):
                # (vehicle configuration) a static member named through a derived class (`AP_MotorsMatrix::var_info` is
                # AP_MotorsMulticopter's): the configured static for this function and name
                key = "%s:%s:%s" % (self.f.qual, rd.get("name"), (rd.get("type") or {}).get("qualType"))
                if key in tr.cfg["static_refs"]:
                    return tr.cfg["static_refs"][key]
                print("static_refs: unresolved %s (candidates %s)" % (key, c), file=sys.stderr)
        return None

    def static_const(self, q, t):
        """A `static const` integral member with an in-class initializer: its value (no storage in the IR)."""
        if t.kind in ("float", "double") and self.tr.cfg.get("vehicle"):
            # (vehicle configuration) a `static constexpr float` member (`Location::LOCATION_SCALING_FACTOR`): its
            # literal, converted as C converts it (to the literal's type first)
            import cpp2lean as C
            for n in self.tr.static_nodes.get(q, []):
                if "const" in n.get("type", {}).get("qualType", "") and kids(n):
                    e = kids(n)[0]
                    while e.get("kind") in ("ImplicitCastExpr", "ParenExpr", "ConstantExpr", "CStyleCastExpr") and kids(e):
                        e = kids(e)[0]
                    if e.get("kind") == "FloatingLiteral":
                        val, _ = C.parse_c_float(e["value"])
                        lt = self.tr.ty(e.get("type"))
                        if lt.kind == "double" and t.kind == "float":
                            import struct
                            val = Fraction(struct.unpack(">d", struct.pack(">Q", C.float_bits(val, C.DOUBLE)))[0])
                        return self.float_lit(val, t)
            return None
        if t.kind not in ("int", "enum", "bool"):
            return None
        m = re.match(r"^Bitmask<(\d+)>::NUMWORDS$", q or "")
        if m and self.tr.cfg.get("dynamic"):
            # (GCS configuration) `static constexpr uint16_t NUMWORDS = ((num_bits+31)/32);` of a specialization
            # (clang's JSON gives the dependent initializer only)
            return self.int_lit((int(m.group(1)) + 31) // 32, t)
        for n in self.tr.static_nodes.get(q, []):
            if "const" in n.get("type", {}).get("qualType", "") and kids(n) and not n.get("previousDecl"):
                try:
                    v = self.tr.const_int(kids(n)[0])
                except Exception:
                    return None
                return self.int_lit(v, t)
        return None

    def static_ref(self, q):
        if q is None:
            raise Reject("a static member whose declaration is in no dump")
        self.tr.static_addr.setdefault(q, None)
        return "(PMem'static %s)" % json.dumps(q)

    def load(self, lv):
        if lv.kind == "reg":
            return lv.text
        if lv.kind == "bits":
            raw = self.bind("PMem.ldBits %s %d %d" % (par(lv.text), lv.bitoff, lv.width))
            return self.convert(raw, U64, lv.t) if lv.t.kind != "bool" else "(%s != 0)" % raw
        t = lv.t
        if t.kind == "ref":
            raise Reject("load of a reference")
        if t.kind in ("rec", "arr"):
            return lv.text
        return self.bind("PMem.ld%s %s" % (t.suffix(), par(lv.text)))

    def store(self, lv, v):
        if lv.kind == "reg":
            self.emit("%s := %s" % (lv.text, v))
            return
        if lv.kind == "bits":
            self.emit("PMem.stBits %s %d %d %s" % (par(lv.text), lv.bitoff, lv.width, par(self.to_u64(v, lv.t))))
            return
        t = lv.t
        if t.kind in ("rec",):
            self.emit("discard <| PMem.memcpy %s %s %d" % (par(lv.text), par(v), self.tr.size_of(t)))
            return
        self.emit("PMem.st%s %s %s" % (t.suffix(), par(lv.text), par(v)))

    def assign(self, n):
        a, b = kids(n)
        t = self.tr.ty(n["type"])
        if t.kind in ("rec",):
            dst = self.addr_of(a)
            src = self.addr_of(b) if b.get("kind") not in ("CXXConstructExpr", "InitListExpr") else self.expr(b)
            self.emit("discard <| PMem.memcpy %s %s %d" % (par(dst), par(src), self.tr.size_of(t)))
            return dst
        v = self.rv(b, t)
        v = self.bindv(v) if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*|\(-?\d+ : \w+\)|true|false", v) else v
        lv = self.lvalue(a)
        self.store(lv, v)
        return v

    def compound(self, n):
        a, b = kids(n)
        op = n["opcode"][:-1]
        ct = self.tr.ty(n["computationResultType"]) if "computationResultType" in n else self.tr.ty(n["type"])
        clt = self.tr.ty(n["computationLHSType"]) if "computationLHSType" in n else ct
        t = self.tr.ty(n["type"])
        lv = self.lvalue(a)
        if lv.kind == "mem" and not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*|\(fp \+ \d+\)", lv.text):
            lv = LV(lv.kind, lv.t, self.letv(lv.text), lv.bitoff, lv.width)
        cur = self.load(lv)
        if t.kind == "bool" and op in ("&", "|", "^") and self.tr.cfg.get("vehicle"):
            # (vehicle configuration) `ok &= f()` on a bool: the logical operation (both sides evaluated)
            y = self.cond(b)
            v = self.bindv("(%s %s %s)" % (par(cur), {"&": "&&", "|": "||", "^": "!="}[op], par(y)))
            self.store(lv, v)
            return v
        if t.kind == "ptr":
            sz = self.tr.size_of(self.tr.ty_str(t.name))
            y = self.rv(b)
            tb = self.tr.ty(b["type"])
            iv = self.convert(y, tb, I64)
            v = "(%s %s (%s * %d).toUInt64)" % (par(cur), "+" if op == "+" else "-", par(iv), sz)
        else:
            x = self.convert(cur, t, clt) if (t.kind, t.bits, t.signed) != (clt.kind, clt.bits, clt.signed) else cur
            y = self.rv(b, ct if op not in ("<<", ">>") else None)
            if op in ("<<", ">>"):
                tb = self.tr.ty(b["type"])
                y = self.convert(y, tb, ct) if (tb.kind, tb.bits, tb.signed) != (ct.kind, ct.bits, ct.signed) else y
            lop = {"+": "+", "-": "-", "*": "*", "/": "/", "%": "%", "&": "&&&", "|": "|||", "^": "^^^", "<<": "<<<", ">>": ">>>"}[op]
            r = "(%s %s %s)" % (par(x), lop, par(y))
            v = self.convert(r, ct, t) if (ct.kind, ct.bits, ct.signed) != (t.kind, t.bits, t.signed) else r
        v = self.bindv(v)
        self.store(lv, v)
        return v

    def incdec(self, n):
        a = kids(n)[0]
        t = self.tr.ty(a["type"])
        lv = self.lvalue(a)
        if lv.kind == "mem" and not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*|\(fp \+ \d+\)", lv.text):
            lv = LV(lv.kind, lv.t, self.letv(lv.text), lv.bitoff, lv.width)
        old = self.bindv(self.load(lv))
        if lv.kind == "reg" and n.get("isPostfix") and (self.tr.cfg.get("dynamic") or os.environ.get("CPP2LEAN_MEM_POSTFIX_FIX")):
            # (GCS configuration) `buf[ofs++] = x` on a register: the value before the increment, a snapshot (the
            # variable's name would read the incremented value)
            old = self.letv(old)
        if t.kind == "ptr":
            sz = self.tr.size_of(self.tr.ty_str(t.name))
            new = "(%s %s %d)" % (old, "+" if n["opcode"] == "++" else "-", sz)
        elif t.kind == "bool":
            raise Reject("++ on bool")
        else:
            new = "(%s %s 1)" % (old, "+" if n["opcode"] == "++" else "-")
        new = self.letv(new)
        self.store(lv, new)
        return old if n.get("isPostfix") else new

    def cast(self, n):
        ck = n.get("castKind")
        e = kids(n)[0]
        t = self.tr.ty(n.get("type"))
        te = self.tr.ty(e.get("type"))
        if ck == "LValueToRValue":
            if te.kind in ("rec", "arr"):
                return self.addr_of(e)
            e1 = e
            while e1.get("kind") == "ParenExpr":
                e1 = kids(e1)[0]
            if e1.get("kind") == "ConditionalOperator" and self.tr.cfg.get("dynamic"):
                # (GCS configuration) `a < b ? a : b` of two lvalues, read: the value of the arm taken
                c = self.cond(kids(e1)[0])
                res = self.fresh("c")
                self.emit("let mut %s : %s := default" % (res, t.lean))
                for arm, kw in ((kids(e1)[1], "if %s then" % c), (kids(e1)[2], "else")):
                    self.emit(kw)
                    self.ind += 1
                    self.emit("%s := %s" % (res, self.load(self.lvalue(arm))))
                    self.ind -= 1
                return res
            return self.load(self.lvalue(e))
        if ck in ("NoOp",):
            if t.kind in ("rec", "arr"):
                return self.addr_of(e) if e.get("kind") not in ("CXXConstructExpr", "InitListExpr", "MaterializeTemporaryExpr") else self.expr(e)
            v = self.expr(e)
            return v
        if ck in ("ArrayToPointerDecay",):
            return self.addr_of(e)
        if ck in ("FunctionToPointerDecay", "BuiltinFnToFnPtr"):
            return self.expr(e)
        if ck in ("BitCast", "UncheckedDerivedToBase", "DerivedToBase", "BaseToDerived", "LValueBitCast"):
            if t.kind == "ptr" or te.kind == "ptr":
                return self.rv(e)
            if t.kind in ("rec",):
                return self.addr_of(e)
            return self.rv(e)
        if ck == "NullToPointer":
            self.expr_stmt(e) if e.get("kind") not in ("IntegerLiteral", "CXXNullPtrLiteralExpr", "GNUNullExpr", "ImplicitCastExpr", "ParenExpr") else None
            return "(0 : UInt64)"
        if ck in ("IntegralCast", "IntegralToBoolean", "FloatingToBoolean", "IntegralToFloating", "FloatingToIntegral",
                  "FloatingCast", "PointerToIntegral", "IntegralToPointer", "PointerToBoolean", "BooleanToSignedIntegral"):
            import cpp2lean as C
            if ck in ("FloatingCast", "IntegralToFloating", "FloatingToIntegral", "IntegralCast"):
                cn = C.const_number(e) if False else None
            v = self.rv(e)
            if ck == "PointerToBoolean":
                return "(%s != 0)" % par(v)
            return self.convert(v, te, t)
        if ck == "ToVoid":
            self.expr_stmt(e)
            return "()"
        if ck == "ConstructorConversion":
            return self.expr(e)
        if ck == "UserDefinedConversion":
            return self.expr(e)
        if ck == "Dependent":
            raise Reject("dependent cast")
        raise Reject("cast %s in %s" % (ck, self.f.qual))

    # -- calls
    def callee_decl(self, n):
        k = n.get("kind")
        c = kids(n)[0]
        while c.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
            c = kids(c)[0]
        if c.get("kind") == "DeclRefExpr":
            return c["referencedDecl"], None, c
        if c.get("kind") == "MemberExpr":
            return {"id": c["referencedMemberDecl"], "name": c["name"]}, c, c
        if c.get("kind") == "BinaryOperator" and c.get("opcode") in ("->*", ".*") and self.tr.cfg.get("vehicle"):
            # (vehicle configuration) `(t->*method)(args...)` with a constant member pointer (Functor's
            # method_wrapper<T, method>): a call of that member function on the object
            obj, mp = kids(c)
            while mp.get("kind") in ("SubstNonTypeTemplateParmExpr", "UnaryOperator", "ImplicitCastExpr", "ParenExpr", "ConstantExpr"):
                mp = kids(mp)[-1]
            if mp.get("kind") != "DeclRefExpr" or mp["referencedDecl"].get("kind") != "CXXMethodDecl":
                raise Reject("call through a member pointer that is not a constant")
            md = mp["referencedDecl"]
            pseudo = {"kind": "MemberExpr", "isArrow": c["opcode"] == "->*", "inner": [obj], "name": md["name"],
                      "referencedMemberDecl": md["id"]}
            return {"id": md["id"], "name": md["name"], "type": md.get("type")}, pseudo, pseudo
        raise Reject("call through %s" % c.get("kind"))

    def is_indirect(self, c):
        while c.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
            if c.get("kind") == "ImplicitCastExpr" and c.get("castKind") == "LValueToRValue":
                return True
            c = kids(c)[0]
        return False

    def fnptr_call(self, n, c, args, t):
        """(vehicle configuration) a call through a function pointer (`_method(_obj, args...)` of Functor): the
        dispatcher of the pointer's function type over the functions whose address the program takes with that type."""
        tr = self.tr
        pt = re.sub(r"\s+", " ", (c.get("type") or {}).get("qualType", "")).replace(" noexcept", "")
        sig = pt.replace("(*)", "").replace("  ", " ")
        ret, ps = parse_fn_type(sig)
        if ret is None:
            raise Reject("function pointer type %s" % pt)
        d = tr.fnptr_sigs.setdefault(sig, {"targets": {}})
        if "name" not in d:
            d["name"] = "fnptr'%d" % len([x for x in tr.fnptr_sigs.values() if "name" in x])
        fv = self.rv(c)
        rt = tr.ty_str(ret)
        avs = []
        for a, p in zip(args, ps):
            ptt = tr.ty_str(p)
            if ptt.kind == "ref":
                avs.append(self.ref_arg(a, tr.ty_str(ptt.name)))
            elif ptt.kind == "rec":
                off = self.slot(tr.size_of(ptt))
                self.init_mem("(fp + %d)" % off, ptt, a)
                avs.append("(fp + %d)" % off)
            else:
                avs.append(self.rv(a, ptt))
        if rt.kind == "rec":
            raise Reject("function pointer returning a record")
        text = "%s %s%s" % (d["name"], par(fv), "".join(" " + par(v) for v in avs))
        if rt.kind == "void":
            self.emit(text)
            return "()"
        return self.bind(text)

    def virtual_decl(self, q, decl):
        """(Phase 5b) the in-class declaration of member function q that is `virtual` (or pure), with decl's parameter
        types, if any: the declaration a definition outside its class refers to (`previousDecl`), else one of q's
        declarations in the dumps (the class dumped on demand)."""
        tr = self.tr
        pd = tr.idx.get(decl.get("previousDecl")) if decl.get("previousDecl") else None
        if pd is not None and (pd.get("virtual") or pd.get("pure")):
            return pd
        def ptypes(d):
            return [((k.get("type") or {}).get("qualType")) for k in kids(d) if k.get("kind") == "ParmVarDecl"]
        cands = list(tr.decls.get(q, []))
        if not any(c.get("virtual") or c.get("pure") for c in cands) and "::" in q:
            try:
                tr.ensure_class(q.rsplit("::", 1)[0])
            except Reject:
                pass
            cands = list(tr.decls.get(q, []))
        for c in cands:
            if (c.get("virtual") or c.get("pure")) and (not decl or ptypes(c) == ptypes(decl)):
                return c
        return None

    def address_dispatch(self, dref, member, q, did):
        """(vehicle configuration, `by_address`) a virtual call through a pointer or reference to a class whose
        objects are member objects of one static object (`Mode *`: the modes are members of `copter`): a dispatcher
        over the addresses of those members, each arm the final overrider of that member's class."""
        tr = self.tr
        ba = tr.cfg.get("by_address") or {}
        if member is None or "::" not in (q or ""):
            return None
        cls, name = q.rsplit("::", 1)
        if cls not in ba:
            return None
        decl = tr.idx.get(did) or next(iter(tr.decls.get(q, [])), None) or {}
        if not (decl.get("virtual") or decl.get("pure")):
            # (Phase 5b) the out-of-line definition (`bool Mode::do_user_takeoff_start_m(float)`, takeoff.cpp) carries no
            # `virtual`: the in-class declaration does (mode.h:306; ModeGuided overrides it)
            vd = self.virtual_decl(q, decl)
            if vd is None:
                return None
            decl = vd
        base = kids(member)[0]
        while base.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
            base = kids(base)[0]
        rb = member.get("range", {}).get("begin", {})
        if base.get("kind") == "CXXThisExpr" and base.get("implicit") and (rb.get("tokLen") not in (None, len(name)) or
                                                                           self.written_qualified(member, name)):
            return None     # qualified: Class::f(...)
        ty = (decl.get("type") or {}).get("qualType", "")
        sig = ty[ty.index("("):] if "(" in ty else ty
        key = (cls, name, sig)
        if key not in tr.vdispatch:
            obj, objcls = ba[cls]
            nargs = len([k for k in kids(decl) if k.get("kind") == "ParmVarDecl"])
            arms = []
            for fl in tr.rec_layout(objcls)["fields"]:
                if fl["base"] or fl["bitoff"] is not None:
                    continue
                ft = tr.ty_str(fl["type"])
                if ft.kind != "rec" or norm_rec(ft.name) == cls or cls not in tr.bases(ft.name):
                    continue
                g = tr.final_overrider(ft.name, name, sig, nargs)
                if g is not None:
                    arms.append((fl["off"], ft.name, g))
            tr.static_addr.setdefault(obj, None)

            class Disp:
                pass
            dp = Disp()
            dp.node, dp.qname, dp.qual = decl, q, q
            dp.params = [k for k in kids(decl) if k.get("kind") == "ParmVarDecl"]
            dp.is_static, dp.ctor, dp.body = False, False, None
            dp.lean = "vcall'%s'%s'%d" % (lean_name(cls).replace(".", "'"), name, len(tr.vdispatch))
            tr.vdispatch[key] = {"fn": dp, "arms": arms, "obj": obj}
        return tr.vdispatch[key]["fn"]

    def callee_qname(self, dref, member):
        tr = self.tr
        if dref["id"] in tr.qual:
            return tr.qual[dref["id"]]
        if member is not None:
            bt = tr.ty(kids(member)[0].get("type"))
            if bt.kind in ("ptr", "ref"):
                bt = tr.ty_str(bt.name)
            return "%s::%s" % (norm_rec(bt.name or ""), member["name"])
        return dref.get("name")

    def call_args(self, f, args):
        """Arguments of a call of f, as Lean texts (the callee's convention)."""
        out = []
        params = f.params
        for i, p in enumerate(params):
            pt = self.tr.ty(p["type"])
            if i < len(args):
                a = args[i]
            else:
                a = None
            if a is None or a.get("kind") == "CXXDefaultArgExpr":
                # the parameter's default argument
                init = kids(p)[0] if kids(p) else None
                if init is None:
                    raise Reject("missing argument %d of %s" % (i, f.qual))
                a = init
            if pt.kind == "ref":
                rt = self.tr.ty_str(pt.name)
                out.append(self.ref_arg(a, rt))
            elif pt.kind == "rec":
                # by value: a copy in the caller's frame
                sz = self.tr.size_of(pt)
                off = self.slot(sz)
                self.init_mem("(fp + %d)" % off, pt, a)
                out.append("(fp + %d)" % off)
            else:
                out.append(self.rv(a, pt))
        if self.tr.cfg.get("varargs") and getattr(f, "node", {}).get("variadic"):
            out.append(self.va_block(args[len(params):]))
        return out

    def va_block(self, extra):
        """(Phase 5c, `varargs`) the variadic arguments of a call (after the default promotions clang made explicit),
        each in its own 8-byte slot of a block in the caller's frame, as arm64 Apple passes them on the stack: integers
        sign- or zero-extended to 64 bits, `double` as its bits, pointers as addresses; the block's address."""
        off = self.slot(8 * max(len(extra), 1), 8)
        for j, a in enumerate(extra):
            at = self.tr.ty(a.get("type"))
            if at.kind in ("ptr", "ref"):
                v = self.rv(a)
            elif at.kind == "arr":
                v = self.addr_of(a)
            elif at.kind == "double":
                v = "(Binary64.toBits %s)" % par(self.rv(a, DOUBLE))
            elif at.kind == "float":
                v = "(Binary64.toBits %s)" % par(self.rv(a, DOUBLE))
            elif at.kind in ("int", "enum"):
                v = self.convert(self.rv(a), at, U64)
            elif at.kind == "bool":
                v = "(if %s then (1 : UInt64) else 0)" % par(self.rv(a))
            else:
                raise Reject("variadic argument of type %r" % at)
            self.emit("PMem.stU64 (fp + %d) %s" % (off + 8 * j, par(v)))
        return "(fp + %d)" % off

    def ref_arg(self, a, rt):
        """The address bound to a reference parameter (a temporary for a prvalue)."""
        k = a.get("kind")
        while k in ("ExprWithCleanups",):
            a = kids(a)[0]
            k = a.get("kind")
        if k == "MaterializeTemporaryExpr":
            inner = kids(a)[0]
            it = self.tr.ty(inner.get("type"))
            if it.kind in ("rec", "arr"):
                if inner.get("kind") in ("CXXConstructExpr", "CXXTemporaryObjectExpr", "InitListExpr"):
                    return self.expr(inner)
                return self.addr_of(inner)
            off = self.slot(self.tr.size_of(it), self.tr.size_of(it))
            v = self.rv(inner, it)
            self.emit("PMem.st%s (fp + %d) %s" % (it.suffix(), off, par(v)))
            return "(fp + %d)" % off
        return self.addr_of(a)

    def call(self, n):
        tr = self.tr
        k = n.get("kind")
        t = tr.ty(n.get("type"))
        if tr.cfg.get("vehicle") and k == "CallExpr" and self.is_indirect(kids(n)[0]):
            c0 = kids(n)[0]
            while c0.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                c0 = kids(c0)[0]
            bq = None
            if c0.get("kind") == "MemberExpr":
                bt0 = tr.ty(kids(c0)[0].get("type"))
                bt0 = tr.ty_str(bt0.name) if bt0.kind in ("ptr", "ref") else bt0
                bq = "%s::%s" % (norm_rec(bt0.name or ""), c0.get("name"))
            if bq not in tr.boundary:       # a function pointer member configured as boundary (GCS: signing callbacks)
                return self.fnptr_call(n, kids(n)[0], kids(n)[1:], t)
        dref, member, cnode = self.callee_decl(n)
        did = dref["id"]
        name = dref.get("name")
        args = kids(n)[1:]
        # the boundary and the C library
        q = self.callee_qname(dref, member)
        if tr.cfg.get("static_construction") and name == "bind" and len(args) == 1 and \
                re.match(r"^(Functor<.*>::)?bind$", q or "") and t.kind == "rec" and norm_rec(t.name).startswith("Functor<"):
            # (vehicle configuration, static construction) FUNCTOR_BIND_MEMBER: `Functor<R, Args...>::bind<T, method>(obj)`
            # is `{ obj, method_wrapper<T, method> }` (functor.h:75): the object and the bound member function's address
            # (a dispatcher target of the functor's pointer type: `bound_methods`)
            meth = self.bound_method(n, dref)
            off = self.slot(16)
            self.emit("PMem.stU64 (fp + %d) %s" % (off, par(self.rv(args[0]))))
            self.emit("PMem.stU64 (fp + %d) %s" % (off + 8, "(0x%x : UInt64)" % tr.bound_address(meth) if meth is not None else "(0 : UInt64)"))
            return "(fp + %d)" % off
        if tr.cfg.get("vehicle"):
            bq = q
            if k == "CXXOperatorCallExpr" and did not in tr.qual and args and tr.ty(args[0].get("type")).kind == "rec":
                bq = "%s::%s" % (tr.ty(args[0].get("type")).name, name)
            if tr.is_bridge(bq):
                return self.bridge_call(n, bq, did, dref, t, member, args)
        if tr.cfg.get("dynamic"):
            uq = q
            if k == "CXXOperatorCallExpr" and did not in tr.qual and args and tr.ty(args[0].get("type")).kind == "rec":
                uq = "%s::%s" % (tr.ty(args[0].get("type")).name, name)
            if uq in tr.cfg.get("unreached", []) or name in tr.cfg.get("unreached_names", []):
                # (GCS configuration) outside this slice and not reached by the recorded sessions: a call records
                # the name (the harness reports it) and gives the type's default
                self.emit("PMem.unreached %s" % json.dumps(uq))
                return "()" if t.kind == "void" else ("(default : %s)" % ("UInt64" if t.kind in ("ref", "ptr") else t.lean))
            if name == "operator=" and len(args) == 2 and tr.ty(args[0].get("type")).kind == "rec" and \
                    norm_rec(tr.ty(args[0].get("type")).name) == norm_rec(tr.ty(args[1].get("type")).name if tr.ty(args[1].get("type")).kind == "rec" else ""):
                d0 = tr.idx.get(did) or {}
                if d0.get("isImplicit") or d0.get("explicitlyDefaulted") or did not in tr.qual or "operator=" in str(tr.cfg.get("trivial_assign", [])) and uq in tr.cfg.get("trivial_assign", []):
                    # the implicit (trivial) copy assignment of a struct: its bytes
                    a0 = self.addr_of(args[0])
                    a1 = self.addr_of(args[1])
                    self.emit("discard <| PMem.memcpy %s %s %d" % (par(a0), par(a1), tr.size_of(tr.ty(args[0].get("type")))))
                    return a0
        b = self.boundary_call(n, q, name, member, args, t)
        if b is not None:
            return b
        if q in tr.cfg.get("drop", []):
            self.emit("-- %s: dropped (configuration)" % q) if t.kind == "void" else None
            if t.kind == "void":
                return "()"
            raise Reject("dropped function %s has a result" % q)
        if k == "CXXOperatorCallExpr":
            # an overloaded operator: a member (first argument the object) or a free function
            oq = q
            if did not in tr.qual and args:
                at = tr.ty(args[0].get("type"))
                if at.kind == "rec":
                    oq = "%s::%s" % (at.name, name)
            if oq in tr.boundary and tr.cfg.get("dynamic"):
                v = tr.boundary[oq]
                if "{" in v:
                    # an operator's object is its first argument
                    v2 = v.replace("{this}", "{T}")
                    for i in range(len(args) - 1, 0, -1):
                        v2 = v2.replace("{%d}" % (i - 1), "{%d}" % i)
                    return self.boundary_text(v2.replace("{T}", "{0}"), args, None, t)
                return v if t.kind != "void" else "()"
            try:
                f = tr.use(did, oq, dref.get("type", {}).get("qualType"))
            except Reject as e:
                raise Reject("%s (operator %s on %s in %s)" % (e, name, tr.ty(args[0].get("type")) if args else None, self.f.qual))
            if f.node["kind"] == "CXXMethodDecl" and not f.is_static:
                obj = self.addr_of(args[0])
                avs = self.call_args(f, args[1:])
                return self.call_text(f, [obj] + avs, t)
            return self.call_text(f, self.call_args(f, args), t)
        self._cur_call = n
        f = self.dynamic_callee(dref, member, q)
        if f is None and tr.cfg.get("vehicle"):
            f = self.address_dispatch(dref, member, q, did)
        tr._call_nargs = len(args)
        tr._call_args = args if tr.cfg.get("vehicle") else None
        if f is None and tr.cfg.get("dynamic"):
            f0 = tr.fn_of(did, self.callee_qname(dref, member), dref.get("type", {}).get("qualType") if isinstance(dref.get("type"), dict) else None)
            if f0.qname in tr.cfg.get("unreached", []) or f0.qname in tr.boundary:
                f = f0
        if f is None and tr.cfg.get("vehicle"):
            # (vehicle configuration) a static member function called by its unqualified name: the definition's
            # qualified name decides whether it is the estimator's
            try:
                f1 = tr.fn_of(did, self.callee_qname(dref, member), dref.get("type", {}).get("qualType") if isinstance(dref.get("type"), dict) else None)
            except Reject:
                f1 = None
            if f1 is not None and tr.is_bridge(f1.qname):
                tr._call_args = None
                return self.bridge_call(n, f1.qname, did, dref, t, member, args)
        if f is None:
            try:
                f = tr.use(did, self.callee_qname(dref, member), dref.get("type", {}).get("qualType") if isinstance(dref.get("type"), dict) else None)
            finally:
                tr._call_args = None
        tr._call_args = None
        if tr.cfg.get("dynamic") and f.qname in tr.cfg.get("unreached", []):
            self.emit("PMem.unreached %s" % json.dumps(f.qname))
            return "()" if t.kind == "void" else ("(default : %s)" % ("UInt64" if t.kind in ("ref", "ptr") else t.lean))
        if tr.cfg.get("dynamic") and f.qname in tr.boundary:
            v = tr.boundary[f.qname]
            if "{" in v:
                return self.boundary_text(v, args, kids(member)[0] if member is not None else None, t)
            return v if t.kind != "void" else "()"
        avs = self.call_args(f, args)
        is_method = f.node["kind"] in ("CXXMethodDecl", "CXXConversionDecl") and not f.is_static
        if is_method:
            if member is None:
                obj = "this"
            else:
                base = kids(member)[0]
                if member.get("isArrow"):
                    obj = self.rv(base)
                else:
                    obj = self.addr_of(base)
            avs = [obj] + avs
        elif member is not None:
            # a static member called through an object: evaluate nothing of it
            pass
        return self.call_text(f, avs, t)

    def dynamic_callee(self, dref, member, q):
        """(configuration `dynamic`, GCS) a member function call on an object of a class whose objects all have one
        known dynamic class (`GCS_MAVLINK` objects are `GCS_MAVLINK_Copter`s): the final overrider, found by name and
        parameter types along the configured chain of classes (most derived first). A call qualified with a class
        name (`GCS_MAVLINK::handle_message(msg)` in an overrider) is not virtual."""
        dyn = self.tr.cfg.get("dynamic")
        if not dyn or member is None or "::" not in (q or ""):
            return None
        cls, name = q.rsplit("::", 1)
        if cls not in dyn:
            return None
        base = kids(member)[0]
        while base.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
            base = kids(base)[0]
        rb = member.get("range", {}).get("begin", {})
        if base.get("kind") == "CXXThisExpr" and base.get("implicit") and (rb.get("tokLen") not in (None, len(name)) or
                                                                           self.written_qualified(member, name)):
            return None     # qualified: Class::f(...)
        decl = self.tr.idx.get(dref["id"]) or {}
        ty = (decl.get("type") or {}).get("qualType") or (dref.get("type") or {}).get("qualType") or ""
        sig = ty[ty.index("("):] if "(" in ty else ty
        nargs = len(kids(self._cur_call)) - 1
        if self.tr.cfg.get("vehicle"):
            # (vehicle configuration) only a virtual function is dispatched; the final overrider along the base chain
            # of the one dynamic class (its members' declarations dumped on demand)
            d0 = decl or next(iter(self.tr.decls.get(q, [])), None) or {}
            if not d0:
                self.tr.ensure_class(cls)
                d0 = next(iter(self.tr.decls.get(q, [])), None) or {}
            if not (d0.get("virtual") or d0.get("pure")):
                # (Phase 5b) a definition outside its class: its in-class declaration
                vd = self.virtual_decl(q, d0)
                if vd is None:
                    return None
                d0 = vd
            if not sig:
                ty = (d0.get("type") or {}).get("qualType") or ""
                sig = ty[ty.index("("):] if "(" in ty else ty
            return self.tr.final_overrider(dyn[cls][0], name, sig, nargs)
        for dc in dyn[cls]:
            cands = [g for g in set(self.tr.fns.values()) if g.qname == dc + "::" + name and not g.ctor]
            if sig:
                cands = [g for g in cands if (lambda t: t[t.index("("):] if "(" in t else t)(g.node.get("type", {}).get("qualType", "")) == sig]
            else:
                # the declaration is in another dump: by the number of parameters, the non-const overload first
                cands = sorted([g for g in cands if len(g.params) == nargs], key=lambda g: g.node.get("type", {}).get("qualType", "").endswith(" const"))
            if len(cands) >= 1:
                return self.tr.use(cands[0].node["id"])
        return None

    def call_text(self, f, avs, t):
        if self.tr.cfg.get("vehicle") and self.tr.ret_rec(f) is not None:
            # a record returned by value: into a temporary of the caller's frame, whose address is the value
            rt = self.tr.ret_rec(f)
            off = self.slot(self.tr.size_of(rt))
            k = 1 if f.node["kind"] in ("CXXMethodDecl", "CXXConversionDecl") and not f.is_static else 0
            avs = list(avs[:k]) + ["(fp + %d)" % off] + list(avs[k:])
            self.emit(f.lean + "".join(" " + par(a) for a in avs))
            return "(fp + %d)" % off
        text = f.lean + "".join(" " + par(a) for a in avs)
        rt = t
        if rt.kind == "void":
            self.emit(text)
            return "()"
        return self.bind(text)

    def boundary_call(self, n, q, name, member, args, t):
        tr = self.tr
        # hal.<driver>->m(...)
        if member is not None:
            base = kids(member)[0]
            bt = tr.ty(base.get("type"))
            bname = bt.name if bt.kind in ("ptr", "rec", "ref") else ""
            bname = norm_rec(bname or "")
            if bname.startswith("AP_HAL::"):
                cls = bname
                m = member["name"]
                key = "%s::%s" % (cls, m)
                if key == "AP_HAL::Storage::read_block":
                    d = self.rv(args[0])
                    s = self.rv(args[1], T("int", 16, False))
                    c = self.rv(args[2], U64)
                    self.emit("PMem.halRead %s %s %s" % (par(d), par(s), par(c)))
                    return "()"
                if key == "AP_HAL::Storage::write_block":
                    d = self.rv(args[0], T("int", 16, False))
                    s = self.rv(args[1])
                    c = self.rv(args[2], U64)
                    self.emit("PMem.halWrite %s %s %s" % (par(d), par(s), par(c)))
                    return "()"
                if key in tr.cfg.get("hal_dispatch", {}):
                    # (Phase 5c, configuration `hal_dispatch`) a virtual HAL member whose objects in translated code are
                    # all of one translated class (print_vprintf's `s->write(c)` on Util.cpp's BufferPrinter): its final
                    # overrider, called on the object
                    dref0 = self.callee_decl(n)[0]
                    decl = tr.idx.get(dref0["id"]) or {}
                    ty = (decl.get("type") or {}).get("qualType") or (dref0.get("type") or {}).get("qualType") or ""
                    sig = ty[ty.index("("):] if "(" in ty else ty
                    f = tr.final_overrider(tr.cfg["hal_dispatch"][key], m, sig, len(args))
                    if f is None:
                        raise Reject("hal_dispatch: no overrider of %s in %s" % (key, tr.cfg["hal_dispatch"][key]))
                    bt0 = tr.ty(base.get("type"))
                    thisv = self.rv(base) if bt0.kind == "ptr" else self.addr_of(base)
                    return self.call_text(f, [thisv] + self.call_args(f, args), t)
                if key in tr.cfg.get("hal_translated", {}):
                    # a HAL member the reference's HAL inherits from AP_HAL (lockstep.cpp's Storage keeps AP_HAL::Storage::erase)
                    f = tr.fn_by_qname(tr.cfg["hal_translated"][key])
                    avs = self.call_args(f, args)
                    return self.call_text(f, ["(0 : UInt64)"] + avs, t)
                if "%s/%d" % (key, len(args)) in self.tr.boundary:
                    key = "%s/%d" % (key, len(args))       # (GCS configuration) an overload by its number of arguments
                if key in self.tr.boundary:
                    v = self.tr.boundary[key]
                    if "{" in v:
                        return self.boundary_text(v, args, base, t)
                    for a in args:
                        pass    # boundary arguments are not evaluated for effects (none have any)
                    return v if t.kind != "void" else "()"
                if tr.cfg.get("vehicle") and tr.cfg.get("hal_hook"):
                    # (vehicle configuration, `hal_hook`) a HAL member outside the configured boundary: a call of the
                    # HAL (`PMem.hal`, lockstep.cpp's semantics, implemented by the replay driver) with the object's
                    # address and the arguments as 64-bit words (floats as their bits, records by address)
                    tr.hal_calls.setdefault(key, []).append(self.site(n))
                    bt0 = tr.ty(base.get("type"))
                    thisv = par(self.rv(base) if bt0.kind == "ptr" else self.addr_of(base))
                    vals = []
                    # (Phase 5d) the callee's parameter types: a non-const lvalue reference parameter is passed as its
                    # address (`get_system_id_unformatted(uint8_t buf[], uint8_t &len)` passed len's value before)
                    try:
                        dref0 = self.callee_decl(n)[0]
                        decl = tr.idx.get(dref0["id"]) or {}
                        fty = (decl.get("type") or {}).get("qualType") or (dref0.get("type") or {}).get("qualType") or ""
                    except Exception:
                        fty = ""
                    pts = []
                    if "(" in fty:
                        inner, d, cur = fty[fty.index("(") + 1:], 0, ""
                        for ch in inner:
                            if ch in "(<[":
                                d += 1
                            elif ch in ")>]":
                                if d == 0:
                                    break
                                d -= 1
                            if ch == "," and d == 0:
                                pts.append(cur.strip())
                                cur = ""
                            else:
                                cur += ch
                        if cur.strip():
                            pts.append(cur.strip())
                    for ai, a in enumerate(args):
                        at = tr.ty(a.get("type"))
                        if a.get("kind") == "CXXDefaultArgExpr":
                            pass
                        pt = pts[ai] if ai < len(pts) else ""
                        # the parameter's declared type when the declaration is indexed; else clang's value category: a
                        # scalar argument that stays an lvalue (no lvalue-to-rvalue conversion) is bound to a reference
                        byref = (pt.endswith("&") and not pt.endswith("&&") and not pt.startswith("const ")) if pt else \
                            (a.get("valueCategory") == "lvalue")
                        if byref and at.kind not in ("rec", "arr"):
                            tr.hal_ref_params.add("%s/%d" % (key, ai))
                            vals.append(par(self.addr_of(a)))
                            continue
                        if at.kind in ("rec", "arr"):
                            if at.kind == "rec":
                                off = self.slot(tr.size_of(at))
                                self.init_mem("(fp + %d)" % off, at, a)
                                vals.append("(fp + %d)" % off)
                            else:
                                vals.append(par(self.addr_of(a)))
                        elif at.kind in ("ptr", "ref"):
                            vals.append(par(self.rv(a)))
                        elif at.kind == "float":
                            vals.append("(Binary32.toBits %s).toUInt64" % par(self.rv(a)))
                        elif at.kind == "double":
                            vals.append("(Binary64.toBits %s)" % par(self.rv(a)))
                        elif at.kind == "bool":
                            vals.append("(if %s then (1 : UInt64) else 0)" % par(self.rv(a)))
                        else:
                            vals.append(par(self.convert(self.rv(a), at, U64)))
                    text = "PMem.hal %s %s #[%s]" % (json.dumps(key), thisv, ", ".join(vals))
                    if t.kind == "void":
                        self.emit("discard <| " + text)
                        return "()"
                    r = self.bind(text)
                    if t.kind == "bool":
                        return "(%s != 0)" % r
                    if t.kind == "float":
                        return "(Binary32.ofBits %s.toUInt32)" % r
                    if t.kind == "double":
                        return "(Binary64.ofBits %s)" % r
                    if t.kind in ("ptr", "ref"):
                        return r
                    return self.convert(r, U64, t)
                if tr.cfg.get("vehicle"):
                    # (vehicle configuration) a HAL member outside the configured boundary: recorded, the default
                    tr.hal_calls.setdefault(key, []).append(self.site(n))
                    self.emit("PMem.halCall %s" % json.dumps(key))
                    return self.default_of(t)
                raise Reject("HAL call %s in %s" % (key, self.f.qual))
        lib = {"strlen": ("strlen", [PTR], U64), "strnlen": ("strnlen", [PTR, U64], U64),
               "strncpy": ("strncpy", [PTR, PTR, U64], PTR), "strcmp": ("strcmp", [PTR, PTR], I32),
               "strncmp": ("strncmp", [PTR, PTR, U64], I32), "strcasecmp": ("strcasecmp", [PTR, PTR], I32),
               "strncasecmp": ("strncasecmp", [PTR, PTR, U64], I32), "memcpy": ("memcpy", [PTR, PTR, U64], PTR),
               "memset": ("memset", [PTR, I32, U64], PTR), "memcmp": ("memcmp", [PTR, PTR, U64], I32),
               "__builtin_memcpy": ("memcpy", [PTR, PTR, U64], PTR), "__builtin_memset": ("memset", [PTR, I32, U64], PTR),
               "__builtin___memcpy_chk": ("memcpy", [PTR, PTR, U64], PTR), "__builtin___strncpy_chk": ("strncpy", [PTR, PTR, U64], PTR),
               "__builtin___memset_chk": ("memset", [PTR, I32, U64], PTR)}
        if member is None and tr.cfg.get("varargs") and name in ("__builtin_va_start", "__builtin_va_end", "__builtin_va_copy"):
            # (Phase 5c, `varargs`) `va_start(ap, last)`: ap is the address of the block (the hidden parameter);
            # `va_copy(d, s)`: d is s; `va_end(ap)`: nothing
            if name == "__builtin_va_start":
                if "va'" not in self.names:
                    raise Reject("va_start outside a variadic function")
                self.store(self.lvalue(args[0]), "va'")
            elif name == "__builtin_va_copy":
                v = self.bindv(self.load(self.lvalue(args[1])))
                self.store(self.lvalue(args[0]), v)
            return "()"
        if member is None and name in lib:
            fn, pts, rt = lib[name]
            avs = [self.rv(a, pt) for a, pt in zip(args, pts)]
            return self.bind("PMem.%s %s" % (fn, " ".join(par(v) for v in avs)))
        if member is None and name in ("fabsf", "__builtin_fabsf", "fabs", "__builtin_fabs"):
            at = tr.ty(args[0]["type"])
            return "(%s.abs %s)" % (t.lean, par(self.rv(args[0], t)))
        if member is None and name == "epsilon" and q in ("epsilon", "std::numeric_limits::epsilon"):
            # std::numeric_limits<T>::epsilon(): FLT_EPSILON / DBL_EPSILON
            return "(Binary32.ofBits 0x34000000)" if t.kind == "float" else "(Binary64.ofBits 0x3cb0000000000000)"
        if member is None and name in ("isnan", "__builtin_isnan", "isinf", "__builtin_isinf", "isfinite", "__builtin_isfinite"):
            at = tr.ty(args[0]["type"])
            if at.kind in ("int", "enum") and tr.cfg.get("vehicle"):
                return "true" if name.endswith("isfinite") else "false"     # libc++'s overloads for integers
            fn = {"isnan": "isNaN", "isinf": "isInf", "isfinite": "isFinite"}[name.replace("__builtin_", "")]
            return "(%s.%s %s)" % (at.lean, fn, par(self.rv(args[0], at)))
        if member is None and name in ("__builtin_nanf",):
            return "(Binary32.ofBits 0x7fc00000)"
        if member is None and tr.cfg.get("vehicle"):
            m = self.cmath_call(n, name, args)
            if m is not None:
                return m
        if member is None and name in ("printf", "__builtin_printf", "hal_printf"):
            return "()"
        if q in self.tr.boundary or name in self.tr.boundary:
            v = self.tr.boundary.get(q, self.tr.boundary.get(name))
            if "{" in v:
                return self.boundary_text(v, args, kids(member)[0] if member is not None else None, t)
            return v if t.kind != "void" else "()"
        return None


    def cmath_call(self, n, name, args):
        """(vehicle configuration) <cmath>: the functions IEEE 754 defines exactly as FloatLib operations, the others
        as the translation of musl's C sources (`Musl.f.f`, README.md "The C library"), by cpp2lean's table."""
        import cpp2lean as C
        c = kids(n)[0]
        while c.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
            c = kids(c)[0]
        ty = re.sub(r"\s*noexcept$", "", (c.get("type") or {}).get("qualType", ""))
        m = re.match(r"^(\w+(?: \w+)?) \(([^()]*)\)$", ty)
        if not m:
            return None
        cn = {"float": "float", "double": "double", "int": "int32_t", "bool": "bool"}
        ps = [x.strip() for x in m.group(2).split(",") if x.strip()]
        if any(x not in cn for x in ps) or m.group(1) not in cn:
            return None
        cmp = {"isgreater": ">", "isgreaterequal": "≥", "isless": "<", "islessequal": "≤"}.get(name.replace("__builtin_", ""))
        if cmp and len(args) == 2:
            at = self.tr.ty(args[0].get("type"))
            return "(decide (%s %s %s))" % (par(self.rv(args[0], at)), cmp, par(self.rv(args[1], at)))
        key = (name.replace("__builtin_", ""), tuple(cn[x] for x in ps), cn[m.group(1)])
        lf = C.CMATH.get(key)
        if lf is None or len(args) != len(ps):
            return None
        conv_double = isinstance(lf, tuple)
        if conv_double:
            lf = lf[0]
        tys = {"float": FLOAT, "double": DOUBLE, "int": I32, "bool": BOOL}
        avs = [self.rv(a, DOUBLE if conv_double else tys[p]) for a, p in zip(args, ps)]
        if lf.startswith(C.LIBM_NS + "."):
            self.tr.musl_imports.add(lf.rsplit(".", 1)[0])
        return "(%s %s)" % (lf, " ".join(par(v) for v in avs))

    def bound_method(self, n, dref):
        """(static construction) the member function a FUNCTOR_BIND_MEMBER(&T::m, ...) binds: from the specialization's
        template arguments if dumped, else from the macro's source text at the expansion."""
        tr = self.tr
        node = tr.idx.get(dref["id"]) or {}
        for a in kids(node):
            if a.get("kind") == "TemplateArgument" and (a.get("decl") or {}).get("kind") == "CXXMethodDecl":
                try:
                    return tr.use(a["decl"]["id"])
                except Reject:
                    pass
        def first_loc(x):
            r = (x.get("range") or {}).get("begin") or {}
            e = r.get("expansionLoc") or r
            if e.get("file") and e.get("line"):
                return e
            for c in kids(x):
                v = first_loc(c)
                if v:
                    return v
            return None
        loc = first_loc(n)
        if not loc:
            raise Reject("FUNCTOR_BIND_MEMBER: no location")
        path = loc["file"]
        if not os.path.isabs(path):
            path = os.path.join(str(tr.U.b.WAF), path)
        try:
            line = open(path, errors="replace").read().split("\n")[loc["line"] - 1][loc.get("col", 1) - 1:]
        except Exception:
            raise Reject("FUNCTOR_BIND_MEMBER: source of %s not readable" % path)
        m = re.match(r"\s*FUNCTOR_BIND_MEMBER\s*\(\s*&\s*([\w:]+)", line) or re.match(r"\s*FUNCTOR_BIND\s*\([^,]*,\s*&\s*([\w:]+)", line)
        q = m.group(1) if m else None
        if not m:
            # the scheduler's tables: SCHED_TASK_CLASS(classname, classptr, func, ...) (AP_Scheduler.h:46),
            # SCHED_TASK(func, ...) of AP_Vehicle.cpp (AP_Vehicle.cpp:33: SCHED_TASK_CLASS(AP_Vehicle, &vehicle, func, ...))
            m2 = re.match(r"\s*(?:SCHED|FAST)_TASK_CLASS\s*\(\s*(\w+)\s*,[^,]*,\s*(\w+)", line)
            m3 = re.match(r"\s*SCHED_TASK\s*\(\s*(\w+)", line)
            if m2:
                q = "%s::%s" % (m2.group(1), m2.group(2))
            elif m3 and path.endswith("AP_Vehicle.cpp"):
                q = "AP_Vehicle::%s" % m3.group(1)
            else:
                raise Reject("FUNCTOR_BIND_MEMBER: not recognized at %s:%s: %s" % (path, loc["line"], line[:80]))
        cands = [g for g in set(tr.fns.values()) if g.qname == q and not g.ctor]
        if not cands:
            try:
                tr.ensure_class("::".join(split_scope(q)[:-1]))
            except Reject:
                pass
            cands = [g for g in set(tr.fns.values()) if g.qname == q and not g.ctor]
        if not cands:
            raise Reject("FUNCTOR_BIND_MEMBER: no definition of %s" % q)
        return tr.use(sorted(cands, key=lambda g: g.node.get("type", {}).get("qualType", "").endswith(" const"))[0].node["id"])

    def boundary_text(self, v, args, base, t):
        """(GCS configuration) a boundary call whose Lean text names its arguments: `{0}`, `{1}`, ... the
        arguments' values (pointers and references as addresses), `{this}` the object's address."""
        vals = {"_": "(0 : UInt64)"}
        for i, a in enumerate(args):
            if "{%d}" % i in v:
                at = self.tr.ty(a.get("type"))
                vals[str(i)] = par(self.addr_of(a) if at.kind in ("rec", "arr") else self.rv(a))
        if "{this}" in v:
            if base is None:
                vals["this"] = "this"
            else:
                bt = self.tr.ty(base.get("type"))
                vals["this"] = par(self.rv(base) if bt.kind == "ptr" else self.addr_of(base))
        text = re.sub(r"\{(\w+)\}", lambda m: vals[m.group(1)], v)
        if t.kind == "void":
            self.emit(text)
            return "()"
        return self.bind(text)


def static_dynamic_init(tr):
    """(GCS configuration) `staticDynamicInit`: the dynamic initialization of the statics the code uses whose type is a
    record with default member initializers (`static struct LastRadioStatus { ...; uint8_t txbuf = 100; }
    last_radio_status;`: clang's IR has `zeroinitializer` and a global constructor), run by the harness's static
    construction."""
    class DummyFn:
        qual = qname = "static construction"
        node = {"range": {}, "loc": {}}
        params = []
        body = None
        ctor = False
        is_static = True
        lean = "staticDynamicInit"
    ft = FnTranslator(tr, DummyFn())
    ft.is_method = False
    ft.ret = VOID
    done = 0
    for q in sorted(list(tr.static_addr)):
        nodes = tr.static_nodes.get(q, [])
        if not nodes:
            continue
        t = tr.ty(nodes[0].get("type"))
        if t.kind != "rec":
            continue
        n0 = len(ft.lines)
        ft.default_member_inits("(PMem'static %s)" % json.dumps(q), t.name)
        done += len(ft.lines) > n0
    body = ft.lines or ["  pure ()"]
    out = ["/-- Dynamic initialization of statics with default member initializers (%d statics). -/" % done]
    if ft.frame:
        out.append("partial def staticDynamicInit : PMem.M Unit := do")
        out.append("  let fp ← PMem.enter %d" % ft.frame)
        out += body
        out.append("  PMem.leave fp")
    else:
        out.append("partial def staticDynamicInit : PMem.M Unit := do")
        out += body
    return "\n".join(out)


def ir_dynamic_inits(tr, u):
    """(static construction) the globals of unit u that its global constructor initializes, in the order
    `_GLOBAL__sub_I_<unit>` runs their `__cxx_global_var_init` functions (C++'s order within a unit): [IR symbol]."""
    cache = tr.__dict__.setdefault("_dyninit", {})
    if u in cache:
        return cache[u]
    m = tr.ir_mod(u)
    text = open(os.path.join(tr.U.cache, u.replace("/", "__") + ".ll")).read()
    bodies = {}
    for fm in re.finditer(r"^define [^\n]*?@(\"[^\"]+\"|[^\s(]+)\([^\n]*\{\n(.*?)^\}", text, re.M | re.S):
        bodies[fm.group(1).strip('"')] = fm.group(2)
    order = []
    subs = [k for k in bodies if k.startswith("_GLOBAL__sub_I_")]
    calls = []
    for k in subs:
        calls += re.findall(r"call void @(__cxx_global_var_init[\w.]*)\(", bodies[k])
    if not subs:
        calls = sorted((k for k in bodies if k.startswith("__cxx_global_var_init")), key=lambda x: int(x.split(".")[-1]) if "." in x else 0)
    data = set(k.lstrip("@") for k in m.raw)
    for c in calls:
        b = bodies.get(c, "")
        # the initialized global: the one stored to, else the object a constructor is called on, else the first
        # global named (not a string constant or a guard variable)
        cand = [g.strip('"') for g in re.findall(r"store [^\n]*?, ptr @(\"[^\"]+\"|[A-Za-z_$][\w.$]*)", b)]
        cand += [g.strip('"') for g in re.findall(r"call [^\n]*?C[12]E[^\n(]*\(ptr [^\n]*?@(\"[^\"]+\"|[A-Za-z_$][\w.$]*)", b)]
        cand += [g.strip('"') for g in re.findall(r"@(\"[^\"]+\"|[A-Za-z_$][\w.$]*)", b)]
        for g in cand:
            if g in data and not g.startswith("_ZGV") and not g.startswith(".") and g not in order:
                order.append(g)
                break
    cache[u] = order
    return order


def static_construct(tr):
    """(static construction, vehicle configuration) `staticConstruct`: the dynamic initialization of the statics the
    translation uses (clang's global constructors: `Copter copter;` with its members' constructors, AP_Param's
    `param_loader`, the `StorageAccess` statics, the `ObjectBuffer` statics, ...), each initializer translated from
    the static's declaration, in C++'s order: the units in the order of the reference executable's initializer
    list (`init_order`, from copter_ref's `__init_offsets`), within a unit the order of its global constructor.
    Statics of the estimator classes are constructed by the World; references are bound to their objects."""
    class DummyFn:
        qual = qname = "static construction"
        node = {"range": {}, "loc": {}}
        params = []
        body = None
        ctor = False
        is_static = True
        lean = "staticConstruct"
    ft = FnTranslator(tr, DummyFn())
    ft.is_method = False
    ft.ret = VOID
    unit_order = tr.cfg.get("init_order", [])
    def unit_rank(u):
        b = "__GLOBAL__sub_I_" + os.path.basename(u)
        idx = [i for i, x in enumerate(unit_order) if x == b]
        if not idx:
            return 10 ** 6
        return idx[0] if u.startswith("ArduCopter/") else idx[-1]
    todo = []
    skipped = []
    for q in sorted(list(tr.static_addr)):
        if "(...)::" in q or q in tr.cfg.get("zero_statics", {}):
            continue
        loc = tr.static_loc(q)
        if os.environ.get("CPP2LEAN_SC_DEBUG"):
            print("sc: %s -> %s %s" % (q, loc, ir_dynamic_inits(tr, loc[0])[:12] if loc else ""), file=sys.stderr)
        if not loc:
            continue
        u, sym = loc
        dyn = ir_dynamic_inits(tr, u)
        if sym.lstrip("@") not in dyn:
            continue
        todo.append((unit_rank(u), dyn.index(sym.lstrip("@")), q, u))
    todo.sort()
    L = []
    for rank, pos, q, u in todo:
        def init_nodes():
            ns = list(tr.static_nodes.get(q, []))
            for nd in list(ns):
                ns += tr.static_nodes.get(("def", nd.get("id")), [])
            return [n for n in ns if [x for x in kids(n) if "Comment" not in x.get("kind", "")]]
        nodes = init_nodes()
        if not nodes:
            # the definition: a dump of its unit filtered by the static's name
            try:
                tr.add_dump(u, split_scope(q)[-1])
            except Reject:
                pass
            nodes = init_nodes()
        try:
            t = tr.ty(tr.static_nodes[q][0].get("type")) if tr.static_nodes.get(q) else None
        except Reject:
            t = VOID
        if not nodes or t is None:
            skipped.append(q)
            ft.emit("-- %s (%s): its initializer is in no dump" % (q, u))
            continue
        ini = [x for x in kids(nodes[0]) if "Comment" not in x.get("kind", "")][0]
        qt = (nodes[0].get("type") or {}).get("qualType", "")
        if re.search(r"\[\d+\]$", qt):
            t = tr.ty(nodes[0].get("type"))
        if qt.endswith("[]"):
            # an array of unknown bound (`const AP_Scheduler::Task AP_Vehicle::scheduler_tasks[] = {...}`): its
            # initializer's elements
            ini0 = ini
            while ini0.get("kind") in ("ExprWithCleanups", "ConstantExpr"):
                ini0 = kids(ini0)[0]
            t = tr.ty({"qualType": "%s[%d]" % (qt[:-2].strip(), len(kids(ini0)))})
        if t.kind == "rec" and tr.is_bridge_class(t.name):
            ft.emit("-- %s (%s): constructed by the estimator World" % (q, u))
            continue
        ft.emit("-- %s (%s)" % (q, u))
        try:
            if t.kind == "ref":
                ft.emit("PMem.stU64 %s %s" % (ft.static_ref(q), par(ft.addr_of(ini))))
            else:
                ft.init_mem(ft.static_ref(q), t, ini)
        except Reject as e:
            skipped.append(q)
            ft.emit("-- %s: not constructed (%s)" % (q, str(e).replace("\n", " ")))
            print("static construction: %s: %s" % (q, e), file=sys.stderr)
    tr.static_construct_report = (todo, skipped)
    body = ft.lines or ["  pure ()"]
    out = ["/-- C++ static construction (%d statics, %d not constructed): the global constructors of the units in the "
           "reference executable's order. -/" % (len(todo), len(skipped))]
    out.append("partial def staticConstruct : PMem.M Unit := do")
    if ft.frame:
        out.append("  let fp ← PMem.enter %d" % ft.frame)
        out += body
        out.append("  PMem.leave fp")
    else:
        out += body
    return "\n".join(out)


def world_outputs_def(tr, wo):
    """(vehicle configuration, Phase 5b) `worldOutputs'drain`: the estimator World's output events (`Mem.eo`, appended
    by the bridge's adapters), each replayed on the memory as the call the World's translation made it of: configured as
    `constructor: [function, arguments...]`, an argument `{k}` the event's k-th field, `@f` the result of the translated
    function f (an accessor: `@gcs`, `@AP::mission`), any other text Lean; a constructor not configured is an output
    outside the vehicle's memory (AP_Notify's flags, the HAL's persistent data) and is dropped."""
    out = ["partial def worldOutputs'drain : PMem.M Unit := do",
           "  let os ← modifyGet fun m => (m.eo, { m with eo := #[] })",
           "  for o in os do",
           "    match o with"]
    text = any(isinstance(a, str) and (a.startswith("%text ") or a.startswith("%snprintf ") or a.startswith("%ctext ")) for c, sp in wo.items() if not c.startswith("_") for a in sp[1:]) or \
        any(not c.startswith("_") and sp[0].startswith("%textsink ") for c, sp in wo.items())
    ctext = any(isinstance(a, str) and (a.startswith("%ctext ") or a.startswith("%textsink ")) for c, sp in wo.items() if not c.startswith("_") for a in sp)
    if text:
        # (Phase 5c) an argument `%text {f} {a}`: a World text event's format (a String) and variadic arguments (tagged
        # 64-bit slots and strings, cpp2lean.py --text-log) in memory as the C++ caller has them: a block of 8-byte
        # slots (a string's slot the address of its bytes), the format's bytes and NUL, the strings' bytes and NULs, in a
        # frame of the drain's (`PMem.enter`, left after the call); two arguments, the format's address and the block's
        out = ["/-- (Phase 5c) a World text event's format and variadic arguments in memory (a frame: the block of 8-byte",
               "slots, the format's bytes and NUL, the string arguments' bytes and NULs): (frame, format, block). -/",
               "partial def worldOutputs'textBlock (fmt : String) (args : Array (Sum UInt64 String)) : PMem.M (UInt64 × UInt64 × UInt64) := do",
               "  let fb := fmt.toUTF8",
               "  let ss := args.foldl (fun n a => match a with | .inr s => n + s.toUTF8.size + 1 | .inl _ => n) 0",
               "  let fp ← PMem.enter (8 * args.size + fb.size + 1 + ss)",
               "  let mut p := fp + (8 * args.size).toUInt64",
               "  let f := p",
               "  for i in [0:fb.size] do",
               "    PMem.stU8 (p + i.toUInt64) (fb.get! i)",
               "  PMem.stU8 (p + fb.size.toUInt64) 0",
               "  p := p + (fb.size + 1).toUInt64",
               "  for k in [0:args.size] do",
               "    match args[k]! with",
               "    | .inl w => PMem.stU64 (fp + (8 * k).toUInt64) w",
               "    | .inr s =>",
               "      let b := s.toUTF8",
               "      for i in [0:b.size] do",
               "        PMem.stU8 (p + i.toUInt64) (b.get! i)",
               "      PMem.stU8 (p + b.size.toUInt64) 0",
               "      PMem.stU64 (fp + (8 * k).toUInt64) p",
               "      p := p + (b.size + 1).toUInt64",
               "  return (fp, f, fp)",
               ""] + out
    if ctext:
        # (Phase 5d, cpp2lean.py --text-buffers) a World text (`Estimator_lib.CText`: the formatted write that filled a
        # `char` buffer) written into the buffer at `bp` as the C++ wrote it: `fmt n g a` by the translated
        # AP_HAL::Util::snprintf on hal.util (`snprintf(bp, n, g, a...)`, the format and arguments in a text block);
        # `text n src a` the same with the format the text of the buffer src (formatted first into a zero-filled
        # buffer of the drain's frame of src's size); `none` nothing written (the caller's buffer as it was; as a
        # format, the zero-filled buffer: the empty string); `null` (a null `const char *` used as text, undefined in
        # C) is recorded as unreached and nothing is written
        util_off = next(fl["off"] for fl in tr.rec_layout("AP_HAL::HAL")["fields"] if fl["name"] == "util")
        tr.static_addr.setdefault("hal", None)
        g = tr.fn_by_qname("AP_HAL::Util::snprintf")
        ct = [
               "/-- (Phase 5d) the bytes a buffer holding a World text needs: the size of its last write (at least 1, a",
               "zero-filled byte: the empty string) -/",
               "partial def worldOutputs'ctextSize (t : Estimator_lib.CText) : UInt64 :=",
               "  match t with",
               "  | .fmt n _ _ => max n 1",
               "  | .text n _ _ => max n 1",
               "  | _ => 1",
               "",
               "/-- (Phase 5d) a World text (`Estimator_lib.CText`, cpp2lean.py --text-buffers) written into the buffer at `bp`",
               "with the translated AP_HAL::Util::snprintf, as the C++ wrote it (a format that is a text formatted first). -/",
               "partial def worldOutputs'ctext (bp : UInt64) (t : Estimator_lib.CText) : PMem.M Unit := do",
               "  match t with",
               "  | .none => pure ()",
               "  | .null => PMem.unreached \"cpp2lean::ctext_null\"",
               "  | .fmt n g a =>",
               "    let u ← PMem.ldU64 ((PMem'static \"hal\") + %d)  -- hal.util" % util_off,
               "    let (ip, f, iv) ← worldOutputs'textBlock g a",
               "    discard <| %s u bp n f iv" % g.lean,
               "    PMem.leave ip",
               "  | .text n src a =>",
               "    let sb ← PMem.enter (worldOutputs'ctextSize src).toNat",
               "    worldOutputs'ctext sb src",
               "    let u ← PMem.ldU64 ((PMem'static \"hal\") + %d)  -- hal.util" % util_off,
               "    let (ip, _, iv) ← worldOutputs'textBlock \"\" a",
               "    discard <| %s u bp n sb iv" % g.lean,
               "    PMem.leave ip",
               "    PMem.leave sb",
               "",
               ""]
        k0 = next(i for i, l in enumerate(out) if l.startswith("partial def worldOutputs'drain"))
        out = out[:k0] + ct + out[k0:]
    for ctor in sorted(wo):
        if ctor.startswith("_"):
            continue
        spec = wo[ctor]
        if spec[0].startswith("%console "):
            # (Phase 5c) a World console text (`Output.console_printf fmt args`, cpp2lean.py --text-log): the format and
            # the arguments laid out as for `%text`, then the HAL's console printf (`PMem.hal "<name>"`) with the format's
            # address and the 8-byte slots, as the vehicle's own console texts reach it
            out.append("    | .%s x0 x1 =>" % ctor)
            out.append("      let (fpc, fc, vac) ← worldOutputs'textBlock x0 x1")
            out.append("      let mut av : Array UInt64 := #[fc]")
            out.append("      for k in [0:x1.size] do")
            out.append("        av := av.push (← PMem.ldU64 (vac + (8 * k).toUInt64))")
            out.append("      discard <| PMem.hal %s 0 av" % json.dumps(spec[0][len("%console "):]))
            out.append("      PMem.leave fpc")
            continue
        if spec[0].startswith("%textsink "):
            # (Phase 5d) `%textsink {a} {t}`: the text a World function wrote to its `char *` parameter (cpp2lean.py
            # --text-buffers; the event the bridge's adapter pushes after the call, gen_bridge.py) formatted into the
            # caller's buffer at address a
            fa, ta = [re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), x) for x in spec[0].split()[1:3]]
            out.append("    | .%s x0 x1 =>" % ctor)
            out.append("      worldOutputs'ctext %s %s" % (fa, ta))
            continue
        if spec[0].startswith("%hal "):
            # (Phase 5c) an event for the harness: `PMem.hal "<name>" 0 #[args as 64-bit words]` (the World's lock-step
            # points `est_mark`, reference/hal/est_scheduler.cpp: the vehicle's part of the step runs there)
            nf = max([int(x) for a in spec[1:] for x in re.findall(r"\{(\d+)\}", a)] + [-1]) + 1
            out.append("    | .%s%s =>" % (ctor, "".join(" x%d" % i for i in range(nf))))
            out.append("      discard <| PMem.hal %s 0 #[%s]" % (json.dumps(spec[0][5:]), ", ".join(
                "(%s).toUInt64" % re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), a) for a in spec[1:])))
            continue
        f = tr.fn_by_qname(spec[0])
        nf = max([int(x) for a in spec[1:] for x in re.findall(r"\{(\d+)\}", a)] + [-1]) + 1
        vs = ["x%d" % i for i in range(nf)]
        pat = "    | .%s%s =>" % (ctor, "".join(" " + v for v in vs))
        body, args, after = [], [], []
        for k, a in enumerate(spec[1:]):
            if a.startswith("%text "):
                fa, va = [re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), x) for x in a.split()[1:3]]
                body.append("      let (fp%d, f%d, va%d) ← worldOutputs'textBlock %s %s" % (k, k, k, fa, va))
                args += ["f%d" % k, "va%d" % k]
                after.append("      PMem.leave fp%d" % k)
                continue
            if a.startswith("%ctext "):
                # (Phase 5d, cpp2lean.py --text-buffers) `%ctext {f} {t}`: the C++ caller's `char` buffer holding the World
                # text t, sent as `send_text(sev, f, buffer)`: a buffer of t's size in a frame of the drain's, the text
                # formatted into it (worldOutputs'ctext), then the format f and the variadic block `#[buffer]` (two
                # arguments, as for `%text`); the frames left after the call
                fa, ta = [re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), x) for x in a.split()[1:3]]
                body.append("      let bp%d ← PMem.enter (worldOutputs'ctextSize %s).toNat" % (k, ta))
                body.append("      worldOutputs'ctext bp%d %s" % (k, ta))
                body.append("      let (fp%d, f%d, va%d) ← worldOutputs'textBlock %s #[Sum.inl bp%d]" % (k, k, k, fa, k))
                args += ["f%d" % k, "va%d" % k]
                after.append("      PMem.leave bp%d" % k)
                after.append("      PMem.leave fp%d" % k)
                continue
            if a.startswith("%snprintf "):
                # (Phase 5c, cpp2lean.py --text-buffers) `%snprintf {f} {n} {g} {a}`: the C++ caller's `char buffer[n]` that
                # `hal.util->snprintf(buffer, n, g, a...)` filled, sent as `send_text(sev, f, buffer)`: a buffer of n bytes
                # in a frame of the drain's, formatted by the translated AP_HAL::Util::snprintf on hal.util (the inner
                # format and arguments in a text block, left after the call), then the format f and the variadic block
                # `#[buffer]` (two arguments, as for `%text`); the frames left after the call
                fa, sz, ifa, iva = [re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), x) for x in a.split()[1:5]]
                util_off = next(fl["off"] for fl in tr.rec_layout("AP_HAL::HAL")["fields"] if fl["name"] == "util")
                tr.static_addr.setdefault("hal", None)
                g = tr.fn_by_qname("AP_HAL::Util::snprintf")
                body.append("      let bp%d ← PMem.enter (%s).toNat" % (k, sz))
                body.append("      let u%d ← PMem.ldU64 ((PMem'static \"hal\") + %d)  -- hal.util" % (k, util_off))
                body.append("      let (ip%d, if%d, iv%d) ← worldOutputs'textBlock %s %s" % (k, k, k, ifa, iva))
                body.append("      discard <| %s u%d bp%d (%s) if%d iv%d" % (g.lean, k, k, sz, k, k))
                body.append("      PMem.leave ip%d" % k)
                body.append("      let (fp%d, f%d, va%d) ← worldOutputs'textBlock %s #[Sum.inl bp%d]" % (k, k, k, fa, k))
                args += ["f%d" % k, "va%d" % k]
                after.append("      PMem.leave bp%d" % k)
                after.append("      PMem.leave fp%d" % k)
                continue
            if a.startswith("@"):
                g = tr.fn_by_qname(a[1:])
                body.append("      let a%d ← %s" % (k, g.lean))
                args.append("a%d" % k)
            elif re.fullmatch(r"&\{\d+\}", a):
                # (Phase 5c) `&{j}`: the event's j-th field is a record (a `const T *` argument of the World's call,
                # cpp2lean.py --output-fn): its members stored at clang's layout of T (the callee's parameter) in a
                # temporary of the drain's frame, whose address is passed
                j = int(a[2:-1])
                pt = tr.ty(f.params[k]["type"])
                rt = tr.ty_str(pt.name) if pt.kind in ("ptr", "ref") and pt.name else None
                if rt is None or rt.kind != "rec":
                    raise Reject("world_outputs %s: argument %d of %s is not a pointer to a record" % (ctor, k, spec[0]))
                lay = tr.rec_layout(rt.name)
                body.append("      let a%d ← PMem.enter %d" % (k, lay["size"]))
                for fl in lay["fields"]:
                    ft = tr.ty_str(fl["type"])
                    if fl["base"] or fl["width"] is not None or not ft.scalar():
                        raise Reject("world_outputs %s: member %s of %s" % (ctor, fl["name"], rt.name))
                    body.append("      PMem.st%s (a%d + %d) x%d.%s" % (ft.suffix(), k, fl["off"], j, fl["name"]))
                args.append("a%d" % k)
                after.append("      PMem.leave a%d" % k)
            else:
                args.append("(%s)" % re.sub(r"\{(\d+)\}", lambda m: "x" + m.group(1), a))
        out.append(pat)
        out += body
        out.append("      %s%s" % (f.lean, "".join(" " + x for x in args)))
        out += reversed(after)
    out.append("    | _ => pure ()")
    return "\n".join(out)


def dispatchers(tr):
    """(vehicle configuration) the dispatchers of calls through function pointers (per function type, over the
    functions whose address is taken with it) and of virtual calls through `Mode *` (per member function, over the
    member objects of `copter`)."""
    out = []
    def lean_t(t):
        return "UInt64" if t.kind in ("rec", "ref", "ptr", "arr") else t.lean
    for sig, d in sorted(tr.fnptr_sigs.items(), key=lambda x: x[1].get("name", "~")):
        if "name" not in d:
            continue
        ret, ps = parse_fn_type(sig)
        rt = tr.ty_str(ret)
        names = ["a%d" % i for i in range(len(ps))]
        L = ["/-- Calls through a function pointer of type `%s`: the functions whose address the program takes with this "
             "type (%d). -/" % (sig, len(d["targets"])),
             "partial def %s (f : UInt64)%s : PMem.M %s := do" % (d["name"], "".join(" (%s : %s)" % (nm, lean_t(tr.ty_str(p))) for nm, p in zip(names, ps)), "Unit" if rt.kind == "void" else lean_t(rt))]
        first = True
        for a, g in sorted(d["targets"].items()):
            L.append("  %s f == 0x%x then  -- %s" % ("if" if first else "else if", a, g.qual))
            L.append("    %s%s" % (g.lean, "".join(" " + nm for nm in names)))
            first = False
        if ps and re.sub(r"\s+", "", ps[0]) == "void*":
            # (static construction) member functions bound by FUNCTOR_BIND_MEMBER: called on the bound object
            for a, g in sorted(getattr(tr, "bound_methods", {}).items()):
                grt = FnTranslator(tr, g).ret_type()
                if len(g.params) != len(ps) - 1 or (lean_t(grt) if grt.kind != "void" else "Unit") != ("Unit" if rt.kind == "void" else lean_t(rt)):
                    continue
                try:
                    if [lean_t(tr.ty(p["type"])) for p in g.params] != [lean_t(tr.ty_str(p)) for p in ps[1:]]:
                        continue
                except Reject:
                    continue
                L.append("  %s f == 0x%x then  -- %s (FUNCTOR_BIND_MEMBER)" % ("if" if first else "else if", a, g.qual))
                L.append("    %s%s" % (g.lean, "".join(" " + nm for nm in names)))
                first = False
        if not first:
            L.append("  else")
        ind = "    " if not first else "  "
        L.append(ind + "PMem.unreached %s" % json.dumps("function pointer " + sig))
        L.append(ind + ("return ()" if rt.kind == "void" else "return default"))
        out.append("\n".join(L))
    for (cls, name, sig), d in sorted(tr.vdispatch.items(), key=lambda x: x[1]["fn"].lean):
        dp = d["fn"]
        ft = FnTranslator(tr, dp)
        rt = ft.ret_type()
        ps = ["(this : UInt64)"] + (["(sret : UInt64)"] if rt.kind == "rec" else [])
        names = ["this"] + (["sret"] if rt.kind == "rec" else [])
        for i, p in enumerate(dp.params):
            ps.append("(p%d : %s)" % (i, lean_t(tr.ty(p["type"]))))
            names.append("p%d" % i)
        rl = "Unit" if rt.kind in ("void", "rec") else lean_t(rt)
        L = ["/-- Virtual calls of `%s%s` through a `%s *`: by the object's address, over the member objects of `%s` "
             "whose class derives from %s (%d), each arm the final overrider of its class. -/" % (dp.qual, sig, cls, d["obj"], cls, len(d["arms"])),
             "partial def %s %s : PMem.M %s := do" % (dp.lean, " ".join(ps), rl)]
        first = True
        for off, fcls, g in d["arms"]:
            L.append("  %s this == ((PMem'static %s) + %d) then  -- %s.%s" % ("if" if first else "else if", json.dumps(d["obj"]), off, d["obj"], fcls))
            L.append("    %s%s" % (g.lean, "".join(" " + nm for nm in names)))
            first = False
        if not first:
            L.append("  else")
        ind = "    " if not first else "  "
        L.append(ind + "PMem.unreached %s" % json.dumps("virtual %s on an object outside %s" % (dp.qual, d["obj"])))
        L.append(ind + ("return ()" if rl == "Unit" else "return default"))
        out.append("\n".join(L))
    return out


def always_returns(n):
    k = n.get("kind")
    if k == "ReturnStmt":
        return True
    if k == "CompoundStmt":
        return bool(kids(n)) and always_returns(kids(n)[-1])
    if k == "IfStmt":
        ks = kids(n)
        return len(ks) > 2 and always_returns(ks[1]) and always_returns(ks[2])
    if k == "SwitchStmt":
        body = kids(kids(n)[1]) if kids(n)[1].get("kind") == "CompoundStmt" else [kids(n)[1]]
        has_default, ok = False, True
        for s in body:
            cur = s
            while cur.get("kind") in ("CaseStmt", "DefaultStmt"):
                has_default |= cur["kind"] == "DefaultStmt"
                cur = kids(cur)[-1]
            if cur.get("kind") == "BreakStmt":
                ok = False
        return has_default and ok and bool(body) and always_returns(body[-1] if body[-1].get("kind") not in ("CaseStmt", "DefaultStmt") else _case_last(body[-1]))
    return False


def _case_last(n):
    while n.get("kind") in ("CaseStmt", "DefaultStmt"):
        n = kids(n)[-1]
    return n


def decode_c_string(v):
    """A clang JSON string literal's value (C escapes in double quotes) -> bytes."""
    s = v[1:-1]
    out, i = bytearray(), 0
    esc = {"n": 10, "t": 9, "r": 13, "0": 0, "\\": 92, "\"": 34, "'": 39, "a": 7, "b": 8, "f": 12, "v": 11}
    while i < len(s):
        c = s[i]
        if c == "\\":
            d = s[i + 1]
            if d == "x":
                j = i + 2
                while j < len(s) and s[j] in "0123456789abcdefABCDEF":
                    j += 1
                out.append(int(s[i + 2:j], 16) & 255)
                i = j
                continue
            if d in "01234567":
                j = i + 1
                while j < len(s) and j < i + 4 and s[j] in "01234567":
                    j += 1
                out.append(int(s[i + 1:j], 8) & 255)
                i = j
                continue
            out.append(esc[d])
            i += 2
            continue
        out += c.encode()
        i += 1
    return bytes(out)


# ---------------------------------------------------------------------------------------------
# The memory image: constant data and statics at fixed addresses.

def macho_section(path, segname, sectname):
    """The bytes of one section of a 64-bit Mach-O file (the reference binary's `__TEXT,__cstring`)."""
    import struct
    d = open(path, "rb").read()
    magic, _, _, _, ncmds, _, _, _ = struct.unpack_from("<IiiIIIII", d, 0)
    if magic != 0xfeedfacf:
        raise Reject("string_pool: %s is not a 64-bit Mach-O file" % path)
    off = 32
    for _ in range(ncmds):
        cmd, size = struct.unpack_from("<II", d, off)
        if cmd == 0x19:   # LC_SEGMENT_64
            nsects = struct.unpack_from("<I", d, off + 64)[0]
            for k in range(nsects):
                so = off + 72 + 80 * k
                sn = d[so:so + 16].rstrip(b"\0").decode()
                gn = d[so + 16:so + 32].rstrip(b"\0").decode()
                if sn == sectname and gn == segname:
                    _, sz, fo = struct.unpack_from("<QQI", d, so + 32)
                    return d[fo:fo + sz]
        off += size
    raise Reject("string_pool: no section %s,%s in %s" % (segname, sectname, path))


class Image:
    BASE = 0x1000

    def __init__(self, units):
        self.U = units
        self.mods = {}
        self.segs = []          # [name, addr, size, bytes, relocs (off, sym, add) , unit, kind]
        self.addr = {}          # (unit, sym) or ("global", sym) -> address
        self.by_name = {}       # demangled / qualified name -> address
        self.next = self.BASE
        self.demangled = {}

    def mod(self, unit):
        if unit not in self.mods:
            self.mods[unit] = self.U.ir(unit)
        return self.mods[unit]

    def demangle(self, syms):
        todo = [s for s in syms if s not in self.demangled]
        if todo:
            out = subprocess.run(["c++filt"], input="\n".join("_" + s.lstrip("@").strip('"') for s in todo),
                                 capture_output=True, text=True).stdout.split("\n")
            for s, d in zip(todo, out):
                d = d.strip()
                self.demangled[s] = s.lstrip("@").strip('"') if d == "_" + s.lstrip("@").strip('"') else d
        return [self.demangled[s] for s in syms]

    def alloc(self, size, align):
        a = max(align, 8)
        self.next = (self.next + a - 1) // a * a
        r = self.next
        self.next += max(size, 1)
        return r

    def place(self, unit, sym, kind, size=None, data=None, relocs=(), name=None):
        key = (unit, sym) if sym.startswith("@.") or kind == "local" else ("global", sym)
        if key in self.addr:
            return self.addr[key]
        g = self.mod(unit).get(sym) if unit else None
        if size is None:
            size, align = g["size"], g["align"]
        else:
            align = 8
        a = self.alloc(size, align)
        self.addr[key] = a
        seg = {"name": name or sym, "addr": a, "size": size, "bytes": bytearray(size) if data is None else bytearray(data),
               "relocs": list(relocs), "unit": unit, "kind": kind}
        self.segs.append(seg)
        if name:
            self.by_name[name] = a
        return a

    def resolve(self):
        for s in self.segs:
            for off, sym, add in s["relocs"]:
                key = (s["unit"], sym) if sym.startswith("@.") else ("global", sym)
                if key not in self.addr and hasattr(self, "fn_syms") and (sym in self.fn_syms or s["unit"] is None or sym not in self.mod(s["unit"]).raw):
                    # (vehicle configuration) a function's address (0: a function the translation does not have)
                    v = self.fn_syms.get(sym, 0) + (add if sym in self.fn_syms else 0)
                    s["bytes"][off:off + 8] = v.to_bytes(8, "little")
                    continue
                if key not in self.addr:
                    raise Reject("unresolved relocation to %s in %s" % (sym, s["name"]))
                v = self.addr[key] + add
                s["bytes"][off:off + 8] = v.to_bytes(8, "little")


def build_image(tr, units, cfg):
    img = Image(units)
    if cfg.get("vehicle"):
        img.fn_syms = {"@" + mg[1:]: a for mg, a in tr.fn_addrs.items() if mg.startswith("__Z")}
    # the tables: the closure of the root table (every group table reachable through group_info pointers)
    root_unit, root_sym = cfg["root_table"]
    texts = {}
    srcs = units.srcs

    def find_unit(sym, qual):
        parts = qual.split("::")
        pat = re.compile(r"\b" + re.escape(parts[-2]) + r"::" + re.escape(parts[-1]) + r"\s*\[\s*\]\s*[={]")
        cands = []
        for r in srcs:
            if r not in texts:
                with open(srcs[r], errors="replace") as fh:
                    texts[r] = fh.read()
            if pat.search(texts[r]):
                cands.append(r)
        import glob
        for h in sorted(glob.glob(os.path.join(str(units.b.AP), "libraries", "*", "*.h"))):
            with open(h, errors="replace") as fh:
                if pat.search(fh.read()):
                    base = os.path.basename(h)
                    cands += [r for r in srcs if base in texts.get(r, "")]
        for r in cands:
            g = img.mod(r).get(sym)
            if g and g["defined"]:
                return r
        return None

    tables = {}
    todo = [(root_unit, root_sym)] + [tuple(x) for x in cfg.get("extra_tables", [])]
    objects = {}
    while todo:
        unit, sym = todo.pop(0)
        if sym in tables:
            continue
        g = img.mod(unit).get(sym)
        tables[sym] = unit
        for off, s, add in g["relocs"]:
            if s.startswith("@."):
                continue
            gg = img.mod(unit).get(s)
            d = img.demangle([s])[0]
            is_table = "var_info" in d and not (gg is not None and gg["defined"] and not gg["const"])
            if is_table:
                if gg is not None and gg["defined"] and gg["const"]:
                    todo.append((unit, s))
                    continue
                u = find_unit(s, d)
                if u is None:
                    objects[s] = (unit, d)      # a mutable array of table pointers (GCS::_chan_var_info): an object
                    continue
                if img.mod(u).get(s)["const"]:
                    todo.append((u, s))
                else:
                    objects[s] = (u, d)
            else:
                objects[s] = (unit, d)
    # place the tables (in discovery order: the root first) and their strings
    for sym, unit in tables.items():
        g = img.mod(unit).get(sym)
        img.place(unit, sym, "table", size=g["size"], data=g["bytes"], relocs=g["relocs"], name=img.demangle([sym])[0])
        for off, s, add in g["relocs"]:
            if s.startswith("@."):
                gs = img.mod(unit).get(s)
                img.place(unit, s, "string", size=gs["size"], data=gs["bytes"], relocs=gs["relocs"])
    # the objects the tables point into (zero: their contents are set by constructors and AP_Param)
    for sym, (unit, d) in sorted(objects.items(), key=lambda x: x[1][1]):
        g = img.mod(unit).get(sym)
        img.place(unit, sym, "object", size=g["size"], name=d)
    # the statics the translated code names (AP_Param's static members, StorageManager's layout, ...),
    # with their constant initial values from the IR of their units
    static_units = cfg["static_units"]
    names_by_unit = {}
    for u in static_units:
        m = img.mod(u)
        syms = [s for s in m.raw if not s.startswith("@.") and not s.startswith('@"')]
        for s, d in zip(syms, img.demangle(syms)):
            if cfg.get("dynamic") and d in names_by_unit:
                # (GCS configuration) the unit that defines it (an `extern` declaration elsewhere)
                u0, s0 = names_by_unit[d]
                ext = lambda r: bool(re.match(r"^(?:\w+ )*(external|extern_weak) ", r or ""))
                if ext(img.mod(u0).raw.get(s0)) and not ext(m.raw.get(s)):
                    names_by_unit[d] = (u, s)
                continue
            names_by_unit.setdefault(d, (u, s))
    for q in list(tr.static_addr):
        if q in img.by_name:
            continue
        if q in getattr(tr, "static_syms", {}):
            # (Phase 5b) a discriminated static local: its own symbol in its function's unit
            sym, su = tr.static_syms[q]
            cands = [su] + [g.node.get("_unit") for g in tr.order if g.qname == q.split("(...)::")[0] and g.node.get("_unit")]
            for u in cands:
                if u and img.mod(u).get(sym) and img.mod(u).get(sym)["defined"]:
                    names_by_unit[q] = (u, sym)
                    break
        if q not in names_by_unit and q.endswith(")") is False and "(...)::" in q:
            fq, nm = q.split("(...)::")
            c = [d for d in names_by_unit if (d.startswith(fq + "(") and re.search(r"\)( const)?::" + re.escape(nm) + "$", d)) or d == fq + "::" + nm]
            if len(c) == 1:
                names_by_unit[q] = names_by_unit[c[0]]
        if q in cfg.get("zero_statics", {}):
            # (GCS configuration) a static whose definition is outside the units (the HAL's `hal`): zero bytes
            img.place(None, "zero:" + q, "static", size=cfg["zero_statics"][q], name=q)
            continue
        if q in names_by_unit and cfg.get("vehicle"):
            g0 = img.mod(names_by_unit[q][0]).get(names_by_unit[q][1])
            if g0 is None or not g0["defined"]:
                del names_by_unit[q]        # an extern declaration: the defining unit below
        if q not in names_by_unit and cfg.get("vehicle"):
            # (vehicle configuration) the unit whose object defines it (the symbol index)
            want, us = q, tr.sym_index()["data"].get(q, [])
            if not us and "::" not in q and "(" not in q:
                # a static member named without its class (declared in a dump of its users only): unique by its name
                c = [k for k in tr.sym_index()["data"] if k.endswith("::" + q) and "(" not in k and not k.startswith("_")]
                if len(c) == 1:
                    want, us = c[0], tr.sym_index()["data"][c[0]]
            if "(...)::" in q and not us:
                fq, nm = q.split("(...)::")
                for key, us2 in tr.sym_index()["data"].items():
                    if key.startswith(fq + "(") and re.search(r"\)( const)?::" + re.escape(nm) + "$", key):
                        want, us = key, us2
                        break
            if "(...)::" in q:
                fq, nm = q.split("(...)::")
                us = list(us) + [g.node.get("_unit") for g in tr.order if g.qname == fq and g.node.get("_unit")]
            for u in us:
                m = img.mod(u)
                syms = [s for s in m.raw if not s.startswith("@.") and not s.startswith('@"')]
                for s, d in zip(syms, img.demangle(syms)):
                    if "(...)::" in q and d.startswith(q.split("(...)::")[0] + "(") and re.search(r"\)( const)?::" + re.escape(q.split("(...)::")[1]) + "$", d):
                        want = d
                    if d == want and m.get(s) and m.get(s)["defined"]:
                        names_by_unit[q] = (u, s)
                if q in names_by_unit:
                    break
        if q not in names_by_unit and cfg.get("vehicle"):
            # (vehicle configuration) not found: zero bytes, listed in the survey
            tr.vehicle_log.append("static %s: no definition found (256 zero bytes)" % q)
            img.place(None, "zero:" + q, "static", size=256, name=q)
            continue
        if q not in names_by_unit:
            raise Reject("static %s: no definition in the static units" % q)
        u, s = names_by_unit[q]
        _place_rec(img, u, s, q)
        if cfg.get("vehicle") and q not in img.by_name:
            img.by_name[q] = img.addr[("global", s)]     # placed earlier under its qualified name
    img.resolve()
    return img, tables, objects


def _place_rec(img, u, s, name=None):
    g = img.mod(u).get(s)
    if g is None or not g["defined"]:
        raise Reject("static %s is not defined in %s" % (s, u))
    a = img.place(u, s, "static", size=g["size"], data=g["bytes"], relocs=g["relocs"], name=name or img.demangle([s])[0])
    for off, t, add in g["relocs"]:
        key = (u, t) if t.startswith("@.") else ("global", t)
        if key not in img.addr and hasattr(img, "fn_syms") and (t in img.fn_syms or t not in img.mod(u).raw):
            continue        # (vehicle configuration) a function
        if key not in img.addr:
            _place_rec(img, u, t)
    return a


# ---------------------------------------------------------------------------------------------
# Output.

def describe_table(img, seg, recs):
    """A readable listing of a GroupInfo/Info table: its entries as the code reads them."""
    b = seg["bytes"]
    n = len(b) // 32
    rows = []
    rev = {s["addr"]: s for s in img.segs}
    is_info = seg["name"].endswith("Copter::var_info")

    def cstr(a):
        s = next((x for x in img.segs if x["addr"] <= a < x["addr"] + x["size"]), None)
        if s is None:
            return "?"
        raw = bytes(s["bytes"][a - s["addr"]:])
        return raw.split(b"\0")[0].decode(errors="replace")

    def sym(a):
        s = next((x for x in img.segs if x["addr"] <= a < x["addr"] + max(x["size"], 1)), None)
        if s is None:
            return "0x%x" % a if a else "null"
        return "%s%s" % (s["name"], "+%d" % (a - s["addr"]) if a != s["addr"] else "")
    for i in range(n):
        e = b[32 * i:32 * i + 32]
        name = int.from_bytes(e[0:8], "little")
        off = int.from_bytes(e[8:16], "little", signed=not is_info)
        un = int.from_bytes(e[16:24], "little")
        flags = int.from_bytes(e[24:26], "little")
        if is_info:
            key = int.from_bytes(e[26:28], "little")
            typ = e[28]
        else:
            key = e[26]
            typ = e[27]
        if typ == 6:
            u = "group_info_ptr=" + sym(un) if flags & 16 else "group_info=" + sym(un)
        elif flags & 128:
            u = "def_value_offset=%d" % int.from_bytes(e[16:24], "little", signed=True)
        else:
            import struct
            u = "def_value=%r" % struct.unpack("<f", bytes(e[16:20]))[0]
        rows.append("{%s, %s, %s, flags=%d, %s=%d, type=%d}" % (json.dumps(cstr(name)), sym(off) if is_info else off, u, flags,
                                                                 "key" if is_info else "idx", key, typ))
    return rows


def write_vehicle_reports(tr, cfg, out, ns, root):
    """(vehicle configuration) the bridge's API (`bridge_list`: every estimator function the translated vehicle calls,
    with its signature and call sites; the estimator data members it reads or writes), the HAL calls outside the
    boundary, and the survey (every function emitted as a stub, with the rejection)."""
    def sites(lst):
        c = {}
        for x in lst:
            c[x] = c.get(x, 0) + 1
        return ", ".join("%s%s" % (k, " x%d" % v if v > 1 else "") for k, v in sorted(c.items()))
    L = ["# Generated by cpp2lean --param-memory %s (vehicle configuration). Do not edit." % cfg.get("_config_path", ""),
         "# The estimator functions the translated vehicle calls (the bridge's API): qualified name <TAB> signature <TAB>",
         "# number of call sites <TAB> call sites (calling function (file:line)). Most called first.",
         "# %d functions, %d call sites; then the estimator data members accessed directly (%d)." % (
             len(tr.bridge_calls), sum(len(e["sites"]) for e in tr.bridge_calls.values()), len(tr.bridge_fields))]
    for q, e in tr.bridge_calls.items():
        if e["sig"] == "?":
            # the declaration: from a dump of its class (for this list only)
            comps = split_scope(q)
            try:
                if len(comps) >= 2:
                    tr.ensure_class("::".join(comps[:-1]))
                else:
                    tr.add_dump(tr.sym_index()["fn"].get("AP::" + q, [None])[0] or "", "AP::" + q) if tr.sym_index()["fn"].get("AP::" + q) else None
            except Reject:
                pass
            ds = tr.decls.get(q, []) or tr.decls.get("AP::" + q, [])
            sigs = sorted(set((d.get("type") or {}).get("qualType", "?") for d in ds if d.get("kind") != "CXXRecordDecl"))
            e["sig"] = " | ".join(sigs) if sigs else "?"
    for q, e in sorted(tr.bridge_calls.items(), key=lambda x: (-len(x[1]["sites"]), x[0])):
        L.append("%s\t%s\t%d\t%s" % (q, e["sig"], len(e["sites"]), sites(e["sites"])))
    L.append("")
    L.append("# data members of estimator classes read or written by translated code (the bridge must provide them too)")
    for q, st in sorted(tr.bridge_fields.items(), key=lambda x: (-len(x[1]), x[0])):
        L.append("%s\t(field)\t%d\t%s" % (q, len(st), sites(st)))
    path = os.path.join(root, cfg.get("bridge_list", "ardupilot/vehicle/bridge_calls.txt"))
    with open(path, "w") as fh:
        fh.write("\n".join(L) + "\n")
    H = ["# HAL members called outside the configured boundary (PMem.halCall): name <TAB> call sites"]
    for q, st in sorted(tr.hal_calls.items()):
        H.append("%s\t%d\t%s" % (q, len(st), sites(st)))
    if tr.hal_ref_params:
        H.append("# reference parameters passed by address (name/index): " + ", ".join(sorted(tr.hal_ref_params)))
    with open(os.path.join(out, ns + ".hal_calls.txt"), "w") as fh:
        fh.write("\n".join(H) + "\n")
    S = ["# functions reached and translated: %d; emitted as stubs (rejected): %d" % (len(tr.order) - len(tr.rejected), len(tr.rejected))]
    for q, loc, r in tr.rejected:
        S.append("%s\t%s\t%s" % (q, loc, r))
    with open(os.path.join(out, ns + ".survey.txt"), "w") as fh:
        fh.write("\n".join(S) + "\n")
    with open(os.path.join(out, ns + ".dumps.txt"), "w") as fh:
        fh.write("\n".join(tr.vehicle_log) + "\n")


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="cpp2lean.py --param-memory")
    ap.add_argument("config")
    ap.add_argument("-o", dest="out", required=True)
    ap.add_argument("--namespace", default="AP_Param_lib")
    a = ap.parse_args(argv)
    with open(a.config) as f:
        cfg = json.load(f)
    if cfg.get("vehicle"):
        cfg["_config_path"] = os.path.relpath(os.path.abspath(a.config), HERE)
    root = HERE
    units = Units(root, os.path.join(root, "build", "param-memory-cache"))
    tr = Translator(cfg, units)
    defs = tr.translate_all(cfg["entries"])
    if cfg.get("static_construction"):
        # the constructors the static construction reaches, translated like the entries' callees (to a fixpoint:
        # a constructor can name further statics)
        sc = None
        for _ in range(4):
            n0 = len(tr.order)
            s0 = len(tr.static_addr)
            sc = static_construct(tr)
            i = n0
            while True:
                tr._translate_from(i, defs)
                i = len(tr.order)
                if not tr.static_fn_closure():
                    break
                tr._translate_from(i, defs)
                i = len(tr.order)
            if len(tr.order) == n0 and len(tr.static_addr) == s0:
                break
        defs.append(sc)
    if cfg.get("dynamic"):
        defs.append(static_dynamic_init(tr))
    if cfg.get("vehicle"):
        defs += dispatchers(tr)
    if cfg.get("world_outputs"):
        defs.append(world_outputs_def(tr, cfg["world_outputs"]))
    # string literals of the code: constant data too
    img, tables, objects = build_image(tr, units, cfg)
    pool = None
    if cfg.get("string_pool"):
        # (Phase 5d, key `string_pool`) the C string literals at the reference binary's layout: the linker's merged
        # `__TEXT,__cstring` section of the reference build is placed whole as constant data, and every literal of the
        # code that is a whole string of it (at the section's start or after a NUL) takes its address there. A read past
        # a literal's end (C undefined behavior, but compiled code reads the linker's neighbors: GCS_MAVLINK_Copter's
        # `mavlink_msg_available_modes_send(..., name)` copies 50 bytes from mode names of 4 to 17) then reads the
        # reference's bytes. Literals the section does not have are placed as before.
        pool = macho_section(os.path.join(HERE, cfg["string_pool"]["binary"]), "__TEXT", cfg["string_pool"].get("section", "__cstring"))
        pool_addr = img.place(None, "cstring_pool", "local", size=len(pool), data=pool, name=None)
    for bs in tr.literals:
        if pool is not None:
            i = pool.find(bs)
            while i > 0 and pool[i - 1] != 0:
                i = pool.find(bs, i + 1)
            if i >= 0:
                tr.literals[bs] = pool_addr + i
                continue
        a2 = img.place(None, "lit:" + bs.hex(), "local", size=len(bs), data=bs, name=None)
        tr.literals[bs] = a2
    for q in tr.static_addr:
        tr.static_addr[q] = img.by_name[q]
    img.resolve()
    heap = (img.next + 0xffff) // 0x10000 * 0x10000
    stack = heap + cfg.get("heap_size", 0x10000)
    size = stack + cfg.get("stack_size", 0x10000)

    def subst(text):
        text = re.sub(r'\(PMem\'static "([^"]*)"\)', lambda m: "(0x%x : UInt64) /- &%s -/" % (tr.static_addr[m.group(1)], m.group(1)), text)
        text = re.sub(r'\(PMem\'lit "([0-9a-f]*)"\)', lambda m: "(0x%x : UInt64) /- %s -/" % (
            tr.literals[bytes.fromhex(m.group(1))], json.dumps(bytes.fromhex(m.group(1))[:-1].decode(errors="replace")).replace("-/", "- /")), text)
        return text
    defs = [subst(d) for d in defs]
    os.makedirs(a.out, exist_ok=True)
    ns = a.namespace
    L = []
    L.append("import CFloat\nimport %s\n" % cfg.get("memory_module", "ParamMemory") + "".join("import %s\n" % m for m in cfg.get("imports", [])) +
             ("import %s\n" % cfg["bridge_module"] if cfg.get("bridge_module") else "") +
             "".join("import %s\n" % m for m in sorted(tr.musl_imports)))
    L.append("/-!\nGenerated by cpp2lean (`--param-memory %s`). Do not edit.\n" % os.path.relpath(a.config, root))
    L.append("ArduPilot's AP_Param over one byte memory (README.md, \"Phase 4: AP_Param\"): every function below is "
             "translated from clang's AST of its unit (the reference build's flags); the constant data (the `var_info` "
             "tables, their strings, the statics' initial values) is clang's evaluation of ArduPilot's initializers, "
             "placed at the addresses of `image`. Pointers, references and `ptrdiff_t` are addresses (`UInt64`).\n-/\n")
    L.append("open FloatLib.Floats (Binary32 Binary64)\n\nset_option linter.unusedVariables false\nset_option linter.unreachableTactic false\n%s\nnamespace %s\n" % ("".join("set_option %s\n" % o for o in cfg.get("lean_options", [])), ns))
    L.append("/-- The end of the constant data and statics; the heap and the stack follow. -/")
    L.append("def heapBase : Nat := 0x%x\ndef stackBase : Nat := 0x%x\ndef memSize : Nat := 0x%x\n" % (heap, stack, size))
    L.append("/-! The address of each static object and table (the address map; also `%s.addresses.json`). -/\n" % ns)
    amap = []
    for s in img.segs:
        if s["kind"] in ("table", "object", "static"):
            amap.append({"name": s["name"], "addr": s["addr"], "size": s["size"], "kind": s["kind"],
                         "unit": s["unit"], "symbol": next((k[1] for k, v in img.addr.items() if v == s["addr"] and k[0] == "global"), None)})
            if s["kind"] == "table":
                amap[-1]["bytes"] = s["bytes"].hex()
    seen_addr_names = set()
    for e in amap:
        an = re.sub(r"[^A-Za-z0-9_]", "_", e["name"])
        if cfg.get("vehicle") and an in seen_addr_names:
            an = "%s_%x" % (an, e["addr"])     # (vehicle configuration) the same local name in several units
        seen_addr_names.add(an)
        L.append("/-- `%s` (%s, %d bytes) -/\ndef addr'%s : UInt64 := 0x%x" % (e["name"], e["kind"], e["size"],
                                                                         an, e["addr"]))
    L.append("")
    L.append("/-- The constant data: each table, string and static at its address, as its bytes (hex). -/")
    L.append("def image : Array (UInt64 × String) := #[")
    rows = []
    for s in img.segs:
        if s["kind"] == "object" or not any(s["bytes"]):
            continue
        doc = ""
        if s["kind"] == "table":
            doc = "\n    /- %s (%s):\n       %s -/\n    " % (s["name"], s["unit"], "\n       ".join(r.replace("-/", "- /") for r in describe_table(img, s, tr.layouts)))
        rows.append("%s(0x%x, \"%s\")" % (doc, s["addr"], s["bytes"].hex()))
    L.append("  " + ",\n  ".join(rows))
    L.append("]\n")
    L.append("/-- A fresh memory with the constant data placed, over the HAL storage `st`. -/")
    L.append("def initMem (st : ByteArray) : PMem.Mem := Id.run do\n  let s0 := PMem.fresh memSize stackBase heapBase st\n"
             "  let ((), s) := (do for (a, h) in image do PMem.place a h : PMem.M Unit).run s0\n  return s\n")
    L.append("mutual\n")
    L.append("\n\n".join(defs))
    L.append("\nend\n\nend %s\n" % ns)
    with open(os.path.join(a.out, ns + ".lean"), "w") as f:
        f.write("\n".join(L))
    with open(os.path.join(a.out, ns + ".addresses.json"), "w") as f:
        json.dump({"heapBase": heap, "stackBase": stack, "memSize": size, "objects": amap,
                   "functions": [{"cxx": fn.qual, "lean": ns + "." + fn.lean, "loc": FnTranslator(tr, fn).loc()} for fn in tr.order]},
                  f, indent=1)
    import shutil
    for sup in ("CFloat.lean", cfg.get("memory_module", "ParamMemory") + ".lean") + tuple(m + ".lean" for m in cfg.get("imports", [])):
        shutil.copy(os.path.join(root, "support", sup), os.path.join(a.out, sup))
    if cfg.get("vehicle"):
        write_vehicle_reports(tr, cfg, a.out, ns, root)
    if cfg.get("bridge_module"):
        # (bridge) the adapters' signatures, for ardupilot/vehicle/gen_bridge.py
        with open(os.path.join(a.out, ns + ".bridge.json"), "w") as f:
            json.dump(sorted(tr.bridge_adapters.values(), key=lambda d: d["adapter"]), f, indent=1)
        with open(os.path.join(a.out, ns + ".bridge_fields.json"), "w") as f:
            json.dump(sorted(tr.bridge_field_adapters.values(), key=lambda d: d["adapter"]), f, indent=1)
    print("cpp2lean --param-memory: %d functions, %d tables, %d objects, %d statics; memory %d bytes" % (
        len(tr.order), len(tables), len(objects), sum(1 for s in img.segs if s["kind"] == "static"), size))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
