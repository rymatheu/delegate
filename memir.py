"""Constant data of a translation unit as clang evaluated it (README.md, "Phase 4: AP_Param").

`--param-memory` places ArduPilot's parameter tables (`var_info`), their strings and the objects they point
into in one byte memory. The tables' initializers are constant expressions behind macros (`AP_VAROFFSET`:
`__builtin_offsetof` of members of non-standard-layout classes, `&copter.g.v`, defaults converted to
`float`), whose values only clang's constant evaluator gives exactly. This module reads them from clang's
own evaluation: the unit is compiled with the reference flags to LLVM IR (`-S -emit-llvm -O0`), and each
global's initializer is serialized into its object representation (the IR types are laid out by the
target's data layout, natural alignment, `<{ }>` packed), with every pointer field recorded as a
relocation (symbol + byte offset) to be resolved to the memory's addresses.
"""
import re

TOKEN = re.compile(r'''\s*(?:
    (?P<str>c"(?:[^"\\]|\\[0-9A-Fa-f]{2}|\\\\)*")
  | (?P<punct><\{|\}>|[{}\[\](),=*])
  | (?P<name>[@%](?:"[^"]*"|[-a-zA-Z$._0-9]+))
  | (?P<num>-?0x[0-9A-Fa-fKLMHR][0-9A-Fa-f]*|-?\d+\.\d+(?:e[+-]?\d+)?|-?\d+)
  | (?P<word>[a-zA-Z_][a-zA-Z_0-9.]*)
)''', re.X)


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m or m.end() == i:
            if s[i:].strip() == "":
                break
            raise ValueError("IR token at %r" % s[i:i + 40])
        i = m.end()
        out.append(m.group(m.lastgroup))
    return out


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def take(self, want=None):
        x = self.t[self.i]
        if want is not None and x != want:
            raise ValueError("IR: expected %r, got %r near %r" % (want, x, self.t[self.i:self.i + 8]))
        self.i += 1
        return x


def parse_type(p, named):
    x = p.take()
    if re.fullmatch(r"i\d+", x):
        return ("int", int(x[1:]))
    if x in ("float", "double", "ptr"):
        return (x,)
    if x.startswith("%"):
        return ("named", x)
    if x == "[":
        n = int(p.take())
        p.take("x")
        e = parse_type(p, named)
        p.take("]")
        return ("array", n, e)
    if x in ("{", "<{"):
        close = "}" if x == "{" else "}>"
        fs = []
        while p.peek() != close:
            fs.append(parse_type(p, named))
            if p.peek() == ",":
                p.take()
        p.take(close)
        return ("struct", x == "<{", tuple(fs))
    raise ValueError("IR type %r" % x)


def resolve(t, named):
    while t[0] == "named":
        t = named[t[1]]
    return t


def size_align(t, named):
    t = resolve(t, named)
    k = t[0]
    if k == "int":
        n = max(1, (t[1] + 7) // 8)
        return n, n
    if k in ("float",):
        return 4, 4
    if k in ("double", "ptr"):
        return 8, 8
    if k == "array":
        s, a = size_align(t[2], named)
        return s * t[1], a
    if k == "struct":
        off, al = 0, 1
        for f in t[2]:
            s, a = size_align(f, named)
            if not t[1]:
                off = (off + a - 1) // a * a
                al = max(al, a)
            off += s
        if not t[1]:
            off = (off + al - 1) // al * al
        return off, al
    raise ValueError(t)


def field_offsets(t, named):
    t = resolve(t, named)
    offs, off = [], 0
    for f in t[2]:
        s, a = size_align(f, named)
        if not t[1]:
            off = (off + a - 1) // a * a
        offs.append(off)
        off += s
    return offs


def float_bits(text, width):
    import struct
    if text.lower().startswith(("0x", "-0x")):
        neg = text.startswith("-")
        h = text.lstrip("-")[2:]
        if h[0] in "KLMHR":
            raise ValueError("IR float " + text)
        v = int(h, 16)      # LLVM prints float constants as the bits of the double of the same value
        d = struct.unpack("<d", struct.pack("<Q", v))[0]
        if neg:
            d = -d
    else:
        d = float(text)
    if width == 4:
        return struct.unpack("<I", struct.pack("<f", d))[0]
    return struct.unpack("<Q", struct.pack("<d", d))[0]


def parse_ptr_value(p):
    """A pointer constant: (symbol, offset) or None (null)."""
    x = p.take()
    if x == "null" or x == "undef" or x == "zeroinitializer":
        return None
    if x.startswith("@"):
        return (x, 0)
    if x == "getelementptr":
        if p.peek() == "inbounds":
            p.take()
        p.take("(")
        et = parse_type(p, {})
        p.take(",")
        p.take("ptr")
        base = p.take()
        idx = []
        while p.peek() == ",":
            p.take()
            it = p.take()
            idx.append(int(p.take()))
        p.take(")")
        if et != ("int", 8) or len(idx) != 1:
            raise ValueError("IR getelementptr form %r %r" % (et, idx))
        return (base, idx[0])
    raise ValueError("IR pointer value %r" % x)


def unescape_c(s):
    body = s[2:-1]
    out, i = bytearray(), 0
    while i < len(body):
        if body[i] == "\\":
            if body[i + 1] == "\\":
                out.append(92)
                i += 2
            else:
                out.append(int(body[i + 1:i + 3], 16))
                i += 3
        else:
            out += body[i].encode()
            i += 1
    return bytes(out)


def serialize(p, t, named, buf, off, relocs):
    """Parse the value of type t at the parser and write it into buf at off."""
    t = resolve(t, named)
    if p.peek() in ("zeroinitializer", "undef", "poison"):
        p.take()
        return
    k = t[0]
    if k == "int":
        v = int(p.take())
        n = max(1, (t[1] + 7) // 8)
        if t[1] == 1:
            v = 1 if v in (1, -1) else 0
        buf[off:off + n] = (v % (1 << (8 * n))).to_bytes(n, "little")
        return
    if k in ("float", "double"):
        w = 4 if k == "float" else 8
        buf[off:off + w] = float_bits(p.take(), w).to_bytes(w, "little")
        return
    if k == "ptr":
        r = parse_ptr_value(p)
        if r is not None:
            relocs.append((off, r[0], r[1]))
        return
    if k == "array":
        if p.peek().startswith('c"'):
            bs = unescape_c(p.take())
            buf[off:off + len(bs)] = bs
            return
        p.take("[")
        es, _ = size_align(t[2], named)
        for i in range(t[1]):
            if i:
                p.take(",")
            et = parse_type(p, named)
            serialize(p, et, named, buf, off + i * es, relocs)
        p.take("]")
        return
    if k == "struct":
        offs = field_offsets(t, named)
        open_ = p.take()
        if open_ not in ("{", "<{"):
            raise ValueError("IR struct value %r" % open_)
        for i in range(len(t[2])):
            if i:
                p.take(",")
            ft = parse_type(p, named)
            serialize(p, ft, named, buf, off + offs[i], relocs)
        p.take("}" if open_ == "{" else "}>")
        return
    raise ValueError(t)


GLOBAL = re.compile(r'^(@(?:"[^"]*"|[-a-zA-Z$._0-9]+)) = (.*)$')
TYPEDEF = re.compile(r'^(%(?:"[^"]*"|[-a-zA-Z$._0-9]+)) = type (.*)$')
LINKAGE = {"private", "internal", "external", "unnamed_addr", "local_unnamed_addr", "dso_local", "hidden",
           "linkonce_odr", "weak_odr", "available_externally", "constant", "global", "thread_local",
           "linkonce", "weak", "common", "extern_weak", "protected", "default"}


class Module:
    """The globals of one IR file, parsed on demand: get(name) -> dict(defined, bytes, relocs, size, align,
    const)."""

    def __init__(self, text):
        self.named, self.raw, self.cache = {}, {}, {}
        lines = text.split("\n")
        for ln in lines:
            m = TYPEDEF.match(ln)
            if m:
                body = m.group(2)
                if body.strip() == "opaque":
                    continue
                self.named[m.group(1)] = parse_type(P(tokenize(body)), self.named)
        for ln in lines:
            m = GLOBAL.match(ln)
            if m and not m.group(2).startswith(("alias", "ifunc")):
                self.raw[m.group(1)] = m.group(2)

    def get(self, name):
        if name in self.cache:
            return self.cache[name]
        rest = self.raw.get(name)
        if rest is None:
            return None
        body = re.split(r", (?:align \d+|section \"[^\"]*\"|comdat(?:\([^)]*\))?)", rest)[0]
        p = P(tokenize(body))
        words = []
        while p.peek() in LINKAGE or (p.peek() and p.peek().startswith("addrspace")):
            words.append(p.take())
        ext = "external" in words or "extern_weak" in words
        t = parse_type(p, self.named)
        al = re.search(r", align (\d+)", rest)
        size, nal = size_align(t, self.named)
        g = {"type": t, "size": size, "align": int(al.group(1)) if al else nal, "const": "constant" in words,
             "defined": not ext, "relocs": [], "bytes": bytearray(size)}
        if not ext:
            serialize(p, t, self.named, g["bytes"], 0, g["relocs"])
        self.cache[name] = g
        return g
