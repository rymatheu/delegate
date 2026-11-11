#!/usr/bin/env python3
"""Generate Leanfc/Mavlink/Messages.lean from the MAVLink XML message definitions.

Usage (from the repository root):

    python3 sim/mavlink/gen_messages.py [--xml DIR] [--out Leanfc/Mavlink/Messages.lean]

DIR defaults to /Users/ryan/Research/delegate/mavlink/message_definitions/v1.0 (the MAVLink
protocol repository); the dialect read is ardupilotmega.xml with its includes (common.xml,
standard.xml, minimal.xml, ...). Only the messages named in MESSAGES are emitted.

Wire format (https://mavlink.io/en/guide/serialization.html):
  * the base fields (those before <extensions/>) are sorted by the size of their element type,
    largest first, with a stable sort (an array sorts by its element size);
  * the extension fields follow, in declaration order, unsorted;
  * CRC_EXTRA is the X.25 checksum of "NAME " followed, for each base field in wire order, by
    "TYPE NAME " (TYPE without the "_mavlink_version" suffix, "char" for strings) and, for an
    array, the byte of its length; the result is folded to one byte, (crc & 0xFF) ^ (crc >> 8).

No third-party module is used: the XML is read with the standard library.
"""

import argparse
import os
import sys
import xml.etree.ElementTree as ET

DEFAULT_XML = "/Users/ryan/Research/delegate/mavlink/message_definitions/v1.0"

# The supported messages. Keep in sync with README.md ("MAVLink interface").
MESSAGES = [
    "HEARTBEAT", "SYS_STATUS", "SYSTEM_TIME", "PING", "TIMESYNC",
    "PARAM_REQUEST_READ", "PARAM_REQUEST_LIST", "PARAM_VALUE", "PARAM_SET", "PARAM_ERROR",
    "GPS_RAW_INT", "ATTITUDE", "ATTITUDE_QUATERNION", "LOCAL_POSITION_NED", "GLOBAL_POSITION_INT",
    "MISSION_ITEM", "MISSION_REQUEST_LIST", "MISSION_COUNT", "MISSION_REQUEST", "MISSION_REQUEST_INT",
    "MISSION_ITEM_INT", "MISSION_ACK", "MISSION_CLEAR_ALL", "MISSION_SET_CURRENT", "MISSION_CURRENT",
    "MISSION_ITEM_REACHED", "GPS_GLOBAL_ORIGIN", "HOME_POSITION", "SET_MODE", "REQUEST_DATA_STREAM",
    "VFR_HUD", "COMMAND_INT", "COMMAND_LONG", "COMMAND_ACK", "NAV_CONTROLLER_OUTPUT",
    "EXTENDED_SYS_STATE", "BATTERY_STATUS", "AUTOPILOT_VERSION", "STATUSTEXT", "MESSAGE_INTERVAL",
    "SET_POSITION_TARGET_LOCAL_NED", "FILE_TRANSFER_PROTOCOL",
]

SIZES = {"char": 1, "uint8_t": 1, "int8_t": 1, "uint16_t": 2, "int16_t": 2, "uint32_t": 4,
         "int32_t": 4, "float": 4, "uint64_t": 8, "int64_t": 8, "double": 8}

# Lean type, byte reader, byte writer, word conversions (to/from Int) per element type.
LEAN = {
    "uint8_t": ("UInt8", "Bytes.u8", "Bytes.putU8"),
    "int8_t": ("Int8", "Bytes.i8", "Bytes.putI8"),
    "uint16_t": ("UInt16", "Bytes.u16", "Bytes.putU16"),
    "int16_t": ("Int16", "Bytes.i16", "Bytes.putI16"),
    "uint32_t": ("UInt32", "Bytes.u32", "Bytes.putU32"),
    "int32_t": ("Int32", "Bytes.i32", "Bytes.putI32"),
    "uint64_t": ("UInt64", "Bytes.u64", "Bytes.putU64"),
    "int64_t": ("Int64", "Bytes.i64", "Bytes.putI64"),
    "float": ("R", "Bytes.f32", "Bytes.putF32"),
    "double": ("UInt64", "Bytes.u64", "Bytes.putU64"),  # carried as its bit pattern
}
TO_WORD = {"uint8_t": "Int.ofNat {}.toNat", "uint16_t": "Int.ofNat {}.toNat",
           "uint32_t": "Int.ofNat {}.toNat", "uint64_t": "Int.ofNat {}.toNat",
           "double": "Int.ofNat {}.toNat",
           "int8_t": "{}.toInt", "int16_t": "{}.toInt", "int32_t": "{}.toInt", "int64_t": "{}.toInt",
           "float": "Int.ofNat (ExecFloat.Binary.toBits32 {}).toNat", "char": "Int.ofNat {}.toNat"}
OF_WORD = {"uint8_t": "UInt8.ofNat {}.toNat", "uint16_t": "UInt16.ofNat {}.toNat",
           "uint32_t": "UInt32.ofNat {}.toNat", "uint64_t": "UInt64.ofNat {}.toNat",
           "double": "UInt64.ofNat {}.toNat",
           "int8_t": "Int8.ofInt {}", "int16_t": "Int16.ofInt {}", "int32_t": "Int32.ofInt {}",
           "int64_t": "Int64.ofInt {}",
           "float": "ExecFloat.Binary.ofBits32 (UInt32.ofNat {}.toNat)", "char": "UInt8.ofNat {}.toNat"}

KEYWORDS = {"type", "from", "at", "end", "do", "let", "in", "fun", "if", "then", "else", "match",
            "with", "where", "open", "import", "structure", "class", "instance", "def", "theorem",
            "by", "have", "show", "mut", "return", "for", "unless", "local", "private", "protected",
            "deriving", "variable", "universe", "namespace", "section", "notation", "macro",
            "syntax", "axiom", "example", "abbrev", "inductive", "set_option", "calc", "nomatch"}


def x25(data, crc=0xFFFF):
    for b in data:
        tmp = b ^ (crc & 0xFF)
        tmp = (tmp ^ (tmp << 4)) & 0xFF
        crc = ((crc >> 8) ^ (tmp << 8) ^ (tmp << 3) ^ (tmp >> 4)) & 0xFFFF
    return crc


class Field:
    def __init__(self, el, ext):
        t = el.get("type")
        self.name = el.get("name")
        self.ext = ext
        self.array = None
        if "[" in t:
            base, n = t.split("[")
            self.array = int(n.rstrip("]"))
            t = base
        self.crc_type = "uint8_t" if t == "uint8_t_mavlink_version" else t
        self.type = self.crc_type
        self.size = SIZES[self.type]
        self.desc = " ".join((el.text or "").split())

    @property
    def lean_name(self):
        return f"«{self.name}»" if self.name in KEYWORDS else self.name

    @property
    def wire_len(self):
        return self.size * (self.array or 1)


class Message:
    def __init__(self, el):
        self.id = int(el.get("id"))
        self.name = el.get("name")
        self.desc = " ".join((el.findtext("description") or "").split())
        self.fields = []
        ext = False
        for child in el:
            if child.tag == "extensions":
                ext = True
            elif child.tag == "field":
                self.fields.append(Field(child, ext))
        base = [f for f in self.fields if not f.ext]
        self.wire = sorted(base, key=lambda f: -f.size) + [f for f in self.fields if f.ext]
        self.base_len = sum(f.wire_len for f in base)
        self.max_len = sum(f.wire_len for f in self.fields)
        crc = x25((self.name + " ").encode())
        for f in sorted(base, key=lambda f: -f.size):
            crc = x25((f.crc_type + " ").encode(), crc)
            crc = x25((f.name + " ").encode(), crc)
            if f.array:
                crc = x25(bytes([f.array]), crc)
        self.crc_extra = (crc & 0xFF) ^ (crc >> 8)

    @property
    def struct(self):
        return "".join(p.capitalize() for p in self.name.split("_"))

    @property
    def ctor(self):
        s = self.struct
        return s[0].lower() + s[1:]


def load(xml_dir, root="ardupilotmega.xml"):
    seen, msgs = set(), {}

    def visit(fn):
        if fn in seen:
            return
        seen.add(fn)
        tree = ET.parse(os.path.join(xml_dir, fn)).getroot()
        for inc in tree.findall("include"):
            visit(inc.text.strip())
        for m in tree.iter("message"):
            msg = Message(m)
            msgs[msg.name] = msg
    visit(root)
    return msgs


def lean_doc(s, limit=240):
    """The first sentence of a description, at most `limit` characters, safe inside a Lean comment."""
    first = s.split(". ")[0].rstrip(".")
    if len(first) > limit:
        first = first[:limit].rsplit(" ", 1)[0] + " ..."
    return (first + ".").replace("-/", "- /").replace("/-", "/ -")


def gen(msgs, xml_dir, git_rev):
    out = []
    w = out.append
    w("import Leanfc.Mavlink.Bytes")
    w("")
    w("/-!")
    w("# Messages (GENERATED, do not edit)")
    w("")
    w("Generated by `sim/mavlink/gen_messages.py` from the MAVLink XML definitions")
    w(f"(`ardupilotmega.xml` and its includes in `{xml_dir}`, MAVLink repository {git_rev}):")
    w("`python3 sim/mavlink/gen_messages.py`. The message list is `MESSAGES` in the script.")
    w("")
    w("One structure per message with its fields in declaration order (MAVLink names; Lean keywords")
    w("in «»), and the inductive `Msg` with one constructor per message. `encode` gives the message id")
    w("and the full payload in wire order (base fields sorted by element size, largest first, stable;")
    w("extensions last, unsorted), without truncation (`Frame.serialize` truncates). `decode` reads a")
    w("payload of any length, every missing byte read as zero (the MAVLink 2 zero extension), and")
    w("ignores bytes past the known fields. MAVLink `float` is `R` (binary32) by its bit pattern,")
    w("`char[n]` a `ByteArray`, other arrays `Array`; encoding pads short arrays with zeros and cuts")
    w("long ones. `info` gives CRC_EXTRA and the base and full payload lengths. `toWords`/`ofWords`")
    w("flatten the fields to integers (floats as their bits) for the codec test.")
    w("-/")
    w("")
    w("namespace Mavlink")
    w("")
    w("open FloatLib.Floats")
    w("")
    w("/-- CRC_EXTRA and payload lengths of a message: base fields only, and with extensions. -/")
    w("structure MsgInfo where")
    w("  crcExtra : UInt8")
    w("  minLen : Nat")
    w("  maxLen : Nat")
    w("  deriving Repr, BEq")
    w("")
    for m in msgs:
        w(f"/-- {m.name} (#{m.id}, CRC_EXTRA {m.crc_extra}, payload {m.base_len}..{m.max_len} bytes). "
          f"{lean_doc(m.desc)} -/")
        w(f"structure {m.struct} where")
        for f in m.fields:
            lt = LEAN.get(f.type, ("UInt8",))[0]
            if f.type == "char":
                ty, dflt = "ByteArray", "ByteArray.empty"
            elif f.array:
                ty, dflt = f"Array {lt}", "#[]"
            else:
                ty, dflt = lt, "0"
            ext = " (extension)" if f.ext else ""
            w(f"  /-- {f.type}{'[' + str(f.array) + ']' if f.array else ''}{ext}: {lean_doc(f.desc)} -/")
            w(f"  {f.lean_name} : {ty} := {dflt}")
        w("  deriving Inhabited")
        w("")
        w(f"namespace {m.struct}")
        w("")
        w(f"def encode (m : {m.struct}) : ByteArray :=")
        parts = ["ByteArray.empty"]
        for f in m.wire:
            if f.type == "char":
                parts.append(f"Bytes.putChars {f.array} m.{f.lean_name}")
            elif f.array:
                parts.append(f"Bytes.putArray {f.array} {LEAN[f.type][2]} m.{f.lean_name}")
            else:
                parts.append(f"{LEAN[f.type][2]} m.{f.lean_name}")
        w("  " + "\n    |> ".join(parts))
        w("")
        w(f"def decode (b : ByteArray) : {m.struct} :=")
        off, inits = 0, []
        for f in m.wire:
            if f.type == "char":
                inits.append(f"{f.lean_name} := Bytes.chars b {off} {f.array}")
            elif f.array:
                inits.append(f"{f.lean_name} := Bytes.array b {off} {f.array} {f.size} {LEAN[f.type][1]}")
            else:
                inits.append(f"{f.lean_name} := {LEAN[f.type][1]} b {off}")
            off += f.wire_len
        w("  { " + ",\n    ".join(inits) + " }")
        w("")
        w(f"def toWords (m : {m.struct}) : Array Int :=")
        ws = []
        for f in m.fields:
            conv = TO_WORD[f.type].format("x")
            if f.type == "char":
                ws.append(f"(Bytes.charsPadded {f.array} m.{f.lean_name}).map (fun x => {conv})")
            elif f.array:
                zero = "(0 : R)" if f.type == "float" else "0"
                ws.append(f"(Bytes.padded {f.array} {zero} m.{f.lean_name}).map (fun x => {conv})")
            else:
                ws.append("#[" + TO_WORD[f.type].format(f"m.{f.lean_name}") + "]")
        w("  " + " ++\n  ".join(ws))
        w("")
        w(f"def ofWords (ws : Array Int) : {m.struct} :=")
        off, inits = 0, []
        for f in m.fields:
            conv = OF_WORD[f.type].format("x")
            if f.type == "char":
                inits.append(f"{f.lean_name} := ByteArray.mk (Array.ofFn (n := {f.array}) fun i => "
                             f"let x := ws.getD ({off} + i.val) 0; {conv})")
                off += f.array
            elif f.array:
                inits.append(f"{f.lean_name} := Array.ofFn (n := {f.array}) fun i => "
                             f"let x := ws.getD ({off} + i.val) 0; {conv}")
                off += f.array
            else:
                inits.append(f"{f.lean_name} := let x := ws.getD {off} 0; {conv}")
                off += 1
        w("  { " + ",\n    ".join(inits) + " }")
        w("")
        w(f"end {m.struct}")
        w("")
    w("/-- The supported messages. -/")
    w("inductive Msg where")
    for m in msgs:
        w(f"  | {m.ctor} (m : {m.struct})")
    w("  deriving Inhabited")
    w("")
    w("namespace Msg")
    w("")
    w("/-- The message id. -/")
    w("def id : Msg → UInt32")
    for m in msgs:
        w(f"  | .{m.ctor} _ => {m.id}")
    w("")
    w("/-- The message name, as in the XML. -/")
    w("def name : Msg → String")
    for m in msgs:
        w(f"  | .{m.ctor} _ => \"{m.name}\"")
    w("")
    w("/-- Message id and full (untruncated) payload in wire order. -/")
    w("def encode : Msg → UInt32 × ByteArray")
    for m in msgs:
        w(f"  | .{m.ctor} m => ({m.id}, m.encode)")
    w("")
    w("/-- The message of a payload (zero-extended as needed), `none` for an unsupported id. -/")
    w("def decode (msgid : UInt32) (payload : ByteArray) : Option Msg :=")
    w("  match msgid.toNat with")
    for m in msgs:
        w(f"  | {m.id} => some (.{m.ctor} ({m.struct}.decode payload))")
    w("  | _ => none")
    w("")
    w("/-- The fields as integers, in declaration order (floats as bits, arrays flattened). -/")
    w("def toWords : Msg → Array Int")
    for m in msgs:
        w(f"  | .{m.ctor} m => m.toWords")
    w("")
    w("/-- Inverse of `toWords` for a message id; `none` for an unsupported id. -/")
    w("def ofWords (msgid : UInt32) (ws : Array Int) : Option Msg :=")
    w("  match msgid.toNat with")
    for m in msgs:
        w(f"  | {m.id} => some (.{m.ctor} ({m.struct}.ofWords ws))")
    w("  | _ => none")
    w("")
    w("end Msg")
    w("")
    w("/-- CRC_EXTRA and payload lengths of each supported message id. -/")
    w("def info (msgid : UInt32) : Option MsgInfo :=")
    w("  match msgid.toNat with")
    for m in msgs:
        w(f"  | {m.id} => some ⟨{m.crc_extra}, {m.base_len}, {m.max_len}⟩")
    w("  | _ => none")
    w("")
    w("end Mavlink")
    w("")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xml", default=DEFAULT_XML)
    ap.add_argument("--out", default="Leanfc/Mavlink/Messages.lean")
    ap.add_argument("--table", action="store_true", help="print name, id, CRC_EXTRA, lengths")
    a = ap.parse_args()
    allm = load(a.xml)
    missing = [n for n in MESSAGES if n not in allm]
    if missing:
        sys.exit(f"not in the XML: {missing}")
    msgs = sorted((allm[n] for n in MESSAGES), key=lambda m: m.id)
    if a.table:
        for m in msgs:
            print(f"{m.name:32s} {m.id:4d} {m.crc_extra:4d} {m.base_len:4d} {m.max_len:4d}")
        return
    rev = "(unknown revision)"
    try:
        import subprocess
        rev = "commit " + subprocess.check_output(
            ["git", "-C", a.xml, "rev-parse", "--short", "HEAD"], text=True).strip()
    except Exception:
        pass
    with open(a.out, "w") as fh:
        fh.write(gen(msgs, a.xml, rev))
    print(f"wrote {a.out}: {len(msgs)} messages")


if __name__ == "__main__":
    main()
