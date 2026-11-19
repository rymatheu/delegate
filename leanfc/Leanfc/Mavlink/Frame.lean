import Leanfc.Mavlink.Crc
import Leanfc.Mavlink.Messages

/-!
# Frame

MAVLink framing; https://mavlink.io/en/guide/serialization.html.

MAVLink 2: `0xFD len incompat compat seq sysid compid msgid(3, LE) payload(len) crc(2)`, plus a
13-byte signature when `incompat` has bit 0 (MAVLINK_IFLAG_SIGNED). MAVLink 1:
`0xFE len seq sysid compid msgid payload crc`. The checksum (`Crc`) covers everything after the
start marker up to the end of the payload, then the message's CRC_EXTRA (`Messages.info`).

`feed` is the byte-fed parser. A candidate frame starts at a start marker; it fails when its
incompatibility flags are not 0 or 1, when its message id is not supported (its CRC_EXTRA is
unknown, so it cannot be checked), or when its checksum is wrong. On failure the parser drops the
start marker and rescans the candidate's other bytes, so a real frame that follows garbage, or
hides inside a failed candidate, is still found. A frame whose checksum is right is accepted
whatever its length (a shorter MAVLink 2 payload is zero-extended when decoded, a longer one keeps
only the known fields). Signed frames are checked, skipped past their signature and not returned
(no signing support). A single byte can complete several frames (on a rescan); `feed` returns the
first and keeps the rest in `backlog`, which the next `feed` or `drain` returns.

Termination: `run` is given fuel 281·(bytes pending + 1). Each byte is fed once plus once per failed
candidate that started before it and covers it; such candidates start at distinct positions at most
280 bytes before it (the longest frame is 280 bytes), so 281 feeds per byte suffice.

`serialize` writes MAVLink 2 (payload truncated: trailing zero bytes removed, the first byte always
kept) or MAVLink 1 (the base payload, cut or zero-padded to its length), never signed. The sequence
number is the caller's (`Frame.seq`).
-/

namespace Mavlink

inductive Version where
  | v1
  | v2
  deriving Repr, BEq, Inhabited

structure Frame where
  version : Version := .v2
  seq : UInt8 := 0
  sysid : UInt8 := 0
  compid : UInt8 := 0
  msgid : UInt32 := 0
  /-- As received (MAVLink 2: possibly truncated) or as to be sent (untruncated). -/
  payload : ByteArray := ByteArray.empty
  deriving Inhabited

/-- Counters, for tests and diagnostics. -/
structure ParserStats where
  frames : Nat := 0
  /-- candidates rejected (bad flags, unknown id, bad checksum) -/
  rejected : Nat := 0
  /-- valid signed frames skipped -/
  signed : Nat := 0
  deriving Repr, Inhabited

structure ParserState where
  /-- the candidate frame so far, from its start marker (empty between frames) -/
  buf : ByteArray := ByteArray.empty
  backlog : List Frame := []
  stats : ParserStats := {}
  deriving Inhabited

namespace Frame

def stxV1 : UInt8 := 0xFE
def stxV2 : UInt8 := 0xFD

/-- The message of a frame, `none` for an unsupported id. -/
def msg? (f : Frame) : Option Msg := Msg.decode f.msgid f.payload

def ofMsg (seq sysid compid : UInt8) (m : Msg) : Frame :=
  let (msgid, payload) := m.encode
  { seq, sysid, compid, msgid, payload }

/-- The outcome of one byte added to a candidate. -/
inductive Step where
  | more (buf : ByteArray)
  | frame (f : Frame)
  /-- not part of a frame (no start marker), or a valid signed frame skipped -/
  | drop (signed : Bool)
  | fail
  deriving Inhabited

/-- Add byte `b` to the candidate `buf`. -/
def push (buf : ByteArray) (b : UInt8) : Step :=
  if buf.size == 0 then
    if b == stxV2 || b == stxV1 then .more (ByteArray.empty.push b) else .drop false
  else
    let buf := buf.push b
    let n := buf.size
    let v2 := buf.get! 0 == stxV2
    let hdr := if v2 then 10 else 6
    if v2 && n == 3 && buf.get! 2 > 1 then .fail else
    if n < hdr then .more buf else
    let msgid : UInt32 :=
      if v2 then (buf.get! 7).toUInt32 ||| ((buf.get! 8).toUInt32 <<< 8) ||| ((buf.get! 9).toUInt32 <<< 16)
      else (buf.get! 5).toUInt32
    match info msgid with
    | none => .fail
    | some inf =>
      let len := (buf.get! 1).toNat
      let signed := v2 && buf.get! 2 == 1
      let total := hdr + len + 2 + (if signed then 13 else 0)
      if n < total then .more buf else
      let crc := Crc.frame buf 1 (hdr + len) inf.crcExtra
      let got := (buf.get! (hdr + len)).toUInt16 ||| ((buf.get! (hdr + len + 1)).toUInt16 <<< 8)
      if crc != got then .fail
      else if signed then .drop true
      else
        let (seq, sysid, compid) :=
          if v2 then (buf.get! 4, buf.get! 5, buf.get! 6) else (buf.get! 2, buf.get! 3, buf.get! 4)
        .frame { version := if v2 then .v2 else .v1, seq, sysid, compid, msgid,
                 payload := buf.extract hdr (hdr + len) }

/-- Feed `bs` to the candidate `buf`, collecting frames; a failed candidate's bytes after its
start marker are fed again. -/
def run : Nat → ByteArray → List UInt8 → Array Frame → ParserStats → ByteArray × Array Frame × ParserStats
  | 0, _, _, acc, st => (ByteArray.empty, acc, st)
  | _, buf, [], acc, st => (buf, acc, st)
  | fuel + 1, buf, b :: rest, acc, st =>
    match push buf b with
    | .more buf' => run fuel buf' rest acc st
    | .frame f => run fuel ByteArray.empty rest (acc.push f) { st with frames := st.frames + 1 }
    | .drop s => run fuel ByteArray.empty rest acc (if s then { st with signed := st.signed + 1 } else st)
    | .fail => run fuel ByteArray.empty ((buf.push b).toList.drop 1 ++ rest) acc
        { st with rejected := st.rejected + 1 }

end Frame

namespace Parser

/-- One byte: the first frame it completes (or one left from an earlier byte). -/
def feed (s : ParserState) (b : UInt8) : ParserState × Option Frame :=
  let (buf, fs, stats) := Frame.run (281 * (s.buf.size + 2)) s.buf [b] #[] s.stats
  match s.backlog ++ fs.toList with
  | [] => ({ s with buf, stats, backlog := [] }, none)
  | f :: rest => ({ buf, stats, backlog := rest }, some f)

/-- The frames kept in the backlog. -/
def drain (s : ParserState) : ParserState × Array Frame :=
  ({ s with backlog := [] }, s.backlog.toArray)

/-- Every frame completed by the bytes `bs`, in order. -/
def feedBytes (s : ParserState) (bs : ByteArray) : ParserState × Array Frame :=
  let (s, acc) := bs.foldl (fun (acc : ParserState × Array Frame) b =>
    let (s, f) := feed acc.1 b
    (s, match f with | some f => acc.2.push f | none => acc.2)) (s, #[])
  let (s, rest) := drain s
  (s, acc ++ rest)

end Parser

namespace Frame

/-- MAVLink 2 payload truncation: trailing zero bytes removed, the first byte kept. -/
def truncate (p : ByteArray) : ByteArray :=
  let n := (p.data.toList.reverse.dropWhile (· == 0)).length
  p.extract 0 (max n 1)

/-- The frame's bytes; the checksum uses the message's CRC_EXTRA (0 for an unsupported id). -/
def serialize (f : Frame) : ByteArray :=
  let extra := ((info f.msgid).map (·.crcExtra)).getD 0
  let body : ByteArray := match f.version with
    | .v2 =>
      let p := truncate (f.payload.extract 0 255)
      ByteArray.mk #[stxV2, p.size.toUInt8, 0, 0, f.seq, f.sysid, f.compid,
        f.msgid.toUInt8, (f.msgid >>> 8).toUInt8, (f.msgid >>> 16).toUInt8] ++ p
    | .v1 =>
      let len := ((info f.msgid).map (·.minLen)).getD f.payload.size
      let p := ByteArray.mk (Array.ofFn (n := min len 255) fun i => Bytes.at_ f.payload i.val)
      ByteArray.mk #[stxV1, p.size.toUInt8, f.seq, f.sysid, f.compid, f.msgid.toUInt8] ++ p
  let crc := Crc.frame body 1 body.size extra
  (body.push crc.toUInt8).push (crc >>> 8).toUInt8

end Frame

end Mavlink
