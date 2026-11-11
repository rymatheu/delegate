/-!
# Crc

The MAVLink checksum: CRC-16/MCRF4XX (the X.25 CRC as MAVLink computes it), initial value 0xFFFF,
fed one byte at a time; https://mavlink.io/en/guide/serialization.html#checksum. A frame's checksum
covers the bytes after the start marker up to the end of the payload, then the message's
CRC_EXTRA byte.
-/

namespace Mavlink.Crc

def init : UInt16 := 0xFFFF

/-- One byte into the checksum. -/
def accumulate (crc : UInt16) (b : UInt8) : UInt16 :=
  let t : UInt8 := b ^^^ crc.toUInt8
  let t : UInt8 := t ^^^ (t <<< 4)
  let t16 := t.toUInt16
  (crc >>> 8) ^^^ (t16 <<< 8) ^^^ (t16 <<< 3) ^^^ (t16 >>> 4)

/-- The bytes `b[lo..hi)` into the checksum. -/
def accumulateRange (crc : UInt16) (b : ByteArray) (lo hi : Nat) : UInt16 :=
  (List.range (hi - lo)).foldl (fun c i => accumulate c (b.get! (lo + i))) crc

/-- The checksum of the bytes `b[lo..hi)` followed by `extra`. -/
def frame (b : ByteArray) (lo hi : Nat) (extra : UInt8) : UInt16 :=
  accumulate (accumulateRange init b lo hi) extra

end Mavlink.Crc
