import GCS_lib

/-! `gcs_smoke INPUTS OUTPUTS STORAGE` (README.md, "Phase 4: GCS_MAVLink"): a smoke run of the translated GCS, NOT the
byte replay of the brief (not done, see the README): one `GCS_MAVLINK_Copter` channel built by the translated
constructor on a GCS object in the heap (zero: AP_Param's boot is not run, SYSID_THISMAV is set to 1 by hand), the
recorded uplink bytes appended to SERIAL0's receive queue per input line, the translated `GCS::update_receive` and
`GCS::update_send` run once per line at the line's time (the reference's tasks 28 and 29 at 400 Hz, without the
scheduler's skips or the boot's delay callbacks). Prints the frames the translation wrote per message id, the
boundary log and the unreached functions called. -/

open GCS_lib

def hexBytes (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for k in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (digit cs[2 * k]! * 16 + digit cs[2 * k + 1]!))
  return out

def field (line key : String) : Option String :=
  (line.splitOn " ").findSome? fun t => if t.startsWith (key ++ "=") then some (t.drop (key.length + 1)).toString else none

/-- MAVLink 2 / 1 frames in a byte stream (start byte, length) by message id; other bytes counted as text. -/
def frameIds (b : ByteArray) : Array UInt32 × Nat := Id.run do
  let mut i := 0
  let mut ids : Array UInt32 := #[]
  let mut other := 0
  while i < b.size do
    if b.get! i == 0xfd && i + 10 ≤ b.size then
      let len := (b.get! (i + 1)).toNat
      let id := (b.get! (i + 7)).toUInt32 ||| ((b.get! (i + 8)).toUInt32 <<< 8) ||| ((b.get! (i + 9)).toUInt32 <<< 16)
      ids := ids.push id
      i := i + 12 + len
    else if b.get! i == 0xfe && i + 6 ≤ b.size then
      ids := ids.push (b.get! (i + 5)).toUInt32
      i := i + 8 + (b.get! (i + 1)).toNat
    else
      other := other + 1
      i := i + 1
  return (ids, other)

def count (xs : Array UInt32) : List (UInt32 × Nat) :=
  let ks := xs.foldl (fun (acc : List UInt32) x => if acc.contains x then acc else acc ++ [x]) []
  ks.map fun k => (k, (xs.filter (· == k)).size)

def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, outp, stPath] =>
    let st ← IO.FS.readBinFile stPath
    let ins ← IO.FS.lines inp
    let outs ← IO.FS.lines outp
    let setup : PMem.M (UInt64 × UInt64) := do
      let g ← PMem.alloc 544                     -- GCS_Copter (clang's sizeof)
      PMem.stU64 addr'GCS___singleton g
      PMem.stU32 (g + 160) 1                     -- SYSID_THISMAV (GCS::sysid)
      PMem.stU32 (g + 164) 255                   -- MAV_GCS_SYSID
      let c ← PMem.alloc 880                     -- GCS_MAVLINK_Copter
      GCS_MAVLINK.GCS_MAVLINK c 0x10             -- the UART: a non-null address the boundary does not read
      PMem.stU8 (c + 40) 0                       -- chan = MAVLINK_COMM_0 (GCS_MAVLINK::init)
      PMem.stU64 (g + 32) c                      -- _chan[0]
      PMem.stU8 (g + 28) 1                       -- _num_gcs
      PMem.stU64 addr'mavlink_comm_port 0x10     -- mavlink_comm_port[0]
      modify fun s => { s with seqAddr := c + 408 + 10 }
      return (g, c)
    let (gc, m0) := setup.run (initMem st)
    let g := gc.1
    let mut m := m0
    let mut ours : Array UInt32 := #[]
    let mut recd : Array UInt32 := #[]
    let mut text := 0
    let t0 ← IO.monoNanosNow
    for k in [0:ins.size] do
      let line := ins[k]!
      let t := (field line "t").getD "0"
      let up := hexBytes ((field line "up").getD "")
      m := { m with clockUs := t.toNat!.toUInt64, rx := m.rx.extract m.rxPos m.rx.size ++ up, rxPos := 0, tx := ByteArray.empty }
      let ((), m1) := (do GCS.update_receive g; GCS.update_send g : PMem.M Unit).run m
      m := m1
      let (ids, _) := frameIds m.tx
      if k < 3 || (ids.size > 1 && ours.size < 40) then
        IO.println s!"line {k + 1} tx {m.tx.size} bytes: {m.tx.toList.take 40}"
      ours := ours ++ ids
      if h : k < outs.size then
        let (rids, o) := frameIds (hexBytes ((field outs[k] "down").getD ""))
        recd := recd ++ rids
        text := text + o
    let t1 ← IO.monoNanosNow
    IO.println s!"gcs_smoke: {ins.size} lines in {(t1 - t0).toFloat / 1e9} s ({(t1 - t0).toFloat / 1e3 / ins.size.toFloat} us per line)"
    IO.println s!"frames written by the translation: {ours.size}; recorded downlink frames: {recd.size} (+{text} non-MAVLink bytes)"
    IO.println s!"translation by message id: {count ours}"
    IO.println s!"recorded by message id: {count recd}"
    IO.println s!"unreached functions called: {m.unreached.toList.eraseDups}"
    IO.println s!"boundary log ({m.log.size} lines), first 10: {m.log.toList.take 10}"
    return 0
  | _ => IO.eprintln "usage: gcs_smoke INPUTS OUTPUTS STORAGE"; return 2
