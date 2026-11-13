/-
The Lean side of the mission round trip against the reference (ardupilot/mission_roundtrip.py; README.md "Phase 4:
AP_Mission"): the translated MAVLink library (`Mavlink_lib`) parses the flight's uplink, the translated AP_Mission
(`Mission_lib`) stores and reads the mission. What MissionItemProtocol and MissionItemProtocol_Waypoints do with the
messages (GCS_MAVLink/MissionItemProtocol*.cpp, not translated in this slice) is written out below, call for call; it
is the check's harness, not translated code. Input (argument 2, written by the script): `total N` (MIS_TOTAL at boot),
then in time order `home T LAT LNG ALT` (AP_AHRS::set_home: the mission's home record rewritten) and `up T LINE HEX`
(uplink bytes), then `mark LINE` (the input line after which the storage is printed as `storage_mark`). Output:
`item SEQ HEX` for each MISSION_REQUEST_INT answered (the 38 bytes of the MISSION_ITEM_INT struct), `storage_mark HEX`,
`storage_end HEX`, and a line per mission message.
-/
import Mavlink_lib
import Mission_lib

open Mission_lib in
/-- The bytes of a MISSION_ITEM_INT (its packed struct, wire order). -/
def itemBytes (p : Mission_lib.__mavlink_mission_item_int_t) : Array UInt8 :=
  CString.ofUInt32 (Binary32.toBits p.param1) ++ CString.ofUInt32 (Binary32.toBits p.param2) ++
  CString.ofUInt32 (Binary32.toBits p.param3) ++ CString.ofUInt32 (Binary32.toBits p.param4) ++
  CString.ofUInt32 p.x.toUInt32 ++ CString.ofUInt32 p.y.toUInt32 ++ CString.ofUInt32 (Binary32.toBits p.z) ++
  CString.ofUInt16 p.seq ++ CString.ofUInt16 p.command ++
  #[p.target_system, p.target_component, p.frame, p.current, p.autocontinue, p.mission_type]

/-- MAVLink's struct as AP_Mission's translation spells it (the same C struct, two translations). -/
def toMission (p : Mavlink_lib.__mavlink_mission_item_int_t) : Mission_lib.__mavlink_mission_item_int_t :=
  { param1 := p.param1, param2 := p.param2, param3 := p.param3, param4 := p.param4, x := p.x, y := p.y, z := p.z,
    seq := p.seq, command := p.command, target_system := p.target_system, target_component := p.target_component,
    frame := p.frame, current := p.current, autocontinue := p.autocontinue, mission_type := p.mission_type }

def hexOf (a : Array UInt8) : String :=
  String.join (a.toList.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)

def hexBytes (s : String) : Array UInt8 := Id.run do
  let cs := s.toList.toArray
  let mut out : Array UInt8 := #[]
  let dig := fun (c : Char) => if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  for i in [0:cs.size / 2] do
    out := out.push (dig cs[2 * i]! * 16 + dig cs[2 * i + 1]!).toUInt8
  return out

structure RT where
  w : Mission_lib.World
  hs : Array UInt8
  msg : Mavlink_lib.__mavlink_message := {}
  st : Mavlink_lib.__mavlink_status := {}
  bufs : Array Mavlink_lib.__mavlink_message := Mavlink_lib.mav_chan_buffer'init
  sts : Array Mavlink_lib.__mavlink_status := Mavlink_lib.mav_chan_status'init
  receiving : Bool := false
  requestI : UInt16 := 0
  requestLast : UInt16 := 0

open Mission_lib in
/-- One parsed message: what GCS_MAVLINK routes to the mission's MissionItemProtocol_Waypoints and what that does. -/
def handle (r : RT) (m : Mavlink_lib.__mavlink_message) (out : IO.FS.Stream) : IO RT := do
  let mut r := r
  let w := r.w
  let inp := w.mission'inp
  if m.msgid == 44 then          -- MISSION_COUNT: MissionItemProtocol::handle_mission_count
    let c := Mavlink_lib.mavlink_msg_mission_count_decode m {}
    if c.mission_type == 0 then
      let s := AP_Mission.truncate w.mission inp c.count       -- MissionItemProtocol_Waypoints::truncate
      r := { r with w := { w with mission := s }, receiving := c.count != 0, requestI := 0, requestLast := c.count - 1 }
      out.putStrLn s!"count {c.count}: truncate, num_commands {AP_Mission.num_commands s}"
  else if m.msgid == 45 then     -- MISSION_CLEAR_ALL
    let c := Mavlink_lib.mavlink_msg_mission_clear_all_decode m {}
    if c.mission_type == 0 then
      let (s, ok) := AP_Mission.clear w.mission inp
      r := { r with w := { w with mission := s } }
      out.putStrLn s!"clear_all: {ok}"
  else if m.msgid == 73 then     -- MISSION_ITEM_INT: MissionItemProtocol::handle_mission_item
    let p := toMission (Mavlink_lib.mavlink_msg_mission_item_int_decode m {})
    if p.mission_type == 0 && r.receiving && p.seq == r.requestI then
      let n := AP_Mission.num_commands w.mission
      let (cmd, res) := AP_Mission.mavlink_int_to_mission_cmd p {}
      let mut ok := MAV_MISSION_RESULT.toInt res == 0
      let mut how := "rejected"
      -- (the DO_JUMP target check of append_item/replace_item: no DO_JUMP in the flight's mission; reported if seen)
      if cmd.id == 177 then out.putStrLn "DO_JUMP: target check not emulated"
      if ok then
        if p.seq < n then
          let (s, hs, b) := AP_Mission.replace_cmd w.mission w inp cmd.index cmd r.hs
          r := { r with w := { w with mission := s }, hs := hs }
          ok := b; how := "replace_cmd"
        else if p.seq == n then
          let (s, _, hs, b) := AP_Mission.add_cmd w.mission w inp cmd r.hs
          r := { r with w := { w with mission := s }, hs := hs }
          ok := b; how := "add_cmd"
        else
          ok := false; how := "beyond the end"
      out.putStrLn s!"item_int {p.seq} command {p.command}: mavlink_int_to_mission_cmd {MAV_MISSION_RESULT.toInt res}, {how} {ok}, num_commands {AP_Mission.num_commands r.w.mission}"
      if ok then
        let i := r.requestI + 1
        r := { r with requestI := i, receiving := i ≤ r.requestLast }
      else
        r := { r with receiving := false }
  else if m.msgid == 51 then     -- MISSION_REQUEST_INT: MissionItemProtocol_Waypoints::get_item
    let q := Mavlink_lib.mavlink_msg_mission_request_int_decode m {}
    if q.mission_type == 0 then
      if q.seq != 0 && q.seq ≥ AP_Mission.num_commands w.mission then
        out.putStrLn s!"request_int {q.seq}: invalid sequence"
      else
        let (cmd, ok) := AP_Mission.read_cmd_from_storage w.mission w inp q.seq {} r.hs
        let (p, ok2) := AP_Mission.mission_cmd_to_mavlink_int cmd {}
        let p := { p with mission_type := 0, current := if cmd.id == w.mission._nav_cmd.index then 1 else p.current }
        out.putStrLn s!"item {q.seq} {hexOf (itemBytes p)} {ok} {ok2}"
  return r

def main (args : List String) : IO UInt32 := do
  let img ← IO.FS.readBinFile args[0]!
  let lines := (← IO.FS.readFile args[1]!).splitOn "\n"
  let out ← IO.getStdout
  let total := ((lines[0]!.splitOn " ")[1]!).toNat!
  let mut w := Mission_lib.World.init
  -- AP_Param's load at boot: MIS_TOTAL (a parameter held as state, --param-ext)
  w := { w with mission := { w.mission with _cmd_total := { _value := total.toUInt16.toInt16 } } }
  let (s, hs) := Mission_lib.AP_Mission.init w.mission w w.mission'inp img.data
  w := { w with mission := s }
  out.putStrLn s!"init: MIS_TOTAL {total}, num_commands {Mission_lib.AP_Mission.num_commands s}, num_commands_max {Mission_lib.AP_Mission.num_commands_max s}"
  let mut r : RT := { w := w, hs := hs }
  let mut homes := 0
  for l in lines.drop 1 do
    let t := l.splitOn " "
    if t[0]! == "home" then
      -- AP_AHRS::set_home: `_home` set (the `get_home` input), then the mission's home record (AP_AHRS.cpp:1787)
      let loc : Mission_lib.Location.State := { lat := t[2]!.toInt!.toInt32, lng := t[3]!.toInt!.toInt32, alt := t[4]!.toInt!.toInt32 }
      let w1 := { r.w with mission'inp := { r.w.mission'inp with get_home := loc } }
      let (s, hs) := Mission_lib.AP_Mission.write_home_to_storage w1.mission w1 w1.mission'inp r.hs
      r := { r with w := { w1 with mission := s }, hs := hs }
      homes := homes + 1
    else if t[0]! == "up" then
      for b in hexBytes t[3]! do
        let (m, st, bufs, sts, res) := Mavlink_lib.mavlink_parse_char 0 b r.msg r.st r.bufs r.sts
        r := { r with msg := m, st := st, bufs := bufs, sts := sts }
        if res == 1 then
          r ← handle r m out
      if t[2]! == ((lines.getLast!.splitOn " ").getD 1 "x") || some t[2]! == ((lines.find? (·.startsWith "mark ")).map (fun x => (x.splitOn " ")[1]!)) then
        out.putStrLn s!"storage_mark {hexOf r.hs}"
  out.putStrLn s!"home records written: {homes}"
  out.putStrLn s!"storage_end {hexOf r.hs}"
  return 0
