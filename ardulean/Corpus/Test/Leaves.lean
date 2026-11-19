import ArduLean.Vehicle
import Corpus.Test.Edge

/-!
# Edge evaluation of the fourth increment's pure-leaf candidates (Corpus/PLAN.md, rule 6)

Each `#guard` evaluates a candidate statement before it is proved. Integer leaves: exhaustively over `UInt8` and
`UInt16`, and on the type's edges (min, max, `0`, `±1`, the listed values and their neighbors, `2^31`) for `UInt32`,
`Int32` and `Int64`. Float leaves: on `Corpus.Edge.inputs` (pairs where there are two arguments) and a sample. A
candidate that fails is a finding (`FINDINGS.md`, F19 on) and its true statement is tested next to it.
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge

namespace Corpus.Test.Leaves

def u16s : List UInt16 := (List.range 65536).map UInt16.ofNat
def u8s : List UInt8 := (List.range 256).map UInt8.ofNat

def nearU32 (l : List Nat) : List UInt32 :=
  ([0, 1, 2, 255, 256, 65535, 65536, 2^31 - 1, 2^31, 2^31 + 1, 2^32 - 1] ++ l ++ l.map (· + 1) ++ l.map (· - 1)).map
    UInt32.ofNat
def nearI32 (l : List Int) : List Int32 :=
  ([0, 1, -1, 2, -2, 255, 2^31 - 1, -2^31, -2^31 + 1, 2000, 2001, 1999, 1800000000, -1800000000, 900000000,
    -900000000, 900000001, -900000001] ++ l ++ l.map (· + 1) ++ l.map (· - 1)).map Int32.ofInt

/-! ## Membership tables (`switch` on an id) -/

def storedL : List Nat := [16, 17, 18, 19, 21, 22, 30, 31, 82, 92, 179, 188, 189, 191, 195, 201, 84, 85, 94, 5001,
  5002, 5003, 5004, 5000, 5100, 36]
#guard u16s.all fun id => Id.run (Vehicle_lib.AP_Mission.stored_in_location.pure' id) == storedL.contains id.toNat
#guard u16s.all fun id => Id.run (Vehicle_lib.AP_Mission.cmd_has_location.pure' id) == storedL.contains id.toNat
#guard u16s.all fun id => Id.run (Vehicle_lib.AP_Mission.is_landing_type_cmd.pure' 0 id) == [21, 85, 208].contains id.toNat
#guard u16s.all fun id => Id.run (Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure' 0 id) == [22, 84].contains id.toNat
#guard u8s.all fun id =>
  Id.run (Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback.pure' 0 id) == [31, 0, 73].contains id.toNat
def storesL : List Nat := [179, 201, 195, 192, 43003, 611]
#guard (nearU32 storesL).all fun c =>
  Id.run (Vehicle_lib.GCS_MAVLINK.command_long_stores_location.pure' c) == storesL.contains c.toNat
#guard (nearU32 [84]).all fun c => Id.run (Vehicle_lib.GCS_MAVLINK_Copter.command_int_only.pure' 0 c) == (c.toNat == 84)
def estopL : List Int := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 69, 70, 73, 74, 81, 82, 83, 84, 85, 30]
#guard (nearI32 (estopL ++ [160, 179])).all fun f =>
  Id.run (Vehicle_lib.SRV_Channel.should_e_stop.pure' f) == (estopL.contains f.toInt || (160 ≤ f.toInt && f.toInt ≤ 179))
#guard (nearI32 [154, 153, 165]).all fun f =>
  Id.run (Vehicle_lib.RC_Channel.init_position_on_first_radio_read.pure' 0 f) == [154, 153, 165].contains f.toInt
#guard (nearI32 [33, 40, 82, 85, 160, 179]).all fun f =>
  Id.run (Vehicle_lib.SRV_Channel.is_motor.pure' f) ==
    ((33 ≤ f.toInt && f.toInt ≤ 40) || (82 ≤ f.toInt && f.toInt ≤ 85) || (160 ≤ f.toInt && f.toInt ≤ 179))
#guard (nearI32 [0, 190]).all fun f =>
  Id.run (Vehicle_lib.SRV_Channel.valid_function'2.pure' f) == (0 ≤ f.toInt && f.toInt < 190)

/-! ## `valid_channel`: the naive statement and the true one (F19) -/

/-- Naive: `valid_channel chan ↔ chan < 16`. Fails at `chan ≥ 2^31` (a signed comparison). -/
def validNaive (c : UInt32) : Bool := Id.run (Vehicle_lib.valid_channel.pure' c) == (c.toNat < 16)
#guard !validNaive (UInt32.ofNat (2^31))
#guard (nearU32 [16]).all fun c => Id.run (Vehicle_lib.valid_channel.pure' c) == (c.toNat < 16 || 2^31 ≤ c.toNat)

/-! ## Bounds and tables over small integers -/

#guard u16s.all fun b => Id.run (Vehicle_lib.Bitmask'102.validate.pure' 0 b) == (b.toNat < 102)
#guard u16s.all fun b => Id.run (Vehicle_lib.Bitmask'190.validate.pure' 0 b) == (b.toNat < 190)
#guard u16s.all fun b => Id.run (Vehicle_lib.Bitmask'317.validate.pure' 0 b) == (b.toNat < 317)
#guard (nearU32 [255]).all fun t => (Id.run (Vehicle_lib.mavlink_msg_target_field.pure' t)).toNat == min t.toNat 255
#guard u8s.all fun c => (Id.run (Vehicle_lib.SRV_Channels.get_motor_function.pure' c)).toInt ==
  if c.toNat < 8 then 33 + c.toNat else if c.toNat < 12 then 74 + c.toNat else 148 + c.toNat
#guard (nearU32 [1, 2, 3]).all fun t => Id.run (Vehicle_lib.GCS_MAVLINK.mav_param_type.pure' t) ==
  if t.toNat = 1 then 2 else if t.toNat = 2 then 4 else if t.toNat = 3 then 6 else 9
#guard (nearU32 [0, 1, 2, 3, 4, 5, 6]).all fun t => Id.run (Vehicle_lib.AP_Param.type_size.pure' t) ==
  if t.toNat = 1 then 1 else if t.toNat = 2 then 2 else if t.toNat = 3 ∨ t.toNat = 4 then 4
  else if t.toNat = 5 then 12 else 0
#guard (nearI32 [0, 1, 2000, 2001]).all fun r =>
  (r.toInt ≤ 0 → Id.run (Vehicle_lib.AP_SerialManager.map_baudrate.pure' r) == 57600) &&
  (2000 < r.toInt → Id.run (Vehicle_lib.AP_SerialManager.map_baudrate.pure' r) == r.toUInt32)
#guard (nearI32 [0, 1, 5]).all fun v => (nearI32 [0, 5]).all fun lo => (nearI32 [0, 5]).all fun hi =>
  Id.run (Vehicle_lib.is_bounded_int32.pure' v lo hi) == (decide (lo ≤ hi) && decide (lo ≤ v) && decide (v ≤ hi))

/-! ## Addresses -/

def bases : List UInt64 := [0, 0x20000, 0x30000, 2^63, 2^64 - 1000]
#guard bases.all fun t => u8s.all fun c =>
  (Id.run (Vehicle_lib.RC_Channels_Copter.channel.pure' t c)).toNat ==
    if c.toNat < 16 then (t.toNat + 48 + 56 * c.toNat) % 2^64 else 0
#guard bases.all fun t => u8s.all fun c =>
  Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' t c) != 0
#guard bases.all fun t => u8s.all fun c =>
  Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure' t c) != 0
#guard bases.all fun t => u8s.all fun c =>
  (Id.run (Vehicle_lib.Vector3'float.operator__.pure' t c)).toNat == (t.toNat + 4 * c.toNat) % 2^64
#guard bases.all fun t => u8s.all fun c =>
  (Id.run (Vehicle_lib.AP_BattMonitor.get_cell_voltages.pure' t c)).toNat ==
    (t.toNat + 408 + 112 * (if c.toNat ≥ 9 then 0 else c.toNat)) % 2^64

/-! ## Longitude and latitude (`Location.cpp`) -/

def lons : List Int := [0, 1, -1, 1800000000, -1800000000, 1799999999, -1799999999, 900000000, -900000000,
  1234567890, -1234567890, 2^31 - 1, -2^31]
-- `diff_longitude` for valid longitudes: in `[-1.8e9, 1.8e9]` and congruent to `lon1 - lon2` modulo `3.6e9`.
#guard (lons.filter (·.natAbs ≤ 1800000000)).all fun a => (lons.filter (·.natAbs ≤ 1800000000)).all fun b =>
  let r := (Id.run (Vehicle_lib.Location.diff_longitude.pure' (Int32.ofInt a) (Int32.ofInt b))).toInt
  decide ((-1800000000 : Int) ≤ r) && r ≤ 1800000000 && (r - (a - b)) % 3600000000 == 0
#guard lons.all fun a => (Id.run (Vehicle_lib.Location.limit_lattitude.pure' (Int32.ofInt a))).toInt ==
  if a > 900000000 then 1800000000 - a else if a < -900000000 then -(1800000000 + a) else a
def wlons : List Int := lons ++ [3600000000, -3600000000, 5400000000, -5400000000, 1800000001, -1800000001,
  5399999999, -5399999999]
#guard (wlons.filter (·.natAbs ≤ 5400000000)).all fun a =>
  (Id.run (Vehicle_lib.Location.wrap_longitude.pure' (Int64.ofInt a))).toInt ==
    if a > 1800000000 then a - 3600000000 else if a < -1800000000 then a + 3600000000 else a

/-! ## Float leaves -/

#guard inputs.all fun x => Id.run (Vehicle_lib.check_lat'2.pure' x) ==
  (decide (Binary32.ofBits 0xc2b40000 ≤ x) && decide (x ≤ Binary32.ofBits 0x42b40000))
#guard inputs.all fun x => Id.run (Vehicle_lib.check_lng'2.pure' x) ==
  (decide (Binary32.ofBits 0xc3340000 ≤ x) && decide (x ≤ Binary32.ofBits 0x43340000))
#guard (inputs ++ sample 300).all fun x =>
  Id.run (Vehicle_lib.is_zero'2.pure' (Binary32.toBinary64 x)) == Id.run (Vehicle_lib.is_zero.pure' x)
#guard inputs.all fun a => inputs.all fun b => inputs.all fun c =>
  Binary32.isNaN a || Binary32.isNaN b || Binary32.isNaN c ||
    (!Binary32.isNaN (Id.run (Vehicle_lib.norm'2.pure' a b c)) &&
      decide (Binary32.ofBits 0 ≤ Id.run (Vehicle_lib.norm'2.pure' a b c)))
#guard [Int32.ofInt 0, 1, -1, 180, -180, 2^31 - 1, -2^31].all fun d =>
  Binary32.toBits (Id.run (Vehicle_lib.radians'2.pure' d)) ==
    Binary32.toBits (Id.run (Vehicle_lib.radians.pure' (Int32.toBinary32 d)))
#guard inputs.all fun a => inputs.all fun b =>
  !Binary32.isNaN a || Binary32.isNaN (Id.run (Vehicle_lib.AP_BattMonitor_Backend.calculate_mah.pure' a b))
#guard inputs.all fun p =>
  !Binary32.isNaN p || (Id.run (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p true) == 0 &&
    Id.run (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p false) == 0)
#guard Binary32.toBits (Id.run (Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' 0)) == 0

#guard (nearI32 [1, 35]).all fun m =>
  Id.run (Vehicle_lib.AP_Arming.method_is_GCS.pure' m) == [1, 35].contains m.toInt
#guard (List.range 256).all fun k =>
  let p := UInt8.ofNat k
  Id.run (Vehicle_lib.RC_Channel.string_for_aux_pos.pure' 0 p) ==
    if p = 2 then 0x18e42 else if p = 1 then 0x18e47 else if p = 0 then 0x18e4e else 0x14223

/-! ## F20 (corrected in the code): every motor output is stopped by an emergency stop -/

def motorStops (f : Int32) : Bool :=
  !Id.run (Vehicle_lib.SRV_Channel.is_motor.pure' f) || Id.run (Vehicle_lib.SRV_Channel.should_e_stop.pure' f)
#guard motorStops (Int32.ofInt 161)
#guard ((List.range 400).map (fun k => Int32.ofInt (k - 50))).all motorStops

end Corpus.Test.Leaves
