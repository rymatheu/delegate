import ArduLean.Musl.cosf
import ArduLean.Estimator.libraries.AP_Math.AP_Math

/-!
ArduPilot `libraries/AP_Common`, part 1 of 3. Sources: `libraries/AP_Common/Location.cpp`, `libraries/AP_Common/TSIndex.h`, `libraries/AP_Common/Location.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Location

/-- State of C++ `Location` (`AP_Common/Location.h:7-220`): its data members. -/
structure State where
  /-- `uint8_t relative_alt : 1` of `Location` (`AP_Common/Location.h:11`). -/
  relative_alt : UInt8 := (0 : UInt8)
  /-- `uint8_t loiter_ccw : 1` of `Location` (`AP_Common/Location.h:12`). -/
  loiter_ccw : UInt8 := (0 : UInt8)
  /-- `uint8_t terrain_alt : 1` of `Location` (`AP_Common/Location.h:13`). -/
  terrain_alt : UInt8 := (0 : UInt8)
  /-- `uint8_t origin_alt : 1` of `Location` (`AP_Common/Location.h:14`). -/
  origin_alt : UInt8 := (0 : UInt8)
  /-- `uint8_t loiter_xtrack : 1` of `Location` (`AP_Common/Location.h:15`). -/
  loiter_xtrack : UInt8 := (0 : UInt8)
  /-- `int32_t alt` of `Location` (`AP_Common/Location.h:18`). -/
  alt : Int32 := (0 : Int32)
  /-- `int32_t lat` of `Location` (`AP_Common/Location.h:19`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `Location` (`AP_Common/Location.h:20`). -/
  lng : Int32 := (0 : Int32)
deriving Inhabited

end Location

namespace Location

/-- C++ `void Location::copy_alt_from(const Location & other)`, `AP_Common/Location.cpp:119-125`. -/
def copy_alt_from (s : State) (other : Location.State) : State := Id.run do
  let mut s := s
  s := { s with alt := other.alt }
  s := { s with relative_alt := other.relative_alt &&& (1 : UInt8) }
  s := { s with terrain_alt := other.terrain_alt &&& (1 : UInt8) }
  s := { s with origin_alt := other.origin_alt &&& (1 : UInt8) }
  return s

end Location

namespace typesafe_index_unsigned_char_TAG_Priority

/-- State of C++ `typesafe_index<unsigned char, TAG_Priority>` (`AP_Common/TSIndex.h:27-99`): its data members. -/
structure State where
  /-- `unsigned char p` of `typesafe_index<unsigned char, TAG_Priority>` (`AP_Common/TSIndex.h:98`). -/
  p : UInt8 := (0 : UInt8)
deriving Inhabited

end typesafe_index_unsigned_char_TAG_Priority

namespace RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority

/-- State of C++ `RestrictIDTypeArray<unsigned int, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:105-118`): its data members. -/
structure State where
  /-- `unsigned int _priv_instance[3]` of `RestrictIDTypeArray<unsigned int, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:108`). -/
  _priv_instance : Array UInt32 := Array.replicate 3 (0 : UInt32)
deriving Inhabited

end RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority

namespace typesafe_index_unsigned_char_TAG_StateIndex

/-- State of C++ `typesafe_index<unsigned char, TAG_StateIndex>` (`AP_Common/TSIndex.h:27-99`): its data members. -/
structure State where
  /-- `unsigned char p` of `typesafe_index<unsigned char, TAG_StateIndex>` (`AP_Common/TSIndex.h:98`). -/
  p : UInt8 := (0 : UInt8)
deriving Inhabited

end typesafe_index_unsigned_char_TAG_StateIndex

namespace typesafe_index_unsigned_char_TAG_Priority

/-- C++ `typesafe_index<unsigned char, TAG_Priority>::typesafe_index(unsigned char i)`, `AP_Common/TSIndex.h:30`. -/
def init (i : UInt8 := (0 : UInt8)) : State := Id.run do
  let mut s : State := {}
  s := { s with p := i }
  return s

end typesafe_index_unsigned_char_TAG_Priority

namespace typesafe_index_unsigned_char_TAG_StateIndex

/-- C++ `unsigned char typesafe_index<unsigned char, TAG_StateIndex>::get_int() const`, `AP_Common/TSIndex.h:37-40`. -/
def get_int (s : State) : UInt8 := Id.run do
  return s.p

/-- C++ `typesafe_index<unsigned char, TAG_StateIndex>::typesafe_index(unsigned char i)`, `AP_Common/TSIndex.h:30`. -/
def init (i : UInt8 := (0 : UInt8)) : State := Id.run do
  let mut s : State := {}
  s := { s with p := i }
  return s

/-- C++ `bool typesafe_index<unsigned char, TAG_StateIndex>::operator<(const unsigned char & val) const`, `AP_Common/TSIndex.h:57-60`. -/
def op_lt (s : State) (val : UInt8) : Bool := Id.run do
  return (decide (UInt32.toInt32 (UInt8.toUInt32 s.p) < UInt32.toInt32 (UInt8.toUInt32 val)))

-- not read in the Lean: unnamed'0
set_option linter.unusedVariables false in
/-- C++ `typesafe_index<unsigned char, TAG_StateIndex> typesafe_index<unsigned char, TAG_StateIndex>::operator++(int )`, `AP_Common/TSIndex.h:47-50`. -/
def op_inc_int32_t (s : State) (unnamed'0 : Int32) : State × typesafe_index_unsigned_char_TAG_StateIndex.State := Id.run do
  let mut s := s
  let t'1 := s.p
  s := { s with p := s.p + (1 : UInt8) }
  return (s, typesafe_index_unsigned_char_TAG_StateIndex.init t'1)

end typesafe_index_unsigned_char_TAG_StateIndex

namespace typesafe_index_unsigned_char_TAG_Priority

/-- C++ `unsigned char typesafe_index<unsigned char, TAG_Priority>::get_int() const`, `AP_Common/TSIndex.h:37-40`. -/
def get_int (s : State) : UInt8 := Id.run do
  return s.p

end typesafe_index_unsigned_char_TAG_Priority

namespace RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority

/-- C++ `const unsigned int & RestrictIDTypeArray<unsigned int, 3, typesafe_index<unsigned char, TAG_Priority>>::operator[](const typesafe_index<unsigned char, TAG_Priority> & index) const`, `AP_Common/TSIndex.h:114-117`. -/
def op_index (s : State) (index : typesafe_index_unsigned_char_TAG_Priority.State) : UInt32 := Id.run do
  return s._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int index)]!

end RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority

namespace typesafe_index_unsigned_char_TAG_StateIndex

/-- C++ `bool typesafe_index<unsigned char, TAG_StateIndex>::operator>=(const unsigned char & val) const`, `AP_Common/TSIndex.h:67-70`. -/
def op_ge (s : State) (val : UInt8) : Bool := Id.run do
  return (decide (UInt32.toInt32 (UInt8.toUInt32 s.p) ≥ UInt32.toInt32 (UInt8.toUInt32 val)))

end typesafe_index_unsigned_char_TAG_StateIndex

namespace Location

/-- C++ `void Location::zero()`, `AP_Common/Location.cpp:18-21`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { relative_alt := (0 : UInt8), loiter_ccw := (0 : UInt8), terrain_alt := (0 : UInt8), origin_alt := (0 : UInt8), loiter_xtrack := (0 : UInt8), alt := (0 : Int32), lat := (0 : Int32), lng := (0 : Int32) }
  return s

/-- C++ `enum class Location::AltFrame`, `AP_Common/Location.h:23-28`. -/
inductive AltFrame where
  | ABSOLUTE
  | ABOVE_HOME
  | ABOVE_ORIGIN
  | ABOVE_TERRAIN
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `Location::AltFrame` (underlying type `int32_t`). -/
def AltFrame.toInt : AltFrame → Int32
  | .ABSOLUTE => (0 : Int32)
  | .ABOVE_HOME => (1 : Int32)
  | .ABOVE_ORIGIN => (2 : Int32)
  | .ABOVE_TERRAIN => (3 : Int32)

/-- C++ `void Location::set_alt_cm(int32_t alt_cm, AltFrame frame)`, `AP_Common/Location.cpp:83-106`. -/
def set_alt_cm (s : State) (alt_cm : Int32) (frame : Location.AltFrame) : State := Id.run do
  let mut s := s
  s := { s with alt := alt_cm }
  s := { s with relative_alt := (if false then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with terrain_alt := (if false then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with origin_alt := (if false then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  match frame with
  | .ABSOLUTE =>
    pure ()
  | .ABOVE_HOME =>
    s := { s with relative_alt := (if true then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  | .ABOVE_ORIGIN =>
    s := { s with origin_alt := (if true then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  | .ABOVE_TERRAIN =>
    s := { s with relative_alt := (if true then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
    s := { s with terrain_alt := (if true then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  return s

/-- C++ `Location::Location(int32_t latitude, int32_t longitude, int32_t alt_in_cm, AltFrame frame)`, `AP_Common/Location.cpp:24-33`. -/
def init_int32_t3_AltFrame (latitude : Int32) (longitude : Int32) (alt_in_cm : Int32) (frame : Location.AltFrame) : State := Id.run do
  let mut s : State := {}
  pure ()  -- C++ `do`: a compile-time size check (AP_Common's ASSERT_STORAGE_SIZE)
  s := zero s
  s := { s with lat := latitude }
  s := { s with lng := longitude }
  s := set_alt_cm s alt_in_cm frame
  return s

end Location

namespace Location

/-- C++ `Location::Location()`, `AP_Common/Location.h:31`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := zero s
  return s

end Location

namespace Location

/-- C++ `bool Location::initialised() const`, `AP_Common/Location.h:198`. -/
def initialised (s : State) : Bool := Id.run do
  return (s.lat != (0 : Int32) || s.lng != (0 : Int32) || s.alt != (0 : Int32))

end Location

namespace Location

/-- C++ `static ftype Location::longitude_scale(int32_t lat)`, `AP_Common/Location.cpp:528-532`. -/
def longitude_scale (lat : Int32) : Binary64 := Id.run do
  let scale : Binary64 := Binary32.toBinary64 (Musl.cosf.cosf (Int32.toBinary32 lat * ((Binary32.ofBits 0x33d6bf95 /- (float)944473296573929/9444732965739290427392 -/) * ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) / (Binary32.ofBits 0x43340000 /- 180 -/)))))
  return Estimator_lib.MAX_double_float scale (Binary32.ofBits 0x3c23d70a /- 0.01 -/)

/-- C++ `static int32_t Location::diff_longitude(int32_t lon1, int32_t lon2)`, `AP_Common/Location.cpp:650-663`. -/
def diff_longitude (lon1 lon2 : Int32) : Int32 := Id.run do
  if (Int32.toUInt32 lon1 &&& (2147483648 : UInt32)) == (Int32.toUInt32 lon2 &&& (2147483648 : UInt32)) then
    return lon1 - lon2
  let mut dlon : Int64 := Int32.toInt64 lon1 - Int32.toInt64 lon2
  if dlon > (1800000000 : Int64) then
    dlon := dlon - (3600000000 : Int64)
  else if dlon < -(1800000000 : Int64) then
    dlon := dlon + (3600000000 : Int64)
  return Int64.toInt32 dlon

/-- C++ `static const float Location::LOCATION_SCALING_FACTOR`, `AP_Common/Location.h:217`. -/
def LOCATION_SCALING_FACTOR : Binary32 := (Binary32.ofBits 0x3c366282 /- (float)6417094514661347/576460752303423488 -/)

/-- C++ `ftype Location::get_distance(const Location & loc2) const`, `AP_Common/Location.cpp:369-374`. -/
def get_distance (s : State) (loc2 : Location.State) : Binary64 := Id.run do
  let dlat : Binary64 := Int32.toBinary64 (loc2.lat - s.lat)
  let dlng : Binary64 := (Int32.toBinary64 (diff_longitude loc2.lng s.lng)) * longitude_scale ((s.lat + loc2.lat) / (2 : Int32))
  return Estimator_lib.norm_double2 dlat dlng * Binary32.toBinary64 LOCATION_SCALING_FACTOR

end Location

namespace Location

/-- C++ `static int32_t Location::wrap_longitude(int64_t lon)`, `AP_Common/Location.cpp:637-645`. -/
def wrap_longitude (lon : Int64) : Int32 := Id.run do
  let mut lon := lon
  if lon > (1800000000 : Int64) then
    lon := Int32.toInt64 (Int64.toInt32 (lon - (3600000000 : Int64)))
  else if lon < -(1800000000 : Int64) then
    lon := Int32.toInt64 (Int64.toInt32 (lon + (3600000000 : Int64)))
  return Int64.toInt32 lon

/-- C++ `static int32_t Location::limit_lattitude(int32_t lat)`, `AP_Common/Location.cpp:668-676`. -/
def limit_lattitude (lat : Int32) : Int32 := Id.run do
  let mut lat := lat
  if Int32.toInt64 lat > (900000000 : Int64) then
    lat := Int64.toInt32 ((1800000000 : Int64) - Int32.toInt64 lat)
  else if Int32.toInt64 lat < -(900000000 : Int64) then
    lat := Int64.toInt32 (-((1800000000 : Int64) + Int32.toInt64 lat))
  return lat

/-- C++ `static const float Location::LOCATION_SCALING_FACTOR_INV`, `AP_Common/Location.h:219`. -/
def LOCATION_SCALING_FACTOR_INV : Binary32 := (Binary32.ofBits 0x42b3aa02 /- (float)6321368512591417/70368744177664 -/)

/-- C++ `static void Location::offset_latlng(int32_t & lat, int32_t & lng, ftype ofs_north, ftype ofs_east)`, `AP_Common/Location.cpp:480-487`. -/
def offset_latlng (lat lng : Int32) (ofs_north ofs_east : Binary64) : Int32 × Int32 := Id.run do
  let mut lat := lat
  let mut lng := lng
  let dlat : Int32 := Binary64.toInt32 (ofs_north * Binary32.toBinary64 LOCATION_SCALING_FACTOR_INV)
  let dlng : Int64 := Binary64.toInt64 ((ofs_east * Binary32.toBinary64 LOCATION_SCALING_FACTOR_INV) / longitude_scale (lat + dlat / (2 : Int32)))
  lat := lat + dlat
  lat := limit_lattitude lat
  lng := wrap_longitude (dlng + Int32.toInt64 lng)
  return (lat, lng)

end Location

namespace Location

/-- C++ `Vector2F Location::get_distance_NE_ftype(const Location & loc2) const`, `AP_Common/Location.cpp:473-477`. -/
def get_distance_NE_ftype (s : State) (loc2 : Location.State) : Vector2p.State := Id.run do
  return Vector2p.init_double2 (Int32.toBinary64 (loc2.lat - s.lat) * Binary32.toBinary64 LOCATION_SCALING_FACTOR) (Int32.toBinary64 (diff_longitude loc2.lng s.lng) * Binary32.toBinary64 LOCATION_SCALING_FACTOR * longitude_scale ((s.lat + loc2.lat) / (2 : Int32)))

end Location

/-- C++ `const Location definitely_zero`, `AP_Common/Location.cpp:12`. -/
def definitely_zero : Location.State := Location.init_void

namespace Location

/-- C++ `bool Location::is_zero() const`, `AP_Common/Location.cpp:13-16`. -/
def is_zero (s : State) : Bool := Id.run do
  let t'1 := Estimator_lib.definitely_zero
  return !((if s.relative_alt == t'1.relative_alt && s.loiter_ccw == t'1.loiter_ccw && s.terrain_alt == t'1.terrain_alt && s.origin_alt == t'1.origin_alt && s.loiter_xtrack == t'1.loiter_xtrack && s.alt == t'1.alt && s.lat == t'1.lat && s.lng == t'1.lng then (0 : Int32) else (1 : Int32)) != (0 : Int32))

end Location

namespace typesafe_index_unsigned_char_TAG_Priority

/-- C++ `bool typesafe_index<unsigned char, TAG_Priority>::operator<(const unsigned char & val) const`, `AP_Common/TSIndex.h:57-60`. -/
def op_lt (s : State) (val : UInt8) : Bool := Id.run do
  return (decide (UInt32.toInt32 (UInt8.toUInt32 s.p) < UInt32.toInt32 (UInt8.toUInt32 val)))

-- not read in the Lean: unnamed'0
set_option linter.unusedVariables false in
/-- C++ `typesafe_index<unsigned char, TAG_Priority> typesafe_index<unsigned char, TAG_Priority>::operator++(int )`, `AP_Common/TSIndex.h:47-50`. -/
def op_inc_int32_t (s : State) (unnamed'0 : Int32) : State × typesafe_index_unsigned_char_TAG_Priority.State := Id.run do
  let mut s := s
  let t'1 := s.p
  s := { s with p := s.p + (1 : UInt8) }
  return (s, typesafe_index_unsigned_char_TAG_Priority.init t'1)

/-- C++ `unsigned char typesafe_index<unsigned char, TAG_Priority>::operator unsigned char() const`, `AP_Common/TSIndex.h:88-91`. -/
def op_to_unsigned_char (s : State) : UInt8 := Id.run do
  return s.p

end typesafe_index_unsigned_char_TAG_Priority

namespace Location

/-- C++ `void Location::offset(ftype ofs_north, ftype ofs_east)`, `AP_Common/Location.cpp:490-493`. -/
def offset_double2 (s : State) (ofs_north : Binary64) (ofs_east : Binary64) : State := Id.run do
  let mut s := s
  let (t'1, t'2) := offset_latlng s.lat s.lng ofs_north ofs_east
  s := { s with lat := t'1 }
  s := { s with lng := t'2 }
  return s

end Location

namespace Location

/-- C++ `Vector3p Location::get_distance_NED_postype(const Location & loc2) const`, `AP_Common/Location.cpp:433-438`. -/
def get_distance_NED_postype (s : State) (loc2 : Location.State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (Binary32.toBinary64 (Int32.toBinary32 (loc2.lat - s.lat) * LOCATION_SCALING_FACTOR)) (Binary32.toBinary64 (Int32.toBinary32 (diff_longitude loc2.lng s.lng) * LOCATION_SCALING_FACTOR) * longitude_scale ((s.lat + loc2.lat) / (2 : Int32))) (Binary32.toBinary64 (Int32.toBinary32 (s.alt - loc2.alt) * (Binary32.ofBits 0x3c23d70a /- 0.01 -/)))

end Location

namespace Location

/-- C++ `Vector2p Location::get_distance_NE_postype(const Location & loc2) const`, `AP_Common/Location.cpp:467-471`. -/
def get_distance_NE_postype (s : State) (loc2 : Location.State) : Vector2p.State := Id.run do
  return Vector2p.init_double2 (Int32.toBinary64 (loc2.lat - s.lat) * Binary32.toBinary64 LOCATION_SCALING_FACTOR) (Int32.toBinary64 (diff_longitude loc2.lng s.lng) * Binary32.toBinary64 LOCATION_SCALING_FACTOR * longitude_scale ((s.lat + loc2.lat) / (2 : Int32)))

end Location

namespace Location

/-- C++ `Vector3f Location::get_distance_NED(const Location & loc2) const`, `AP_Common/Location.cpp:426-431`. -/
def get_distance_NED (s : State) (loc2 : Location.State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (Int32.toBinary32 (loc2.lat - s.lat) * LOCATION_SCALING_FACTOR) (Binary64.toBinary32 (Binary32.toBinary64 (Int32.toBinary32 (diff_longitude loc2.lng s.lng) * LOCATION_SCALING_FACTOR) * longitude_scale ((s.lat + loc2.lat) / (2 : Int32)))) (Int32.toBinary32 (s.alt - loc2.alt) * (Binary32.ofBits 0x3c23d70a /- 0.01 -/))

end Location

namespace typesafe_index_unsigned_char_TAG_Priority

/-- C++ `typesafe_index<unsigned char, TAG_Priority> typesafe_index<unsigned char, TAG_Priority>::operator+(const unsigned char & val) const`, `AP_Common/TSIndex.h:93-96`. -/
def op_add (s : State) (val : UInt8) : typesafe_index_unsigned_char_TAG_Priority.State := Id.run do
  return typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s.p) + UInt32.toInt32 (UInt8.toUInt32 val))))

end typesafe_index_unsigned_char_TAG_Priority

namespace typesafe_index_unsigned_char_TAG_StateIndex

/-- C++ `void typesafe_index<unsigned char, TAG_StateIndex>::operator=(const unsigned char & val)`, `AP_Common/TSIndex.h:32-35`. -/
def op_assign (s : State) (val : UInt8) : State := Id.run do
  let mut s := s
  s := { s with p := val }
  return s

end typesafe_index_unsigned_char_TAG_StateIndex

namespace typesafe_index_unsigned_char_TAG_Priority

/-- C++ `bool typesafe_index<unsigned char, TAG_Priority>::operator>=(const unsigned char & val) const`, `AP_Common/TSIndex.h:67-70`. -/
def op_ge (s : State) (val : UInt8) : Bool := Id.run do
  return (decide (UInt32.toInt32 (UInt8.toUInt32 s.p) ≥ UInt32.toInt32 (UInt8.toUInt32 val)))

end typesafe_index_unsigned_char_TAG_Priority

namespace typesafe_index_unsigned_char_TAG_StateIndex

/-- C++ `bool typesafe_index<unsigned char, TAG_StateIndex>::operator!=(const unsigned char & val) const`, `AP_Common/TSIndex.h:78-81`. -/
def op_ne (s : State) (val : UInt8) : Bool := Id.run do
  return (UInt32.toInt32 (UInt8.toUInt32 s.p) != UInt32.toInt32 (UInt8.toUInt32 val))

/-- C++ `unsigned char typesafe_index<unsigned char, TAG_StateIndex>::operator unsigned char() const`, `AP_Common/TSIndex.h:88-91`. -/
def op_to_unsigned_char (s : State) : UInt8 := Id.run do
  return s.p

end typesafe_index_unsigned_char_TAG_StateIndex

end Estimator_lib
