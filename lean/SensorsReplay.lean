import Sensors_lib
import SensorsReplayParams

/-!
The replay of the sensor front ends' World (ardupilot/out/Sensors) on a recorded flight (README.md, "Phase 3:
sensor front ends and AP_Param"): a harness, not a translation. `ardupilot/sensors_replay.py` writes the
commands from the flight's input lines and its reference estimation output (`copter_ref --est`): the
parameters the vehicle loaded at boot, the input records, where the vehicle consumed a line outside the front
ends (a step: `est_scheduler.delay_microseconds 1`), where it called the front ends (the stand-ins' events and
the scheduler's task list of the reference), with the values the rest of the vehicle gave them; this program
runs them on the World and prints, per line of the flight, the front ends' state as the reference's probe
prints it (`baro=`, `mag=`, `ev=`).
-/

open FloatLib.Floats (Binary32 Binary64)
open Sensors_lib

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0
def hex (width : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) (Char.ofNat 48)) ++ s
def f32 (s : String) : Binary32 := Binary32.ofBits (UInt32.ofNat (hexNat s))
def f64 (s : String) : Binary64 := Binary64.ofBits (UInt64.ofNat (hexNat s))
def nat (s : String) : Nat := s.toNat?.getD 0
def int (s : String) : Int := s.toInt?.getD 0
def outF (x : Binary32) : String := hex 8 (Binary32.toBits x).toNat
def outB (b : Bool) : String := if b then "1" else "0"
def outV (v : Vector3f.State) : String := outF v.x ++ "," ++ outF v.y ++ "," ++ outF v.z
/-- `Location::get_alt_frame` (AP_Common/Location.cpp:128-146) on the flags, as the probe's `putloc` prints it. -/
def outLoc (l : Location.State) : String :=
  let frame := if l.terrain_alt != 0 then 3 else if l.origin_alt != 0 then 2 else if l.relative_alt != 0 then 1 else 0
  toString l.lat.toInt ++ "," ++ toString l.lng.toInt ++ "," ++ toString l.alt.toInt ++ "," ++ toString frame

/-- An input record from the command's tokens: t, the two IMUs' sample counts, the 16 accel and 16 gyro
samples (x y z each), baro flag, pressure, temperature, mag flag, field, gps flag and its six doubles. -/
def record (t : Array String) : EstRecord := Id.run do
  let mut r : EstRecord := {}
  r := { r with t_us := UInt64.ofNat (nat t[1]!), imu_n := #[UInt8.ofNat (nat t[2]!), UInt8.ofNat (nat t[3]!)] }
  let mut k := 4
  let mut acc : Array Vector3f.State := #[]
  let mut gyr : Array Vector3f.State := #[]
  for _ in [0:16] do
    acc := acc.push { x := f32 t[k]!, y := f32 t[k+1]!, z := f32 t[k+2]! }
    gyr := gyr.push { x := f32 t[k+3]!, y := f32 t[k+4]!, z := f32 t[k+5]! }
    k := k + 6
  r := { r with accel := acc, gyro := gyr }
  r := { r with baro := t[k]! == "1", baro_pa := f32 t[k+1]!, baro_degc := f32 t[k+2]! }
  r := { r with mag := t[k+3]! == "1", mag_mgauss := { x := f32 t[k+4]!, y := f32 t[k+5]!, z := f32 t[k+6]! } }
  r := { r with gps := t[k+7]! == "1", gps_lat_deg := f64 t[k+8]!, gps_lon_deg := f64 t[k+9]!, gps_alt_m := f64 t[k+10]!,
                gps_vn := f64 t[k+11]!, gps_ve := f64 t[k+12]!, gps_vd := f64 t[k+13]! }
  return r

def location (ok lat lng alt : String) : Location.State × Bool :=
  ({ lat := Int32.ofInt (int lat), lng := Int32.ofInt (int lng), alt := Int32.ofInt (int alt) }, ok == "1")

/-- The front ends' state as the reference's probe prints it (reference/hal/est_probe.cpp, put_front_ends). -/
def frontEnds (w : World) : String := Id.run do
  let b := w.barometer
  let n := AP_Baro.num_instances b
  let mut out := " baro=" ++ toString n.toNat
  if n > 0 then
    out := out ++ "," ++ outB (AP_Baro.healthy_uint8_t b 0) ++ "," ++ outF (AP_Baro.get_pressure_uint8_t b 0) ++ "," ++
      outF (AP_Baro.get_temperature_uint8_t b 0) ++ "," ++ outF (AP_Baro.get_altitude_uint8_t b 0) ++ "," ++
      outF (AP_Baro.get_ground_pressure_uint8_t b 0) ++ "," ++ toString (AP_Baro.get_last_update_uint8_t b 0).toNat
  let c := w.compass
  let m := Compass.get_count c
  out := out ++ " mag=" ++ toString m.toNat
  if m > 0 then
    let f := Compass.get_field_uint8_t c 0
    let o := Compass.get_offsets_uint8_t c 0
    out := out ++ "," ++ outB (Compass.healthy_uint8_t c 0) ++ "," ++ outF f.x ++ "," ++ outF f.y ++ "," ++ outF f.z ++ "," ++
      toString (Compass.last_update_usec_uint8_t c 0).toNat ++ "," ++ outF o.x ++ "," ++ outF o.y ++ "," ++ outF o.z ++ "," ++
      toString (c._state._priv_instance[0]!.dev_id._value).toNat
  -- AP_InertialSensor (est_probe.cpp: `ins=`, `imu<i>=`)
  let ins := w.ins
  out := out ++ " ins=" ++ toString (AP_InertialSensor.get_gyro_count ins).toNat ++ "," ++ toString (AP_InertialSensor.get_accel_count ins).toNat ++
    "," ++ toString (AP_InertialSensor.get_first_usable_gyro ins).toNat ++ "," ++ toString (AP_InertialSensor.get_first_usable_accel ins).toNat ++
    "," ++ outB (AP_InertialSensor.calibrating ins) ++ "," ++ outF (AP_InertialSensor.get_delta_time ins) ++
    "," ++ toString (AP_InertialSensor.get_last_update_usec ins).toNat ++ "," ++ outB ins._have_sample ++
    "," ++ toString ins._next_sample_usec.toNat ++ "," ++ toString ins._last_sample_usec.toNat
  let nimu := max (AP_InertialSensor.get_gyro_count ins).toNat (AP_InertialSensor.get_accel_count ins).toNat
  for i in [0:nimu] do
    let iu := UInt8.ofNat i
    let (dang, dang_dt, dang_ok) := AP_InertialSensor.get_delta_angle_uint8_t_Vector3f_float ins iu {} (Binary32.ofBits 0)
    let (dvel, dvel_dt, dvel_ok) := AP_InertialSensor.get_delta_velocity_uint8_t_Vector3f_float ins iu {} (Binary32.ofBits 0)
    out := out ++ " imu" ++ toString i ++ "=" ++ outV (AP_InertialSensor.get_accel_uint8_t ins iu) ++ "," ++ outV (AP_InertialSensor.get_gyro_uint8_t ins iu) ++
      "," ++ outV dang ++ "," ++ outF dang_dt ++ "," ++ outB dang_ok ++ "," ++ outV dvel ++ "," ++ outF dvel_dt ++ "," ++ outB dvel_ok ++
      "," ++ outB (AP_InertialSensor.get_accel_health_uint8_t ins iu) ++ "," ++ outB (AP_InertialSensor.get_gyro_health_uint8_t ins iu) ++
      "," ++ outB (AP_InertialSensor.gyro_calibrated_ok ins iu) ++ "," ++ outV (AP_InertialSensor.get_gyro_offsets_uint8_t ins iu) ++
      "," ++ outV (AP_InertialSensor.get_accel_offsets_uint8_t ins iu)
  -- AP_GPS (`gps=`, `gps<i>=`)
  let g := w.gps
  out := out ++ " gps=" ++ toString (AP_GPS.num_sensors g).toNat ++ "," ++ toString (AP_GPS.primary_sensor g).toNat
  for i in [0:2] do
    let iu := UInt8.ofNat i
    let (hacc, hok) := AP_GPS.horizontal_accuracy_uint8_t_float g iu (Binary32.ofBits 0)
    let (vacc, vok) := AP_GPS.vertical_accuracy_uint8_t_float g iu (Binary32.ofBits 0)
    let (sacc, sok) := AP_GPS.speed_accuracy_uint8_t_float g iu (Binary32.ofBits 0)
    let (lag, lok) := AP_GPS.get_lag_uint8_t_float g w iu (Binary32.ofBits 0)
    out := out ++ " gps" ++ toString i ++ "=" ++ toString (AP_GPS_FixType.toInt (AP_GPS.status_uint8_t g iu)).toNat ++ "," ++ outLoc (AP_GPS.location_uint8_t g iu) ++
      "," ++ outV (AP_GPS.velocity_uint8_t g iu) ++ "," ++ outF (AP_GPS.ground_speed_uint8_t g iu) ++ "," ++ outF (AP_GPS.ground_course_uint8_t g iu) ++
      "," ++ toString (AP_GPS.get_hdop_uint8_t g iu).toNat ++ "," ++ toString (AP_GPS.get_vdop_uint8_t g iu).toNat ++ "," ++ toString (AP_GPS.num_sats_uint8_t g iu).toNat ++
      "," ++ outB hok ++ "," ++ outF hacc ++ "," ++ outB vok ++ "," ++ outF vacc ++ "," ++ outB sok ++ "," ++ outF sacc ++
      "," ++ toString (AP_GPS.time_week_uint8_t g iu).toNat ++ "," ++ toString (AP_GPS.time_week_ms_uint8_t g iu).toNat ++
      "," ++ toString (AP_GPS.last_message_time_ms_uint8_t g iu).toNat ++ "," ++ toString (AP_GPS.last_fix_time_ms_uint8_t g iu).toNat ++
      "," ++ outB (AP_GPS.have_vertical_velocity_uint8_t g iu) ++ "," ++ outB lok ++ "," ++ outF lag
  -- the stand-ins' events: the barometer's and compass's (1, 2, 4) as `ev=`, the IMU's (8) as `evx=` (shifted)
  return out ++ " ev=" ++ toString (w.est_scheduler._events.toNat % 8) ++ " evx=" ++ toString (w.est_scheduler._events.toNat / 8)

def run1 (w : World) (o : Outputs) (t : Array String) : World × Outputs × Option String := Id.run do
  let mut w := w
  let mut o := o
  match t[0]! with
  | "F" =>
    let (s, _) := EstScheduler.feed w.est_scheduler (record t)
    w := { w with est_scheduler := s }
  | "S" =>
    -- the vehicle consumes line k outside the front ends: unless a front-end call consumed it already
    let k := nat t[1]!
    for _ in [0:k] do
      if w.est_scheduler._lines.toNat ≥ k || w.est_scheduler._exhausted then break
      let (s, w') := EstScheduler.delay_microseconds w.est_scheduler w 1
      w := { w' with est_scheduler := s }
  | "P" => w := setParam w t[1]! t[2]!
  | "BI" =>
    let (s, w') := AP_Baro.init w.barometer w
    w := { w' with barometer := s }
  | "CI" =>
    let (s, w', o') := Compass.init w.compass w o w.compass'inp
    w := { w' with compass := s }
    o := o'
  | "BC" =>
    let (s, w', o') := AP_Baro.calibrate w.barometer w o w.barometer'inp true
    w := { w' with barometer := s }
    o := o'
  | "BU" =>
    let (loc, ok) := location t[2]! t[3]! t[4]! t[5]!
    w := { w with barometer'inp := { w.barometer'inp with get_soft_armed := t[1]! == "1", get_origin := ok, get_origin_ret := loc } }
    let (s, w', o') := AP_Baro.update w.barometer w o w.barometer'inp
    w := { w' with barometer := s }
    o := o'
  | "GI" =>
    -- gps.init (Copter::init_ardupilot, right before compass.init): GPS1_TYPE is in the storage image (configured),
    -- AP_SerialManager finds the GPS protocol on SERIAL3 and SERIAL4 (their default protocol)
    w := { w with gps'inp := { w.gps'inp with params_0_type_configured := true, find_serial_found_SerialProtocol_GPS_at1 := #[true, true] } }
    w := { w with gps := AP_GPS.init w.gps w.gps'inp }
  | "II" =>
    -- ins.init(loop rate) (Copter::startup_INS_ground), with the gyro calibration's delays; the gyro and accel ids
    -- were stored (`P` of a non-zero id: AP_Param::load finds them), no watchdog reset
    w := { w with ins'inp := { w.ins'inp with gyro_id__gyro_count_loaded := t[2]! == "1", accel_id__accel_count_loaded := t[3]! == "1",
                                              was_watchdog_reset := false } }
    let (s, w', o') := AP_InertialSensor.init w.ins w o w.ins'inp (UInt16.ofNat (nat t[1]!))
    w := { w' with ins := s }
    o := o'
  | "WS" =>
    let (s, w') := AP_InertialSensor.wait_for_sample w.ins w
    w := { w' with ins := s }
  | "A" =>
    -- the armed flag as the IMU back end (sensors_converging, in its timer process and update) and AP_RTC (the GPS
    -- time) read it: the vehicle's state at the end of the previous step
    w := { w with heap'AP_InertialSensor_SITL'inp := { w.heap'AP_InertialSensor_SITL'inp with get_soft_armed := t[1]! == "1" },
                  rtc'inp := { w.rtc'inp with get_soft_armed := t[1]! == "1" } }
  | "IU" =>
    let (s, w') := AP_InertialSensor.update w.ins w
    w := { w' with ins := s }
  | "GU" =>
    let (s, w', o') := AP_GPS.update w.gps w o
    w := { w' with gps := s }
    o := o'
  | "CT" => w := { w with compass := Compass.set_throttle w.compass (f32 t[1]!) }
  | "CV" => w := { w with compass := Compass.set_voltage w.compass (f32 t[1]!) }
  | "CR" =>
    let (loc, ok) := location t[1]! t[2]! t[3]! t[4]!
    w := { w with compass'inp := { w.compass'inp with get_location := ok, get_location_loc := loc } }
    let (s, w', _) := Compass.read w.compass w w.compass'inp
    w := { w' with compass := s }
  | "E" => return (w, #[], some (t[1]! ++ " t=" ++ t[2]! ++ " " ++ toString w.est_scheduler._lines.toNat ++ frontEnds w))   -- (the output log is not compared: emptied)
  | _ => pure ()
  return (w, o, none)

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (w : World) (o : Outputs) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let t := (((line.trimAscii.toString).splitOn " ").filter (· ≠ "")).toArray
  let (w, o, r) := run1 w o t
  if let some s := r then out.putStrLn s
  loop h out w o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout) World.init #[]
