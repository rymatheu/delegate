import Estimator_lib

/-!
The estimator probe's keys (reference/hal/est_probe.cpp) printed from a World: copied from lean/EstimationReplay.lean
(its printers: `ahrsKeys`, `ekfKeys`, `frontEnds`, `vehicleKeys`, the record parser), for the one-state replay
(lean/OneStateReplay.lean), which cannot import EstimationReplay (its `main` and its ParamMemory-based `PMem`).
-/

open FloatLib.Floats (Binary32 Binary64)
open Estimator_lib

namespace EstimatorProbe

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

def outD (x : Binary64) : String := hex 16 (Binary64.toBits x).toNat
def outVp (v : Vector3p.State) : String := outD v.x ++ "," ++ outD v.y ++ "," ++ outD v.z

/-! FNV-1a 64 over the little-endian bytes of each value (est_probe.cpp's `Fnv`). -/
def fnvU (h : UInt64) (v : UInt64) (n : Nat) : UInt64 := Id.run do
  let mut h := h
  for i in [0:n] do
    h := (h ^^^ ((v >>> (8 * i).toUInt64) &&& 0xff)) * 0x100000001b3
  return h
def fnvD (h : UInt64) (x : Binary64) : UInt64 := fnvU h (Binary64.toBits x) 8
def fnvB (h : UInt64) (b : Bool) : UInt64 := fnvU h (if b then 1 else 0) 1
def fnv8 (h : UInt64) (v : UInt8) : UInt64 := fnvU h v.toUInt64 1
def fnv32 (h : UInt64) (v : UInt32) : UInt64 := fnvU h v.toUInt64 4
def fnvV (h : UInt64) (v : Vector3p.State) : UInt64 := fnvD (fnvD (fnvD h v.x) v.y) v.z
def fnvQ (h : UInt64) (q : QuaternionT_double.State) : UInt64 := fnvD (fnvD (fnvD (fnvD h q.q1) q.q2) q.q3) q.q4
def fnvOut (h : UInt64) (o : NavEKF3_core.output_elements) : UInt64 := fnvV (fnvV (fnvQ h o.quat) o.velocity) o.position
def fnvInit : UInt64 := 0xcbf29ce484222325

/-- Core k's keys (est_probe.cpp: `c<k>.x`, `.fs`, `.P`, `.out`, `.imu`, `.var`, `.gsf`). -/
def coreKeys (w : World) (k : Nat) : String := Id.run do
  let c := w.heap'NavEKF3_core[WPtr.index w.EKF3.core + k]!
  let ck := " c" ++ toString k ++ "."
  let mut out := ck ++ "x=" ++ ",".intercalate (c.statesArray.toList.map outD)
  out := out ++ ck ++ "fs=" ++ hex 8 (NavEKF3_core.getFilterStatus c 0).toNat ++ "," ++ outB c.statesInitialised
  let mut dp := fnvInit
  for x in c.Pmut do
    dp := fnvD dp x
  out := out ++ ck ++ "P=" ++ hex 16 dp.toNat
  let mut d := fnvOut (fnvOut fnvInit c.outputDataNew) c.outputDataDelayed
  d := fnvV (fnvV (fnvV d c.delAngCorrection) c.velErrintegral) c.posErrintegral
  d := fnvD (fnvD (fnvD d c.vertCompFiltState.pos) c.vertCompFiltState.vel) c.vertCompFiltState.acc
  let ob := c.storedOutput
  d := fnvB (fnv8 (fnv8 (fnv8 d ob._size) ob._oldest) ob._youngest) ob._filled
  if ob.buffer'alloc then
    for i in [0:ob._size.toNat] do
      d := fnvOut d ob.buffer[i]!
  out := out ++ ck ++ "out=" ++ hex 16 d.toNat
  let ib := c.storedIMU
  let mut di := fnvB (fnv8 (fnv8 (fnv8 fnvInit ib._size) ib._oldest) ib._youngest) ib._filled
  if ib.buffer'alloc then
    for i in [0:ib._size.toNat] do
      let e := ib.buffer[i]!
      di := fnv8 (fnv8 (fnv32 (fnvD (fnvD (fnvV (fnvV di e.delAng) e.delVel) e.delAngDT) e.delVelDT) e.time_ms) e.gyro_index) e.accel_index
  out := out ++ ck ++ "imu=" ++ hex 16 di.toNat
  let (a, b2, h2, mm, t2, _, ok) := NavEKF3_core.getVariances c (Binary32.ofBits 0) (Binary32.ofBits 0) (Binary32.ofBits 0) {} (Binary32.ofBits 0) {}
  out := out ++ ck ++ "var=" ++ outB ok ++ "," ++ outF a ++ "," ++ outF b2 ++ "," ++ outF h2 ++ "," ++ outV mm ++ "," ++ outF t2
  if c.yawEstimator != WPtr.null then
    let g := w.heap'EKFGSF_yaw[WPtr.index c.yawEstimator]!
    let (yaw, yv, nclips, ok) := EKFGSF_yaw.getYawData g (Binary64.ofBits 0) (Binary64.ofBits 0) true 0
    let mut dg := fnvD (fnvD (fnvV (fnvV fnvInit g.delta_angle) g.delta_velocity) g.angle_dt) g.velocity_dt
    for a in g.AHRS do
      dg := fnvV (fnvV (fnvV (fnvV dg a.R.a) a.R.b) a.R.c) a.gyro_bias
      dg := fnvB dg a.aligned
      dg := fnvD (fnvD (fnvD (fnvD dg a.accel_FR[0]!) a.accel_FR[1]!) a.vel_NE[0]!) a.vel_NE[1]!
      dg := fnvD (fnvB dg a.fuse_gps) a.accel_dt
    dg := fnvD (fnvD (fnvV (fnvD (fnvB dg g.ahrs_tilt_aligned) g.accel_gain) g.ahrs_accel) g.ahrs_accel_norm) g.true_airspeed
    for e in g.EKF do
      for x in e.X do dg := fnvD dg x
      for x in e.P do dg := fnvD dg x
      for x in e.S do dg := fnvD dg x
      dg := fnvD (fnvD dg e.innov[0]!) e.innov[1]!
    dg := fnvB (fnvB dg g.vel_fuse_running) g.run_ekf_gsf
    dg := fnvD (fnvD dg g.GSF.yaw) g.GSF.yaw_variance
    for x in g.GSF.weights do dg := fnvD dg x
    dg := fnv8 dg g.n_clips
    out := out ++ ck ++ "gsf=" ++ outB ok ++ "," ++ outD yaw ++ "," ++ outD yv ++ "," ++ toString nclips.toNat ++ "," ++ hex 16 dg.toNat
  return out

/-- The EKF3 keys of the probe: `primary`, `ncores`, and while there are cores `gbias`, `abias`, `var` (the primary
core's, through the front end) and each core's keys. -/
def ekfKeys (w : World) : String := Id.run do
  let e := w.EKF3
  let ncores := if e.core != WPtr.null then e.num_cores.toNat else 0
  let mut out := " primary=" ++ toString (NavEKF3.getPrimaryCoreIndex e).toInt ++ " ncores=" ++ toString ncores
  if e.core != WPtr.null then
    let gb := NavEKF3.getGyroBias e w (-1) {}
    let ab := NavEKF3.getAccelBias e w (-1) {}
    out := out ++ " gbias=" ++ outV gb ++ " abias=" ++ outV ab
    let (vv, pv, hv, mv, tv, off, ok) := NavEKF3.getVariances e w (Binary32.ofBits 0) (Binary32.ofBits 0) (Binary32.ofBits 0) {} (Binary32.ofBits 0) {}
    out := out ++ " var=" ++ outB ok ++ "," ++ outF vv ++ "," ++ outF pv ++ "," ++ outF hv ++ "," ++ outV mv ++ "," ++ outF tv ++ "," ++ outF off.x ++ "," ++ outF off.y
    for k in [0:ncores] do
      out := out ++ coreKeys w k
  return out


/-- The AP_AHRS keys of the probe (est_probe.cpp, "AP_AHRS outputs"): `q rpy dcm vel pos loc gyro accef resets healthy
initialised origin ekf fs`, through the translated getters, with the probe's initial values of the out-parameters
(`Quaternion q;` is (1, 0, 0, 0), the others zero). -/
def ahrsKeys (w : World) : String := Id.run do
  let a := w.ahrs
  let (q, qok) := AP_AHRS.get_quaternion a Quaternion.init_void
  let mut out := " q=" ++ outB qok ++ "," ++ outF q.q1 ++ "," ++ outF q.q2 ++ "," ++ outF q.q3 ++ "," ++ outF q.q4
  out := out ++ " rpy=" ++ outF (AP_AHRS.get_roll_rad a) ++ "," ++ outF (AP_AHRS.get_pitch_rad a) ++ "," ++ outF (AP_AHRS.get_yaw_rad a)
  let m := AP_AHRS.get_rotation_body_to_ned a
  out := out ++ " dcm=" ++ outV m.a ++ "," ++ outV m.b ++ "," ++ outV m.c
  let (vel, vok) := AP_AHRS.get_velocity_NED a {}
  out := out ++ " vel=" ++ outB vok ++ "," ++ outV vel
  let (pos, pok) := AP_AHRS.get_relative_position_NED_origin a {}
  out := out ++ " pos=" ++ outB pok ++ "," ++ outVp pos
  let (loc, lok) := AP_AHRS.get_location a {}
  out := out ++ " loc=" ++ outB lok ++ "," ++ outLoc loc
  out := out ++ " gyro=" ++ outV (AP_AHRS.get_gyro a) ++ " accef=" ++ outV (AP_AHRS.get_accel_ef a)
  out := out ++ " resets=" ++ toString (AP_AHRS.get_last_attitude_reset_count a).toNat ++ "," ++ toString (AP_AHRS.get_yaw_reset_count a).toNat ++
    "," ++ toString (AP_AHRS.get_position_NE_reset_count a).toNat ++ "," ++ toString (AP_AHRS.get_position_D_reset_count a).toNat
  out := out ++ " healthy=" ++ outB (AP_AHRS.healthy a) ++ " initialised=" ++ outB (AP_AHRS.initialised a)
  let (org, ook) := AP_AHRS.get_origin a {}
  out := out ++ " origin=" ++ outB ook ++ "," ++ outLoc org
  out := out ++ " ekf=" ++ toString (AP_AHRS.EKFType.toInt (AP_AHRS.active_EKF_type a)).toNat
  let (fs, fok) := AP_AHRS.get_filter_status_for_configured_backend a 0
  return out ++ " fs=" ++ outB fok ++ "," ++ hex 8 fs.toNat

/-- The vehicle-side keys of the probe that the World holds: AP_AHRS's `tkd` (takeoff/touchdown expected), `thgt`
(terrain height stable), `home`, `cfg` (vehicle class, fly forward, configured EKF type, source set, trim), Compass's
`comp` (throttle, voltage) and AP_Baro's `bgnd` (ground pressures, drift offset). -/
def vehicleKeys (w : World) : String := Id.run do
  let a := w.ahrs
  let mut out := " tkd=" ++ outB a.takeoff_expected ++ "," ++ toString a.takeoff_expected_start_ms.toNat ++ "," ++ outB a.touchdown_expected ++
    "," ++ toString a.touchdown_expected_start_ms.toNat
  out := out ++ " thgt=" ++ toString (AP_AHRS.TriState.toInt a.terrainHgtStableState).toInt.toNat
  out := out ++ " home=" ++ outB (AP_AHRS.home_is_set a) ++ "," ++ outB (AP_AHRS.home_is_locked a) ++ "," ++ outLoc (AP_AHRS.get_home a)
  let tr := AP_AHRS.get_trim a
  out := out ++ " cfg=" ++ toString (AP_AHRS.VehicleClass.toInt (AP_AHRS.get_vehicle_class a)).toNat ++ "," ++ outB (AP_AHRS.get_fly_forward a) ++
    "," ++ toString (AP_AHRS.EKFType.toInt (AP_AHRS.configured_ekf_type a)).toNat ++ "," ++ toString (AP_AHRS.get_posvelyaw_source_set w).toNat ++
    "," ++ outV tr
  out := out ++ " comp=" ++ outF w.compass._thr ++ "," ++ outF w.compass._per_motor.voltage
  let b := w.barometer
  let n := AP_Baro.num_instances b
  out := out ++ " bgnd=" ++ toString n.toNat
  for i in [0:n.toNat] do
    out := out ++ "," ++ outF (AP_Baro.get_ground_pressure_uint8_t b (UInt8.ofNat i))
  return out ++ "," ++ outF (AP_Baro.get_baro_drift_offset b)


end EstimatorProbe
