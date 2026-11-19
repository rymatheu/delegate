import Leanfc.ParamFile

/-!
# ParamTable (the parameter service's view of `Params`)

Two tables, indexed together by the parameter protocol (leanfc's first, then the compatibility
table):

1. `entries`: every numeric parameter of the parameter files (`ParamFile.names`), with its
   MAVLink name (at most 16 characters), its file name, its unit and a getter over `Params`. The
   name is ArduPilot's where ArduPilot has a parameter of the same meaning and unit (ArduCopter
   4.7/4.8 names; QGroundControl then shows ArduPilot's documentation for it), otherwise a leanfc
   name with the prefix `LFC_`. README.md, "MAVLink interface", lists the mapping with the nearest
   ArduPilot parameter where its unit differs.
2. `compat`: ArduPilot parameters that QGroundControl reads from an ArduCopter vehicle and that mean
   nothing to leanfc (frame, radio mapping, compass and accelerometer calibration, battery and
   failsafe setup, flight-mode switch). They hold ArduPilot's defaults (or a value that marks the
   setup step done), are writable and inert: nothing in leanfc reads them. They are not part of
   `Params`. `MAV_SYSID` is read by `leanfc` at startup only (ArduPilot needs a reboot too).

The vehicle layer's parameters have ArduCopter's names in the files too (`RTL_ALT_M`, ...), and
their MAV_PARAM_TYPE is ArduPilot's (`Entry.ty`: INT8 for the enumerations and DISARM_DELAY,
INT32 for RTL_LOIT_TIME); every other entry is REAL32. Values are always sent as numeric floats
(ArduPilot's encoding).

The values (`Store`) are the decimal values of the parameter files, rounded once to binary32, as
`ParamFile.load` reads them; `Store.params` is `ParamFile.build` of them. Setting a parameter
replaces its value and runs `ParamFile.build` again, the loader's own validation and derived-
constant computation (the modules' `make` functions), so a set parameter takes effect exactly as
if it had been in the file; a value `build` rejects is refused and the old value kept. The getter
over `Params` equals the stored value for every entry except `LFC_HDG_C`/`LFC_HDG_S`, which
`build` normalizes; the protocol reports the stored value.

The waypoints, the `TAKEOFF` and `LAND` lines and the `estimator` line are not parameters (the
mission protocol carries the mission).
-/

namespace Mavlink.ParamTable

/-- MAV_PARAM_TYPE of a parameter. -/
inductive PType where
  | int8
  | int16
  | int32
  | real32
  deriving Repr, BEq, Inhabited

def PType.code : PType → UInt8
  | .int8 => 2 | .int16 => 4 | .int32 => 6 | .real32 => 9

structure Entry where
  /-- MAVLink name, at most 16 characters -/
  name : String
  /-- the parameter-file name (`ParamFile.names`) -/
  file : String
  unit : String
  get : Params → R
  /-- MAV_PARAM_TYPE: ArduPilot's storage type for its own names, REAL32 for leanfc's -/
  ty : PType := .real32

/-- A small natural number as binary32 (exact). -/
def natR (n : Nat) : R := OfScientific.ofScientific n false 0

def mk (name file unit : String) (get : Params → R) (ty : PType := .real32) : Entry :=
  { name, file, unit, get, ty }

/-- leanfc's parameters, in the order of `ParamFile.names`. -/
def entries : Array Entry := #[
  mk "LFC_VEH_MASS" "vehicle.mass" "kg" (·.vehicle.mass),
  mk "LFC_VEH_IXX" "vehicle.inertia.x" "kg m^2" (·.vehicle.inertia.x),
  mk "LFC_VEH_IYY" "vehicle.inertia.y" "kg m^2" (·.vehicle.inertia.y),
  mk "LFC_VEH_IZZ" "vehicle.inertia.z" "kg m^2" (·.vehicle.inertia.z),
  mk "LFC_VEH_ARM_L" "vehicle.l" "m" (·.vehicle.l),
  mk "LFC_VEH_KM_KF" "vehicle.kmKf" "m" (·.vehicle.kmKf),
  mk "LFC_VEH_TMAX" "vehicle.tMax" "N" (·.vehicle.tMax),
  mk "LFC_DT" "dt" "s" (·.dt),
  mk "LFC_DT_FIX" "dtFix" "s" (·.dtFix),
  mk "LFC_AF_KACC" "attFilter.kAcc" "1/s" (·.attFilter.kAcc),
  mk "LFC_AF_KYAW" "attFilter.kYaw" "1/s" (·.attFilter.kYaw),
  mk "LFC_AF_KBIAS" "attFilter.kBias" "1/s^2" (·.attFilter.kBias),
  mk "LFC_AF_CUTOFF" "attFilter.cutoffHz" "Hz" (·.attFilter.cutoffHz),
  mk "LFC_NF_ALPHA" "navFilter.alpha" "" (·.navFilter.alpha),
  mk "LFC_NF_BETA" "navFilter.beta" "" (·.navFilter.beta),
  mk "LFC_NF_KV" "navFilter.kV" "" (·.navFilter.kV),
  mk "LFC_NF_KB" "navFilter.kB" "" (·.navFilter.kB),
  mk "EK3_GYRO_P_NSE" "ekf.gyroNoise" "rad/s" (·.ekf.cfg.gyroNoise),
  mk "EK3_ACC_P_NSE" "ekf.accelNoise" "m/s/s" (·.ekf.cfg.accelNoise),
  mk "LFC_EKF_GBIAS_W" "ekf.gyroBiasWalk" "rad/s/sqrt(s)" (·.ekf.cfg.gyroBiasWalk),
  mk "LFC_EKF_ABIAS_W" "ekf.accelBiasWalk" "m/s/s/sqrt(s)" (·.ekf.cfg.accelBiasWalk),
  mk "EK3_POSNE_M_NSE" "ekf.posNE" "m" (·.ekf.cfg.posNE),
  mk "EK3_ALT_M_NSE" "ekf.posD" "m" (·.ekf.cfg.posD),
  mk "LFC_EKF_VEL_NSE" "ekf.vel" "m/s" (·.ekf.cfg.vel),
  mk "EK3_YAW_M_NSE" "ekf.heading" "rad" (·.ekf.cfg.heading),
  mk "LFC_EKF_TILT0" "ekf.tilt0" "rad" (·.ekf.cfg.tilt0),
  mk "LFC_EKF_YAW0" "ekf.yaw0" "rad" (·.ekf.cfg.yaw0),
  mk "LFC_EKF_VEL0" "ekf.vel0" "m/s" (·.ekf.cfg.vel0),
  mk "LFC_EKF_POS0" "ekf.pos0" "m" (·.ekf.cfg.pos0),
  mk "LFC_EKF_GBIAS0" "ekf.gyroBias0" "rad/s" (·.ekf.cfg.gyroBias0),
  mk "LFC_EKF_ABIAS0" "ekf.accelBias0" "m/s/s" (·.ekf.cfg.accelBias0),
  mk "LFC_EKF_GBIASMIN" "ekf.gyroBiasMin" "rad/s" (·.ekf.cfg.gyroBiasMin),
  mk "LFC_EKF_PFLOOR" "ekf.pFloor" "" (·.ekf.cfg.pFloor),
  mk "LFC_EKF_CUTOFF" "ekf.cutoffHz" "Hz" (·.ekf.cfg.cutoffHz),
  mk "WP_SPD" "nav.vMax" "m/s" (·.nav.vMax),
  mk "WP_ACC" "nav.aMax" "m/s/s" (·.nav.aMax),
  mk "LFC_WP_ACC_LAT" "nav.aLat" "m/s/s" (·.nav.aLat),
  mk "LFC_WP_SPD_Z" "nav.vMaxZ" "m/s" (·.nav.vMaxZ),
  mk "WP_RADIUS_M" "nav.radius" "m" (·.nav.radius),
  mk "LFC_WP_LAG_MAX" "nav.lagMax" "m" (·.nav.lagMax),
  mk "WP_YAW_BEHAVIOR" "nav.yawBehavior" "" (fun P => if P.nav.followPath then 1 else 0),
  mk "LFC_WP_YAW_REV" "nav.yawReverse" "" (fun P => if P.nav.yawReverse then 1 else 0),
  mk "LFC_WP_YAW_RATE" "nav.yawRateMax" "rad/s" (·.nav.yawRateMax),
  mk "LFC_WP_YAW_ACC" "nav.yawAccelMax" "rad/s/s" (·.nav.yawAccelMax),
  mk "LFC_WP_YAW_VMIN" "nav.yawSpeedMin" "" (·.nav.yawSpeedMin),
  mk "PSC_NE_POS_P" "position.kpPos" "1/s" (·.position.kpPos),
  mk "LFC_PSC_VMAX_NE" "position.vMaxXY" "m/s" (·.position.vMaxXY),
  mk "LFC_PSC_VMAX_D" "position.vMaxZ" "m/s" (·.position.vMaxZ),
  mk "PSC_NE_VEL_P" "position.vel.kp" "1/s" (·.position.vel.kp),
  mk "PSC_NE_VEL_I" "position.vel.ki" "1/s/s" (·.position.vel.ki),
  mk "PSC_NE_VEL_IMAX" "position.vel.iMax" "m/s/s" (·.position.vel.iMax),
  mk "LFC_PSC_AMAX_NE" "position.aMaxXY" "m/s/s" (·.position.aMaxXY),
  mk "LFC_PSC_AMAX_D" "position.aMaxZ" "m/s/s" (·.position.aMaxZ),
  mk "ATC_ANG_RLL_P" "attitude.kpAtt" "1/s" (·.attitude.kpAtt),
  mk "LFC_ATC_RATE_MAX" "attitude.rateMax" "rad/s" (·.attitude.rateMax),
  mk "LFC_RAT_RP_P" "attitude.rate.kp" "1/s" (·.attitude.rate.kp),
  mk "LFC_RAT_RP_I" "attitude.rate.ki" "1/s/s" (·.attitude.rate.ki),
  mk "LFC_RAT_RP_IMAX" "attitude.rate.iMax" "rad/s/s" (·.attitude.rate.iMax),
  mk "ATC_ANG_YAW_P" "attitude.kpYaw" "1/s" (·.attitude.kpYaw),
  mk "LFC_RAT_Y_P" "attitude.rateYaw.kp" "1/s" (·.attitude.rateYaw.kp),
  mk "LFC_RAT_Y_I" "attitude.rateYaw.ki" "1/s/s" (·.attitude.rateYaw.ki),
  mk "LFC_RAT_Y_IMAX" "attitude.rateYaw.iMax" "rad/s/s" (·.attitude.rateYaw.iMax),
  mk "LFC_START_N" "start.x" "m" (·.start.x),
  mk "LFC_START_E" "start.y" "m" (·.start.y),
  mk "LFC_START_D" "start.z" "m" (·.start.z),
  mk "LFC_HDG_C" "setpoint.hc" "" (·.setpoint.hc),
  mk "LFC_HDG_S" "setpoint.hs" "" (·.setpoint.hs),
  mk "RTL_ALT_M" "RTL_ALT_M" "m" (·.copter.rtlAlt),
  { name := "RTL_LOIT_TIME", file := "RTL_LOIT_TIME", unit := "ms", get := (·.copter.rtlLoitTime), ty := .int32 },
  mk "LAND_SPD_MS" "LAND_SPD_MS" "m/s" (·.copter.landSpeed),
  mk "LAND_ALT_LOW_M" "LAND_ALT_LOW_M" "m" (·.copter.landAltLow),
  { name := "DISARM_DELAY", file := "DISARM_DELAY", unit := "s", get := (·.copter.disarmDelay), ty := .int8 },
  { name := "FS_GCS_ENABLE", file := "FS_GCS_ENABLE", unit := "", get := (natR ·.copter.fsGcs), ty := .int8 },
  mk "FS_GCS_TIMEOUT" "FS_GCS_TIMEOUT" "s" (·.copter.fsGcsTimeout),
  { name := "FS_EKF_ACTION", file := "FS_EKF_ACTION", unit := "", get := (natR ·.copter.fsEkf), ty := .int8 },
  mk "LFC_FS_EKF_POS" "copter.ekfPosMax" "m" (·.copter.ekfPosMax),
  mk "MOT_SPIN_ARM" "MOT_SPIN_ARM" "" (·.copter.spinArm),
  mk "MOT_SPOOL_TIME" "MOT_SPOOL_TIME" "s" (·.copter.spoolTime),
  mk "TKOFF_SLEW_TIME" "TKOFF_SLEW_TIME" "s" (·.copter.tkoffSlewTime),
  mk "TKOFF_THR_MAX" "TKOFF_THR_MAX" "" (·.copter.tkoffThrMax)]

/-- The compatibility table: (name, type, value). ArduPilot's default unless noted. -/
def compat : Array (String × PType × R) := #[
  ("MAV_SYSID", .int32, 1),
  ("FRAME_CLASS", .int8, 1),          -- 1 quad (ArduPilot default 0 = undefined: "setup needed")
  ("FRAME_TYPE", .int8, 1),           -- 1 X
  ("RCMAP_ROLL", .int8, 1), ("RCMAP_PITCH", .int8, 2), ("RCMAP_THROTTLE", .int8, 3),
  ("RCMAP_YAW", .int8, 4),
  ("RC1_MIN", .int16, 1000), ("RC1_MAX", .int16, 2000), ("RC1_TRIM", .int16, 1500),  -- as calibrated
  ("RC2_MIN", .int16, 1000), ("RC2_MAX", .int16, 2000), ("RC2_TRIM", .int16, 1500),
  ("RC3_MIN", .int16, 1000), ("RC3_MAX", .int16, 2000), ("RC3_TRIM", .int16, 1000),
  ("RC4_MIN", .int16, 1000), ("RC4_MAX", .int16, 2000), ("RC4_TRIM", .int16, 1500),
  ("COMPASS_DEV_ID", .int32, 0), ("COMPASS_DEV_ID2", .int32, 0), ("COMPASS_DEV_ID3", .int32, 0),
  ("COMPASS_USE", .int8, 1), ("COMPASS_USE2", .int8, 1), ("COMPASS_USE3", .int8, 1),
  ("COMPASS_OFS_X", .real32, 0), ("COMPASS_OFS_Y", .real32, 0), ("COMPASS_OFS_Z", .real32, 0),
  ("INS_ACCOFFS_X", .real32, 0.001), ("INS_ACCOFFS_Y", .real32, 0.001),  -- as calibrated
  ("INS_ACCOFFS_Z", .real32, 0.001),
  ("FLTMODE_CH", .int8, 5),
  ("FLTMODE1", .int8, 0), ("FLTMODE2", .int8, 0), ("FLTMODE3", .int8, 0),
  ("FLTMODE4", .int8, 0), ("FLTMODE5", .int8, 0), ("FLTMODE6", .int8, 0),
  ("ARMING_CHECK", .int32, 1),
  ("BATT_MONITOR", .int8, 0), ("BATT_CAPACITY", .int32, 3300),
  ("BATT_FS_LOW_ACT", .int8, 0), ("BATT_FS_CRT_ACT", .int8, 0),
  ("BATT_LOW_VOLT", .real32, 10.5), ("BATT_LOW_MAH", .int32, 0),
  ("BATT_CRT_VOLT", .real32, 0), ("BATT_CRT_MAH", .int32, 0),
  ("FS_OPTIONS", .int32, 16),
  ("FS_THR_ENABLE", .int8, 1),
  -- read by QGroundControl's Sensors and Tuning setup pages (when the user opens them)
  ("AHRS_ORIENTATION", .int8, 0), ("COMPASS_AUTODEC", .int8, 1), ("COMPASS_DEC", .real32, 0),
  ("COMPASS_EXTERNAL", .int8, 0), ("COMPASS_EXTERN2", .int8, 0), ("COMPASS_EXTERN3", .int8, 0),
  ("COMPASS_OFS2_X", .real32, 0), ("COMPASS_OFS2_Y", .real32, 0), ("COMPASS_OFS2_Z", .real32, 0),
  ("COMPASS_OFS3_X", .real32, 0), ("COMPASS_OFS3_Y", .real32, 0), ("COMPASS_OFS3_Z", .real32, 0),
  ("COMPASS_ORIENT", .int8, 0), ("COMPASS_ORIENT2", .int8, 0), ("COMPASS_ORIENT3", .int8, 0),
  ("COMPASS_PRIMARY", .int8, 0),
  ("COMPASS_PRIO1_ID", .int32, 0), ("COMPASS_PRIO2_ID", .int32, 0), ("COMPASS_PRIO3_ID", .int32, 0),
  ("INS_ACC_ID", .int32, 0), ("INS_ACC2_ID", .int32, 0), ("INS_ACC3_ID", .int32, 0),
  ("BARO1_DEVID", .int32, 0), ("BARO2_DEVID", .int32, 0), ("BARO3_DEVID", .int32, 0),
  ("RC7_OPTION", .int16, 0), ("RC8_OPTION", .int16, 0), ("RC9_OPTION", .int16, 0),
  ("RC10_OPTION", .int16, 0), ("RC11_OPTION", .int16, 0), ("RC12_OPTION", .int16, 0)]

/-- Number of parameters served: leanfc's, then the compatibility table. -/
def count : Nat := entries.size + compat.size

/-- The parameter values: leanfc's (as read from the files) and the compatibility table's. -/
structure Store where
  values : Array R
  compatValues : Array R
  waypoints : Array Waypoint
  /-- the `TAKEOFF` and `LAND` lines of the files (the onboard mission's ends) -/
  ends : ParamFile.Ends
  estimator : Estimator
  /-- the `ORIGIN` line of the files (latitude, longitude ·1e7, altitude AMSL mm), if any -/
  origin : Option (Int × Int × Int)
  /-- `ParamFile.build` of `values` -/
  params : Params

namespace Store

/-- The value of each name in `ParamFile.names` order. -/
def lookup (vals : Array R) (k : String) : R :=
  match entries.findIdx? (·.file == k) with
  | some i => vals.getD i 0
  | none => 0

def rebuild (vals : Array R) (wps : Array Waypoint) (est : Estimator) : Except String Params :=
  ParamFile.build (lookup vals) wps est

/-- The files `(name, text)` merged and validated by `ParamFile.merge` and `ParamFile.complete`
(as `ParamFile.load` does), then built. -/
def load (files : List (String × String)) : Except String Store := do
  let raw ← ParamFile.merge files
  let (g, wps, e) ← ParamFile.complete raw
  let values := entries.map fun en => g en.file
  let params ← rebuild values wps e
  pure { values, compatValues := compat.map (·.2.2), waypoints := wps, ends := raw.ends, estimator := e,
         origin := raw.origin, params }

/-- (name, type, value) of parameter `i` (leanfc's first, then the compatibility table). -/
def get (s : Store) (i : Nat) : Option (String × PType × R) :=
  if h : i < entries.size then some (entries[i].name, entries[i].ty, s.values.getD i 0)
  else
    let j := i - entries.size
    if h : j < compat.size then some (compat[j].1, compat[j].2.1, s.compatValues.getD j 0) else none

def indexOf (name : String) : Option Nat :=
  match entries.findIdx? (·.name == name) with
  | some i => some i
  | none => (compat.findIdx? (·.1 == name)).map (entries.size + ·)

/-- Set parameter `i` to `x`. A leanfc parameter is rebuilt with `ParamFile.build` (its error if
it rejects the value); a compatibility parameter is stored as sent. -/
def set (s : Store) (i : Nat) (x : R) : Except String Store :=
  if i < entries.size then
    let values := s.values.set! i x
    match rebuild values s.waypoints s.estimator with
    | .ok params => .ok { s with values, params }
    | .error e => .error e
  else
    let j := i - entries.size
    if j < compat.size then .ok { s with compatValues := s.compatValues.set! j x }
    else .error "no such parameter"

end Store

end Mavlink.ParamTable
