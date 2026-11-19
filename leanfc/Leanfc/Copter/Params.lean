import Leanfc.Scalar

/-!
# Copter.Params (the vehicle layer's configuration)

The parameters of the vehicle layer (`Leanfc/Copter/*`: arming, modes, takeoff, landing,
failsafes), with ArduCopter's names, meanings and defaults (ArduPilot checkout 802db19de1,
ArduCopter 4.8.0-dev; README.md, "Parameters of the vehicle layer"). They are read from the
parameter file by `ParamFile.build` like every other parameter and stored here twice: the value
as the file gives it (binary32, what the MAVLink parameter service reports) and, for the times,
the number of control ticks, computed once at load time by `ticksOf` (exact rational arithmetic
on the binary32 values, then rounded to the nearest tick), so that every timer of the vehicle
layer is a natural-number counter.

`ticksOf` and `natOf?` are setup functions (load time and mission-item acceptance), never part of
a control tick's arithmetic.
-/

open FloatLib.Floats

/-- The vehicle layer's parameters (file names in brackets). -/
structure CopterParams where
  /-- [RTL_ALT_M] m above home: RTL climbs to at least this altitude before returning -/
  rtlAlt : R
  /-- [RTL_LOIT_TIME] ms: RTL waits this long above home before the final descent -/
  rtlLoitTime : R
  rtlLoitTicks : Nat
  /-- [LAND_SPD_MS] m/s: the descent speed of the final stage of a landing -/
  landSpeed : R
  /-- [LAND_ALT_LOW_M] m above home: above it a landing descends at the vertical speed limit
  `nav.vMaxZ` (ArduCopter: WP_SPD_DN), slowing to LAND_SPD_MS on the way down to it -/
  landAltLow : R
  /-- [DISARM_DELAY] s: an armed vehicle that stays on the ground this long disarms (0: never) -/
  disarmDelay : R
  disarmTicks : Nat
  /-- [FS_GCS_ENABLE] ground-station failsafe action: 0 none, 1 RTL, 3 RTL (SmartRTL or RTL),
  4 LAND (SmartRTL or LAND), 5 LAND, 6 RTL (DO_LAND_START or RTL), 7 BRAKE then LAND (Brake or LAND) -/
  fsGcs : Nat
  /-- [FS_GCS_TIMEOUT] s without a ground-station HEARTBEAT that triggers the failsafe -/
  fsGcsTimeout : R
  fsGcsTicks : Nat
  /-- [FS_EKF_ACTION] estimator failsafe action: 0 report only, 1..3 LAND (with the 4 s pause) -/
  fsEkf : Nat
  /-- [copter.ekfPosMax] m: the estimator is unhealthy while the 1σ of its north or east position
  exceeds this (EKF covariance) -/
  ekfPosMax : R
  /-- derived: ekfPosMax² -/
  ekfPosMax2 : R
  /-- [MOT_SPIN_ARM] motor command (fraction of the maximum thrust) while armed on the ground -/
  spinArm : R
  /-- [MOT_SPOOL_TIME] s: spool-up before a takeoff, and spool-down after a touchdown before the
  disarm -/
  spoolTime : R
  spoolTicks : Nat
  /-- [TKOFF_SLEW_TIME] s: the takeoff throttle rises from 0 to 1 in this time -/
  tkoffSlewTime : R
  /-- derived: dt / TKOFF_SLEW_TIME, the takeoff throttle's rise per tick -/
  tkoffSlew : R
  /-- [TKOFF_THR_MAX] throttle at which a takeoff counts as lifted off -/
  tkoffThrMax : R
  /-- fixed durations of the vehicle layer as tick counts (ArduCopter's constants, `buildCopter`):
  boot gyro calibration 1 s; estimator settling after its start 2 s; a fix counts as present for
  1 s; the estimator failsafe needs 1 s of bad health (ArduCopter EKF_CHECK_ITERATIONS_MAX at 10 Hz);
  touchdown 1 s (LAND_DETECTOR_TRIGGER_SEC) and "maybe landed" 0.2 s
  (LAND_DETECTOR_MAYBE_TRIGGER_SEC); the failsafe landing's pause 4 s (LAND_WITH_DELAY_MS) -/
  calTicks : Nat
  settleTicks : Nat
  fixTicks : Nat
  ekfFsTicks : Nat
  landTicks : Nat
  landMaybeTicks : Nat
  landPauseTicks : Nat
  deriving Inhabited, Repr

namespace CopterParams

/-- The exact rational value of a finite binary32 number. -/
def ratOf? (x : R) : Option Rat := ExecFloat.Binary.toRat? x

/-- `x` if it is an integer in [0, hi]. -/
def natOf? (x : R) (hi : Nat) : Option Nat :=
  match ratOf? x with
  | some q => if q.den == 1 && 0 ≤ q.num && q.num ≤ hi then some q.num.toNat else none
  | none => none

/-- The number of ticks of period `dt` nearest to the duration `x` (exact: floor(x/dt + 1/2) on the
rational values); 0 for a nonpositive or nonfinite `x`. -/
def ticksOf (x dt : R) : Nat :=
  match ratOf? x, ratOf? dt with
  | some a, some b => if b > 0 && a > 0 then (a / b + 1 / 2).floor.toNat else 0
  | _, _ => 0

end CopterParams
