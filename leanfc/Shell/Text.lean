import Leanfc

/-!
# Shell.Text (decimal text of the lock-step protocol and the parameter listing)

IO-side formatting for `Main.lean`: the sensor line parser (each decimal rounded once to binary32 by
`Decimal.parseR`), the output line (motors, `--trace`, `--trace-ekf`, `--trace-vehicle`, `--bits`),
the `--ekf-only` lines, `--print-params` and the argument helpers. `fmt` uses binary64 `Float` to
print a binary32 number with 9 significant digits (which round-trips); it is logging, never part of
a tick.
-/

open FloatLib.Floats

/-! ## Decimal text ↔ binary32 -/

/-- The line without trailing whitespace (for messages). -/
def chomp (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

def parseLine (s : String) : Option (Array R) :=
  (Decimal.tokens s).toArray.mapM Decimal.parseR

/-- 9 significant digits (enough to round-trip binary32), as `d.dddddddde±x`. -/
def fmt (x : R) : String :=
  let f := R.toFloat x
  if f.isNaN then "nan" else if f.isInf then (if f > 0 then "inf" else "-inf") else
  if f == 0 then (if ExecFloat.Binary.toBits32 x >>> 31 == 1 then "-0" else "0") else
  let a := f.abs
  let digits (e : Float) : Nat := (a * Float.pow 10 (8 - e)).round.toUInt64.toNat
  let e := (Float.log10 a).floor
  let (n, e) := if digits e ≥ 1000000000 then (digits (e + 1), e + 1)
    else if digits e < 100000000 then (digits (e - 1), e - 1) else (digits e, e)
  let ds := toString n
  let ei : Int := if e < 0 then -((-e).toUInt64.toNat : Int) else (e.toUInt64.toNat : Int)
  s!"{if f < 0 then "-" else ""}{ds.take 1}.{ds.drop 1}e{ei}"

def hex8 (x : R) : String :=
  let s := String.ofList (Nat.toDigits 16 (ExecFloat.Binary.toBits32 x).toNat)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

/-! ## The tick -/

def v3 (a : Array R) (i : Nat) : Vec3 := ⟨a[i]!, a[i + 1]!, a[i + 2]!⟩

def present (x : R) : Bool := !(x == 0)

/-- 16 numbers, or 17 with the position-fix presence last. -/
def sensorsOf (a : Array R) : Sensors :=
  let fix := present a[6]!
  let posFix := fix && (a.size < 17 || present a[16]!)
  { gyro := v3 a 0, accel := v3 a 3,
    heading := if fix then some (a[7]!, a[8]!) else none,
    position := if posFix then some (v3 a 9) else none,
    velocity := if present a[15]! then some (v3 a 12) else none }

def vec (v : Vec3) : Array R := #[v.x, v.y, v.z]

/-- `--trace-ekf` fields: diag P (15), gyro bias (3), accelerometer bias (3). -/
def ekfFields (st : State) : Array R :=
  match st.est with
  | .ekf e => (Array.ofFn fun i : Fin 15 => e.P[i][i]) ++ vec e.bg ++ vec e.ba
  | .fixed af nf => Array.replicate 15 0 ++ vec af.bias ++ vec nf.aBias

def withBits (bits : Bool) (xs : Array R) (body : String) : String :=
  if bits then body ++ " |" ++ String.join (xs.map (" " ++ hex8 ·)).toList else body

def outputLine (trace traceEkf bits : Bool) (st : State) (m : Motors) (extra : String := "") : String :=
  let (p, v, q) := Controller.estimate st
  let sp := st.target.pSp
  let xs := #[m.m1, m.m2, m.m3, m.m4] ++
    (if trace then #[p.x, p.y, p.z, v.x, v.y, v.z, q.w, q.x, q.y, q.z, sp.x, sp.y, sp.z] else #[])
  let ys := (if traceEkf then ekfFields st else #[]) ++
    (if trace then #[st.target.heading.1, st.target.heading.2] else #[])
  let body := " ".intercalate (xs.map fmt).toList ++ (if trace then s!" {st.nav.leg}" else "") ++
    String.join (ys.map (" " ++ fmt ·)).toList
  withBits bits (xs ++ ys) (body ++ extra)

def zerosLine (trace traceEkf : Bool) : String :=
  " ".intercalate (List.replicate ((if trace then 20 else 4) + (if traceEkf then 21 else 0)) "0")

/-- `--trace-vehicle`: the vehicle layer's mode number, armed (0/1), landed state
(MAV_LANDED_STATE: 1 on ground, 2 in air, 3 takeoff, 4 landing) and current mission item, as
integers after the other numbers (before the `--bits` words, which cover only binary32 numbers). -/
def vehicleFields (v : Copter.State) : String :=
  let landed : Nat := match v.landed with
    | .onGround => 1 | .inAir => 2 | .takeoff => 3 | .landing => 4
  s!" {v.mode} {if v.armed then 1 else 0} {landed} {v.cur}"

/-- `--ekf-only`: the whole EKF state as hex words. -/
def ekfStateLine (e : EKF.State) : String :=
  let xs := #[e.q.w, e.q.x, e.q.y, e.q.z] ++ vec e.omega ++ vec e.p ++ vec e.v ++ vec e.bg ++ vec e.ba ++
    (e.P.toArray.flatMap Vector.toArray)
  " ".intercalate (xs.map hex8).toList

/-- `--ekf-only`: the derived constants, as hex words: dt, dt/2, dt²/2, Q (15), R pos (3), R vel,
R heading, P floor, low-pass coefficient, σ_gyro², σ_min², initial P diagonal (15). -/
def ekfConstLine (k : EKF.Params) : String :=
  let xs := #[k.dt, k.halfDt, k.halfDt2] ++ k.qd.toArray ++ vec k.rPos ++
    #[k.rVel, k.rHdg, k.cfg.pFloor, k.lp, k.gyroVar, k.gyroBiasVarMin] ++ k.p0.toArray
  "const " ++ " ".intercalate (xs.map hex8).toList

/-! ## Arguments and the loop -/

def argNat (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

/-- Every value following an occurrence of `flag`. -/
def argAll : List String → String → List String
  | f :: v :: rest, flag => if f == flag then v :: argAll rest flag else argAll (v :: rest) flag
  | _, _ => []

def argOne (args : List String) (flag : String) : Option String := (argAll args flag).head?

/-- The `n` values after `flag`. -/
def argsAfter (args : List String) (flag : String) (n : Nat) : Option (List String) :=
  match args.dropWhile (· != flag) with
  | _ :: rest => if rest.length ≥ n then some (rest.take n) else none
  | [] => none

def fmtRow (r : Row4) : String := " ".intercalate [fmt r.c1, fmt r.c2, fmt r.c3, fmt r.c4]

/-- The loaded configuration in the file format (input values as binary32, 9 digits), the derived
mixer rows as comments. -/
def paramLines (P : Params) : List String :=
  let v := P.vehicle
  let e := P.ekf.cfg
  let k := P.copter
  let kv (k : String) (x : R) := s!"{k} {fmt x}"
  let (a0, a1, a2, a3) := v.allocRows
  ["# vehicle", kv "vehicle.mass" v.mass, kv "vehicle.inertia.x" v.inertia.x,
   kv "vehicle.inertia.y" v.inertia.y, kv "vehicle.inertia.z" v.inertia.z, kv "vehicle.l" v.l,
   kv "vehicle.kmKf" v.kmKf, kv "vehicle.tMax" v.tMax,
   "# timing", kv "dt" P.dt, kv "dtFix" P.dtFix,
   "# attitude filter", kv "attFilter.kAcc" P.attFilter.kAcc, kv "attFilter.kYaw" P.attFilter.kYaw,
   kv "attFilter.kBias" P.attFilter.kBias, kv "attFilter.cutoffHz" P.attFilter.cutoffHz,
   "# navigation filter", kv "navFilter.alpha" P.navFilter.alpha, kv "navFilter.beta" P.navFilter.beta,
   kv "navFilter.kV" P.navFilter.kV, kv "navFilter.kB" P.navFilter.kB,
   "# estimator", s!"estimator {match P.estimator with | .fixed => "fixed" | .ekf => "ekf"}",
   "# EKF", kv "ekf.gyroNoise" e.gyroNoise, kv "ekf.accelNoise" e.accelNoise,
   kv "ekf.gyroBiasWalk" e.gyroBiasWalk, kv "ekf.accelBiasWalk" e.accelBiasWalk,
   kv "ekf.posNE" e.posNE, kv "ekf.posD" e.posD, kv "ekf.vel" e.vel, kv "ekf.heading" e.heading,
   kv "ekf.tilt0" e.tilt0, kv "ekf.yaw0" e.yaw0, kv "ekf.vel0" e.vel0, kv "ekf.pos0" e.pos0,
   kv "ekf.gyroBias0" e.gyroBias0, kv "ekf.accelBias0" e.accelBias0,
   kv "ekf.gyroBiasMin" e.gyroBiasMin, kv "ekf.pFloor" e.pFloor, kv "ekf.cutoffHz" e.cutoffHz,
   "# navigator", kv "nav.vMax" P.nav.vMax, kv "nav.aMax" P.nav.aMax, kv "nav.aLat" P.nav.aLat,
   kv "nav.vMaxZ" P.nav.vMaxZ, kv "nav.radius" P.nav.radius,
   kv "nav.lagMax" P.nav.lagMax, s!"nav.yawBehavior {if P.nav.followPath then 1 else 0}",
   s!"nav.yawReverse {if P.nav.yawReverse then 1 else 0}",
   kv "nav.yawRateMax" P.nav.yawRateMax, kv "nav.yawAccelMax" P.nav.yawAccelMax,
   kv "nav.yawSpeedMin" P.nav.yawSpeedMin,
   "# position", kv "position.kpPos" P.position.kpPos, kv "position.vMaxXY" P.position.vMaxXY,
   kv "position.vMaxZ" P.position.vMaxZ, kv "position.vel.kp" P.position.vel.kp,
   kv "position.vel.ki" P.position.vel.ki, kv "position.vel.iMax" P.position.vel.iMax,
   kv "position.aMaxXY" P.position.aMaxXY, kv "position.aMaxZ" P.position.aMaxZ,
   "# attitude", kv "attitude.kpAtt" P.attitude.kpAtt, kv "attitude.rateMax" P.attitude.rateMax,
   kv "attitude.rate.kp" P.attitude.rate.kp, kv "attitude.rate.ki" P.attitude.rate.ki,
   kv "attitude.rate.iMax" P.attitude.rate.iMax, kv "attitude.kpYaw" P.attitude.kpYaw,
   kv "attitude.rateYaw.kp" P.attitude.rateYaw.kp, kv "attitude.rateYaw.ki" P.attitude.rateYaw.ki,
   kv "attitude.rateYaw.iMax" P.attitude.rateYaw.iMax,
   "# mission", kv "start.x" P.start.x, kv "start.y" P.start.y, kv "start.z" P.start.z,
   kv "setpoint.hc" P.setpoint.hc, kv "setpoint.hs" P.setpoint.hs,
   "# vehicle layer", kv "RTL_ALT_M" k.rtlAlt, kv "RTL_LOIT_TIME" k.rtlLoitTime, kv "LAND_SPD_MS" k.landSpeed,
   kv "LAND_ALT_LOW_M" k.landAltLow, kv "DISARM_DELAY" k.disarmDelay, s!"FS_GCS_ENABLE {k.fsGcs}",
   kv "FS_GCS_TIMEOUT" k.fsGcsTimeout, s!"FS_EKF_ACTION {k.fsEkf}", kv "copter.ekfPosMax" k.ekfPosMax,
   kv "MOT_SPIN_ARM" k.spinArm, kv "MOT_SPOOL_TIME" k.spoolTime, kv "TKOFF_SLEW_TIME" k.tkoffSlewTime,
   kv "TKOFF_THR_MAX" k.tkoffThrMax] ++
  P.waypoints.toList.map (fun w =>
    s!"{if w.kind == .line then "WAYPOINT" else "SPLINE"} {fmt w.pos.x} {fmt w.pos.y} {fmt w.pos.z}{if w.stop then " stop" else ""}") ++
  ["# derived: legs (chord length, speed limit, end speed, passed at speed)"] ++
  P.nav.legs.toList.map (fun l =>
    s!"# leg {fmt l.length} {fmt l.vLeg} {fmt l.vEnd} {l.passed}") ++
  ["# derived: allocation A (rows thrust, roll, pitch, yaw; columns motors 1..4)",
   s!"# alloc 0 {fmtRow a0}", s!"# alloc 1 {fmtRow a1}", s!"# alloc 2 {fmtRow a2}", s!"# alloc 3 {fmtRow a3}",
   "# derived: inverse rows (motor i <- [T, tau_x, tau_y, tau_z])",
   s!"# inv 0 {fmtRow v.inv0}", s!"# inv 1 {fmtRow v.inv1}", s!"# inv 2 {fmtRow v.inv2}", s!"# inv 3 {fmtRow v.inv3}"]

