import Leanfc.Controller

/-!
# ParamFile

The parameter file: the whole configuration of the controller as text, so one executable flies
different vehicles. `Main` reads the files (the only IO) and calls `load`, which is pure.

Format: one `NAME value` per line; `#` starts a comment; blank lines are ignored. NAME is the path
of the field in `Params` (`vehicle.mass`, `position.vel.kp`, `start.z`, ...; the list is `names`).
More line kinds: `WAYPOINT n e d [stop]` and `SPLINE n e d [stop]` (a straight leg or a
spline leg to that destination, NED m, repeated, in flying order; `stop`: the target stops there),
`TAKEOFF d` and `LAND [n e]` (the onboard mission's first and last items, below), `estimator
fixed|ekf` (which estimator the controller runs; required), `ORIGIN lat lon alt` (the geodetic
origin of the NED frame for the ground station: degrees, degrees, m AMSL, kept as exact integers
·1e7, ·1e7, ·1e3; optional) and `SIM_VEHICLE name`, which is for the simulator harness (it picks
the URDF) and is accepted and ignored here. Several files may be given; a later file overrides the
names it sets, and replaces the mission (the waypoint list, `TAKEOFF` and `LAND`) if it has any
`WAYPOINT` or `SPLINE` lines. Within one file a name may appear once. `merge` returns the merged
settings (`Raw`), which `complete` validates as complete and `build` turns into `Params`; `load` is
the three in a row.

The onboard mission. The waypoint lines are the navigator's waypoint list (`Params.waypoints`), the
mission of the batch start (in the air at the start point, armed, in AUTO). A vehicle started on the
ground (`--ground`) boots with the mission a real ArduCopter keeps in its storage, which ArduCopter
flies in AUTO from the ground only if its first item is a takeoff: `TAKEOFF d` is a NAV_TAKEOFF
before the waypoints (climb straight up from the start point to down coordinate `d`, NED m, the
same frame as the waypoint lines; it must be above the start: `d` < `start.z`), and `LAND n e` a
NAV_LAND after them (fly to north `n`, east `e` at the altitude reached, then descend and land;
`LAND` alone lands where the last leg ends). Each may appear once per file, anywhere in it (the
takeoff is always the first item and the landing the last), and only in a file with waypoint lines.
With a `TAKEOFF` line the start point is where the vehicle rests on the ground, and the onboard
mission's relative altitudes (the MISSION_ITEM_INT form, frame GLOBAL_RELATIVE_ALT) are measured
from it, as the vehicle's home is at boot (`Shell/Tools.lean`, `Main.lean`). Neither line changes
`Params` (the waypoint list, the navigator, the batch start); they are kept in `Raw.ends` and the
services' store (`ParamTable.Store.ends`).

The vehicle layer's parameters have ArduCopter's names (`RTL_ALT_M`, `LAND_SPD_MS`, ...;
`Leanfc/Copter/Params.lean`); `buildCopter` checks their ranges (integers where ArduCopter's are)
and converts the times to tick counts.

Every value is rounded once from its decimal text to binary32 (the same `Decimal.parseR` the sensor
lines go through). Unknown names, names set twice in one file, malformed numbers, missing names, an
empty waypoint list, `TAKEOFF` or `LAND` set twice in a file or in a file without waypoint
lines, a `TAKEOFF` not above the start point, a leg of zero length (a point equal to the one before it), nonpositive values
where a division, a period or a limit needs a positive one (`nav.vMax`, `nav.aMax`, `nav.aLat`,
`nav.vMaxZ` among them), a `nav.yawBehavior` or `nav.yawReverse` other than 0 or 1 and a negative
`nav.yawSpeedMin` are errors. The derived constants (mixer inverse, ki·dt, beta/dtFix, the filter coefficient, the
navigator's legs, ...) are computed here, once, by the modules' `make` functions; `nav.yawBehavior` becomes the Boolean
`NavParams.followPath` and `nav.yawReverse` the Boolean `NavParams.yawReverse`.
-/

namespace Decimal

/-- Digits of a run, as (value, count, rest). -/
def digitRun (cs : List Char) : Nat × Nat × List Char :=
  let ds := cs.takeWhile Char.isDigit
  (ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0, ds.length, cs.drop ds.length)

/-- `[+-]digits[.digits][(e|E)[+-]digits]`, rounded once to binary32 (FloatLib's
`OfScientific`, round to nearest even). -/
def parseR (s : String) : Option R :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let (ip, ni, cs) := digitRun cs
  let (fp, nf, cs) := match cs with
    | '.' :: r => digitRun r | r => (0, 0, r)
  if ni + nf = 0 then none else
  let m := ip * 10 ^ nf + fp
  let ex : Option Int := match cs with
    | [] => some 0
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (en, r) := match r with
          | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
        let (e, ne, r) := digitRun r
        if ne = 0 || !r.isEmpty then none else some (if en then -(e : Int) else e)
      else none
  ex.map fun e =>
    let d : Int := e - (nf : Int)
    let x : R := if d ≥ 0 then OfScientific.ofScientific m false d.toNat
      else OfScientific.ofScientific m true (-d).toNat
    if neg then -x else x

/-- `[+-]digits[.digits]` scaled by 10^k exactly, with at most `k` decimals (`-35.3632621`, k = 7
↦ -353632621): the `ORIGIN` line, whose latitude and longitude binary32 cannot carry. -/
def parseScaled (s : String) (k : Nat) : Option Int :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let (ip, ni, cs) := digitRun cs
  let (fp, nf, cs) := match cs with
    | '.' :: r => digitRun r | r => (0, 0, r)
  if ni + nf = 0 || !cs.isEmpty || nf > k then none else
  let n : Int := ip * 10 ^ k + fp * 10 ^ (k - nf)
  some (if neg then -n else n)

/-- Whitespace-separated tokens. -/
def tokens (s : String) : List String :=
  (s.toList.splitBy (fun a b => a.isWhitespace == b.isWhitespace)).filterMap fun t =>
    if t.all Char.isWhitespace then none else some (String.ofList t)

end Decimal

namespace ParamFile

/-- Every name a configuration must set, grouped by module, in the order of the shipped files. -/
def names : List String :=
  ["vehicle.mass", "vehicle.inertia.x", "vehicle.inertia.y", "vehicle.inertia.z",
   "vehicle.l", "vehicle.kmKf", "vehicle.tMax",
   "dt", "dtFix",
   "attFilter.kAcc", "attFilter.kYaw", "attFilter.kBias", "attFilter.cutoffHz",
   "navFilter.alpha", "navFilter.beta", "navFilter.kV", "navFilter.kB",
   "ekf.gyroNoise", "ekf.accelNoise", "ekf.gyroBiasWalk", "ekf.accelBiasWalk",
   "ekf.posNE", "ekf.posD", "ekf.vel", "ekf.heading",
   "ekf.tilt0", "ekf.yaw0", "ekf.vel0", "ekf.pos0", "ekf.gyroBias0", "ekf.accelBias0",
   "ekf.gyroBiasMin", "ekf.pFloor", "ekf.cutoffHz",
   "nav.vMax", "nav.aMax", "nav.aLat", "nav.vMaxZ", "nav.radius", "nav.lagMax", "nav.yawBehavior", "nav.yawReverse",
   "nav.yawRateMax", "nav.yawAccelMax", "nav.yawSpeedMin",
   "position.kpPos", "position.vMaxXY", "position.vMaxZ",
   "position.vel.kp", "position.vel.ki", "position.vel.iMax", "position.aMaxXY", "position.aMaxZ",
   "attitude.kpAtt", "attitude.rateMax", "attitude.rate.kp", "attitude.rate.ki", "attitude.rate.iMax",
   "attitude.kpYaw", "attitude.rateYaw.kp", "attitude.rateYaw.ki", "attitude.rateYaw.iMax",
   "start.x", "start.y", "start.z", "setpoint.hc", "setpoint.hs",
   "RTL_ALT_M", "RTL_LOIT_TIME", "LAND_SPD_MS", "LAND_ALT_LOW_M", "DISARM_DELAY",
   "FS_GCS_ENABLE", "FS_GCS_TIMEOUT", "FS_EKF_ACTION", "copter.ekfPosMax",
   "MOT_SPIN_ARM", "MOT_SPOOL_TIME", "TKOFF_SLEW_TIME", "TKOFF_THR_MAX"]

/-- Where a `LAND` line lands: where the last leg ends (`LAND`), or at north `n`, east `e` (`LAND n e`). -/
inductive LandAt where
  | here
  | point (n e : R)
  deriving Inhabited, Repr

/-- The onboard mission's items around the waypoints: the `TAKEOFF` line (the down coordinate to
climb to) and the `LAND` line, if any. -/
structure Ends where
  takeoff : Option R := none
  land : Option LandAt := none
  deriving Inhabited, Repr

/-- The content of parameter files before validation: the `NAME value` settings (one per name; a
later file overrides an earlier one), the waypoints and the mission's ends (a later file with
`WAYPOINT` or `SPLINE` lines replaces all three), the `estimator` line and the `ORIGIN` line
(latitude and longitude in degrees·1e7, altitude AMSL in mm, exact integers). -/
structure Raw where
  vals : List (String × R) := []
  waypoints : Array Waypoint := #[]
  ends : Ends := {}
  estimator : Option Estimator := none
  origin : Option (Int × Int × Int) := none
  deriving Inhabited

/-- One file: its `NAME value` settings in file order, its waypoints, its `TAKEOFF`, `LAND`,
`estimator` and `ORIGIN` lines. -/
def parseFile (file text : String) : Except String Raw := do
  let mut vals : List (String × R) := []
  let mut wps : Array Waypoint := #[]
  let mut ends : Ends := {}
  let mut est : Option Estimator := none
  let mut origin : Option (Int × Int × Int) := none
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    let at_ := s!"{file}:{n}"
    match Decimal.tokens ((line.splitOn "#").headD "") with
    | [] => pure ()
    | ["SIM_VEHICLE", _] => pure ()
    | "SIM_VEHICLE" :: _ => throw s!"{at_}: expected `SIM_VEHICLE name`"
    | "ORIGIN" :: xs =>
      if origin.isSome then throw s!"{at_}: `ORIGIN` is set twice in this file"
      match xs with
      | [a, b, c] =>
        match Decimal.parseScaled a 7, Decimal.parseScaled b 7, Decimal.parseScaled c 3 with
        | some la, some lo, some al =>
          if la < -900000000 || la > 900000000 || lo < -1800000000 || lo > 1800000000 then
            throw s!"{at_}: `ORIGIN`: latitude within ±90, longitude within ±180 degrees"
          origin := some (la, lo, al)
        | _, _, _ => throw s!"{at_}: expected `ORIGIN lat lon alt` (degrees with at most 7 decimals, m AMSL with at most 3)"
      | _ => throw s!"{at_}: expected `ORIGIN lat lon alt`"
    | "TAKEOFF" :: xs =>
      if ends.takeoff.isSome then throw s!"{at_}: `TAKEOFF` is set twice in this file"
      match xs.mapM Decimal.parseR with
      | some [d] => ends := { ends with takeoff := some d }
      | _ => throw s!"{at_}: expected `TAKEOFF d` (the down coordinate to climb to, NED m)"
    | "LAND" :: xs =>
      if ends.land.isSome then throw s!"{at_}: `LAND` is set twice in this file"
      match xs.mapM Decimal.parseR with
      | some [] => ends := { ends with land := some .here }
      | some [x, y] => ends := { ends with land := some (.point x y) }
      | _ => throw s!"{at_}: expected `LAND` or `LAND n e` (NED m)"
    | "estimator" :: xs =>
      if est.isSome then throw s!"{at_}: `estimator` is set twice in this file"
      match xs with
      | ["fixed"] => est := some .fixed
      | ["ekf"] => est := some .ekf
      | _ => throw s!"{at_}: expected `estimator fixed` or `estimator ekf`"
    | kw :: xs =>
      if kw == "WAYPOINT" || kw == "SPLINE" then
        let kind := if kw == "WAYPOINT" then LegKind.line else LegKind.spline
        let (nums, stop) := match xs with
          | [a, b, c, "stop"] => ([a, b, c], true)
          | _ => (xs, false)
        match nums.mapM Decimal.parseR with
        | some [a, b, c] => wps := wps.push ⟨⟨a, b, c⟩, kind, stop⟩
        | _ => throw s!"{at_}: expected `{kw} n e d` or `{kw} n e d stop`"
      else
        match xs with
        | [v] =>
          let name := kw
          if !names.contains name then throw s!"{at_}: unknown parameter `{name}`"
          if vals.any (·.1 == name) then throw s!"{at_}: `{name}` is set twice in this file"
          match Decimal.parseR v with
          | some x => vals := vals ++ [(name, x)]
          | none => throw s!"{at_}: `{name}`: malformed number `{v}`"
        | _ => throw s!"{at_}: expected `NAME value`, got `{kw}` with another number of values"
  if wps.isEmpty && (ends.takeoff.isSome || ends.land.isSome) then
    throw s!"{file}: `TAKEOFF` and `LAND` need the mission's `WAYPOINT` or `SPLINE` lines in the same file"
  return { vals, waypoints := wps, ends, estimator := est, origin }

/-- The files `(name, text)` merged, later files overriding earlier ones (`Raw`); not validated. -/
def merge (files : List (String × String)) : Except String Raw := do
  let mut r : Raw := {}
  for (file, text) in files do
    let f ← parseFile file text
    for (k, v) in f.vals do
      r := { r with vals := (k, v) :: r.vals.filter (·.1 != k) }
    if !f.waypoints.isEmpty then r := { r with waypoints := f.waypoints, ends := f.ends }
    if f.estimator.isSome then r := { r with estimator := f.estimator }
    if f.origin.isSome then r := { r with origin := f.origin }
  return r

/-- The value of `k` in merged settings (0 if absent). -/
def Raw.get (r : Raw) (k : String) : R := (List.lookup k r.vals).getD 0

/-- The vehicle layer's parameters from a complete set of values `g` (`Copter.Params`). -/
def buildCopter (g : String → R) (dt : R) : Except String CopterParams := do
  let nat (k : String) (hi : Nat) : Except String Nat :=
    match CopterParams.natOf? (g k) hi with
    | some n => pure n
    | none => throw s!"`{k}` must be an integer from 0 to {hi}"
  let pos (k : String) : Except String R :=
    if g k > 0 then pure (g k) else throw s!"`{k}` must be positive"
  let nonneg (k : String) : Except String R :=
    if g k ≥ 0 then pure (g k) else throw s!"`{k}` must not be negative"
  let ticks (x : R) := CopterParams.ticksOf x dt
  let rtlAlt ← nonneg "RTL_ALT_M"
  let _ ← nat "RTL_LOIT_TIME" 60000
  let landSpeed ← pos "LAND_SPD_MS"
  let landAltLow ← nonneg "LAND_ALT_LOW_M"
  let _ ← nat "DISARM_DELAY" 127
  let fsGcs ← nat "FS_GCS_ENABLE" 7
  let fsGcsTimeout ← pos "FS_GCS_TIMEOUT"
  let fsEkf ← nat "FS_EKF_ACTION" 3
  let ekfPosMax ← pos "copter.ekfPosMax"
  let spinArm ← nonneg "MOT_SPIN_ARM"
  if !(spinArm < 1) then throw "`MOT_SPIN_ARM` must be below 1"
  let spoolTime ← nonneg "MOT_SPOOL_TIME"
  let tkoffSlewTime ← pos "TKOFF_SLEW_TIME"
  let tkoffThrMax ← pos "TKOFF_THR_MAX"
  if tkoffThrMax > 1 then throw "`TKOFF_THR_MAX` must not exceed 1"
  pure
    { rtlAlt, rtlLoitTime := g "RTL_LOIT_TIME", rtlLoitTicks := ticks (g "RTL_LOIT_TIME" / 1000),
      landSpeed, landAltLow,
      disarmDelay := g "DISARM_DELAY", disarmTicks := ticks (g "DISARM_DELAY"),
      fsGcs, fsGcsTimeout, fsGcsTicks := ticks fsGcsTimeout, fsEkf,
      ekfPosMax, ekfPosMax2 := ekfPosMax * ekfPosMax, spinArm,
      spoolTime, spoolTicks := ticks spoolTime,
      tkoffSlewTime, tkoffSlew := dt / tkoffSlewTime, tkoffThrMax,
      calTicks := ticks 1, settleTicks := ticks 2, fixTicks := ticks 1, ekfFsTicks := ticks 1,
      landTicks := ticks 1, landMaybeTicks := ticks 0.2, landPauseTicks := ticks 4 }

/-- `Params` from a complete set of values `g` and the waypoints; checks the values that are
divided by or that must be periods, and computes every derived constant. -/
def build (g : String → R) (wps : Array Waypoint) (est : Estimator) : Except String Params := do
  let pos (k : String) : Except String R :=
    if g k > 0 then pure (g k) else throw s!"`{k}` must be positive"
  let dt ← pos "dt"
  let dtFix ← pos "dtFix"
  let veh := Vehicle.make (← pos "vehicle.mass")
    ⟨← pos "vehicle.inertia.x", ← pos "vehicle.inertia.y", ← pos "vehicle.inertia.z"⟩
    (← pos "vehicle.l") (← pos "vehicle.kmKf") (← pos "vehicle.tMax")
  let kAcc ← pos "attFilter.kAcc"
  let hc := g "setpoint.hc"
  let hs := g "setpoint.hs"
  let hn := R.sqrt (hc * hc + hs * hs)
  if !(hn > 0) then throw "the heading setpoint (`setpoint.hc`, `setpoint.hs`) must not be zero"
  let yb := g "nav.yawBehavior"
  if !(yb == 0 || yb == 1) then
    throw "`nav.yawBehavior` must be 0 (hold the initial heading) or 1 (follow the path)"
  let followPath := yb == 1
  let yr := g "nav.yawReverse"
  if !(yr == 0 || yr == 1) then
    throw "`nav.yawReverse` must be 0 (nose along the direction of travel) or 1 (nose against it)"
  let start : Vec3 := ⟨g "start.x", g "start.y", g "start.z"⟩
  for i in [0:wps.size] do
    let a := if i = 0 then start else wps[i - 1]!.pos
    let d := wps[i]!.pos - a
    if !(Vec3.dot d d > 0) then throw s!"waypoint {i + 1} equals the point before it (a leg of zero length)"
  let yawRateMax ← pos "nav.yawRateMax"
  let yawAccelMax ← pos "nav.yawAccelMax"
  if g "nav.yawSpeedMin" < 0 then throw "`nav.yawSpeedMin` must not be negative"
  let ekf : EKF.Config :=
    { gyroNoise := ← pos "ekf.gyroNoise", accelNoise := ← pos "ekf.accelNoise",
      gyroBiasWalk := g "ekf.gyroBiasWalk", accelBiasWalk := g "ekf.accelBiasWalk",
      posNE := ← pos "ekf.posNE", posD := ← pos "ekf.posD", vel := ← pos "ekf.vel",
      heading := ← pos "ekf.heading",
      tilt0 := ← pos "ekf.tilt0", yaw0 := ← pos "ekf.yaw0", vel0 := ← pos "ekf.vel0",
      pos0 := ← pos "ekf.pos0", gyroBias0 := ← pos "ekf.gyroBias0", accelBias0 := ← pos "ekf.accelBias0",
      gyroBiasMin := ← pos "ekf.gyroBiasMin", pFloor := ← pos "ekf.pFloor", cutoffHz := g "ekf.cutoffHz" }
  let copter ← buildCopter g dt
  pure
    { vehicle := veh, dt, dtFix, estimator := est, ekf := EKF.make ekf dt, copter,
      attFilter := AttitudeFilter.make kAcc (g "attFilter.kYaw") (g "attFilter.kBias")
        (g "attFilter.cutoffHz") dt,
      navFilter := NavFilter.make (g "navFilter.alpha") (g "navFilter.beta") (g "navFilter.kV")
        (g "navFilter.kB") dt dtFix,
      nav := Navigator.make (← pos "nav.vMax") (← pos "nav.aMax") (← pos "nav.aLat") (← pos "nav.vMaxZ")
        (g "nav.radius") (g "nav.lagMax") followPath (yr == 1) yawRateMax yawAccelMax (g "nav.yawSpeedMin") dt start wps,
      start,
      waypoints := wps,
      setpoint := ⟨hc / hn, hs / hn⟩,
      position :=
        { kpPos := g "position.kpPos", vMaxXY := g "position.vMaxXY", vMaxZ := g "position.vMaxZ",
          vel := PI.gains (g "position.vel.kp") (g "position.vel.ki") (g "position.vel.iMax") dt,
          aMaxXY := g "position.aMaxXY", aMaxZ := g "position.aMaxZ" },
      attitude :=
        { kpAtt := g "attitude.kpAtt", rateMax := g "attitude.rateMax",
          rate := PI.gains (g "attitude.rate.kp") (g "attitude.rate.ki") (g "attitude.rate.iMax") dt,
          kpYaw := g "attitude.kpYaw",
          rateYaw := PI.gains (g "attitude.rateYaw.kp") (g "attitude.rateYaw.ki") (g "attitude.rateYaw.iMax") dt } }

/-- The merged settings validated as complete: the value function, the waypoints and the estimator
(missing names, an empty mission and a `TAKEOFF` not above the start point are errors). -/
def complete (r : Raw) : Except String ((String → R) × Array Waypoint × Estimator) := do
  let missing := names.filter fun k => !(r.vals.any (·.1 == k))
  let missing := if r.estimator.isNone then missing ++ ["estimator"] else missing
  if !missing.isEmpty then throw s!"missing parameters: {", ".intercalate missing}"
  if r.waypoints.isEmpty then throw "no `WAYPOINT` or `SPLINE` lines"
  if let some d := r.ends.takeoff then
    if !(d < r.get "start.z") then
      throw "`TAKEOFF d` must be above the start point (d < `start.z`, NED down)"
  return (r.get, r.waypoints, r.estimator.getD .fixed)

/-- The configuration of the files `(name, text)`, later files overriding earlier ones. -/
def load (files : List (String × String)) : Except String Params := do
  let (g, wps, est) ← complete (← merge files)
  build g wps est

end ParamFile
