import Leanfc.ParamFile

open FloatLib.Floats

/-!
# Checks

Controller-side unit checks, pyfc `checks.py` minus the plant, run by `Main --check` on the
configurations loaded from the shipped `params/cf2x.params` and `params/x500.params`: hover
command, allocation round trip and sign of the roll response for each vehicle, attitude-filter
convergence at rest from a wrong initial attitude. Each is a `Bool`. Trigonometric values of the
test attitudes are binary64 literals (cos and sin of the half angles, computed offline).
-/

namespace Checks

def near (a b tol : R) : Bool := decide (R.abs (a - b) ≤ tol)

/-- Thrust m·g and zero torque give the same command on every motor, equal to `expected`, the
binary32 value `sim/mixer_inverse.py` computes for the same operations. -/
def checkHover (v : Vehicle) (expected : R) : Bool :=
  let m := Mixer.step v (v.mass * gravity) Vec3.zero
  near m.m1 expected 0 && near m.m2 expected 0 && near m.m3 expected 0 && near m.m4 expected 0

/-- A · (A⁻¹ w) = w within 1e-5 relative per component. -/
def checkAllocation (v : Vehicle) (thrust : R) (τ : Vec3) : Bool :=
  let (t, τ') := Mixer.allocate v (Mixer.perMotor v thrust τ)
  let rel (a b : R) := near a b ((1e-5 : R) * R.abs b)
  rel t thrust && rel τ'.x τ.x && rel τ'.y τ.y && rel τ'.z τ.z

/-- Desired attitude rolled 0.1 rad right of a level estimate: positive roll torque, no pitch or
yaw torque. -/
def checkRollSign (v : Vehicle) (k : AttitudeParams) : Bool :=
  let qDes : Quat := ⟨0.9987502603949663, 0.04997916927067833, 0, 0⟩
  let (_, τ) := Attitude.step v k PI.init qDes Quat.identity Vec3.zero 0
  decide (τ.x > 0) && decide (R.abs τ.y < 1e-9) && decide (R.abs τ.z < 1e-9)

/-- Expected binary32 hover commands (`sim/mixer_inverse.py`): CF2X 0.44444448 (binary64 1/2.25),
X500 0.59202653 (binary64 0.5920264837). -/
def hoverCf2x : R := 0.44444448
def hoverX500 : R := 0.59202653

/-- A copy of the vehicle and attitude numbers of `params/cf2x.params`, for the build-time proofs
at the end (the kernel cannot read files); `--check` confirms that the file loads to the same
binary32 values. -/
def cf2xVehicle : Vehicle :=
  Vehicle.make 0.027 ⟨1.4e-5, 1.4e-5, 2.17e-5⟩ 0.028072139213105935 0.025126582278481014 0.148938496875
def cf2xAttitude : AttitudeParams :=
  { kpAtt := 10, rateMax := 5, rate := PI.gains 30 10 2 0.0025, kpYaw := 10, rateYaw := PI.gains 30 10 2 0.0025 }

def sameRow (a b : Row4) : Bool := a.c1 == b.c1 && a.c2 == b.c2 && a.c3 == b.c3 && a.c4 == b.c4

def sameVehicle (a b : Vehicle) : Bool :=
  a.mass == b.mass && a.inertia.x == b.inertia.x && a.inertia.y == b.inertia.y &&
  a.inertia.z == b.inertia.z && a.l == b.l && a.kmKf == b.kmKf && a.tMax == b.tMax &&
  sameRow a.inv0 b.inv0 && sameRow a.inv1 b.inv1 && sameRow a.inv2 b.inv2 && sameRow a.inv3 b.inv3

def sameAttitude (a b : AttitudeParams) : Bool :=
  a.kpAtt == b.kpAtt && a.rateMax == b.rateMax && a.rate.kp == b.rate.kp &&
  a.rate.ki == b.rate.ki && a.rate.iMax == b.rate.iMax && a.rate.kiDt == b.rate.kiDt &&
  a.kpYaw == b.kpYaw && a.rateYaw.kp == b.rateYaw.kp && a.rateYaw.ki == b.rateYaw.ki &&
  a.rateYaw.iMax == b.rateYaw.iMax && a.rateYaw.kiDt == b.rateYaw.kiDt

/-- CF2X: w = (0.2 N, 1e-3, −2e-3, 5e-5 N m), about 0.8 of hover thrust and torques in the range
the flights use. -/
def checkAllocationCf2x (v : Vehicle) : Bool := checkAllocation v 0.2 ⟨1e-3, -2e-3, 5e-5⟩

/-- X500: w = (20 N, 0.5, −1.0, 0.05 N m), the same proportions for the larger vehicle. -/
def checkAllocationX500 (v : Vehicle) : Bool := checkAllocation v 20 ⟨0.5, -1.0, 0.05⟩

/-- Attitude filter at rest, level, heading 0 (constant readings gyro 0, accel (0, 0, −g),
heading (1, 0)), started at `q0`, after `ticks` steps at 400 Hz: the remaining error
‖vec q‖ = sin(angle/2). -/
def filterResidual (p : AttFilterParams) (dt : R) (q0 : Quat) (ticks : Nat) : R :=
  let step (st : AttFilterState) : AttFilterState :=
    (AttitudeFilter.step p st Vec3.zero ⟨0, 0, -gravity⟩ (some (1, 0)) dt).1
  let q := (Nat.repeat step ticks (AttitudeFilter.init q0)).q
  Vec3.norm q.vec

/-- 0.5 rad yaw error: below 0.1° (sin 0.05° = 8.7266e-4) after 60 s at 400 Hz. -/
def checkFilterYaw (P : Params) : Bool :=
  decide (filterResidual P.attFilter P.dt ⟨0.9689124217106447, 0, 0, 0.24740395925452294⟩ 24000 < 8.7266e-4)

/-- 0.5 rad error about the axis (0.2, −0.1, 0.5) (pyfc `checks.py`'s initial attitude scaled
to 0.5 rad): below 1° (sin 0.5° = 8.7265e-3) after 60 s, pyfc's tolerance. The tilt modes of
the filter decay as e^(−kAcc t / 2) = e^(−0.05 t) (characteristic s² + kAcc s + kBias), so 0.1°
is out of reach in 60 s from a 0.5 rad tilt with the DESIGN.md gains. -/
def checkFilterTilt (P : Params) : Bool :=
  decide (filterResidual P.attFilter P.dt ⟨0.9689124217106447, 0.09033915286652748, -0.04516957643326374,
    0.2258478821663187⟩ 24000 < 8.7265e-3)

/-! ## EKF -/

/-- P exactly symmetric (bitwise equal mirror entries) with a positive diagonal. -/
def healthy (P : EKF.Mat) : Bool :=
  (List.finRange 15).all fun i =>
    decide (P[i][i] > 0) && (List.finRange 15).all fun j => P[i][j] == P[j][i]

/-- `ticks` EKF ticks of a synthetic flight: level, heading 0, no bias, acceleration `accelAt i`
(NED) during tick i (specific force (a.x, a.y, a.z − g)), truth propagated with p += v dt + a dt²/2, v += a dt from the
start point at rest. Every `fixEvery` ticks the heading (1, 0) and the true position and
velocity at the end of the tick (the instant the prediction reaches) are fixes. Returns the final
state and whether P was `healthy` after every tick. -/
def ekfRun (k : EKF.Params) (st0 : EKF.State) (p0 : Vec3) (accelAt : Nat → Vec3) (ticks fixEvery : Nat) :
    EKF.State × Bool :=
  let r := (List.range ticks).foldl (fun (acc : EKF.State × Vec3 × Vec3 × Bool) i =>
    let (st, p, v, ok) := acc
    let a := accelAt i
    let p := p + Vec3.scale k.dt v + Vec3.scale k.halfDt2 a
    let v := v + Vec3.scale k.dt a
    let fix := i % fixEvery == 0
    let (st, _) := EKF.step k st Vec3.zero ⟨a.x, a.y, a.z - gravity⟩ (if fix then some (1, 0) else none)
      (if fix then some p else none) (if fix then some v else none)
    (st, p, v, ok && healthy st.P)) (st0, p0, Vec3.zero, true)
  (r.1, r.2.2.2)

/-- 60 s at rest with 10 Hz fixes from the configuration's start state: P stays exactly
symmetric with a positive diagonal after every prediction and update. -/
def checkEkfHealthy (P : Params) : Bool :=
  (ekfRun P.ekf (EKF.init P.ekf P.start Quat.identity) P.start (fun _ => Vec3.zero) 24000 40).2

/-- The synthetic acceleration of the convergence check: at rest except 3 m/s² north for
20 ≤ t < 22 s, −3 for 22 ≤ t < 24 s, and the same east for 30 ≤ t < 34 s (400 Hz ticks). At rest
a tilt error and a horizontal accelerometer bias both show up only as a constant horizontal
acceleration error, so the tilt is observable only while the specific force turns: a north
acceleration separates pitch from the bias, an east one roll. With 1 m/s² segments the filter
ends at 0.17° tilt and 29 mm/s² bias (g · 0.17°), at rest throughout at 0.40° and 68 mm/s²
(measured with this check's code and a 5° yaw prior). -/
def convergenceAccel (i : Nat) : Vec3 :=
  if 8000 ≤ i ∧ i < 8800 then ⟨3, 0, 0⟩ else if 8800 ≤ i ∧ i < 9600 then ⟨-3, 0, 0⟩
  else if 12000 ≤ i ∧ i < 12800 then ⟨0, 3, 0⟩ else if 12800 ≤ i ∧ i < 13600 then ⟨0, -3, 0⟩
  else Vec3.zero

/-- The remaining errors after `ticks` of the convergence flight from 5° roll and 20° heading
error (q0 = yaw 20° ⊗ roll 5°, binary64 literals): sin of the tilt (horizontal part of the
estimated body z axis), sin of the heading error, ‖bg‖ (rad/s), ‖ba‖ (m/s²). -/
def ekfConvergence (P : Params) (ticks : Nat) : R × R × R × R :=
  let q0 : Quat := ⟨0.9838704342468719, 0.042956710859025644, 0.007574427126938522, 0.1734829030790772⟩
  -- The filter is told the uncertainty this check injects (5° tilt, 20° heading), not the shipped
  -- known-start prior of 1°: with a 1° tilt prior against a 5° error it ends at 0.15° and 26 mm/s².
  let k := EKF.make { P.ekf.cfg with tilt0 := 0.08726646259971647, yaw0 := 0.3490658503988659 } P.ekf.dt
  let (st, _) := ekfRun k (EKF.init k P.start q0) P.start convergenceAccel ticks 40
  let z := Quat.rotate st.q ⟨0, 0, 1⟩
  (R.sqrt (z.x * z.x + z.y * z.y), R.abs (Quat.headingVec st.q).2, Vec3.norm st.bg, Vec3.norm st.ba)

/-- After 60 s: tilt and heading below 0.1° (sin 0.1° = 1.7453e-3), gyro bias below 0.01°/s
(1.7453e-4 rad/s), accelerometer bias below 10 mm/s². -/
def checkEkfConvergence (P : Params) : Bool × String :=
  let (tilt, hdg, bg, ba) := ekfConvergence P 24000
  let deg (x : R) : String := toString ((x.toFloat * 57.29577951308232 * 10000).round / 10000)
  (decide (tilt < 1.7453e-3) && decide (hdg < 1.7453e-3) && decide (bg < 1.7453e-4) && decide (ba < 1e-2),
   s!"tilt {deg tilt} deg, heading {deg hdg} deg, |bg| {deg bg} deg/s, |ba| {toString ((ba.toFloat * 1e6).round / 1000)} mm/s^2")

/-! ## Navigator

The mission of a configuration flown by the navigator alone, open loop: the position estimate is
the previous tick's target (at first the start point), so the lag gate never closes and every
stop is left at once. The properties are measured in binary64 on the binary32 values (angles with
`Float.atan2`); the measurements are not part of the controller. -/

def f3 (v : Vec3) : Float × Float × Float := (v.x.toFloat, v.y.toFloat, v.z.toFloat)

def fdot (a b : Float × Float × Float) : Float := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def fsub (a b : Float × Float × Float) : Float × Float × Float := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

def fnorm (a : Float × Float × Float) : Float := Float.sqrt (fdot a a)

def sameVec (a b : Vec3) : Bool :=
  ExecFloat.Binary.toBits32 a.x == ExecFloat.Binary.toBits32 b.x &&
  ExecFloat.Binary.toBits32 a.y == ExecFloat.Binary.toBits32 b.y &&
  ExecFloat.Binary.toBits32 a.z == ExecFloat.Binary.toBits32 b.z

/-- The angle (rad) between two heading vectors. -/
def angleBetween (a b : R × R) : Float :=
  let (ac, as_, bc, bs) := (a.1.toFloat, a.2.toFloat, b.1.toFloat, b.2.toFloat)
  (Float.atan2 (ac * bs - as_ * bc) (ac * bc + as_ * bs)).abs

/-- The angle (rad) between two nonzero vectors. -/
def angle3 (a b : Float × Float × Float) : Float :=
  let c := a.2.1 * b.2.2 - a.2.2 * b.2.1
  let d := a.2.2 * b.1 - a.1 * b.2.2
  let e := a.1 * b.2.1 - a.2.1 * b.1
  Float.atan2 (Float.sqrt (c * c + d * d + e * e)) (fdot a b)

def sameBits (a b : R × R) : Bool :=
  ExecFloat.Binary.toBits32 a.1 == ExecFloat.Binary.toBits32 b.1 &&
  ExecFloat.Binary.toBits32 a.2 == ExecFloat.Binary.toBits32 b.2

/-- What `navRun` measured. -/
structure NavStats where
  ticks : Nat := 0
  /-- (1) line legs: largest distance of a target from its line, and largest distance beyond the
  segment's ends (m) -/
  lineOff : Float := 0
  lineOut : Float := 0
  /-- (2) every target at τ = 1 equals the destination bit for bit -/
  endsExact : Bool := true
  /-- (3) passed waypoints: count, largest angle between consecutive vFF across the change (rad),
  largest speed change across it (m/s) -/
  passed : Nat := 0
  passAngle : Float := 0
  passDu : Float := 0
  /-- largest angle between the vFF of consecutive ticks on one leg (rad) -/
  turnInLeg : Float := 0
  /-- (4) largest speed, |vFF.z|, change of u in a tick, the speed of an arrival at a rest point
  (which is 0 the tick after), and the largest u²κ/aLat on spline legs -/
  vMax : Float := 0
  vzMax : Float := 0
  duMax : Float := 0
  arriveU : Float := 0
  latRatio : Float := 0
  /-- (5) arrivals at rest points (the target stays on the destination, and vFF = 0 once u = 0,
  until the leg is left), and ticks with u = 0 that are not at a rest point -/
  rests : Nat := 0
  restsOk : Bool := true
  zeroElsewhere : Nat := 0
  /-- (6) the final state -/
  final : NavState := default
  /-- heading: largest angle to the leg's end direction when a leg ending at rest is left (deg),
  fastest turn (rad/s), held below the speed threshold -/
  hdgEndDeg : Float := 0
  hdgRate : Float := 0
  hdgHeld : Bool := true

def navTick (P : Params) (acc : NavState × NavStats) : NavState × NavStats :=
  let (st, ns) := acc
  let p := P.nav
  let n := p.legs.size
  let (st', tgt) := Navigator.step p st st.pos P.dt
  let dt := P.dt.toFloat
  let ns := { ns with ticks := ns.ticks + 1 }
  -- heading
  let below := !decide (tgt.vFF.x * tgt.vFF.x + tgt.vFF.y * tgt.vFF.y > p.yawSpeed2)
  let ns := { ns with hdgRate := max ns.hdgRate (angleBetween st.heading st'.heading / dt),
                      hdgHeld := ns.hdgHeld && (!below || sameBits st.heading st'.heading) }
  -- (4) speeds
  let v := f3 tgt.vFF
  let du := (st'.u.toFloat - st.u.toFloat).abs
  let ns := { ns with vMax := max ns.vMax (fnorm v), vzMax := max ns.vzMax v.2.2.abs,
                      duMax := max ns.duMax du }
  -- (5) u = 0 only at a rest point: waiting on a destination that ends at rest, or leaving it
  let atRest := st'.leg ≥ n ||
    (st'.tau == 1 && !p.legs[st'.leg]!.passed) || (st'.tau == 0 && st'.leg > 0 && !p.legs[st'.leg - 1]!.passed)
  let ns := { ns with zeroElsewhere := ns.zeroElsewhere + (if st'.u == 0 && !atRest then 1 else 0) }
  let ns := if h : st.leg < n then
    let L := p.legs[st.leg]
    -- (1) line legs: the target on the segment
    let ns :=
      if L.kind == .line then
        let a := f3 L.curve.p0
        let ab := fsub (f3 L.curve.p1) a
        let ax := fsub (f3 tgt.pSp) a
        let t := fdot ax ab / fdot ab ab
        let off := fnorm (fsub ax (t * ab.1, t * ab.2.1, t * ab.2.2))
        { ns with lineOff := max ns.lineOff off, lineOut := max ns.lineOut (max 0 (max (-t) (t - 1)) * fnorm ab) }
      else ns
    -- (4) lateral acceleration on spline legs
    let ns :=
      if L.kind == .spline && st'.leg == st.leg then
        let k := (Path.curvature L.curve st'.tau).toFloat
        { ns with latRatio := max ns.latRatio (st'.u.toFloat * st'.u.toFloat * k / p.aLat.toFloat) }
      else ns
    -- (2) at τ = 1 the target is the destination
    let reached := st'.leg > st.leg || st'.tau == 1
    let ns := { ns with endsExact := ns.endsExact && (!reached || sameVec tgt.pSp L.curve.p1) }
    let v0 := f3 st.vel
    let moving := fnorm v0 > 0 && fnorm v > 0
    if st'.leg > st.leg ∧ L.passed then
      -- (3) passed waypoint: velocity across the change
      { ns with passed := ns.passed + 1, passAngle := max ns.passAngle (angle3 v0 v),
                passDu := max ns.passDu (fnorm v - fnorm v0).abs }
    else
    let ns := if moving && st'.leg == st.leg then { ns with turnInLeg := max ns.turnInLeg (angle3 v0 v) } else ns
    -- (5) arrival at a destination that ends at rest (left in the same tick if the vehicle is within radius)
    let ns :=
      if st.tau < 1 && st'.tau == 1 then
        { ns with rests := ns.rests + 1, arriveU := max ns.arriveU st'.u.toFloat,
                  restsOk := ns.restsOk && sameVec tgt.pSp L.curve.p1 }
      else if st.tau == 1 then
        { ns with restsOk := ns.restsOk && sameVec tgt.pSp L.curve.p1 && (st'.u > 0 || sameVec tgt.vFF Vec3.zero) }
      else ns
    if st'.leg > st.leg then
      -- a leg ending at rest is left: the heading against the leg's horizontal end direction
      let d := Path.deriv L.curve 1
      let m := R.sqrt (d.x * d.x + d.y * d.y)
      let err := if m > 0 then angleBetween st'.heading (d.x / m, d.y / m) * 57.29577951308232 else 0
      { ns with hdgEndDeg := max ns.hdgEndDeg err }
    else ns
  else ns
  (st', ns)

def navRun (P : Params) (ticks : Nat) : NavStats :=
  let st0 := Navigator.init P.start (P.setpoint.hc, P.setpoint.hs)
  let (st, ns) := Nat.repeat (navTick P) ticks (st0, {})
  { ns with final := st }

/-- (2) on the table: every leg's curve gives its origin at τ = 0 and its destination at τ = 1 bit
for bit, each leg starts on the previous leg's destination (the first on the start point, −0
read as +0) and ends on its waypoint. -/
def legEnds (P : Params) : Bool :=
  let ls := P.nav.legs
  (List.range ls.size).all fun k =>
    let h := ls[k]!.curve
    let o := if k = 0 then P.start + Vec3.zero else ls[k - 1]!.curve.p1
    sameVec (Path.eval h 0) h.p0 && sameVec (Path.eval h 1) h.p1 && sameVec h.p0 o &&
      sameVec h.p1 (P.waypoints[k]!.pos + Vec3.zero)

/-- (3) on the table: at every passed waypoint the end direction of the leg and the start direction
of the next agree (largest angle, rad). -/
def tangentGap (P : Params) : Float :=
  let ls := P.nav.legs
  (List.range ls.size).foldl (fun m k =>
    if ls[k]!.passed then max m (angle3 (f3 (Path.deriv ls[k]!.curve 1)) (f3 (Path.deriv ls[k + 1]!.curve 0))) else m) 0

def fmtF (x : Float) (scale : Float := 1) : String := toString ((x * scale * 1000).round / 1000)

/-- The three navigator checks of a configuration, 30 s open loop: path, motion, heading. -/
def checkNav (P : Params) : List (String × Bool) :=
  let s := navRun P 12000
  let p := P.nav
  let n := p.legs.size
  let tg := tangentGap P
  let ends := legEnds P
  let rests := (p.legs.toList.filter (!·.passed)).length
  let path := s.lineOff ≤ 2e-6 && s.lineOut ≤ 2e-6 && ends && s.endsExact && tg ≤ 1e-6 &&
    s.passAngle ≤ s.turnInLeg * 1.01 + 1e-6 && s.passDu ≤ p.duMax.toFloat + 1e-6
  let vm := p.vMax.toFloat
  let motion := s.vMax ≤ vm * (1 + 1e-6) && s.vzMax ≤ p.vMaxZ.toFloat * (1 + 1e-6) &&
    s.duMax ≤ p.duMax.toFloat + 1e-6 &&
    s.latRatio ≤ 1.05 && s.rests == rests && s.restsOk && s.zeroElsewhere == 0 &&
    s.final.leg == n && sameVec s.final.pos (p.legs.back?.map (·.curve.p1) |>.getD P.start) &&
    sameVec s.final.vel Vec3.zero
  let heading := s.hdgEndDeg < 0.5 && s.hdgRate ≤ p.yawRateMax.toFloat + 1e-4 && s.hdgHeld
  [(s!"(1) Waypoint legs: every target on its segment (off the line {fmtF s.lineOff 1e6} um, beyond the ends {fmtF s.lineOut 1e6} um, tolerance 2 um); " ++
    s!"(2) every leg starts on its origin and ends on its destination bit for bit (table: {ends}, every arrival in the run: {s.endsExact}); " ++
    s!"(3) {s.passed} passed waypoints: tangents agree to {fmtF tg 1e6} urad, vFF across the change turns {fmtF s.passAngle 1e3} mrad (largest turn between two ticks of one leg {fmtF s.turnInLeg 1e3} mrad) and changes speed by {fmtF s.passDu 1e3} mm/s (aMax dt {fmtF p.duMax.toFloat 1e3})", path),
   (s!"(4) speed max {fmtF s.vMax} m/s (vMax {fmtF vm}), |vFF.z| max {fmtF s.vzMax} (vMaxZ {fmtF p.vMaxZ.toFloat}), " ++
    s!"|du| per tick {fmtF s.duMax 1e3} mm/s (aMax dt {fmtF p.duMax.toFloat 1e3}; tolerance 1e-6 m/s; speed on arriving at a rest point <= {fmtF s.arriveU 1e3} mm/s), " ++
    s!"worst u^2 kappa / aLat on spline legs {fmtF s.latRatio} (<= 1.05); (5) {s.rests} arrivals at rest points of {rests} legs that end at rest, the target stays on the destination, vFF = 0 once u = 0: {s.restsOk}; " ++
    s!"ticks with u = 0 elsewhere: {s.zeroElsewhere}; (6) complete ({s.final.leg}/{n} legs) at rest on the last waypoint after {s.ticks} ticks", motion),
   (s!"heading: worst angle to the end direction of a leg ending at rest {fmtF s.hdgEndDeg} deg (< 0.5), fastest turn {fmtF (s.hdgRate * 57.29577951308232)} deg/s " ++
    s!"(limit {fmtF (p.yawRateMax.toFloat * 57.29577951308232)}), held below the speed threshold: {s.hdgHeld}", heading)]

/-- The checks on the loaded CF2X and X500 configurations (`x500m`: X500 + params/mocap.params).
The EKF checks run on the X500 configurations, the ones that use the EKF by default;
params/cf2x.params carries the same EKF numbers. `navs` are the configurations whose missions the
navigator checks fly (name, configuration). -/
def runChecks (cf2x x500 x500m : Params) (navs : List (String × Params)) : List (String × Bool) :=
  let (convOk, convMsg) := checkEkfConvergence x500
  [("cf2x: params/cf2x.params equals the build-time copy (vehicle, attitude gains)",
      sameVehicle cf2x.vehicle cf2xVehicle && sameAttitude cf2x.attitude cf2xAttitude),
   ("cf2x: hover command 0.44444448", checkHover cf2x.vehicle hoverCf2x),
   ("cf2x: allocation round trip", checkAllocationCf2x cf2x.vehicle),
   ("cf2x: roll error gives roll torque", checkRollSign cf2x.vehicle cf2x.attitude),
   ("x500: hover command 0.59202653", checkHover x500.vehicle hoverX500),
   ("x500: allocation round trip", checkAllocationX500 x500.vehicle),
   ("x500: roll error gives roll torque", checkRollSign x500.vehicle x500.attitude),
   ("cf2x: attitude filter, 0.5 rad yaw error, < 0.1 deg after 60 s", checkFilterYaw cf2x),
   ("cf2x: attitude filter, 0.5 rad tilt+yaw error, < 1 deg after 60 s", checkFilterTilt cf2x),
   ("x500: attitude filter, 0.5 rad yaw error, < 0.1 deg after 60 s", checkFilterYaw x500),
   ("x500: attitude filter, 0.5 rad tilt+yaw error, < 1 deg after 60 s", checkFilterTilt x500),
   ("x500: EKF, 60 s at rest with 10 Hz fixes, P symmetric with positive diagonal every tick", checkEkfHealthy x500),
   ("x500 + mocap: EKF, 60 s at rest with 100 Hz fixes (R floored at (1e-3)^2), P symmetric with positive diagonal every tick",
      checkEkfHealthy x500m),
   (s!"x500: EKF, 5 deg tilt + 20 deg heading error, 10 Hz fixes, 3 m/s^2 north and east segments: tilt and heading < 0.1 deg, |bg| < 0.01 deg/s, |ba| < 10 mm/s^2 after 60 s ({convMsg})", convOk)] ++
  navs.flatMap fun (name, P) => (checkNav P).map fun (m, ok) => (s!"{name}: navigator {m}", ok)

/-! Build-time proofs of the three small CF2X checks on the copy above, by kernel evaluation of
the binary32 arithmetic (`decide` alone hits the elaborator's recursion limit; `decide +kernel`
takes under a second, no `native_decide`). The filter checks run 24000 ticks and stay runtime-only
(`Main --check`): the kernel already overflows its recursion depth at 400. -/
example : checkHover cf2xVehicle hoverCf2x = true := by decide +kernel
example : checkAllocationCf2x cf2xVehicle = true := by decide +kernel
example : checkRollSign cf2xVehicle cf2xAttitude = true := by decide +kernel

end Checks
