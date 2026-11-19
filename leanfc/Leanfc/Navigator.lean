import Leanfc.Path

/-!
# Navigator

The mission is a list of legs, each a cubic Hermite curve (`Path`) from the previous point (the
start for the first leg) to its destination. Two kinds of leg, as ArduPilot's Waypoint and Spline
navigation offer them:

- **Waypoint leg** (`WAYPOINT n e d`): the straight line to the destination, `Path.line`.
- **Spline leg** (`SPLINE n e d`): a curve to the destination with tangents m0 = L·t0, m1 = L·t1
  (L the chord length, t0, t1 unit directions). t0 is the end direction of the previous leg if the
  previous waypoint is passed at speed, else the chord direction. t1 is the chord direction if the
  leg ends at rest; else the direction of the next segment if the next leg is a Waypoint leg, or of
  (next waypoint − this leg's origin) if it is a Spline leg (Catmull–Rom).

**End speed.** A leg ends at rest at the last waypoint, at a waypoint marked `stop`, and where a
Waypoint leg is followed by a Waypoint leg (so that each stays a straight line); every other
waypoint is passed at speed, and by the tangent rules the direction of motion is the same on both
sides of it.

**Speed limits, computed once by `make`.** vLeg = min(vMax, the vertical limit, and on a spline
sqrt(aLat/κmax)), with κmax the largest curvature at τ = j/16, j = 0..16, and the vertical limit
vMaxZ / max |p′z|/‖p′‖ (exact on a line, sampled at the same τ on a spline). The end speed vEnd is 0
at a leg that ends at rest and min(vLeg_i, vLeg_{i+1}, B(vEnd_{i+1}, L_{i+1})) at a passed waypoint
(made consistent backward from the last leg), with the braking curve B below.

**Braking curve.** B(v, d) = sqrt((v + h)² + 2·aMax·d) − h, h = aMax·dt/2: the speed from which
a deceleration of aMax·dt per tick, moving u·dt per tick, ends at v after d. It is the per-tick
form of sqrt(v² + 2·aMax·d) (they differ by less than h = 2.5 mm/s on the X500): following it, the
target arrives at a rest point with u ≤ aMax·dt on a line (with the continuous form the arrival
speed was up to 0.1 m/s), and about that on a spline, where d is the chord.

**One tick.** The speed u moves by at most aMax·dt toward u_cmd = min(vLeg, B(vEnd, d)), d the
straight distance from the target to the destination (never more than the arc left, so braking
starts in time), and 0 while the vehicle lags the target by more than lagMax. Then
τ ← min(1, τ + u·dt/max(‖p′(τ)‖, 1e-3)); the target is p(τ), vFF = u·p′(τ)/‖p′(τ)‖ and
aFF = (vFF − vFF of the previous tick)/dt. When τ reaches 1 at a passed waypoint the next leg starts
in the same tick at τ = 0 with the same u. At a leg that ends at rest the target arrives with
u of about aMax·dt or less, the remaining u goes to 0 at aMax·dt per tick while the target stays on
the destination (one tick, rarely two), and the target waits there until the vehicle is within
`radius`; then the next leg starts from rest, or, after the last leg, the mission
is complete and the target holds the last waypoint.

The heading setpoint (`slewHeading`, unchanged by the leg kinds; ArduCopter's default
`WP_YAW_BEHAVIOR` 1, shaped as the attitude controller shapes yaw: slew limit `ATC_RATE_WPY_MAX`,
acceleration limit `ATC_ACC_Y_MAX`): with `followPath` the heading target is the direction of the
horizontal velocity feedforward vFF while |vFF_xy| > yawSpeedMin·vMax, or the opposite direction
with `yawReverse` (`nav.yawReverse` 1: the vehicle flies backward, nose against the direction of
travel); below that the setpoint is held where it is and its rate is zero. The setpoint is a unit
vector h = (cos ψ, sin ψ) turning at the signed rate ρ. With x = cross (h, target) (sin of the
remaining angle θ) and c = dot (its cosine), the side is s = sign x (+1 when the target is exactly behind) and θ is bounded below
without an angle by θ' = |x| if c > 0, else 2 − |x|. The rate moves by at most yawAccelMax·dt per
tick toward s·min(yawRateMax, sqrt(2·yawAccelMax·θ')). The setpoint snaps to the target when c > 0
and |x| ≤ s·ρ·dt·c, with the rate x/dt; otherwise it takes the first-order rotation
h ← normalize(h + ρ·dt·h⊥). The rate ρ is the yaw-rate feedforward. Without `followPath` the
setpoint stays at its initial value and the feedforward is 0.

**For the vehicle layer** (`Leanfc/Copter/*`): `withLegs` builds the legs of a run-time mission (the
same `make`, from the current target, at a speed limit set by WP_SPD or DO_CHANGE_SPEED); `brake` is
the tick of a target that stops along its path: u falls by aMax·dt per tick while τ advances on the
current leg, never past its end, and at u = 0 the target holds (BRAKE, LOITER, and the stop before a
new path). An empty leg list is a navigator that holds its start point.
-/

inductive LegKind where
  | line
  | spline
  deriving Inhabited, Repr, BEq

/-- A mission point as the file gives it: destination (NED m), the kind of leg flown to it, and
whether the target stops there. -/
structure Waypoint where
  pos : Vec3
  kind : LegKind
  stop : Bool
  deriving Inhabited, Repr

/-- A leg with everything the tick needs, computed by `make`. -/
structure Leg where
  kind : LegKind
  curve : Hermite
  /-- chord length ‖p1 − p0‖, m -/
  length : R
  /-- speed limit on the leg, m/s -/
  vLeg : R
  /-- speed at the destination, m/s (0: the leg ends at rest) -/
  vEnd : R
  /-- (vEnd + aMax·dt/2)², for the braking curve -/
  vEndH2 : R
  /-- the destination is passed at speed (not a stop) -/
  passed : Bool
  deriving Inhabited, Repr

structure NavParams where
  vMax : R
  aMax : R
  /-- m/s², the lateral acceleration limit on spline legs -/
  aLat : R
  /-- m/s, the vertical speed limit of the target -/
  vMaxZ : R
  radius : R
  lagMax : R
  /-- `nav.yawBehavior` 1: the heading follows the path; 0: it holds the initial setpoint -/
  followPath : Bool
  /-- `nav.yawReverse` 1: the heading target is the opposite of the direction of travel -/
  yawReverse : Bool
  /-- rad/s, the largest rate the heading setpoint turns at -/
  yawRateMax : R
  /-- rad/s², the largest change of that rate per second -/
  yawAccelMax : R
  /-- fraction of vMax above which the horizontal feedforward defines the heading target -/
  yawSpeedMin : R
  legs : Array Leg
  /-- derived by `make`: aMax · dt, the largest change of u in one tick -/
  duMax : R
  /-- derived by `make`: aMax · dt / 2 -/
  halfDu : R
  /-- derived by `make`: 2 · aMax -/
  twoAMax : R
  /-- derived by `make`: lagMax² -/
  lagMax2 : R
  /-- derived by `make`: radius² -/
  radius2 : R
  /-- derived by `make`: yawAccelMax · dt -/
  dYawRateMax : R
  /-- derived by `make`: 2 · yawAccelMax -/
  twoYawAccel : R
  /-- derived by `make`: (yawSpeedMin · vMax)², the threshold on |vFF_xy|² -/
  yawSpeed2 : R
  deriving Inhabited, Repr

/-- `leg` indexes the leg being flown (= the number of legs once the mission is complete); `tau`
is the path parameter on it and `u` the target's speed; `pos` and `vel` are the target and the
velocity feedforward of the last tick; `heading` is the heading setpoint (cos ψ, sin ψ) and
`yawRate` the rate it turned at in the last tick (rad/s about NED down). -/
structure NavState where
  leg : Nat
  tau : R
  u : R
  pos : Vec3
  vel : Vec3
  heading : R × R
  yawRate : R
  deriving Inhabited, Repr

/-- Navigator output: position target, velocity and acceleration feedforward (NED), heading
setpoint (cos ψ, sin ψ) and yaw-rate feedforward (rad/s about NED down). -/
structure Target where
  pSp : Vec3
  vFF : Vec3
  aFF : Vec3
  heading : R × R
  yawRate : R
  deriving Inhabited, Repr

namespace Navigator

/-- Number of intervals of the curvature and vertical-slope sampling of a spline leg. -/
def samples : Nat := 16

/-- Smallest ‖p′(τ)‖ the tick divides by (m per unit τ). -/
def minDeriv : R := 1e-3

/-- A small natural number as binary32 (exact). -/
def natR (j : Nat) : R := OfScientific.ofScientific j false 0

def unit (v : Vec3) : Vec3 := let n := Vec3.norm v; if n > 0 then Vec3.div v n else Vec3.zero

/-- The vertical slope max |p′z|/‖p′‖ and the curvature max over τ = j/samples. -/
def sampleLeg (h : Hermite) : R × R := Id.run do
  let mut slope : R := 0
  let mut kappa : R := 0
  for j in [0:samples + 1] do
    let τ : R := natR j / natR samples
    let d := Path.deriv h τ
    let n := Vec3.norm d
    if n > 0 then slope := max slope (R.abs d.z / n)
    kappa := max kappa (Path.curvature h τ)
  return (slope, kappa)

/-- The legs of a mission from `start` through `wps`: geometry by the tangent rules, then the
speed limits and the end speeds (backward). End points are stored as w + 0 (−0 becomes +0, see
`Path`). -/
def legsOf (vMax aMax aLat vMaxZ dt : R) (start : Vec3) (wps : Array Waypoint) : Array Leg := Id.run do
  let hdt := aMax * dt / 2
  let n := wps.size
  let pt (i : Nat) : Vec3 := (if i = 0 then start else wps[i - 1]!.pos) + Vec3.zero
  let passed (k : Nat) : Bool :=
    k + 1 < n && !wps[k]!.stop && !(wps[k]!.kind == .line && wps[k + 1]!.kind == .line)
  let mut legs : Array Leg := #[]
  let mut endDir := Vec3.zero
  for k in [0:n] do
    let o := pt k
    let chord := pt (k + 1) - o
    let len := Vec3.norm chord
    let c := unit chord
    let wp := wps[k]!
    let curve : Hermite := match wp.kind with
      | .line => Path.line o (pt (k + 1))
      | .spline =>
        let t0 := if k > 0 && passed (k - 1) then endDir else c
        let t1 :=
          if !passed k then c
          else
            let next := if wps[k + 1]!.kind == .line then pt (k + 2) - pt (k + 1) else pt (k + 2) - o
            let t := unit next
            if Vec3.dot t t > 0 then t else c
        ⟨o, Vec3.scale len t0, pt (k + 1), Vec3.scale len t1⟩
    endDir := unit curve.m1
    let (slope, kappa) := match wp.kind with
      | .line => (if len > 0 then R.abs chord.z / len else 0, (0 : R))
      | .spline => sampleLeg curve
    let vz := if slope > 0 then vMaxZ / slope else vMax
    let vk := if kappa > 0 then R.sqrt (aLat / kappa) else vMax
    legs := legs.push ⟨wp.kind, curve, len, min vMax (min vz vk), 0, hdt * hdt, passed k⟩
  for i in [0:n] do
    let k := n - 1 - i
    if legs[k]!.passed then
      let nx := legs[k + 1]!
      let v := min (min legs[k]!.vLeg nx.vLeg) (R.sqrt (nx.vEndH2 + 2 * aMax * nx.length) - hdt)
      legs := legs.set! k { legs[k]! with vEnd := v, vEndH2 := (v + hdt) * (v + hdt) }
  return legs

def make (vMax aMax aLat vMaxZ radius lagMax : R) (followPath yawReverse : Bool) (yawRateMax yawAccelMax yawSpeedMin dt : R)
    (start : Vec3) (wps : Array Waypoint) : NavParams :=
  let vMin := yawSpeedMin * vMax
  ⟨vMax, aMax, aLat, vMaxZ, radius, lagMax, followPath, yawReverse, yawRateMax, yawAccelMax, yawSpeedMin,
   legsOf vMax aMax aLat vMaxZ dt start wps, aMax * dt, aMax * dt / 2, 2 * aMax, lagMax * lagMax, radius * radius,
   yawAccelMax * dt, 2 * yawAccelMax, vMin * vMin⟩

def init (start : Vec3) (heading : R × R) : NavState := ⟨0, 0, 0, start, Vec3.zero, heading, 0⟩

/-- One tick of the heading setpoint `h`, turning at `rate`, toward the direction of `vFF`, or its
opposite with `yawReverse` (see the module comment): the new setpoint and the rate it turned at,
which is the yaw-rate feedforward. -/
def slewHeading (p : NavParams) (h : R × R) (rate : R) (vFF : Vec3) (dt : R) : (R × R) × R :=
  let v2 := vFF.x * vFF.x + vFF.y * vFF.y
  if !p.followPath || !decide (v2 > p.yawSpeed2) then (h, 0) else
  let n := R.sqrt v2
  let (tc, ts) := if p.yawReverse then (-(vFF.x / n), -(vFF.y / n)) else (vFF.x / n, vFF.y / n)
  let x := h.1 * ts - h.2 * tc
  let c := h.1 * tc + h.2 * ts
  let ax := R.abs x
  let rem := if c > 0 then ax else 2 - ax
  let speed := min p.yawRateMax (R.sqrt (p.twoYawAccel * rem))
  let rDes := if x < 0 then -speed else speed
  let r := rate + R.clamp (-p.dYawRateMax) p.dYawRateMax (rDes - rate)
  let step := r * dt
  let ahead := if x < 0 then -step else step
  if c > 0 ∧ ax ≤ ahead * c then ((tc, ts), x / dt) else
  let hc := h.1 - step * h.2
  let hs := h.2 + step * h.1
  let m := R.sqrt (hc * hc + hs * hs)
  ((hc / m, hs / m), r)

/-- u · p′(τ)/‖p′(τ)‖. -/
def velocity (h : Hermite) (τ u : R) : Vec3 :=
  let d := Path.deriv h τ
  let n := Vec3.norm d
  if n > 0 then Vec3.scale (u / n) d else Vec3.zero

/-- The target and its velocity feedforward of one tick (state with the new `pos` and `vel`). -/
def stepTarget (p : NavParams) (st : NavState) (pHat : Vec3) (dt : R) : NavState :=
  if h : st.leg < p.legs.size then
    let L := p.legs[st.leg]
    let lag := st.pos - pHat
    let toGo := L.curve.p1 - st.pos
    let uCmd : R :=
      if Vec3.dot lag lag > p.lagMax2 then 0
      else min L.vLeg (R.sqrt (L.vEndH2 + p.twoAMax * Vec3.norm toGo) - p.halfDu)
    let u := st.u + R.clamp (-p.duMax) p.duMax (uCmd - st.u)
    let tau := min 1 (st.tau + u * dt / max (Vec3.norm (Path.deriv L.curve st.tau)) minDeriv)
    let pos := Path.eval L.curve tau
    if tau < 1 then { st with tau, u, pos, vel := velocity L.curve tau u }
    else if L.passed then
      -- the waypoint is passed: the next leg starts here with the same speed
      { st with leg := st.leg + 1, tau := 0, u, pos, vel := velocity p.legs[st.leg + 1]!.curve 0 u }
    else if st.tau < 1 then
      -- arrival at a rest point, with u ≈ aMax·dt or less by the braking curve
      { st with tau, u, pos, vel := velocity L.curve tau u }
    else if st.u > 0 then
      -- on the destination: the remaining speed goes to 0 at aMax·dt per tick
      let u := max 0 (st.u - p.duMax)
      { st with u, pos, vel := if u > 0 then velocity L.curve 1 u else Vec3.zero }
    else
      -- at rest on the destination until the vehicle is within radius
      let e := L.curve.p1 - pHat
      let st' := { st with pos, vel := Vec3.zero }
      if Vec3.dot e e ≤ p.radius2 then { st' with leg := st.leg + 1, tau := 0 } else st'
  else
    { st with u := 0, vel := Vec3.zero }

/-- The navigator parameters `p` with the legs of a new mission from `start` through `wps` at the
speed limit `vMax` (`make` with `p`'s other values): the vehicle layer's run-time missions. -/
def withLegs (p : NavParams) (vMax dt : R) (start : Vec3) (wps : Array Waypoint) : NavParams :=
  make vMax p.aMax p.aLat p.vMaxZ p.radius p.lagMax p.followPath p.yawReverse p.yawRateMax p.yawAccelMax
    p.yawSpeedMin dt start wps

/-- The target braking along its path: u falls by aMax·dt per tick (the acceleration limit) while
τ advances on the leg being flown (never past its end); at u = 0 the target holds its position.
The vehicle layer's pause (BRAKE, LOITER) and the stop before a new path. -/
def brakeTarget (p : NavParams) (st : NavState) (dt : R) : NavState :=
  if h : st.leg < p.legs.size then
    let L := p.legs[st.leg]
    let u := max 0 (st.u - p.duMax)
    let tau := min 1 (st.tau + u * dt / max (Vec3.norm (Path.deriv L.curve st.tau)) minDeriv)
    { st with tau, u, pos := Path.eval L.curve tau, vel := if u > 0 then velocity L.curve tau u else Vec3.zero }
  else
    { st with u := 0, vel := Vec3.zero }

/-- One tick: target, feedforward, then the heading setpoint from this tick's vFF. -/
def step (p : NavParams) (st : NavState) (pHat : Vec3) (dt : R) : NavState × Target :=
  let st' := stepTarget p st pHat dt
  let aFF := Vec3.div (st'.vel - st.vel) dt
  let (heading, yawRate) := slewHeading p st.heading st.yawRate st'.vel dt
  ({ st' with heading, yawRate }, ⟨st'.pos, st'.vel, aFF, heading, yawRate⟩)

/-- One braking tick (`brakeTarget`), with the feedforward and heading as in `step`. -/
def brake (p : NavParams) (st : NavState) (dt : R) : NavState × Target :=
  let st' := brakeTarget p st dt
  let aFF := Vec3.div (st'.vel - st.vel) dt
  let (heading, yawRate) := slewHeading p st.heading st.yawRate st'.vel dt
  ({ st' with heading, yawRate }, ⟨st'.pos, st'.vel, aFF, heading, yawRate⟩)

end Navigator
