import Flight.Types

/-!
# Waypoint navigator

Structured after ArduPilot's `AC_WPNav` library: the vehicle flies the mission as a path through
the waypoints, straight legs from one waypoint to the next with every inner corner rounded by a
blend, and a target point moves along that path with a speed profile. The navigator hands the
position controller the target point together with the target's velocity and acceleration as
feed-forward terms, as `AC_WPNav` feeds `AC_PosControl`. After the final waypoint the target is
held there.

* **Take-off to the first waypoint.** While waypoint `0` is targeted (index `0`) the position
  setpoint is waypoint `0` itself with zero feed-forward. Once the vehicle is within
  `acceptRadius` of it and a second waypoint exists, the target starts along the first leg.
* **Legs and blends.** On leg `k` (from waypoint `k` to `k + 1`, index `k + 1`) the target is at
  distance `σ = frac · L` from the leg start. Within the blend radius `r` of an inner corner
  `C`, measured along the path on both legs, the straight path is replaced by the quadratic Bézier
  curve with control points `C - r d₁`, `C`, `C + r d₂` (`d₁`, `d₂` the unit directions of the two
  legs), parametrized by `u ∈ [0, 1]` growing linearly with the distance flown, so the point is
  `C + r (u² d₂ - (1 - u)² d₁)` and its derivative with respect to the distance is the tangent
  `(1 - u) d₁ + u d₂`. The radius is `cornerRadius`, reduced to half the shorter leg.
* **Speed profile.** The path speed `v` rises at `wpAccel` to `wpSpeed`, and is limited so that
  braking at `wpAccel` reaches the corner speed at the start of the next blend (zero at the final
  waypoint), a trapezoidal profile on each leg. In a blend the target accelerates at the constant
  `v² ‖d₂ - d₁‖ / (2 r)`, so the corner speed is the largest speed at which this stays within
  `wpAccel`, capped at `wpSpeed`.
* **Outputs.** The position setpoint is the target point; the velocity feed-forward is `v` times
  the tangent `t`; the acceleration feed-forward is `v²` times the derivative of the tangent with
  respect to the distance (`(d₂ - d₁) / (2 r)` in a blend, zero on a straight part) plus the
  change of path speed over the step times `t`; the heading setpoint is the yaw stored with the
  waypoint being flown to, or, with `yawAlongPath`, the direction of the horizontal tangent (on
  take-off, of the first leg).

Simplified relative to `AC_WPNav`: the profile is trapezoidal in speed (no jerk limit or S-curve);
corners are rounded by a fixed-radius Bézier blend instead
of the S-curve overlap of consecutive legs; there are no spline segments, terrain following,
leash, or slowing when the vehicle lags behind the target; the first waypoint is approached as a
position step, as on take-off, rather than along a track from the current position; the stored
progress and speed are saturated to `[0, 1]` and `[0, wpSpeed]`; at most one waypoint is passed per
step; consecutive waypoints are assumed distinct, and on a leg with no horizontal extent the
path heading is `atan2 0 0`; an empty mission holds the current position at yaw `0`. With
`yawAlongPath` the heading is that of the path tangent, as with ArduCopter's `WP_YAW_BEHAVIOR`
facing along the track; without it the heading is a fixed yaw stored with each waypoint.
-/

namespace Flight

/-- A mission item: a position in the world frame and the heading to hold while flying to it. -/
structure Waypoint (α : Type) where
  /-- Target position, meters (NED). -/
  pos : Vec3 α
  /-- Heading to hold, radians (used unless the heading follows the path). -/
  yaw : α
  deriving Repr

/-- Navigator parameters; defaults are in the range ArduCopter ships with and are untuned. -/
structure NavParams (α : Type) [Arith α] where
  /-- Waypoints, flown in order. -/
  waypoints : List (Waypoint α) := []
  /-- Distance below which the first waypoint counts as reached, meters. -/
  acceptRadius : α := 2.0
  /-- Cruise speed along the path, meters per second. -/
  wpSpeed : α := 5.0
  /-- Acceleration and braking along the path, and bound on the blend acceleration, meters per second squared. -/
  wpAccel : α := 2.5
  /-- Blend radius at inner corners, meters (reduced to half the shorter leg). -/
  cornerRadius : α := 1.0
  /-- Face along the path instead of holding the yaw stored with the waypoint. -/
  yawAlongPath : Bool := false

/-- Navigator memory: the waypoint targeted, the progress along the current leg and the path speed. -/
structure NavState (α : Type) where
  /-- Index `0` while flying to the first waypoint; index `k + 1` while on the leg from waypoint `k` to `k + 1`. -/
  index : Nat
  /-- Fraction of the current leg flown, in `[0, 1]`. -/
  frac : α
  /-- Path speed of the target, meters per second. -/
  speed : α
  deriving Repr

/-- Navigator memory before the first step. -/
def NavState.init {α : Type} [Arith α] : NavState α := ⟨0, 0, 0⟩

/-- Navigator output: position setpoint, velocity and acceleration feed-forward, and heading setpoint. -/
structure NavOutput (α : Type) where
  /-- Position setpoint, meters (NED). -/
  posSp : Vec3 α
  /-- Velocity feed-forward, meters per second (NED). -/
  velSp : Vec3 α
  /-- Acceleration feed-forward, meters per second squared (NED, without gravity). -/
  accSp : Vec3 α
  /-- Heading setpoint, radians. -/
  yawSp : α
  deriving Repr

namespace Navigator

variable {α : Type} [Arith α]

/-- Length and unit direction of the straight segment from `a` to `b` (direction zero if they coincide). -/
def segment (a b : Vec3 α) : α × Vec3 α :=
  let L := Vec3.norm (b - a)
  (L, if 0 < L then Vec3.smul (1 / L) (b - a) else Vec3.zero)

/-- Blend radius at a corner between legs of lengths `lin` and `lout`. -/
def blendRadius (p : NavParams α) (lin lout : α) : α :=
  max 0 (min p.cornerRadius (min lin lout * 0.5))

/-- Corner speed of a blend of radius `r` between directions `d1` and `d2`: the largest speed, at most `wpSpeed`, with `v² ‖d2 - d1‖ / (2 r) ≤ wpAccel`. -/
def cornerSpeed (p : NavParams α) (r : α) (d1 d2 : Vec3 α) : α :=
  let k := Vec3.norm (d2 - d1)
  if sq p.wpSpeed * k ≤ 2.0 * r * p.wpAccel then p.wpSpeed
  else Arith.sqrt (2.0 * r * p.wpAccel / k)

/-- Point, tangent, and derivative of the tangent with respect to the distance, on the blend at corner `c` from direction `d1` to `d2` with radius `r`, at blend parameter `u`. -/
def blend (c d1 d2 : Vec3 α) (r u : α) : Vec3 α × Vec3 α × Vec3 α :=
  (c + Vec3.smul r (Vec3.smul (u * u) d2 - Vec3.smul ((1 - u) * (1 - u)) d1),
   Vec3.smul (1 - u) d1 + Vec3.smul u d2, Vec3.smul (1 / (2.0 * r)) (d2 - d1))

/-- Heading of the horizontal part of a direction, radians. -/
def heading (t : Vec3 α) : α := Arith.atan2 t.y t.x

/-- One leg of the path with its two corners. -/
structure Leg (α : Type) where
  /-- Waypoint at the start of the leg. -/
  start : Waypoint α
  /-- Waypoint at the end of the leg. -/
  stop : Waypoint α
  /-- Length, meters. -/
  len : α
  /-- Unit direction. -/
  dir : Vec3 α
  /-- Blend radius at the start corner (`0` on the first leg). -/
  rIn : α
  /-- Direction of the previous leg (this leg's direction on the first leg). -/
  dIn : Vec3 α
  /-- Corner speed at the start corner. -/
  vIn : α
  /-- Blend radius at the end corner (`0` on the last leg). -/
  rOut : α
  /-- Direction of the next leg (this leg's direction on the last leg). -/
  dOut : Vec3 α
  /-- Corner speed at the end corner (`0` on the last leg, where the target stops). -/
  vOut : α

/-- Leg `k`, from waypoint `k` to waypoint `k + 1`, if both exist. -/
def legAt (p : NavParams α) (k : Nat) : Option (Leg α) :=
  match p.waypoints[k]?, p.waypoints[k + 1]? with
  | some a, some b =>
    let (L, d) := segment a.pos b.pos
    let prev : Option (Waypoint α) := match k with
      | 0 => none
      | j + 1 => p.waypoints[j]?
    let (rIn, dIn, vIn) : α × Vec3 α × α := match prev with
      | some w =>
        let (L0, d0) := segment w.pos a.pos
        let r := blendRadius p L0 L
        (r, d0, cornerSpeed p r d0 d)
      | none => (0, d, p.wpSpeed)
    let (rOut, dOut, vOut) : α × Vec3 α × α := match p.waypoints[k + 2]? with
      | some w =>
        let (L2, d2) := segment b.pos w.pos
        let r := blendRadius p L L2
        (r, d2, cornerSpeed p r d d2)
      | none => (0, d, 0)
    some ⟨a, b, L, d, rIn, dIn, vIn, rOut, dOut, vOut⟩
  | _, _ => none

/-- Point, tangent and derivative of the tangent with respect to the distance, at fraction `f` of the leg. -/
def Leg.sample (g : Leg α) (f : α) : Vec3 α × Vec3 α × Vec3 α :=
  let σ := f * g.len
  if σ < g.rIn then blend g.start.pos g.dIn g.dir g.rIn ((g.rIn + σ) / (2.0 * g.rIn))
  else if g.len - g.rOut < σ then
    blend g.stop.pos g.dir g.dOut g.rOut ((σ - (g.len - g.rOut)) / (2.0 * g.rOut))
  else if 1 ≤ f then (g.stop.pos, g.dir, Vec3.zero)
  else (g.start.pos + Vec3.smul σ g.dir, g.dir, Vec3.zero)

/-- Speed limit at distance `σ` along the leg: the corner speed inside the start blend, otherwise `wpSpeed`, and at most the speed from which braking at `wpAccel` reaches the end corner speed where the end blend begins. -/
def Leg.speedLimit (p : NavParams α) (g : Leg α) (σ : α) : α :=
  let cap := if σ < g.rIn then g.vIn else p.wpSpeed
  let brake := max 0 (g.len - g.rOut - σ)
  min cap (Arith.sqrt (sq g.vOut + 2.0 * p.wpAccel * brake))

/-- The unsaturated next memory: start the first leg once the first waypoint is reached; on a leg, update the speed and the progress, and pass to the next leg (carrying the excess distance) or stop at the final waypoint. -/
def advance (p : NavParams α) (s : NavState α) (pos : Vec3 α) (dt : α) : NavState α :=
  match s.index with
  | 0 =>
    match p.waypoints[0]?, p.waypoints[1]? with
    | some w, some _ =>
      if Vec3.normSq (w.pos - pos) ≤ sq p.acceptRadius then ⟨1, 0, 0⟩ else ⟨0, 0, 0⟩
    | _, _ => ⟨0, 0, 0⟩
  | k + 1 =>
    match legAt p k with
    | none => ⟨k + 1, 0, 0⟩
    | some g =>
      let v := min (g.speedLimit p (s.frac * g.len)) (s.speed + p.wpAccel * dt)
      let f := if 0 < g.len then s.frac + v * dt / g.len else 1
      if f < 1 then ⟨k + 1, f, v⟩
      else
        match legAt p (k + 1) with
        | some g2 => ⟨k + 2, if 0 < g2.len then (f - 1) * g.len / g2.len else 0, v⟩
        | none => ⟨k + 1, 1, 0⟩

/-- The navigator output for a memory, given the rate of change `aT` of the path speed: the first waypoint while it is targeted, otherwise the target on the current leg. -/
def output (p : NavParams α) (s : NavState α) (pos : Vec3 α) (aT : α) : NavOutput α :=
  match s.index with
  | 0 =>
    match p.waypoints[0]? with
    | none => ⟨pos, Vec3.zero, Vec3.zero, 0⟩
    | some w =>
      let yaw := if p.yawAlongPath then
        (match legAt p 0 with
          | some g => heading g.dir
          | none => w.yaw)
        else w.yaw
      ⟨w.pos, Vec3.zero, Vec3.zero, yaw⟩
  | k + 1 =>
    match legAt p k with
    | none => ⟨pos, Vec3.zero, Vec3.zero, 0⟩
    | some g =>
      let (x, t, κ) := g.sample s.frac
      let v := s.speed
      ⟨x, Vec3.smul v t, Vec3.smul (v * v) κ + Vec3.smul aT t,
       if p.yawAlongPath then heading t else g.stop.yaw⟩

end Navigator

/-- One navigator step: advance the target along the path (progress saturated to `[0, 1]`, speed to `[0, wpSpeed]`), then output the target's position, velocity, acceleration and heading. -/
def Navigator.step {α : Type} [Arith α] (p : NavParams α) (s : NavState α) (pos : Vec3 α)
    (dt : α) : NavState α × NavOutput α :=
  let a := Navigator.advance p s pos dt
  let s' : NavState α := ⟨a.index, clip 0 1 a.frac, clip 0 p.wpSpeed a.speed⟩
  let aT := if 0 < dt then (s'.speed - s.speed) / dt else 0
  (s', Navigator.output p s' pos aT)

end Flight
