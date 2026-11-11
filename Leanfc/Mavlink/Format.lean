import Leanfc.Mavlink.Vehicle
import FloatLib.Numerics.Exact.Trigonometric.Atan2.Enclosure.Runtime
import FloatLib.Numerics.Enclosure.Interval.InverseTrig

/-!
# Format (telemetry number formatting: geodesy, angles, integer fields)

Outside the control law: the controller modules never import this file and stay free of
transcendental functions.

**Integers.** `ratOf` is the exact rational value of a binary32 number (`toRat?`, 0 for NaN and
infinities); `roundR` rounds it to the nearest integer exactly; `ofInt` and `ofRat` round a rational
once to binary32. No conversion goes through `Float`.

**Geodesy.** Local NED offsets from the origin ↔ WGS84 latitude/longitude in degrees·1e7, by the
flat-earth scaling ArduPilot uses (`Location::get_distance_NE`, `offset`): one 1e-7 degree of
latitude is `latLonToM` = 0.011131884502145034 m, one of longitude `latLonToM · cos(origin
latitude)`. The latitude and longitude differences are taken as integers first (`lat − origin`),
converted once to binary32 and scaled in binary32; the cosine is the vehicle's (`Origin.cosLat`);
this module never computes one. The reverse divides in binary32 and rounds to the nearest integer.
Altitudes: AMSL mm = origin AMSL mm − 1000·down.

**Angles.** Roll, pitch and yaw (ZYX Euler angles) of a quaternion, bearings and headings, from
FloatLib's certified rational enclosures: `TrigonometricComparison.atan2Interval` (its theorem
`contains_atan2Interval`: the interval contains `Complex.arg (x + i y)`) and
`Interval.asinBounds?` (`containsReal_asinBounds?`). The arguments are formed exactly in ℚ from the
binary32 components, so they carry no rounding: roll = atan2(2(wx + yz), 1 − 2(x² + y²)), pitch =
asin(2(wy − xz)) (clamped to [−1, 1]), yaw = atan2(2(wz + xy), 1 − 2(y² + z²)). The degree of the
enclosure is raised (16, 24, 40) until its width is at most 2⁻³⁰, and the midpoint is rounded once
to binary32. Error bound: |result − exact| ≤ 2⁻³¹ + ½ ulp(result) ≤ 2⁻³¹ + 2⁻²³ rad (|angle| ≤ π),
whenever the widest enclosure meets the width test, which `widthOk` reports (a test checks it;
otherwise the result is still the midpoint of a valid enclosure). For a quaternion that is not
exactly unit, roll and yaw are those of the normalized quaternion (atan2 is scale-invariant) and
pitch is asin of the clamped, unnormalized argument. Cost: about 0.1 ms per angle, so only the
telemetry formatter at its stream rate calls these.
-/

namespace Mavlink.Format

open FloatLib.Floats FloatLib.Numerics

/-- Exact rational value (0 for NaN and infinities). -/
def ratOf (x : R) : ℚ := (ExecFloat.Binary.toRat? x).getD 0

/-- Round a rational once to binary32 (nearest even). -/
def ofRat (q : ℚ) : R := ExecFloat.Binary.ofRat q

def ofInt (n : Int) : R := ofRat n

/-- Nearest integer (Mathlib's `round`: halves toward +∞). -/
def roundQ (q : ℚ) : Int := round q

def roundR (x : R) : Int := roundQ (ratOf x)

def clampInt (lo hi : Int) (n : Int) : Int := max lo (min hi n)

/-! ## Geodesy -/

/-- Meters per 1e-7 degree of latitude (ArduPilot `LATLON_TO_M`). -/
def latLonToM : R := 0.011131884502145034

/-- NED offset (north, east) of a latitude/longitude from the origin. -/
def toNE (o : Origin) (latE7 lonE7 : Int) : R × R :=
  (ofInt (latE7 - o.latE7) * latLonToM, ofInt (lonE7 - o.lonE7) * (latLonToM * o.cosLat))

/-- Latitude/longitude of an NED offset. -/
def toLatLon (o : Origin) (p : Vec3) : Int × Int :=
  (o.latE7 + roundR (p.x / latLonToM), o.lonE7 + roundR (p.y / (latLonToM * o.cosLat)))

/-- AMSL altitude in mm of a down coordinate. -/
def amslMm (o : Origin) (down : R) : Int := o.altMm - roundR (down * 1000)

/-- Down coordinate of an AMSL altitude in m. -/
def downOfAmsl (o : Origin) (altM : R) : R := -(altM - ofRat (o.altMm / 1000 : ℚ))

/-! ## Angles -/

def maxWidth : ℚ := 1 / 2 ^ 30

/-- `atan2 y x` (the argument of x + i y) as an enclosure narrower than 2⁻³⁰ if the degrees
allow, and whether it is. -/
def atan2Q (y x : ℚ) : RationalInterval × Bool :=
  let go (d : Nat) := TrigonometricComparison.atan2Interval x y d
  let a := go 16
  if a.hi - a.lo ≤ maxWidth then (a, true) else
  let b := go 24
  if b.hi - b.lo ≤ maxWidth then (b, true) else
  let c := go 40
  (c, c.hi - c.lo ≤ maxWidth)

/-- `asin s` for s ∈ [−1, 1] as an enclosure (π/2 enclosures at ±1). -/
def asinQ (s : ℚ) : RationalInterval × Bool :=
  let s := max (-1) (min 1 s)
  let go (t : Nat) : Option RationalInterval :=
    (Interval.asinBounds? ⟨s, s⟩ t (2 * t + 8)).map fun I => ⟨I.lo, I.hi⟩
  let ok (I : RationalInterval) := I.hi - I.lo ≤ maxWidth
  match go 16 with
  | some a => if ok a then (a, true) else
    match go 40 with
    | some b => (b, ok b)
    | none => (a, false)
  | none =>
    -- |s| so close to 1 that the square-root bound cannot separate 1 − s² from 0: atan2 form
    atan2Q s 0

def mid (I : RationalInterval) : ℚ := (I.lo + I.hi) / 2

/-- Angle of the argument of `(x, y)` in radians, rounded once to binary32. -/
def atan2R (y x : ℚ) : R := ofRat (mid (atan2Q y x).1)

/-- Roll, pitch, yaw (rad) of a quaternion, and whether all three enclosures met the width. -/
def eulerQ (q : Quat) : (ℚ × ℚ × ℚ) × Bool :=
  let w := ratOf q.w; let x := ratOf q.x; let y := ratOf q.y; let z := ratOf q.z
  let (r, okr) := atan2Q (2 * (w * x + y * z)) (1 - 2 * (x * x + y * y))
  let (p, okp) := asinQ (2 * (w * y - x * z))
  let (yw, oky) := atan2Q (2 * (w * z + x * y)) (1 - 2 * (y * y + z * z))
  ((mid r, mid p, mid yw), okr && okp && oky)

/-- Yaw alone (rad, exact rational midpoint), for headings. -/
def yawQ (q : Quat) : ℚ :=
  let w := ratOf q.w; let x := ratOf q.x; let y := ratOf q.y; let z := ratOf q.z
  mid (atan2Q (2 * (w * z + x * y)) (1 - 2 * (y * y + z * z))).1

def euler (q : Quat) : R × R × R :=
  let ((r, p, y), _) := eulerQ q
  (ofRat r, ofRat p, ofRat y)

def widthOk (q : Quat) : Bool := (eulerQ q).2

/-- π as a rational (the midpoint of Machin's enclosure, within 2⁻⁶⁰). -/
def piQ : ℚ := 4 * mid (Enclosure.piQuarter 24)

/-- An angle in radians as whole degrees in [0, 360) (VFR_HUD heading). -/
def deg360 (a : ℚ) : Nat :=
  ((roundQ (a * 180 / piQ)) % 360).toNat

/-- An angle in radians as centidegrees in [0, 36000) (GLOBAL_POSITION_INT hdg). -/
def cdeg36000 (a : ℚ) : Nat :=
  ((roundQ (a * 18000 / piQ)) % 36000).toNat

/-- An angle in radians as degrees in (−180, 180], rounded (NAV_CONTROLLER_OUTPUT nav_bearing). -/
def deg180 (a : ℚ) : Int := roundQ (a * 180 / piQ)

/-- Radians to degrees, rounded once to binary32. -/
def degR (a : ℚ) : R := ofRat (a * 180 / piQ)

end Mavlink.Format
