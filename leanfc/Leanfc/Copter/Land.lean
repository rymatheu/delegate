import Leanfc.Copter.State

/-!
# Copter.Land (the landing descent and the touchdown detector)

**Descent.** A landing commands a vertical speed, not a position below the ground: the target
keeps the landing point's north and east and the vehicle's own estimated down coordinate, with the
descent speed as vertical velocity feedforward, so the vertical velocity setpoint of the position
loop is exactly that speed (`Position.step`: kpPos·0 + vFF). On the ground the vehicle can no
longer descend, the velocity error stays, and the position loop lowers the thrust. The speed is
ArduCopter's (`Mode::land_run_vertical_control`): LAND_SPD_MS below LAND_ALT_LOW_M above home and,
above it, kpPos·(height − LAND_ALT_LOW_M) between LAND_SPD_MS and the vertical speed limit
`nav.vMaxZ` (ArduCopter: a square-root controller between LAND_SPD_MS and WP_SPD_DN).

**Touchdown detector** (ArduCopter `update_land_detector`, `land_detector.cpp`): landed when, for
LAND_DETECTOR_TRIGGER_SEC (1 s) without interruption, the commanded collective thrust is low — below
0.9 of the hover thrust (ArduCopter: the motors at their lower limit) — and the vertical velocity
estimate is below 0.25 m/s (ArduCopter: 1 m/s; leanfc's landing speed is lower than ArduCopter's
threshold, so the bound is tighter). After LAND_DETECTOR_MAYBE_TRIGGER_SEC (0.2 s) the vehicle is
"maybe landed" and the horizontal position target and the integrators are relaxed so that it
cannot tip over (ArduCopter `NE_soften_for_landing`).

The commanded thrust fraction is the mean of the four motor commands (the mixer's inverse rows sum
to T/tMax, so the mean is T/(4·tMax) unless a motor saturates).
-/

namespace Copter.Land

open Mavlink

/-- Descent speed (m/s, positive down) at `height` m above home. -/
def speed (P : Params) (height : R) : R :=
  let k := P.copter
  let high := max P.nav.vMaxZ k.landSpeed
  if height ≤ k.landAltLow then k.landSpeed
  else min high (max k.landSpeed (P.position.kpPos * (height - k.landAltLow)))

/-- The commanded thrust as a fraction of the maximum (mean motor command). -/
def throttle (m : Motors) : R := (m.m1 + m.m2 + m.m3 + m.m4) / 4

/-- The hover thrust as a fraction of the maximum: m·g / (4·tMax). -/
def hoverThrottle (P : Params) : R := P.vehicle.mass * gravity / (4 * P.vehicle.tMax)

/-- One tick of the detector: the new count, "maybe landed" and "landed". -/
def detect (P : Params) (count : Nat) (m : Motors) (vz : R) : Nat × Bool × Bool :=
  let low := throttle m < (0.9 : R) * hoverThrottle P && R.abs vz < (0.25 : R)
  let c := if low then count + 1 else 0
  (c, c ≥ P.copter.landMaybeTicks, c ≥ P.copter.landTicks)

end Copter.Land
