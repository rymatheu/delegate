import Leanfc.Quat
import Leanfc.PI
import Leanfc.Vehicle

/-!
# Position

Position and velocity control; pyfc `position.py`. vSp = kpPos (pSp − pHat) + vFF, limited to
vMaxXY in the plane and ±vMaxZ vertically; aSp = PI(vSp − vHat) + aFF, limited to aMaxXY and
±aMaxZ; specific force f = aSp − (0, 0, g) with f.z ≤ −g/2 (always thrusting upward);
collective thrust mass·‖f‖ (the vehicle's mass) and desired attitude with body z along −f and
body x toward the heading setpoint (cos ψ, sin ψ) (pyfc takes the yaw angle and calls cos and sin).
The gains are in acceleration units, so they carry over between vehicles of different mass.
-/

structure PositionParams where
  kpPos : R
  vMaxXY : R
  vMaxZ : R
  vel : PIGains
  aMaxXY : R
  aMaxZ : R
  deriving Inhabited, Repr

namespace Position

/-- One tick. Output: collective thrust (N) and desired attitude. -/
def step (veh : Vehicle) (k : PositionParams) (st : PIState) (pSp vFF aFF : Vec3) (heading : R × R)
    (pHat vHat : Vec3) : PIState × (R × Quat) :=
  let v0 := Vec3.scale k.kpPos (pSp - pHat) + vFF
  let v1 := Vec3.clampXY v0 k.vMaxXY
  let vSp : Vec3 := ⟨v1.x, v1.y, R.clamp (-k.vMaxZ) k.vMaxZ v1.z⟩
  let (st', u) := PI.step k.vel st (vSp - vHat)
  let a1 := Vec3.clampXY (u + aFF) k.aMaxXY
  let f : Vec3 := ⟨a1.x, a1.y, min (R.clamp (-k.aMaxZ) k.aMaxZ a1.z - gravity) (-gravity / 2)⟩
  let n := Vec3.norm f
  let zb := Vec3.div (-f) n
  (st', (veh.mass * n, Quat.fromThrustHeading zb heading))

end Position
