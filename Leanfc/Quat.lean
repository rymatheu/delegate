import Leanfc.Vec3

/-!
# Quat

Unit quaternions (w, x, y, z) rotating body (FRD) vectors into the world (NED); pyfc `quat.py`.
Differences from pyfc, as DESIGN.md requires (no transcendental functions): `integrate` is the
first-order update followed by normalization instead of the exponential map; headings are unit
vectors (cos ψ, sin ψ) instead of angles (`headingVec` replaces `yaw`); `fromThrustHeading` builds
the attitude from a thrust direction and a heading vector (pyfc `position.py` + `from_matrix`).
-/

structure Quat where
  w : R
  x : R
  y : R
  z : R
  deriving Inhabited, Repr

namespace Quat

def identity : Quat := ⟨1, 0, 0, 0⟩

def vec (q : Quat) : Vec3 := ⟨q.x, q.y, q.z⟩

/-- Hamilton product `q ⊗ r`. -/
def mul (q r : Quat) : Quat :=
  ⟨q.w * r.w - q.x * r.x - q.y * r.y - q.z * r.z,
   q.w * r.x + q.x * r.w + q.y * r.z - q.z * r.y,
   q.w * r.y - q.x * r.z + q.y * r.w + q.z * r.x,
   q.w * r.z + q.x * r.y - q.y * r.x + q.z * r.w⟩

def conj (q : Quat) : Quat := ⟨q.w, -q.x, -q.y, -q.z⟩

def neg (q : Quat) : Quat := ⟨-q.w, -q.x, -q.y, -q.z⟩

def normalize (q : Quat) : Quat :=
  let n := R.sqrt (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z)
  ⟨q.w / n, q.x / n, q.y / n, q.z / n⟩

/-- `R(q) v`, computed as the vector part of `q ⊗ (0, v) ⊗ q⁻¹`. -/
def rotate (q : Quat) (v : Vec3) : Vec3 :=
  (mul (mul q ⟨0, v.x, v.y, v.z⟩) (conj q)).vec

/-- First-order attitude update by body rate `ω` over dt: normalize (q + ½ q ⊗ (0, ω) dt), with
`halfDt` = dt/2 passed in. -/
def integrate (q : Quat) (ω : Vec3) (halfDt : R) : Quat :=
  let d := mul q ⟨0, ω.x, ω.y, ω.z⟩
  let h := halfDt
  normalize ⟨q.w + d.w * h, q.x + d.x * h, q.y + d.y * h, q.z + d.z * h⟩

/-- Heading as a unit vector (cos ψ, sin ψ): the body x axis projected onto the horizontal plane
and normalized; (1, 0) if the projection is shorter than 1e-6. -/
def headingVec (q : Quat) : R × R :=
  let c := 1 - 2 * (q.y * q.y + q.z * q.z)
  let s := 2 * (q.x * q.y + q.w * q.z)
  let n := R.sqrt (c * c + s * s)
  if n < (1e-6 : R) then (1, 0) else (c / n, s / n)

/-- Rotation matrix with columns `xb yb zb` to a unit quaternion, Shepperd's method (pyfc
`from_matrix`: pick the largest of the trace and the diagonal, then normalize). -/
def fromAxes (xb yb zb : Vec3) : Quat :=
  -- R[i][j] = column j, component i
  let r00 := xb.x; let r11 := yb.y; let r22 := zb.z
  let r01 := yb.x; let r02 := zb.x; let r10 := xb.y
  let r12 := zb.y; let r20 := xb.z; let r21 := yb.z
  let t := r00 + r11 + r22
  let q : Quat :=
    if t > 0 then
      let s := R.sqrt (1 + t) * 2
      ⟨s / 4, (r21 - r12) / s, (r02 - r20) / s, (r10 - r01) / s⟩
    else if r00 > r11 ∧ r00 > r22 then
      let s := R.sqrt (1 + r00 - r11 - r22) * 2
      ⟨(r21 - r12) / s, s / 4, (r01 + r10) / s, (r02 + r20) / s⟩
    else if r11 > r22 then
      let s := R.sqrt (1 + r11 - r00 - r22) * 2
      ⟨(r02 - r20) / s, (r01 + r10) / s, s / 4, (r12 + r21) / s⟩
    else
      let s := R.sqrt (1 + r22 - r00 - r11) * 2
      ⟨(r10 - r01) / s, (r02 + r20) / s, (r12 + r21) / s, s / 4⟩
  normalize q

/-- The attitude whose body z axis is the unit vector `zb` and whose body x axis points toward
the heading `(hc, hs)`: y_b = zb × (hc, hs, 0) normalized, x_b = y_b × zb. -/
def fromThrustHeading (zb : Vec3) (heading : R × R) : Quat :=
  let yc := Vec3.cross zb ⟨heading.1, heading.2, 0⟩
  let yb := Vec3.div yc (Vec3.norm yc)
  let xb := Vec3.cross yb zb
  fromAxes xb yb zb

/-- Attitude error in the body frame: 2 · vector part of `qHat⁻¹ ⊗ qDes`, taken the short way
round (the product negated if its w is negative). -/
def errorVec (qHat qDes : Quat) : Vec3 :=
  let e := mul (conj qHat) qDes
  let e := if e.w < 0 then neg e else e
  Vec3.scale 2 e.vec

end Quat
