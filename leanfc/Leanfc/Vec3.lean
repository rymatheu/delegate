import Leanfc.Scalar

/-!
# Vec3

Three-vectors over `R`: the `np.array(3, float32)` arithmetic of pyfc, written out per component
in numpy's evaluation order (`dot` is `x*x + y*y + z*z` left to right). `clampNorm` is pyfc
`position._clamp_norm`; `clampAxes` is `np.clip(v, -limit, limit)`.
-/

structure Vec3 where
  x : R
  y : R
  z : R
  deriving Inhabited, Repr

namespace Vec3

def zero : Vec3 := ⟨0, 0, 0⟩

instance : Add Vec3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub Vec3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg Vec3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩

/-- `k * v` componentwise. -/
def scale (k : R) (v : Vec3) : Vec3 := ⟨k * v.x, k * v.y, k * v.z⟩

/-- `v / k` componentwise (a true division, not a multiplication by `1/k`). -/
def div (v : Vec3) (k : R) : Vec3 := ⟨v.x / k, v.y / k, v.z / k⟩

/-- Componentwise product, for the diagonal inertia `J · u`. -/
def hadamard (a b : Vec3) : Vec3 := ⟨a.x * b.x, a.y * b.y, a.z * b.z⟩

def dot (a b : Vec3) : R := a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def norm (v : Vec3) : R := R.sqrt (dot v v)

/-- `v` scaled down to length `limit` if it is longer. -/
def clampNorm (v : Vec3) (limit : R) : Vec3 :=
  let n := norm v
  if n > limit then scale (limit / n) v else v

/-- The horizontal part `(x, y)` scaled down to length `limit` if longer; `z` untouched. -/
def clampXY (v : Vec3) (limit : R) : Vec3 :=
  let n := R.sqrt (v.x * v.x + v.y * v.y)
  if n > limit then ⟨v.x * (limit / n), v.y * (limit / n), v.z⟩ else v

/-- Each component clamped to `[-limit, limit]`. -/
def clampAxes (v : Vec3) (limit : R) : Vec3 :=
  ⟨R.clamp (-limit) limit v.x, R.clamp (-limit) limit v.y, R.clamp (-limit) limit v.z⟩

end Vec3
