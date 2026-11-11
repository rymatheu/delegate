import Leanfc.Vehicle

/-!
# Mixer

Collective thrust and body torque to four motor commands in [0, 1]; pyfc `mixer.py`. The
allocation A (rows thrust, roll, pitch, yaw; columns motors 1..4) and its inverse belong to the
vehicle (`Vehicle.lean`, layout and sources there). The inverse rows and T_max are decimal
literals computed once in binary64 by `sim/mixer_inverse.py`; pyfc inverts the binary32 matrix
instead. A tick does only the sixteen multiply-adds, a division by T_max and the clamp.
-/

structure Motors where
  m1 : R
  m2 : R
  m3 : R
  m4 : R
  deriving Inhabited, Repr

namespace Mixer

/-- A · (per-motor thrusts): the wrench (T, τ). Used by the checks. -/
def allocate (v : Vehicle) (t : Motors) : R × Vec3 :=
  let (a0, a1, a2, a3) := v.allocRows
  let f (r : Row4) := r.dot t.m1 t.m2 t.m3 t.m4
  (f a0, ⟨f a1, f a2, f a3⟩)

/-- A⁻¹ · [T, τx, τy, τz]: per-motor thrusts (N), unclamped. -/
def perMotor (v : Vehicle) (thrust : R) (torque : Vec3) : Motors :=
  let f (r : Row4) := r.dot thrust torque.x torque.y torque.z
  ⟨f v.inv0, f v.inv1, f v.inv2, f v.inv3⟩

/-- Motor commands: per-motor thrust / T_max, clamped to [0, 1]. -/
def step (v : Vehicle) (thrust : R) (torque : Vec3) : Motors :=
  let t := perMotor v thrust torque
  let c (x : R) := R.clamp 0 1 (x / v.tMax)
  ⟨c t.m1, c t.m2, c t.m3, c t.m4⟩

end Mixer
