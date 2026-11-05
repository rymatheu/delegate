import FloatModel.Compare

/-!
# Float literals

The value of a float literal of the translated code (`(0.5 : Float32)`, `Int32.toFloat32 2`, …) is
fixed by evaluating core's model of the literal (`OfScientific`, `Int32.toFloat32`, …) down to its
unpacked form. Those bodies are not exposed to modules, so this is a plain (non-module) file.

* `Float32.toReal_of_unpack`, `Float32.isFinite_of_unpack` (and the `Float` versions): read value
  and finiteness off an unpacked form;
* `f32_unpack`: the tactic that proves `x.toModel.unpack = u` for a closed literal `x` and its
  unpacked form `u`, by evaluation (`with_unfolding_all exact rfl`; checked by the kernel);
* `Float32.two32`: the hypothesis `Two32` of `FloatModel.Compare` (the literal `2` of the midpoint);
* the literals the actuator and integrator proofs use: `0.0`, `1.0`, `0.5` as `Float32`.

`Float.toFloat32` and `Float32.toFloat` are opaque in core v4.36 (`@[extern] opaque`): a literal
written `Float.toFloat32 (1.0 : Float)` has no value in the logic, and its value comes from the
hypothesis `LibmSpec.f64ToF32_exact` (`Contracts/Mission/Spec.lean`).
-/

open Float.Model UnpackedFloat

/-- Proves `x.toModel.unpack = u` for a closed float literal `x` by evaluation. -/
macro "f32_unpack" : tactic => `(tactic| with_unfolding_all exact rfl)

namespace Float32

theorem toReal_of_unpack {x : Float32} {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : x.toModel.unpack = .finite s m e hm) : x.toReal = ((s.apply (m : ℤ) : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal, h]; rfl

theorem toReal_of_unpack_zero {x : Float32} {s : Sign} (h : x.toModel.unpack = .zero s) :
    x.toReal = 0 := by
  rw [toReal, h]; rfl

theorem isFinite_of_unpack {x : Float32} {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : x.toModel.unpack = .finite s m e hm) : x.IsFinite := by
  rw [isFinite_iff, h]; rfl

theorem isFinite_of_unpack_zero {x : Float32} {s : Sign} (h : x.toModel.unpack = .zero s) :
    x.IsFinite := by
  rw [isFinite_iff, h]; rfl

theorem unpack_lit_zero : (0.0 : Float32).toModel.unpack = .zero .positive := by f32_unpack
theorem unpack_lit_one :
    (1.0 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-23) (by decide) := by f32_unpack
theorem unpack_lit_half :
    (0.5 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-24) (by decide) := by f32_unpack
theorem unpack_int32_two :
    (Int32.toFloat32 (2 : Int32)).toModel.unpack = .finite .positive (2 ^ 23) (-22) (by decide) := by
  f32_unpack
theorem unpack_int32_zero : (Int32.toFloat32 (0 : Int32)).toModel.unpack = .zero .positive := by
  f32_unpack

@[simp] theorem toReal_lit_zero : (0.0 : Float32).toReal = 0 := toReal_of_unpack_zero unpack_lit_zero
@[simp] theorem toReal_lit_one : (1.0 : Float32).toReal = 1 := by
  rw [toReal_of_unpack unpack_lit_one]; simp [Sign.apply]; norm_num
@[simp] theorem toReal_lit_half : (0.5 : Float32).toReal = 1 / 2 := by
  rw [toReal_of_unpack unpack_lit_half]; simp [Sign.apply]; norm_num
@[simp] theorem toReal_int32_two : (Int32.toFloat32 (2 : Int32)).toReal = 2 := by
  rw [toReal_of_unpack unpack_int32_two]; simp [Sign.apply]; norm_num
@[simp] theorem toReal_int32_zero : (Int32.toFloat32 (0 : Int32)).toReal = 0 :=
  toReal_of_unpack_zero unpack_int32_zero

theorem isFinite_lit_zero : (0.0 : Float32).IsFinite := isFinite_of_unpack_zero unpack_lit_zero
theorem isFinite_lit_one : (1.0 : Float32).IsFinite := isFinite_of_unpack unpack_lit_one
theorem isFinite_lit_half : (0.5 : Float32).IsFinite := isFinite_of_unpack unpack_lit_half
theorem isFinite_int32_two : (Int32.toFloat32 (2 : Int32)).IsFinite :=
  isFinite_of_unpack unpack_int32_two
theorem isFinite_int32_zero : (Int32.toFloat32 (0 : Int32)).IsFinite :=
  isFinite_of_unpack_zero unpack_int32_zero

/-- The literal `2` of the translated midpoint `(lo + hi) / 2`. -/
theorem two32 : Two32 := ⟨isFinite_int32_two, toReal_int32_two⟩

end Float32

namespace Float

theorem toReal_of_unpack {x : Float} {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : x.toModel.unpack = .finite s m e hm) : x.toReal = ((s.apply (m : ℤ) : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal, h]; rfl

theorem toReal_of_unpack_zero {x : Float} {s : Sign} (h : x.toModel.unpack = .zero s) :
    x.toReal = 0 := by
  rw [toReal, h]; rfl

theorem isFinite_of_unpack {x : Float} {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : x.toModel.unpack = .finite s m e hm) : x.IsFinite := by
  rw [isFinite_iff, h]; rfl

theorem isFinite_of_unpack_zero {x : Float} {s : Sign} (h : x.toModel.unpack = .zero s) :
    x.IsFinite := by
  rw [isFinite_iff, h]; rfl

theorem unpack_int32_two :
    (Int32.toFloat (2 : Int32)).toModel.unpack = .finite .positive (2 ^ 52) (-51) (by decide) := by
  f32_unpack

/-- The literal `2` of a translated `double` midpoint. -/
theorem two64 : Two64 :=
  ⟨isFinite_of_unpack unpack_int32_two, by rw [toReal_of_unpack unpack_int32_two]; simp [Sign.apply]; norm_num⟩

end Float
