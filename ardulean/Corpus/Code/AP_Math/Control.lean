import ArduLean.Vehicle
import Corpus.Machine.Float
import Corpus.Code.AP_Math.AP_Math

/-!
# AP_Math: `control.cpp`

Low-level lemmas about the translated shaping functions of `libraries/AP_Math/control.cpp`. The tests `is_positive`,
`is_zero`, `is_negative` are used through their own lemmas (`Corpus.AP_Math`); each branch lemma takes the values of
the tests that select it.
-/

open FloatLib.Floats (Binary32 Binary64 ExecFloat)
open FloatLib.Floats.Formats.BinaryInterchange (Model)

set_option linter.unusedSimpArgs false

namespace Corpus.Control

/-! ## `sqrt_controller_accel`

C++ `sqrt_controller_accel : float (float, float, float, float, float)`, `control.cpp:673-706`: the acceleration
`d(rate)/dt` of `sqrt_controller` along a trajectory: `0` unless `rate_cmd * rate_state` is positive; `-p * rate_state`
without a second-order limit or inside the linear region `|error| ≤ second_ord_lim / p²`; else
`-(second_ord_lim / |rate_cmd|) * rate_state` (`0` when `rate_cmd` is zero). -/

theorem sqrt_controller_accel_eq (e rc rs p s : Binary32) :
    Vehicle_lib.sqrt_controller_accel e rc rs p s = pure (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) := rfl


section
variable {e rc rs p s : Binary32}


/-- Case: the product of the rates is not positive: `0`. -/
theorem sqrt_controller_accel_of_not_pos (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = false) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = Binary32.ofBits 0x00000000 := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.zero64_const]

/-- Case: no second-order limit: the linear law `-p * rate_state`. -/
theorem sqrt_controller_accel_of_not_pos_lim (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = false) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -p * rs := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]

/-- Case: `p` not positive and `rate_cmd` zero: `0`. -/
theorem sqrt_controller_accel_of_not_pos_p_of_zero
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true)
    (h3 : Id.run (Vehicle_lib.is_positive'float.pure' p) = false) (h4 : Id.run (Vehicle_lib.is_zero.pure' rc) = true) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = Binary32.ofBits 0x00000000 := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, h3, h4, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.zero64_const]

/-- Case: `p` not positive, `rate_cmd` not zero: `-(second_ord_lim / |rate_cmd|) * rate_state`. -/
theorem sqrt_controller_accel_of_not_pos_p
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true)
    (h3 : Id.run (Vehicle_lib.is_positive'float.pure' p) = false) (h4 : Id.run (Vehicle_lib.is_zero.pure' rc) = false) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -(s / Binary32.abs rc) * rs := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, h3, h4, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]

/-- Case: inside the linear region `|error| ≤ second_ord_lim / p²`: `-p * rate_state`. -/
theorem sqrt_controller_accel_of_linear
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true)
    (h3 : Id.run (Vehicle_lib.is_positive'float.pure' p) = true)
    (h5 : Binary32.abs e ≤ s / Id.run (Vehicle_lib.sq.pure' p)) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -p * rs := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]
  rw [Corpus.ite_pos h5]; rfl

/-- Case: outside the linear region, `rate_cmd` zero: `0`. -/
theorem sqrt_controller_accel_of_sqrt_of_zero
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true)
    (h3 : Id.run (Vehicle_lib.is_positive'float.pure' p) = true)
    (h5 : ¬ Binary32.abs e ≤ s / Id.run (Vehicle_lib.sq.pure' p)) (h6 : Id.run (Vehicle_lib.is_zero.pure' rc) = true) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = Binary32.ofBits 0x00000000 := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]
  rw [Corpus.ite_neg h5]
  simp only [Corpus.id_bind, h6, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]

/-- Case: outside the linear region, `rate_cmd` not zero: `-(second_ord_lim / |rate_cmd|) * rate_state`. -/
theorem sqrt_controller_accel_of_sqrt
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true)
    (h3 : Id.run (Vehicle_lib.is_positive'float.pure' p) = true)
    (h5 : ¬ Binary32.abs e ≤ s / Id.run (Vehicle_lib.sq.pure' p)) (h6 : Id.run (Vehicle_lib.is_zero.pure' rc) = false) :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -(s / Binary32.abs rc) * rs := by
  unfold Vehicle_lib.sqrt_controller_accel.pure'
  simp only [Corpus.id_bind, h1, h2, h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]
  rw [Corpus.ite_neg h5]
  simp only [Corpus.id_bind, h6, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]

/-- Safety: the branches that divide by `|rate_cmd|` take it only when `is_zero rate_cmd` is false, so the divisor is
at least `ε` in magnitude or a NaN; the branches that divide by `p²` take it only when `p ≥ ε`. -/
theorem sqrt_controller_accel_divisor (h : Id.run (Vehicle_lib.is_zero.pure' rc) = false) :
    Binary32.ofBits 0x34000000 ≤ Binary32.abs rc ∨ Binary32.isNaN rc = true := by
  cases hn : Binary32.isNaN rc
  · left
    have han : Binary32.isNaN (Binary32.abs rc) = false := by rw [Corpus.F32.isNaN_abs]; exact hn
    rw [Corpus.AP_Math.is_zero_pure_eq, decide_eq_false_iff_not,
      Corpus.F32.not_lt_iff_le han Corpus.F32.isNaN_eps] at h
    exact h
  · exact Or.inr rfl

end

/-! ## `inv_sqrt_controller`, `stopping_distance`

C++ `inv_sqrt_controller : float (float, float, float)`, `control.cpp:630-659`: the error that `sqrt_controller` maps
to `output`. C++ `stopping_distance : float (float, float, float)`, `control.cpp:712-716`: `inv_sqrt_controller`. -/

theorem inv_sqrt_controller_eq (o p d : Binary32) :
    Vehicle_lib.inv_sqrt_controller o p d = pure (Vehicle_lib.inv_sqrt_controller.pure' o p d) := rfl

theorem stopping_distance_eq (v p a : Binary32) :
    Vehicle_lib.stopping_distance v p a = pure (Vehicle_lib.stopping_distance.pure' v p a) := rfl

/-- Case: `stopping_distance` is `inv_sqrt_controller`. -/
theorem stopping_distance_pure_eq (v p a : Binary32) :
    Id.run (Vehicle_lib.stopping_distance.pure' v p a) = Id.run (Vehicle_lib.inv_sqrt_controller.pure' v p a) := rfl


section
variable {o p d : Binary32}


/-- Case: `D_max` positive and `p` zero: the pure second-order law `output² / (2 D_max)`; the divisor is
`≥ 2ε`. -/
theorem inv_sqrt_controller_of_pos_zero (h1 : Id.run (Vehicle_lib.is_positive'float.pure' d) = true)
    (h2 : Id.run (Vehicle_lib.is_zero.pure' p) = true) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) = (o * o) / (Binary32.ofBits 0x40000000 * d) := by
  unfold Vehicle_lib.inv_sqrt_controller.pure'
  simp only [Corpus.id_bind, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.two64_const]

/-- Case: `D_max` negative or zero and `p` not zero: the linear law `output / p`. -/
theorem inv_sqrt_controller_of_linear (h1 : Id.run (Vehicle_lib.is_negative'float.pure' d) = true ∨
      Id.run (Vehicle_lib.is_zero.pure' d) = true) (h2 : Id.run (Vehicle_lib.is_zero.pure' p) = false) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) = o / p := by
  have hpos : Id.run (Vehicle_lib.is_positive'float.pure' d) = false := by
    rcases h1 with h | h
    · cases hp : Id.run (Vehicle_lib.is_positive'float.pure' d)
      · rfl
      · rw [Corpus.AP_Math.is_positive_not_negative d hp] at h; exact absurd h (by simp)
    · exact Corpus.AP_Math.is_zero_not_positive d h
  unfold Vehicle_lib.inv_sqrt_controller.pure'
  rcases h1 with h | h
  · simp only [Corpus.id_bind, hpos, h, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]
  · cases hn : Id.run (Vehicle_lib.is_negative'float.pure' d) <;>
    simp only [Corpus.id_bind, hpos, hn, h, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure]

/-- Case: `D_max` negative or zero and `p` zero: `0`. -/
theorem inv_sqrt_controller_of_zero (h1 : Id.run (Vehicle_lib.is_negative'float.pure' d) = true ∨
      Id.run (Vehicle_lib.is_zero.pure' d) = true) (h2 : Id.run (Vehicle_lib.is_zero.pure' p) = true) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) = Binary32.ofBits 0x00000000 := by
  have hpos : Id.run (Vehicle_lib.is_positive'float.pure' d) = false := by
    rcases h1 with h | h
    · cases hp : Id.run (Vehicle_lib.is_positive'float.pure' d)
      · rfl
      · rw [Corpus.AP_Math.is_positive_not_negative d hp] at h; exact absurd h (by simp)
    · exact Corpus.AP_Math.is_zero_not_positive d h
  unfold Vehicle_lib.inv_sqrt_controller.pure'
  rcases h1 with h | h
  · simp only [Corpus.id_bind, hpos, h, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.zero64_const]
  · cases hn : Id.run (Vehicle_lib.is_negative'float.pure' d) <;>
    simp only [Corpus.id_bind, hpos, hn, h, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.zero64_const]

/-- Case: the remaining inputs (`D_max` neither negative nor zero, and not both `D_max` positive and `p` zero),
inside the linear region `|output| < D_max / p`: `output / p`. -/
theorem inv_sqrt_controller_of_inside (hn : Id.run (Vehicle_lib.is_negative'float.pure' d) = false)
    (hz : Id.run (Vehicle_lib.is_zero.pure' d) = false)
    (hg : (Id.run (Vehicle_lib.is_positive'float.pure' d) && Id.run (Vehicle_lib.is_zero.pure' p)) = false)
    (h : Binary32.abs o < d / p) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) = o / p := by
  unfold Vehicle_lib.inv_sqrt_controller.pure'
  cases hp : Id.run (Vehicle_lib.is_positive'float.pure' d) <;> cases hzp : Id.run (Vehicle_lib.is_zero.pure' p) <;>
    simp only [hp, hzp, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.true_eq_false] at hg <;>
    simp only [Corpus.id_bind, hp, hzp, hn, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure] <;>
    rw [Corpus.ite_pos h] <;> rfl

/-- Case: the remaining inputs, outside the linear region: `±(D_max / p² / 2 + output² / (2 D_max))`, with the sign of
`is_positive output`. -/
theorem inv_sqrt_controller_of_outside (hn : Id.run (Vehicle_lib.is_negative'float.pure' d) = false)
    (hz : Id.run (Vehicle_lib.is_zero.pure' d) = false)
    (hg : (Id.run (Vehicle_lib.is_positive'float.pure' d) && Id.run (Vehicle_lib.is_zero.pure' p)) = false)
    (h : ¬ Binary32.abs o < d / p) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) =
      let stop := d / Id.run (Vehicle_lib.sq.pure' p) * Binary32.ofBits 0x3f000000 +
        Id.run (Vehicle_lib.sq.pure' o) / (Binary32.ofBits 0x40000000 * d)
      if Id.run (Vehicle_lib.is_positive'float.pure' o) then stop else -stop := by
  unfold Vehicle_lib.inv_sqrt_controller.pure'
  cases hp : Id.run (Vehicle_lib.is_positive'float.pure' d) <;> cases hzp : Id.run (Vehicle_lib.is_zero.pure' p) <;>
    simp only [hp, hzp, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.true_eq_false] at hg <;>
    simp only [Corpus.id_bind, hp, hzp, hn, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure, Corpus.F32.two64_const] <;>
    rw [Corpus.ite_neg h] <;>
    cases ho : Id.run (Vehicle_lib.is_positive'float.pure' o) <;>
    simp only [Corpus.id_bind, ho, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, decide_eq_true_eq, Corpus.id_run_pure] <;> rfl

end

/-! ## `input_expo`

C++ `input_expo : float (float, float)`, `control.cpp:810-820`: the input constrained to `[-1, 1]`, then, for
`expo < 0.95`, the expo curve `(1 - expo) * input / (1 - expo * |input|)`. -/

theorem input_expo_eq (i e : Binary32) : Vehicle_lib.input_expo i e = pure (Vehicle_lib.input_expo.pure' i e) := rfl




/-- Case: the body, with the constants as their words (`0.95` is `0x3f733333`). -/
theorem input_expo_pure_eq (i e : Binary32) :
    Id.run (Vehicle_lib.input_expo.pure' i e) =
      let c := Id.run (Vehicle_lib.constrain_value_line'float.pure' i (Binary32.ofBits 0xbf800000)
        (Binary32.ofBits 0x3f800000) (Int32.toUInt32 813))
      if e < Binary32.ofBits 0x3f733333 then
        ((Binary32.ofBits 0x3f800000 - e) * c) / (Binary32.ofBits 0x3f800000 - e * Binary32.abs c)
      else c := by
  unfold Vehicle_lib.input_expo.pure'
  simp only [Corpus.F32.neg_one64_const, Corpus.F32.expo_max_const, Corpus.F32.int32_one, Corpus.F32.one64_const]
  rfl

/-- Range: when the expo curve is not applied (`expo ≥ 0.95` or NaN), the result is in `[-1, 1]`, for every
input (a NaN input gives `0`). -/
theorem input_expo_mem_of_not_lt {e : Binary32} (i : Binary32) (h : ¬ e < Binary32.ofBits 0x3f733333) :
    Binary32.ofBits 0xbf800000 ≤ Id.run (Vehicle_lib.input_expo.pure' i e) ∧
      Id.run (Vehicle_lib.input_expo.pure' i e) ≤ Binary32.ofBits 0x3f800000 := by
  rw [input_expo_pure_eq]
  simp only
  rw [Corpus.ite_neg h]
  cases hi : Binary32.isNaN i
  · exact Corpus.AP_Math.constrain_float_mem _ (by decide +kernel) hi
  · rw [Corpus.AP_Math.constrain_float_of_isNaN _ _ _ hi]
    exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## `angle_rad_to_accel_mss`, `accel_mss_to_angle_rad`

C++ `angle_rad_to_accel_mss : float (float)`, `control.cpp:823-827` (`GRAVITY_MSS * tanf(angle_rad)`) and
`accel_mss_to_angle_rad : float (float)`, `control.cpp:838-842` (`atanf(accel_mss / GRAVITY_MSS)`); `GRAVITY_MSS` is the
word `0x411ce80a` (`9.80665`). -/

theorem angle_rad_to_accel_mss_eq (a : Binary32) :
    Vehicle_lib.angle_rad_to_accel_mss a = pure (Vehicle_lib.angle_rad_to_accel_mss.pure' a) := rfl

theorem accel_mss_to_angle_rad_eq (a : Binary32) :
    Vehicle_lib.accel_mss_to_angle_rad a = pure (Vehicle_lib.accel_mss_to_angle_rad.pure' a) := rfl

theorem angle_rad_to_accel_mss_pure_eq (a : Binary32) :
    Id.run (Vehicle_lib.angle_rad_to_accel_mss.pure' a) = Binary32.ofBits 0x411ce80a * Musl.tanf.tanf a := rfl

theorem accel_mss_to_angle_rad_pure_eq (a : Binary32) :
    Id.run (Vehicle_lib.accel_mss_to_angle_rad.pure' a) = Musl.atanf.atanf (a / Binary32.ofBits 0x411ce80a) := rfl

/-- The premise on musl's `atanf` (plan rule 5): a number in, a number out. -/
def AtanfNotNaN : Prop := ∀ y : Binary32, Binary32.isNaN y = false → Binary32.isNaN (Musl.atanf.atanf y) = false

/-- Safety: under `AtanfNotNaN`, a number in gives a number out (division by `GRAVITY_MSS` is never by zero). -/
theorem accel_mss_to_angle_rad_not_isNaN (hatan : AtanfNotNaN) {a : Binary32} (ha : Binary32.isNaN a = false) :
    Binary32.isNaN (Id.run (Vehicle_lib.accel_mss_to_angle_rad.pure' a)) = false := by
  rw [accel_mss_to_angle_rad_pure_eq]
  apply hatan
  rcases Corpus.F32.finite_or_inf ha with hf | hp | hn
  · show Model.isNaN (ExecFloat.Binary.toModel (a / Binary32.ofBits 0x411ce80a)) = false
    simp only [ExecFloat.Binary.toModel_hDiv]
    exact Model.isNaN_div_eq_false_of_isFinite _ _ .nearest (by decide) hf (by decide +kernel) (by decide +kernel)
  · subst hp; decide +kernel
  · subst hn; decide +kernel

end Corpus.Control

/-! ## `sqrt_controller_accel`: safety and sign (second increment) -/

namespace Corpus.Control

open Corpus.F32 (ext)

section
variable {e rc rs p s : Binary32}

/-- In every branch that is not `0`, `rate_state` is not a zero (`rate_cmd * rate_state ≥ ε`). -/
private theorem rs_ne_zero (hrc : Binary32.isFinite rc = true) (hrs : Binary32.isFinite rs = true)
    (h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true) :
    Model.isZero (Corpus.F32.model rs) = false := by
  cases hz : Model.isZero (Corpus.F32.model rs)
  · rfl
  · exfalso
    have h0 : Corpus.F32.real rs = 0 := Model.toReal_eq_zero_of_isZero _ hz
    rw [Corpus.AP_Math.is_positive_iff_ext, Corpus.F32.ext_mul_of_isFinite hrc hrs, h0, mul_zero,
      Corpus.F32.rnd_zero] at h1
    exact absurd h1.2 (not_le.2 (by exact_mod_cast (show (0 : ℝ) < ((1 / 8388608 : ℚ) : ℝ) by norm_num)))

/-- `|rate_cmd|` is finite and `> 0` when `is_zero rate_cmd` is false. -/
private theorem abs_pos (hrc : Binary32.isFinite rc = true) (h : Id.run (Vehicle_lib.is_zero.pure' rc) = false) :
    Binary32.isFinite (Binary32.abs rc) = true ∧ Binary32.ofBits 0x00000000 < Binary32.abs rc := by
  have hn : Binary32.isNaN rc = false := Model.isNaN_eq_false_of_isFinite_eq_true (Corpus.F32.model rc) hrc
  refine ⟨?_, ?_⟩
  · show Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.abs rc)) = true
    rw [ExecFloat.Binary.toModel_abs, Model.isFinite_abs]; exact hrc
  · rcases sqrt_controller_accel_divisor h with h' | h'
    · exact Corpus.F32.lt_of_lt_of_le (by decide +kernel) h'
    · rw [hn] at h'; cases h'

/-- The three values `sqrt_controller_accel` returns: `0`, `-p * rate_state`, `-(second_ord_lim / |rate_cmd|) *
rate_state`; the last only with `second_ord_lim ≥ ε` and `is_zero rate_cmd` false. -/
private theorem shapes :
    Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = Binary32.ofBits 0x00000000 ∨
      (Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true ∧
        Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -p * rs) ∨
      (Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs)) = true ∧
        Id.run (Vehicle_lib.is_positive'float.pure' s) = true ∧ Id.run (Vehicle_lib.is_zero.pure' rc) = false ∧
        Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) = -(s / Binary32.abs rc) * rs) := by
  cases h1 : Id.run (Vehicle_lib.is_positive'float.pure' (rc * rs))
  · exact Or.inl (sqrt_controller_accel_of_not_pos h1)
  cases h2 : Id.run (Vehicle_lib.is_positive'float.pure' s)
  · exact Or.inr (Or.inl ⟨rfl, sqrt_controller_accel_of_not_pos_lim h1 h2⟩)
  cases h3 : Id.run (Vehicle_lib.is_positive'float.pure' p)
  · cases h4 : Id.run (Vehicle_lib.is_zero.pure' rc)
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, sqrt_controller_accel_of_not_pos_p h1 h2 h3 h4⟩)
    · exact Or.inl (sqrt_controller_accel_of_not_pos_p_of_zero h1 h2 h3 h4)
  by_cases h5 : Binary32.abs e ≤ s / Id.run (Vehicle_lib.sq.pure' p)
  · exact Or.inr (Or.inl ⟨rfl, sqrt_controller_accel_of_linear h1 h2 h3 h5⟩)
  cases h6 : Id.run (Vehicle_lib.is_zero.pure' rc)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, sqrt_controller_accel_of_sqrt h1 h2 h3 h5 h6⟩)
  · exact Or.inl (sqrt_controller_accel_of_sqrt_of_zero h1 h2 h3 h5 h6)

/-- `second_ord_lim / |rate_cmd|`, negated: a number `≤ 0` (`-∞` when the quotient overflows). -/
private theorem neg_q_nonpos (hs : Binary32.isFinite s = true) (hrc : Binary32.isFinite rc = true)
    (h2 : Id.run (Vehicle_lib.is_positive'float.pure' s) = true) (h4 : Id.run (Vehicle_lib.is_zero.pure' rc) = false) :
    -(s / Binary32.abs rc) ≤ Binary32.ofBits 0x00000000 := by
  obtain ⟨haf, hap⟩ := abs_pos hrc h4
  have hsp : Binary32.ofBits 0x00000000 < s :=
    Corpus.F32.lt_of_lt_of_le (by decide +kernel) ((Corpus.AP_Math.is_positive_iff s).1 h2)
  obtain ⟨hqn, hq0⟩ := Corpus.F32.div_nonneg_of_pos hs hsp haf hap
  rw [Corpus.F32.le_zero_iff (by rw [Corpus.F32.isNaN_neg]; exact hqn), Corpus.F32.ext_neg hqn]
  rw [Corpus.F32.zero_le_iff hqn] at hq0
  exact EReal.neg_le_zero.2 hq0

/-- Safety: for finite inputs the acceleration is not a NaN (it may be `±∞`, when `second_ord_lim / |rate_cmd|`
overflows). -/
theorem sqrt_controller_accel_not_isNaN (hrc : Binary32.isFinite rc = true) (hrs : Binary32.isFinite rs = true)
    (hp : Binary32.isFinite p = true) (hs : Binary32.isFinite s = true) :
    Binary32.isNaN (Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s)) = false := by
  rcases shapes (e := e) (rc := rc) (rs := rs) (p := p) (s := s) with h | ⟨_, h⟩ | ⟨h1, _, _, h⟩ <;> rw [h]
  · decide +kernel
  · exact Corpus.F32.isNaN_mul_of_isFinite (by rw [Corpus.F32.isFinite_neg]; exact hp) hrs
  · rename_i h2 h4
    exact Corpus.F32.isNaN_mul_of_ne_zero (Corpus.F32.isNaN_false_of_le (neg_q_nonpos hs hrc h2 h4)).1 hrs
      (rs_ne_zero hrc hrs h1)

/-- Range (sign): for finite inputs and `p ≥ 0`, the acceleration opposes `rate_state`: `≤ 0` when
`rate_state ≥ 0`, `≥ 0` when `rate_state ≤ 0` (FINDINGS F8: false for `p < 0`). -/
theorem sqrt_controller_accel_opposes_nonneg (hrc : Binary32.isFinite rc = true) (hrs : Binary32.isFinite rs = true)
    (hp : Binary32.isFinite p = true) (hs : Binary32.isFinite s = true) (hp0 : Binary32.ofBits 0x00000000 ≤ p) :
    (Binary32.ofBits 0x00000000 ≤ rs → Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s) ≤
        Binary32.ofBits 0x00000000) ∧
      (rs ≤ Binary32.ofBits 0x00000000 → Binary32.ofBits 0x00000000 ≤
        Id.run (Vehicle_lib.sqrt_controller_accel.pure' e rc rs p s)) := by
  have hnp : -p ≤ Binary32.ofBits 0x00000000 := by
    have hpn := (Corpus.F32.isNaN_false_of_le hp0).2
    rw [Corpus.F32.le_zero_iff (by rw [Corpus.F32.isNaN_neg]; exact hpn), Corpus.F32.ext_neg hpn]
    rw [Corpus.F32.zero_le_iff hpn] at hp0
    exact EReal.neg_le_zero.2 hp0
  have key : ∀ x : Binary32, x ≤ Binary32.ofBits 0x00000000 → Model.isZero (Corpus.F32.model rs) = false →
      (Binary32.ofBits 0x00000000 ≤ rs → x * rs ≤ Binary32.ofBits 0x00000000) ∧
      (rs ≤ Binary32.ofBits 0x00000000 → Binary32.ofBits 0x00000000 ≤ x * rs) := by
    intro x hx hz
    rcases Corpus.F32.lt_or_gt_of_ne_zero hrs hz with hneg | hpos
    · refine ⟨fun h => absurd (Corpus.F32.lt_of_le_of_lt h hneg) (by decide +kernel), fun _ => ?_⟩
      exact Corpus.F32.nonneg_of_mul_neg hx hrs hneg
    · refine ⟨fun _ => Corpus.F32.mul_nonpos_of_pos hx hrs hpos, fun h => ?_⟩
      exact absurd (Corpus.F32.lt_of_lt_of_le hpos h) (by decide +kernel)
  rcases shapes (e := e) (rc := rc) (rs := rs) (p := p) (s := s) with h | ⟨h1, h⟩ | ⟨h1, h2, h4, h⟩ <;> rw [h]
  · exact ⟨fun _ => by decide +kernel, fun _ => by decide +kernel⟩
  · exact key _ hnp (rs_ne_zero hrc hrs h1)
  · exact key _ (neg_q_nonpos hs hrc h2 h4) (rs_ne_zero hrc hrs h1)

end

end Corpus.Control

/-! ## `input_expo`, `inv_sqrt_controller`: odd (second increment) -/

namespace Corpus.Control

/-- `(a * -c) / d` against `(a * c) / d`: the negation, or both NaN. -/
private theorem neg_mul_div (a c d : Binary32) :
    (a * -c) / d = -((a * c) / d) ∨ (Binary32.isNaN ((a * -c) / d) = true ∧ Binary32.isNaN ((a * c) / d) = true) := by
  by_cases hn : Binary32.isNaN (a * c) = true
  · right
    exact ⟨Corpus.F32.isNaN_div_of_isNaN (Or.inl (by rw [Corpus.F32.isNaN_mul_neg]; exact hn)),
      Corpus.F32.isNaN_div_of_isNaN (Or.inl hn)⟩
  have hn' : Binary32.isNaN (a * c) = false := by simpa using hn
  have ha : Binary32.isNaN a = false := by
    cases h : Binary32.isNaN a
    · rfl
    · exact absurd (Corpus.F32.isNaN_mul_of_isNaN (Or.inl h)) hn
  have hc : Binary32.isNaN c = false := by
    cases h : Binary32.isNaN c
    · rfl
    · exact absurd (Corpus.F32.isNaN_mul_of_isNaN (Or.inr h)) hn
  rw [Corpus.F32.mul_neg' ha hc hn']
  by_cases hq : Binary32.isNaN ((a * c) / d) = true
  · right; exact ⟨by rw [Corpus.F32.isNaN_neg_div]; exact hq, hq⟩
  · left
    have hd : Binary32.isNaN d = false := by
      cases h : Binary32.isNaN d
      · rfl
      · exact absurd (Corpus.F32.isNaN_div_of_isNaN (Or.inr h)) hq
    exact Corpus.F32.neg_div' hn' hd (by simpa using hq)

/-- Order: `input_expo` is odd in the input, as words, for a number `input` and every `expo`: the result for `-input`
is the negation of the result for `input`, or both are NaN (a NaN arises only for a non-finite `expo`, FINDINGS F11). -/
theorem input_expo_odd {i : Binary32} (e : Binary32) (hi : Binary32.isNaN i = false) :
    Id.run (Vehicle_lib.input_expo.pure' (-i) e) = -Id.run (Vehicle_lib.input_expo.pure' i e) ∨
      (Binary32.isNaN (Id.run (Vehicle_lib.input_expo.pure' (-i) e)) = true ∧
        Binary32.isNaN (Id.run (Vehicle_lib.input_expo.pure' i e)) = true) := by
  have hc : Id.run (Vehicle_lib.constrain_value_line'float.pure' (-i) (Binary32.ofBits 0xbf800000)
      (Binary32.ofBits 0x3f800000) (Int32.toUInt32 813)) =
      -Id.run (Vehicle_lib.constrain_value_line'float.pure' i (Binary32.ofBits 0xbf800000)
        (Binary32.ofBits 0x3f800000) (Int32.toUInt32 813)) := by
    rw [← Corpus.F32.neg_one_const]
    exact Corpus.AP_Math.constrain_float_odd _ _ (by decide +kernel) hi
  rw [input_expo_pure_eq, input_expo_pure_eq]
  simp only
  rw [hc, Corpus.F32.abs_neg']
  by_cases he : e < Binary32.ofBits 0x3f733333
  · rw [Corpus.ite_pos he, Corpus.ite_pos he]; exact neg_mul_div _ _ _
  · rw [Corpus.ite_neg he, Corpus.ite_neg he]; exact Or.inl rfl

end Corpus.Control

namespace Corpus.Control

private theorem neg_div_or (o p : Binary32) (ho : Binary32.isNaN o = false) :
    (-o) / p = -(o / p) ∨ (Binary32.isNaN ((-o) / p) = true ∧ Binary32.isNaN (o / p) = true) := by
  by_cases hq : Binary32.isNaN (o / p) = true
  · right; exact ⟨by rw [Corpus.F32.isNaN_neg_div]; exact hq, hq⟩
  · left
    have hp : Binary32.isNaN p = false := by
      cases h : Binary32.isNaN p
      · rfl
      · exact absurd (Corpus.F32.isNaN_div_of_isNaN (Or.inr h)) hq
    exact Corpus.F32.neg_div' ho hp (by simpa using hq)

/-- `ε ≤ |o|`: `o` is a number with `ε ≤ o` or `o ≤ -ε`. -/
private theorem abs_ge_eps {o : Binary32} (ho : Binary32.ofBits 0x34000000 ≤ Binary32.abs o) :
    Binary32.isNaN o = false ∧ (Binary32.ofBits 0x34000000 ≤ o ∨ o ≤ Binary32.ofBits 0xb4000000) := by
  have han := (Corpus.F32.isNaN_false_of_le ho).2
  have hon : Binary32.isNaN o = false := by rw [Corpus.F32.isNaN_abs] at han; exact han
  refine ⟨hon, ?_⟩
  rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_eps han, Corpus.F32.ext_abs hon, le_max_iff] at ho
  rcases ho with h | h
  · left; rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_eps hon]; exact h
  · right
    rw [← Corpus.F32.neg_eps, Corpus.F32.le_iff_ext hon (by decide +kernel), Corpus.F32.ext_neg Corpus.F32.isNaN_eps]
    exact EReal.le_neg_of_le_neg h

/-- Order: for `p ≥ ε` (`is_positive p`) and `|output| ≥ ε`, `inv_sqrt_controller` is odd in `output`, as words (or
both results are NaN). FINDINGS F14, F15: false for `0 < p < ε`, and for `0 < |output| < ε`. -/
theorem inv_sqrt_controller_odd {o p d : Binary32} (hp : Id.run (Vehicle_lib.is_positive'float.pure' p) = true)
    (ho : Binary32.ofBits 0x34000000 ≤ Binary32.abs o) :
    Id.run (Vehicle_lib.inv_sqrt_controller.pure' (-o) p d) = -Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d) ∨
      (Binary32.isNaN (Id.run (Vehicle_lib.inv_sqrt_controller.pure' (-o) p d)) = true ∧
        Binary32.isNaN (Id.run (Vehicle_lib.inv_sqrt_controller.pure' o p d)) = true) := by
  obtain ⟨hon, hsign⟩ := abs_ge_eps ho
  have hzp : Id.run (Vehicle_lib.is_zero.pure' p) = false := by
    cases h : Id.run (Vehicle_lib.is_zero.pure' p)
    · rfl
    · rw [Corpus.AP_Math.is_zero_not_positive p h] at hp; cases hp
  by_cases hlin : Id.run (Vehicle_lib.is_negative'float.pure' d) = true ∨ Id.run (Vehicle_lib.is_zero.pure' d) = true
  · rw [inv_sqrt_controller_of_linear hlin hzp, inv_sqrt_controller_of_linear hlin hzp]
    exact neg_div_or o p hon
  have hn : Id.run (Vehicle_lib.is_negative'float.pure' d) = false := by simp_all
  have hz : Id.run (Vehicle_lib.is_zero.pure' d) = false := by simp_all
  have hg : (Id.run (Vehicle_lib.is_positive'float.pure' d) && Id.run (Vehicle_lib.is_zero.pure' p)) = false := by
    rw [hzp, Bool.and_false]
  by_cases hin : Binary32.abs o < d / p
  · rw [inv_sqrt_controller_of_inside hn hz hg hin,
      inv_sqrt_controller_of_inside hn hz hg (by rw [Corpus.F32.abs_neg']; exact hin)]
    exact neg_div_or o p hon
  rw [inv_sqrt_controller_of_outside hn hz hg hin,
    inv_sqrt_controller_of_outside hn hz hg (by rw [Corpus.F32.abs_neg']; exact hin)]
  have hnon : Binary32.isNaN (-o) = false := by rw [Corpus.F32.isNaN_neg]; exact hon
  have hsq : Id.run (Vehicle_lib.sq.pure' (-o)) = Id.run (Vehicle_lib.sq.pure' o) := by
    rw [Corpus.AP_Math.sq_pure_eq, Corpus.AP_Math.sq_pure_eq]
    have h1 := (Corpus.F32.mul_self_nonneg' hon).1
    have h2 : Binary32.isNaN (o * -o) = false := by rw [Corpus.F32.isNaN_mul_neg]; exact h1
    rw [Corpus.F32.neg_mul' hon hnon h2, Corpus.F32.mul_neg' hon hon h1, Corpus.F32.neg_neg']
  simp only [hsq]
  left
  rcases hsign with h | h
  · have h1 : Id.run (Vehicle_lib.is_positive'float.pure' o) = true := (Corpus.AP_Math.is_positive_iff o).2 h
    have h2 : Id.run (Vehicle_lib.is_positive'float.pure' (-o)) = false := by
      rw [Bool.eq_false_iff, Ne, Corpus.AP_Math.is_positive_iff]
      intro h'
      have h3 : -o ≤ -(Binary32.ofBits 0x34000000) := (Corpus.F32.neg_le_neg_iff' hon Corpus.F32.isNaN_eps).2 h
      have := Corpus.F32.le_trans h' h3
      rw [Corpus.F32.neg_eps] at this
      exact absurd this (by decide +kernel)
    rw [h1, h2]; rfl
  · have h1 : Id.run (Vehicle_lib.is_positive'float.pure' o) = false := by
      rw [Bool.eq_false_iff, Ne, Corpus.AP_Math.is_positive_iff]
      intro h'
      exact absurd (Corpus.F32.le_trans h' h) (by decide +kernel)
    have h2 : Id.run (Vehicle_lib.is_positive'float.pure' (-o)) = true := by
      rw [Corpus.AP_Math.is_positive_iff]
      have := (Corpus.F32.neg_le_neg_iff' (by decide +kernel) hon).2 h
      rwa [show -(Binary32.ofBits 0xb4000000) = Binary32.ofBits 0x34000000 by decide +kernel] at this
    rw [h1, h2]; simp only [Bool.false_eq_true, ite_false, ite_true, Corpus.F32.neg_neg']

end Corpus.Control

namespace Corpus.Control

/-- Case: `input_expo` fixes `0` for a finite `expo`: the result is a number that denotes `0` (FINDINGS F11: for
`expo = -∞` it is a NaN). -/
theorem input_expo_zero {e : Binary32} (he : Binary32.isFinite e = true) :
    Binary32.isNaN (Id.run (Vehicle_lib.input_expo.pure' (Binary32.ofBits 0x00000000) e)) = false ∧
      Corpus.F32.ext (Id.run (Vehicle_lib.input_expo.pure' (Binary32.ofBits 0x00000000) e)) = 0 := by
  have hc : Id.run (Vehicle_lib.constrain_value_line'float.pure' (Binary32.ofBits 0x00000000) (Binary32.ofBits 0xbf800000)
      (Binary32.ofBits 0x3f800000) (Int32.toUInt32 813)) = Binary32.ofBits 0x00000000 :=
    Corpus.AP_Math.constrain_float_of_mem _ (by decide +kernel) (by decide +kernel)
  rw [input_expo_pure_eq]
  simp only
  rw [hc]
  by_cases hlt : e < Binary32.ofBits 0x3f733333
  · rw [Corpus.ite_pos hlt]
    have h0f : Binary32.isFinite (Binary32.ofBits 0x00000000) = true := by decide +kernel
    have e0 : Corpus.F32.real (Binary32.ofBits 0x00000000) = 0 := by
      rw [Corpus.F32.real_eq_of_toRat? (q := 0) (by decide +kernel)]; simp
    have e1 : Corpus.F32.real (Binary32.ofBits 0x3f800000) = 1 := by
      rw [Corpus.F32.real_eq_of_toRat? (q := 1) (by decide +kernel)]; simp
    have habs : Binary32.abs (Binary32.ofBits 0x00000000) = Binary32.ofBits 0x00000000 := by decide +kernel
    rw [habs]
    have ha := Corpus.F32.isFinite_one_sub he
    -- the numerator: finite, value 0
    have hnf : Binary32.isFinite ((Binary32.ofBits 0x3f800000 - e) * Binary32.ofBits 0x00000000) = true :=
      Corpus.F32.isFinite_mul_of_le ha h0f (by
        rw [e0, abs_zero, mul_zero]; exact Model.toReal_posMaxFinite_nonneg _)
    have hnr : Corpus.F32.real ((Binary32.ofBits 0x3f800000 - e) * Binary32.ofBits 0x00000000) = 0 := by
      rw [Corpus.F32.real_mul hnf, e0, mul_zero, Model.roundAt_zero]
    -- the denominator: `e * 0` is finite with value 0, so `1 - e * 0` is finite with value 1
    have hmf : Binary32.isFinite (e * Binary32.ofBits 0x00000000) = true :=
      Corpus.F32.isFinite_mul_of_le he h0f (by
        rw [e0, abs_zero, mul_zero]; exact Model.toReal_posMaxFinite_nonneg _)
    have hmr : Corpus.F32.real (e * Binary32.ofBits 0x00000000) = 0 := by
      rw [Corpus.F32.real_mul hmf, e0, mul_zero, Model.roundAt_zero]
    have h1f : Binary32.isFinite (Binary32.ofBits 0x3f800000) = true := by decide +kernel
    obtain ⟨hdf, -, -⟩ := Corpus.F32.sub_mem h1f hmf h1f h1f (by rw [hmr, e1]; norm_num) (by rw [hmr, e1]; norm_num)
    have hdr : Corpus.F32.real (Binary32.ofBits 0x3f800000 - e * Binary32.ofBits 0x00000000) = 1 := by
      rw [Corpus.F32.real_sub hdf, hmr, e1, sub_zero, ← e1]; exact Model.roundAt_toReal_eq (Corpus.F32.model (Binary32.ofBits 0x3f800000)) h1f
    have hd0 : Model.isZero (Corpus.F32.model (Binary32.ofBits 0x3f800000 - e * Binary32.ofBits 0x00000000)) = false := by
      cases hz : Model.isZero (Corpus.F32.model (Binary32.ofBits 0x3f800000 - e * Binary32.ofBits 0x00000000))
      · rfl
      · have := Model.toReal_eq_zero_of_isZero _ hz
        have hdr' : Corpus.F32.real (Binary32.ofBits 0x3f800000 - e * Binary32.ofBits 0x00000000) = 0 := this
        rw [hdr] at hdr'; norm_num at hdr'
    obtain ⟨hqf, hq1, hq2⟩ := Corpus.F32.div_mem hnf hdf hd0 h0f h0f (by rw [hnr, hdr, e0]; norm_num)
      (by rw [hnr, hdr, e0]; norm_num)
    have hqn : Binary32.isNaN _ = false := Model.isNaN_eq_false_of_isFinite_eq_true (Corpus.F32.model _) hqf
    refine ⟨hqn, ?_⟩
    rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_zero hqn, Corpus.F32.ext_zero] at hq1
    rw [Corpus.F32.le_iff_ext hqn Corpus.F32.isNaN_zero, Corpus.F32.ext_zero] at hq2
    exact le_antisymm hq2 hq1
  · rw [Corpus.ite_neg hlt]; exact ⟨by decide +kernel, Corpus.F32.ext_zero⟩

end Corpus.Control
