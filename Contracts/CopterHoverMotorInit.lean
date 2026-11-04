import Contracts.CopterVertNearStep
import Contracts.CopterZero
import AP_Motors.AP_MotorsMatrix

/-!
# The motors object at boot

`AP_MotorsMatrix.init CopterVertNear.runMot` builds the quad-X mixer: `setup_motors` removes the
four slots, `setup_quad_matrix` adds them back through `add_motor` (roll factor
`cosf(radians(angle + 90))`, pitch factor `cosf(radians(angle))`, yaw factor `±1`, throttle factor
`1`), and `normalise_rpy_factors` scales each axis to maximum magnitude `0.5`.

The roll and pitch factors come from `Float32.cos`, an opaque `extern` constant, so their finiteness
is a C-library fact: `LibmCos32` (finite argument, finite result). Nothing else about `cosf` is
needed, not even `|cosf x| ≤ 1`, because the normalization divides each factor by the maximum of the
magnitudes, so every quotient has magnitude at most `0.5` in reals and at most `1` after rounding.

The proof never unrolls the whole construction with symbolic `cos` values:
- `init_eq_normalise`: up to `normalise_rpy_factors`, `init` is the literal state `bootQuad`, whose
  roll and pitch vectors hold the eight `cosf` terms (kernel `rfl`);
- `normalise_eq`: for an arbitrary state with all four motors enabled, `normalise_rpy_factors`
  replaces each factor vector by a closed form (`normRpy`, `normThr`), proved once over a variable
  state, so the goals stay small;
- `normRpy_fin`: `normRpy` maps finite vectors to finite vectors (`half_div_fin`);
- the yaw and throttle vectors are concrete and are computed by the kernel (`decide +kernel`).

Main results: `init_factors` (what `motors_output_main_hover` needs), `init_fields` and `init_Z`
(the other members at boot, as literals), and `init_runMot_eq` (the state in closed form).
-/

open Float.Model UnpackedFloat AP_Math AP_MotorsMatrix Contracts.CopterZero

namespace Contracts.CopterHover

/-! ## The C-library hypothesis -/

/-- `cosf` of a finite argument is finite (C99 Annex F, F.9.1.5: `cos` is defined on every finite
argument and returns NaN only for an infinite or NaN argument). `Float32.cos` is an opaque `extern`
constant, so this cannot be computed. -/
-- <<LibmCos32>>
structure LibmCos32 : Prop where
  cos_fin : ∀ x : Float32, x.IsFinite → (Float32.cos x).IsFinite
-- <</LibmCos32>>

/-! ## `normalise_rpy_factors` in closed form -/

/-- The roll, pitch or yaw maximum of `normalise_rpy_factors` (`.cpp:1362-1366`) with all four
motors enabled: `MAX(MAX(MAX(MAX(0, |v0|), |v1|), |v2|), |v3|)`. -/
def rpyMax (v : Vector Float32 4) : Float32 :=
  MAX (MAX (MAX (MAX 0.0 v[(0 : Fin 4)].abs) v[(1 : Fin 4)].abs) v[(2 : Fin 4)].abs) v[(3 : Fin 4)].abs

/-- The throttle maximum of `normalise_rpy_factors` (`.cpp:1367`) with all four motors enabled. -/
def thrMax (v : Vector Float32 4) : Float32 :=
  MAX (MAX (MAX (MAX 0.0 (MAX 0.0 v[(0 : Fin 4)])) (MAX 0.0 v[(1 : Fin 4)])) (MAX 0.0 v[(2 : Fin 4)]))
    (MAX 0.0 v[(3 : Fin 4)])

/-- The unfolded `rpyMax`, as the loop leaves it. -/
theorem rpyMax_eq (v : Vector Float32 4) :
    MAX (MAX (MAX (MAX 0.0 v[(0 : Fin 4)].abs) v[(1 : Fin 4)].abs) v[(2 : Fin 4)].abs) v[(3 : Fin 4)].abs
      = rpyMax v := rfl

/-- The unfolded `thrMax`, as the loop leaves it. -/
theorem thrMax_eq (v : Vector Float32 4) :
    MAX (MAX (MAX (MAX 0.0 (MAX 0.0 v[(0 : Fin 4)])) (MAX 0.0 v[(1 : Fin 4)])) (MAX 0.0 v[(2 : Fin 4)]))
      (MAX 0.0 v[(3 : Fin 4)]) = thrMax v := rfl

/-- A roll, pitch or yaw vector after `normalise_rpy_factors` (`.cpp:1372-1380`): unchanged when its
maximum `is_zero`, otherwise each entry becomes `0.5 * v[i] / max`. -/
def normRpy (v : Vector Float32 4) : Vector Float32 4 :=
  if is_zero (rpyMax v) then v
  else #v[0.5 * v[(0 : Fin 4)] / rpyMax v, 0.5 * v[(1 : Fin 4)] / rpyMax v,
    0.5 * v[(2 : Fin 4)] / rpyMax v, 0.5 * v[(3 : Fin 4)] / rpyMax v]

/-- The throttle vector after `normalise_rpy_factors` (`.cpp:1381-1383`). -/
def normThr (v : Vector Float32 4) : Vector Float32 4 :=
  if is_zero (thrMax v) then v
  else #v[MAX 0.0 (v[(0 : Fin 4)] / thrMax v), MAX 0.0 (v[(1 : Fin 4)] / thrMax v),
    MAX 0.0 (v[(2 : Fin 4)] / thrMax v), MAX 0.0 (v[(3 : Fin 4)] / thrMax v)]

/-- Four successive in-place updates `v[i] := g v[i]`, each reading the partly updated vector at
its own index, give `#v[g v0, g v1, g v2, g v3]`. -/
theorem set_seq4 (v : Vector Float32 4) (g : Float32 → Float32) :
    let v1 := v.set ((0 : Fin 4) : ℕ) (g v[(0 : Fin 4)])
    let v2 := v1.set ((1 : Fin 4) : ℕ) (g v1[(1 : Fin 4)])
    let v3 := v2.set ((2 : Fin 4) : ℕ) (g v2[(2 : Fin 4)])
    v3.set ((3 : Fin 4) : ℕ) (g v3[(3 : Fin 4)]) =
      #v[g v[(0 : Fin 4)], g v[(1 : Fin 4)], g v[(2 : Fin 4)], g v[(3 : Fin 4)]] := by
  intro v1 v2 v3
  ext i hi
  match i, hi with
  | 0, _ => simp [v1, v2, v3]
  | 1, _ => simp [v1, v2, v3]
  | 2, _ => simp [v1, v2, v3]
  | 3, _ => simp [v1, v2, v3]

set_option linter.unusedSimpArgs false in
/-- **Frame lemma for `normalise_rpy_factors`.** With all four motors enabled it changes only the
four factor vectors, to `normRpy` (roll, pitch, yaw) and `normThr` (throttle). The state is a
variable, so the sixteen branches on the four `is_zero` tests stay small. -/
theorem normalise_eq (s : State) (h : s.motor_enabled = #v[true, true, true, true]) :
    normalise_rpy_factors s = { s with
      _roll_factor := normRpy s._roll_factor
      _pitch_factor := normRpy s._pitch_factor
      _yaw_factor := normRpy s._yaw_factor
      _throttle_factor := normThr s._throttle_factor } := by
  unfold normalise_rpy_factors
  have hfin : List.finRange 4 = [0, 1, 2, 3] := by decide
  have e0 : (#v[true, true, true, true] : Vector Bool 4)[(0 : Fin 4)] = true := rfl
  have e1 : (#v[true, true, true, true] : Vector Bool 4)[(1 : Fin 4)] = true := rfl
  have e2 : (#v[true, true, true, true] : Vector Bool 4)[(2 : Fin 4)] = true := rfl
  have e3 : (#v[true, true, true, true] : Vector Bool 4)[(3 : Fin 4)] = true := rfl
  simp only [Id.run, hfin, List.forIn_cons, List.forIn_nil, h, e0, e1, e2, e3, ite_true, pure_bind]
  rw [rpyMax_eq, rpyMax_eq, rpyMax_eq, thrMax_eq]
  cases hr : is_zero (rpyMax s._roll_factor) <;> cases hp : is_zero (rpyMax s._pitch_factor) <;>
    cases hy : is_zero (rpyMax s._yaw_factor) <;> cases ht : is_zero (thrMax s._throttle_factor) <;>
    simp only [h, e0, e1, e2, e3, hr, hp, hy, ht, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true, pure_bind, normRpy, normThr]
  all_goals
    show State.mk _ _ _ _ _ _ _ = _
    simp only [State.mk.injEq, true_and, and_true]
    try and_intros
    all_goals first
      | with_reducible exact set_seq4 _ (fun x => 0.5 * x / rpyMax _)
      | with_reducible exact set_seq4 _ (fun x => MAX 0.0 (x / thrMax _))

/-! ## Finiteness of the normalized factors -/

/-- `MAX` of two finite floats is finite and bounds both in value. -/
theorem MAX_spec {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MAX a b).IsFinite ∧ a.toReal ≤ (MAX a b).toReal ∧ b.toReal ≤ (MAX a b).toReal := by
  rw [MAX_eq]
  split_ifs with h
  · exact ⟨ha, le_rfl, ((lt_iff hb ha).1 h).le⟩
  · exact ⟨hb, not_lt.1 (fun h' => h ((lt_iff hb ha).2 h')), le_rfl⟩

/-- For a finite vector, `rpyMax` is finite, nonnegative, and bounds every magnitude. -/
theorem rpyMax_spec {v : Vector Float32 4} (hv : ∀ i : Fin 4, v[i].IsFinite) :
    (rpyMax v).IsFinite ∧ 0 ≤ (rpyMax v).toReal ∧ ∀ i : Fin 4, |v[i].toReal| ≤ (rpyMax v).toReal := by
  have ha : ∀ i : Fin 4, v[i].abs.IsFinite := fun i => (isFinite_abs _).2 (hv i)
  obtain ⟨f1, l1, r1⟩ := MAX_spec Z_lit0.1 (ha 0)
  obtain ⟨f2, l2, r2⟩ := MAX_spec f1 (ha 1)
  obtain ⟨f3, l3, r3⟩ := MAX_spec f2 (ha 2)
  obtain ⟨f4, l4, r4⟩ := MAX_spec f3 (ha 3)
  rw [toReal_abs] at r1 r2 r3 r4
  rw [Z_lit0.2] at l1
  refine ⟨f4, by unfold rpyMax; linarith, fun i => ?_⟩
  unfold rpyMax
  fin_cases i
  · exact r1.trans (l2.trans (l3.trans l4))
  · exact r2.trans (l3.trans l4)
  · exact r3.trans l4
  · exact r4

/-- `0.5 * c / r` is finite when `c` and `r` are finite and `0 < r`, `|c| ≤ r`: the rounded
`0.5 * c` stays in `[-r, r]` (rounding is monotone and `±r` are floats), so the quotient has
magnitude at most `1` before rounding. -/
theorem half_div_fin {c r : Float32} (hc : c.IsFinite) (hr : r.IsFinite) (hle : |c.toReal| ≤ r.toReal)
    (hpos : 0 < r.toReal) : (0.5 * c / r).IsFinite := by
  obtain ⟨hhf, hhv⟩ := lit_half
  have hM : |(0.5 : Float32).toReal * c.toReal| ≤ maxFinite32 := by
    rw [hhv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := Float32.abs_toReal_le_maxFinite c
    have : 0 ≤ |c.toReal| := abs_nonneg _
    linarith
  have hmf := (Float32.mul_err_all hhf hc hM).1
  have hb1 := (Float32.mul_bracket hhf hc hM hr).2
  have hb2 := (Float32.mul_bracket hhf hc hM ((Float32.isFinite_neg r).2 hr)).1
  rw [Float32.toReal_neg, hhv] at hb2
  rw [hhv] at hb1
  have hca := abs_le.1 hle
  have hu : (0.5 * c).toReal ≤ r.toReal := hb1 (by linarith)
  have hl : -r.toReal ≤ (0.5 * c).toReal := hb2 (by linarith)
  have hq : |(0.5 * c).toReal / r.toReal| ≤ maxFinite32 := by
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have : |(0.5 * c).toReal| ≤ r.toReal := abs_le.2 ⟨hl, hu⟩
    nlinarith [Float32.one_le_maxFinite32]
  exact (Float32.div_err_all hmf hr hpos.ne' hq).1

/-- `normalise_rpy_factors` maps finite roll, pitch or yaw factors to finite factors: either the
vector is unchanged, or its maximum is at least `FLT_EPSILON` and `half_div_fin` applies. -/
theorem normRpy_fin {v : Vector Float32 4} (hv : ∀ i : Fin 4, v[i].IsFinite) :
    ∀ i : Fin 4, ((normRpy v)[i]).IsFinite := by
  obtain ⟨hf, h0, hle⟩ := rpyMax_spec hv
  intro i
  unfold normRpy
  split
  · exact hv i
  · rename_i hz
    have hz' : ¬ (rpyMax v).abs < FLT_EPSILON := by simpa [is_zero] using hz
    rw [lt_iff ((isFinite_abs _).2 hf) FLT_EPSILON_spec.1, toReal_abs, FLT_EPSILON_spec.2,
      abs_of_nonneg h0, not_lt] at hz'
    have hpos : 0 < (rpyMax v).toReal := lt_of_lt_of_le eps_pos hz'
    fin_cases i
    · exact half_div_fin (hv 0) hf (hle 0) hpos
    · exact half_div_fin (hv 1) hf (hle 1) hpos
    · exact half_div_fin (hv 2) hf (hle 2) hpos
    · exact half_div_fin (hv 3) hf (hle 3) hpos

/-- The quad-X yaw factors `(1, 1, -1, -1)` normalize to `(0.5, 0.5, -0.5, -0.5)` (kernel
computation). -/
theorem normRpy_yaw : normRpy #v[AP_MOTORS_MATRIX_YAW_FACTOR_CCW, AP_MOTORS_MATRIX_YAW_FACTOR_CCW,
      AP_MOTORS_MATRIX_YAW_FACTOR_CW, AP_MOTORS_MATRIX_YAW_FACTOR_CW] = #v[0.5, 0.5, -0.5, -0.5] := by
  decide +kernel

/-- The throttle factors `(1, 1, 1, 1)` are left at `1` (kernel computation). -/
theorem normThr_one : normThr #v[1.0, 1.0, 1.0, 1.0] = #v[1.0, 1.0, 1.0, 1.0] := by
  decide +kernel

/-! ## The boot state -/

/-- `cosf(radians(a))`, the factor `add_motor_rp` computes from an angle (`.cpp:541-542`). -/
abbrev motorCos (a : Float32) : Float32 := (radians a).cos

/-- The state `init` passes to `normalise_rpy_factors`: the constructor members, the four quad-X
motors of `setup_quad_matrix` (`.cpp:582-586`) added, `_initialised_ok` still false. -/
def bootQuad : State :=
  { _throttle_filter_cutoff := 0.0
    _throttle_filter_value := 0.0
    limit := ({} : AP_Motors.Limit).set_all true
    _throttle_hover := CopterVertNear.runMot.MOT_THST_HOVER
    _throttle_limit := 1.0
    motor_enabled := #v[true, true, true, true]
    _roll_factor := #v[motorCos (45 + 90), motorCos (-135 + 90), motorCos (-45 + 90),
      motorCos (135 + 90)]
    _pitch_factor := #v[motorCos 45, motorCos (-135), motorCos (-45), motorCos 135]
    _yaw_factor := #v[AP_MOTORS_MATRIX_YAW_FACTOR_CCW, AP_MOTORS_MATRIX_YAW_FACTOR_CCW,
      AP_MOTORS_MATRIX_YAW_FACTOR_CW, AP_MOTORS_MATRIX_YAW_FACTOR_CW]
    _throttle_factor := #v[1.0, 1.0, 1.0, 1.0]
    _test_order := #v[1, 3, 4, 2] }

/-- `init` is `normalise_rpy_factors bootQuad` with `_initialised_ok` set (the removals and the
additions are record updates on literal vectors, so this is `rfl`). -/
theorem init_eq_normalise : init CopterVertNear.runMot =
    { normalise_rpy_factors bootQuad with _initialised_ok := true } := by
  rfl

/-- **The boot state in closed form.** Roll and pitch factors are `normRpy` of the `cosf` terms;
yaw and throttle factors are computed. -/
theorem init_runMot_eq : init CopterVertNear.runMot =
    { bootQuad with
      _roll_factor := normRpy bootQuad._roll_factor
      _pitch_factor := normRpy bootQuad._pitch_factor
      _yaw_factor := #v[0.5, 0.5, -0.5, -0.5]
      _throttle_factor := #v[1.0, 1.0, 1.0, 1.0]
      _initialised_ok := true } := by
  have hy : normRpy bootQuad._yaw_factor = #v[0.5, 0.5, -0.5, -0.5] := normRpy_yaw
  have ht : normThr bootQuad._throttle_factor = #v[1.0, 1.0, 1.0, 1.0] := normThr_one
  rw [init_eq_normalise, normalise_eq bootQuad rfl, hy, ht]

/-! ## The facts `motors_output_main_hover` needs -/

/-- **The motor factors at boot.** All four motors are enabled; the roll, pitch and yaw factors are
finite (roll and pitch under `LibmCos32`, since the eight `cosf` arguments are finite); the
throttle factors have value one; the boost ratio is a zero; the hover throttle is `hoverF`. -/
theorem init_factors (LC : LibmCos32) :
    let m := AP_MotorsMatrix.init CopterVertNear.runMot
    m.motor_enabled = #v[true, true, true, true] ∧
    (∀ i : Fin 4, (m._roll_factor[i]).IsFinite) ∧ (∀ i : Fin 4, (m._pitch_factor[i]).IsFinite) ∧
    (∀ i : Fin 4, (m._yaw_factor[i]).IsFinite) ∧ (∀ i : Fin 4, CopterZero.One m._throttle_factor[i]) ∧
    CopterZero.Z m._thrust_boost_ratio ∧ m._throttle_hover = CopterVertNear.hoverF := by
  rw [init_runMot_eq]
  refine ⟨rfl, normRpy_fin fun i => ?_, normRpy_fin fun i => ?_, fun i => ?_, fun i => ?_, Z_lit0, rfl⟩
  · fin_cases i <;> exact LC.cos_fin _ (by decide +kernel)
  · fin_cases i <;> exact LC.cos_fin _ (by decide +kernel)
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> exact lit_one

/-- The other members of the boot state, as literals (no hypothesis). -/
theorem init_fields :
    let m := AP_MotorsMatrix.init CopterVertNear.runMot
    m._initialised_ok = true ∧ m._yaw_factor = #v[0.5, 0.5, -0.5, -0.5] ∧
    m._throttle_factor = #v[1.0, 1.0, 1.0, 1.0] ∧ m._test_order = #v[1, 3, 4, 2] ∧
    m._throttle_filter_value = 0.0 ∧ m._throttle_filter_cutoff = 0.0 ∧
    m._throttle_in = 0 ∧ m._throttle_avg_max = 0 ∧
    m._roll_in = 0 ∧ m._roll_in_ff = 0 ∧ m._pitch_in = 0 ∧ m._pitch_in_ff = 0 ∧
    m._yaw_in = 0 ∧ m._yaw_in_ff = 0 ∧ m._throttle_out = 0 ∧ m._throttle_thrust_max = 0 ∧
    m.limit = ({} : AP_Motors.Limit).set_all true ∧ m._dt_s = 0.0 ∧ m.air_density_ratio = 1.0 ∧
    m._thrust_boost_ratio = 0.0 ∧ m._spin_up_ratio = 0.0 ∧ m._throttle_limit = 1.0 ∧
    m._disarm_safe_timer = 0.0 ∧ m._actuator = #v[0.0, 0.0, 0.0, 0.0] ∧
    m._thrust_rpyt_out = #v[0.0, 0.0, 0.0, 0.0] ∧ m.thr_lin = {} ∧
    m._throttle_hover = CopterVertNear.hoverF := by
  rw [init_runMot_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The controller inputs, the throttle filter, the boost ratio and `_dt_s` at boot are zeros. -/
theorem init_Z :
    let m := AP_MotorsMatrix.init CopterVertNear.runMot
    Z m._roll_in ∧ Z m._roll_in_ff ∧ Z m._pitch_in ∧ Z m._pitch_in_ff ∧ Z m._yaw_in ∧
    Z m._yaw_in_ff ∧ Z m._throttle_in ∧ Z m._throttle_filter_value ∧ Z m._throttle_filter_cutoff ∧
    Z m._thrust_boost_ratio ∧ Z m._dt_s := by
  rw [init_runMot_eq]
  exact ⟨Z_zero, Z_zero, Z_zero, Z_zero, Z_zero, Z_zero, Z_zero, Z_lit0, Z_lit0, Z_lit0, Z_lit0⟩

end Contracts.CopterHover
