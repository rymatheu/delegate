import Contracts.Mission.NavStop

/-!
# Milestone (b), geometric part: a straight S-curve leg puts the target on the leg

`SCurve::project_scurve_onto_track` of a straight segment adds `P · normalized(seg_delta)` to the
origin (in `float`, widened to `double`). If the S-curve position `P` is in `[0, ‖seg_delta‖ + e]`, the
result is within `e + 2⁻¹⁹ P + 2⁻³⁸` of the segment from the origin to the destination
(`proj_straight_near`). The bound on `P` is the property of the S-curve's segment table that the
proof of the full invariant still needs (`MISSION.md`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-- The square of a finite `float` of magnitude at most `100`. -/
theorem A32.sq_exact {a : Float32} (ha : a.IsFinite) (ha' : |a.toReal| ≤ 100) :
    A32 (a * a) (a.toReal ^ 2) (u32 * a.toReal ^ 2 + η32) := by
  have hm : |a.toReal * a.toReal| ≤ maxFinite32 := by
    rw [abs_mul_self]
    have : a.toReal * a.toReal ≤ 10000 := by nlinarith [sq_abs a.toReal, abs_nonneg a.toReal]
    have : (10000 : ℝ) ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha ha hm
  refine ⟨hf, ?_⟩
  have := rnd32 he
  rwa [abs_mul_self, ← sq] at this

/-- A sum of nonnegative approximations. -/
theorem A32.add_nonneg {a b : Float32} {ra rb ea eb : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hra : 0 ≤ ra) (hrb : 0 ≤ rb) (hc : ra + rb + ea + eb ≤ capF) :
    A32 (a + b) (ra + rb) (ea + eb + u32 * (ra + rb + ea + eb) + η32) := by
  have := A32.add ha hb (by rw [abs_of_nonneg (by linarith)]; exact hc)
  rwa [abs_of_nonneg (by linarith : 0 ≤ ra + rb)] at this

set_option maxHeartbeats 1000000 in
/-- The `float` length of a `float` vector, relative to the exact length. -/
theorem len_approx {dx dy dz : Float32} (hx : dx.IsFinite) (hy : dy.IsFinite) (hz : dz.IsFinite)
    (hx' : |dx.toReal| ≤ 100) (hy' : |dy.toReal| ≤ 100) (hz' : |dz.toReal| ≤ 100)
    (hL : (1 / 2 ^ 30 : ℝ) ≤ Real.sqrt (dx.toReal ^ 2 + dy.toReal ^ 2 + dz.toReal ^ 2)) :
    (dx * dx + dy * dy + dz * dz).sqrt.IsFinite ∧
      |(dx * dx + dy * dy + dz * dz).sqrt.toReal -
          Real.sqrt (dx.toReal ^ 2 + dy.toReal ^ 2 + dz.toReal ^ 2)| ≤
        1 / 2 ^ 21 * Real.sqrt (dx.toReal ^ 2 + dy.toReal ^ 2 + dz.toReal ^ 2) := by
  set L := Real.sqrt (dx.toReal ^ 2 + dy.toReal ^ 2 + dz.toReal ^ 2) with hLd
  set x := dx.toReal
  set y := dy.toReal
  set z := dz.toReal
  have hu32 : u32 = 1 / 16777216 := by norm_num [u32]
  have e32 := η32_small
  have p32 := η32_pos
  have hS : x ^ 2 + y ^ 2 + z ^ 2 = L ^ 2 := by
    rw [hLd, Real.sq_sqrt (by positivity)]
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hx2 : x ^ 2 ≤ 10000 := by nlinarith [sq_abs x, abs_nonneg x]
  have hy2 : y ^ 2 ≤ 10000 := by nlinarith [sq_abs y, abs_nonneg y]
  have hz2 : z ^ 2 ≤ 10000 := by nlinarith [sq_abs z, abs_nonneg z]
  have ax := A32.sq_exact hx hx'
  have ay := A32.sq_exact hy hy'
  have az := A32.sq_exact hz hz'
  have axy := A32.add_nonneg ax ay (sq_nonneg _) (sq_nonneg _) (by
    rw [hu32]; norm_num [capF]; nlinarith)
  have axyz := A32.add_nonneg axy az (by positivity) (sq_nonneg _) (by
    rw [hu32]; norm_num [capF]; nlinarith)
  -- the sum of squares is nonnegative
  obtain ⟨f1, n1, l1⟩ := sq_nonneg32 hx (by norm_num; linarith)
  obtain ⟨f2, n2, l2⟩ := sq_nonneg32 hy (by norm_num; linarith)
  obtain ⟨f3, n3, l3⟩ := sq_nonneg32 hz (by norm_num; linarith)
  have hu1 : u32 ≤ 1 := by rw [hu32]; norm_num
  have hu0 : 0 ≤ u32 := u32_pos.le
  have hb1 : (dx * dx).toReal ≤ 20001 := by
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg x)
    nlinarith only [l1, this, hx2, e32]
  have hb2 : (dy * dy).toReal ≤ 20001 := by
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg y)
    nlinarith only [l2, this, hy2, e32]
  have hb3 : (dz * dz).toReal ≤ 20001 := by
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg z)
    nlinarith only [l3, this, hz2, e32]
  have hcap : (1000000 : ℝ) ≤ maxFinite32 := le_trans (by norm_num [capF]) capF_le_max32
  have hsum0 : 0 ≤ (dx * dx + dy * dy + dz * dz).toReal := by
    have m1 : |(dx * dx).toReal + (dy * dy).toReal| ≤ maxFinite32 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have b1 := ((Float32.add_bracket f1 f2 m1 Float32.isFinite_zero).1
      (by rw [Float32.toReal_zero]; linarith))
    rw [Float32.toReal_zero] at b1
    obtain ⟨f12, e12⟩ := Float32.add_err_all f1 f2 m1
    have hb12 : (dx * dx + dy * dy).toReal ≤ 80004 := by
      have h1 := (abs_le.1 e12).2
      rw [abs_of_nonneg (by linarith)] at h1
      have h2 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 := by norm_num
      have h3 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ (dx * dx).toReal + (dy * dy).toReal)
      have h4 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 := by norm_num
      generalize (2 : ℝ) ^ (-24 : ℤ) = c at h1 h2 h3
      generalize (2 : ℝ) ^ (-150 : ℤ) = d at h1 h4
      linarith
    have m2 : |(dx * dx + dy * dy).toReal + (dz * dz).toReal| ≤ maxFinite32 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have b2 := ((Float32.add_bracket f12 f3 m2 Float32.isFinite_zero).1
      (by rw [Float32.toReal_zero]; linarith))
    rwa [Float32.toReal_zero] at b2
  have hsumM : (dx * dx + dy * dy + dz * dz).toReal ≤ maxFinite32 :=
    (le_abs_self _).trans (Float32.abs_toReal_le_maxFinite _)
  obtain ⟨fl, el⟩ := Float32.sqrt_err_all axyz.1 hsum0 hsumM
  refine ⟨fl, ?_⟩
  -- `|√SQ - L| ≤ |SQ - L²| / L`
  set SQ := (dx * dx + dy * dy + dz * dz).toReal
  have hE := axyz.2
  rw [hS] at hE
  have hsq : |Real.sqrt SQ - L| ≤ |SQ - L ^ 2| / L := by
    rw [le_div_iff₀ hL0]
    have h1 : Real.sqrt SQ - L = (SQ - L ^ 2) / (Real.sqrt SQ + L) := by
      rw [eq_div_iff (by positivity)]
      have := Real.sq_sqrt hsum0
      nlinarith
    rw [h1, abs_div, abs_of_pos (by positivity : 0 < Real.sqrt SQ + L)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg SQ]) (abs_nonneg _)
  -- the error of the sum of squares: at most `4 u L²`
  have hL2 : (1 / 2 ^ 60 : ℝ) ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hL 2; norm_num at this ⊢; linarith
  have hErr : |SQ - L ^ 2| ≤ 4 / 16777216 * L ^ 2 := by
    refine hE.trans ?_
    have hx0 := sq_nonneg x
    have hy0 := sq_nonneg y
    have hz0 := sq_nonneg z
    rw [hu32]
    generalize η32 = e at e32 p32 ⊢
    have : e ≤ 1 / 2 ^ 70 * L ^ 2 := by
      have : (1 / 2 ^ 70 : ℝ) * (1 / 2 ^ 60) ≤ 1 / 2 ^ 70 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by norm_num)
      have : (1 / 10 ^ 40 : ℝ) ≤ 1 / 2 ^ 70 * (1 / 2 ^ 60) := by norm_num
      linarith
    linarith
  have hsq' : |Real.sqrt SQ - L| ≤ 4 / 16777216 * L := by
    refine hsq.trans ?_
    rw [div_le_iff₀ hL0]
    have : 4 / 16777216 * L * L = 4 / 16777216 * L ^ 2 := by ring
    linarith
  have hsqrt : Real.sqrt SQ ≤ 2 * L := by
    have := (abs_le.1 hsq').2; linarith
  have h1 := el
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 16777216 * L := by
    have : (1 / 16777216 : ℝ) * (1 / 2 ^ 30) ≤ 1 / 16777216 * L :=
      mul_le_mul_of_nonneg_left hL (by norm_num)
    have : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 16777216 * (1 / 2 ^ 30) := by norm_num
    linarith
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [h24] at h1
  have := abs_sub_le (dx * dx + dy * dy + dz * dz).sqrt.toReal (Real.sqrt SQ) L
  generalize (2 : ℝ) ^ (-150 : ℤ) = d at h1 h150
  norm_num
  linarith

/-- One axis of the projection: `pos + (d/ℓ) · P` in `double`, against the exact
`pos + (d/L) · P`. -/
theorem axis_proj (hL : LibmSpec) {dc ℓ P : Float32} {pc : Float} {L : ℝ} (hdc : dc.IsFinite)
    (hdcL : |dc.toReal| ≤ L) (hℓ : A32 ℓ L (L / 2 ^ 21)) (hL1 : (1 / 2 ^ 30 : ℝ) ≤ L)
    (hP : P.IsFinite) (hP0 : 0 ≤ P.toReal) (hP10 : P.toReal ≤ 10)
    (hpc : pc.IsFinite) (hpc' : |pc.toReal| ≤ 100) :
    |(pc + Float32.toFloat (dc / ℓ) * Float32.toFloat P).toReal -
        (pc.toReal + dc.toReal / L * P.toReal)| ≤ P.toReal / 2 ^ 19 + 1 / 2 ^ 42 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hu32 : u32 = 1 / 16777216 := by norm_num [u32]
  have hu64 : u64 = 1 / 9007199254740992 := by norm_num [u64]
  have e32 := η32_small
  have p32 := η32_pos
  have e64 := η64_small
  have p64 := η64_pos
  have hq1 : |dc.toReal / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL0, div_le_one hL0]; exact hdcL
  -- the unit vector's component
  have aux := A32.div (A32.of_exact hdc) hℓ (m := L / 2) (by positivity)
    (by rw [abs_of_pos hL0]; nlinarith) (by
      rw [abs_of_pos hL0]
      have : (L * 0 + |dc.toReal| * (L / 2 ^ 21)) / (L / 2 * L) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [abs_nonneg dc.toReal]
      have : (2 : ℝ) ≤ capF := by norm_num [capF]
      linarith)
  rw [abs_of_pos hL0] at aux
  have hε : (L * 0 + |dc.toReal| * (L / 2 ^ 21)) / (L / 2 * L) ≤ 1 / 2 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have : |dc.toReal| * (L / 2 ^ 21) ≤ L * (L / 2 ^ 21) :=
      mul_le_mul_of_nonneg_right hdcL (by positivity)
    nlinarith
  have aux' : A32 (dc / ℓ) (dc.toReal / L) (1 / 2 ^ 20 + u32 * (1 + 1 / 2 ^ 20) + η32) :=
    aux.mono (by
      have h1 := mul_le_mul_of_nonneg_left (add_le_add hq1 hε) u32_pos.le
      linarith)
  -- the product and the sum, in `double`
  have am := A64.mul (aux'.toFloat hL) ((A32.of_exact hP).toFloat hL) (by
    rw [hu32, abs_mul]
    have : |P.toReal| ≤ 10 := by rw [abs_of_nonneg hP0]; exact hP10
    have h1 : |dc.toReal / L| * |P.toReal| ≤ 10 := by nlinarith [abs_nonneg (dc.toReal / L), abs_nonneg P.toReal]
    have : (1000 : ℝ) ≤ capF := by norm_num [capF]
    nlinarith [abs_nonneg (dc.toReal / L), abs_nonneg P.toReal])
  have as := (A64.of_exact hpc).add am (by
    rw [hu32, abs_mul]
    have : |P.toReal| ≤ 10 := by rw [abs_of_nonneg hP0]; exact hP10
    have h0 := abs_add_le pc.toReal (dc.toReal / L * P.toReal)
    rw [abs_mul] at h0
    have : (10000 : ℝ) ≤ capF := by norm_num [capF]
    nlinarith [abs_nonneg (dc.toReal / L), abs_nonneg P.toReal])
  have h := as.2
  have hPa : |P.toReal| = P.toReal := abs_of_nonneg hP0
  have f1 : |dc.toReal / L| * P.toReal ≤ P.toReal := mul_le_of_le_one_left hP0 hq1
  have h0 := abs_add_le pc.toReal (dc.toReal / L * P.toReal)
  rw [abs_mul, hPa] at h0
  have f2 : P.toReal * η32 ≤ 10 * (1 / 10 ^ 40) := mul_le_mul hP10 e32 p32.le (by norm_num)
  rw [hu32, hu64] at h
  simp only [abs_mul, hPa] at h
  norm_num at h ⊢
  nlinarith

/-- The S-curve position is clamped at `0` (`Pt_out = MAX(0, Pt_out)`): when finite, it is
nonnegative. The upper bound `P ≤ ‖seg_delta‖ + e` is a property of the segment table
(`calculate_path`, `add_segments`), which this package does not prove yet. -/
theorem scurve_pos_nonneg (s : SCurve.State) (t J A V P : Float32)
    (hf : (SCurve.get_jerk_accel_vel_pos_at_time s t J A V P).2.2.2.IsFinite) :
    0 ≤ (SCurve.get_jerk_accel_vel_pos_at_time s t J A V P).2.2.2.toReal := by
  have key : ∀ x : Float32, (AC_WPNav_lib.MAX_float2 0.0 x).IsFinite →
      0 ≤ (AC_WPNav_lib.MAX_float2 0.0 x).toReal := by
    intro x hx
    simp only [AC_WPNav_lib.MAX_float2, Id.run, id_pure_eq] at hx ⊢
    by_cases h : (0.0 : Float32) > x
    · rw [ite_eq_left h, f32_toReal_0p0]
    · rw [ite_eq_right h] at hx ⊢
      have := (Float32.lt_iff_toReal_lt hx f32_isFinite_0p0).not.1 h
      rw [f32_toReal_0p0, not_lt] at this
      exact this
  have hform : (SCurve.get_jerk_accel_vel_pos_at_time s t J A V P).2.2.2 = 0.0 ∨
      ∃ x, (SCurve.get_jerk_accel_vel_pos_at_time s t J A V P).2.2.2 = AC_WPNav_lib.MAX_float2 0.0 x := by
    unfold SCurve.get_jerk_accel_vel_pos_at_time
    simp only [Id.run, id_pure_eq, id_bind_eq]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, rfl⟩
      · split
        · exact Or.inr ⟨_, rfl⟩
        · split <;> exact Or.inr ⟨_, rfl⟩
  rcases hform with h | ⟨x, h⟩
  · rw [h, f32_toReal_0p0]
  · rw [h] at hf ⊢; exact key x hf

/-- A point of `P3` from three reals. -/
def pt3 (a b c : ℝ) : P3 := !₂[a, b, c]

@[simp] theorem pt3_0 (a b c : ℝ) : pt3 a b c 0 = a := by simp [pt3]
@[simp] theorem pt3_1 (a b c : ℝ) : pt3 a b c 1 = b := by simp [pt3]
@[simp] theorem pt3_2 (a b c : ℝ) : pt3 a b c 2 = c := by simp [pt3]

/-- The navigator's `double` point as a point of `P3`. -/
def p3d (v : Vector3p.State) : P3 := pt3 v.x.toReal v.y.toReal v.z.toReal

/-- The navigator's `float` vector as a vector of `P3`. -/
def p3f (v : Vector3f.State) : P3 := pt3 v.x.toReal v.y.toReal v.z.toReal

/-- **Milestone (b), geometric part.** The straight-segment projection of `SCurve` puts the target
within `e + P/2¹⁷ + 2⁻⁴⁰` of the segment from the origin `pos` to `pos + seg_delta`, when the S-curve
position `P` is in `[0, ‖seg_delta‖ + e]` (and at most `10` m, as on this course). -/
theorem proj_straight_near (hL : LibmSpec) (s : SCurve.State) (A V P : Float32)
    (pos : Vector3p.State) (vel acc : Vector3f.State) (harc : s.is_arc_segment = false)
    (hdx : s.seg_delta.x.IsFinite) (hdy : s.seg_delta.y.IsFinite) (hdz : s.seg_delta.z.IsFinite)
    (hdx' : |s.seg_delta.x.toReal| ≤ 100) (hdy' : |s.seg_delta.y.toReal| ≤ 100)
    (hdz' : |s.seg_delta.z.toReal| ≤ 100)
    (hlen : (1 / 2 ^ 30 : ℝ) ≤ ‖p3f s.seg_delta‖) {e : ℝ} (he : 0 ≤ e)
    (hP : P.IsFinite) (hP0 : 0 ≤ P.toReal) (hPL : P.toReal ≤ ‖p3f s.seg_delta‖ + e)
    (hP10 : P.toReal ≤ 10)
    (hpx : pos.x.IsFinite) (hpy : pos.y.IsFinite) (hpz : pos.z.IsFinite)
    (hpx' : |pos.x.toReal| ≤ 100) (hpy' : |pos.y.toReal| ≤ 100) (hpz' : |pos.z.toReal| ≤ 100) :
    ∃ y ∈ segment ℝ (p3d pos) (p3d pos + p3f s.seg_delta),
      dist (p3d (SCurve.project_scurve_onto_track s A V P pos vel acc).2.1) y ≤
        e + P.toReal / 2 ^ 17 + 1 / 2 ^ 40 := by
  by_cases hz : is_zero_float s.seg_length = true
  · refine ⟨p3d pos, left_mem_segment _ _ _, ?_⟩
    simp only [SCurve.project_scurve_onto_track, Id.run, id_pure_eq, hz, ite_true]
    rw [dist_self]; positivity
  rw [Bool.not_eq_true] at hz
  simp only [SCurve.project_scurve_onto_track, Id.run, id_pure_eq, harc, hz, Bool.false_eq_true,
    ite_false, Vector3f.normalized, Vector3f.op_div, Vector3f.length, norm_float3, sq_float,
    Vector3f.init_float3, Vector3p.op_add_assign, Vector3p.op_mul_double, Vector3f.todouble,
    Vector3p.init_double3]
  set L := ‖p3f s.seg_delta‖ with hLd
  have hLe : L = Real.sqrt (s.seg_delta.x.toReal ^ 2 + s.seg_delta.y.toReal ^ 2 +
      s.seg_delta.z.toReal ^ 2) := by
    rw [hLd, norm_eq3]; simp [p3f]
  obtain ⟨fl, el⟩ := len_approx hdx hdy hdz hdx' hdy' hdz' (hLe ▸ hlen)
  rw [← hLe] at el
  have hℓ : A32 _ L (L / 2 ^ 21) := ⟨fl, by rw [div_eq_mul_one_div, mul_comm]; exact el⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hlen
  have cx : |s.seg_delta.x.toReal| ≤ L := by
    have := abs_coord_le_dist (p3f s.seg_delta) 0 0
    simp [p3f, dist_zero_right] at this; rw [hLd]; simpa [p3f] using this
  have cy : |s.seg_delta.y.toReal| ≤ L := by
    have := abs_coord_le_dist (p3f s.seg_delta) 0 1
    simp [p3f, dist_zero_right] at this; rw [hLd]; simpa [p3f] using this
  have cz : |s.seg_delta.z.toReal| ≤ L := by
    have := abs_coord_le_dist (p3f s.seg_delta) 0 2
    simp [p3f, dist_zero_right] at this; rw [hLd]; simpa [p3f] using this
  have ex := axis_proj hL hdx cx hℓ hlen hP hP0 hP10 hpx hpx'
  have ey := axis_proj hL hdy cy hℓ hlen hP hP0 hP10 hpy hpy'
  have ez := axis_proj hL hdz cz hℓ hlen hP hP0 hP10 hpz hpz'
  -- the exact point at `P` and its clamp onto the segment
  set Q := min P.toReal L with hQ
  have hQ0 : 0 ≤ Q := le_min hP0 hL0.le
  have hQL : Q ≤ L := min_le_right _ _
  refine ⟨p3d pos + (Q / L) • p3f s.seg_delta, ?_, ?_⟩
  · refine ⟨1 - Q / L, Q / L, by rw [sub_nonneg, div_le_one hL0]; exact hQL,
      div_nonneg hQ0 hL0.le, by ring, ?_⟩
    rw [smul_add, sub_smul, one_smul]; abel
  · set y' := p3d pos + (P.toReal / L) • p3f s.seg_delta
    have d2 : dist y' (p3d pos + (Q / L) • p3f s.seg_delta) ≤ e := by
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, ← hLd, Real.norm_eq_abs,
        ← sub_div, abs_div, abs_of_pos hL0, div_mul_cancel₀ _ hL0.ne']
      rw [abs_of_nonneg (by rw [hQ]; linarith [min_le_left P.toReal L])]
      rcases le_total P.toReal L with h | h
      · rw [hQ, min_eq_left h]; linarith
      · rw [hQ, min_eq_right h]; linarith
    have hle : 3 * (P.toReal / 2 ^ 19 + 1 / 2 ^ 42) ≤ P.toReal / 2 ^ 17 + 1 / 2 ^ 40 := by
      have : 0 ≤ P.toReal := hP0
      norm_num; linarith
    refine (dist_triangle _ y' _).trans
      ((add_le_add (b := 3 * (P.toReal / 2 ^ 19 + 1 / 2 ^ 42)) ?_ d2).trans (by linarith))
    refine (dist_le_sum_abs _ _).trans ?_
    simp only [y', p3d, p3f, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt3_0, pt3_1, pt3_2]
    rw [show P.toReal / L * s.seg_delta.x.toReal = s.seg_delta.x.toReal / L * P.toReal by ring,
      show P.toReal / L * s.seg_delta.y.toReal = s.seg_delta.y.toReal / L * P.toReal by ring,
      show P.toReal / L * s.seg_delta.z.toReal = s.seg_delta.z.toReal / L * P.toReal by ring]
    linarith

/-- The S-curve position that `move_from_pos_vel_accel s dt` projects. -/
def scurvePos (s : SCurve.State) (dt : Float32) : Float32 :=
  (SCurve.get_jerk_accel_vel_pos_at_time (SCurve.advance_time s dt) (SCurve.advance_time s dt).time
    0.0 0.0 0.0 0.0).2.2.2

/-- **Milestone (b): a straight leg.** `SCurve::move_from_pos_vel_accel` of a straight leg moves the
target from the leg's origin to within `e + P/2¹⁷ + 2⁻⁴⁰` of the leg, provided the S-curve's position
is finite and at most `‖seg_delta‖ + e` (the property of the segment table; `0 ≤ P` holds by the
clamp, `scurve_pos_nonneg`). -/
theorem move_from_near (hL : LibmSpec) (s : SCurve.State) (dt : Float32)
    (pos : Vector3p.State) (vel acc : Vector3f.State) (harc : s.is_arc_segment = false)
    (hdx : s.seg_delta.x.IsFinite) (hdy : s.seg_delta.y.IsFinite) (hdz : s.seg_delta.z.IsFinite)
    (hdx' : |s.seg_delta.x.toReal| ≤ 100) (hdy' : |s.seg_delta.y.toReal| ≤ 100)
    (hdz' : |s.seg_delta.z.toReal| ≤ 100)
    (hlen : (1 / 2 ^ 30 : ℝ) ≤ ‖p3f s.seg_delta‖) {e : ℝ} (he : 0 ≤ e)
    (hP : (scurvePos s dt).IsFinite) (hPL : (scurvePos s dt).toReal ≤ ‖p3f s.seg_delta‖ + e)
    (hP10 : (scurvePos s dt).toReal ≤ 10)
    (hpx : pos.x.IsFinite) (hpy : pos.y.IsFinite) (hpz : pos.z.IsFinite)
    (hpx' : |pos.x.toReal| ≤ 100) (hpy' : |pos.y.toReal| ≤ 100) (hpz' : |pos.z.toReal| ≤ 100) :
    ∃ y ∈ segment ℝ (p3d pos) (p3d pos + p3f s.seg_delta),
      dist (p3d (SCurve.move_from_pos_vel_accel s dt pos vel acc).2.1) y ≤
        e + (scurvePos s dt).toReal / 2 ^ 17 + 1 / 2 ^ 40 := by
  have hP0 := scurve_pos_nonneg _ _ _ _ _ _ hP
  have hadv : (SCurve.advance_time s dt).seg_delta = s.seg_delta := by
    simp [SCurve.advance_time, Id.run]
  have harc' : (SCurve.advance_time s dt).is_arc_segment = false := by
    simp [SCurve.advance_time, Id.run, harc]
  have h := proj_straight_near hL (SCurve.advance_time s dt)
    (SCurve.get_jerk_accel_vel_pos_at_time (SCurve.advance_time s dt) (SCurve.advance_time s dt).time
      0.0 0.0 0.0 0.0).2.1
    (SCurve.get_jerk_accel_vel_pos_at_time (SCurve.advance_time s dt) (SCurve.advance_time s dt).time
      0.0 0.0 0.0 0.0).2.2.1 (scurvePos s dt) pos vel acc harc'
    (by rw [hadv]; exact hdx) (by rw [hadv]; exact hdy) (by rw [hadv]; exact hdz)
    (by rw [hadv]; exact hdx') (by rw [hadv]; exact hdy') (by rw [hadv]; exact hdz')
    (by rw [hadv]; exact hlen) he hP hP0 (by rw [hadv]; exact hPL) hP10 hpx hpy hpz hpx' hpy' hpz'
  rw [hadv] at h
  simpa [SCurve.move_from_pos_vel_accel, Id.run, scurvePos] using h

end

end Contracts.Mission
