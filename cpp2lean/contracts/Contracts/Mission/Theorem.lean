import Contracts.Mission.Sub

/-!
# The mission contract

`mission_contract`: the closed loop of the translated controller and the sampled plant implements
`⟨Atakeoff, lang_t 0 ψmission⟩` for the mission world, under accurate sensing ports, the C library
hypotheses and the escape of the climb (`ClimbEscape`, validated, not proved).

The assembly `mission_of_sub` derives it from the two open sub-contracts, taken as hypotheses, and
is proved without `sorry`:

1. `chain` composes `track_contract` (on `Mloop`) with `nav_contract` read on the loop: the loop's
   samples meet the navigator's assumption (`navA_of_loop`, from the plant's sensing ports, the
   takeoff assumption, and the tracking guarantee);
2. `refines_sound` weakens the joint guarantee to the mission (`mission_of_guarantees`): safety from
   the target's corridor or column (`safe_of_parts`), arrival in order from the target's arrival
   through the transfer property (`arrive_lemma`), and the hold likewise.

`mission_nonvacuous`: the loop has a behavior from the takeoff assumption, for every world.
-/

namespace Contracts.Mission

open Contracts Contracts.STL Contracts.Lift

noncomputable section

/-! ## Contract algebra -/

/-- A contract refines the contract with the same assumption and a guarantee that contains its
guarantee on the assumption. -/
theorem refines_of_inter_subset {B : Type} {A G G' : Set B} (h : A ∩ G ⊆ G') :
    (⟨A, G⟩ : Contract B) ⪯ ⟨A, G'⟩ := by
  refine ⟨subset_rfl, ?_⟩
  rintro b (hG | hA)
  · by_cases hb : b ∈ A
    · exact Or.inl (h ⟨hb, hG⟩)
    · exact Or.inr hb
  · exact Or.inr hA

/-! ## Geometry of the climb out of the box -/

/-- The distance from the takeoff column to the polyline is below `0.2136` m (the column's corner,
`√(2 · 0.151² + 0.002²) = 0.21356`, against the first, vertical leg). -/
theorem polyDist_of_inColumn {q : P3} (h : inColumn q) : polyDist q ≤ 0.2136 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [colNE, colDownLo, colDownHi] at h0 h1 h2 h3
  have hm0 : min (q 2) 0 ≤ 0 := min_le_right _ _
  have hm1 : -0.8 ≤ min (q 2) 0 := le_min h2 (by norm_num)
  have hc : (!₂[0, 0, min (q 2) 0] : P3) ∈ polySet := by
    refine Set.mem_iUnion.2 ⟨0, 1 + min (q 2) 0 / 0.8, -(min (q 2) 0 / 0.8), ?_, ?_, by ring, ?_⟩
    · have : -1 ≤ min (q 2) 0 / 0.8 := by rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    · have : min (q 2) 0 / 0.8 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm0 (by norm_num)
      linarith
    · ext i
      fin_cases i <;> simp [pathPt]
      ring
  refine (Metric.infDist_le_dist_of_mem hc).trans ?_
  rw [dist_eq3, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have e0 : q 0 ^ 2 ≤ 0.151 ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : q 1 ^ 2 ≤ 0.151 ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : (q 2 - min (q 2) 0) ^ 2 ≤ 0.002 ^ 2 := by
    rcases le_total (q 2) 0 with hq | hq
    · rw [min_eq_left hq]; norm_num
    · rw [min_eq_right hq]; nlinarith
  simp
  nlinarith

/-- **Safety at a tick** from the parts of the sub-contracts: the target within `ρ` of the polyline
or in the column, the error at most `δ`, and at most `δ₀` during the climb out of the box. -/
theorem safe_of_parts {y : X} (hnav : polyDist (posTarget y) ≤ ρ ∨ inColumn (posTarget y))
    (he : err y ≤ δ) (hto : inColumn (posTarget y) ∧ ¬ polyDist (posTarget y) ≤ ρ → err y ≤ δ₀) :
    inSafe (pos y) ∧ alt y ≤ ceiling := by
  have hs : inSafe (pos y) := by
    left
    have hL := polyDist_le (pos y) (posTarget y)
    rw [← err] at hL
    by_cases hρ : polyDist (posTarget y) ≤ ρ
    · linarith [hρδ]
    · have hc : inColumn (posTarget y) := hnav.resolve_left hρ
      have := polyDist_of_inColumn hc
      have := hto ⟨hc, hρ⟩
      norm_num [corridor, δ₀] at *
      linarith
  refine ⟨hs, ?_⟩
  have := down_of_inSafe hs
  simp only [pos, alt] at this ⊢
  simp at this
  linarith

/-! ## The mission from the guarantees -/

@[simp] theorem sat_nearPolyT {ρ' : ℝ} {x : ℕ → X} {t : ℕ} :
    sat x t (nearPolyT ρ') ↔ polyDist (posTarget (x t)) ≤ ρ' := by simp [nearPolyT]

@[simp] theorem sat_inColumnT {x : ℕ → X} {t : ℕ} :
    sat x t inColumnT ↔ inColumn (posTarget (x t)) := by simp [inColumnT]

/-- The transfer property at a tick, for every waypoint. -/
theorem prox_of_sat {x : ℕ → X} {τ : ℕ} (h : sat x τ proxAllF) {w : P3} (hw : w ∈ List.ofFn wp)
    (hT : sat x τ (nearT w (rPass w))) : sat x τ (near w rWp) := by
  rw [proxAllF, sat_allF] at h
  exact (sat_imp.1 (h (proxF w) (List.mem_map_of_mem hw))) hT

/-- **The mission follows from the guarantees** of `track_contract` and `nav_contract`. -/
theorem mission_of_guarantees {x : ℕ → X} (hT : x ∈ lang_t 0 ψtrack) (hN : x ∈ lang_t 0 ψnavG) :
    x ∈ lang_t 0 ψmission := by
  simp only [mem_lang_t, ψtrack, ψnavG, ψmission, sat_and, sat_always, sat_eventually, add_zero,
    zero_add] at hT hN ⊢
  obtain ⟨hA, hR, hH⟩ := hT
  have hHor := horizonTicks_eq
  have hprox : ∀ τ ≤ horizonTicks, ∀ w ∈ List.ofFn wp,
      sat x τ (nearT w (rPass w)) → sat x τ (near w rWp) :=
    fun τ hτ w hw => prox_of_sat (hA τ (Nat.zero_le _) hτ).2.2.2.1 hw
  refine ⟨fun τ _ hτ => ?_, ?_, ?_⟩
  · -- safety
    obtain ⟨he, -, hto, -, -⟩ := hA τ (Nat.zero_le _) hτ
    have hn := hN τ (Nat.zero_le _) hτ
    simp only [sat_or, sat_nearPolyT, sat_inColumnT] at hn
    simp only [takeoffF, sat_imp, sat_and, sat_not, sat_inColumnT, sat_nearPolyT, sat_errLE] at hto
    exact sat_safeF.2 (safe_of_parts hn (sat_errLE.1 he) hto)
  · -- the waypoints in order: the vehicle at `w0`, then the transfer from the target's arrivals
    obtain ⟨τ, -, hτ, h0, hR'⟩ := hR
    have hspan : span legs.tail = 9600 := by decide
    refine ⟨τ, Nat.zero_le _, hτ, h0, ?_⟩
    refine arrive_lemma (L' := legs.tail) x horizonTicks (fun σ hσ w T hwT hw => ?_) legs.tail τ
      (fun _ hp => hp) (by rw [hspan, horizonTicks]; omega) hR'
    refine hprox σ hσ w ?_ hw
    rw [← legs_waypoints]
    exact List.mem_map_of_mem (f := Prod.fst) (List.mem_of_mem_tail hwT)
  · -- the hold
    obtain ⟨τ, -, hτ, hτH⟩ := hH
    refine ⟨τ, Nat.zero_le _, hτ, fun σ h1 h2 => hprox σ (by omega) w7 ?_ (hτH σ h1 h2)⟩
    exact List.mem_ofFn.2 ⟨7, rfl⟩

/-! ## The sensing ports -/

theorem eta32_le : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 10 :=
  (zpow_le_zpow_right₀ one_le_two (by norm_num : (-150 : ℤ) ≤ -40)).trans (by norm_num)

theorem eta64_le : (2 : ℝ) ^ (-1075 : ℤ) ≤ 1 / 10 ^ 10 :=
  (zpow_le_zpow_right₀ one_le_two (by norm_num : (-1075 : ℤ) ≤ -40)).trans (by norm_num)

/-- The `float` port on `|r| ≤ B ≤ 100`: finite, within `B/10⁷ + 10⁻¹⁰` of `r`. -/
theorem port32 {s32 : ℝ → Float32} {sP : ℝ → Float} (hS : Plant.CopterSense s32 sP) {r B : ℝ}
    (hr : |r| ≤ B) (hB : B ≤ 100) :
    (s32 r).IsFinite ∧ |(s32 r).toReal - r| ≤ B / 10 ^ 7 + 1 / 10 ^ 10 := by
  obtain ⟨hf, he⟩ := hS.f32.err r (hr.trans hB)
  refine ⟨hf, he.trans ?_⟩
  have h24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 / 10 ^ 7 := by norm_num
  have h0 : (0 : ℝ) ≤ 2 ^ (-24 : ℤ) := by positivity
  nlinarith [eta32_le, abs_nonneg r, mul_le_mul h24 hr (abs_nonneg r) (by norm_num)]

/-- The `double` port on `|r| ≤ B ≤ 10⁴`: finite, within `B/10¹⁰ + 10⁻¹⁰` of `r`. -/
theorem portP {s32 : ℝ → Float32} {sP : ℝ → Float} (hS : Plant.CopterSense s32 sP) {r B : ℝ}
    (hr : |r| ≤ B) (hB : B ≤ 10000) :
    (sP r).IsFinite ∧ |(sP r).toReal - r| ≤ B / 10 ^ 10 + 1 / 10 ^ 10 := by
  obtain ⟨hf, he⟩ := hS.pos.err r (hr.trans hB)
  refine ⟨hf, he.trans ?_⟩
  have h53 : (2 : ℝ) ^ (-53 : ℤ) ≤ 1 / 10 ^ 10 := by norm_num
  nlinarith [eta64_le, abs_nonneg r, mul_le_mul h53 hr (abs_nonneg r) (by norm_num)]

theorem abs_le_of_near {a r e B : ℝ} (hr : |r| ≤ B) (h : |a - r| ≤ e) : |a| ≤ B + e := by
  have := abs_add_le (a - r) r
  simp only [sub_add_cancel] at this
  linarith

theorem f32Bd_of {s32 : ℝ → Float32} {sP : ℝ → Float} (hS : Plant.CopterSense s32 sP) {r B B' : ℝ}
    (hr : |r| ≤ B) (hB : B ≤ 100) (hB' : B + B / 10 ^ 7 + 1 / 10 ^ 10 ≤ B') : F32Bd (s32 r) B' := by
  obtain ⟨hf, he⟩ := port32 hS hr hB
  exact ⟨hf, (abs_le_of_near hr he).trans (by linarith)⟩

theorem f64Bd_of {s32 : ℝ → Float32} {sP : ℝ → Float} (hS : Plant.CopterSense s32 sP) {r B B' : ℝ}
    (hr : |r| ≤ B) (hB : B ≤ 10000) (hB' : B + B / 10 ^ 10 + 1 / 10 ^ 10 ≤ B') :
    F64Bd (sP r) B' := by
  obtain ⟨hf, he⟩ := portP hS hr hB
  exact ⟨hf, (abs_le_of_near hr he).trans (by linarith)⟩

/-! ## The plant's specific force -/

theorem accel_bounds (u : Fin 4 → ℝ) : 0 ≤ Plant.accel u ∧ Plant.accel u ≤ Plant.amax := by
  have hc : ∀ i, 0 ≤ Plant.clip01 (u i) ∧ Plant.clip01 (u i) ≤ 1 :=
    fun i => ⟨Plant.clip01_nonneg _, Plant.clip01_le_one _⟩
  have hf := Plant.fmax_pos
  have hm := Plant.mass_pos
  have hT0 : 0 ≤ Plant.thrust u := by
    simp only [Plant.thrust, Plant.force]
    nlinarith [hc 0, hc 1, hc 2, hc 3]
  have hT1 : Plant.thrust u ≤ 4 * Plant.fmax := by
    simp only [Plant.thrust, Plant.force]
    nlinarith [hc 0, hc 1, hc 2, hc 3]
  refine ⟨div_nonneg hT0 hm.le, ?_⟩
  rw [Plant.accel, ← Plant.four_fmax_div_mass]
  exact div_le_div_of_nonneg_right hT1 hm.le

theorem amax_le : Plant.amax ≤ 22.07 := by
  norm_num [Plant.amax, Plant.thrust2weight, Plant.grav]

/-- On the unit sphere every component of the specific force is at most `amax`. -/
theorem specForce_bound {q : Plant.Quat} (hq : q.normSq = 1) (u : Fin 4 → ℝ) :
    |(Plant.specForce q u).x| ≤ Plant.amax ∧ |(Plant.specForce q u).y| ≤ Plant.amax ∧
      |(Plant.specForce q u).z| ≤ Plant.amax := by
  obtain ⟨ha0, ha1⟩ := accel_bounds u
  simp only [Plant.Quat.normSq] at hq
  have dx : |2 * (q.q2 * q.q4 + q.q1 * q.q3)| ≤ 1 := abs_le.2
    ⟨by nlinarith [sq_nonneg (q.q2 + q.q4), sq_nonneg (q.q1 + q.q3)],
     by nlinarith [sq_nonneg (q.q2 - q.q4), sq_nonneg (q.q1 - q.q3)]⟩
  have dy : |2 * (q.q3 * q.q4 - q.q1 * q.q2)| ≤ 1 := abs_le.2
    ⟨by nlinarith [sq_nonneg (q.q3 + q.q4), sq_nonneg (q.q1 - q.q2)],
     by nlinarith [sq_nonneg (q.q3 - q.q4), sq_nonneg (q.q1 + q.q2)]⟩
  have dz : |q.q1 * q.q1 - q.q2 * q.q2 - q.q3 * q.q3 + q.q4 * q.q4| ≤ 1 := abs_le.2
    ⟨by nlinarith [sq_nonneg q.q1, sq_nonneg q.q4], by nlinarith [sq_nonneg q.q2, sq_nonneg q.q3]⟩
  have key : ∀ d : ℝ, |d| ≤ 1 → |-(Plant.accel u) * d| ≤ Plant.amax := fun d hd => by
    rw [abs_mul, abs_neg, abs_of_nonneg ha0]
    nlinarith [abs_nonneg d]
  exact ⟨key _ dx, key _ dy, key _ dz⟩

/-- The tick-0 specific force of the takeoff state is `(0, 0, -g)`, whatever the heading. -/
theorem tickSpecForce_startP (p : P3) (ψ : ℝ) :
    Plant.tickSpecForce (startP p ψ) = ⟨0, 0, -Plant.grav⟩ := by
  have hA := Plant.accel_hover (u := hoverHeld) (fun _ => rfl)
  have hcs : Real.cos (ψ / 2) * Real.cos (ψ / 2) + Real.sin (ψ / 2) * Real.sin (ψ / 2) = 1 := by
    nlinarith [Real.cos_sq_add_sin_sq (ψ / 2)]
  simp only [Plant.tickSpecForce, Plant.specForce, Plant.downAxis, startP, startState, yawQuat,
    Plant.State.ofX_toX, hA]
  simp [hcs]

/-- The heading quaternion is a unit quaternion. -/
theorem yawQuat_normSq (ψ : ℝ) :
    Real.cos (ψ / 2) ^ 2 + Real.sin (ψ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (ψ / 2)

/-! ## The loop meets the navigator's assumption -/

/-- **The bridge**: on a behavior of the plant from the takeoff assumption that meets the tracking
guarantee, the samples meet the navigator's assumption. -/
theorem navA_of_loop {s32 : ℝ → Float32} {sP : ℝ → Float} (hS : Plant.CopterSense s32 sP)
    {x : ℕ → X} (hP : x ∈ Mplant s32 sP) (hA : x ∈ Atakeoff) (hG : x ∈ lang_t 0 ψtrack) :
    x ∈ lang_t 0 ψnavA := by
  obtain ⟨p, ψ, hp, h0⟩ := hA
  have hsmp : ∀ t, (x t).smp = toVSample (Plant.sample s32 sP (x t).phys) :=
    fun t => ((mem_Mplant.1 hP) t).2
  -- the attitude stays on the unit sphere
  have hq : ∀ t, Plant.qnormSq (x t).phys.x = 1 := by
    obtain ⟨y, hy, hxy⟩ := mem_Mplant_iff_plant.1 hP
    intro t
    rw [← (hxy t).1, Plant.Mplant_qnormSq hy t, (hxy 0).1, h0]
    simp [Plant.qnormSq, startP, startState, yawQuat, Plant.State.toX]
  simp only [mem_lang_t, ψtrack, sat_and, sat_always, add_zero, envF, sat_propF, physEnv, PBd,
    Plant.VBd, Plant.WBd] at hG
  obtain ⟨hGA, -⟩ := hG
  simp only [mem_lang_t, ψnavA, sat_and, sat_always, sat_propF, sat_atom, add_zero, sub_nonneg]
  refine ⟨?_, fun τ _ hτ => ?_⟩
  · -- the first sample
    obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩ := hp
    simp only [boxNE, boxDownLo, boxDownHi] at hp0 hp1 hp2 hp3 hp4 hp5
    have a0 : |p 0| ≤ 0.15 := abs_le.2 ⟨hp0, hp1⟩
    have a1 : |p 1| ≤ 0.15 := abs_le.2 ⟨hp2, hp3⟩
    have a2 : |p 2| ≤ 0.3 := abs_le.2 ⟨hp4, by linarith⟩
    have e0 := (portP hS a0 (by norm_num)).2
    have e1 := (portP hS a1 (by norm_num)).2
    have e2 := (portP hS a2 (by norm_num)).2
    have eg := (port32 hS (r := -Plant.grav) (B := 9.80665)
      (by norm_num [Plant.grav]) (by norm_num)).2
    have hz := hS.f32.zero
    have hc1 : |Real.cos (ψ / 2)| ≤ 1 := Real.abs_cos_le_one _
    have hs1 : |Real.sin (ψ / 2)| ≤ 1 := Real.abs_sin_le_one _
    have ec := (port32 hS hc1 (by norm_num)).2
    have es := (port32 hS hs1 (by norm_num)).2
    have hcs := yawQuat_normSq ψ
    rw [hsmp 0, h0]
    simp only [smpStart, toVSample, Plant.sample, tickSpecForce_startP]
    simp only [startP, startState, yawQuat, Plant.State.ofX_toX, hz, colNE, boxDownHi,
      boxDownLo]
    refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, ?_, trivial, trivial, ?_⟩
    · have := abs_le_of_near a0 e0; norm_num at this ⊢; linarith
    · have := abs_le_of_near a1 e1; norm_num at this ⊢; linarith
    · have := (abs_le.1 e2).1; norm_num at this ⊢; linarith
    · have := (abs_le.1 e2).2; norm_num at this ⊢; linarith
    · -- `q1² + q4²` of the sensed heading quaternion
      set c := Real.cos (ψ / 2)
      set sn := Real.sin (ψ / 2)
      set a := (s32 c).toReal
      set b := (s32 sn).toReal
      obtain ⟨ha1, ha2⟩ := abs_le.1 ec
      obtain ⟨hb1, hb2⟩ := abs_le.1 es
      obtain ⟨hc1', hc2'⟩ := abs_le.1 hc1
      obtain ⟨hs1', hs2'⟩ := abs_le.1 hs1
      norm_num at ha1 ha2 hb1 hb2
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a - c), sq_nonneg (b - sn)]
    · rw [show (s32 (-Plant.grav)).toReal + Plant.grav = (s32 (-Plant.grav)).toReal - -Plant.grav
        by ring]
      refine eg.trans ?_
      norm_num
  · -- every sample of the horizon
    obtain ⟨he, ⟨⟨P0, P1, P2⟩, ⟨V0, V1, V2⟩, ⟨W0, W1, W2⟩⟩, -, -, hrest⟩ := hGA τ (Nat.zero_le _) hτ
    have hqτ := hq τ
    simp only [Plant.qnormSq] at hqτ
    have s6 := sq_nonneg ((x τ).phys.x 6)
    have s7 := sq_nonneg ((x τ).phys.x 7)
    have s8 := sq_nonneg ((x τ).phys.x 8)
    have s9 := sq_nonneg ((x τ).phys.x 9)
    have Q6 : |(x τ).phys.x 6| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have Q7 : |(x τ).phys.x 7| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have Q8 : |(x τ).phys.x 8| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have Q9 : |(x τ).phys.x 9| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have hqn : (Plant.State.ofX (x τ).phys.x).q.normSq = 1 := by
      simpa [Plant.Quat.normSq, Plant.State.ofX] using hqτ
    obtain ⟨A0, A1, A2⟩ := specForce_bound hqn (x τ).phys.held
    have am := amax_le
    refine ⟨?_, ?_, ?_, hrest⟩
    · rw [hsmp τ]; rfl
    · rw [hsmp τ]
      simp only [smpEnv, toVSample, Plant.sample, Plant.tickSpecForce]
      refine ⟨⟨f64Bd_of hS P0 (by norm_num) (by norm_num), f64Bd_of hS P1 (by norm_num) (by norm_num),
          f64Bd_of hS P2 (by norm_num) (by norm_num)⟩,
        ⟨f32Bd_of hS V0 (by norm_num) (by norm_num), f32Bd_of hS V1 (by norm_num) (by norm_num),
          f32Bd_of hS V2 (by norm_num) (by norm_num)⟩,
        ⟨f32Bd_of hS (A0.trans am) (by norm_num) (by norm_num),
          f32Bd_of hS (A1.trans am) (by norm_num) (by norm_num),
          f32Bd_of hS (A2.trans am) (by norm_num) (by norm_num)⟩,
        ⟨f32Bd_of hS Q6 (by norm_num) (by norm_num), f32Bd_of hS Q7 (by norm_num) (by norm_num),
          f32Bd_of hS Q8 (by norm_num) (by norm_num), f32Bd_of hS Q9 (by norm_num) (by norm_num)⟩,
        ⟨f32Bd_of hS W0 (by norm_num) (by norm_num), f32Bd_of hS W1 (by norm_num) (by norm_num),
          f32Bd_of hS W2 (by norm_num) (by norm_num)⟩⟩
    · -- the sampled tracking error
      have e0 := (portP hS P0 (by norm_num)).2
      have e1 := (portP hS P1 (by norm_num)).2
      have e2 := (portP hS P2 (by norm_num)).2
      have hd := dist_le_sum_abs (smpPos (x τ)) (pos (x τ))
      have ht := dist_triangle (smpPos (x τ)) (pos (x τ)) (posTarget (x τ))
      have c0 : smpPos (x τ) 0 = (sP ((x τ).phys.x 0)).toReal := by
        simp [smpPos, hsmp τ, toVSample, Plant.sample, Plant.State.ofX]
      have c1 : smpPos (x τ) 1 = (sP ((x τ).phys.x 1)).toReal := by
        simp [smpPos, hsmp τ, toVSample, Plant.sample, Plant.State.ofX]
      have c2 : smpPos (x τ) 2 = (sP ((x τ).phys.x 2)).toReal := by
        simp [smpPos, hsmp τ, toVSample, Plant.sample, Plant.State.ofX]
      have d0 : pos (x τ) 0 = (x τ).phys.x 0 := by simp [pos]
      have d1 : pos (x τ) 1 = (x τ).phys.x 1 := by simp [pos]
      have d2 : pos (x τ) 2 = (x τ).phys.x 2 := by simp [pos]
      rw [c0, c1, c2, d0, d1, d2] at hd
      have he' := sat_errLE.1 he
      rw [err] at he'
      rw [smpErr]
      norm_num [δ, δs] at he' e0 e1 e2 ⊢
      linarith

/-! ## Assembly -/

/-- **The assembly**, with the two open sub-contracts as hypotheses: the closed loop implements the
mission contract. Proved by `chain` (tracking, then navigation read on the loop through the bridge
`navA_of_loop`) and `refines_sound` (`mission_of_guarantees`). -/
theorem mission_of_sub (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hS : Plant.CopterSense sense32 senseP)
    (htrack : Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩)
    (hnav : Mctrl w₀ ⊨ ⟨lang_t 0 ψnavA, lang_t 0 ψnavG⟩) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψmission⟩ := by
  have h₂ : Mloop sense32 senseP w₀ ⊨
      ⟨Atakeoff ∩ lang_t 0 ψtrack, lang_t 0 ψtrack ∩ lang_t 0 ψnavG⟩ := by
    rintro x ⟨hx, hA, hG⟩
    exact ⟨hG, hnav ⟨hx.2, navA_of_loop hS hx.1 hA hG⟩⟩
  have h := chain htrack h₂
  rw [Set.inter_self] at h
  exact refines_sound
    (refines_of_inter_subset (A := Atakeoff) (G := lang_t 0 ψtrack ∩ lang_t 0 ψnavG)
      (G' := lang_t 0 ψmission) fun _ hx => mission_of_guarantees hx.2.1 hx.2.2) h

/-- **The mission contract.** For the vehicle built from the course parameter files, with sensing
ports at round-to-nearest accuracy and the C library hypotheses, the closed loop of the translated
controller and the sampled Crazyflie plant implements: from a start at rest in the takeoff box, over
the 30 s horizon the vehicle stays in the corridor ∪ box below the ceiling, reaches `w0 … w7` in
order each within `0.1` m and within its allowance, and holds within `0.1` m of `w7` for 3 s within
the 27 s total. The hypothesis `hE` (`ClimbEscape`, the escape of the climb by tick 350) is
validated on the Monte Carlo runs and not proved (MISSION.md). -/
theorem mission_contract (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hM : MissionWorld w₀) (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hE : ClimbEscape sense32 senseP w₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψmission⟩ :=
  mission_of_sub sense32 senseP w₀ hS (track_contract sense32 senseP w₀ hM hS hL hE)
    (nav_contract w₀ hM hL)

/-! ## Nonvacuity -/

/-- One tick of plant and controller together: the plant's sample, the controller's step on it,
the plant's step under the actuators. -/
def jointStep (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (st : Plant.PState × Option Vehicle.World) (_ : Unit) :
    (Plant.PState × Option Vehicle.World) × X :=
  let smp := toVSample (Plant.sample sense32 senseP st.1)
  let r := tickT w₀ st.2 smp
  ((Plant.next st.1 r.2.act, r.1), ⟨st.1, smp, r.2⟩)

/-- The behavior of the loop from the takeoff point at the origin: the joint step iterated
(`runState`). -/
def witness (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) : ℕ → X :=
  fun t => (jointStep sense32 senseP w₀
    (runState (jointStep sense32 senseP w₀) (startP 0 0, none) (fun _ => ()) t) ()).2

/-- **Nonvacuity**: for every world and every pair of ports, the loop has a behavior from the
takeoff assumption. -/
theorem mission_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) :
    (Mloop sense32 senseP w₀ ∩ Atakeoff).Nonempty := by
  refine ⟨witness sense32 senseP w₀, ⟨mem_Mplant.2 fun t => ⟨rfl, rfl⟩,
    ⟨fun t => (runState (jointStep sense32 senseP w₀) (startP 0 0, none) (fun _ => ()) t).2, rfl,
      fun t => rfl⟩⟩, 0, 0, ?_, rfl⟩
  norm_num [inBox, boxNE, boxDownLo, boxDownHi]

end

end Contracts.Mission
