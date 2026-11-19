import Contracts.Track.PacingFilter

/-!
# Milestone M8, lemma P-3: arrival within the allowances, and the hold

The target is the S-curve path evaluated at the **S-curve time** `q t` (in ticks): the sum of the
time steps `_track_dt_scalar · vel_dt_scalar · dt` that `advance_wp_target_along_track` passes to
`SCurve::advance_target_along_track` up to tick `t`. With `vel_dt_scalar = 1` each step is the
filtered scaler `s t` up to the rounding `ε_q` (`prog_step`).

`Pace s r q α ε_f ε_q` collects the code facts: the filter run of `PacingFilter.lean`, the raw
scaler in `[0, 1]`, the filter in `[−c, 1 + c]` (`c = ε_f/α`), and the progress of `q`.

The S-curve library (milestone M7) and the tracking certificates enter through two kinds of
hypotheses on S-curve-time intervals:

* *windows*: while `q t ∈ [a, a + w)` the arrival atom of the leg holds at tick `t` (for `w1 … w7`:
  the target within the waypoint's radius; for `w0`: the vehicle within `r`, from the climb
  certificate);
* *phases*: while `q t ∈ [a_prev − 1, a)` the raw scaler of the next tick is at least `ρ`
  (`rawScaler_ge` with the S-curve's speed profile `|v_T| ≥ v_min` on the phase and the tracking
  bounds; `rho_of_P1`).

The results:

* `leg_arrive`: from a tick with `q ∈ [A, B)`, the first tick with `q ≥ B` comes within `T` ticks
  when `ρ T − (1/α − 1)(D₀ + c) − T (c + ε_q) ≥ B − A`, and it lies in `[B, B + 1 + c + ε_q)`;
* `leg0_arrive`: the first leg, from the escape of the leg-start phase (closed-loop hypothesis: by
  tick `W₀` the S-curve time has reached `τ_v`, where the speed profile passes `v_min`), with the
  deficit at arrival decayed to `Δ`;
* `chain_reach`: legs `1 … 7` by induction, keeping the deficit below `Δ`;
* **`pacing_reach` (P-3)**: the nested reach formula, each atom within its allowance;
* `hold_w7`: after arrival at `w7` the target stays within the radius until completion (S-curve
  end, M7) and after it (the loiter destination, `loiter_dest_bound` of the navigator);
* `pacing_course`: the course instance, with all numeric conditions checked.
-/

namespace Contracts.Track.Pacing

open Contracts Contracts.STL Contracts.Mission Float.Model UnpackedFloat AC_PosControl_lib

noncomputable section

/-! ## The code facts -/

/-- The pacing facts of a run: `s` the filtered scaler after tick `t`, `r` the raw scaler of tick
`t`, `q` the S-curve time after tick `t` (ticks). -/
structure Pace (s r q : ℕ → ℝ) (α εf εq : ℝ) : Prop where
  hα0 : 0 < α
  hα1 : α ≤ 1
  hεf : 0 ≤ εf
  hεq : 0 ≤ εq
  filt : FilterRun s r α εf
  r01 : ∀ t, 0 ≤ r t ∧ r t ≤ 1
  sb : ∀ t, -(εf / α) ≤ s t ∧ s t ≤ 1 + εf / α
  prog : ∀ t, |q (t + 1) - q t - s (t + 1)| ≤ εq
  prog0 : |q 0 - s 0| ≤ εq

variable {s r q : ℕ → ℝ} {α εf εq : ℝ}

theorem Pace.c_nonneg (P : Pace s r q α εf εq) : 0 ≤ εf / α := div_nonneg P.hεf P.hα0.le

/-- One tick advances the S-curve time by at most `1 + c + ε_q`. -/
theorem Pace.step_up (P : Pace s r q α εf εq) (t : ℕ) :
    q (t + 1) ≤ q t + (1 + εf / α + εq) := by
  have h := (abs_le.1 (P.prog t)).2; have := (P.sb (t + 1)).2; linarith

/-- The S-curve time decreases by at most `c + ε_q` per tick. -/
theorem Pace.leak (P : Pace s r q α εf εq) (t : ℕ) : ∀ k : ℕ,
    q t - k * (εf / α + εq) ≤ q (t + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := (abs_le.1 (P.prog (t + k))).1
    have := (P.sb (t + k + 1)).1
    rw [show t + (k + 1) = t + k + 1 by ring]; push_cast; linarith

/-- The progress over `n` ticks: `n` minus the summed deficit, minus the rounding. -/
theorem Pace.progress (P : Pace s r q α εf εq) (t0 : ℕ) : ∀ n : ℕ,
    q t0 + n - ∑ k ∈ Finset.range n, (1 - s (t0 + k + 1)) - n * εq ≤ q (t0 + n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := (abs_le.1 (P.prog (t0 + n))).1
    rw [show t0 + (n + 1) = t0 + n + 1 by ring]; push_cast; linarith

/-- The deficit stays below a level `Δ ≥ (1 − ρ) + c` while the raw scaler is at least `ρ`. -/
theorem Pace.deficit_inv (P : Pace s r q α εf εq) {ρ Δ : ℝ} (hΔ : (1 - ρ) + εf / α ≤ Δ) (t : ℕ)
    (hD : 1 - s t ≤ Δ) (hr : ρ ≤ r (t + 1)) : 1 - s (t + 1) ≤ Δ := by
  have h := deficit_step P.filt t
  have hc : α * (εf / α) = εf := by field_simp [P.hα0.ne']
  have h1 : 0 ≤ 1 - α := by linarith [P.hα1]
  nlinarith [mul_le_mul_of_nonneg_left hD h1, P.hα0]

/-! ## One leg -/

/-- **Arrival on one leg.** From a tick `t₀` with `A ≤ q t₀ < B` and deficit at most `D₀`, if the
raw scaler is at least `ρ` whenever `q ∈ [A − 1, B)` (before tick `N`), then the S-curve time
reaches `B` within `T` ticks, at a first tick `t₀ + k` with `q ∈ [B, B + 1 + c + ε_q)`, provided
`ρ T − (1/α − 1)(D₀ + c) − T (c/1 + ε_q) ≥ B − A` (with `ε_f/α` per tick) and `T (c + ε_q) ≤ 1/2`. -/
theorem leg_arrive (P : Pace s r q α εf εq) {A B ρ D0 : ℝ} {t0 T N : ℕ}
    (hA : A ≤ q t0) (hB : q t0 < B) (hD : 1 - s t0 ≤ D0) (hN : t0 + T ≤ N)
    (hphase : ∀ t < N, A - 1 ≤ q t → q t < B → ρ ≤ r (t + 1))
    (hnum : B - A ≤ ρ * T - (1 - α) / α * (D0 + εf / α) - T * (εf / α + εq))
    (hleak : T * (εf / α + εq) ≤ 1 / 2) :
    ∃ k, 0 < k ∧ k ≤ T ∧ B ≤ q (t0 + k) ∧ q (t0 + k) < B + (1 + εf / α + εq) ∧
      ∀ j < k, q (t0 + j) < B := by
  by_cases hex : ∃ j, j ≤ T ∧ B ≤ q (t0 + j)
  · classical
    obtain ⟨k, hk, hmin⟩ : ∃ k, (k ≤ T ∧ B ≤ q (t0 + k)) ∧ ∀ j < k, ¬ (j ≤ T ∧ B ≤ q (t0 + j)) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · have := hk.2; rw [h] at this; simp at this; linarith
      · exact h
    have hlt : ∀ j < k, q (t0 + j) < B := fun j hj => by
      have := hmin j hj; push Not at this; exact this (by omega)
    refine ⟨k, hk0, hk.1, hk.2, ?_, hlt⟩
    have h1 := hlt (k - 1) (by omega)
    have h2 := P.step_up (t0 + (k - 1))
    rw [show t0 + (k - 1) + 1 = t0 + k by omega] at h2
    linarith
  · exfalso
    push Not at hex
    have hc := P.c_nonneg
    -- every tick of the stretch is in the phase
    have hr : ∀ k < T, ρ ≤ r (t0 + k + 1) := by
      intro k hk
      have hl := P.leak t0 k
      have : (k : ℝ) * (εf / α + εq) ≤ 1 / 2 := by
        have : (k : ℝ) ≤ T := by exact_mod_cast hk.le
        nlinarith [P.hεq]
      exact hphase (t0 + k) (by omega) (by linarith) (hex k hk.le)
    -- the summed deficit
    have hs := deficit_sum P.filt t0 T
    have hsum : ∑ k ∈ Finset.range T, (1 - r (t0 + k + 1)) ≤ T * (1 - ρ) := by
      have := Finset.sum_le_sum (s := Finset.range T) (f := fun k => 1 - r (t0 + k + 1))
        (g := fun _ => 1 - ρ) (fun k hk => by have := hr k (Finset.mem_range.1 hk); linarith)
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this; linarith
    have hDT : -(εf / α) ≤ 1 - s (t0 + T) := by linarith [(P.sb (t0 + T)).2]
    have hα := P.hα0
    have h1α : 0 ≤ 1 - α := by linarith [P.hα1]
    have hS : ∑ k ∈ Finset.range T, (1 - s (t0 + k + 1)) ≤
        (1 - α) / α * (D0 + εf / α) + T * (1 - ρ) + T * (εf / α) := by
      have e1 : (1 - α) * ((1 - s t0) - (1 - s (t0 + T))) ≤ (1 - α) * (D0 + εf / α) :=
        mul_le_mul_of_nonneg_left (by linarith) h1α
      have e2 : α * ∑ k ∈ Finset.range T, (1 - s (t0 + k + 1)) ≤
          α * ((1 - α) / α * (D0 + εf / α) + T * (1 - ρ) + T * (εf / α)) := by
        have : α * ((1 - α) / α * (D0 + εf / α) + T * (1 - ρ) + T * (εf / α)) =
            (1 - α) * (D0 + εf / α) + α * (T * (1 - ρ)) + T * εf := by
          field_simp
        rw [this]; nlinarith
      exact le_of_mul_le_mul_left e2 hα
    have hp := P.progress t0 T
    have := hex T le_rfl
    nlinarith

/-! ## The first leg -/

/-- **The first leg.** Suppose the S-curve time reaches `τ_v` by tick `W₀` (the escape from the
leg-start phase, a closed-loop hypothesis), the raw scaler is at least `ρ₀ ≤ 1` while
`q ∈ [τ_v − 1, a₀)`, and the numbers satisfy the leg condition over `T₀ − W₀` ticks from a deficit
`1 + c`, `(K + 2)(1 + c + ε_q) ≤ a₀ − τ_v` and `T₀ (c + ε_q) ≤ 1/2`. Then the first tick with
`q ≥ a₀` is at most `T₀`, its S-curve time is below `a₀ + 1 + c + ε_q`, every earlier tick is below
`a₀`, and its deficit is at most `(1 − α)^K (1 + c) + (1 − ρ₀) + c`. -/
theorem leg0_arrive (P : Pace s r q α εf εq) {τv a0 ρ0 : ℝ} {W0 T0 N K : ℕ} (hρ1 : ρ0 ≤ 1)
    (hτv : 0 ≤ τv) (hesc : ∃ t ≤ W0, τv ≤ q t) (hW : W0 ≤ T0) (hN : T0 ≤ N)
    (hphase : ∀ t < N, τv - 1 ≤ q t → q t < a0 → ρ0 ≤ r (t + 1))
    (hnum : a0 - τv ≤ ρ0 * (T0 - W0 : ℕ) - (1 - α) / α * ((1 + εf / α) + εf / α) -
      (T0 - W0 : ℕ) * (εf / α + εq))
    (hK : (K + 2) * (1 + εf / α + εq) ≤ a0 - τv) (hleak : T0 * (εf / α + εq) ≤ 1 / 2) :
    ∃ t1, t1 ≤ T0 ∧ a0 ≤ q t1 ∧ q t1 < a0 + (1 + εf / α + εq) ∧ (∀ j < t1, q j < a0) ∧
      1 - s t1 ≤ (1 - α) ^ K * (1 + εf / α) + ((1 - ρ0) + εf / α) := by
  classical
  have hc := P.c_nonneg
  have hεq := P.hεq
  -- the escape tick `E`: the first tick with `q ≥ τ_v`
  obtain ⟨E, hE, hEmin'⟩ : ∃ E, (E ≤ W0 ∧ τv ≤ q E) ∧ ∀ j < E, ¬ (j ≤ W0 ∧ τv ≤ q j) :=
    ⟨Nat.find hesc, Nat.find_spec hesc, fun j hj => Nat.find_min hesc hj⟩
  have hEmin : ∀ j < E, q j < τv := fun j hj => by
    have := hEmin' j hj; push Not at this
    exact this (by have := hE.1; omega)
  have hqE : q E ≤ τv + (1 + εf / α + εq) := by
    rcases Nat.eq_zero_or_pos E with h | h
    · rw [h]
      have := (abs_le.1 P.prog0).2; have := (P.sb 0).2; linarith
    · have h1 := hEmin (E - 1) (by omega)
      have h2 := P.step_up (E - 1)
      rw [show E - 1 + 1 = E by omega] at h2
      linarith
  have hg0 : 0 < 1 + εf / α + εq := by linarith
  have hgap : 2 * (1 + εf / α + εq) ≤ a0 - τv := by
    have : (0 : ℝ) ≤ K * (1 + εf / α + εq) := by positivity
    nlinarith
  -- the leg from `E`
  have hDE : 1 - s E ≤ 1 + εf / α := by linarith [(P.sb E).1]
  obtain ⟨k, hk0, hkT, hk1, hk2, hk3⟩ := leg_arrive P (A := τv) (B := a0) (T := T0 - W0) (N := N)
    hE.2 (by linarith) hDE (by have := hE.1; omega) hphase hnum (by
      have : ((T0 - W0 : ℕ) : ℝ) ≤ T0 := by exact_mod_cast Nat.sub_le T0 W0
      nlinarith)
  refine ⟨E + k, by have := hE.1; omega, hk1, hk2, ?_, ?_⟩
  · intro j hj
    by_cases hjE : j < E
    · have := hEmin j hjE; linarith
    · have := hk3 (j - E) (by omega)
      rwa [show E + (j - E) = j by omega] at this
  · -- the decay from `E` over `k ≥ K` ticks
    have hdec := deficit_decay P.hα0 P.hα1 P.filt hρ1 P.hεf E k (fun j hj => by
      refine hphase (E + j) (by have := hE.1; omega) ?_ (hk3 j hj)
      have hl := P.leak E j
      have : (j : ℝ) * (εf / α + εq) ≤ 1 / 2 := by
        have : (j : ℝ) ≤ T0 := by exact_mod_cast (show j ≤ T0 by omega)
        nlinarith
      linarith [hE.2])
    have hkK : K ≤ k := by
      -- `q` grows by at most `1 + c + ε_q` per tick
      have hup : ∀ n : ℕ, q (E + n) ≤ q E + n * (1 + εf / α + εq) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have := P.step_up (E + n)
          rw [show E + (n + 1) = E + n + 1 by ring]; push_cast; linarith
      have h1 := hup k
      by_contra hlt
      push Not at hlt
      have : (k : ℝ) ≤ K - 1 := by
        have : k ≤ K - 1 := by omega
        have h' : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        exact_mod_cast (show (k : ℝ) ≤ ((K - 1 : ℕ) : ℝ) by exact_mod_cast this).trans h'.le
      have h2 : (k : ℝ) * (1 + εf / α + εq) ≤ (K - 1) * (1 + εf / α + εq) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      nlinarith
    have hpow : (1 - α) ^ k ≤ (1 - α) ^ K :=
      pow_le_pow_of_le_one (by linarith [P.hα1]) (by linarith [P.hα0]) hkK
    have h0 : 0 ≤ (1 - α) ^ k := pow_nonneg (by linarith [P.hα1]) k
    have hDE0 : -(εf / α) ≤ 1 - s E := by linarith [(P.sb E).2]
    have : (1 - α) ^ k * (1 - s E) ≤ (1 - α) ^ K * (1 + εf / α) := by
      calc (1 - α) ^ k * (1 - s E) ≤ (1 - α) ^ k * (1 + εf / α) :=
            mul_le_mul_of_nonneg_left hDE h0
        _ ≤ (1 - α) ^ K * (1 + εf / α) := mul_le_mul_of_nonneg_right hpow (by linarith)
    linarith

/-! ## The nested reach formula -/

/-- Reaching a list of atoms in order, each within its allowance after the previous one. -/
def reachI : List (Formula X × ℕ) → Formula X
  | [] => trueF
  | (φ, T) :: rest => .eventually 0 T (.and φ (reachI rest))

/-- `reachSeqF` of the spec is `reachI` of its atoms. -/
theorem reachSeqF_eq (F : P3 → Formula X) : ∀ L : List (P3 × ℕ),
    reachSeqF F L = reachI (L.map fun wT => (F wT.1, wT.2))
  | [] => rfl
  | (w, T) :: L => by simp [reachSeqF, reachI, reachSeqF_eq F L]

/-- A leg: its arrival atom `φ`, the S-curve time `a` at which its window starts, the raw-scaler
bound `ρ` on its phase, its allowance `T`. -/
structure Leg where
  φ : Formula X
  a : ℝ
  ρ : ℝ
  T : ℕ

/-- The total allowance of a list of legs. -/
def legSpan : List Leg → ℕ
  | [] => 0
  | l :: L => l.T + legSpan L

/-- The hypotheses and numeric conditions of the legs after a window starting at `A`: windows of
width `w` in order, the phase bounds `ρ` of the raw scaler, the windows' atoms, and the leg
condition of `leg_arrive` from the deficit level `Δ`. -/
def LegsOK (x : ℕ → X) (r q : ℕ → ℝ) (α εf εq Δ w : ℝ) (N : ℕ) : ℝ → List Leg → Prop
  | _, [] => True
  | A, l :: L =>
    A + w ≤ l.a ∧ l.ρ ≤ 1 ∧ (1 - l.ρ) + εf / α ≤ Δ ∧
    l.a - A ≤ l.ρ * l.T - (1 - α) / α * (Δ + εf / α) - l.T * (εf / α + εq) ∧
    l.T * (εf / α + εq) ≤ 1 / 2 ∧
    (∀ t < N, A - 1 ≤ q t → q t < l.a → l.ρ ≤ r (t + 1)) ∧
    (∀ t ≤ N, l.a ≤ q t → q t < l.a + w → sat x t l.φ) ∧
    LegsOK x r q α εf εq Δ w N l.a L

/-- The window start of the last leg (`A` for no legs). -/
def lastA : ℝ → List Leg → ℝ
  | A, [] => A
  | _, l :: L => lastA l.a L

/-- **The chain of legs.** From a tick in the window `[A, A + w)` with deficit at most `Δ`, the
legs are reached in order, each within its allowance. -/
theorem chain_reach (P : Pace s r q α εf εq) (x : ℕ → X) {Δ w : ℝ} {N : ℕ}
    (hw : 1 + εf / α + εq ≤ w) :
    ∀ (L : List Leg) (A : ℝ) (t0 : ℕ), LegsOK x r q α εf εq Δ w N A L → A ≤ q t0 →
      q t0 < A + w → 1 - s t0 ≤ Δ → t0 + legSpan L ≤ N →
      sat x t0 (reachI (L.map fun l => (l.φ, l.T))) ∧
        ∃ t, t0 ≤ t ∧ t ≤ t0 + legSpan L ∧ lastA A L ≤ q t
  | [], _, t0, _, hA, _, _, _ => ⟨by simp [reachI, trueF], t0, le_rfl, by simp [legSpan], hA⟩
  | l :: L, A, t0, hok, hA, hAw, hD, hN => by
    obtain ⟨hw1, hρ1, hΔ, hnum, hleak, hphase, hwin, hrest⟩ := hok
    have hB : q t0 < l.a := by linarith
    obtain ⟨k, hk0, hkT, hk1, hk2, hk3⟩ := leg_arrive P (A := A) (B := l.a) (T := l.T) (N := N)
      hA hB hD (by simp [legSpan] at hN; omega) hphase hnum hleak
    simp only [List.map_cons, reachI, sat_eventually, sat_and, lastA]
    suffices hD' : 1 - s (t0 + k) ≤ Δ by
      obtain ⟨h1, t, ht1, ht2, ht3⟩ := chain_reach P x hw L l.a (t0 + k) hrest hk1 (by linarith) hD'
        (by simp [legSpan] at hN; omega)
      exact ⟨⟨t0 + k, by omega, by omega, hwin _ (by simp [legSpan] at hN; omega) hk1 (by linarith),
        h1⟩, t, by omega, by simp [legSpan]; omega, ht3⟩
    -- the deficit stays below `Δ` on the leg
    have hinv : ∀ j ≤ k, 1 - s (t0 + j) ≤ Δ := by
      intro j hj
      induction j with
      | zero => simpa using hD
      | succ j ih =>
        have h1 := ih (by omega)
        have hq := hk3 j (by omega)
        have hl := P.leak t0 j
        have : (j : ℝ) * (εf / α + εq) ≤ 1 / 2 := by
          have : (j : ℝ) ≤ l.T := by exact_mod_cast (show j ≤ l.T by omega)
          nlinarith [P.hεq, P.c_nonneg]
        have hr := hphase (t0 + j) (by simp [legSpan] at hN; omega) (by linarith) hq
        rw [show t0 + (j + 1) = t0 + j + 1 by ring]
        exact P.deficit_inv hΔ (t0 + j) h1 hr
    exact hinv k le_rfl

/-- **Lemma P-3 (arrival within the allowances).** The first leg as in `leg0_arrive`, with its atom
`φ₀` holding while `q ∈ [a₀, a₀ + w)`; the deficit level `Δ` of the later legs at least
`(1 − α)^K (1 + c) + (1 − ρ₀) + c`; the later legs `L` as in `LegsOK`. Then the nested reach formula
holds at tick `0`: `φ₀` within `T₀` ticks, and each later atom within its allowance after the
previous one. -/
theorem pacing_reach (P : Pace s r q α εf εq) (x : ℕ → X) {τv a0 ρ0 Δ w : ℝ} {W0 T0 N K : ℕ}
    (φ0 : Formula X) (L : List Leg) (hρ1 : ρ0 ≤ 1) (hτv : 0 ≤ τv)
    (hesc : ∃ t ≤ W0, τv ≤ q t) (hW : W0 ≤ T0) (hN : T0 + legSpan L ≤ N)
    (hphase : ∀ t < N, τv - 1 ≤ q t → q t < a0 → ρ0 ≤ r (t + 1))
    (hwin : ∀ t ≤ N, a0 ≤ q t → q t < a0 + w → sat x t φ0)
    (hnum : a0 - τv ≤ ρ0 * (T0 - W0 : ℕ) - (1 - α) / α * ((1 + εf / α) + εf / α) -
      (T0 - W0 : ℕ) * (εf / α + εq))
    (hK : (K + 2) * (1 + εf / α + εq) ≤ a0 - τv) (hleak : T0 * (εf / α + εq) ≤ 1 / 2)
    (hΔ : (1 - α) ^ K * (1 + εf / α) + ((1 - ρ0) + εf / α) ≤ Δ)
    (hw : 1 + εf / α + εq ≤ w) (hL : LegsOK x r q α εf εq Δ w N a0 L) :
    sat x 0 (reachI ((φ0, T0) :: L.map fun l => (l.φ, l.T))) ∧
      ∃ t, t ≤ T0 + legSpan L ∧ lastA a0 L ≤ q t := by
  obtain ⟨t1, ht1, h1, h2, -, h4⟩ := leg0_arrive P hρ1 hτv hesc hW (by omega) hphase hnum hK hleak
  obtain ⟨hc, t, -, ht2, ht3⟩ := chain_reach P x hw L a0 t1 hL h1 (by linarith) (h4.trans hΔ)
    (by omega)
  simp only [reachI, sat_eventually, sat_and]
  exact ⟨⟨t1, by omega, by omega, hwin t1 (by omega) h1 (by linarith), hc⟩, t, by omega, ht3⟩

/-! ## The S-curve time step of the code -/

/-- **The S-curve time step.** `advance_wp_target_along_track` passes
`_track_dt_scalar * vel_dt_scalar * dt` to the S-curve; with `vel_dt_scalar = 1` (the speed ramp
at its target) and `dt = 0.0025f`, the step in ticks (`× 400`) is within `10⁻⁷` of the filtered
scaler, for `|s| ≤ 1 + 10⁻⁴`. -/
theorem prog_step {sc v : Float32} (hs : sc.IsFinite) (hv : v.IsFinite) (hv1 : v.toReal = 1)
    (hs1 : |sc.toReal| ≤ 1 + 1 / 10 ^ 4) :
    (sc * v * (0.0025 : Float32)).IsFinite ∧
      |(sc * v * (0.0025 : Float32)).toReal * 400 - sc.toReal| ≤ 1 / 10 ^ 7 := by
  obtain ⟨f1, e1⟩ := Float32.mul_exact hs hv hs (by rw [hv1, mul_one])
  have hdt : (0.0025 : Float32).toModel.unpack = .finite .positive 10737418 (-32) (by decide) := by
    rfl
  have fdt : (0.0025 : Float32).IsFinite := by rw [Float32.isFinite_iff, hdt]; rfl
  have edt : (0.0025 : Float32).toReal = 5368709 / 2147483648 := by
    rw [Float32.toReal, hdt]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
  have m := B32.mul (e := 16 / 10 ^ 11) (R := 26 / 10000) (B32.of_exact f1 (R := 1 + 1 / 10 ^ 4)
    (by rw [e1]; exact hs1)) (B32.of_exact fdt (R := 1 / 400) (by rw [edt]; norm_num))
    (by norm_num [capF]) (by norm_num) (by norm_num)
  refine ⟨m.1.1, ?_⟩
  have h := m.1.2
  rw [e1, edt] at h
  have h2 : |sc.toReal * (5368709 / 2147483648) * 400 - sc.toReal| ≤ (1 + 1 / 10 ^ 4) * (48 / 2147483648) := by
    rw [show sc.toReal * (5368709 / 2147483648) * 400 - sc.toReal = sc.toReal * (-(48 / 2147483648)) by
      ring, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 48 / 2147483648)]
    exact mul_le_mul_of_nonneg_right hs1 (by norm_num)
  have h3 : |(sc * v * (0.0025 : Float32)).toReal * 400 - sc.toReal * (5368709 / 2147483648) * 400|
      ≤ 400 * (16 / 10 ^ 11) := by
    rw [show (sc * v * (0.0025 : Float32)).toReal * 400 - sc.toReal * (5368709 / 2147483648) * 400 =
      400 * ((sc * v * (0.0025 : Float32)).toReal - sc.toReal * (5368709 / 2147483648)) by ring,
      abs_mul]
    norm_num; linarith
  have := abs_sub_le ((sc * v * (0.0025 : Float32)).toReal * 400)
    (sc.toReal * (5368709 / 2147483648) * 400) sc.toReal
  norm_num at h2 h3 ⊢; linarith

/-! ## The hold at `w7` -/

/-- **The hold.** Let the target reach S-curve time `a₇` at tick `t₇`. Until the mission completes
(tick `t_c`) the target is within `r_E` of `w7` whenever `q ≥ a₇ − 1` (the end of the last S-curve:
monotone approach and rest at `w7`, M7); from `t_c` on it is on the loiter leg towards the stopping
point `stopPt` of the completion tick's position controller state (M7), whose distance to `w7` is
bounded by the navigator's `loiter_dest_bound` from the sampled position and velocity at `t_c`.
With those within `ε_p` and `ε_v` and `ε_p + ε_v + 10⁻⁵ ≤ r_E`, the target stays within `r_E` of
`w7` from `t₇` to `N`. -/
theorem hold_w7 (hL : LibmSpec) (P : Pace s r q α εf εq) (x : ℕ → X) {a7 rE εp εvl : ℝ}
    {t7 tc N : ℕ} (ht7 : a7 ≤ q t7) (hleakN : N * (εf / α + εq) ≤ 1 / 2)
    (hpre : ∀ t ≤ N, t < tc → a7 - 1 ≤ q t → dist (posTarget (x t)) w7 ≤ rE)
    (pc : AC_PosControl.Params) (sc : AC_PosControl.State)
    (hpost : ∀ t ≤ N, tc ≤ t → dist (posTarget (x t)) w7 ≤ dist (stopPt pc sc) w7)
    (hkp : pc._p_pos_ne_m._kp = 1.5) (hacc : sc._accel_max_ne_mss = 1.5) (hvm : sc._vel_max_ne_ms = 1)
    (hkpd : pc._p_pos_d_m._kp = 1) (haccd : sc._accel_max_d_mss = 1)
    (hpox : A64 sc._pos_offset_ned_m.x 0 0) (hpoy : A64 sc._pos_offset_ned_m.y 0 0)
    (hpoz : A64 sc._pos_offset_ned_m.z 0 0)
    (hvox : A32 sc._vel_offset_ned_ms.x 0 0) (hvoy : A32 sc._vel_offset_ned_ms.y 0 0)
    (hvoz : A32 sc._vel_offset_ned_ms.z 0 0)
    (hpx : sc._pos_estimate_ned_m.x.IsFinite) (hpy : sc._pos_estimate_ned_m.y.IsFinite)
    (hpz : sc._pos_estimate_ned_m.z.IsFinite)
    (hvx : sc._vel_estimate_ned_ms.x.IsFinite) (hvy : sc._vel_estimate_ned_ms.y.IsFinite)
    (hvz : sc._vel_estimate_ned_ms.z.IsFinite)
    (hd : dist (estPos sc) w7 ≤ εp) (hv : ‖estVel sc‖ ≤ εvl) (hεp : εp ≤ 1) (hεv : εvl ≤ 9 / 10)
    (hsum : εp + εvl + 1 / 10 ^ 5 ≤ rE) :
    ∀ t, t7 ≤ t → t ≤ N → sat x t (nearT w7 rE) := by
  intro t h1 h2
  simp only [nearT, sat_atom, sub_nonneg]
  by_cases htc : tc ≤ t
  · refine (hpost t h2 htc).trans ?_
    have hc : ∀ i : Fin 3, |estPos sc i| ≤ 2 := by
      intro i
      have h1 := abs_coord_le_dist (estPos sc) w7 i
      have h2 : |w7 i| ≤ 1 := by fin_cases i <;> norm_num [w7, wp]
      have h3 := abs_sub_abs_le_abs_sub (estPos sc i) (w7 i)
      linarith
    have c0 := hc 0
    have c1 := hc 1
    have c2 := hc 2
    simp [estPos] at c0 c1 c2
    have := loiter_dest_bound hL pc sc hkp hacc hvm hkpd haccd hpox hpoy hpoz hvox hvoy hvoz hpx hpy
      hpz c0 c1 c2 hvx hvy hvz (hv.trans hεv) w7
    linarith
  · push Not at htc
    refine hpre t h2 htc ?_
    have hl := P.leak t7 (t - t7)
    rw [show t7 + (t - t7) = t by omega] at hl
    have : ((t - t7 : ℕ) : ℝ) * (εf / α + εq) ≤ 1 / 2 := by
      have : ((t - t7 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show t - t7 ≤ N by omega)
      nlinarith [P.hεq, P.c_nonneg]
    linarith

/-- The hold as the formula of `ψtrack`: within `10800` ticks the target is within `r_E` of `w7`
for `1200` ticks, from the arrival tick `t₇ ≤ 10800`. -/
theorem hold_formula (x : ℕ → X) {rE : ℝ} {t7 : ℕ} (ht7 : t7 ≤ 10800)
    (hhold : ∀ t, t7 ≤ t → t ≤ t7 + 1200 → sat x t (nearT w7 rE)) :
    sat x 0 (.eventually 0 10800 (.always 0 1200 (nearT w7 rE))) := by
  simp only [sat_eventually, sat_always]
  exact ⟨t7, by omega, by omega, fun t h1 h2 => hhold t (by omega) (by omega)⟩

/-- `Pace` from the per-tick code facts: the filter run (`code_filter_step`), the raw scaler in
`[0, 1]` (`rawScaler_unit`), the initial scaler (`1.0` after `wp_and_spline_init_m`, so in
`[−c, 1 + c]`), and the S-curve time steps (`prog_step`). -/
theorem pace_of (hf : FilterRun s r α₀ (1 / 10 ^ 7)) (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1)
    (hs0 : -((1 / 10 ^ 7) / α₀) ≤ s 0 ∧ s 0 ≤ 1 + (1 / 10 ^ 7) / α₀)
    (hq : ∀ t, |q (t + 1) - q t - s (t + 1)| ≤ 1 / 10 ^ 7) (hq0 : |q 0 - s 0| ≤ 1 / 10 ^ 7) :
    Pace s r q α₀ (1 / 10 ^ 7) (1 / 10 ^ 7) := by
  have hα : (0 : ℝ) < α₀ := by rw [α₀]; norm_num
  have hα1 : α₀ ≤ 1 := by rw [α₀]; norm_num
  exact ⟨hα, hα1, by norm_num, by norm_num, hf, hr, filter_bounds hα hα1 hf hr hs0, hq, hq0⟩

/-! ## The course -/

/-- The raw-scaler bounds of the course's phases, from P-1 with along-track errors
`ε_v = 0.055` m/s, `ε_e = 0.03` m and the S-curve speed `|v_T| ≥ v_min` on the phase:
`v_min = 0.36` (leg-start escape to the `w1` window, through the `w0` blend), `0.6` (`w1 … w6`),
`0.48` (the deceleration into `w7`). -/
def ρLo : ℝ := 7712 / 10000
def ρMid : ℝ := 8823 / 10000
def ρEnd : ℝ := 8406 / 10000

/-- P-1 gives these bounds: `min 1 (1.05 − (0.055 + 1.5 · 0.03)/v_min − 10⁻³) ≥ ρ`. -/
theorem rho_course :
    ρLo ≤ min 1 (21 / 20 - (55 / 1000 + 3 / 2 * (3 / 100)) / (36 / 100) - 1 / 1000) ∧
    ρMid ≤ min 1 (21 / 20 - (55 / 1000 + 3 / 2 * (3 / 100)) / (6 / 10) - 1 / 1000) ∧
    ρEnd ≤ min 1 (21 / 20 - (55 / 1000 + 3 / 2 * (3 / 100)) / (48 / 100) - 1 / 1000) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [le_min_iff] <;> constructor <;> norm_num [ρLo, ρMid, ρEnd]

/-- The phase hypothesis from P-1: at a tick whose inputs meet the hypotheses of `rawScaler_ge`
with `v_min ≥ 0.36`, `ε_v = 0.055`, `ε_e = 0.03`, the raw scaler is at least `ρLo`. -/
theorem rawScaler_ge_course (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32)
    (hkPf : kP.IsFinite) (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4)
    (hve : Fin3 ve 3) (hL : 36 / 100 ≤ len3 vT)
    (hv : dot3 vT vT - dot3 ve vT ≤ 55 / 1000 * len3 vT) (he : dot3 pe vT ≤ 3 / 100 * len3 vT) :
    ρLo ≤ (rawScaler vT pe ve kP).toReal :=
  rho_course.1.trans (rawScaler_ge vT pe ve kP hkPf hkP hvT hpe hve (by norm_num) hL
    (by norm_num) hv he)

theorem legsOK_cons (x : ℕ → X) (r q : ℕ → ℝ) {α εf εq Δ w : ℝ} {N : ℕ} {A : ℝ} {l : Leg}
    {L : List Leg} (h1 : A + w ≤ l.a) (h2 : l.ρ ≤ 1) (h3 : (1 - l.ρ) + εf / α ≤ Δ)
    (h4 : l.a - A ≤ l.ρ * l.T - (1 - α) / α * (Δ + εf / α) - l.T * (εf / α + εq))
    (h5 : l.T * (εf / α + εq) ≤ 1 / 2)
    (h6 : ∀ t < N, A - 1 ≤ q t → q t < l.a → l.ρ ≤ r (t + 1))
    (h7 : ∀ t ≤ N, l.a ≤ q t → q t < l.a + w → sat x t l.φ)
    (h8 : LegsOK x r q α εf εq Δ w N l.a L) : LegsOK x r q α εf εq Δ w N A (l :: L) :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The numeric leg condition of the course: duration `X`, allowance `T`, bound `ρ`, from the
deficit level `Δ = 0.38`. -/
theorem num_leg {A a ρ X : ℝ} {T : ℕ} (ha : a - A ≤ X)
    (h : X ≤ ρ * T - (1 - α₀) / α₀ * (38 / 100 + 1 / 10 ^ 7 / α₀) - T * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7)) :
    a - A ≤ ρ * T - (1 - α₀) / α₀ * (38 / 100 + 1 / 10 ^ 7 / α₀) - T * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7) :=
  ha.trans h

/-- **P-3 on the course: the pacing conjunct of `ψtrack`.** Hypotheses, with S-curve times in
ticks:

* the code facts `Pace` with the coefficient `α₀`, filter rounding `10⁻⁷`, step rounding `10⁻⁷`
  (`code_filter_step`, `rawScaler_unit`, `filter_bounds`, `prog_step`);
* the leg-start escape (closed loop): by tick `350` the S-curve time reaches `τ_v ≥ 0`, after which
  the climb's speed is at least `0.36` m/s;
* S-curve geometry (M7): window starts `a 0 … a 7` with `240 ≤ a₀ − τ_v ≤ 510` and leg durations
  `2 ≤ a_i − a_{i−1} ≤ (860, 743, 743, 1450, 743, 743, 750)`;
* phases (P-1 with the tracking bounds and the speed profile, `rawScaler_ge_course`): the raw scaler
  is at least `ρLo` while `q ∈ [τ_v − 1, a₁)`, `ρMid` while `q ∈ [a_{i−1} − 1, a_i)` for
  `i = 2 … 6`, `ρEnd` while `q ∈ [a₆ − 1, a₇)`;
* windows (M7 and, for `w0`, the climb certificate): while `q ∈ [a_i, a_i + 2)`, the vehicle is
  within `r` of `w0` (`i = 0`), the target within `rPass w_i` of `w_i` (`i ≥ 1`).

Then the reach conjunct of `ψtrack` holds: the vehicle reaches `w0` within `1200` ticks, then the
target reaches `w1 … w7` (radius `rPass`) in order within the allowances. -/
theorem pacing_course (P : Pace s r q α₀ (1 / 10 ^ 7) (1 / 10 ^ 7)) (x : ℕ → X) {τv : ℝ}
    (a : Fin 8 → ℝ) (hτv : 0 ≤ τv) (hesc : ∃ t ≤ 350, τv ≤ q t)
    (ha0 : 240 ≤ a 0 - τv ∧ a 0 - τv ≤ 510)
    (ha1 : 2 ≤ a 1 - a 0 ∧ a 1 - a 0 ≤ 860) (ha2 : 2 ≤ a 2 - a 1 ∧ a 2 - a 1 ≤ 743)
    (ha3 : 2 ≤ a 3 - a 2 ∧ a 3 - a 2 ≤ 743) (ha4 : 2 ≤ a 4 - a 3 ∧ a 4 - a 3 ≤ 1450)
    (ha5 : 2 ≤ a 5 - a 4 ∧ a 5 - a 4 ≤ 743) (ha6 : 2 ≤ a 6 - a 5 ∧ a 6 - a 5 ≤ 743)
    (ha7 : 2 ≤ a 7 - a 6 ∧ a 7 - a 6 ≤ 750)
    (hph0 : ∀ t < 12000, τv - 1 ≤ q t → q t < a 1 → ρLo ≤ r (t + 1))
    (hph : ∀ i : Fin 8, 2 ≤ (i : ℕ) → (i : ℕ) ≤ 6 → ∀ t < 12000,
      a (i - 1) - 1 ≤ q t → q t < a i → ρMid ≤ r (t + 1))
    (hph7 : ∀ t < 12000, a 6 - 1 ≤ q t → q t < a 7 → ρEnd ≤ r (t + 1))
    (hwin0 : ∀ t ≤ 12000, a 0 ≤ q t → q t < a 0 + 2 → sat x t (near (wp 0) rWp))
    (hwin : ∀ i : Fin 8, 1 ≤ (i : ℕ) → ∀ t ≤ 12000, a i ≤ q t → q t < a i + 2 →
      sat x t (nearT (wp i) (rPass (wp i)))) :
    sat x 0 (.eventually 0 1200 (.and (near (wp 0) rWp)
      (reachSeqF (fun w => nearT w (rPass w)) legs.tail))) ∧ ∃ t ≤ 10800, a 7 ≤ q t := by
  have hα : (0 : ℝ) < α₀ := by rw [α₀]; norm_num
  have hc : (1 / 10 ^ 7 : ℝ) / α₀ ≤ 13 / 10 ^ 6 := c_course
  have hc0 : (0 : ℝ) ≤ 1 / 10 ^ 7 / α₀ := by positivity
  -- the phases, in the form of `LegsOK`
  have p0 : ∀ t < 12000, τv - 1 ≤ q t → q t < a 0 → ρLo ≤ r (t + 1) := fun t ht h1 h2 =>
    hph0 t ht h1 (by linarith [ha1.1])
  have p1 : ∀ t < 12000, a 0 - 1 ≤ q t → q t < a 1 → ρLo ≤ r (t + 1) := fun t ht h1 h2 =>
    hph0 t ht (by linarith [ha0.1]) h2
  have pm : ∀ i : Fin 8, 2 ≤ (i : ℕ) → (i : ℕ) ≤ 6 → ∀ t < 12000,
      a (i - 1) - 1 ≤ q t → q t < a i → ρMid ≤ r (t + 1) := hph
  have p2 := pm 2 (by decide) (by decide)
  have p3 := pm 3 (by decide) (by decide)
  have p4 := pm 4 (by decide) (by decide)
  have p5 := pm 5 (by decide) (by decide)
  have p6 := pm 6 (by decide) (by decide)
  have e21 : (2 : Fin 8) - 1 = 1 := by decide
  have e32 : (3 : Fin 8) - 1 = 2 := by decide
  have e43 : (4 : Fin 8) - 1 = 3 := by decide
  have e54 : (5 : Fin 8) - 1 = 4 := by decide
  have e65 : (6 : Fin 8) - 1 = 5 := by decide
  rw [e21] at p2; rw [e32] at p3; rw [e43] at p4; rw [e54] at p5; rw [e65] at p6
  have w1 := hwin 1 (by decide)
  have w2 := hwin 2 (by decide)
  have w3 := hwin 3 (by decide)
  have w4 := hwin 4 (by decide)
  have w5 := hwin 5 (by decide)
  have w6 := hwin 6 (by decide)
  have w7' := hwin 7 (by decide)
  -- the legs
  let L : List Leg := [⟨nearT (wp 1) (rPass (wp 1)), a 1, ρLo, 1200⟩,
    ⟨nearT (wp 2) (rPass (wp 2)), a 2, ρMid, 1200⟩, ⟨nearT (wp 3) (rPass (wp 3)), a 3, ρMid, 1200⟩,
    ⟨nearT (wp 4) (rPass (wp 4)), a 4, ρMid, 2400⟩, ⟨nearT (wp 5) (rPass (wp 5)), a 5, ρMid, 1200⟩,
    ⟨nearT (wp 6) (rPass (wp 6)), a 6, ρMid, 1200⟩, ⟨nearT (wp 7) (rPass (wp 7)), a 7, ρEnd, 1200⟩]
  have hlegs : reachSeqF (fun w => nearT w (rPass w)) legs.tail = reachI (L.map fun l => (l.φ, l.T)) := by
    rw [reachSeqF_eq]; rfl
  have nΔLo : (1 - ρLo) + 1 / 10 ^ 7 / α₀ ≤ 38 / 100 := by rw [ρLo]; linarith
  have nΔMid : (1 - ρMid) + 1 / 10 ^ 7 / α₀ ≤ 38 / 100 := by rw [ρMid]; linarith
  have nΔEnd : (1 - ρEnd) + 1 / 10 ^ 7 / α₀ ≤ 38 / 100 := by rw [ρEnd]; linarith
  have lk1 : ((1200 : ℕ) : ℝ) * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7) ≤ 1 / 2 := by push_cast; nlinarith
  have lk2 : ((2400 : ℕ) : ℝ) * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7) ≤ 1 / 2 := by push_cast; nlinarith
  have nk : ∀ (ρ X : ℝ) (T : ℕ), X ≤ ρ * T - 1191 / 10 * (38 / 100 + 13 / 10 ^ 6) - T * (13 / 10 ^ 6 + 1 / 10 ^ 7) →
      X ≤ ρ * T - (1 - α₀) / α₀ * (38 / 100 + 1 / 10 ^ 7 / α₀) - T * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7) := by
    intro ρ X T h
    have h1 : (1 - α₀) / α₀ ≤ 1191 / 10 := by rw [α₀]; norm_num
    have h2 : (0 : ℝ) ≤ (1 - α₀) / α₀ := by rw [α₀]; norm_num
    have h3 : (1 - α₀) / α₀ * (38 / 100 + 1 / 10 ^ 7 / α₀) ≤ 1191 / 10 * (38 / 100 + 13 / 10 ^ 6) :=
      mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
    have h4 : (T : ℝ) * (1 / 10 ^ 7 / α₀ + 1 / 10 ^ 7) ≤ T * (13 / 10 ^ 6 + 1 / 10 ^ 7) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hOK : LegsOK x r q α₀ (1 / 10 ^ 7) (1 / 10 ^ 7) (38 / 100) 2 12000 (a 0) L := by
    refine legsOK_cons x r q (by simp; linarith [ha1.1]) (by simp [ρLo]; norm_num) nΔLo
      (by simp only; exact num_leg ha1.2 (nk _ _ _ (by rw [ρLo]; norm_num))) (by simpa using lk1)
      p1 w1 ?_
    refine legsOK_cons x r q (by simp; linarith [ha2.1]) (by simp [ρMid]; norm_num) nΔMid
      (by simp only; exact num_leg ha2.2 (nk _ _ _ (by rw [ρMid]; norm_num))) (by simpa using lk1)
      p2 w2 ?_
    refine legsOK_cons x r q (by simp; linarith [ha3.1]) (by simp [ρMid]; norm_num) nΔMid
      (by simp only; exact num_leg ha3.2 (nk _ _ _ (by rw [ρMid]; norm_num))) (by simpa using lk1)
      p3 w3 ?_
    refine legsOK_cons x r q (by simp; linarith [ha4.1]) (by simp [ρMid]; norm_num) nΔMid
      (by simp only; exact num_leg ha4.2 (nk _ _ _ (by rw [ρMid]; norm_num))) (by simpa using lk2)
      p4 w4 ?_
    refine legsOK_cons x r q (by simp; linarith [ha5.1]) (by simp [ρMid]; norm_num) nΔMid
      (by simp only; exact num_leg ha5.2 (nk _ _ _ (by rw [ρMid]; norm_num))) (by simpa using lk1)
      p5 w5 ?_
    refine legsOK_cons x r q (by simp; linarith [ha6.1]) (by simp [ρMid]; norm_num) nΔMid
      (by simp only; exact num_leg ha6.2 (nk _ _ _ (by rw [ρMid]; norm_num))) (by simpa using lk1)
      p6 w6 ?_
    exact legsOK_cons x r q (by simp; linarith [ha7.1]) (by simp [ρEnd]; norm_num) nΔEnd
      (by simp only; exact num_leg ha7.2 (nk _ _ _ (by rw [ρEnd]; norm_num))) (by simpa using lk1)
      hph7 w7' trivial
  have h := pacing_reach P x (τv := τv) (a0 := a 0) (ρ0 := ρLo) (Δ := 38 / 100) (w := 2) (W0 := 350)
    (T0 := 1200) (N := 12000) (K := 230) (near (wp 0) rWp) L (by rw [ρLo]; norm_num) hτv hesc
    (by norm_num) (by simp [L, legSpan]) p0 hwin0 ?_ ?_ ?_ ?_ (by linarith) hOK
  · obtain ⟨h1, t, ht, ht'⟩ := h
    refine ⟨by simpa [reachI, hlegs] using h1, t, by simpa [L, legSpan] using ht, by simpa [L, lastA] using ht'⟩
  · -- the first leg's condition
    have h1 : (1 - α₀) / α₀ ≤ 1191 / 10 := by rw [α₀]; norm_num
    have h2 : (0 : ℝ) ≤ (1 - α₀) / α₀ := by rw [α₀]; norm_num
    have h3 : (1 - α₀) / α₀ * ((1 + 1 / 10 ^ 7 / α₀) + 1 / 10 ^ 7 / α₀) ≤ 1191 / 10 * (1 + 26 / 10 ^ 6) :=
      mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
    have h4 : ((1200 - 350 : ℕ) : ℝ) = 850 := by norm_num
    rw [h4, ρLo]
    nlinarith [ha0.2]
  · push_cast; nlinarith [ha0.1]
  · push_cast; nlinarith
  · -- the deficit level after the first leg
    have hpow : (1 - α₀) ^ 230 ≤ 146 / 1000 := by rw [α₀]; norm_num
    have : (1 - α₀) ^ 230 * (1 + 1 / 10 ^ 7 / α₀) ≤ 146 / 1000 * (1 + 13 / 10 ^ 6) :=
      mul_le_mul hpow (by linarith) (by positivity) (by norm_num)
    rw [ρLo]; linarith

/-- **The hold on the course: the hold conjunct of `ψtrack`.** The S-curve time reaches `a₇` by
tick `10800` (`pacing_course`); until completion the target is within `rPass w7 = rPassEnd` of `w7`
whenever `q ≥ a₇ − 1` (M7: the last S-curve ends at `w7`, approached monotonically); after
completion it is on the loiter leg (M7), whose destination `stopPt` is bounded by the navigator's
`loiter_dest_bound`; at the completion tick the sampled position is within `0.03` m of `w7` and the
sampled speed at most `0.05` m/s (closed loop). Then within `10800` ticks the target is within
`rPass w7` of `w7` for `1200` ticks. -/
theorem hold_course (hL : LibmSpec) (P : Pace s r q α₀ (1 / 10 ^ 7) (1 / 10 ^ 7)) (x : ℕ → X)
    {a7 : ℝ} {tc : ℕ} (ht7 : ∃ t ≤ 10800, a7 ≤ q t)
    (hpre : ∀ t ≤ 12000, t < tc → a7 - 1 ≤ q t → dist (posTarget (x t)) w7 ≤ rPass w7)
    (pc : AC_PosControl.Params) (sc : AC_PosControl.State)
    (hpost : ∀ t ≤ 12000, tc ≤ t → dist (posTarget (x t)) w7 ≤ dist (stopPt pc sc) w7)
    (hkp : pc._p_pos_ne_m._kp = 1.5) (hacc : sc._accel_max_ne_mss = 1.5) (hvm : sc._vel_max_ne_ms = 1)
    (hkpd : pc._p_pos_d_m._kp = 1) (haccd : sc._accel_max_d_mss = 1)
    (hpox : A64 sc._pos_offset_ned_m.x 0 0) (hpoy : A64 sc._pos_offset_ned_m.y 0 0)
    (hpoz : A64 sc._pos_offset_ned_m.z 0 0)
    (hvox : A32 sc._vel_offset_ned_ms.x 0 0) (hvoy : A32 sc._vel_offset_ned_ms.y 0 0)
    (hvoz : A32 sc._vel_offset_ned_ms.z 0 0)
    (hpx : sc._pos_estimate_ned_m.x.IsFinite) (hpy : sc._pos_estimate_ned_m.y.IsFinite)
    (hpz : sc._pos_estimate_ned_m.z.IsFinite)
    (hvx : sc._vel_estimate_ned_ms.x.IsFinite) (hvy : sc._vel_estimate_ned_ms.y.IsFinite)
    (hvz : sc._vel_estimate_ned_ms.z.IsFinite)
    (hd : dist (estPos sc) w7 ≤ 3 / 100) (hv : ‖estVel sc‖ ≤ 5 / 100) :
    sat x 0 (.eventually 0 totalTicks (.always 0 holdTicks (nearT w7 (rPass w7)))) := by
  obtain ⟨t7, ht7a, ht7b⟩ := ht7
  have hc := c_course
  have hα : (0 : ℝ) < α₀ := by rw [α₀]; norm_num
  have hc0 : (0 : ℝ) ≤ 1 / 10 ^ 7 / α₀ := by positivity
  have hh := hold_w7 hL P x (rE := rPass w7) (εp := 3 / 100) (εvl := 5 / 100) (N := 12000) ht7b
    (by push_cast; nlinarith) hpre pc sc hpost hkp hacc hvm hkpd haccd hpox hpoy hpoz hvox hvoy hvoz
    hpx hpy hpz hvx hvy hvz hd hv (by norm_num) (by norm_num)
    (by rw [rPass_w7, rPassEnd]; norm_num)
  rw [show totalTicks = 10800 from rfl, show holdTicks = 1200 from rfl]
  exact hold_formula x ht7a (fun t h1 h2 => hh t h1 (by omega))

end

end Contracts.Track.Pacing
