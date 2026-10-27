import Contracts
/-!
# Typed check of the delegation construction (review copy)

Ports are separate types `U W E Y`; a set over a sub-alphabet is a predicate on those types only, so
Theorem (a) (alphabets) holds by the type signatures. Everything is core Lean 4 plus the project's
`Contracts` library, which is used only in the last section to connect D3+ with `AG.rule_general`.

Sections:
1. definitions (A1, A2, G2, R, G1, Bad) and Theorem (b), (c), (d), (e), (f);
2. monotonicity along the chain of tubes and the up-set of certified indices;
3. relation to the quotient: saturated G1 equals the universal projection of the AG quotient;
   the exact quotient with the controller code inlined; the loss of not inlining;
4. side facts: strict D2 with P in A2, maximality under the weaker side condition, the literal D3;
5. the pointwise lemma (Box and Diamond parts) with its side conditions and a counterexample for H < m;
6. the deadline-to-ticks conversion, with the polarity check;
7. D3+ as the tightening side condition after `AG.rule_general`;
8. F2-F4 over a product of ports (after the namespace).
-/

namespace Deleg

/-! ## 1. Construction and Theorem (b)-(f) -/

section Typed
attribute [local instance] Classical.propDecidable
variable {U W E Y : Type}
variable (A : U → E → Prop) (G : U → E → Y → Prop)
variable (V : W → Prop) (P : W → E → Prop) (T : W → E → Y → Prop)

/-- Step 3: `A1 := ∃_{E∪Y} A` (A does not mention Y here). -/
def A1 (u : U) : Prop := ∃ e, A u e
/-- Step 2: `A2 := V`. -/
def A2 (w : W) : Prop := V w
/-- Step 2: `G2 := ¬P ∪ T`. -/
def G2 (w : W) (e : E) (y : Y) : Prop := P w e → T w e y
/-- Step 4: `R := ∀_{E∪Y} (¬A ∪ ¬A2 ∪ ¬G2 ∪ G)`. -/
def R (u : U) (w : W) : Prop := ∀ e y, A u e → A2 V w → G2 P T w e y → G u e y
/-- Step 4: `G1 := A2 ∩ R`. -/
def G1 (u : U) (w : W) : Prop := A2 V w ∧ R A G V P T u w
/-- Step 5: `Bad := A1 ∩ ¬∃_W G1`. -/
def Bad (u : U) : Prop := A1 A u ∧ ¬ ∃ w, G1 A G V P T u w

-- (b)
theorem D1 : ∀ u e, A u e → A1 A u := fun _ e h => ⟨e, h⟩
theorem D2 : ∀ u w, G1 A G V P T u w → A2 V w := fun _ _ h => h.1
theorem D3plus : ∀ u w e y, A u e → G1 A G V P T u w → A2 V w → G2 P T w e y → G u e y :=
  fun _ _ e y hA hG1 hA2 hG2 => hG1.2 e y hA hA2 hG2

-- (c) composition, in the form asked for, and with the wire hidden
theorem compose (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (h1 : ∀ u w, M1 u w → A1 A u → G1 A G V P T u w)
    (h2 : ∀ w e y, M2 w e y → A2 V w → G2 P T w e y) :
    ∀ u w e y, M1 u w → M2 w e y → A u e → G u e y := by
  intro u w e y m1 m2 hA
  have g1 := h1 u w m1 (D1 A u e hA)
  have a2 := D2 A G V P T u w g1
  exact D3plus A G V P T u w e y hA g1 a2 (h2 w e y m2 a2)

theorem compose_hidden (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (h1 : ∀ u w, M1 u w → A1 A u → G1 A G V P T u w)
    (h2 : ∀ w e y, M2 w e y → A2 V w → G2 P T w e y) :
    ∀ u e y, (∃ w, M1 u w ∧ M2 w e y) → A u e → G u e y :=
  fun u e y ⟨w, m1, m2⟩ hA => compose A G V P T M1 M2 h1 h2 u w e y m1 m2 hA

/-- (c) is not vacuous once both components accept all inputs: a total planner meeting `(A1, G1)` and a
controller that answers every mission in `V` give a composite behaviour for every `(u, e)` in `A`. -/
theorem compose_nonvacuous (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (htot : ∀ u, ∃ w, M1 u w) (h1 : ∀ u w, M1 u w → A1 A u → G1 A G V P T u w)
    (hrec : ∀ w e, V w → ∃ y, M2 w e y) :
    ∀ u e, A u e → ∃ w y, M1 u w ∧ M2 w e y := by
  intro u e hA
  obtain ⟨w, hw⟩ := htot u
  obtain ⟨y, hy⟩ := hrec w e (h1 u w hw ⟨e, hA⟩).1
  exact ⟨w, y, hw, hy⟩

-- (d) the controller's obligation is unchanged by moving P into the guarantee
theorem obligation (M2 : W → E → Y → Prop) :
    (∀ w e y, M2 w e y → A2 V w → G2 P T w e y) ↔ (∀ w e y, M2 w e y → V w → P w e → T w e y) :=
  Iff.rfl

-- (e) maximality among guarantees over U,W meeting D2 and D3+
theorem maximal (G1' : U → W → Prop)
    (h2 : ∀ u w, G1' u w → A2 V w)
    (h3 : ∀ u w e y, A u e → G1' u w → A2 V w → G2 P T w e y → G u e y) :
    ∀ u w, G1' u w → G1 A G V P T u w :=
  fun u w h => ⟨h2 u w h, fun e y hA hV hG => h3 u w e y hA h hV hG⟩

-- (f) realizability. `Nonempty W` is needed: a total planner must output something even off A1.
theorem realizable [inst : Nonempty W] :
    (∀ u, A1 A u → ∃ w, G1 A G V P T u w) ↔
    ∃ M1 : U → W → Prop, (∀ u, ∃ w, M1 u w) ∧ (∀ u w, M1 u w → A1 A u → G1 A G V P T u w) := by
  constructor
  · intro h
    refine ⟨fun u w => G1 A G V P T u w ∨ ¬ A1 A u, fun u => ?_, fun u w hm ha => ?_⟩
    · by_cases ha : A1 A u
      · obtain ⟨w, hw⟩ := h u ha
        exact ⟨w, Or.inl hw⟩
      · obtain ⟨w⟩ := inst
        exact ⟨w, Or.inr ha⟩
    · rcases hm with hg | hn
      · exact hg
      · exact absurd ha hn
  · rintro ⟨M1, htot, himp⟩ u ha
    obtain ⟨w, hw⟩ := htot u
    exact ⟨w, himp u w hw ha⟩

/-- `Bad = ∅` is the realizability condition of (f). -/
theorem bad_empty_iff : (∀ u, ¬ Bad A G V P T u) ↔ (∀ u, A1 A u → ∃ w, G1 A G V P T u w) := by
  constructor
  · intro h u ha
    exact Classical.byContradiction (fun hn => h u ⟨ha, hn⟩)
  · intro h u hb
    exact hb.2 (h u hb.1)

/-- A deterministic planner (a function) exists under the same condition. -/
theorem realizable_function [inst : Nonempty W] :
    (∀ u, A1 A u → ∃ w, G1 A G V P T u w) ↔ ∃ f : U → W, ∀ u, A1 A u → G1 A G V P T u (f u) := by
  constructor
  · intro h
    refine ⟨fun u => if hu : A1 A u then Classical.choose (h u hu) else Classical.choice inst, ?_⟩
    intro u hu
    simp only [hu]
    exact Classical.choose_spec (h u hu)
  · rintro ⟨f, hf⟩ u hu
    exact ⟨f u, hf u hu⟩

/-- The `Hence` paragraph is vacuous: off `A1`, every mission in `V` meets `G1`. -/
theorem G1_contains_vacuous_part : ∀ u w, ¬ A1 A u → V w → G1 A G V P T u w :=
  fun _ _ hn hv => ⟨hv, fun e _ hA _ _ => absurd ⟨e, hA⟩ hn⟩

/-- The `Hence` reading, made informative by restricting to `A1`: when every allowed `(u, e)` admits a
target outside `G`, some input in `A1` has a mission in `G1` iff some `u ∈ A1` and `w ∈ V` have
`A ⊆ P` and `A ∩ T ⊆ G` at `(u, w)`. -/
theorem hence_on_A1 (hbreak : ∀ u e, A u e → ∃ y, ¬ G u e y) :
    (∃ u w, A1 A u ∧ G1 A G V P T u w) ↔
    ∃ u w, A1 A u ∧ V w ∧ (∀ e, A u e → P w e) ∧ (∀ e y, A u e → T w e y → G u e y) := by
  constructor
  · rintro ⟨u, w, ha, g⟩
    refine ⟨u, w, ha, g.1, fun e hA => ?_, fun e y hA hT => g.2 e y hA g.1 (fun _ => hT)⟩
    apply Classical.byContradiction
    intro hP
    obtain ⟨y', hy'⟩ := hbreak u e hA
    exact hy' (g.2 e y' hA g.1 (fun hp => absurd hp hP))
  · rintro ⟨u, w, ha, hv, hP, hT⟩
    exact ⟨u, w, ha, hv, fun e y hA _ hG2 => hT e y hA (hG2 (hP e hA))⟩

/-! ## 2. The chain of tubes -/

/-- `R` (hence `G1`) is antitone in the tube. -/
theorem R_antitone {T T' : W → E → Y → Prop} (hT : ∀ w e y, T w e y → T' w e y) :
    ∀ u w, R A G V P T' u w → R A G V P T u w :=
  fun _ w h e y hA hV hG2 => h e y hA hV (fun hp => hT w e y (hG2 hp))

theorem G1_antitone {T T' : W → E → Y → Prop} (hT : ∀ w e y, T w e y → T' w e y) :
    ∀ u w, G1 A G V P T' u w → G1 A G V P T u w :=
  fun u w h => ⟨h.1, R_antitone A G V P hT u w h.2⟩

theorem Bad_monotone {T T' : W → E → Y → Prop} (hT : ∀ w e y, T w e y → T' w e y) :
    ∀ u, Bad A G V P T u → Bad A G V P T' u :=
  fun u hb => ⟨hb.1, fun ⟨w, hw⟩ => hb.2 ⟨w, G1_antitone A G V P hT u w hw⟩⟩

section Chain
variable (Tc : Nat → W → E → Y → Prop) (hc : ∀ j w e y, Tc j w e y → Tc (j + 1) w e y)
include hc

theorem chain_mono : ∀ i j, i ≤ j → ∀ w e y, Tc i w e y → Tc j w e y := by
  intro i j hij
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => intro w e y h; exact h
  | succ k ih =>
    intro w e y h
    exact hc (i + k) w e y (ih (Nat.le_add_right i k) w e y h)

/-- Certified indices form an up-set, so binary search for the least one is correct. -/
theorem certified_upset (M2 : W → E → Y → Prop) :
    ∀ i j, i ≤ j → (∀ w e y, M2 w e y → V w → P w e → Tc i w e y) →
      (∀ w e y, M2 w e y → V w → P w e → Tc j w e y) :=
  fun i j hij h w e y m v p => chain_mono Tc hc i j hij w e y (h w e y m v p)

/-- Along the chain, a smaller index gives a larger planner guarantee and a smaller Bad set. -/
theorem chain_G1 : ∀ i j, i ≤ j → ∀ u w, G1 A G V P (Tc j) u w → G1 A G V P (Tc i) u w :=
  fun i j hij => G1_antitone A G V P (chain_mono Tc hc i j hij)

theorem chain_Bad : ∀ i j, i ≤ j → ∀ u, Bad A G V P (Tc i) u → Bad A G V P (Tc j) u :=
  fun i j hij => Bad_monotone A G V P (chain_mono Tc hc i j hij)
end Chain

/-! ## 3. Quotient and the exact (inlined) planner guarantee -/

/-- Saturated AG quotient `(A,G)/(A2,G2)` (closed form of Incer et al., MEMOCODE 2018), over all ports:
assumption `A ∩ (G2 ∪ ¬A2)`, guarantee `(A2 ∩ G) ∪ ¬assumption`. -/
def Aq (u : U) (w : W) (e : E) (y : Y) : Prop := A u e ∧ (G2 P T w e y ∨ ¬ A2 V w)
def Gq (u : U) (w : W) (e : E) (y : Y) : Prop := (A2 V w ∧ G u e y) ∨ ¬ Aq A V P T u w e y

/-- A planner over `U × W` implements `(A1, G1)` iff it implements the quotient. -/
theorem planner_iff_quotient [Nonempty Y] (M1 : U → W → Prop) :
    (∀ u w, M1 u w → A1 A u → G1 A G V P T u w) ↔
    (∀ u w e y, M1 u w → Aq A V P T u w e y → Gq A G V P T u w e y) := by
  constructor
  · intro h u w e y hm hq
    have g1 := h u w hm ⟨e, hq.1⟩
    refine Or.inl ⟨g1.1, g1.2 e y hq.1 g1.1 ?_⟩
    rcases hq.2 with h2 | hn
    · exact h2
    · exact absurd g1.1 hn
  · intro h u w hm ⟨e0, hA0⟩
    have y0 : Y := Classical.ofNonempty
    have hV : A2 V w := by
      apply Classical.byContradiction
      intro hn
      rcases h u w e0 y0 hm ⟨hA0, Or.inr hn⟩ with hg | hg
      · exact hn hg.1
      · exact hg ⟨hA0, Or.inr hn⟩
    refine ⟨hV, fun e y hA _ hG2 => ?_⟩
    rcases h u w e y hm ⟨hA, Or.inl hG2⟩ with hg | hg
    · exact hg.2
    · exact absurd ⟨hA, Or.inl hG2⟩ hg

/-- Saturated `G1` is the universal projection over `E ∪ Y` of the quotient's maximal implementation. -/
theorem saturated_G1 [Nonempty Y] (u : U) (w : W) :
    (A1 A u → G1 A G V P T u w) ↔ ∀ e y, A u e → (A2 V w ∧ (G2 P T w e y → G u e y)) := by
  constructor
  · intro h e y hA
    have g := h ⟨e, hA⟩
    exact ⟨g.1, fun h2 => g.2 e y hA g.1 h2⟩
  · intro h ⟨e0, hA0⟩
    have y0 : Y := Classical.ofNonempty
    have hV := (h e0 y0 hA0).1
    exact ⟨hV, fun e y hA _ h2 => (h e y hA).2 h2⟩

/-- The exact planner guarantee with the controller inlined (the weakest assumption of `M2`). -/
def G1x (M2 : W → E → Y → Prop) (u : U) (w : W) : Prop := ∀ e y, A u e → M2 w e y → G u e y

/-- Exactness: the series composition meets `(A, G)` iff the planner stays inside `G1x`. -/
theorem exact_iff (M1 : U → W → Prop) (M2 : W → E → Y → Prop) :
    (∀ u w e y, M1 u w → M2 w e y → A u e → G u e y) ↔ ∀ u w, M1 u w → G1x A G M2 u w :=
  ⟨fun h u w hm e y hA h2 => h u w e y hm h2 hA, fun h u w e y hm h2 hA => h u w hm e y hA h2⟩

/-- Not inlining loses: if `M2` is certified, `G1 ⊆ V ∩ G1x`. -/
theorem G1_sub_exact (M2 : W → E → Y → Prop) (h2 : ∀ w e y, M2 w e y → V w → P w e → T w e y) :
    ∀ u w, G1 A G V P T u w → V w ∧ G1x A G M2 u w :=
  fun _ w g => ⟨g.1, fun e y hA hm => g.2 e y hA g.1 (fun hp => h2 w e y hm g.1 hp)⟩

/-- Inlining recovers the exact quotient on `V`: with `P := ⊤` and `T := M2`, `G1 = V ∩ G1x`. -/
theorem G1_inlined (M2 : W → E → Y → Prop) (u : U) (w : W) :
    G1 A G V (fun _ _ => True) M2 u w ↔ V w ∧ G1x A G M2 u w :=
  ⟨fun g => ⟨g.1, fun e y hA hm => g.2 e y hA g.1 (fun _ => hm)⟩,
   fun ⟨hv, hx⟩ => ⟨hv, fun e y hA _ h2 => hx e y hA (h2 trivial)⟩⟩

/-! ## 4. Side facts -/

/-- With `P` kept in the assumption, strict D2 forces `P` for every environment. -/
theorem strictD2_P (G1' : U → W → Prop) (h : ∀ u w e, G1' u w → V w ∧ P w e) :
    ∀ u w, G1' u w → ∀ e, P w e :=
  fun u w hg e => (h u w e hg).2

/-- Under the weaker side condition of `rule_general` (`A ∩ G1 ⊆ A2`), the maximum is `G1 ∪ ¬A1`:
every admissible `G1'` agrees with `G1` on `A1`, so the planner obligation is the same. -/
theorem maximal_weak (G1' : U → W → Prop)
    (h2 : ∀ u w e, A u e → G1' u w → A2 V w)
    (h3 : ∀ u w e y, A u e → G1' u w → A2 V w → G2 P T w e y → G u e y) :
    ∀ u w, G1' u w → A1 A u → G1 A G V P T u w :=
  fun u w hg ⟨e0, hA0⟩ => ⟨h2 u w e0 hA0 hg, fun e y hA hV hG => h3 u w e y hA hg hV hG⟩

/-- Keeping `P` in the assumption (`A2' := V ∩ P`, `G2' := T`) under the weak side condition gives the
planner guarantee `G1alt`. On `A1` it is contained in `G1`, and equal to it when every allowed `(u, e)`
admits some target outside `G`; otherwise `G1` can be larger. -/
def G1alt (u : U) (w : W) : Prop := ∀ e y, A u e → V w ∧ P w e ∧ (T w e y → G u e y)

theorem G1alt_sub [Nonempty Y] (u : U) (w : W) (ha : A1 A u) :
    G1alt A G V P T u w → G1 A G V P T u w := by
  intro h
  obtain ⟨e0, hA0⟩ := ha
  have y0 : Y := Classical.ofNonempty
  refine ⟨(h e0 y0 hA0).1, fun e y hA _ hG2 => ?_⟩
  have hh := h e y hA
  exact hh.2.2 (hG2 hh.2.1)

theorem G1_sub_alt (hbreak : ∀ u e, A u e → ∃ y, ¬ G u e y) (u : U) (w : W) :
    G1 A G V P T u w → G1alt A G V P T u w := by
  intro g e y hA
  refine ⟨g.1, ?_, fun hT => g.2 e y hA g.1 (fun _ => hT)⟩
  apply Classical.byContradiction
  intro hP
  obtain ⟨y', hy'⟩ := hbreak u e hA
  exact hy' (g.2 e y' hA g.1 (fun hp => absurd hp hP))

/-- The literal third condition without `G1` makes the controller keep `G` for every compatible `u`. -/
theorem literal_D3_uniform
    (h : ∀ u w e y, A u e → A2 V w → G2 P T w e y → G u e y) :
    ∀ w e y, A2 V w → G2 P T w e y → ∀ u, A u e → G u e y :=
  fun w e y hV hG u hA => h u w e y hA hV hG

/-- A controller guarantee mentioning `U` gains nothing: the obligation equals the one for `∀_U G2'`. -/
theorem G2_with_U (M2 : W → E → Y → Prop) (G2' : U → W → E → Y → Prop) :
    (∀ u w e y, M2 w e y → V w → G2' u w e y) ↔ (∀ w e y, M2 w e y → V w → ∀ u, G2' u w e y) :=
  ⟨fun h w e y m v u => h u w e y m v, fun h u w e y m v => h w e y m v u⟩

/-- A mentioning `Y` (e.g. a plant model): the construction and (c) go through unchanged. -/
theorem compose_A_with_Y (AY : U → E → Y → Prop) (GY : U → E → Y → Prop)
    (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (h1 : ∀ u w, M1 u w → (∃ e y, AY u e y) →
      (V w ∧ ∀ e y, AY u e y → V w → G2 P T w e y → GY u e y))
    (h2 : ∀ w e y, M2 w e y → V w → G2 P T w e y) :
    ∀ u w e y, M1 u w → M2 w e y → AY u e y → GY u e y := by
  intro u w e y m1 m2 hA
  have g := h1 u w m1 ⟨e, y, hA⟩
  exact g.2 e y hA g.1 (h2 w e y m2 g.1)

end Typed

/-! ## 5. The pointwise lemma

Static values are fixed (they are parameters of `α γ c d`); `Z` is the set of one tick's values of the
per-tick ports, a signal is `z : Nat → Z` read on ticks `0..H`. `Phi` is `Box α ∧ ⋀_{j<m} Dia γ_j`
(the static conjunct `β` is a side case and is omitted). -/

section Pointwise
attribute [local instance] Classical.propDecidable
variable {Z : Type} (H m : Nat) (α : Z → Prop) (γ : Nat → Z → Prop)

def Phi (z : Nat → Z) : Prop := (∀ t, t ≤ H → α (z t)) ∧ ∀ j, j < m → ∃ t, t ≤ H ∧ γ j (z t)

/-- The signal used in both proofs: witnesses on ticks `0..m-1`, then a fixed value. -/
def sig (wit : Nat → Z) (x : Z) (t : Nat) : Z := if t < m then wit t else x

theorem sig_lt {wit : Nat → Z} {x : Z} {t : Nat} (h : t < m) : sig m wit x t = wit t := by
  simp [sig, h]
theorem sig_ge {wit : Nat → Z} {x : Z} {t : Nat} (h : ¬ t < m) : sig m wit x t = x := by
  simp [sig, h]

/-- A choice of witnesses for the indices below `m`, with a default value elsewhere. -/
noncomputable def pick (p : Nat → Z → Prop) (hp : ∀ j, j < m → ∃ x, p j x) (x0 : Z) (j : Nat) : Z :=
  if h : j < m then Classical.choose (hp j h) else x0

theorem pick_spec (p : Nat → Z → Prop) (hp : ∀ j, j < m → ∃ x, p j x) (x0 : Z) {j : Nat}
    (h : j < m) : p j (pick m p hp x0 j) := by
  simp only [pick, h]
  exact Classical.choose_spec (hp j h)

theorem box_iff (c : Z → Prop) (hH : m ≤ H) :
    (∀ z, Phi H m α γ z → ∀ t, t ≤ H → c (z t)) ↔
    ((∀ x, ¬ α x) ∨ (∃ j, j < m ∧ ∀ x, α x → ¬ γ j x) ∨ (∀ x, α x → c x)) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hj : ∀ j, j < m → ∃ x, α x ∧ γ j x := fun j hj =>
      Classical.byContradiction (fun h' => hn (Or.inr (Or.inl ⟨j, hj, fun x hx hg => h' ⟨x, hx, hg⟩⟩)))
    have hc : ∃ x, α x ∧ ¬ c x := Classical.byContradiction (fun h' =>
      hn (Or.inr (Or.inr (fun x hx => Classical.byContradiction (fun hcx => h' ⟨x, hx, hcx⟩)))))
    obtain ⟨xs, hxa, hxc⟩ := hc
    let wit := pick m (fun j x => α x ∧ γ j x) hj xs
    have hwit : ∀ j, j < m → α (wit j) ∧ γ j (wit j) := fun j hj' => pick_spec m _ hj xs hj'
    have hz : Phi H m α γ (sig m wit xs) := by
      constructor
      · intro t _
        by_cases ht : t < m
        · rw [sig_lt m ht]; exact (hwit t ht).1
        · rw [sig_ge m ht]; exact hxa
      · intro j hjm
        refine ⟨j, Nat.le_trans (Nat.le_of_lt hjm) hH, ?_⟩
        rw [sig_lt m hjm]; exact (hwit j hjm).2
    have hm := h _ hz m hH
    rw [sig_ge m (Nat.lt_irrefl m)] at hm
    exact hxc hm
  · rintro (h0 | ⟨j, hj, hjα⟩ | hsub) z ⟨hα, hγ⟩ t ht
    · exact absurd (hα t ht) (h0 _)
    · obtain ⟨t', ht', hg⟩ := hγ j hj
      exact absurd hg (hjα _ (hα t' ht'))
    · exact hsub _ (hα t ht)

theorem dia_iff (d : Z → Prop) (hH : m ≤ H + 1) :
    (∀ z, Phi H m α γ z → ∃ t, t ≤ H ∧ d (z t)) ↔
    ((∀ x, α x → d x) ∨ ∃ j, j < m ∧ ∀ x, α x → γ j x → d x) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have h0 : ∃ x, α x ∧ ¬ d x := Classical.byContradiction (fun h' =>
      hn (Or.inl (fun x hx => Classical.byContradiction (fun hd => h' ⟨x, hx, hd⟩))))
    have hj : ∀ j, j < m → ∃ x, α x ∧ γ j x ∧ ¬ d x := fun j hj =>
      Classical.byContradiction (fun h' => hn (Or.inr ⟨j, hj, fun x hx hg =>
        Classical.byContradiction (fun hd => h' ⟨x, hx, hg, hd⟩)⟩))
    obtain ⟨x0, hx0a, hx0d⟩ := h0
    let wit := pick m (fun j x => α x ∧ γ j x ∧ ¬ d x) hj x0
    have hwit : ∀ j, j < m → α (wit j) ∧ γ j (wit j) ∧ ¬ d (wit j) :=
      fun j hj' => pick_spec m _ hj x0 hj'
    have hz : Phi H m α γ (sig m wit x0) := by
      constructor
      · intro t _
        by_cases ht : t < m
        · rw [sig_lt m ht]; exact (hwit t ht).1
        · rw [sig_ge m ht]; exact hx0a
      · intro j hjm
        refine ⟨j, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hjm hH), ?_⟩
        rw [sig_lt m hjm]; exact (hwit j hjm).2.1
    obtain ⟨t, _, hd⟩ := h _ hz
    by_cases ht : t < m
    · rw [sig_lt m ht] at hd; exact (hwit t ht).2.2 hd
    · rw [sig_ge m ht] at hd; exact hx0d hd
  · rintro (hsub | ⟨j, hj, hjd⟩) z ⟨hα, hγ⟩
    · exact ⟨0, Nat.zero_le H, hsub _ (hα 0 (Nat.zero_le H))⟩
    · obtain ⟨t, ht, hg⟩ := hγ j hj
      exact ⟨t, ht, hjd _ (hα t ht) hg⟩

end Pointwise

/-- The Box part fails for `H < m`: one tick, one Diamond `γ = {true}`, `α = ⊤`, `c = {true}`.
The implication holds over all signals, the pointwise condition does not. -/
theorem box_needs_H_ge_m :
    (∀ z : Nat → Bool, Phi 0 1 (fun _ => True) (fun _ x => x = true) z →
      ∀ t, t ≤ 0 → z t = true) ∧
    ¬ ((∀ _x : Bool, ¬ True) ∨ (∃ j, j < 1 ∧ ∀ x : Bool, True → ¬ x = true) ∨
       (∀ x : Bool, True → x = true)) := by
  constructor
  · intro z ⟨_, hγ⟩ t ht
    obtain ⟨t', ht', hg⟩ := hγ 0 (Nat.zero_lt_one)
    have h1 : t = 0 := Nat.le_zero.mp ht
    have h2 : t' = 0 := Nat.le_zero.mp ht'
    subst h1; subst h2; exact hg
  · rintro (h | ⟨_, _, h⟩ | h)
    · exact h true trivial
    · exact h true trivial rfl
    · exact Bool.false_ne_true (h false trivial)

/-- Windows matter: applying the Diamond formula when the consequent's deadline is shorter than the
antecedent's window is unsound. `H = 1`, `α = ⊤`, `γ = d = {true}`; the antecedent's Diamond ranges over
ticks `0..1`, the consequent's over tick `0` only. The pointwise condition `α ∩ γ ⊆ d` holds, yet the
signal `(false, true)` meets the antecedent and misses the deadline. -/
theorem dia_window_mismatch :
    (∀ x : Bool, True → x = true → x = true) ∧
    (Phi 1 1 (fun _ => True) (fun _ x => x = true) (fun t => decide (t = 1)) ∧
      ¬ ∃ t, t ≤ 0 ∧ decide (t = 1) = true) := by
  refine ⟨fun _ _ h => h, ⟨fun _ _ => trivial, fun _ _ => ⟨1, Nat.le_refl 1, rfl⟩⟩, ?_⟩
  rintro ⟨t, ht, h⟩
  have : t = 0 := Nat.le_zero.mp ht
  subst this
  exact absurd h (by decide)

/-- Diamond half with mismatched windows (`D2 < D1 ≤ H`): antecedent `Box_[0,H] α ∧ Dia_[0,D1] γ`,
consequent `Dia_[0,D2] d`. The valid condition is `α ⊆ d` or `α ∩ γ = ∅`; the disjunct `α ∩ γ ⊆ d` of
the full-window lemma is lost. -/
theorem dia_short_deadline {Z : Type} (H D1 D2 : Nat) (α γ d : Z → Prop) (h1 : D1 ≤ H) (h2 : D2 < D1) :
    (∀ z : Nat → Z, (∀ t, t ≤ H → α (z t)) → (∃ t, t ≤ D1 ∧ γ (z t)) → ∃ t, t ≤ D2 ∧ d (z t)) ↔
    ((∀ x, α x → d x) ∨ (∀ x, α x → ¬ γ x)) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have h0 : ∃ x, α x ∧ ¬ d x := Classical.byContradiction (fun h' =>
      hn (Or.inl (fun x hx => Classical.byContradiction (fun hd => h' ⟨x, hx, hd⟩))))
    have h1' : ∃ x, α x ∧ γ x := Classical.byContradiction (fun h' =>
      hn (Or.inr (fun x hx hg => h' ⟨x, hx, hg⟩)))
    obtain ⟨x0, ha0, hd0⟩ := h0
    obtain ⟨x1, ha1, hg1⟩ := h1'
    have key := h (fun t => if t = D1 then x1 else x0)
      (fun t _ => by by_cases ht : t = D1 <;> simp [ht, ha0, ha1])
      ⟨D1, Nat.le_refl D1, by simp [hg1]⟩
    obtain ⟨t, ht, hd⟩ := key
    have hne : t ≠ D1 := by omega
    simp [hne] at hd
    exact hd0 hd
  · rintro (hsub | hdis) z hα ⟨t, ht, hg⟩
    · exact ⟨0, Nat.zero_le D2, hsub _ (hα 0 (Nat.zero_le H))⟩
    · exact absurd hg (hdis _ (hα t (Nat.le_trans ht h1)))

/-! ## 6. Deadline to ticks (time in integer units, e.g. microseconds) -/

/-- Elapsed time at tick `t`: the sum of the first `t` tick lengths. -/
def elapsed (dt : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => elapsed dt t + dt t

theorem elapsed_le (dt : Nat → Nat) (dmax : Nat) (h : ∀ i, dt i ≤ dmax) :
    ∀ t, elapsed dt t ≤ t * dmax := by
  intro t
  induction t with
  | zero => simp [elapsed]
  | succ t ih => rw [elapsed, Nat.succ_mul]; exact Nat.add_le_add ih (h t)

theorem elapsed_ge (dt : Nat → Nat) (dmin : Nat) (h : ∀ i, dmin ≤ dt i) :
    ∀ t, t * dmin ≤ elapsed dt t := by
  intro t
  induction t with
  | zero => simp [elapsed]
  | succ t ih => rw [elapsed, Nat.succ_mul]; exact Nat.add_le_add ih (h t)

/-- Diamond with a deadline in `G`: a witness on a tick `t` with `t * dmax ≤ D` is within `D`. -/
theorem deadline_dia_sound (dt : Nat → Nat) (dmax D t : Nat) (h : ∀ i, dt i ≤ dmax)
    (ht : t * dmax ≤ D) : elapsed dt t ≤ D :=
  Nat.le_trans (elapsed_le dt dmax h t) ht

/-- Box over the first `D` time units in `G`: every tick inside `D` has `t * dmin ≤ D`, so the sound
tick window uses `dmin`, not `dmax`. -/
theorem deadline_box_sound (dt : Nat → Nat) (dmin D t : Nat) (h : ∀ i, dmin ≤ dt i)
    (ht : elapsed dt t ≤ D) : t * dmin ≤ D :=
  Nat.le_trans (elapsed_ge dt dmin h t) ht

/-- The `dmax` window is unsound for Box: with `dt ≡ 1`, `dmax = 2`, `D = 2`, tick 2 is inside the
deadline (elapsed 2) but outside the window `t * dmax ≤ D`. -/
theorem deadline_box_dmax_unsound :
    elapsed (fun _ => 1) 2 ≤ 2 ∧ ¬ (2 * 2 ≤ 2) := by
  refine ⟨by decide, by decide⟩

/-! ## 7. D3+ and `AG.rule_general` -/

section Bridge
open AG
variable {B : Type}

/-- Given the side condition `A ∩ G1 ⊆ A2` of `rule_general`, D3+ is exactly the side condition of
Guarantee Tightening applied to the composite guarantee `G1 ∩ G2`. -/
theorem D3plus_iff_tightening {A G1 A2 G2 G : Behaviours B} (hA2 : (A ∩ G1) ⊆ A2) :
    ((A ∩ G1 ∩ A2 ∩ G2) ⊆ G) ↔ (((G1 ∩ G2) ∩ A) ⊆ G) := by
  constructor
  · intro h x hx
    exact h x ⟨⟨⟨hx.2, hx.1.1⟩, hA2 x ⟨hx.2, hx.1.1⟩⟩, hx.1.2⟩
  · intro h x hx
    exact h x ⟨⟨hx.1.1.2, hx.2⟩, hx.1.1.1⟩

/-- Theorem (c) from the library rules: `rule_general`, then `rule_guarantee_tightening`. D2 is used
only through its consequence `A ∩ G1 ⊆ A2`. -/
theorem delegation_D3plus {M1 M2 A G A1 G1 A2 G2 : Behaviours B}
    (h1 : M1 ⊨ ⟨A1, G1⟩) (h2 : M2 ⊨ ⟨A2, G2⟩)
    (hD1 : A ⊆ A1) (hD2 : (A ∩ G1) ⊆ A2) (hD3 : (A ∩ G1 ∩ A2 ∩ G2) ⊆ G) :
    M1 ⊗ M2 ⊨ ⟨A, G⟩ :=
  rule_guarantee_tightening (rule_general h1 h2 hD1 hD2) ((D3plus_iff_tightening hD2).mp hD3)

/-- The typed construction, lifted to behaviours `U × W × E × Y`, meets the library's hypotheses. -/
theorem typed_meets_library {U W E Y : Type}
    (A : U → E → Prop) (G : U → E → Y → Prop) (V : W → Prop) (P : W → E → Prop)
    (T : W → E → Y → Prop) (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (h1 : ∀ u w, M1 u w → A1 A u → G1 A G V P T u w)
    (h2 : ∀ w e y, M2 w e y → A2 V w → G2 P T w e y) :
    let AL : Behaviours (U × W × E × Y) := fun x => A x.1 x.2.2.1
    let GL : Behaviours (U × W × E × Y) := fun x => G x.1 x.2.2.1 x.2.2.2
    let M1L : Behaviours (U × W × E × Y) := fun x => M1 x.1 x.2.1
    let M2L : Behaviours (U × W × E × Y) := fun x => M2 x.2.1 x.2.2.1 x.2.2.2
    M1L ⊗ M2L ⊨ ⟨AL, GL⟩ := by
  intro AL GL M1L M2L
  let A1L : Behaviours (U × W × E × Y) := fun x => A1 A x.1
  let G1L : Behaviours (U × W × E × Y) := fun x => G1 A G V P T x.1 x.2.1
  let A2L : Behaviours (U × W × E × Y) := fun x => A2 V x.2.1
  let G2L : Behaviours (U × W × E × Y) := fun x => G2 P T x.2.1 x.2.2.1 x.2.2.2
  have i1 : M1L ⊨ ⟨A1L, G1L⟩ := implements_iff.mpr (fun x hx => h1 _ _ hx.1 hx.2)
  have i2 : M2L ⊨ ⟨A2L, G2L⟩ := implements_iff.mpr (fun x hx => h2 _ _ _ hx.1 hx.2)
  exact delegation_D3plus i1 i2
    (fun x hx => D1 A x.1 x.2.2.1 hx)
    (fun x hx => D2 A G V P T x.1 x.2.1 hx.2)
    (fun x hx => D3plus A G V P T x.1 x.2.1 x.2.2.1 x.2.2.2 hx.1.1.1 hx.1.1.2 hx.1.2 hx.2)

end Bridge

end Deleg

/-! ## 8. Projection facts F2-F4 over a product of ports

Behaviours are dependent functions `σ : (i : Port) → Val i` (the product over ports, Finding 1.1). A set of
ports is a predicate `X : Port → Prop`. -/

section Projections
attribute [local instance] Classical.propDecidable
variable {Port : Type} {Val : Port → Type}

/-- `σ` and `τ` agree outside `X`. -/
def agreeOut (X : Port → Prop) (σ τ : (i : Port) → Val i) : Prop := ∀ i, ¬ X i → σ i = τ i

/-- `∃_X S`. -/
def exP (X : Port → Prop) (S : ((i : Port) → Val i) → Prop) (σ : (i : Port) → Val i) : Prop :=
  ∃ τ, agreeOut X σ τ ∧ S τ

/-- `∀_X S := ¬∃_X¬S`. -/
def allP (X : Port → Prop) (S : ((i : Port) → Val i) → Prop) (σ : (i : Port) → Val i) : Prop :=
  ¬ exP X (fun τ => ¬ S τ) σ

/-- `C` is over `Π ∖ X`: membership does not change when ports in `X` change. -/
def overCompl (X : Port → Prop) (C : ((i : Port) → Val i) → Prop) : Prop :=
  ∀ σ τ, agreeOut X σ τ → (C σ ↔ C τ)

theorem agreeOut_symm {X : Port → Prop} {σ τ : (i : Port) → Val i} (h : agreeOut X σ τ) :
    agreeOut X τ σ := fun i hi => (h i hi).symm

/-- F3, first half. -/
theorem F3a {X : Port → Prop} {C S : ((i : Port) → Val i) → Prop} (hC : overCompl X C) :
    (∀ σ, C σ → S σ) ↔ (∀ σ, C σ → allP X S σ) := by
  constructor
  · intro h σ hc ⟨τ, hag, hn⟩
    exact hn (h τ ((hC σ τ hag).mp hc))
  · intro h σ hc
    apply Classical.byContradiction
    intro hn
    exact h σ hc ⟨σ, fun _ _ => rfl, hn⟩

/-- F3, second half. -/
theorem F3b {X : Port → Prop} {C S : ((i : Port) → Val i) → Prop} (hC : overCompl X C) :
    (∀ σ, S σ → C σ) ↔ (∀ σ, exP X S σ → C σ) := by
  constructor
  · intro h σ ⟨τ, hag, hs⟩
    exact (hC σ τ hag).mpr (h τ hs)
  · intro h σ hs
    exact h σ ⟨σ, fun _ _ => rfl, hs⟩

/-- F4. -/
theorem F4 {X : Port → Prop} {C S : ((i : Port) → Val i) → Prop} (hC : overCompl X C) (σ : (i : Port) → Val i) :
    exP X (fun τ => C τ ∧ S τ) σ ↔ (C σ ∧ exP X S σ) := by
  constructor
  · rintro ⟨τ, hag, hc, hs⟩
    exact ⟨(hC σ τ hag).mpr hc, τ, hag, hs⟩
  · rintro ⟨hc, τ, hag, hs⟩
    exact ⟨τ, hag, (hC σ τ hag).mp hc, hs⟩

/-- The hypothesis of F3 is needed: one port `x`, `C = S = {x = 0}`, `X = {x}`. -/
theorem F3_needs_over :
    let X : Unit → Prop := fun _ => True
    let C : ((_ : Unit) → Nat) → Prop := fun σ => σ () = 0
    (∀ σ, C σ → C σ) ∧ ¬ (∀ σ, C σ → allP X C σ) := by
  intro X C
  refine ⟨fun _ h => h, fun h => ?_⟩
  exact h (fun _ => 0) rfl ⟨fun _ => 1, fun _ hi => absurd trivial hi, by simp [C]⟩

/-- The product structure behind F2: `∃_X ∃_{X'} = ∃_{X ∪ X'}`. -/
theorem exP_exP {X X' : Port → Prop} {S : ((i : Port) → Val i) → Prop} (σ : (i : Port) → Val i) :
    exP X (exP X' S) σ ↔ exP (fun i => X i ∨ X' i) S σ := by
  constructor
  · rintro ⟨τ, h1, ρ, h2, hs⟩
    refine ⟨ρ, fun i hi => ?_, hs⟩
    have hx : ¬ X i := fun h => hi (Or.inl h)
    have hx' : ¬ X' i := fun h => hi (Or.inr h)
    exact (h1 i hx).trans (h2 i hx')
  · rintro ⟨ρ, hag, hs⟩
    refine ⟨fun i => if X i then ρ i else σ i, fun i hi => by simp [hi], ρ, fun i hi => ?_, hs⟩
    by_cases hx : X i
    · simp [hx]
    · simp only [hx, ↓reduceIte]; exact hag i (fun h => h.elim hx hi)

/-- F2 for `∃`: if `S` is over `Π ∖ Y0` (unchanged by ports in `Y0`), then `∃_X S` is unchanged by ports
in `Y0` as well; i.e. `∃_X S` is over `Z ∖ X` when `S` is over `Z`. -/
theorem F2_ex {X Y0 : Port → Prop} {S : ((i : Port) → Val i) → Prop} (hS : overCompl Y0 S) :
    overCompl (fun i => Y0 i ∨ X i) (exP X S) := by
  intro σ τ hag
  constructor
  · rintro ⟨ρ, h1, hs⟩
    -- build ρ' agreeing with τ outside X, and with ρ outside Y0 ∪ X
    refine ⟨fun i => if X i then ρ i else τ i, fun i hi => by simp [hi], ?_⟩
    apply (hS ρ _ (fun i hi => ?_)).mp hs
    by_cases hx : X i
    · simp [hx]
    · simp only [hx, ↓reduceIte]; exact (h1 i hx).symm.trans (hag i (fun h => h.elim hi hx))
  · rintro ⟨ρ, h1, hs⟩
    refine ⟨fun i => if X i then ρ i else σ i, fun i hi => by simp [hi], ?_⟩
    apply (hS ρ _ (fun i hi => ?_)).mp hs
    by_cases hx : X i
    · simp [hx]
    · simp only [hx, ↓reduceIte]; exact (h1 i hx).symm.trans (hag i (fun h => h.elim hi hx)).symm
/-- F2 for `∀`, from F2 for `∃` and F0 (complement). -/
theorem F2_all {X Y0 : Port → Prop} {S : ((i : Port) → Val i) → Prop} (hS : overCompl Y0 S) :
    overCompl (fun i => Y0 i ∨ X i) (allP X S) := by
  have hn : overCompl Y0 (fun τ => ¬ S τ) := fun σ τ h => not_congr (hS σ τ h)
  intro σ τ hag
  exact not_congr (F2_ex hn σ τ hag)

end Projections

#print axioms Deleg.compose
#print axioms Deleg.realizable
#print axioms Deleg.planner_iff_quotient
#print axioms Deleg.box_iff
#print axioms Deleg.dia_iff
#print axioms Deleg.typed_meets_library
#print axioms F4
#print axioms F2_ex
