-- Typed check of the delegation construction: ports are separate types, so the alphabet
-- of every contract is enforced by its type signature.
section
variable {U W E Y : Type}
variable (A : U → E → Prop) (G : U → E → Y → Prop)
variable (V : W → Prop) (P : W → E → Prop) (T : W → E → Y → Prop)

def A1 (u : U) : Prop := ∃ e, A u e
def A2 (w : W) : Prop := V w
def G2 (w : W) (e : E) (y : Y) : Prop := P w e → T w e y
def G1 (u : U) (w : W) : Prop :=
  V w ∧ ∀ e y, A u e → V w → G2 P T w e y → G u e y

theorem D1 : ∀ u e, A u e → A1 A u := fun u e h => ⟨e, h⟩
theorem D2 : ∀ u w, G1 A G V P T u w → A2 V w := fun _ _ h => h.1
theorem D3plus : ∀ u w e y, A u e → G1 A G V P T u w → A2 V w → G2 P T w e y → G u e y :=
  fun _ _ e y hA hG1 hA2 hG2 => hG1.2 e y hA hA2 hG2

-- maximality: any G1' over U,W meeting D2 and D3+ is contained in G1
theorem maximal (G1' : U → W → Prop)
    (h2 : ∀ u w, G1' u w → V w)
    (h3 : ∀ u w e y, A u e → G1' u w → V w → G2 P T w e y → G u e y) :
    ∀ u w, G1' u w → G1 A G V P T u w :=
  fun u w h => ⟨h2 u w h, fun e y hA hV hG => h3 u w e y hA h hV hG⟩

-- M2's obligation is unchanged by moving P into the guarantee
theorem obligation (M2 : W → E → Y → Prop) :
    (∀ w e y, M2 w e y → V w → G2 P T w e y) ↔ (∀ w e y, M2 w e y → V w → P w e → T w e y) :=
  Iff.rfl

-- composition: series M1 ; M2 implements (A, G)
theorem compose (M1 : U → W → Prop) (M2 : W → E → Y → Prop)
    (h1 : ∀ u w, M1 u w → A1 A u → G1 A G V P T u w)
    (h2 : ∀ w e y, M2 w e y → A2 V w → G2 P T w e y) :
    ∀ u w e y, M1 u w → M2 w e y → A u e → G u e y := by
  intro u w e y m1 m2 hA
  have g1 := h1 u w m1 (D1 A u e hA)
  exact D3plus A G V P T u w e y hA g1 (D2 A G V P T u w g1) (h2 w e y m2 (D2 A G V P T u w g1))

-- literal D3 (without G1) forces G2 to deliver G for every u compatible with e
theorem literal_D3_uniform
    (h : ∀ u w e y, A u e → A2 V w → G2 P T w e y → G u e y) :
    ∀ w e y, A2 V w → G2 P T w e y → ∀ u, A u e → G u e y :=
  fun w e y hV hG u hA => h u w e y hA hV hG
end
