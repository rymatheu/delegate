module

public import DynamicalSystems.Mathlib.Analysis.ODE.RadialTruncation
-- the body of `radialTrunc` is needed for `radialTrunc_eq_smul`
import all DynamicalSystems.Mathlib.Analysis.ODE.RadialTruncation

/-!
# The radial truncation is a scaling

Moved here from the archive's `Flow.lean`, name and proof unchanged.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- The radial retraction is a scaling by `c ∈ [0, 1]`. -/
theorem radialTrunc_eq_smul {R : ℝ} (hR : 0 ≤ R) (y : (Fin 17 → ℝ)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ radialTrunc R y = c • y := by
  unfold radialTrunc
  split_ifs with hy
  · exact ⟨1, zero_le_one, le_rfl, (one_smul _ _).symm⟩
  · push Not at hy
    have : 0 < ‖y‖ := lt_of_le_of_lt hR hy
    exact ⟨R / ‖y‖, div_nonneg hR this.le, (div_le_one this).2 hy.le, rfl⟩

end

end Plant
