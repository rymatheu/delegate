import Contracts.Mission.SCurveTableNear

/-!
# The time stamps of the `add_segments` table

The end time of an entry is the previous end time plus the duration, rounded: it does not
decrease (`time_mono`), and for a ramp of duration `t_j` the `float` difference of consecutive end
times is within `2·10⁻⁶` of `t_j` (`time_dur`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

theorem time_mono {T d : Float32} (fT : T.IsFinite) (fd : d.IsFinite) (hT : |T.toReal| ≤ 100)
    (hd0 : 0 ≤ d.toReal) (hd1 : d.toReal ≤ 100) : T.toReal ≤ (T + d).toReal := by
  have hm : |T.toReal + d.toReal| ≤ maxFinite32 := by
    have : |T.toReal + d.toReal| ≤ 200 := by
      rw [abs_le] at hT ⊢; constructor <;> linarith
    have : (200 : ℝ) ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  exact (Float32.add_bracket fT fd hm fT).1 (by linarith)

theorem time_dur {T d : Float32} (fT : T.IsFinite) (fd : d.IsFinite) (hT : |T.toReal| ≤ 26)
    (hd0 : 0 ≤ d.toReal) (hd1 : d.toReal ≤ 1 / 4) :
    (T + d - T).IsFinite ∧ |(T + d - T).toReal - d.toReal| ≤ 2 / 10 ^ 6 := by
  have eT := B32.of_exact fT hT
  have ed := B32.of_exact fd (R := 1 / 4) (by rw [abs_of_nonneg hd0]; exact hd1)
  have hs : |T.toReal + d.toReal| ≤ 27 := by
    rw [abs_le] at hT ⊢; constructor <;> linarith
  have a1 := A32.add_c eT.1 ed.1 hs (e := 162 / 10 ^ 8) (by norm_num [capF]) (by norm_num)
  have hs2 : |T.toReal + d.toReal - T.toReal| ≤ 1 / 4 := by
    rw [show T.toReal + d.toReal - T.toReal = d.toReal by ring, abs_of_nonneg hd0]; exact hd1
  have a2 := A32.sub_c a1 eT.1 hs2 (e := 164 / 10 ^ 8) (by norm_num [capF]) (by norm_num)
  refine ⟨a2.1, ?_⟩
  have := a2.2
  rw [show T.toReal + d.toReal - T.toReal = d.toReal by ring] at this
  linarith

end SCT

end

end Contracts.Mission
