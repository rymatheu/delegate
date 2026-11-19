import Contracts.Track.Induction.Main
import Contracts.Track.Induction.InitWorld

/-!
# M9, part 6: the instance of `Pieces` (the open part of `track_contract`)

`pieces` is the one place where the open pieces of `track_contract` are `sorry`. Each field is
discharged by the milestone named in INDUCTION.md §3 (the finished theorems of the other
milestones enter in `Main.lean`: M8's `Pacing.pacing_course`, `Pacing.hold_course`,
`Pacing.rawScaler_ge`, `Pacing.pace_of`; M1/M2/Q5 in `Step.lean`).
`track_contract_proof` is `track_contract` from it.
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission

noncomputable section

/-- **The pieces of the mission flight.** Open: every field. -/
def pieces (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hM : MissionWorld w₀) (_hS : Plant.CopterSense sense32 senseP) (_hL : LibmSpec) :
    Pieces sense32 senseP w₀ where
  -- the interfaces (defined by M4, M5/M6, the navigator, M8, the C-series)
  wVs := wSv w₀
  etaHat := sorry
  AttInv := sorry
  YawInv := sorry
  NavInv := sorry
  CtrlInv := sorry
  sc := fun x t => (run w₀ x (t + 1)).wps._track_dt_scalar.toReal
  r := sorry
  q := fun x t => navProgress w₀ x t
  ar := sorry
  τv := fun x => climbTau w₀ x
  -- C16
  init_world := intOK_missionWorld hM
  init := sorry
  init_tube := sorry
  -- VERTICAL.md §7 / HORIZONTAL.md §7
  vglue := sorry
  wVs_def := fun _ _ => rfl
  ne_glue := sorry
  -- M4 and the heading subsystem
  attitude_tracks := sorry
  att_step := sorry
  att_rates := sorry
  yaw_step := sorry
  -- C-series code invariant
  ctrl_step := sorry
  -- navigator
  nav_step := sorry
  nav_bounds := sorry
  -- pacing: the code facts along the run (C15 glue of M8's per-tick lemmas)
  pace_filter := sorry
  pace_raw := sorry
  pace_s0 := sorry
  pace_q := fun x _ t _ => by
    show |navProgress w₀ x (t + 1) - navProgress w₀ x t -
      (run w₀ x (t + 1 + 1)).wps._track_dt_scalar.toReal| ≤ 1 / 10 ^ 7
    rw [navProgress, navProgress, Finset.sum_range_succ _ (t + 1), run_eq_ctrlWorld]
    norm_num
  pace_q0 := fun x _ => by
    show |navProgress w₀ x 0 - (run w₀ x (0 + 1)).wps._track_dt_scalar.toReal| ≤ 1 / 10 ^ 7
    rw [navProgress, Finset.sum_range_one, run_eq_ctrlWorld]
    norm_num
  pace_scaler := sorry
  -- pacing: the navigator's progress and `τ_v` (the escape is the hypothesis `ClimbEscape`)
  q_nav := fun _ _ _ _ => rfl
  τv_nav := fun _ _ => rfl
  -- pacing: the course (M7)
  pace_gaps := sorry
  pace_speed := sorry
  pace_win := sorry
  pace_end := sorry
  -- certificates and the certified nominal
  peakV := sorry
  gainV := sorry
  peakH := sorry
  gainH := sorry
  nom_box := sorry
  nom_T1 := sorry
  nom_climbout := sorry
  nom_w07 := sorry
  nom_corner := sorry
  nom_win0 := sorry
  nom_along := sorry
  nom_rest := sorry
  nom_complete := sorry
  -- the hold
  loiter_nav := sorry

/-- `track_contract`, from the pieces. -/
theorem track_contract_proof (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hM : MissionWorld w₀) (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hE : ClimbEscape sense32 senseP w₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩ :=
  track_contract_of_pieces sense32 senseP w₀ (pieces sense32 senseP w₀ hM hS hL) hM hS hL hE

end

end Contracts.Track.Induction
