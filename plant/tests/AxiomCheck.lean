import Plant

/-! Axiom audit of the plant's main theorems: `lake env lean tests/AxiomCheck.lean` (after `lake build`). Only
`propext`, `Classical.choice`, `Quot.sound` are acceptable. The list follows the plant part of the archive's
`AxiomCheck.lean`; the theorems left out of this library (`OPEN.md`) are replaced by their real-valued counterparts
(`run_flow`, `run_qnormSq`, `run_const`, `sampleR_hover`), and the theorems added here follow. -/

open Plant

#print axioms kf_maxRPM_sq
#print axioms vf_lipschitz_ball
#print axioms vf_locallyLipschitz
#print axioms norm_vf_le
#print axioms vfT_lipschitz
#print axioms norm_le_box_of_scaledSol
#print axioms traj_hasDerivAt
#print axioms step_spec
#print axioms traj_unique
#print axioms step_unique
#print axioms step_eq_flowT
#print axioms qnormSq_const_of_solution
#print axioms qnormSq_step
#print axioms norm_traj_sub_le
#print axioms norm_traj_sub_le_ball
#print axioms norm_traj_sub_le_exp
#print axioms step_sub_eulerStep_le
#print axioms step_sub_eulerStep_le_ball
#print axioms backwardDiff_sub_specForce
#print axioms downAxis_quatOf
#print axioms vf_hover
#print axioms step_hover
#print axioms nextR_hover
#print axioms sampleR_hover
#print axioms run_flow
#print axioms run_qnormSq
#print axioms run_const
#print axioms torqueBd_alphaMax
#print axioms torqueBd_of_spread
#print axioms accel_le_mul
#print axioms WBd_trajA
#print axioms hasDerivAt_dn
#print axioms hasDerivAt_dnDot
#print axioms abs_dnDot_le
#print axioms abs_dnDDot_le
#print axioms traj_dn
#print axioms traj_pv_sharp
#print axioms step_pv_sharp
#print axioms traj_pv_first
#print axioms traj_pos_move
#print axioms step_pos_move
#print axioms vf_att_lipschitz
#print axioms norm_att_vf_le
#print axioms traj_qw_gronwall
#print axioms step_qw_gronwall
#print axioms traj_att_taylor
#print axioms wTA_one_alphaMax_le
#print axioms Cd_alphaMax_le
#print axioms wTA_one_spread_le
#print axioms Cd_spread_le

/-! Phase 3: theorems added in this library. -/

#print axioms clip01_mono
#print axioms thrust_mono
#print axioms wrench_eq_mix
#print axioms unmix_mix
#print axioms mix_unmix
#print axioms range_wrench
#print axioms accel_const_eq_grav_iff
#print axioms abs_accel_sub_le
#print axioms norm_vf_sub_input_le
#print axioms norm_traj_sub_traj_le
#print axioms norm_step_sub_step_le_exp
#print axioms norm_step_sub_input_le
#print axioms norm_step_sub_input_le_mul
#print axioms norm_step_sub_state_le
#print axioms step_lipschitzOnWith
#print axioms continuous_step
#print axioms continuous_step_uncurry
#print axioms spinSol_hasDerivAt
#print axioms traj_spin
#print axioms step_spin
#print axioms step_spin_vz
#print axioms spinState_step
#print axioms step_level
#print axioms step_level_vz
#print axioms step_level_hover_vz
#print axioms traj_freeFall_v
#print axioms step_freeFall
#print axioms vf_add_posVec
#print axioms step_add_posVec
#print axioms vf_yawRot
#print axioms traj_yawRot
#print axioms step_yawRot
#print axioms traj_v_dev_le
#print axioms traj_p_dev_le
#print axioms step_vz_mem
#print axioms step_v_sub_le
#print axioms stepN_add
#print axioms stepN_const
#print axioms run_stepN
#print axioms qnormSq_stepN
#print axioms stepN_hover
#print axioms stepN_yawRot
#print axioms stepN_level_vz
#print axioms stepN_level_pz
#print axioms trajN_sample
#print axioms trajN_hasDerivAt
