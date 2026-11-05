import Contracts
import Contracts.Mission.Theorem
import Contracts.Mission.NavLeg
import Contracts.Mission.NavBlend

/-! Axiom audit of the plant's main theorems: `lake env lean AxiomCheck.lean`. Recorded in
`PLANT.md`; only `propext`, `Classical.choice`, `Quot.sound` are acceptable. -/

open Contracts.Plant

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
#print axioms eulerStep_pv_quatOf
#print axioms vf_hover
#print axioms step_hover
#print axioms nextR_hover
#print axioms sample_hover
#print axioms Mplant_flow
#print axioms Mplant_qnormSq
#print axioms Mplant_const

/-! Mission (`MISSION.md`). `mission_contract` depends on `sorryAx` through the two open
sub-contracts `nav_contract` and `track_contract`; everything else below must be clean. -/

open Contracts.Mission

#print axioms mission_contract
#print axioms nav_contract
#print axioms track_contract
#print axioms mission_of_sub
#print axioms mission_nonvacuous
#print axioms mission_of_guarantees
#print axioms navA_of_loop
#print axioms arrive_lemma
#print axioms arrive_of_err
#print axioms safe_of_parts
#print axioms polyDist_of_inColumn
#print axioms down_of_inSafe
#print axioms sat_imp_iff
#print axioms allowance_rule
#print axioms span_legs
#print axioms horizonTicks_eq
#print axioms hρδ
#print axioms hδ
#print axioms mem_Mplant_iff_plant
#print axioms traceValues_posTarget
#print axioms actVec_toArray
#print axioms tickSpecForce_startP
#print axioms yawQuat_normSq
#print axioms missionParams_of_ok
#print axioms rPass_mid
#print axioms rPass_w7

/-! Navigator milestone (a): the loiter target bound (`NavStop.lean`). -/

#print axioms invSqrt_15
#print axioms stop_NE_bound
#print axioms stop_D_bound
#print axioms loiter_dest_bound
#print axioms loiter_dest_near_w7

/-! Navigator milestones (b) and (c), geometric parts (`NavLeg.lean`, `NavBlend.lean`). -/

#print axioms len_approx
#print axioms axis_proj
#print axioms proj_straight_near
#print axioms scurve_pos_nonneg
#print axioms move_from_near
#print axioms blend_near_first
#print axioms blend_near_second
#print axioms blend_near

/-! The sharp one-period step (`Contracts/Plant/Sharp.lean`, milestone M3). -/

#print axioms Contracts.Plant.torqueBd_alphaMax
#print axioms Contracts.Plant.torqueBd_of_spread
#print axioms Contracts.Plant.accel_le_mul
#print axioms Contracts.Plant.WBd_trajA
#print axioms Contracts.Plant.hasDerivAt_dn
#print axioms Contracts.Plant.hasDerivAt_dnDot
#print axioms Contracts.Plant.abs_dnDot_le
#print axioms Contracts.Plant.abs_dnDDot_le
#print axioms Contracts.Plant.traj_dn
#print axioms Contracts.Plant.traj_pv_sharp
#print axioms Contracts.Plant.step_pv_sharp
#print axioms Contracts.Plant.traj_pv_first
#print axioms Contracts.Plant.traj_pos_move
#print axioms Contracts.Plant.step_pos_move
#print axioms Contracts.Plant.vf_att_lipschitz
#print axioms Contracts.Plant.norm_att_vf_le
#print axioms Contracts.Plant.traj_qw_gronwall
#print axioms Contracts.Plant.step_qw_gronwall
#print axioms Contracts.Plant.traj_att_taylor
#print axioms Contracts.Plant.wTA_one_alphaMax_le
#print axioms Contracts.Plant.Cd_alphaMax_le
#print axioms Contracts.Plant.wTA_one_spread_le
#print axioms Contracts.Plant.Cd_spread_le
