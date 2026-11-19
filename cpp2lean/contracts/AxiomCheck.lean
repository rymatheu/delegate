import Contracts
import Contracts.Mission.Theorem
import Contracts.Mission.NavLeg
import Contracts.Mission.NavBlend
import Contracts.Quick.Order
import Contracts.Quick.Mixer
import Contracts.Quick.Rates
import Contracts.Track.VerticalSCurve
import Contracts.Track.Actuators
import Contracts.Track.Integrators
import Contracts.Track.FloatLib
import FloatModel.Err
import Contracts.Quick.Tilt
import Contracts.Track.Integrators2D
import Contracts.Track.HorizontalCourse
import Contracts.Track.CtrlHorizontalTick
import Contracts.Track.PacingArrive
import Contracts.Track.Induction.Instance
import Contracts.Track.CtrlVerticalNav
import Contracts.Track.Reach.Loop
import Contracts.Track.Reach.GlueLoop
import Contracts.Track.Reach.LegBox
import Contracts.Track.Reach.Leg3Box
import Contracts.Invariant
import Contracts.Track.Reach.Safe3
import Contracts.Track.Reach.Hover

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

/-! Quick controller-only contracts (`QUICK.md`). Q5: the mission runs in order. -/

#print axioms Contracts.Quick.mission_in_order
#print axioms Contracts.Quick.mission_in_order_Mctrl
#print axioms Contracts.Quick.mission_start_of_construct
#print axioms Contracts.Quick.mission_update_spec

/-! Quick Q1 (`Mixer.lean`) and Q2 (`Rates.lean`): the clamps that exist. -/

#print axioms Contracts.Quick.rate_pid_nonfinite
#print axioms Contracts.Quick.rate_controller_nonfinite
#print axioms Contracts.Quick.set_throttle_avg_max_unit01
#print axioms Contracts.Quick.update_throttle_filter_out
#print axioms Contracts.Quick.ang_vel_limit_z
#print axioms Contracts.Quick.ang_vel_limit_x_single
#print axioms Contracts.Quick.ang_vel_limit_y_single

/-! Track M5, the vertical channel (`VERTICAL.md`, `Contracts/Track/Vertical*.lean`): the linear
model, the Lyapunov certificate, the discrete ISS bound, the ℓ1 gain and the S-curve climb bound.
Kernel checks use `decide +kernel` (no `native_decide`). -/

#print axioms Contracts.Track.Vertical.tick_eq
#print axioms Contracts.Track.Vertical.errOf_absTick
#print axioms Contracts.Track.Vertical.comparison
#print axioms Contracts.Track.Vertical.certV
#print axioms Contracts.Track.Vertical.Pv_posDef
#print axioms Contracts.Track.Vertical.V_A
#print axioms Contracts.Track.Vertical.sq_ez_le
#print axioms Contracts.Track.Vertical.V_iss
#print axioms Contracts.Track.Vertical.V_traj_le
#print axioms Contracts.Track.Vertical.ez_traj_le
#print axioms Contracts.Track.Vertical.ez_traj_le_const
#print axioms Contracts.Track.Vertical.XA_close
#print axioms Contracts.Track.Vertical.l1_gain
#print axioms Contracts.Track.Vertical.errResp_eq_code
#print axioms Contracts.Track.Vertical.bang_bound
#print axioms Contracts.Track.Vertical.bang_bound_L
#print axioms Contracts.Track.Vertical.scurve_bound
#print axioms Contracts.Track.Vertical.scurve_climb
#print axioms Contracts.Track.Vertical.errResp_add
#print axioms Contracts.Track.Vertical.tube_bound

-- Track M1/M2 and the float layer (TRACK_PLAN.md P1, M1, M2; FLOAT.md)
#print axioms Contracts.Track.actuators_in_unit
#print axioms Contracts.Track.tick_actOK
#print axioms Contracts.Track.tickT_actOK
#print axioms Contracts.Track.integrators_bounded
#print axioms Contracts.Track.intOK_tick
#print axioms Contracts.Track.intOK_takeover
#print axioms Contracts.Track.Pos.posIB_D_update_controller
#print axioms Float32.cvl_between
#print axioms Float32.cvl_symm
#print axioms Float32.mid_between
#print axioms Float32.between_of_not_lt_of_not_gt
#print axioms Float32.Near.add
#print axioms Float32.Near.mul
#print axioms Float32.Near.div
#print axioms Float32.Near.sqrt
#print axioms Float.Near.mul
#print axioms Float32.two32
#print axioms Contracts.Track.FloatLib.cvl_toReal

/-! Quick Q2 (`Rates.lean`, scaling branch) and Q3 (`Tilt.lean`): the rate and lean limiters. -/

#print axioms Contracts.Quick.ang_vel_limit_xy
#print axioms Contracts.Quick.flen_ge
#print axioms Contracts.Quick.limit_length_bound
#print axioms Contracts.Quick.within_bound
#print axioms Contracts.Quick.limit_accel_xy_bound

-- Track M1 for the mission world, M2 for the 2D integrator
#print axioms Contracts.Track.actuators_in_unit_mission
#print axioms Contracts.Track.actOK_missionWorld
#print axioms Contracts.Track.TwoD.VB_update_i
#print axioms Contracts.Track.TwoD.VB_set_integrator
#print axioms Contracts.Track.TwoD.VB_reset_I
#print axioms Contracts.Track.TwoD.limit_length_keeps_nan

/-! Track M6, the horizontal channel (`HORIZONTAL.md`, `Contracts/Track/Horizontal*.lean`): the
per-axis model with the attitude-lag interface, its Lyapunov certificate, the certified course
response of legs 1–7 and the corner property at `w₁ … w₆`. -/

#print axioms Contracts.Track.Horizontal.tick_eq
#print axioms Contracts.Track.Horizontal.errOf_absTick
#print axioms Contracts.Track.Horizontal.errResp_eq_code
#print axioms Contracts.Track.Horizontal.certV
#print axioms Contracts.Track.Horizontal.Ph_posDef
#print axioms Contracts.Track.Horizontal.V_A
#print axioms Contracts.Track.Horizontal.sq_e_le
#print axioms Contracts.Track.Horizontal.V_iss
#print axioms Contracts.Track.Horizontal.e_traj_le
#print axioms Contracts.Track.Horizontal.course_norm
#print axioms Contracts.Track.Horizontal.course_N
#print axioms Contracts.Track.Horizontal.course_E
#print axioms Contracts.Track.Horizontal.corner_vehicle
#print axioms Contracts.Track.Horizontal.corner_transfer
#print axioms Contracts.Track.Horizontal.course_tube

/-! Track M6, C-series of the horizontal controller (`CTRL_HORIZONTAL.md`,
`Contracts/Track/CtrlHorizontal*.lean`); `LibmSpec` enters as an argument. -/

#print axioms Contracts.Track.HCtl.flen_le
#print axioms Contracts.Track.HCtl.limit_length_inactive
#print axioms Contracts.Track.HCtl.limit_accel_xy_inactive
#print axioms Contracts.Track.HCtl.alpha5
#print axioms Contracts.Track.HCtl.pid_spec
#print axioms Contracts.Track.HCtl.p_spec
#print axioms Contracts.Track.HCtl.ne_spec
#print axioms Contracts.Track.HCtl.rows_compose
#print axioms Contracts.Track.HCtl.estimates_ne_world
#print axioms Contracts.Track.HCtl.thrust_xy
#print axioms Contracts.Track.HCtl.axis_tick
#print axioms Contracts.Track.HCtl.horizontal_tick_eq
#print axioms Contracts.Track.HCtl.d_frame
#print axioms Contracts.Track.HCtl.horizontal_tick_eq_D

/-! Track M8, target pacing (`PACING.md`, `Contracts/Track/Pacing*.lean`); `LibmSpec` enters as an
argument (`hold_w7`, `hold_course`). -/

#print axioms Contracts.Track.Pacing.advance_track_dt_scalar
#print axioms Contracts.Track.Pacing.rawScaler_unit
#print axioms Contracts.Track.Pacing.rawScaler_ge
#print axioms Contracts.Track.Pacing.rawScaler_ge_iso
#print axioms Contracts.Track.Pacing.alpha_eval
#print axioms Contracts.Track.Pacing.filter_step
#print axioms Contracts.Track.Pacing.code_filter_step
#print axioms Contracts.Track.Pacing.filter_bounds
#print axioms Contracts.Track.Pacing.deficit_sum
#print axioms Contracts.Track.Pacing.deficit_decay
#print axioms Contracts.Track.Pacing.stretch_bound
#print axioms Contracts.Track.Pacing.stretch_course
#print axioms Contracts.Track.Pacing.prog_step
#print axioms Contracts.Track.Pacing.leg_arrive
#print axioms Contracts.Track.Pacing.leg0_arrive
#print axioms Contracts.Track.Pacing.chain_reach
#print axioms Contracts.Track.Pacing.pacing_reach
#print axioms Contracts.Track.Pacing.rawScaler_ge_course
#print axioms Contracts.Track.Pacing.pace_of
#print axioms Contracts.Track.Pacing.pacing_course
#print axioms Contracts.Track.Pacing.hold_w7
#print axioms Contracts.Track.Pacing.hold_course

/-! Track M9, the induction (`INDUCTION.md`, `Contracts/Track/Induction/*.lean`): sorry-free from
the pieces; `track_contract_proof` carries the `sorry`s of the `pieces` instance. -/

#print axioms Contracts.Track.Induction.hidden_run
#print axioms Contracts.Track.Induction.tube_out
#print axioms Contracts.Track.Induction.τV_spec
#print axioms Contracts.Track.Induction.τH_spec
#print axioms Contracts.Track.Induction.axis_dev
#print axioms Contracts.Track.Induction.wHβ_bound
#print axioms Contracts.Track.Induction.prow_le
#print axioms Contracts.Track.Induction.βcode_le
#print axioms Contracts.Track.Induction.wV_bound
#print axioms Contracts.Track.Induction.world_all
#print axioms Contracts.Track.Induction.inv_zero
#print axioms Contracts.Track.Induction.inv_succ
#print axioms Contracts.Track.Induction.inv_all
#print axioms Contracts.Track.Induction.pace_run
#print axioms Contracts.Track.Induction.phase_r
#print axioms Contracts.Track.Induction.reach_chain
#print axioms Contracts.Track.Induction.hold
#print axioms Contracts.Track.Induction.ψtrack_of_inv
#print axioms Contracts.Track.Induction.track_contract_of_pieces
#print axioms Contracts.Track.Induction.track_contract_proof

/-! Vertical controller lemmas (C1, C5, C6, C7, C12; `CTRL_VERTICAL.md`). Only `propext`,
`Classical.choice`, `Quot.sound`; `LibmSpec` enters as an argument. -/

#print axioms Contracts.Track.CtrlV.estimates
#print axioms Contracts.Track.CtrlV.pos_p
#print axioms Contracts.Track.CtrlV.vel_pi
#print axioms Contracts.Track.CtrlV.accel_pid
#print axioms Contracts.Track.CtrlV.boost_A32
#print axioms Contracts.Track.CtrlV.throttle_filter
#print axioms Contracts.Track.CtrlV.dctrl_thr
#print axioms Contracts.Track.CtrlV.vtick_real
#print axioms Contracts.Track.CtrlV.vertical_tick_eq
#print axioms Contracts.Track.Horizontal.corner_vehicle_106
#print axioms Contracts.Track.Horizontal.corner_vehicle_105
#print axioms Contracts.Track.Horizontal.corner_vehicle_per
#print axioms Contracts.Track.Horizontal.corner_vehicle_per_105
#print axioms Contracts.Track.CtrlV.accel_pid2
#print axioms Contracts.Track.CtrlV.vel_pi2
#print axioms Contracts.Track.CtrlV.throttle_filter2
#print axioms Contracts.Track.CtrlV.boost_c
#print axioms Contracts.Track.CtrlV.dctrl2_thr
#print axioms Contracts.Track.CtrlV.vtick_split
#print axioms Contracts.Track.CtrlV.vertical_tick_rel
#print axioms Contracts.Track.CtrlV.vertical_tick_split

/-! M9, the escape of the climb as the hypothesis `ClimbEscape` (no new axioms). -/
#print axioms Contracts.Track.Induction.run_eq_ctrlWorld
#print axioms Contracts.Track.Induction.pace_esc_of
#print axioms Contracts.Track.CtrlV.nf_mission_update
#print axioms Contracts.Track.CtrlV.vf_replayPos
#print axioms Contracts.Track.CtrlV.mission_update_steady
#print axioms Contracts.Track.CtrlV.navV_of_logs
#print axioms Contracts.Track.Induction.intOK_missionWorld

-- REACH.md: the attitude certificate, the composite ISS, liveness, reach (milestones 1-4)
#print axioms Contracts.Track.AttJ.certA0
#print axioms Contracts.Track.AttJ.certA1
#print axioms Contracts.Track.AttJ.V_A
#print axioms Contracts.Track.AttJ.V_iss_sw
#print axioms Contracts.Track.AttJ.V_traj_sw
#print axioms Contracts.Track.AttJ.out_sq_le
#print axioms Contracts.Track.AttJ.sq_e_le
#print axioms Contracts.Track.AttJ.sq_a_le
#print axioms Contracts.Track.Reach.Vc_step
#print axioms Contracts.Track.Reach.Vc_step_join
#print axioms Contracts.Track.Reach.Vc_traj
#print axioms Contracts.Track.Reach.pos_sq_le
#print axioms Contracts.Track.Reach.hover_pes_model
#print axioms Contracts.Track.Reach.c_hover_le
#print axioms Contracts.Track.Reach.track_iss_model
#print axioms Contracts.Track.Reach.code_filter_nonneg
#print axioms Contracts.Track.Reach.liveness
#print axioms Contracts.Track.Reach.liveness_code
#print axioms Contracts.Track.Reach.passes_or_stalls
#print axioms Contracts.Track.Reach.joint_stall_eq
#print axioms Contracts.Track.Reach.vert_stall_eq
#print axioms Contracts.Track.Reach.stall_dev
#print axioms Contracts.Track.Reach.stall_ratio
#print axioms Contracts.Track.Reach.stall_ratio_ge_one
#print axioms Contracts.Track.Reach.stall_needs
#print axioms Contracts.Track.Reach.asymptotic_gain
#print axioms Contracts.Track.Reach.stall_scaler_ge
#print axioms Contracts.Track.Reach.stall_scaler_horizontal
#print axioms Contracts.Track.Reach.reach_model
#print axioms Contracts.Track.Reach.waypoint_reach_nonvacuous
#print axioms Contracts.Track.Reach.hover_practically_exponentially_stable
#print axioms Contracts.Track.Reach.waypoint_reach_of_facts

-- REACH.md §8: the glue (`HoverGlue` refuted, the tick split, the readouts, the tube-form hover theorems)
#print axioms Contracts.Track.Reach.not_hoverGlue
#print axioms Contracts.Track.Reach.hoverGlue_hyps_false
#print axioms Contracts.Track.Reach.drift_north_ge
#print axioms Contracts.Track.Reach.quant_V_ge
#print axioms Contracts.Track.Reach.c₀_le_of_hyps
#print axioms Contracts.Track.Reach.ball_route_floor
#print axioms Contracts.Track.Reach.Glue.tick_split
#print axioms Contracts.Track.Reach.Glue.tick_hold
#print axioms Contracts.Track.Reach.Glue.tick_hold_ps
#print axioms Contracts.Track.Reach.Glue.offZ_tick_hold
#print axioms Contracts.Track.Reach.Glue.dt_first_eq
#print axioms Contracts.Track.Reach.Glue.schedW_loop_time
#print axioms Contracts.Track.Reach.Glue.filt_tick
#print axioms Contracts.Track.Reach.Glue.act_tick
#print axioms Contracts.Track.Reach.Glue.hmix_of_spec
#print axioms Contracts.Track.Reach.Glue.navV_hold
#print axioms Contracts.Track.Reach.Glue.ne_desired
#print axioms Contracts.Track.Reach.Glue.ne_posd_val
#print axioms Contracts.Track.Reach.Glue.nef_D
#print axioms Contracts.Track.Reach.Glue.neGlue_hold
#print axioms Contracts.Track.Reach.Glue.chan_tube
#print axioms Contracts.Track.Reach.Glue.chan_tube_gen
#print axioms Contracts.Track.Reach.Glue.regionV
#print axioms Contracts.Track.Reach.Glue.regionH
#print axioms Contracts.Track.Reach.Glue.hover_box
#print axioms Contracts.Track.Reach.Glue.hover_box_gen
#print axioms Contracts.Track.Reach.Glue.respV_decay
#print axioms Contracts.Track.Reach.Glue.respH_decay
#print axioms Contracts.Track.Reach.Glue.freeV_decay
#print axioms Contracts.Track.Reach.Glue.freeH_decay
#print axioms Contracts.Track.Reach.Glue.ξV_pos
#print axioms Contracts.Track.Reach.Glue.ξH_pos
#print axioms Contracts.Track.Reach.Glue.hover_tube_axes
#print axioms Contracts.Track.Reach.Glue.hover_practically_exponentially_stable_tube
#print axioms Contracts.Track.Reach.Glue.hover_practically_exponentially_stable_gen
#print axioms Contracts.Track.Reach.Glue.hover_hold

/-! The leg theorem (REACH.md §9): `Contracts/Track/Reach/Leg.lean`, `Leg{Tube,GainsData,Gains,Nav,Hold,Box}.lean`
(repaired 2026-11-06: the velocity defect `d₂ ≤ 8·10⁻⁴`, completion by decay, `legH` removed). -/
#print axioms Contracts.Track.Reach.Leg.waypoint_reach_h_nonvacuous
#print axioms Contracts.Track.Reach.Leg.rsp_single
#print axioms Contracts.Track.Reach.Leg.forced_eq
#print axioms Contracts.Track.Reach.Leg.free_le
#print axioms Contracts.Track.Reach.Leg.conv_le
#print axioms Contracts.Track.Reach.Leg.out_le
#print axioms Contracts.Track.Reach.Leg.env_le
#print axioms Contracts.Track.Reach.Leg.env_const
#print axioms Contracts.Track.Reach.Leg.env_tail
#print axioms Contracts.Track.Reach.Leg.Ah_vAcc
#print axioms Contracts.Track.Reach.Leg.outH4_vAcc
#print axioms Contracts.Track.Reach.Leg.vAcc_nonneg
#print axioms Contracts.Track.Reach.Leg.zeta_step
#print axioms Contracts.Track.Reach.Leg.Ah_u2
#print axioms Contracts.Track.Reach.Leg.outH4_u2
#print axioms Contracts.Track.Reach.Leg.u2_abs
#print axioms Contracts.Track.Reach.Leg.u2a_nonneg
#print axioms Contracts.Track.Reach.Leg.zeta2_step
#print axioms Contracts.Track.Reach.Leg.Ah_row7
#print axioms Contracts.Track.Reach.Leg.rate_u2
#print axioms Contracts.Track.Reach.Leg.gainU2
#print axioms Contracts.Track.Reach.Leg.gH0
#print axioms Contracts.Track.Reach.Leg.gH1
#print axioms Contracts.Track.Reach.Leg.gV0
#print axioms Contracts.Track.Reach.Leg.gV1
#print axioms Contracts.Track.Reach.Leg.env_const_neg
#print axioms Contracts.Track.Reach.Leg.env_tail_neg
#print axioms Contracts.Track.Reach.Leg.env_tail2
#print axioms Contracts.Track.Reach.Leg.env_tail2_neg
#print axioms Contracts.Track.Reach.Leg.env_tail_l1
#print axioms Contracts.Track.Reach.Leg.env_tail_l1_neg
#print axioms Contracts.Track.Reach.Leg.boxH_close
#print axioms Contracts.Track.Reach.Leg.boxC1_close
#print axioms Contracts.Track.Reach.Leg.boxRate_close
#print axioms Contracts.Track.Reach.Leg.boxV_close
#print axioms Contracts.Track.Reach.Leg.εHL_nonneg
#print axioms Contracts.Track.Reach.Leg.εVL_nonneg
#print axioms Contracts.Track.Reach.Leg.outH3_vAcc
#print axioms Contracts.Track.Reach.Leg.outH_bound
#print axioms Contracts.Track.Reach.Leg.outV_bound
#print axioms Contracts.Track.Reach.Leg.c1_bound
#print axioms Contracts.Track.Reach.Leg.rate_bound
#print axioms Contracts.Track.Reach.Leg.leg_box
#print axioms Contracts.Track.Reach.Leg.leg_ticks
#print axioms Contracts.Track.Reach.Leg.τe_le
#print axioms Contracts.Track.Reach.Leg.τe_nonneg
#print axioms Contracts.Track.Reach.Leg.vzL_le
#print axioms Contracts.Track.Reach.Leg.hC_le
#print axioms Contracts.Track.Reach.Leg.hT_le
#print axioms Contracts.Track.Reach.Leg.vT_le
#print axioms Contracts.Track.Reach.Leg.outH0_dot
#print axioms Contracts.Track.Reach.Leg.outV0_dot
#print axioms Contracts.Track.Reach.Leg.leg_z
#print axioms Contracts.Track.Reach.Leg.tail_e_c
#print axioms Contracts.Track.Reach.Leg.tail_e
#print axioms Contracts.Track.Reach.Leg.tail_z
#print axioms Contracts.Track.Reach.Leg.complete_3d
#print axioms Contracts.Track.Reach.Leg.hold_3d
#print axioms Contracts.Track.Reach.Leg.sqZ_transpose
#print axioms Contracts.Track.Reach.Leg.resp_transpose
#print axioms Contracts.Track.Reach.Leg.forward_transpose
#print axioms Contracts.Track.Reach.Leg.tail_of_state
#print axioms Contracts.Track.Reach.Leg.chk_of_groups
#print axioms Contracts.Track.Reach.Leg.CertGainH.step_spec
#print axioms Contracts.Track.Reach.Leg.CertGainH.hAT
#print axioms Contracts.Track.Reach.Leg.CertGainH.hpowT
#print axioms Contracts.Track.Reach.Leg.CertGainH.MnT_check
#print axioms Contracts.Track.Reach.Leg.CertGainH.ρB_check
#print axioms Contracts.Track.Reach.Leg.CertGainH.initB
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_0
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_1
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_2
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_3
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_4
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_5
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_6
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_7
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_8
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_9
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_10
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_11
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_12
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_13
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_14
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpB_15
#print axioms Contracts.Track.Reach.Leg.CertGainH.chkB
#print axioms Contracts.Track.Reach.Leg.CertGainH.GtailB_13_eq
#print axioms Contracts.Track.Reach.Leg.CertGainH.GtailB_54_eq
#print axioms Contracts.Track.Reach.Leg.CertGainH.numB
#print axioms Contracts.Track.Reach.Leg.CertGainH.ρA_check
#print axioms Contracts.Track.Reach.Leg.CertGainH.initA
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_0
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_1
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_2
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_3
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_4
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_5
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_6
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_7
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_8
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_9
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_10
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_11
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_12
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_13
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_14
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpA_15
#print axioms Contracts.Track.Reach.Leg.CertGainH.chkA
#print axioms Contracts.Track.Reach.Leg.CertGainH.numA
#print axioms Contracts.Track.Reach.Leg.CertGainH.ρE0_check
#print axioms Contracts.Track.Reach.Leg.CertGainH.initE0
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_0
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_1
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_2
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_3
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_4
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_5
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_6
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE0_7
#print axioms Contracts.Track.Reach.Leg.CertGainH.chkE0
#print axioms Contracts.Track.Reach.Leg.CertGainH.GtailE0_13_eq
#print axioms Contracts.Track.Reach.Leg.CertGainH.GtailE0_54_eq
#print axioms Contracts.Track.Reach.Leg.CertGainH.ρE1_check
#print axioms Contracts.Track.Reach.Leg.CertGainH.initE1
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_0
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_1
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_2
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_3
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_4
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_5
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_6
#print axioms Contracts.Track.Reach.Leg.CertGainH.grpE1_7
#print axioms Contracts.Track.Reach.Leg.CertGainH.chkE1
#print axioms Contracts.Track.Reach.Leg.CertGainH.PtailE1_13_eq
#print axioms Contracts.Track.Reach.Leg.CertGainH.PtailE1_54_eq
#print axioms Contracts.Track.Reach.Leg.CertGainV.step_spec
#print axioms Contracts.Track.Reach.Leg.CertGainV.hAT
#print axioms Contracts.Track.Reach.Leg.CertGainV.hpowT
#print axioms Contracts.Track.Reach.Leg.CertGainV.MnT_check
#print axioms Contracts.Track.Reach.Leg.CertGainV.ρB_check
#print axioms Contracts.Track.Reach.Leg.CertGainV.initB
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_0
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_1
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_2
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_3
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_4
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_5
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_6
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpB_7
#print axioms Contracts.Track.Reach.Leg.CertGainV.chkB
#print axioms Contracts.Track.Reach.Leg.CertGainV.GtailB_54_eq
#print axioms Contracts.Track.Reach.Leg.CertGainV.numB
#print axioms Contracts.Track.Reach.Leg.CertGainV.ρE0_check
#print axioms Contracts.Track.Reach.Leg.CertGainV.initE0
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_0
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_1
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_2
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_3
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_4
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_5
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_6
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE0_7
#print axioms Contracts.Track.Reach.Leg.CertGainV.chkE0
#print axioms Contracts.Track.Reach.Leg.CertGainV.GtailE0_54_eq
#print axioms Contracts.Track.Reach.Leg.CertGainV.ρE1_check
#print axioms Contracts.Track.Reach.Leg.CertGainV.initE1
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_0
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_1
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_2
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_3
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_4
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_5
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_6
#print axioms Contracts.Track.Reach.Leg.CertGainV.grpE1_7
#print axioms Contracts.Track.Reach.Leg.CertGainV.chkE1
#print axioms Contracts.Track.Reach.Leg.CertGainV.GtailE1_54_eq
#print axioms Contracts.Track.Reach.Leg.state_le
#print axioms Contracts.Track.Reach.Leg.peak_of_state
#print axioms Contracts.Track.Reach.Leg.CertGainH.gainsB
#print axioms Contracts.Track.Reach.Leg.CertGainH.gainsA
#print axioms Contracts.Track.Reach.Leg.CertGainH.stateAt
#print axioms Contracts.Track.Reach.Leg.CertGainH.y0B
#print axioms Contracts.Track.Reach.Leg.CertGainH.y0E0
#print axioms Contracts.Track.Reach.Leg.CertGainH.y0E1
#print axioms Contracts.Track.Reach.Leg.CertGainH.tail_Bc
#print axioms Contracts.Track.Reach.Leg.CertGainH.tail_E0c
#print axioms Contracts.Track.Reach.Leg.CertGainH.peak_E1c
#print axioms Contracts.Track.Reach.Leg.CertGainH.tail_B
#print axioms Contracts.Track.Reach.Leg.CertGainH.tail_E0
#print axioms Contracts.Track.Reach.Leg.CertGainH.peak_E1
#print axioms Contracts.Track.Reach.Leg.CertGainV.gainsB
#print axioms Contracts.Track.Reach.Leg.CertGainV.stateAt
#print axioms Contracts.Track.Reach.Leg.CertGainV.tail_B
#print axioms Contracts.Track.Reach.Leg.CertGainV.tail_E0
#print axioms Contracts.Track.Reach.Leg.CertGainV.tail_E1
#print axioms Contracts.Track.Reach.Leg.gainBh_coord
#print axioms Contracts.Track.Reach.Leg.gainBv_coord
#print axioms Contracts.Track.Reach.Leg.rsp_sub
#print axioms Contracts.Track.Reach.Leg.gainB_cert
#print axioms Contracts.Track.Reach.Leg.rate_shift
#print axioms Contracts.Track.Reach.Leg.gainJ_cert
#print axioms Contracts.Track.Reach.Leg.gainC1_cert
#print axioms Contracts.Track.Reach.Leg.gainBV_cert
#print axioms Contracts.Track.Reach.Leg.refGains_certified
#print axioms Contracts.Track.Reach.Leg.legModel_of_run
#print axioms Contracts.Track.Reach.Leg.err_eq
#print axioms Contracts.Track.Reach.Leg.box_run
#print axioms Contracts.Track.Reach.Leg.d2sum_run
#print axioms Contracts.Track.Reach.Leg.Tc_le
#print axioms Contracts.Track.Reach.Leg.loiter_near
#print axioms Contracts.Track.Reach.Leg.target_held
#print axioms Contracts.Track.Reach.Leg.per_le
#print axioms Contracts.Track.Reach.Leg.perV_le
#print axioms Contracts.Track.Reach.Leg.forcing_small_H
#print axioms Contracts.Track.Reach.Leg.forcing_small_V
#print axioms Contracts.Track.Reach.Leg.err_hold
#print axioms Contracts.Track.Reach.Leg.waypoint_reach_h
#print axioms Contracts.Track.Reach.Leg.waypointReachH_holds
#print axioms Contracts.Track.Reach.Leg.loiter_of_code'
#print axioms Contracts.Track.Reach.Leg.loiter_of_code
#print axioms Contracts.Track.Reach.Leg.legPhase_of_box
#print axioms Contracts.Track.Reach.Leg.legFacts_of_box
#print axioms Contracts.Track.Reach.Leg.waypoint_reach_h_box

/-! The 3D leg theorem at `PSC_D_ACC_P 0.25` (REACH.md §10): `Contracts/Track/VerticalHi{,CertData,Cert}.lean`,
`Contracts/Track/Reach/Leg3{GainV,GainsData,Gains,Tube,,Nav,Hold,Box}.lean`. -/
#print axioms Contracts.Track.VerticalHi.tick_eq
#print axioms Contracts.Track.VerticalHi.errOf_absTick
#print axioms Contracts.Track.VerticalHi.Av_vAccV
#print axioms Contracts.Track.VerticalHi.Ahat_spec
#print axioms Contracts.Track.VerticalHi.Pv_symm_Q
#print axioms Contracts.Track.VerticalHi.certV
#print axioms Contracts.Track.VerticalHi.Dc_nonneg
#print axioms Contracts.Track.VerticalHi.certP
#print axioms Contracts.Track.VerticalHi.Dp_pos
#print axioms Contracts.Track.VerticalHi.Lp_mul_inv
#print axioms Contracts.Track.VerticalHi.AvR_eq
#print axioms Contracts.Track.VerticalHi.V_nonneg
#print axioms Contracts.Track.VerticalHi.V_A
#print axioms Contracts.Track.Reach.Leg3.GainVHi.step_spec
#print axioms Contracts.Track.Reach.Leg3.GainVHi.ad_spec
#print axioms Contracts.Track.Reach.Leg3.GainVHi.mx_spec
#print axioms Contracts.Track.Reach.Leg3.GainVHi.eqT_spec
#print axioms Contracts.Track.Reach.Leg3.GainVHi.eqU_spec
#print axioms Contracts.Track.Reach.Leg3.GainVHi.C_check
#print axioms Contracts.Track.Reach.Leg3.GainVHi.Pm_check
#print axioms Contracts.Track.Reach.Leg3.GainVHi.R_check
#print axioms Contracts.Track.Reach.Leg3.GainVHi.ρ_check
#print axioms Contracts.Track.Reach.Leg3.GainVHi.Mn_check
#print axioms Contracts.Track.Reach.Leg3.GainVHi.init0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_5
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_6
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_7
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_8
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_9
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_10
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_11
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_12
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_13
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_14
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp0_15
#print axioms Contracts.Track.Reach.Leg3.GainVHi.chk0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.num0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.init1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_5
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_6
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_7
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_8
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_9
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_10
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_11
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_12
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_13
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_14
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp1_15
#print axioms Contracts.Track.Reach.Leg3.GainVHi.chk1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.num1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.init2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_5
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_6
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_7
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_8
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_9
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_10
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_11
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_12
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_13
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_14
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp2_15
#print axioms Contracts.Track.Reach.Leg3.GainVHi.chk2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.num2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.init3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_5
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_6
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_7
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_8
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_9
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_10
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_11
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_12
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_13
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_14
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp3_15
#print axioms Contracts.Track.Reach.Leg3.GainVHi.chk3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.num3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.init4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_5
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_6
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_7
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_8
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_9
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_10
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_11
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_12
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_13
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_14
#print axioms Contracts.Track.Reach.Leg3.GainVHi.grp4_15
#print axioms Contracts.Track.Reach.Leg3.GainVHi.chk4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.num4
#print axioms Contracts.Track.Reach.Leg3.GainVHi.hA
#print axioms Contracts.Track.Reach.Leg3.GainVHi.castLp_inv
#print axioms Contracts.Track.Reach.Leg3.GainVHi.coord
#print axioms Contracts.Track.Reach.Leg3.GainVHi.V_single
#print axioms Contracts.Track.Reach.Leg3.GainVHi.hpow
#print axioms Contracts.Track.Reach.Leg3.GainVHi.out0
#print axioms Contracts.Track.Reach.Leg3.GainVHi.out1
#print axioms Contracts.Track.Reach.Leg3.GainVHi.out2
#print axioms Contracts.Track.Reach.Leg3.GainVHi.out3
#print axioms Contracts.Track.Reach.Leg3.GainVHi.out4
#print axioms Contracts.Track.Reach.Leg3.peakVH'
#print axioms Contracts.Track.Reach.Leg3.gainVH'
#print axioms Contracts.Track.Reach.Leg3.CertVHi.step_spec
#print axioms Contracts.Track.Reach.Leg3.CertVHi.hAT
#print axioms Contracts.Track.Reach.Leg3.CertVHi.hpowT
#print axioms Contracts.Track.Reach.Leg3.CertVHi.MnT_check
#print axioms Contracts.Track.Reach.Leg3.CertVHi.ρB_check
#print axioms Contracts.Track.Reach.Leg3.CertVHi.initB
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_2
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_3
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_4
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_5
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_6
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_7
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_8
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_9
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_10
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_11
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_12
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_13
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_14
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpB_15
#print axioms Contracts.Track.Reach.Leg3.CertVHi.chkB
#print axioms Contracts.Track.Reach.Leg3.CertVHi.GtailB_22_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.GtailB_82_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.numB
#print axioms Contracts.Track.Reach.Leg3.CertVHi.ρA_check
#print axioms Contracts.Track.Reach.Leg3.CertVHi.initA
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_2
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_3
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_4
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_5
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_6
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_7
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_8
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_9
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_10
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_11
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_12
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_13
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_14
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpA_15
#print axioms Contracts.Track.Reach.Leg3.CertVHi.chkA
#print axioms Contracts.Track.Reach.Leg3.CertVHi.numA
#print axioms Contracts.Track.Reach.Leg3.CertVHi.ρE0_check
#print axioms Contracts.Track.Reach.Leg3.CertVHi.initE0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_2
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_3
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_4
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_5
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_6
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_7
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_8
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_9
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE0_10
#print axioms Contracts.Track.Reach.Leg3.CertVHi.chkE0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.GtailE0_22_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.GtailE0_82_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.ρE1_check
#print axioms Contracts.Track.Reach.Leg3.CertVHi.initE1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_2
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_3
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_4
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_5
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_6
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_7
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_8
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_9
#print axioms Contracts.Track.Reach.Leg3.CertVHi.grpE1_10
#print axioms Contracts.Track.Reach.Leg3.CertVHi.chkE1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.PtailE1_22_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.PtailE1_82_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.gainsB
#print axioms Contracts.Track.Reach.Leg3.CertVHi.gainsA
#print axioms Contracts.Track.Reach.Leg3.CertVHi.stateAt
#print axioms Contracts.Track.Reach.Leg3.CertVHi.y0B
#print axioms Contracts.Track.Reach.Leg3.CertVHi.y0E0
#print axioms Contracts.Track.Reach.Leg3.CertVHi.y0E1
#print axioms Contracts.Track.Reach.Leg3.CertVHi.GVH0_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.PVH0_eq
#print axioms Contracts.Track.Reach.Leg3.CertVHi.tail_Bc
#print axioms Contracts.Track.Reach.Leg3.CertVHi.tail_E0c
#print axioms Contracts.Track.Reach.Leg3.CertVHi.peak_E1c
#print axioms Contracts.Track.Reach.Leg3.CertVHi.tail_Bt
#print axioms Contracts.Track.Reach.Leg3.CertVHi.tail_E0t
#print axioms Contracts.Track.Reach.Leg3.CertVHi.peak_E1t
#print axioms Contracts.Track.Reach.Leg3.gainBv3_coord
#print axioms Contracts.Track.Reach.Leg3.gainBV3_cert
#print axioms Contracts.Track.Reach.Leg3.gainU_cert
#print axioms Contracts.Track.Reach.Leg3.refGains3_certified
#print axioms Contracts.Track.Reach.Leg3.outV4_vAccV
#print axioms Contracts.Track.Reach.Leg3.vAccV_abs
#print axioms Contracts.Track.Reach.Leg3.vAVa_nonneg
#print axioms Contracts.Track.Reach.Leg3.inv_amax_le
#print axioms Contracts.Track.Reach.Leg3.zetaV_step
#print axioms Contracts.Track.Reach.Leg3.gVH0
#print axioms Contracts.Track.Reach.Leg3.gVH1
#print axioms Contracts.Track.Reach.Leg3.εVL3_nonneg
#print axioms Contracts.Track.Reach.Leg3.boxV3_close
#print axioms Contracts.Track.Reach.Leg3.boxU3_close
#print axioms Contracts.Track.Reach.Leg3.outH_bound3
#print axioms Contracts.Track.Reach.Leg3.outV_bound3
#print axioms Contracts.Track.Reach.Leg3.u_bound
#print axioms Contracts.Track.Reach.Leg3.c1_bound3
#print axioms Contracts.Track.Reach.Leg3.rate_bound3
#print axioms Contracts.Track.Reach.Leg3.leg_box3
#print axioms Contracts.Track.Reach.Leg3.leg_ticks3
#print axioms Contracts.Track.Reach.Leg3.vC3_le
#print axioms Contracts.Track.Reach.Leg3.vT3_le
#print axioms Contracts.Track.Reach.Leg3.tail_e_c3
#print axioms Contracts.Track.Reach.Leg3.tail_z_c3
#print axioms Contracts.Track.Reach.Leg3.tail_e3
#print axioms Contracts.Track.Reach.Leg3.tail_z3
#print axioms Contracts.Track.Reach.Leg3.complete3_3d
#print axioms Contracts.Track.Reach.Leg3.hold3_3d
#print axioms Contracts.Track.Reach.Leg3.waypoint_reach_nonvacuous
#print axioms Contracts.Track.Reach.Leg3.legModel3_of_run
#print axioms Contracts.Track.Reach.Leg3.box_run3
#print axioms Contracts.Track.Reach.Leg3.d2sum_run3
#print axioms Contracts.Track.Reach.Leg3.Tc_le3
#print axioms Contracts.Track.Reach.Leg3.loiter_near3
#print axioms Contracts.Track.Reach.Leg3.target_held3
#print axioms Contracts.Track.Reach.Leg3.forcing_small_H3
#print axioms Contracts.Track.Reach.Leg3.forcing_small_V3
#print axioms Contracts.Track.Reach.Leg3.err_hold3
#print axioms Contracts.Track.Reach.Leg3.waypoint_reach
#print axioms Contracts.Track.Reach.Leg3.legPhase3_of_box
#print axioms Contracts.Track.Reach.Leg3.legFacts3_of_box
#print axioms Contracts.Track.Reach.Leg3.waypoint_reach_box

-- The invariant rule (Contracts/Invariant.lean)
#print axioms Contracts.STL.sat_untimed
#print axioms Contracts.STL.always_of_invariant
#print axioms Contracts.STL.always_of_invariant_const
#print axioms Contracts.STL.implements_always_of_invariant

-- The safety theorem (Contracts/Track/Reach/SafeRule.lean, Safe.lean, Safe3.lean)
#print axioms Contracts.Track.Reach.Safe.pre_len
#print axioms Contracts.Track.Reach.Safe.pre_last
#print axioms Contracts.Track.Reach.Safe.pre_eq_iff
#print axioms Contracts.Track.Reach.Safe.hist_step
#print axioms Contracts.Track.Reach.Safe.implements_always_of_prefix
#print axioms Contracts.Track.Reach.Safe.sat_track
#print axioms Contracts.Track.Reach.Safe.ahover_tick0
#print axioms Contracts.Track.Reach.Safe.posH_close
#print axioms Contracts.Track.Reach.Safe.boxVS_close
#print axioms Contracts.Track.Reach.Safe.posVS_close
#print axioms Contracts.Track.Reach.Safe.hb_of_tick
#print axioms Contracts.Track.Reach.Safe.axis_out
#print axioms Contracts.Track.Reach.Safe.axis_c1
#print axioms Contracts.Track.Reach.Safe.axis_rate
#print axioms Contracts.Track.Reach.Safe.axis_box
#print axioms Contracts.Track.Reach.Safe.sbox_step
#print axioms Contracts.Track.Reach.Safe.norm3_le
#print axioms Contracts.Track.Reach.Safe.smodel_of_run
#print axioms Contracts.Track.Reach.Safe.sbox_run
#print axioms Contracts.Track.Reach.Safe.err_le_of_sbox
#print axioms Contracts.Track.Reach.Safe.tracking_safe_h
#print axioms Contracts.Track.Reach.Safe.tracking_safe_h_forever
#print axioms Contracts.Track.Reach.Safe.boxV3S_close
#print axioms Contracts.Track.Reach.Safe.posV3S_close
#print axioms Contracts.Track.Reach.Safe.boxU3S_close
#print axioms Contracts.Track.Reach.Safe.hb_of_tick3
#print axioms Contracts.Track.Reach.Safe.u_boundS
#print axioms Contracts.Track.Reach.Safe.sbox3_step
#print axioms Contracts.Track.Reach.Safe.smodel3_of_run
#print axioms Contracts.Track.Reach.Safe.sbox3_run
#print axioms Contracts.Track.Reach.Safe.err_le_of_sbox3
#print axioms Contracts.Track.Reach.Safe.tracking_safe
#print axioms Contracts.Track.Reach.Safe.tracking_safe_forever

-- Hover stability (REACH.md §8.7): HoverTube, HoverModel, HoverCert, Hover
#print axioms Contracts.Track.Reach.Hover.exc_nonneg
#print axioms Contracts.Track.Reach.Hover.abs_le_exc
#print axioms Contracts.Track.Reach.Hover.exc_le_of
#print axioms Contracts.Track.Reach.Hover.lam_pos
#print axioms Contracts.Track.Reach.Hover.lam_le_one
#print axioms Contracts.Track.Reach.Hover.lamh_eq
#print axioms Contracts.Track.Reach.Hover.lamv_le
#print axioms Contracts.Track.Reach.Hover.sum_le_wsum
#print axioms Contracts.Track.Reach.Hover.tube_exc
#print axioms Contracts.Track.Reach.Hover.exc_peak
#print axioms Contracts.Track.Reach.Hover.exc_decay
#print axioms Contracts.Track.Reach.Hover.chan_tube_exc
#print axioms Contracts.Track.Reach.Hover.Vh_single_j
#print axioms Contracts.Track.Reach.Hover.Vv_single_j
#print axioms Contracts.Track.Reach.Hover.respH_decay_gen
#print axioms Contracts.Track.Reach.Hover.respV_decay_gen
#print axioms Contracts.Track.Reach.Hover.κH_eq
#print axioms Contracts.Track.Reach.Hover.le_dinf
#print axioms Contracts.Track.Reach.Hover.dinf_nonneg
#print axioms Contracts.Track.Reach.Hover.dinf_le
#print axioms Contracts.Track.Reach.Hover.εVs_nonneg
#print axioms Contracts.Track.Reach.Hover.εHs_nonneg
#print axioms Contracts.Track.Reach.Hover.κV_nonneg
#print axioms Contracts.Track.Reach.Hover.κH_nonneg
#print axioms Contracts.Track.Reach.Hover.PV_nonneg
#print axioms Contracts.Track.Reach.Hover.PH_nonneg
#print axioms Contracts.Track.Reach.Hover.regionVs
#print axioms Contracts.Track.Reach.Hover.regionHs
#print axioms Contracts.Track.Reach.Hover.tubeVs
#print axioms Contracts.Track.Reach.Hover.tubeHs
#print axioms Contracts.Track.Reach.Hover.tubeV_s
#print axioms Contracts.Track.Reach.Hover.tubeH_s
#print axioms Contracts.Track.Reach.Hover.excV_peak
#print axioms Contracts.Track.Reach.Hover.excH_peak
#print axioms Contracts.Track.Reach.Hover.hover_box_s
#print axioms Contracts.Track.Reach.Hover.hover_axes_s
#print axioms Contracts.Track.Reach.Hover.decay_of_min
#print axioms Contracts.Track.Reach.Hover.respV_decay_v
#print axioms Contracts.Track.Reach.Hover.lamv_nonneg
#print axioms Contracts.Track.Reach.Hover.rat_pow_ge
#print axioms Contracts.Track.Reach.Hover.rat_pow_le
#print axioms Contracts.Track.Reach.Hover.lam_pow_ge
#print axioms Contracts.Track.Reach.Hover.lamv_pow_le
#print axioms Contracts.Track.Reach.Hover.respV_row
#print axioms Contracts.Track.Reach.Hover.respV_cVd
#print axioms Contracts.Track.Reach.Hover.Vh_le_abs
#print axioms Contracts.Track.Reach.Hover.stateE1
#print axioms Contracts.Track.Reach.Hover.VbE1_check
#print axioms Contracts.Track.Reach.Hover.V_E1
#print axioms Contracts.Track.Reach.Hover.lam_pow_1728
#print axioms Contracts.Track.Reach.Hover.respH_e1
#print axioms Contracts.Track.Reach.Hover.respH_cHd
#print axioms Contracts.Track.Reach.Hover.mH_le
#print axioms Contracts.Track.Reach.Hover.mV_le
#print axioms Contracts.Track.Reach.Hover.hover_stable
#print axioms Contracts.Track.Reach.Hover.norm_le_axes3
#print axioms Contracts.Track.Reach.Hover.qnorm_one_hover
#print axioms Contracts.Track.Reach.Hover.prow_ahover
#print axioms Contracts.Track.Reach.Hover.pos_zero
#print axioms Contracts.Track.Reach.Hover.forceH_zero
#print axioms Contracts.Track.Reach.Hover.forceV_zero
#print axioms Contracts.Track.Reach.Hover.rowH_code
#print axioms Contracts.Track.Reach.Hover.εHs_split
#print axioms Contracts.Track.Reach.Hover.εVs_split
#print axioms Contracts.Track.Reach.Hover.excH_le
#print axioms Contracts.Track.Reach.Hover.excV_le
#print axioms Contracts.Track.Reach.Hover.wsum_le_wsum
#print axioms Contracts.Track.Reach.Hover.wsum_mul
#print axioms Contracts.Track.Reach.Hover.hoverModelS_of_run
#print axioms Contracts.Track.Reach.Hover.hover_stable
#print axioms Contracts.Track.Reach.Hover.hover_stable_box
#print axioms Contracts.Track.Reach.Hover.hover_stable_nonvacuous
