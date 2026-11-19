import Harness.System

/-! # The controller chain's discharge table, shared

How the obligations between the controller stages (`rate_c`, `mixer`, `guidance`, `position`,
`attitude`) are discharged, stated once and used by every composite that contains the chain:
`ap_ctl`, `ap_flight`, `ap_full` and `ap_full_ekf` (`harness obligations NAME --status`, which
says of each entry whether the link's checkers prove it). The entries rest on the stages'
guarantees, on the attitude stage's parameter assumption `thr_g_boost_range` (a clause of every
such composite), and, for the rate PIDs' gyro bound, on a clause the composite names (`gyro`):
its own assumption in `ap_ctl`, the estimator's guarantee in `ap_full_ekf`. The entries that
cite `ap_ctl`'s usage assumptions are in `usage`. -/

namespace Ardupilot.Harnesses.Chain

open Harness

/-- The rate PIDs' two obligations per axis; `gyro` names the clause that bounds the gyro
(`none`: nothing does, the signal-bound entries are left out), `boost` the clause that bounds
ATC_THR_G_BOOST (`none` where the composite fixes it to a constant). -/
def rate (gyro : Option String) (boost : Option String) : List Discharge :=
  let signals (a c g : String) : Discharge :=
    { path := "rate_c", clause := s!"{a}_signals_bounded", kind := "guarantee",
      by_ := ["attitude.targets_bounded", g],
      note := s!"|target_{c}| ≤ 1e4 from the attitude stage (previous tick); the gyro by {g}" }
  let scales (a : String) : Discharge :=
    { path := "rate_c", clause := s!"{a}_scales_range", kind := "guarantee",
      by_ := ["attitude.pd_scale_range"] ++ boost.toList ++ ["attitude.i_scale_one"],
      note := "pd_scale ≤ 1 + ATC_THR_G_BOOST ≤ 2; i_scale = 1" }
  let axis (a c : String) : List Discharge :=
    (gyro.map (signals a c)).toList ++ [scales a]
  axis "roll" "x" ++ axis "pitch" "y" ++ axis "yaw" "z"

/-- The entries that rest on the stages' guarantees alone. -/
def stages : List Discharge := [
  { path := "mixer", clause := "throttle_finite", kind := "guarantee",
    by_ := ["attitude.outputs_finite", "attitude.throttle_avg_max_range"] },
  { path := "mixer", clause := "throttle_filter_range", kind := "guarantee",
    by_ := ["attitude.throttle_filter_range"],
    note := "which rests on the attitude stage's pc_throttle_cutoff_range, discharged below" },
  { path := "guidance", clause := "pc_signals_bounded", kind := "hypothesis",
    note := "the position stage guarantees these signals (desired velocity, offsets, errors, \
      target, stopping point) only finite; bounding them by 50 m/s and 100 to 1000 m is a \
      statement about the closed-loop flight envelope, not about one stage" },
  { path := "position", clause := "ac_att_target_range", kind := "guarantee",
    by_ := ["attitude.att_target_euler_range", "attitude.outputs_finite"],
    note := "roll and pitch within ±π; the yaw target only finite (the position stage's \
      assumption was widened to that)" },
  { path := "position", clause := "ac_throttle_range", kind := "guarantee",
    by_ := ["attitude.ac_throttle_in_bounded"] },
  { path := "position", clause := "ac_lean_range", kind := "guarantee",
    by_ := ["attitude.lean_limits"] },
  { path := "position", clause := "hover_range", kind := "guarantee",
    by_ := ["mixer.throttle_hover_range"] },
  { path := "position", clause := "tgt_handover_args", kind := "guarantee",
    by_ := ["guidance.limits_handed_over", "guidance.corrections_handed_over"] },
  { path := "attitude", clause := "thrust_vec_tilt", kind := "hypothesis",
    note := "position's thrust_z_gravity gives the vertical part; on ticks with an NE update its \
      lean_within_max (a child guarantee, not in the composite's) bounds the tilt by 80 degrees; \
      between NE updates the acceleration target is the last update's or NE_init_controller's \
      (from the attitude target's roll and pitch, which only ±π bounds): not implied" },
  { path := "attitude", clause := "throttle_in_range", kind := "guarantee",
    by_ := ["position.throttle_in_bounded"] },
  { path := "attitude", clause := "hover_range", kind := "guarantee",
    by_ := ["mixer.throttle_hover_range"] },
  { path := "attitude", clause := "mixer_throttle_range", kind := "guarantee",
    by_ := ["mixer.signals_finite", "mixer.throttle_filtered_range"] },
  { path := "attitude", clause := "pc_throttle_cutoff_range", kind := "guarantee",
    by_ := ["position.throttle_set_by_d_update"] }]

/-- The entries that cite `ap_ctl`'s usage assumptions (`ApCtl.usage`): clauses on inputs that
in the full stacks are the supervisor's outputs, so these entries are `ap_ctl`'s only. -/
def usage : List Discharge := [
  { path := "mixer", clause := "commands_bounded", kind := "assumption",
    by_ := ["rate_c/roll.command_magnitude", "rate_c/pitch.command_magnitude",
      "rate_c/yaw.command_magnitude", "assume.rate_imax_documented"],
    note := "|command| ≤ 7e15 + kimax ≤ 7e15 + 1 < 1e16" },
  { path := "guidance", clause := "pc_limits_range", kind := "assumption",
    by_ := ["position.limits_follow_guidance", "guidance.limits_handed_over",
      "assume.supervisor_limits_in_guidance_range"],
    note := "plus the constructor's limits (position's withInit, within the range) and the \
      setters being the only writers (AC_PosControl.cpp:460-461, 810-816), read from the code" },
  { path := "position", clause := "tgt_bounded", kind := "assumption",
    by_ := ["guidance.targets_bounded_straight", "assume.straight_legs_only",
      "assume.update_wpnav_last"],
    note := "tgt_terrain_d is the constant 0" }]

/-- The entries between the chain and the supervisor stage (`ap_full`, `ap_full_ekf`): the
supervisor's code-fact guarantees on the commands it hands the mixer and the attitude stage, and
the mixer's spool state, which the supervisor reads. -/
def supervised : List Discharge := [
  { path := "mixer", clause := "spool_desired_range", kind := "guarantee",
    by_ := ["supervisor.spool_desired_range"],
    note := "the supervisor's desired spool state (previous tick; 0 before its first step)" },
  { path := "mixer", clause := "hover_dt_range", kind := "guarantee",
    by_ := ["supervisor.hover_dt_constant"],
    note := "update_throttle_hover(0.01), Attitude.cpp:62" },
  { path := "supervisor", clause := "spool_state_range", kind := "guarantee",
    by_ := ["mixer.spool_state_enum"],
    note := "SpoolState has the values 0 to 4 (same tick)" },
  { path := "attitude", clause := "heading_mode_range", kind := "guarantee",
    by_ := ["supervisor.heading_mode_enum"] },
  { path := "attitude", clause := "mix_ratio_range", kind := "guarantee",
    by_ := ["supervisor.mix_max_ratio_range"] }]

/-- The chain's table, for a composite whose gyro bound is the clause `gyro`. -/
def discharges (gyro : Option String)
    (boost : Option String := some "assume.thr_g_boost_range") : List Discharge :=
  rate gyro boost ++ stages

end Ardupilot.Harnesses.Chain
