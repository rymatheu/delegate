import Contracts.CopterHoverInv

/-!
# The state after the first tick

The hover run has three phases. Tick 0 boots the vehicle (`Copter.takeover`, the switch into Auto,
`ModeAuto::init`, the mission start) and flies the first waypoint leg, which is empty because the
vehicle is already at the waypoint: the waypoint is reached on that tick. Tick 1 sees the waypoint
reached, completes the mission and enters loiter at the stopping point (`ModeAuto::loiter_start`).
From tick 2 on the state is the steady one of `Contracts.CopterHover.InvSteady`.

`InvP1` is the invariant between tick 0 and tick 1: the core invariant `InvCore` (attitude, motors,
position controller, the vertical floats in the Lyapunov sublevel set), the navigator in the steady
form except that the leg origin is the stopping point computed at boot (a binary64 position within
`10⁻⁶` of the waypoint) and the destination is the waypoint, already reached (`NavP1`), the mission
running on its only command in the `WP` submode (`ModeP1`), and the plant at the waypoint altitude
with a vertical speed of a few micrometers per second (`2.45 · 10⁻⁶` m/s in fact), which keeps the
stopping point of tick 1 within the empty-leg threshold of the waypoint.
-/

namespace Contracts.CopterHover

open Contracts.CopterZero
open Contracts.CopterVertNear (Near64)

/-- The only mission command of the hover mission, as `ModeAuto.mission_cmd` builds it. -/
def hoverCmd : Copter.MissionCommand := { index := 1, location := hoverWP }

theorem mission_cmd_one : Copter.ModeAuto.mission_cmd runParams 1 = some hoverCmd := rfl

/-- The navigator after tick 0: the steady form with the leg origin at the boot stopping point,
the waypoint as destination, reached, last updated at `millis() = 2`. -/
structure NavP1 (s : AC_WPNav.State) : Prop where
  steady : NavSteady { s with _origin_ned_m := hoverWP }
  origin_x : ZD s._origin_ned_m.x
  origin_y : ZD s._origin_ned_m.y
  origin_z : Near64 s._origin_ned_m.z (-1) 1e-6
  dest : s._destination_ned_m = hoverWP
  reached : s._flags.reached_destination = true
  last_update : s._wp_last_update_ms = 2

/-- Modes, mission and clock after tick 0. -/
structure ModeP1 (st : Copter.State) : Prop where
  in_auto : st.in_auto = true
  submode : st.mode_auto._mode = .WP
  started : st.mode_auto.waiting_to_start = false
  running : st.mode_auto.mission.state = .MISSION_RUNNING
  nav_cmd : st.mode_auto.mission.nav_cmd = some hoverCmd
  loaded : st.mode_auto.mission.nav_cmd_loaded = true
  loiter_time_max : st.mode_auto.loiter_time_max = 0
  yaw : st.auto_yaw._mode = .LOOK_AT_NEXT_WP
  ticks : st.scheduler.ticks32 = 1
  micros : st.scheduler.micros = 2500

/-- The invariant between tick 0 and tick 1. -/
def InvP1 (st : Copter.State) (phys : CopterPlant.CState) : Prop :=
  InvCore st phys ∧ NavP1 st.wp_nav ∧ ModeP1 st ∧ phys.p.z = -1 ∧ |phys.v.z| ≤ 1e-5

end Contracts.CopterHover
