import Copter.State

/-!
# `Copter.AutoYaw`: the heading command in Auto

Mirrors `ArduCopter/autoyaw.cpp` at 802db19de1: `look_ahead_yaw_rad` (`:16-28`),
`set_mode_to_default` (`:30-33`), `default_mode` (`:37-58`), `set_mode` (`:61-111`), `yaw_rad`
(`:271-345`), `rate_rads` (`:349-376`), `get_heading` (`:378-417`), for the modes of
`Copter.AutoYawMode` (`HOLD`, `LOOK_AT_NEXT_WP`, `LOOK_AHEAD`).

With the default `WP_YAW_BEHAVIOR = 2` (`LOOK_AT_NEXT_WP_EXCEPT_RTL`) the waypoint legs use
`LOOK_AT_NEXT_WP`, whose heading is `pos_control->get_yaw_rad()` and whose rate is
`pos_control->get_yaw_rate_rads()` (`autoyaw.cpp:339-343`, `:364-366`), i.e. the direction of the
desired velocity and the centripetal turn rate computed by `AC_PosControl::calculate_yaw_and_rate_yaw`
(`AC_PosControl.cpp:1641-1670`), as `HeadingMode::Angle_And_Rate`. (`AC_WPNav::get_yaw_rad` and
`get_wp_bearing_to_destination_rad` exist in the port but AutoYaw does not call them: the C++
comment at `:340` explains that the bearing is not used so that the copter does not turn too
much.)

Environment assumptions: no RC pilot yaw input (`rc().has_valid_input()` false, or centred sticks:
`_pilot_yaw_rate_rads` stays 0 and the `PILOT_RATE` branches of `get_heading` do nothing),
weathervaning disabled (`WVANE_ENABLE = 0`, its default, so `update_weathervane` does nothing),
`copter.position_ok()` and `AP::ahrs().get_velocity_NED` succeed (`LOOK_AHEAD`).
-/

namespace Copter

open AP_Math

/-- `YAW_LOOK_AHEAD_MIN_SPEED_MS` (`ArduCopter/config.h:472-473`), an `int` literal. -/
def YAW_LOOK_AHEAD_MIN_SPEED_MS : ftype := 1

namespace AutoYaw

/-- `default_mode(rtl)` (`autoyaw.cpp:37-58`). -/
def default_mode (p : Parameters) (rtl : Bool) : AutoYawMode :=
  if p.WP_YAW_BEHAVIOR == WP_YAW_BEHAVIOR_NONE then .HOLD
  else if p.WP_YAW_BEHAVIOR == WP_YAW_BEHAVIOR_LOOK_AT_NEXT_WP_EXCEPT_RTL then
    (if rtl then .HOLD else .LOOK_AT_NEXT_WP)
  else if p.WP_YAW_BEHAVIOR == WP_YAW_BEHAVIOR_LOOK_AHEAD then .LOOK_AHEAD
  else .LOOK_AT_NEXT_WP

/-- `set_mode(yaw_mode)` (`autoyaw.cpp:61-111`). -/
def set_mode (s : State) (yaw_mode : AutoYawMode) : State :=
  -- return immediately if no change
  if s.auto_yaw._mode == yaw_mode then s
  else
    let ay := { s.auto_yaw with _mode := yaw_mode }
    -- perform initialisation
    let ay := match yaw_mode with
      | .HOLD => { ay with _yaw_angle_rad := (AC_AttitudeControl.get_att_target_euler_rad s.attitude_control.toState).z }
      -- wpnav will initialise heading when wpnav's set_destination method is called
      | .LOOK_AT_NEXT_WP => ay
      -- Commanded Yaw to automatically look ahead.
      | .LOOK_AHEAD => { ay with _look_ahead_yaw_rad := s.ahrs.yaw }
    { s with auto_yaw := ay }

/-- `set_mode_to_default(rtl)` (`autoyaw.cpp:30-33`). -/
def set_mode_to_default (p : Parameters) (s : State) (rtl : Bool) : State :=
  set_mode s (default_mode p rtl)

/-- `look_ahead_yaw_rad()` (`autoyaw.cpp:16-28`); `position_ok()` and `get_velocity_NED` succeed. -/
def look_ahead_yaw_rad (s : State) : State × ftype :=
  let vel_ned_ms := s.ahrs.vel_ned
  let speed_ms_sq := vel_ned_ms.xy.length_squared
  let ay := if speed_ms_sq > (YAW_LOOK_AHEAD_MIN_SPEED_MS * YAW_LOOK_AHEAD_MIN_SPEED_MS) then
      { s.auto_yaw with _look_ahead_yaw_rad := Float32.atan2 vel_ned_ms.y vel_ned_ms.x }
    else s.auto_yaw
  ({ s with auto_yaw := ay }, ay._look_ahead_yaw_rad)

/-- `yaw_rad()` (`autoyaw.cpp:271-345`). -/
def yaw_rad (s : State) : State × ftype :=
  match s.auto_yaw._mode with
  | .LOOK_AHEAD =>
    let (s, y) := look_ahead_yaw_rad s
    ({ s with auto_yaw := { s.auto_yaw with _yaw_angle_rad := y } }, y)
  | .HOLD =>
    let y := (AC_AttitudeControl.get_att_target_euler_rad s.attitude_control.toState).z
    ({ s with auto_yaw := { s.auto_yaw with _yaw_angle_rad := y } }, y)
  | .LOOK_AT_NEXT_WP =>
    -- point towards next waypoint.
    -- we don't use wp_bearing_deg because we don't want the copter to turn too much during flight
    let y := AC_PosControl.get_yaw_rad s.pos_control
    ({ s with auto_yaw := { s.auto_yaw with _yaw_angle_rad := y } }, y)

/-- `rate_rads()` (`autoyaw.cpp:349-376`). -/
def rate_rads (s : State) : State × ftype :=
  let r := match s.auto_yaw._mode with
    | .HOLD | .LOOK_AHEAD => 0.0
    | .LOOK_AT_NEXT_WP => AC_PosControl.get_yaw_rate_rads s.pos_control
  ({ s with auto_yaw := { s.auto_yaw with _yaw_rate_rads := r } }, r)

/-- `get_heading()` (`autoyaw.cpp:378-417`), without pilot input and weathervaning (header). -/
def get_heading (s : State) : State × AC_AttitudeControl.HeadingCommand :=
  -- process pilot's yaw input (none, header)
  let s := { s with auto_yaw := { s.auto_yaw with _pilot_yaw_rate_rads := 0.0 } }
  let (s, yaw_angle_rad) := yaw_rad s
  let (s, yaw_rate_rads) := rate_rads s
  let heading_mode : AC_AttitudeControl.HeadingMode := match s.auto_yaw._mode with
    | .HOLD => .Rate_Only
    | .LOOK_AT_NEXT_WP | .LOOK_AHEAD => .Angle_And_Rate
  (s, { yaw_angle_rad, yaw_rate_rads, heading_mode })

end AutoYaw

end Copter
