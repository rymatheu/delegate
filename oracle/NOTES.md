# Oracle: notes on linking the ArduPilot classes

Status: Route 2 is built; see README.md (build, stubs, harness), RESULTS.md (comparison with the
port) and DIFF.md. The notes below are the findings from before it was built.

ArduPilot tree: /Users/ryan/Research/delegate/ardupilot, commit 802db19de1.

Route 1 (waf example on the SITL board)
- The checkout has every submodule empty (`modules/waf`, `modules/mavlink`,
  `modules/DroneCAN/*`), so `./waf` does not exist. A build needs a copy of the tree
  (to leave the original untouched), `git submodule update --init` for at least waf,
  mavlink and DroneCAN, and a venv with empy 3.3.4, pexpect, future. Host Python is
  3.14 (Homebrew); empy 3.3.4 and waf under 3.14 are untested. github.com is reachable.
- `libraries/AC_AttitudeControl` has no `examples/` directory; one would be written
  on the shape of `libraries/AC_PID/examples/AC_PID_test` (`bld.ap_example(use='ap')`).
- Feeding scripted estimates is the real obstacle. `AP_AHRS_View`'s getters used by
  the cascade are not virtual: `get_gyro_latest`, `get_quat_body_to_ned` (inline,
  AP_AHRS_View.h:55), `cos_roll/cos_pitch/cos_yaw/sin_yaw` (read a cached `trig`
  struct, :68-84), `get_accel_ef` (forwards to `AP_AHRS`, :148), reset counts
  (:152-157); `roll/pitch/yaw` are public fields (:183-185). Only the destructor is
  virtual, so subclassing the view does not intercept anything.
- AC_PosControl also calls the `AP::ahrs()` singleton directly:
  `get_control_gain_scaler_XY/Z` (AC_PosControl.cpp:715, :1105, :1116),
  `get_relative_position_NED_origin`, `get_velocity_NED`, `get_vert_pos_rate_D`
  (`update_estimates`, :1446-1465). None is virtual (AP_AHRS.h:253-325). In SITL the
  SIM backend derives positions from `Location` differences, so a double NED input
  cannot be injected exactly without editing AP_AHRS.

Route 2 (recommended if resumed): compile the real, unmodified .cpp files
(AC_PosControl.cpp, AC_AttitudeControl.cpp, AC_AttitudeControl_Multi.cpp,
AP_MotorsMulticopter.cpp, AP_MotorsMatrix.cpp, AP_Motors_Thrust_Linearization.cpp,
AC_PID/*.cpp, AP_Math/*.cpp, Filter/LowPassFilter.cpp) outside waf, with a stub include
directory placed ahead of `libraries/` that shadows AP_AHRS/AP_AHRS_View.h,
AP_AHRS/AP_AHRS.h, AP_HAL, AP_Logger and GCS_MAVLink with minimal versions whose
getters return the scripted inputs. Keep the real AP_Param var_info tables so the
defaults come from the source, with a small `setup_object_defaults` stub. This beats
transliterating function bodies: the only edits are in the stub headers.
Flags: `-O2 -ffp-contract=off -fno-fast-math -cl-single-precision-constant`. Apple clang 17
ignores `-fsingle-precision-constant` (warning, literals stay double) but honors
`-cl-single-precision-constant` in C++ (checked: `x*0.1` becomes a float multiply); this is
also the flag waf passes for clang (Tools/ardupilotwaf/boards.py:403, :512).
