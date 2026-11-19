import ArduLean.Runtime.CFloat

/-!
ArduPilot `mavlink`. Sources: `(generated)`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `struct __mavlink_ekf_status_report_t`, `build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`. -/
structure __mavlink_ekf_status_report_t where
  /-- `float velocity_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  velocity_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pos_horiz_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  pos_horiz_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pos_vert_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  pos_vert_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float compass_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  compass_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float terrain_alt_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  terrain_alt_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint16_t flags` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  flags : UInt16 := (0 : UInt16)
  /-- `float airspeed_variance` of `__mavlink_ekf_status_report_t` (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/mavlink_msg_ekf_status_report.h:8`). -/
  airspeed_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `enum mavlink_channel_t`, `build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/mavlink_types.h:177-182`. -/
inductive mavlink_channel_t where
  | MAVLINK_COMM_0
  | MAVLINK_COMM_1
  | MAVLINK_COMM_2
  | MAVLINK_COMM_3
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `mavlink_channel_t` (underlying type `uint32_t`). -/
def mavlink_channel_t.toInt : mavlink_channel_t → UInt32
  | .MAVLINK_COMM_0 => (0 : UInt32)
  | .MAVLINK_COMM_1 => (1 : UInt32)
  | .MAVLINK_COMM_2 => (2 : UInt32)
  | .MAVLINK_COMM_3 => (3 : UInt32)

/-- C++ `enum MAV_SEVERITY`, `build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/common/common.h:789-800`. -/
inductive MAV_SEVERITY where
  | MAV_SEVERITY_EMERGENCY
  | MAV_SEVERITY_ALERT
  | MAV_SEVERITY_CRITICAL
  | MAV_SEVERITY_ERROR
  | MAV_SEVERITY_WARNING
  | MAV_SEVERITY_NOTICE
  | MAV_SEVERITY_INFO
  | MAV_SEVERITY_DEBUG
  | MAV_SEVERITY_ENUM_END
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `MAV_SEVERITY` (underlying type `uint32_t`). -/
def MAV_SEVERITY.toInt : MAV_SEVERITY → UInt32
  | .MAV_SEVERITY_EMERGENCY => (0 : UInt32)
  | .MAV_SEVERITY_ALERT => (1 : UInt32)
  | .MAV_SEVERITY_CRITICAL => (2 : UInt32)
  | .MAV_SEVERITY_ERROR => (3 : UInt32)
  | .MAV_SEVERITY_WARNING => (4 : UInt32)
  | .MAV_SEVERITY_NOTICE => (5 : UInt32)
  | .MAV_SEVERITY_INFO => (6 : UInt32)
  | .MAV_SEVERITY_DEBUG => (7 : UInt32)
  | .MAV_SEVERITY_ENUM_END => (8 : UInt32)

/-- C++ `enum EKF_STATUS_FLAGS`, `build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/ardupilotmega/ardupilotmega.h:515-530`. -/
inductive EKF_STATUS_FLAGS where
  | EKF_ATTITUDE
  | EKF_VELOCITY_HORIZ
  | EKF_VELOCITY_VERT
  | EKF_POS_HORIZ_REL
  | EKF_POS_HORIZ_ABS
  | EKF_POS_VERT_ABS
  | EKF_POS_VERT_AGL
  | EKF_CONST_POS_MODE
  | EKF_PRED_POS_HORIZ_REL
  | EKF_PRED_POS_HORIZ_ABS
  | EKF_UNINITIALIZED
  | EKF_GPS_GLITCHING
  | EKF_STATUS_FLAGS_ENUM_END
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `EKF_STATUS_FLAGS` (underlying type `uint32_t`). -/
def EKF_STATUS_FLAGS.toInt : EKF_STATUS_FLAGS → UInt32
  | .EKF_ATTITUDE => (1 : UInt32)
  | .EKF_VELOCITY_HORIZ => (2 : UInt32)
  | .EKF_VELOCITY_VERT => (4 : UInt32)
  | .EKF_POS_HORIZ_REL => (8 : UInt32)
  | .EKF_POS_HORIZ_ABS => (16 : UInt32)
  | .EKF_POS_VERT_ABS => (32 : UInt32)
  | .EKF_POS_VERT_AGL => (64 : UInt32)
  | .EKF_CONST_POS_MODE => (128 : UInt32)
  | .EKF_PRED_POS_HORIZ_REL => (256 : UInt32)
  | .EKF_PRED_POS_HORIZ_ABS => (512 : UInt32)
  | .EKF_UNINITIALIZED => (1024 : UInt32)
  | .EKF_GPS_GLITCHING => (32768 : UInt32)
  | .EKF_STATUS_FLAGS_ENUM_END => (32769 : UInt32)

end Estimator_lib
