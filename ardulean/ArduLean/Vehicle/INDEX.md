# the vehicle translation: ArduPilot source file to Lean module

`lean/Vehicle_lib.lean` (3914 items, 61542 lines) split into 61 modules by `tools/split_modules.py`; `tools/check_split.py` rebuilds it byte for byte from `INDEX.json`. A function is in the folder of the ArduPilot source file its doc comment cites (or of its C++ class). Modules of one folder are numbered in dependency order (`AC_PID.lean` before `AC_PID_2.lean`); the cross-library modules hold the top of the call graph, where the libraries call each other in a cycle.

## Modules

| module | lines | items | ArduPilot sources (by size) |
|---|---:|---:|---|
| `Layout` | 2459 | 390 | `(generated)` |
| `libraries/AP_NavEKF/AP_NavEKF` | 8 | 2 | `libraries/AP_NavEKF/AP_Nav_Common.h` |
| `libraries/AP_RTC/AP_RTC` | 8 | 1 | `libraries/AP_RTC/JitterCorrection.cpp` |
| `libraries/AP_Math/AP_Math` | 5565 | 346 | `libraries/AP_Math/SCurve.cpp`, `libraries/AP_Math/control.cpp`, `libraries/AP_Math/SplineCurve.cpp`, `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/vector2.cpp`, `libraries/AP_Math/quaternion.cpp` (+11) |
| `libraries/AP_HAL/AP_HAL` | 1370 | 37 | `libraries/AP_HAL/utility/print_vprintf.cpp`, `libraries/AP_HAL/utility/RingBuffer.cpp`, `libraries/AP_HAL/utility/ftoa_engine.cpp`, `libraries/AP_HAL/utility/utoa_invert.cpp`, `libraries/AP_HAL/utility/functor.h`, `libraries/AP_HAL/Storage.cpp` (+3) |
| `libraries/Filter/Filter` | 354 | 26 | `libraries/Filter/DerivativeFilter.cpp`, `libraries/Filter/LowPassFilter.cpp`, `libraries/Filter/FilterWithBuffer.h`, `libraries/Filter/SlewLimiter.cpp`, `libraries/Filter/FilterClass.h`, `libraries/Filter/LowPassFilter.h` |
| `libraries/StorageManager/StorageManager` | 262 | 20 | `libraries/StorageManager/StorageManager.cpp`, `libraries/StorageManager/StorageManager.h` |
| `libraries/AP_Param/AP_Param` | 2881 | 209 | `libraries/AP_Param/AP_Param.cpp`, `libraries/AP_Param/AP_Param.h`, `libraries/AP_Param/AP_ParamT.cpp` |
| `libraries/AC_PID/AC_PID` | 555 | 67 | `libraries/AC_PID/AC_PID.cpp`, `libraries/AC_PID/AC_PID_2D.cpp`, `libraries/AC_PID/AC_P_2D.cpp`, `libraries/AC_PID/AC_PID_Basic.cpp`, `libraries/AC_PID/AC_P_1D.cpp`, `libraries/AC_PID/AC_P.h` (+4) |
| `libraries/AC_AttitudeControl/AC_AttitudeControl` | 2406 | 201 | `libraries/AC_AttitudeControl/AC_PosControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl.h`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.h`, `libraries/AC_AttitudeControl/AC_CommandModel.h` (+1) |
| `libraries/AC_WPNav/AC_WPNav` | 726 | 63 | `libraries/AC_WPNav/AC_WPNav.cpp`, `libraries/AC_WPNav/AC_Circle.cpp`, `libraries/AC_WPNav/AC_Loiter.cpp`, `libraries/AC_WPNav/AC_WPNav.h`, `libraries/AC_WPNav/AC_Circle.h`, `libraries/AC_WPNav/AC_Loiter.h` |
| `libraries/AP_SurfaceDistance/AP_SurfaceDistance` | 43 | 6 | `libraries/AP_SurfaceDistance/AP_SurfaceDistance.h`, `libraries/AP_SurfaceDistance/AP_SurfaceDistance.cpp` |
| `libraries/AP_Mission/AP_Mission` | 1364 | 64 | `libraries/AP_Mission/AP_Mission.cpp`, `libraries/AP_Mission/AP_Mission_Commands.cpp` |
| `libraries/AP_BoardConfig/AP_BoardConfig` | 163 | 17 | `libraries/AP_BoardConfig/AP_BoardConfig.cpp`, `libraries/AP_BoardConfig/board_drivers.cpp`, `libraries/AP_BoardConfig/AP_BoardConfig.h` |
| `libraries/RC_Channel/RC_Channel` | 779 | 62 | `libraries/RC_Channel/RC_Channel.cpp`, `libraries/RC_Channel/RC_Channel.h`, `libraries/RC_Channel/RC_Channels.cpp` |
| `libraries/AP_Arming/AP_Arming` | 137 | 15 | `libraries/AP_Arming/AP_Arming.cpp`, `libraries/AP_Arming/AP_Arming.h` |
| `ArduCopter/ArduCopter` | 2416 | 361 | `ArduCopter/mode.h`, `ArduCopter/mode.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/mode_guided.cpp`, `ArduCopter/autoyaw.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp` (+25) |
| `libraries/AP_Notify/AP_Notify` | 50 | 5 | `libraries/AP_Notify/AP_Notify.cpp` |
| `Dispatch` | 581 | 25 | `(generated)` |
| `libraries/AP_Motors/AP_Motors` | 917 | 73 | `libraries/AP_Motors/AP_MotorsMatrix.cpp`, `libraries/AP_Motors/AP_Motors_Class.h`, `libraries/AP_Motors/AP_MotorsMulticopter.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.cpp`, `libraries/AP_Motors/AP_Motors_Class.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.h` (+1) |
| `libraries/AP_Common/AP_Common` | 1351 | 135 | `libraries/AP_Common/Location.cpp`, `libraries/AP_Common/AP_Common.h`, `libraries/AP_Common/Bitmask.h`, `libraries/AP_Common/AP_Common.cpp`, `libraries/AP_Common/Location.h`, `libraries/AP_Common/AP_FWVersion.cpp` (+1) |
| `libraries/GCS_MAVLink/GCS_MAVLink` | 1411 | 130 | `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/GCS_MAVLink/GCS_MAVLink.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp`, `libraries/GCS_MAVLink/GCS.cpp`, `libraries/GCS_MAVLink/GCS.h`, `libraries/GCS_MAVLink/MissionItemProtocol.cpp` (+5) |
| `libraries/AP_BattMonitor/AP_BattMonitor` | 1012 | 63 | `libraries/AP_BattMonitor/AP_BattMonitor.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Backend.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Analog.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Params.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Backend.h`, `libraries/AP_BattMonitor/AP_BattMonitor_Analog.h` (+1) |
| `libraries/AP_Vehicle/AP_Vehicle` | 64 | 8 | `libraries/AP_Vehicle/AP_Vehicle.cpp` |
| `mavlink/mavlink` | 3090 | 282 | `mavlink_helpers.h`, `mavlink_types.h`, `checksum.h`, `mavlink_msg_rc_channels.h`, `mavlink_msg_system_time.h`, `mavlink_msg_timesync.h` (+64) |
| `libraries/AP_RCMapper/AP_RCMapper` | 20 | 2 | `libraries/AP_RCMapper/AP_RCMapper.cpp` |
| `libraries/AP_CANManager/AP_CANManager` | 20 | 2 | `libraries/AP_CANManager/AP_CANManager.cpp` |
| `libraries/AP_Scheduler/AP_Scheduler` | 425 | 30 | `libraries/AP_Scheduler/AP_Scheduler.cpp`, `libraries/AP_Scheduler/PerfInfo.cpp`, `libraries/AP_Scheduler/PerfInfo.h` |
| `libraries/SRV_Channel/SRV_Channel` | 821 | 53 | `libraries/SRV_Channel/SRV_Channel_aux.cpp`, `libraries/SRV_Channel/SRV_Channel.cpp`, `libraries/SRV_Channel/SRV_Channels.cpp`, `libraries/SRV_Channel/SRV_Channel.h`, `libraries/SRV_Channel/SRV_Channel_config.h` |
| `libraries/AP_Math/AP_Math_2` | 84 | 8 | `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/AP_Math.cpp` |
| `libraries/AP_HAL/AP_HAL_2` | 80 | 8 | `libraries/AP_HAL/Util.cpp`, `libraries/AP_HAL/utility/functor.h` |
| `libraries/Filter/Filter_2` | 181 | 6 | `libraries/Filter/SlewLimiter.cpp`, `libraries/Filter/LowPassFilter.cpp` |
| `libraries/AP_Param/AP_Param_2` | 389 | 23 | `libraries/AP_Param/AP_Param.cpp`, `libraries/AP_Param/AP_ParamT.cpp`, `libraries/AP_Param/AP_Param.h` |
| `libraries/AC_PID/AC_PID_2` | 599 | 20 | `libraries/AC_PID/AC_PID.cpp`, `libraries/AC_PID/AC_PID_2D.cpp`, `libraries/AC_PID/AC_PID_Basic.cpp`, `libraries/AC_PID/AC_P_1D.cpp`, `libraries/AC_PID/AC_P_2D.cpp` |
| `libraries/AP_GPS/AP_GPS` | 15 | 2 | `libraries/AP_GPS/AP_GPS.cpp` |
| `libraries/AC_AttitudeControl/AC_AttitudeControl_2` | 1905 | 67 | `libraries/AC_AttitudeControl/AC_AttitudeControl.cpp`, `libraries/AC_AttitudeControl/AC_PosControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp` |
| `libraries/AC_WPNav/AC_WPNav_2` | 1515 | 56 | `libraries/AC_WPNav/AC_WPNav.cpp`, `libraries/AC_WPNav/AC_Circle.cpp`, `libraries/AC_WPNav/AC_Loiter.cpp`, `libraries/AC_WPNav/AC_WPNav.h` |
| `libraries/AP_Mission/AP_Mission_2` | 1119 | 24 | `libraries/AP_Mission/AP_Mission.cpp` |
| `libraries/AP_InternalError/AP_InternalError` | 55 | 5 | `libraries/AP_InternalError/AP_InternalError.cpp`, `libraries/AP_InternalError/AP_InternalError.h` |
| `libraries/RC_Channel/RC_Channel_2` | 296 | 28 | `libraries/RC_Channel/RC_Channels.cpp`, `libraries/RC_Channel/RC_Channel.cpp`, `libraries/RC_Channel/RC_Channel.h` |
| `libraries/AP_Arming/AP_Arming_2` | 41 | 3 | `libraries/AP_Arming/AP_Arming.cpp` |
| `ArduCopter/ArduCopter_2` | 4086 | 184 | `ArduCopter/mode_guided.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/mode.cpp`, `ArduCopter/autoyaw.cpp`, `ArduCopter/mode_rtl.cpp` (+20) |
| `libraries/AP_SerialManager/AP_SerialManager` | 279 | 14 | `libraries/AP_SerialManager/AP_SerialManager.cpp` |
| `Dispatch_2` | 204 | 9 | `(generated)` |
| `libraries/AP_Motors/AP_Motors_2` | 1731 | 47 | `libraries/AP_Motors/AP_MotorsMulticopter.cpp`, `libraries/AP_Motors/AP_MotorsMatrix.cpp`, `libraries/AP_Motors/AP_Motors_Class.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.cpp` |
| `libraries/GCS_MAVLink/GCS_MAVLink_2` | 3922 | 175 | `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/GCS_MAVLink/MissionItemProtocol.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp`, `libraries/GCS_MAVLink/MAVLink_routing.cpp`, `libraries/GCS_MAVLink/GCS.cpp`, `libraries/GCS_MAVLink/MissionItemProtocol_Waypoints.cpp` (+2) |
| `libraries/AP_BattMonitor/AP_BattMonitor_2` | 214 | 6 | `libraries/AP_BattMonitor/AP_BattMonitor_Backend.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor.cpp` |
| `libraries/AP_Vehicle/AP_Vehicle_2` | 172 | 8 | `libraries/AP_Vehicle/AP_Vehicle.cpp`, `libraries/AP_Vehicle/AP_Vehicle.h`, `libraries/AP_Vehicle/Parameters.cpp` |
| `libraries/AP_Param/AP_Param_3` | 240 | 8 | `libraries/AP_Param/AP_Param.cpp` |
| `libraries/AP_Mission/AP_Mission_3` | 557 | 21 | `libraries/AP_Mission/AP_Mission.cpp`, `libraries/AP_Mission/AP_Mission_ChangeDetector.cpp`, `libraries/AP_Mission/AP_Mission_Commands.cpp` |
| `World` | 108 | 4 | `(generated)` |
| `libraries/AP_BoardConfig/AP_BoardConfig_2` | 67 | 4 | `libraries/AP_BoardConfig/board_drivers.cpp`, `libraries/AP_BoardConfig/AP_BoardConfig.cpp` |
| `libraries/AP_Arming/AP_Arming_3` | 1127 | 53 | `libraries/AP_Arming/AP_Arming.cpp` |
| `ArduCopter/ArduCopter_3` | 3365 | 137 | `ArduCopter/AP_Arming_Copter.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/crash_check.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `ArduCopter/mode_rtl.cpp`, `ArduCopter/mode.cpp` (+23) |
| `Dispatch_3` | 48 | 2 | `(generated)` |
| `libraries/GCS_MAVLink/GCS_MAVLink_3` | 593 | 15 | `libraries/GCS_MAVLink/GCS_Common.cpp` |
| `Startup` | 93 | 2 | `(generated)` |
| `Arming` | 616 | 24 | `libraries/GCS_MAVLink/GCS_Common.cpp`, `ArduCopter/AP_Arming_Copter.cpp`, `libraries/AP_Arming/AP_Arming.cpp`, `ArduCopter/motors.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp` |
| `ModeSwitching` | 5505 | 217 | `ArduCopter/events.cpp`, `ArduCopter/mode_auto.cpp`, `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/RC_Channel/RC_Channel.cpp`, `ArduCopter/mode_rtl.cpp`, `libraries/AP_HAL/utility/functor.h` (+18) |
| `GcsMessages` | 528 | 23 | `libraries/GCS_MAVLink/GCS_Common.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `libraries/AP_Vehicle/AP_Vehicle.cpp`, `ArduCopter/system.cpp`, `libraries/RC_Channel/RC_Channels.cpp`, `ArduCopter/mode.cpp` (+2) |
| `SchedulerLoop` | 514 | 16 | `libraries/AP_Scheduler/AP_Scheduler.cpp`, `(generated)`, `libraries/AP_Vehicle/AP_Vehicle.cpp`, `libraries/AP_HAL/utility/functor.h` |

## ArduPilot source files

| source file | modules (items) |
|---|---|
| `(Dispatch: generated)` | `Dispatch` (25), `Dispatch_2` (9), `Dispatch_3` (2), `ModeSwitching` (7), `SchedulerLoop` (2) |
| `(Layout: generated)` | `Layout` (390) |
| `(Startup: generated)` | `Startup` (2) |
| `(World: generated)` | `World` (4) |
| `ArduCopter/AP_Arming_Copter.cpp` | `ArduCopter/ArduCopter` (6), `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (24), `Arming` (5) |
| `ArduCopter/AP_Arming_Copter.h` | `ArduCopter/ArduCopter` (2) |
| `ArduCopter/AP_State.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (2), `ModeSwitching` (1) |
| `ArduCopter/Attitude.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (12) |
| `ArduCopter/Copter.cpp` | `ArduCopter/ArduCopter` (3), `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (6), `ModeSwitching` (2), `GcsMessages` (1) |
| `ArduCopter/Copter.h` | `ArduCopter/ArduCopter` (4) |
| `ArduCopter/GCS_Copter.cpp` | `ArduCopter/ArduCopter_2` (1) |
| `ArduCopter/GCS_MAVLink_Copter.cpp` | `ArduCopter/ArduCopter` (11), `ArduCopter/ArduCopter_2` (29), `ArduCopter/ArduCopter_3` (9), `Arming` (3), `ModeSwitching` (3), `GcsMessages` (2) |
| `ArduCopter/GCS_MAVLink_Copter.h` | `ArduCopter/ArduCopter` (2) |
| `ArduCopter/Parameters.cpp` | `ArduCopter/ArduCopter_3` (2) |
| `ArduCopter/Parameters.h` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (1) |
| `ArduCopter/RC_Channel_Copter.cpp` | `ArduCopter/ArduCopter` (8), `ArduCopter/ArduCopter_3` (2), `ModeSwitching` (6) |
| `ArduCopter/RC_Channel_Copter.h` | `ArduCopter/ArduCopter` (3) |
| `ArduCopter/autoyaw.cpp` | `ArduCopter/ArduCopter` (9), `ArduCopter/ArduCopter_2` (9) |
| `ArduCopter/avoidance.cpp` | `ArduCopter/ArduCopter` (2) |
| `ArduCopter/baro_ground_effect.cpp` | `ArduCopter/ArduCopter_3` (1) |
| `ArduCopter/commands.cpp` | `ArduCopter/ArduCopter_3` (7) |
| `ArduCopter/compassmot.cpp` | `ArduCopter/ArduCopter_3` (1) |
| `ArduCopter/crash_check.cpp` | `ArduCopter/ArduCopter_3` (6) |
| `ArduCopter/ekf_check.cpp` | `ArduCopter/ArduCopter` (1), `ArduCopter/ArduCopter_2` (2), `ArduCopter/ArduCopter_3` (4), `ModeSwitching` (2) |
| `ArduCopter/esc_calibration.cpp` | `ArduCopter/ArduCopter` (1), `ArduCopter/ArduCopter_3` (4), `ModeSwitching` (4) |
| `ArduCopter/events.cpp` | `ArduCopter/ArduCopter` (6), `ArduCopter/ArduCopter_2` (2), `ArduCopter/ArduCopter_3` (10), `ModeSwitching` (26) |
| `ArduCopter/failsafe.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_3` (1) |
| `ArduCopter/inertia.cpp` | `ArduCopter/ArduCopter_2` (2) |
| `ArduCopter/land_detector.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (4) |
| `ArduCopter/mode.cpp` | `ArduCopter/ArduCopter` (59), `ArduCopter/ArduCopter_2` (16), `ArduCopter/ArduCopter_3` (9), `ModeSwitching` (7), `GcsMessages` (1) |
| `ArduCopter/mode.h` | `ArduCopter/ArduCopter` (151), `ModeSwitching` (1) |
| `ArduCopter/mode_althold.cpp` | `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (2) |
| `ArduCopter/mode_auto.cpp` | `ArduCopter/ArduCopter` (31), `ArduCopter/ArduCopter_2` (21), `ArduCopter/ArduCopter_3` (15), `ModeSwitching` (52) |
| `ArduCopter/mode_brake.cpp` | `ArduCopter/ArduCopter_2` (1), `ModeSwitching` (2) |
| `ArduCopter/mode_circle.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (3) |
| `ArduCopter/mode_guided.cpp` | `ArduCopter/ArduCopter` (26), `ArduCopter/ArduCopter_2` (42), `ArduCopter/ArduCopter_3` (2), `ModeSwitching` (4) |
| `ArduCopter/mode_land.cpp` | `ArduCopter/ArduCopter` (3), `ArduCopter/ArduCopter_2` (3), `ModeSwitching` (4) |
| `ArduCopter/mode_loiter.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (2), `ArduCopter/ArduCopter_3` (2) |
| `ArduCopter/mode_rtl.cpp` | `ArduCopter/ArduCopter` (7), `ArduCopter/ArduCopter_2` (16), `ArduCopter/ArduCopter_3` (6), `ModeSwitching` (8) |
| `ArduCopter/mode_stabilize.cpp` | `ArduCopter/ArduCopter_3` (2) |
| `ArduCopter/motor_test.cpp` | `ArduCopter/ArduCopter_3` (4) |
| `ArduCopter/motors.cpp` | `ArduCopter/ArduCopter_3` (3), `Arming` (2) |
| `ArduCopter/navigation.cpp` | `ArduCopter/ArduCopter_2` (5) |
| `ArduCopter/radio.cpp` | `ArduCopter/ArduCopter` (2), `ArduCopter/ArduCopter_2` (3), `ArduCopter/ArduCopter_3` (1), `ModeSwitching` (3) |
| `ArduCopter/sensors.cpp` | `ArduCopter/ArduCopter` (3), `ArduCopter/ArduCopter_2` (1), `ArduCopter/ArduCopter_3` (1) |
| `ArduCopter/standby.cpp` | `ArduCopter/ArduCopter` (1) |
| `ArduCopter/system.cpp` | `ArduCopter/ArduCopter` (3), `ArduCopter/ArduCopter_2` (6), `ArduCopter/ArduCopter_3` (1), `GcsMessages` (1) |
| `ArduCopter/takeoff.cpp` | `ArduCopter/ArduCopter` (3), `ArduCopter/ArduCopter_2` (2), `ArduCopter/ArduCopter_3` (4), `ModeSwitching` (2) |
| `ArduCopter/takeoff_check.cpp` | `ArduCopter/ArduCopter_3` (2) |
| `checksum.h` | `mavlink/mavlink` (5) |
| `libraries/AC_AttitudeControl/AC_AttitudeControl.cpp` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (45), `libraries/AC_AttitudeControl/AC_AttitudeControl_2` (26) |
| `libraries/AC_AttitudeControl/AC_AttitudeControl.h` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (19) |
| `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (6), `libraries/AC_AttitudeControl/AC_AttitudeControl_2` (15) |
| `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.h` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (11) |
| `libraries/AC_AttitudeControl/AC_CommandModel.cpp` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (1) |
| `libraries/AC_AttitudeControl/AC_CommandModel.h` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (3) |
| `libraries/AC_AttitudeControl/AC_PosControl.cpp` | `libraries/AC_AttitudeControl/AC_AttitudeControl` (116), `libraries/AC_AttitudeControl/AC_AttitudeControl_2` (26) |
| `libraries/AC_PID/AC_P.h` | `libraries/AC_PID/AC_PID` (3) |
| `libraries/AC_PID/AC_PID.cpp` | `libraries/AC_PID/AC_PID` (29), `libraries/AC_PID/AC_PID_2` (7) |
| `libraries/AC_PID/AC_PID.h` | `libraries/AC_PID/AC_PID` (1) |
| `libraries/AC_PID/AC_PID_2D.cpp` | `libraries/AC_PID/AC_PID` (12), `libraries/AC_PID/AC_PID_2` (4) |
| `libraries/AC_PID/AC_PID_Basic.cpp` | `libraries/AC_PID/AC_PID` (6), `libraries/AC_PID/AC_PID_2` (5) |
| `libraries/AC_PID/AC_P_1D.cpp` | `libraries/AC_PID/AC_PID` (3), `libraries/AC_PID/AC_PID_2` (2) |
| `libraries/AC_PID/AC_P_1D.h` | `libraries/AC_PID/AC_PID` (2) |
| `libraries/AC_PID/AC_P_2D.cpp` | `libraries/AC_PID/AC_PID` (7), `libraries/AC_PID/AC_PID_2` (2) |
| `libraries/AC_PID/AC_P_2D.h` | `libraries/AC_PID/AC_PID` (2) |
| `libraries/AC_PID/AP_PIDInfo.h` | `libraries/AC_PID/AC_PID` (2) |
| `libraries/AC_WPNav/AC_Circle.cpp` | `libraries/AC_WPNav/AC_WPNav` (16), `libraries/AC_WPNav/AC_WPNav_2` (8) |
| `libraries/AC_WPNav/AC_Circle.h` | `libraries/AC_WPNav/AC_WPNav` (8) |
| `libraries/AC_WPNav/AC_Loiter.cpp` | `libraries/AC_WPNav/AC_WPNav` (5), `libraries/AC_WPNav/AC_WPNav_2` (9) |
| `libraries/AC_WPNav/AC_Loiter.h` | `libraries/AC_WPNav/AC_WPNav` (4) |
| `libraries/AC_WPNav/AC_WPNav.cpp` | `libraries/AC_WPNav/AC_WPNav` (13), `libraries/AC_WPNav/AC_WPNav_2` (32) |
| `libraries/AC_WPNav/AC_WPNav.h` | `libraries/AC_WPNav/AC_WPNav` (17), `libraries/AC_WPNav/AC_WPNav_2` (7) |
| `libraries/AP_Arming/AP_Arming.cpp` | `libraries/AP_Arming/AP_Arming` (13), `libraries/AP_Arming/AP_Arming_2` (3), `libraries/AP_Arming/AP_Arming_3` (53), `Arming` (6) |
| `libraries/AP_Arming/AP_Arming.h` | `libraries/AP_Arming/AP_Arming` (2) |
| `libraries/AP_BattMonitor/AP_BattMonitor.cpp` | `libraries/AP_BattMonitor/AP_BattMonitor` (32), `libraries/AP_BattMonitor/AP_BattMonitor_2` (4), `ModeSwitching` (3) |
| `libraries/AP_BattMonitor/AP_BattMonitor.h` | `libraries/AP_BattMonitor/AP_BattMonitor` (1) |
| `libraries/AP_BattMonitor/AP_BattMonitor_Analog.cpp` | `libraries/AP_BattMonitor/AP_BattMonitor` (3) |
| `libraries/AP_BattMonitor/AP_BattMonitor_Analog.h` | `libraries/AP_BattMonitor/AP_BattMonitor` (3) |
| `libraries/AP_BattMonitor/AP_BattMonitor_Backend.cpp` | `libraries/AP_BattMonitor/AP_BattMonitor` (18), `libraries/AP_BattMonitor/AP_BattMonitor_2` (2) |
| `libraries/AP_BattMonitor/AP_BattMonitor_Backend.h` | `libraries/AP_BattMonitor/AP_BattMonitor` (4) |
| `libraries/AP_BattMonitor/AP_BattMonitor_Params.cpp` | `libraries/AP_BattMonitor/AP_BattMonitor` (2) |
| `libraries/AP_BoardConfig/AP_BoardConfig.cpp` | `libraries/AP_BoardConfig/AP_BoardConfig` (10), `libraries/AP_BoardConfig/AP_BoardConfig_2` (2) |
| `libraries/AP_BoardConfig/AP_BoardConfig.h` | `libraries/AP_BoardConfig/AP_BoardConfig` (2) |
| `libraries/AP_BoardConfig/board_drivers.cpp` | `libraries/AP_BoardConfig/AP_BoardConfig` (5), `libraries/AP_BoardConfig/AP_BoardConfig_2` (2) |
| `libraries/AP_CANManager/AP_CANManager.cpp` | `libraries/AP_CANManager/AP_CANManager` (2) |
| `libraries/AP_Common/AP_Common.cpp` | `libraries/AP_Common/AP_Common` (3) |
| `libraries/AP_Common/AP_Common.h` | `libraries/AP_Common/AP_Common` (54) |
| `libraries/AP_Common/AP_FWVersion.cpp` | `libraries/AP_Common/AP_Common` (1) |
| `libraries/AP_Common/AP_FWVersion.h` | `libraries/AP_Common/AP_Common` (1) |
| `libraries/AP_Common/Bitmask.h` | `libraries/AP_Common/AP_Common` (22) |
| `libraries/AP_Common/Location.cpp` | `libraries/AP_Common/AP_Common` (52) |
| `libraries/AP_Common/Location.h` | `libraries/AP_Common/AP_Common` (2) |
| `libraries/AP_GPS/AP_GPS.cpp` | `libraries/AP_GPS/AP_GPS` (2) |
| `libraries/AP_HAL/Scheduler.cpp` | `libraries/AP_HAL/AP_HAL` (1) |
| `libraries/AP_HAL/Semaphores.h` | `libraries/AP_HAL/AP_HAL` (4) |
| `libraries/AP_HAL/Storage.cpp` | `libraries/AP_HAL/AP_HAL` (2) |
| `libraries/AP_HAL/Util.cpp` | `libraries/AP_HAL/AP_HAL` (1), `libraries/AP_HAL/AP_HAL_2` (5) |
| `libraries/AP_HAL/system.cpp` | `ModeSwitching` (1) |
| `libraries/AP_HAL/utility/RingBuffer.cpp` | `libraries/AP_HAL/AP_HAL` (16) |
| `libraries/AP_HAL/utility/ftoa_engine.cpp` | `libraries/AP_HAL/AP_HAL` (2) |
| `libraries/AP_HAL/utility/functor.h` | `libraries/AP_HAL/AP_HAL` (7), `libraries/AP_HAL/AP_HAL_2` (3), `ModeSwitching` (28), `SchedulerLoop` (7) |
| `libraries/AP_HAL/utility/print_vprintf.cpp` | `libraries/AP_HAL/AP_HAL` (2) |
| `libraries/AP_HAL/utility/utoa_invert.cpp` | `libraries/AP_HAL/AP_HAL` (2) |
| `libraries/AP_InternalError/AP_InternalError.cpp` | `libraries/AP_InternalError/AP_InternalError` (2) |
| `libraries/AP_InternalError/AP_InternalError.h` | `libraries/AP_InternalError/AP_InternalError` (3) |
| `libraries/AP_Math/AP_Math.cpp` | `libraries/AP_Math/AP_Math` (15), `libraries/AP_Math/AP_Math_2` (1) |
| `libraries/AP_Math/AP_Math.h` | `libraries/AP_Math/AP_Math` (47), `libraries/AP_Math/AP_Math_2` (7) |
| `libraries/AP_Math/SCurve.cpp` | `libraries/AP_Math/AP_Math` (61) |
| `libraries/AP_Math/SplineCurve.cpp` | `libraries/AP_Math/AP_Math` (17) |
| `libraries/AP_Math/SplineCurve.h` | `libraries/AP_Math/AP_Math` (1) |
| `libraries/AP_Math/control.cpp` | `libraries/AP_Math/AP_Math` (42) |
| `libraries/AP_Math/definitions.h` | `libraries/AP_Math/AP_Math` (2) |
| `libraries/AP_Math/ftype.h` | `libraries/AP_Math/AP_Math` (18) |
| `libraries/AP_Math/location.cpp` | `libraries/AP_Math/AP_Math` (8) |
| `libraries/AP_Math/location.h` | `libraries/AP_Math/AP_Math` (4) |
| `libraries/AP_Math/matrix3.cpp` | `libraries/AP_Math/AP_Math` (2) |
| `libraries/AP_Math/quaternion.cpp` | `libraries/AP_Math/AP_Math` (18) |
| `libraries/AP_Math/quaternion.h` | `libraries/AP_Math/AP_Math` (4) |
| `libraries/AP_Math/vector2.cpp` | `libraries/AP_Math/AP_Math` (37) |
| `libraries/AP_Math/vector2.h` | `libraries/AP_Math/AP_Math` (10) |
| `libraries/AP_Math/vector3.cpp` | `libraries/AP_Math/AP_Math` (28) |
| `libraries/AP_Math/vector3.h` | `libraries/AP_Math/AP_Math` (32) |
| `libraries/AP_Mission/AP_Mission.cpp` | `libraries/AP_Mission/AP_Mission` (52), `libraries/AP_Mission/AP_Mission_2` (24), `libraries/AP_Mission/AP_Mission_3` (17), `ModeSwitching` (21) |
| `libraries/AP_Mission/AP_Mission_ChangeDetector.cpp` | `libraries/AP_Mission/AP_Mission_3` (2) |
| `libraries/AP_Mission/AP_Mission_Commands.cpp` | `libraries/AP_Mission/AP_Mission` (12), `libraries/AP_Mission/AP_Mission_3` (2) |
| `libraries/AP_Motors/AP_MotorsMatrix.cpp` | `libraries/AP_Motors/AP_Motors` (7), `libraries/AP_Motors/AP_Motors_2` (14) |
| `libraries/AP_Motors/AP_MotorsMatrix.h` | `libraries/AP_Motors/AP_Motors` (1) |
| `libraries/AP_Motors/AP_MotorsMulticopter.cpp` | `libraries/AP_Motors/AP_Motors` (13), `libraries/AP_Motors/AP_Motors_2` (21) |
| `libraries/AP_Motors/AP_Motors_Class.cpp` | `libraries/AP_Motors/AP_Motors` (7), `libraries/AP_Motors/AP_Motors_2` (10) |
| `libraries/AP_Motors/AP_Motors_Class.h` | `libraries/AP_Motors/AP_Motors` (36) |
| `libraries/AP_Motors/AP_Motors_Thrust_Linearization.cpp` | `libraries/AP_Motors/AP_Motors` (5), `libraries/AP_Motors/AP_Motors_2` (2) |
| `libraries/AP_Motors/AP_Motors_Thrust_Linearization.h` | `libraries/AP_Motors/AP_Motors` (4) |
| `libraries/AP_NavEKF/AP_Nav_Common.h` | `libraries/AP_NavEKF/AP_NavEKF` (2) |
| `libraries/AP_Notify/AP_Notify.cpp` | `libraries/AP_Notify/AP_Notify` (5) |
| `libraries/AP_Param/AP_Param.cpp` | `libraries/AP_Param/AP_Param` (107), `libraries/AP_Param/AP_Param_2` (13), `libraries/AP_Param/AP_Param_3` (8) |
| `libraries/AP_Param/AP_Param.h` | `libraries/AP_Param/AP_Param` (88), `libraries/AP_Param/AP_Param_2` (1) |
| `libraries/AP_Param/AP_ParamT.cpp` | `libraries/AP_Param/AP_Param` (14), `libraries/AP_Param/AP_Param_2` (9) |
| `libraries/AP_RCMapper/AP_RCMapper.cpp` | `libraries/AP_RCMapper/AP_RCMapper` (2) |
| `libraries/AP_RTC/JitterCorrection.cpp` | `libraries/AP_RTC/AP_RTC` (1) |
| `libraries/AP_Scheduler/AP_Scheduler.cpp` | `libraries/AP_Scheduler/AP_Scheduler` (17), `SchedulerLoop` (3) |
| `libraries/AP_Scheduler/PerfInfo.cpp` | `libraries/AP_Scheduler/AP_Scheduler` (11) |
| `libraries/AP_Scheduler/PerfInfo.h` | `libraries/AP_Scheduler/AP_Scheduler` (2) |
| `libraries/AP_SerialManager/AP_SerialManager.cpp` | `libraries/AP_SerialManager/AP_SerialManager` (14) |
| `libraries/AP_SurfaceDistance/AP_SurfaceDistance.cpp` | `libraries/AP_SurfaceDistance/AP_SurfaceDistance` (2) |
| `libraries/AP_SurfaceDistance/AP_SurfaceDistance.h` | `libraries/AP_SurfaceDistance/AP_SurfaceDistance` (4) |
| `libraries/AP_Vehicle/AP_Vehicle.cpp` | `libraries/AP_Vehicle/AP_Vehicle` (8), `libraries/AP_Vehicle/AP_Vehicle_2` (5), `GcsMessages` (3), `SchedulerLoop` (4) |
| `libraries/AP_Vehicle/AP_Vehicle.h` | `libraries/AP_Vehicle/AP_Vehicle_2` (1) |
| `libraries/AP_Vehicle/Parameters.cpp` | `libraries/AP_Vehicle/AP_Vehicle_2` (2) |
| `libraries/Filter/DerivativeFilter.cpp` | `libraries/Filter/Filter` (3) |
| `libraries/Filter/FilterClass.h` | `libraries/Filter/Filter` (2) |
| `libraries/Filter/FilterWithBuffer.h` | `libraries/Filter/Filter` (2) |
| `libraries/Filter/LowPassFilter.cpp` | `libraries/Filter/Filter` (15), `libraries/Filter/Filter_2` (4) |
| `libraries/Filter/LowPassFilter.h` | `libraries/Filter/Filter` (1) |
| `libraries/Filter/SlewLimiter.cpp` | `libraries/Filter/Filter` (3), `libraries/Filter/Filter_2` (2) |
| `libraries/GCS_MAVLink/GCS.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (4), `libraries/GCS_MAVLink/GCS_MAVLink_2` (10) |
| `libraries/GCS_MAVLink/GCS.h` | `libraries/GCS_MAVLink/GCS_MAVLink` (7) |
| `libraries/GCS_MAVLink/GCS_Common.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (90), `libraries/GCS_MAVLink/GCS_MAVLink_2` (103), `libraries/GCS_MAVLink/GCS_MAVLink_3` (15), `Arming` (5), `ModeSwitching` (11), `GcsMessages` (11) |
| `libraries/GCS_MAVLink/GCS_MAVLink.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (8), `libraries/GCS_MAVLink/GCS_MAVLink_2` (1) |
| `libraries/GCS_MAVLink/GCS_MAVLink.h` | `libraries/GCS_MAVLink/GCS_MAVLink` (2) |
| `libraries/GCS_MAVLink/GCS_Param.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (3), `libraries/GCS_MAVLink/GCS_MAVLink_2` (17), `Arming` (3) |
| `libraries/GCS_MAVLink/GCS_Signing.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (1), `libraries/GCS_MAVLink/GCS_MAVLink_2` (2) |
| `libraries/GCS_MAVLink/MAVLink_routing.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink_2` (9) |
| `libraries/GCS_MAVLink/MissionItemProtocol.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (5), `libraries/GCS_MAVLink/GCS_MAVLink_2` (21) |
| `libraries/GCS_MAVLink/MissionItemProtocol.h` | `libraries/GCS_MAVLink/GCS_MAVLink` (3) |
| `libraries/GCS_MAVLink/MissionItemProtocol_Waypoints.cpp` | `libraries/GCS_MAVLink/GCS_MAVLink` (2), `libraries/GCS_MAVLink/GCS_MAVLink_2` (12) |
| `libraries/GCS_MAVLink/MissionItemProtocol_Waypoints.h` | `libraries/GCS_MAVLink/GCS_MAVLink` (5) |
| `libraries/RC_Channel/RC_Channel.cpp` | `libraries/RC_Channel/RC_Channel` (35), `libraries/RC_Channel/RC_Channel_2` (7), `ModeSwitching` (12), `GcsMessages` (2) |
| `libraries/RC_Channel/RC_Channel.h` | `libraries/RC_Channel/RC_Channel` (22), `libraries/RC_Channel/RC_Channel_2` (1) |
| `libraries/RC_Channel/RC_Channels.cpp` | `libraries/RC_Channel/RC_Channel` (5), `libraries/RC_Channel/RC_Channel_2` (20), `ModeSwitching` (7), `GcsMessages` (2) |
| `libraries/SRV_Channel/SRV_Channel.cpp` | `libraries/SRV_Channel/SRV_Channel` (12) |
| `libraries/SRV_Channel/SRV_Channel.h` | `libraries/SRV_Channel/SRV_Channel` (11) |
| `libraries/SRV_Channel/SRV_Channel_aux.cpp` | `libraries/SRV_Channel/SRV_Channel` (15) |
| `libraries/SRV_Channel/SRV_Channel_config.h` | `libraries/SRV_Channel/SRV_Channel` (7) |
| `libraries/SRV_Channel/SRV_Channels.cpp` | `libraries/SRV_Channel/SRV_Channel` (8) |
| `libraries/StorageManager/StorageManager.cpp` | `libraries/StorageManager/StorageManager` (18) |
| `libraries/StorageManager/StorageManager.h` | `libraries/StorageManager/StorageManager` (2) |
| `mavlink_helpers.h` | `mavlink/mavlink` (23) |
| `mavlink_msg_ahrs.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_ahrs2.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_attitude.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_attitude_quaternion.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_attitude_target.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_autopilot_version.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_available_modes.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_available_modes_monitor.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_battery_status.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_command_ack.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_command_int.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_command_long.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_ekf_status_report.h` | `mavlink/mavlink` (1) |
| `mavlink_msg_extended_sys_state.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_flight_information.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_global_position_int.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_gps2_raw.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_gps_global_origin.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_gps_raw_int.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_heartbeat.h` | `mavlink/mavlink` (6) |
| `mavlink_msg_highres_imu.h` | `mavlink/mavlink` (1) |
| `mavlink_msg_home_position.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_local_position_ned.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_meminfo.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_mission_ack.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_mission_clear_all.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_mission_count.h` | `mavlink/mavlink` (5) |
| `mavlink_msg_mission_current.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_mission_item.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_mission_item_int.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_mission_item_reached.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_mission_request.h` | `mavlink/mavlink` (5) |
| `mavlink_msg_mission_request_int.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_mission_request_list.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_mission_set_current.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_mission_write_partial_list.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_nav_controller_output.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_param_error.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_param_request_list.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_param_request_read.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_param_set.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_param_value.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_pid_tuning.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_position_target_global_int.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_position_target_local_ned.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_power_status.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_raw_imu.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_rc_channels.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_rc_channels_raw.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_request_data_stream.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_scaled_pressure.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_scaled_pressure2.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_scaled_pressure3.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_servo_output_raw.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_set_attitude_target.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_set_mode.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_set_position_target_global_int.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_set_position_target_local_ned.h` | `mavlink/mavlink` (3) |
| `mavlink_msg_statustext.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_sys_status.h` | `mavlink/mavlink` (2) |
| `mavlink_msg_system_time.h` | `mavlink/mavlink` (6) |
| `mavlink_msg_timesync.h` | `mavlink/mavlink` (6) |
| `mavlink_msg_utm_global_position.h` | `mavlink/mavlink` (1) |
| `mavlink_msg_vfr_hud.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_vibration.h` | `mavlink/mavlink` (4) |
| `mavlink_msg_wind.h` | `mavlink/mavlink` (4) |
| `mavlink_types.h` | `mavlink/mavlink` (24) |
| `protocol.h` | `mavlink/mavlink` (3) |
