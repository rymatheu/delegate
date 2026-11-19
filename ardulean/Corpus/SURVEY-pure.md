# Pure leaves: survey (fourth increment)

Every `f.pure'` constant of `Vehicle_lib` (381), grouped by the C++ source file its memory-side wrapper's docstring
names, with its return type, its fan-in, and the corpus theorems that name it. Generated 2026-11-16 from
`lean/Vehicle_lib.lean` (now split into the modules of `ArduLean/Vehicle/`) and `Corpus/Code/**`.

**Fan-in** is the number of distinct definitions of `Vehicle_lib` whose body refers to `f`, `f.pure'` or `f.body`
(a function's own wrapper and body not counted). `ardupilot/out/Vehicle/Vehicle_lib.callgraph.txt` lists only the
recursive components and the functor dispatch, not every edge, so the count is taken from the code text.

**Docstring file.** For accessors generated from macros or defined in class headers, the code's docstring names the
header the macro expanded in (`AP_Common.h`, `<scratch space>`, `stdint.h`); the corpus files group them by class
(e.g. `AC_PID::kP` is in `Code/AC_PID/Accessors.lean`).

**Covered**: the number of corpus theorems whose statement names the function (the audit counts a leaf as covered
with at least two). Value-returning leaves: 256 of 256 covered. Unit-returning leaves (125, almost all empty default
constructors of message and parameter structures, `f.pure' … = pure ()`): 1 covered; not targeted (OPEN.md).


## `AP_Param.h` (30)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_ParamT'float_4.operator_const_float__'1` | `UInt64` | 118 | 4 | `AP_Param/AP_Param.lean` |
| `AP_ParamT'short_2.operator_const_short__` | `UInt64` | 53 | 2 | `AP_Param/AP_Param.lean` |
| `AP_Param.AP_Param'2` | `Unit` | 52 | 0 |  |
| `AP_ParamT'signed_char_1.operator_const_signed_char__` | `UInt64` | 51 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamTBase'short_2.get` | `UInt64` | 20 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamTBase'float_4.get` | `UInt64` | 18 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamTBase'signed_char_1.get` | `UInt64` | 17 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamT'unsigned_int_3.operator_const_unsigned_int__` | `UInt64` | 16 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamT'unsigned_short_2.operator_const_unsigned_short__` | `UInt64` | 15 | 2 | `AP_Param/AP_Param.lean` |
| `AP_Param.Param_header.Param_header` | `Unit` | 9 | 0 |  |
| `AP_ParamT'int_3.operator_const_int__` | `UInt64` | 7 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamTBase'unsigned_short_2.get` | `UInt64` | 6 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamTBase'unsigned_int_3.get` | `UInt64` | 4 | 2 | `AP_Param/AP_Param.lean` |
| `AP_ParamT'unsigned_char_1.operator_const_unsigned_char__` | `UInt64` | 4 | 2 | `AP_Param/AP_Param.lean` |
| `AP_Param.EEPROM_header.EEPROM_header` | `Unit` | 1 | 0 |  |
| `AP_ParamV'Vector3_float_5.get` | `UInt64` | 1 | 2 | `AP_Param/AP_Param.lean` |
| `AP_Enum16'SRV_Channel_Function.AP_Enum16` | `Unit` | 1 | 0 |  |
| `AP_Param.ParamToken.ParamToken` | `Unit` | 1 | 0 |  |
| `AP_Enum'AP_Motors_PWMType.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_ParamTBase'int_3.get` | `UInt64` | 1 | 2 | `AP_Param/AP_Param.lean` |
| `AP_Enum'ModeRTL_RTLAltType.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'Parameters_FS_GCS_Action.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'Parameters_WPYawBehavior.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'Parameters_FS_THR_Action.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'Parameters_FS_EKF_Action.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'AP_Arming_Required.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum'AP_Arming_RequireLocation.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Enum16'GCS_Option.AP_Enum16` | `Unit` | 1 | 0 |  |
| `AP_Enum'AP_BattMonitor_Params_Type.AP_Enum` | `Unit` | 1 | 0 |  |
| `AP_Param.ConversionInfo.ConversionInfo` | `Unit` | 0 | 0 |  |

## `AP_Math.cpp` (6)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `constrain_value_line'float` | `Binary32` | 90 | 18 | `AC_PID/AC_PID.lean`, `AP_Math/AP_Math.lean` |
| `is_equal'float_float` | `Bool` | 16 | 4 | `AP_Math/AP_Math.lean` |
| `wrap_PI'float` | `Binary32` | 15 | 3 | `AP_Math/AP_Math.lean` |
| `safe_sqrt'float` | `Binary32` | 14 | 9 | `AP_Math/AP_Math.lean` |
| `wrap_2PI` | `Binary32` | 4 | 3 | `AP_Math/AP_Math.lean` |
| `is_equal'double_double` | `Bool` | 1 | 3 | `AP_Math/AP_Math.lean` |

## `<built-in> (as the code's docstring gives it)` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `is_positive'float` | `Bool` | 86 | 26 | `AC_PID/AC_PID.lean`, `AP_Math/AP_Math.lean`, `AP_Math/Control.lean`, `Filter/SlewLimiter.lean` |
| `is_negative'float` | `Bool` | 26 | 14 | `AC_PID/AC_PID.lean`, `AP_Math/AP_Math.lean`, `AP_Math/Control.lean` |

## `ftype.h` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `is_zero` | `Bool` | 57 | 25 | `AC_PID/AC_PID.lean`, `AP_Math/AP_Math.lean`, `AP_Math/Control.lean` |
| `is_zero'2` | `Bool` | 2 | 3 | `AP_Math/AP_Math.lean` |
| `norm'double_double` | `Binary64` | 2 | 2 | `AP_Math/AP_Math.lean` |
| `norm'double_double_double` | `Binary64` | 1 | 2 | `AP_Math/AP_Math.lean` |

## `AP_Math.h` (11)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `radians` | `Binary32` | 40 | 9 | `AP_Math/AP_Math.lean` |
| `sq` | `Binary32` | 28 | 11 | `AP_Math/AP_Math.lean`, `AP_Math/Control.lean` |
| `degrees` | `Binary32` | 10 | 6 | `AP_Math/AP_Math.lean` |
| `constrain_int16` | `Int16` | 6 | 6 | `AP_Math/AP_Math.lean` |
| `radians'2` | `Binary32` | 4 | 2 | `AP_Math/AP_Math.lean` |
| `sq'double` | `Binary64` | 2 | 2 | `AP_Math/AP_Math.lean` |
| `sq'double_double` | `Binary64` | 2 | 2 | `AP_Math/AP_Math.lean` |
| `norm` | `Binary32` | 1 | 4 | `AP_Math/AP_Math.lean` |
| `norm'2` | `Binary32` | 1 | 4 | `AP_Math/AP_Math.lean` |
| `sq'double_double_double` | `Binary64` | 1 | 2 | `AP_Math/AP_Math.lean` |
| `cd_to_rad` | `Binary32` | 1 | 8 | `AC_AttitudeControl/Accessors.lean`, `AP_Math/AP_Math.lean` |

## `vector3.h` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Vector3'float.xy` | `UInt64` | 37 | 2 | `AP_Math/Accessors.lean` |
| `Vector3'double.xy` | `UInt64` | 35 | 2 | `AP_Math/Accessors.lean` |
| `Vector3'float.operator__` | `UInt64` | 2 | 2 | `AP_Math/Accessors.lean` |

## `Copter.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Copter.gcs` | `UInt64` | 32 | 4 | `ArduCopter/Copter.lean` |

## `mode.cpp` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Mode.gcs` | `UInt64` | 17 | 3 | `ArduCopter/Copter.lean`, `ArduCopter/Mode.lean` |
| `Mode.get_avoidance_adjusted_climbrate_ms` | `Binary32` | 6 | 2 | `ArduCopter/Mode.lean` |
| `Copter.mode_from_mode_num` | `UInt64` | 1 | 3 | `ArduCopter/Copter.lean` |

## `RC_Channel_Copter.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `RC_Channels_Copter.channel` | `UInt64` | 16 | 4 | `RC_Channel/RC_Channel.lean` |

## `<scratch space> (as the code's docstring gives it)` (6)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_AttitudeControl.get_att_target_euler_rad` | `UInt64` | 12 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_AttitudeControl.get_roll_trim_rad` | `Binary32` | 3 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_AttitudeControl.get_attitude_target_ang_vel` | `UInt64` | 2 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `constrain_value'short` | `Int16` | 1 | 3 | `AP_Math/AP_Math.lean` |
| `AP_Motors.AP_Motors_limit.AP_Motors_limit` | `Unit` | 1 | 0 |  |
| `AC_AttitudeControl.get_roll_trim_cd` | `Binary32` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |

## `AP_Param.cpp` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_Param.type_size` | `UInt8` | 10 | 3 | `AP_Param/AP_Param.lean` |
| `AP_Param.reload_defaults_file` | `Unit` | 3 | 0 |  |
| `AP_Param_value_storage.AP_Param_value_storage` | `Unit` | 2 | 0 |  |

## `AP_Common.h (as the code's docstring gives it)` (70)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_PosControl.get_pos_estimate_NED_m` | `UInt64` | 9 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_P_2D.get_error` | `UInt64` | 8 | 3 | `AC_PID/Accessors.lean` |
| `AC_PosControl.get_vel_desired_NED_ms` | `UInt64` | 7 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PosControl.get_pos_desired_NED_m` | `UInt64` | 7 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PID_2D.get_error` | `UInt64` | 6 | 3 | `AC_PID/Accessors.lean` |
| `AC_PID.kP` | `UInt64` | 5 | 2 | `AC_PID/Accessors.lean` |
| `AC_PosControl.D_get_accel_pid` | `UInt64` | 4 | 2 | `AC_PID/AC_PID.lean` |
| `AC_P.kP` | `UInt64` | 4 | 2 | `AC_PID/Accessors.lean` |
| `MissionItemProtocol.free_upload_resources` | `Unit` | 4 | 0 |  |
| `AC_PosControl.D_get_pos_p` | `UInt64` | 3 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PID.kI` | `UInt64` | 3 | 3 | `AC_PID/Accessors.lean` |
| `AP_Param.param_save.param_save` | `Unit` | 2 | 0 |  |
| `ByteBuffer.IoVec.IoVec` | `Unit` | 2 | 0 |  |
| `AC_PID.ff` | `UInt64` | 2 | 3 | `AC_PID/Accessors.lean` |
| `AC_PosControl.NE_get_pos_p` | `UInt64` | 2 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PID_Basic.kP` | `UInt64` | 2 | 2 | `AC_PID/Accessors.lean` |
| `AC_PosControl.get_pos_offset_NED_m` | `UInt64` | 2 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `SplineCurve.get_destination_vel` | `UInt64` | 2 | 3 | `AP_Math/Accessors.lean` |
| `AC_PosControl.get_vel_estimate_NED_ms` | `UInt64` | 2 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PosControl.get_accel_target_NED_mss` | `UInt64` | 2 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AP_Mission.get_current_nav_cmd` | `UInt64` | 2 | 3 | `AP_Mission/AP_Mission.lean` |
| `AC_PID.get_pid_info` | `UInt64` | 2 | 3 | `AC_PID/Accessors.lean` |
| `SCurve.get_origin_to_destination` | `UInt64` | 2 | 3 | `AP_Math/Accessors.lean` |
| `AC_PID.filt_T_hz` | `UInt64` | 1 | 3 | `AC_PID/Accessors.lean` |
| `AC_PID.filt_E_hz` | `UInt64` | 1 | 3 | `AC_PID/Accessors.lean` |
| `AC_PID_2D.ff` | `UInt64` | 1 | 3 | `AC_PID/Accessors.lean` |
| `Mode.in_guided_mode` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AP_HAL.BetterStream.BetterStream` | `Unit` | 1 | 0 |  |
| `_assert_storage_size'Location_16_16._assert_storage_size` | `Unit` | 1 | 0 |  |
| `assert_storage_size'Location_16.assert_storage_size` | `Unit` | 1 | 0 |  |
| `_assert_storage_size'PackedContent_12_12._assert_storage_size` | `Unit` | 1 | 0 |  |
| `assert_storage_size'PackedContent_12.assert_storage_size` | `Unit` | 1 | 0 |  |
| `AC_PosControl.D_get_vel_pid` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_PID.kD` | `UInt64` | 1 | 3 | `AC_PID/Accessors.lean` |
| `AP_CANManager.get_num_drivers` | `UInt8` | 1 | 2 | `AP_Common/AP_Common.lean` |
| `Mode.allows_GCS_or_SCR_arming_with_throttle_high` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AP_BattMonitor_Backend.set_powered_state` | `Unit` | 1 | 0 |  |
| `Mode.allows_save_trim` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.pause` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.resume` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.exit` | `Unit` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.allows_entry_in_rc_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.init` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `MissionItemProtocol.allocate_update_resources` | `UInt32` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `Mode.set_speed_NE_ms` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.set_speed_down_ms` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.set_speed_up_ms` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.has_user_takeoff` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.get_wp` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.is_landing` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AP_BattMonitor_Backend.get_mavlink_fault_bitmask` | `UInt32` | 1 | 2 | `AP_BattMonitor/AP_BattMonitor.lean` |
| `SITL.SIM.simstate_send` | `Unit` | 1 | 0 |  |
| `SITL.SIM.sim_state_send` | `Unit` | 1 | 0 |  |
| `GCS.min_status_for_gps_healthy` | `UInt8` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `Mode.crosstrack_error_m` | `Binary32` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.wp_bearing_deg` | `Binary32` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.wp_distance_m` | `Binary32` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.enabled` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AC_PID.ac_pid_flags.ac_pid_flags` | `Unit` | 1 | 0 |  |
| `AP_Vehicle.set_control_channels` | `Unit` | 1 | 0 |  |
| `Mode.move_vehicle_on_ekf_reset` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `Mode.use_pilot_yaw` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AC_PID_2D.kP` | `UInt64` | 1 | 2 | `AC_PID/Accessors.lean` |
| `AC_PosControl.NE_get_vel_pid` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `Mode.crash_check_enabled` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AP_BattMonitor_Backend.calculate_mah` | `Binary32` | 1 | 3 | `AP_BattMonitor/AP_BattMonitor.lean` |
| `Mode.requires_terrain_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `AP_ExternalControl_Copter.AP_ExternalControl_Copter` | `Unit` | 1 | 0 |  |
| `AP_BattMonitor.cells.cells` | `Unit` | 1 | 0 |  |
| `Copter.AHRSTrimming.AHRSTrimming` | `Unit` | 1 | 0 |  |

## `LowPassFilter.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `DigitalLPF'float.get` | `UInt64` | 9 | 2 | `Filter/Filter.lean` |
| `DigitalLPF'Vector3_float.get` | `UInt64` | 3 | 2 | `Filter/Filter.lean` |

## `Semaphores.h` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `HALSITL.Semaphore.Semaphore` | `Unit` | 8 | 0 |  |
| `AP_HAL.Semaphore.Semaphore` | `Unit` | 1 | 0 |  |

## `system.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Copter.is_tradheli` | `Bool` | 8 | 2 | `ArduCopter/Copter.lean` |

## `AP_Mission.cpp` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_Mission.stored_in_location` | `Bool` | 7 | 4 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.cmd_has_location` | `Bool` | 4 | 3 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.is_landing_type_cmd` | `Bool` | 2 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.is_takeoff_type_cmd` | `Bool` | 2 | 3 | `AP_Mission/AP_Mission.lean` |

## `protocol.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `mavlink_msg_target_field` | `UInt8` | 7 | 3 | `GCS_MAVLink/GCS.lean` |

## `Location.cpp` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Location.diff_longitude` | `Int32` | 6 | 4 | `AP_Common/AP_Common.lean` |
| `Location.limit_lattitude` | `Int32` | 1 | 4 | `AP_Common/AP_Common.lean` |
| `Location.wrap_longitude` | `Int32` | 1 | 3 | `AP_Common/AP_Common.lean` |

## `AC_AttitudeControl_Multi.h` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_AttitudeControl_Multi.get_rate_yaw_pid` | `UInt64` | 6 | 2 | `AC_PID/AC_PID.lean` |
| `AC_AttitudeControl_Multi.get_rate_roll_pid` | `UInt64` | 5 | 2 | `AC_PID/AC_PID.lean` |
| `AC_AttitudeControl_Multi.get_rate_pitch_pid` | `UInt64` | 5 | 2 | `AC_PID/AC_PID.lean` |
| `AC_AttitudeControl_Multi.get_rate_yaw_pid'2` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |

## `MissionItemProtocol_Waypoints.h` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `MissionItemProtocol_Waypoints.mission_type` | `UInt32` | 6 | 2 | `GCS_MAVLink/GCS.lean` |
| `MissionItemProtocol_Waypoints.next_item_ap_message_id` | `UInt8` | 3 | 2 | `GCS_MAVLink/GCS.lean` |

## `SRV_Channel_config.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `SRV_Channels.get_motor_function` | `Int32` | 5 | 3 | `SRV_Channel/SRV_Channel.lean` |

## `SRV_Channel.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `SRV_Channel.valid_function'2` | `Bool` | 5 | 2 | `SRV_Channel/SRV_Channel.lean` |

## `GCS_MAVLink.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK.mav_param_type` | `UInt32` | 4 | 3 | `GCS_MAVLink/GCS.lean` |

## `control.cpp` (6)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `inv_sqrt_controller` | `Binary32` | 4 | 8 | `AP_Math/Control.lean` |
| `angle_rad_to_accel_mss` | `Binary32` | 3 | 2 | `AP_Math/Control.lean` |
| `stopping_distance` | `Binary32` | 2 | 2 | `AP_Math/Control.lean` |
| `sqrt_controller_accel` | `Binary32` | 2 | 10 | `AP_Math/Control.lean` |
| `input_expo` | `Binary32` | 1 | 5 | `AP_Math/Control.lean` |
| `accel_mss_to_angle_rad` | `Binary32` | 1 | 3 | `AP_Math/Control.lean` |

## `AC_P_1D.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_P_1D.kP` | `UInt64` | 4 | 2 | `AC_PID/Accessors.lean` |

## `RC_Channels.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `RC_Channels.get_rcmap_channel_nonnull` | `UInt64` | 4 | 4 | `RC_Channel/RC_Channel.lean` |
| `RC_Channels.get_rcmap_channel_nonnull'2` | `UInt64` | 1 | 3 | `RC_Channel/RC_Channel.lean` |

## `AC_P_2D.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_P_2D.kP` | `UInt64` | 3 | 2 | `AC_PID/Accessors.lean` |

## `stdint.h (as the code's docstring gives it)` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Bitmask'102.validate` | `Bool` | 3 | 2 | `AP_Common/AP_Common.lean` |
| `Bitmask'190.validate` | `Bool` | 2 | 2 | `AP_Common/AP_Common.lean` |
| `Bitmask'317.validate` | `Bool` | 2 | 2 | `AP_Common/AP_Common.lean` |
| `Bitmask'317.size` | `UInt16` | 1 | 2 | `AP_Common/AP_Common.lean` |

## `AP_Arming.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_Arming.method_is_GCS` | `Bool` | 3 | 2 | `ArduCopter/Copter.lean` |

## `AC_Circle.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_Circle.get_center_NED_m` | `UInt64` | 3 | 3 | `AC_WPNav/Accessors.lean` |

## `mavlink_msg_mission_item_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_item_int_t.__mavlink_mission_item_int_t` | `Unit` | 3 | 0 |  |

## `GCS_Common.cpp` (7)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK.command_long_stores_location` | `Bool` | 3 | 2 | `GCS_MAVLink/GCS.lean` |
| `GCS_MAVLINK.send_distance_sensor` | `Unit` | 1 | 0 |  |
| `GCS_MAVLINK.capabilities` | `UInt64` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `convert_COMMAND_LONG_loc_param` | `Int32` | 1 | 4 | `GCS_MAVLink/GCS.lean` |
| `camera_command_result_param2'mavlink_command_long_t` | `UInt8` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `camera_command_result_param2'mavlink_command_int_t` | `UInt8` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `GCS_MAVLINK.should_send_message_in_delay_callback` | `Bool` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `AP_PIDInfo.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_PIDInfo.AP_PIDInfo` | `Unit` | 3 | 0 |  |

## `sensors.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Copter.get_rangefinder_height_interpolated_m` | `Bool` | 3 | 2 | `ArduCopter/Copter.lean` |

## `GCS.h` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK.channel_status` | `UInt64` | 2 | 3 | `GCS_MAVLink/GCS.lean` |
| `GCS_MAVLINK.channel_buffer` | `UInt64` | 1 | 3 | `GCS_MAVLink/GCS.lean` |
| `GCS_Copter.min_loop_time_remaining_for_message_send_us` | `UInt16` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `GCS_MAVLink.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `valid_channel` | `Bool` | 2 | 3 | `GCS_MAVLink/GCS.lean` |

## `mavlink_types.h` (12)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_message.__mavlink_message` | `Unit` | 2 | 0 |  |
| `__mavlink_status.__mavlink_status` | `Unit` | 2 | 0 |  |
| `__mavlink_statustext_t.__mavlink_statustext_t` | `Unit` | 1 | 0 |  |
| `__mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t` | `Unit` | 1 | 0 |  |
| `__mavlink_gps2_raw_t.__mavlink_gps2_raw_t` | `Unit` | 1 | 0 |  |
| `__mavlink_home_position_t.__mavlink_home_position_t` | `Unit` | 1 | 0 |  |
| `__mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t` | `Unit` | 1 | 0 |  |
| `__mavlink_battery_status_t.__mavlink_battery_status_t` | `Unit` | 1 | 0 |  |
| `__mavlink_raw_imu_t.__mavlink_raw_imu_t` | `Unit` | 1 | 0 |  |
| `__mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t` | `Unit` | 1 | 0 |  |
| `__mavlink_sys_status_t.__mavlink_sys_status_t` | `Unit` | 1 | 0 |  |
| `__mavlink_pid_tuning_t.__mavlink_pid_tuning_t` | `Unit` | 1 | 0 |  |

## `functor.h (as the code's docstring gives it)` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK.pending_param_request.pending_param_request` | `Unit` | 2 | 0 |  |
| `GCS_MAVLINK.pending_param_reply.pending_param_reply` | `Unit` | 2 | 0 |  |
| `GCS_MAVLINK.handle_change_alt_request` | `Unit` | 1 | 0 |  |
| `GCS_MAVLINK.persist_streamrates` | `Bool` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `mavlink_msg_timesync.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_timesync_t.__mavlink_timesync_t` | `Unit` | 2 | 0 |  |

## `SRV_Channel.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `SRV_Channel.should_e_stop` | `Bool` | 2 | 2 | `SRV_Channel/SRV_Channel.lean` |
| `SRV_Channel.is_motor` | `Bool` | 1 | 3 | `SRV_Channel/SRV_Channel.lean` |

## `location.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `check_lat'2` | `Bool` | 2 | 4 | `AP_Math/AP_Math.lean` |
| `check_lng'2` | `Bool` | 2 | 4 | `AP_Math/AP_Math.lean` |

## `mavlink_msg_mission_request.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_request_t.__mavlink_mission_request_t` | `Unit` | 2 | 0 |  |

## `mavlink_msg_mission_count.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_count_t.__mavlink_mission_count_t` | `Unit` | 2 | 0 |  |

## `mavlink_msg_command_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_command_int_t.__mavlink_command_int_t` | `Unit` | 2 | 0 |  |

## `mavlink_msg_system_time.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_system_time_t.__mavlink_system_time_t` | `Unit` | 2 | 0 |  |

## `mavlink_msg_set_attitude_target.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t` | `Unit` | 1 | 0 |  |

## `definitions.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `safe_asin'float` | `Binary32` | 1 | 7 | `AP_Math/AP_Math.lean` |

## `mode.h` (70)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `ModeGuided.in_guided_mode` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAuto.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.is_autopilot` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeBrake.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeCircle.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeGuided.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeLand.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeLoiter.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeRTL.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeStabilize.mode_number` | `UInt8` | 1 | 3 | `ArduCopter/Mode.lean` |
| `ModeAltHold.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.name4` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.name` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.allows_arming` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAuto.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.has_manual_throttle` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeBrake.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeCircle.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.requires_position` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.allows_save_trim` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.allows_save_trim` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeStabilize.allows_entry_in_rc_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAltHold.has_user_takeoff` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.has_user_takeoff` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLoiter.has_user_takeoff` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeLand.is_landing` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeAuto.requires_terrain_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.requires_terrain_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeRTL.requires_terrain_failsafe` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |

## `mavlink_msg_set_position_target_local_ned.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_set_position_target_global_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t` | `Unit` | 1 | 0 |  |

## `sitl.h` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS.statustext_queue` | `UInt64` | 1 | 3 | `GCS_MAVLink/GCS.lean` |
| `AP_Mission.Mission_Flags.Mission_Flags` | `Unit` | 1 | 0 |  |

## `mavlink_msg_param_request_list.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_param_request_list_t.__mavlink_param_request_list_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_param_set.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_param_set_t.__mavlink_param_set_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_param_error.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_param_error_t.__mavlink_param_error_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_param_value.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_param_value_t.__mavlink_param_value_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_param_request_read.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_param_request_read_t.__mavlink_param_request_read_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_set_mode.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_set_mode_t.__mavlink_set_mode_t` | `Unit` | 1 | 0 |  |

## `__config (as the code's docstring gives it)` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `atan2'int_int_0` | `Binary64` | 1 | 2 | `AP_Math/AP_Math.lean` |

## `AP_MotorsMulticopter.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_MotorsMulticopter.update_external_limits` | `Unit` | 1 | 0 |  |

## `AP_Nav_Common.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `nav_filter_status.nav_filter_status` | `Unit` | 1 | 0 |  |

## `AC_AttitudeControl.h` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_AttitudeControl.get_angle_pitch_p` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_AttitudeControl.get_angle_roll_p` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_AttitudeControl.get_angle_yaw_p` | `UInt64` | 1 | 3 | `AC_AttitudeControl/Accessors.lean` |
| `AC_AttitudeControl.HeadingCommand.HeadingCommand` | `Unit` | 1 | 0 |  |

## `AP_Arming_Copter.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_Arming_Copter.oa_checks` | `Bool` | 1 | 2 | `ArduCopter/Copter.lean` |
| `AP_Arming_Copter.winch_checks` | `Bool` | 1 | 2 | `ArduCopter/Copter.lean` |

## `RC_Channel.cpp` (4)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `RC_Channel.do_aux_function_avoid_proximity` | `Unit` | 1 | 0 |  |
| `RC_Channel.do_aux_function_fft_notch_tune` | `Unit` | 1 | 0 |  |
| `RC_Channel.init_position_on_first_radio_read` | `Bool` | 1 | 2 | `RC_Channel/RC_Channel.lean` |
| `RC_Channel.string_for_aux_pos` | `UInt64` | 1 | 2 | `RC_Channel/RC_Channel.lean` |

## `AP_Mission_Commands.cpp` (6)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_Mission.start_command_parachute` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.start_command_do_scripting` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.start_command_do_sprayer` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.start_command_do_gimbal_manager_pitchyaw` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.start_command_do_set_roi` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |
| `AP_Mission.start_command_do_set_roi_wpnext_offset` | `Bool` | 1 | 2 | `AP_Mission/AP_Mission.lean` |

## `AC_WPNav.h` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_WPNav.get_wp_destination_NED_m` | `UInt64` | 1 | 3 | `AC_WPNav/Accessors.lean` |
| `AC_WPNav.wpnav_flags.wpnav_flags` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_write_partial_list.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_ack.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_ack_t.__mavlink_mission_ack_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_item.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_item_t.__mavlink_mission_item_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_request_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_request_int_t.__mavlink_mission_request_int_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_current.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_current_t.__mavlink_mission_current_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_set_current.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_set_current_t.__mavlink_mission_set_current_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_request_list.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_request_list_t.__mavlink_mission_request_list_t` | `Unit` | 1 | 0 |  |

## `MissionItemProtocol.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `MissionItemProtocol.allocate_receive_resources` | `UInt32` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `mavlink_msg_mission_clear_all.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_command_long.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_command_long_t.__mavlink_command_long_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_wind.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_wind_t.__mavlink_wind_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_attitude.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_attitude_t.__mavlink_attitude_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_attitude_quaternion.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_heartbeat.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_heartbeat_t.__mavlink_heartbeat_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_global_position_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_global_position_int_t.__mavlink_global_position_int_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_mission_item_reached.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t` | `Unit` | 1 | 0 |  |

## `AP_BattMonitor_Backend.h` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_BattMonitor_Backend.has_temperature` | `Bool` | 1 | 2 | `AP_BattMonitor/AP_BattMonitor.lean` |
| `AP_BattMonitor_Backend.has_cell_voltages` | `Bool` | 1 | 2 | `AP_BattMonitor/AP_BattMonitor.lean` |

## `AP_BattMonitor.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_BattMonitor.get_cell_voltages` | `UInt64` | 1 | 2 | `AP_BattMonitor/AP_BattMonitor.lean` |

## `mavlink_msg_meminfo.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_meminfo_t.__mavlink_meminfo_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_local_position_ned.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_local_position_ned_t.__mavlink_local_position_ned_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_attitude_target.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_attitude_target_t.__mavlink_attitude_target_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_position_target_global_int.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t` | `Unit` | 1 | 0 |  |

## `mode_guided.cpp` (3)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `ModeGuided.get_target_pos_NED_m` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.get_target_vel_NED_ms` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |
| `ModeGuided.get_target_accel_NED_mss` | `UInt64` | 1 | 2 | `ArduCopter/Mode.lean` |

## `mavlink_msg_position_target_local_ned.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_power_status.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_power_status_t.__mavlink_power_status_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_rc_channels.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_rc_channels_t.__mavlink_rc_channels_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_rc_channels_raw.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_scaled_pressure.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_scaled_pressure2.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_scaled_pressure3.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_ahrs2.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_ahrs2_t.__mavlink_ahrs2_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_nav_controller_output.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_ahrs.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_ahrs_t.__mavlink_ahrs_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_extended_sys_state.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t` | `Unit` | 1 | 0 |  |

## `GCS_MAVLink_Copter.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK_Copter.vtol_state` | `UInt32` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `mavlink_msg_vfr_hud.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_vfr_hud_t.__mavlink_vfr_hud_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_vibration.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_vibration_t.__mavlink_vibration_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_autopilot_version.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_autopilot_version_t.__mavlink_autopilot_version_t` | `Unit` | 1 | 0 |  |

## `GCS_MAVLink_Copter.cpp` (2)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `GCS_MAVLINK_Copter.capabilities` | `UInt64` | 1 | 2 | `GCS_MAVLink/GCS.lean` |
| `GCS_MAVLINK_Copter.command_int_only` | `Bool` | 1 | 2 | `GCS_MAVLink/GCS.lean` |

## `mavlink_msg_available_modes.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_available_modes_t.__mavlink_available_modes_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_available_modes_monitor.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_flight_information.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_flight_information_t.__mavlink_flight_information_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_command_ack.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_command_ack_t.__mavlink_command_ack_t` | `Unit` | 1 | 0 |  |

## `mavlink_msg_request_data_stream.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `__mavlink_request_data_stream_t.__mavlink_request_data_stream_t` | `Unit` | 1 | 0 |  |

## `AP_SerialManager.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_SerialManager.map_baudrate` | `UInt32` | 1 | 3 | `AP_SerialManager/AP_SerialManager.lean` |

## `board_drivers.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_BoardConfig.board_setup_sbus` | `Unit` | 1 | 0 |  |

## `AP_BattMonitor_Analog.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_BattMonitor_Analog.init` | `Unit` | 1 | 0 |  |

## `FilterClass.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Filter'float.Filter` | `Unit` | 1 | 0 |  |

## `AP_Common.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `is_bounded_int32` | `Bool` | 1 | 2 | `AP_Common/AP_Common.lean` |

## `mode_auto.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `ModeAuto.verify_loiter_unlimited` | `Bool` | 1 | 2 | `ArduCopter/Mode.lean` |

## `avoidance.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Copter.low_alt_avoidance` | `Unit` | 1 | 0 |  |

## `AC_AttitudeControl_Multi.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_AttitudeControl_Multi.set_notch_sample_rate` | `Unit` | 1 | 0 |  |

## `AC_PID.cpp` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AC_PID.set_notch_sample_rate` | `Unit` | 1 | 0 |  |

## `HAL.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_HAL.HAL.Callbacks.Callbacks` | `Unit` | 1 | 0 |  |

## `PerfInfo.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP.PerfInfo.PerfInfo` | `Unit` | 1 | 0 |  |

## `Parameters.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `Parameters.Parameters` | `Unit` | 1 | 0 |  |

## `AP_SurfaceDistance.h` (1)

| function | returns | fan-in | theorems | corpus file |
|---|---|---|---|---|
| `AP_SurfaceDistance.SurfDistParameters.SurfDistParameters` | `Unit` | 1 | 0 |  |

## `Estimator_lib`: scalar pure functions

`Estimator_lib` is pure-functional throughout (`State → State`); its functions of scalars alone (no `World`, state
or array argument) are listed here. The vehicle path does not share these constants (the vehicle's own copies are
`Vehicle_lib`'s). None is covered yet (OPEN.md).

| function (namespace as emitted) | line |
|---|---|
| `AP_Baro.geopotential_alt_to_geometric` | 4090 |
| `AP_Baro.find_atmosphere_layer_by_pressure` | 4116 |
| `AP_Baro.is_positive_float` | 4124 |
| `AP_Baro.is_zero_float` | 4128 |
| `AP_Baro.constrain_value_line_float` | 4161 |
| `AP_Baro.MIN_float2` | 4204 |
| `AP_AHRS.backend_for_type` | 6286 |
| `AP_AHRS.estimates_for_type` | 6296 |
| `AP_AHRS.fallback_active_EKF_type` | 6319 |
| `Vector3f.sq_float` | 7355 |
| `Vector3f.norm_float3` | 7359 |
| `Vector3f.is_negative_float` | 7514 |
| `Vector3f.calc_lowpass_alpha_dt` | 7518 |
| `AP_InertialSensor_SITL.get_temperature` | 7761 |
| `AP_InertialSensor_SITL.timeout_expired` | 7795 |
| `AP_InertialSensor.degrees` | 8463 |
| `AP_InertialSensor.norm_float2` | 8467 |
| `Compass.radians_float` | 8707 |
| `AP_GPS_SITL.get_lag` | 9036 |
| `AP_DAL_InertialSensor.MIN_int32_t_uint8_t` | 9222 |
| `AP_InertialSensor_SITL.gyro_bias_limit_rads` | 9350 |
| `AP_InertialSensor_SITL.gyro_bias_init_dps` | 9369 |
| `AP_DAL_GPS.MIN_uint16_t_int32_t` | 9637 |
| `AP_DAL_GPS.MIN_uint8_t2` | 9641 |
| `AP_DAL_GPS.MAX_double_float` | 9645 |
| `AP_DAL_GPS.MAX_uint16_t2` | 9649 |
| `AP_DAL_GPS.MAX_uint16_t_int32_t` | 9661 |
| `Vector3p.sq_double` | 10323 |
| `Vector3p.sq_double2` | 10328 |
| `Vector3p.sq_double3` | 10332 |
| `Vector3p.norm_double3` | 10336 |
| `AP_DAL_InertialSensor.constrain_value_line_double` | 10651 |
| `AP_DAL_InertialSensor.MAX_double2` | 10662 |
| `Matrix3_double.is_zero_double` | 10674 |
| `QuaternionT_double.wrap_2PI_double` | 10781 |
| `QuaternionT_double.wrap_PI_double` | 10788 |
| `EKF_IMU_buffer_t_NavEKF3_core_imu_elements.radians_int32_t` | 10875 |
| `NavEKF3_core.MIN_float_double` | 11066 |
| `NavEKF3_core.MAX_float_double` | 11070 |
| `AP_DAL_Compass.is_equal_double2` | 11214 |
| `QuaternionT_double.norm_double2` | 11338 |
| `AP_Declination.constrain_value_int32_t` | 11662 |
| `AP_Declination.constrain_int32` | 11674 |
| `AP_Declination.get_mag_field_ef` | 11680 |
| `AP_Declination.get_declination` | 11740 |
| `AP_DAL_GPS.MIN_uint32_t2` | 11830 |
| `AP_DAL_GPS.MIN_double_float` | 11834 |
| `AP_DAL_GPS.MAX_uint32_t2` | 11838 |
| `Location.longitude_scale` | 11909 |
| `Location.diff_longitude` | 11914 |
| `NavEKF3_core.MAX_uint8_t2` | 12362 |
| `Location.wrap_longitude` | 12736 |
| `Location.limit_lattitude` | 12745 |
| `Location.offset_latlng` | 12757 |
| `NavEKF3_core.radians_double` | 13018 |
| `Matrix3f.is_equal_float2` | 14162 |
| `AP_AHRS.wrap_360_float` | 14618 |
| `AP_AHRS.safe_sqrt_float` | 14642 |
| `AP_AHRS.safe_asin_float` | 14649 |
| `AP_GPS.wrap_180_float` | 15259 |
| `AP_AHRS_DCM._P_gain` | 15285 |
| `Compass.wrap_2PI_float` | 15491 |
| `Compass.wrap_PI_float` | 15498 |
| `AP_InertialSensor.get_gyro_drift_rate` | 15648 |
| `AP_InertialSensor.MAX_float_int32_t` | 15654 |
| `AP_AHRS_DCM.shortname` | 16366 |
| `QuaternionT_double.safe_asin_double` | 16815 |
| `NavEKF3_core.MIN_uint16_t2` | 16970 |
| `NavEKF3_core.readyToUseRangeBeacon` | 17019 |
| `NavEKF3_core.readyToUseExtNav` | 17023 |
| `NavEKF3_core.is_positive_double` | 17307 |
| `AP_DAL_Airspeed.MAX_float2` | 20701 |
| `NavEKF3_core.using_extnav_for_yaw` | 22255 |
| `AP_AHRS_NavEKF3.shortname` | 22375 |
| `AP_AHRS_NavEKF3.AP_AHRS_SIM_shortname` | 22381 |
| `AP_AHRS.check_lat_int32_t` | 22645 |
| `AP_AHRS.check_lng_int32_t` | 22649 |
| `AP_AHRS.set_failure_inconsistent_message` | 23849 |
| `AP_AHRS_DCM.pre_arm_check` | 24005 |
| `AP_HAL.Device.make_bus_id` | 24598 |
| `AP_Baro.geometric_alt_to_geopotential` | 24775 |
| `AP_Baro.get_temperature_by_altitude_layer` | 24779 |
| `AP_Baro.find_atmosphere_layer_by_altitude` | 24787 |
| `AP_Baro.get_air_density_for_alt_amsl` | 24797 |
| `AP_Baro.get_EAS2TAS_extended` | 24816 |
| `AP_Baro_SITL.healthy` | 24867 |
| `AP_GPS.needs_uart` | 26198 |
| `EstUART._available` | 26328 |
| `EstUART.read_void` | 26338 |
| `AP_GPS_SITL.name` | 26409 |
| `AP_GPS.istate_time_to_epoch_ms` | 26474 |
| `AP_GPS_SITL.MIN_int32_t2` | 26609 |
| `AP_GPS_SITL.is_configured` | 26893 |
| `AP_GPS_SITL.is_healthy` | 26932 |
| `AP_GPS_SITL.prepare_for_arming` | 26965 |
| `AP_GPS.wrap_360_cd_float` | 27016 |
| `AP_HAL.Device.devid_get_devtype` | 27173 |
| `AP_InertialSensor.MIN_uint8_t_int32_t` | 27578 |
| `AP_InertialSensor.temperature_cal_running` | 28006 |
| `AP_InertialSensor_SITL.get_output_banner` | 28059 |
| `AP_RTC.clock_ms_to_hms_fields` | 29040 |
