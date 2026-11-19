import ArduLean.Runtime.Memory

/-!
`Layout`: generated items without a C++ function of their own.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- The end of the constant data and statics; the heap and the stack follow. -/
def heapBase : Nat := 0x20000
def stackBase : Nat := 0x30000
def memSize : Nat := 0x40000

/-! The address of each static object and table (the address map; also `Vehicle_lib.addresses.json`). -/

/-- `Copter::var_info` (table, 1824 bytes) -/
def addr'Copter__var_info : UInt64 := 0x1000
/-- `AC_AttitudeControl_Multi::var_info` (table, 288 bytes) -/
def addr'AC_AttitudeControl_Multi__var_info : UInt64 := 0x19d0
/-- `AP_MotorsMulticopter::var_info` (table, 832 bytes) -/
def addr'AP_MotorsMulticopter__var_info : UInt64 := 0x1b68
/-- `AP_BattMonitor_Analog::var_info` (table, 224 bytes) -/
def addr'AP_BattMonitor_Analog__var_info : UInt64 := 0x2020
/-- `AP_Arming::var_info` (table, 288 bytes) -/
def addr'AP_Arming__var_info : UInt64 := 0x2168
/-- `Compass::var_info` (table, 1440 bytes) -/
def addr'Compass__var_info : UInt64 := 0x22f0
/-- `AP_InertialSensor::var_info` (table, 1024 bytes) -/
def addr'AP_InertialSensor__var_info : UInt64 := 0x2a30
/-- `AC_WPNav::var_info` (table, 352 bytes) -/
def addr'AC_WPNav__var_info : UInt64 := 0x2fe8
/-- `AC_Loiter::var_info` (table, 256 bytes) -/
def addr'AC_Loiter__var_info : UInt64 := 0x31b8
/-- `AC_Circle::var_info` (table, 128 bytes) -/
def addr'AC_Circle__var_info : UInt64 := 0x3320
/-- `AC_PosControl::var_info` (table, 288 bytes) -/
def addr'AC_PosControl__var_info : UInt64 := 0x33c8
/-- `AP_AHRS::var_info` (table, 480 bytes) -/
def addr'AP_AHRS__var_info : UInt64 := 0x3550
/-- `AP_BattMonitor::var_info` (table, 608 bytes) -/
def addr'AP_BattMonitor__var_info : UInt64 := 0x37f0
/-- `AP_BoardConfig::var_info` (table, 640 bytes) -/
def addr'AP_BoardConfig__var_info : UInt64 := 0x3aa0
/-- `AP_CANManager::var_info` (table, 192 bytes) -/
def addr'AP_CANManager__var_info : UInt64 := 0x3e48
/-- `SITL::SIM::var_info` (table, 32 bytes) -/
def addr'SITL__SIM__var_info : UInt64 := 0x3f40
/-- `AP_Baro::var_info` (table, 512 bytes) -/
def addr'AP_Baro__var_info : UInt64 := 0x3f68
/-- `AP_GPS::var_info` (table, 416 bytes) -/
def addr'AP_GPS__var_info : UInt64 := 0x4248
/-- `AP_Scheduler::var_info` (table, 128 bytes) -/
def addr'AP_Scheduler__var_info : UInt64 := 0x44a0
/-- `RCMapper::var_info` (table, 224 bytes) -/
def addr'RCMapper__var_info : UInt64 := 0x4548
/-- `NavEKF3::var_info` (table, 1920 bytes) -/
def addr'NavEKF3__var_info : UInt64 := 0x4668
/-- `AP_Mission::var_info` (table, 128 bytes) -/
def addr'AP_Mission__var_info : UInt64 := 0x5180
/-- `AP_Notify::var_info` (table, 288 bytes) -/
def addr'AP_Notify__var_info : UInt64 := 0x5220
/-- `ParametersG2::var_info` (table, 608 bytes) -/
def addr'ParametersG2__var_info : UInt64 := 0x53c0
/-- `AP_Vehicle::var_info` (table, 96 bytes) -/
def addr'AP_Vehicle__var_info : UInt64 := 0x5720
/-- `GCS::var_info` (table, 704 bytes) -/
def addr'GCS__var_info : UInt64 := 0x57a8
/-- `AC_AttitudeControl::var_info` (table, 608 bytes) -/
def addr'AC_AttitudeControl__var_info : UInt64 := 0x5b38
/-- `AC_PID::var_info` (table, 384 bytes) -/
def addr'AC_PID__var_info : UInt64 := 0x5ec0
/-- `Compass_PerMotor::var_info` (table, 224 bytes) -/
def addr'Compass_PerMotor__var_info : UInt64 := 0x60a0
/-- `AC_P_1D::var_info` (table, 64 bytes) -/
def addr'AC_P_1D__var_info : UInt64 := 0x61b8
/-- `AC_P_2D::var_info` (table, 64 bytes) -/
def addr'AC_P_2D__var_info : UInt64 := 0x6208
/-- `AC_PID_Basic::var_info` (table, 256 bytes) -/
def addr'AC_PID_Basic__var_info : UInt64 := 0x6258
/-- `AC_PID_2D::var_info` (table, 256 bytes) -/
def addr'AC_PID_2D__var_info : UInt64 := 0x6398
/-- `AP_BattMonitor_Params::var_info` (table, 512 bytes) -/
def addr'AP_BattMonitor_Params__var_info : UInt64 := 0x64d8
/-- `AP_RTC::var_info` (table, 96 bytes) -/
def addr'AP_RTC__var_info : UInt64 := 0x67a8
/-- `AP_CANManager::CANIface_Params::var_info` (table, 160 bytes) -/
def addr'AP_CANManager__CANIface_Params__var_info : UInt64 := 0x6820
/-- `AP_CANManager::CANDriver_Params::var_info` (table, 96 bytes) -/
def addr'AP_CANManager__CANDriver_Params__var_info : UInt64 := 0x68f0
/-- `AP_GPS::Params::var_info` (table, 192 bytes) -/
def addr'AP_GPS__Params__var_info : UInt64 := 0x6978
/-- `NavEKF3::var_info2` (table, 384 bytes) -/
def addr'NavEKF3__var_info2 : UInt64 := 0x6a78
/-- `SRV_Channels::var_info` (table, 1280 bytes) -/
def addr'SRV_Channels__var_info : UInt64 := 0x6c90
/-- `RC_Channels::var_info` (table, 672 bytes) -/
def addr'RC_Channels__var_info : UInt64 := 0x7300
/-- `AC_CommandModel::var_info` (table, 128 bytes) -/
def addr'AC_CommandModel__var_info : UInt64 := 0x7668
/-- `ParametersG2::var_info2` (table, 320 bytes) -/
def addr'ParametersG2__var_info2 : UInt64 := 0x7708
/-- `AP_SerialManager::var_info` (table, 864 bytes) -/
def addr'AP_SerialManager__var_info : UInt64 := 0x78c8
/-- `AC_P::var_info` (table, 64 bytes) -/
def addr'AC_P__var_info : UInt64 := 0x7d80
/-- `AP_NavEKF_Source::var_info` (table, 544 bytes) -/
def addr'AP_NavEKF_Source__var_info : UInt64 := 0x7dd0
/-- `SRV_Channel::var_info` (table, 192 bytes) -/
def addr'SRV_Channel__var_info : UInt64 := 0x8080
/-- `RC_Channel::var_info` (table, 224 bytes) -/
def addr'RC_Channel__var_info : UInt64 := 0x8180
/-- `ModeRTL::var_info` (table, 160 bytes) -/
def addr'ModeRTL__var_info : UInt64 := 0x82a0
/-- `ModeLand::var_info` (table, 128 bytes) -/
def addr'ModeLand__var_info : UInt64 := 0x8380
/-- `AP_AHRS_NavEKF3::EKF3` (object, 480 bytes) -/
def addr'AP_AHRS_NavEKF3__EKF3 : UInt64 := 0x8430
/-- `AP_BattMonitor::backend_var_info` (object, 72 bytes) -/
def addr'AP_BattMonitor__backend_var_info : UInt64 := 0x8610
/-- `GCS::_chan_var_info` (object, 128 bytes) -/
def addr'GCS___chan_var_info : UInt64 := 0x8658
/-- `copter` (object, 13216 bytes) -/
def addr'copter : UInt64 := 0x86d8
/-- `AP_Param::_num_vars` (static, 2 bytes) -/
def addr'AP_Param___num_vars : UInt64 := 0xba78
/-- `AP_Param::registered_save_handler` (static, 1 bytes) -/
def addr'AP_Param__registered_save_handler : UInt64 := 0xba80
/-- `hal` (static, 224 bytes) -/
def addr'hal : UInt64 := 0xba88
/-- `save_dummy` (static, 1 bytes) -/
def addr'save_dummy : UInt64 := 0xbb68
/-- `AP_Param::_storage` (static, 16 bytes) -/
def addr'AP_Param___storage : UInt64 := 0xbb70
/-- `AP_Param::sentinel_offset` (static, 2 bytes) -/
def addr'AP_Param__sentinel_offset : UInt64 := 0xbb80
/-- `AP_Param::_parameter_count` (static, 2 bytes) -/
def addr'AP_Param___parameter_count : UInt64 := 0xbb88
/-- `AP_Param::_count_marker` (static, 2 bytes) -/
def addr'AP_Param___count_marker : UInt64 := 0xbb90
/-- `AP_Param::_count_marker_done` (static, 2 bytes) -/
def addr'AP_Param___count_marker_done : UInt64 := 0xbb98
/-- `AP_Param::eeprom_full` (static, 1 bytes) -/
def addr'AP_Param__eeprom_full : UInt64 := 0xbba0
/-- `AP_Param::done_all_default_params` (static, 1 bytes) -/
def addr'AP_Param__done_all_default_params : UInt64 := 0xbba8
/-- `AP_Param::_frame_type_flags` (static, 2 bytes) -/
def addr'AP_Param___frame_type_flags : UInt64 := 0xbbb0
/-- `AP_Param::_var_info` (static, 8 bytes) -/
def addr'AP_Param___var_info : UInt64 := 0xbbb8
/-- `AP_Param::_singleton` (static, 8 bytes) -/
def addr'AP_Param___singleton : UInt64 := 0xbbc0
/-- `StorageManager::layout` (static, 120 bytes) -/
def addr'StorageManager__layout : UInt64 := 0xbbc8
/-- `SRV_Channels::_singleton` (static, 8 bytes) -/
def addr'SRV_Channels___singleton : UInt64 := 0xbc40
/-- `SRV_Channels::channels` (static, 8 bytes) -/
def addr'SRV_Channels__channels : UInt64 := 0xbc48
/-- `mavlink_system` (static, 5 bytes) -/
def addr'mavlink_system : UInt64 := 0xbc50
/-- `GCS::missionitemprotocols` (static, 24 bytes) -/
def addr'GCS__missionitemprotocols : UInt64 := 0xbc58
/-- `GCS_MAVLINK::var_info` (static, 448 bytes) -/
def addr'GCS_MAVLINK__var_info : UInt64 := 0xbc70
/-- `.str.3` (static, 10 bytes) -/
def addr'_str_3 : UInt64 := 0xbe30
/-- `.str.4` (static, 10 bytes) -/
def addr'_str_4 : UInt64 := 0xbe40
/-- `.str.5` (static, 9 bytes) -/
def addr'_str_5 : UInt64 := 0xbe50
/-- `.str.6` (static, 10 bytes) -/
def addr'_str_6 : UInt64 := 0xbe60
/-- `.str.7` (static, 10 bytes) -/
def addr'_str_7 : UInt64 := 0xbe70
/-- `.str.8` (static, 8 bytes) -/
def addr'_str_8 : UInt64 := 0xbe80
/-- `.str.9` (static, 8 bytes) -/
def addr'_str_9 : UInt64 := 0xbe88
/-- `.str.10` (static, 8 bytes) -/
def addr'_str_10 : UInt64 := 0xbe90
/-- `.str.11` (static, 8 bytes) -/
def addr'_str_11 : UInt64 := 0xbe98
/-- `.str.12` (static, 6 bytes) -/
def addr'_str_12 : UInt64 := 0xbea0
/-- `.str.13` (static, 9 bytes) -/
def addr'_str_13 : UInt64 := 0xbea8
/-- `.str.14` (static, 12 bytes) -/
def addr'_str_14 : UInt64 := 0xbeb8
/-- `.str.15` (static, 7 bytes) -/
def addr'_str_15 : UInt64 := 0xbec8
/-- `.str.16` (static, 1 bytes) -/
def addr'_str_16 : UInt64 := 0xbed0
/-- `GCS_MAVLINK::param_replies` (static, 16 bytes) -/
def addr'GCS_MAVLINK__param_replies : UInt64 := 0xbed8
/-- `GCS_MAVLINK::param_requests` (static, 16 bytes) -/
def addr'GCS_MAVLINK__param_requests : UInt64 := 0xbee8
/-- `NaNf` (static, 4 bytes) -/
def addr'NaNf : UInt64 := 0xbef8
/-- `AP_Vehicle::scheduler_delay_callback(...)::last_1hz` (static, 4 bytes) -/
def addr'AP_Vehicle__scheduler_delay_callback_______last_1hz : UInt64 := 0xbf00
/-- `AP_Vehicle::scheduler_delay_callback(...)::last_50hz` (static, 4 bytes) -/
def addr'AP_Vehicle__scheduler_delay_callback_______last_50hz : UInt64 := 0xbf08
/-- `AP_Vehicle::scheduler_delay_callback(...)::last_5s` (static, 4 bytes) -/
def addr'AP_Vehicle__scheduler_delay_callback_______last_5s : UInt64 := 0xbf10
/-- `AC_PosControl::_singleton` (static, 8 bytes) -/
def addr'AC_PosControl___singleton : UInt64 := 0xbf18
/-- `AP_Mission::_singleton` (static, 8 bytes) -/
def addr'AP_Mission___singleton : UInt64 := 0xbf20
/-- `AP_Mission::_storage` (static, 16 bytes) -/
def addr'AP_Mission___storage : UInt64 := 0xbf28
/-- `AP_Param::save_queue` (static, 16 bytes) -/
def addr'AP_Param__save_queue : UInt64 := 0xbf38
/-- `AP_Param::num_param_overrides` (static, 2 bytes) -/
def addr'AP_Param__num_param_overrides : UInt64 := 0xbf48
/-- `AP_Param::param_overrides` (static, 8 bytes) -/
def addr'AP_Param__param_overrides : UInt64 := 0xbf50
/-- `AP_Param::default_list` (static, 8 bytes) -/
def addr'AP_Param__default_list : UInt64 := 0xbf58
/-- `AP_Param::_hide_disabled_groups` (static, 1 bytes) -/
def addr'AP_Param___hide_disabled_groups : UInt64 := 0xbf60
/-- `SRV_Channel::have_pwm_mask` (static, 4 bytes) -/
def addr'SRV_Channel__have_pwm_mask : UInt64 := 0xbf68
/-- `gcs_alternative_active` (static, 16 bytes) -/
def addr'gcs_alternative_active : UInt64 := 0xbf70
/-- `AP_BoardConfig::_in_error_loop` (static, 1 bytes) -/
def addr'AP_BoardConfig___in_error_loop : UInt64 := 0xbf80
/-- `GCS_MAVLINK::chan_is_streaming` (static, 4 bytes) -/
def addr'GCS_MAVLINK__chan_is_streaming : UInt64 := 0xbf88
/-- `AC_AttitudeControl::_singleton` (static, 8 bytes) -/
def addr'AC_AttitudeControl___singleton : UInt64 := 0xbf90
/-- `AP_BoardConfig::_singleton` (static, 8 bytes) -/
def addr'AP_BoardConfig___singleton : UInt64 := 0xbf98
/-- `Copter::load_parameters(...)::g2_conversions` (static, 0 bytes) -/
def addr'Copter__load_parameters_______g2_conversions : UInt64 := 0xbfa0
/-- `Copter::load_parameters(...)::toplevel_conversions` (static, 24 bytes) -/
def addr'Copter__load_parameters_______toplevel_conversions : UInt64 := 0xbfa8
/-- `Copter::load_parameters(...)::pilot_conversion_info` (static, 96 bytes) -/
def addr'Copter__load_parameters_______pilot_conversion_info : UInt64 := 0xbfc0
/-- `Copter::scheduler_tasks` (static, 960 bytes) -/
def addr'Copter__scheduler_tasks : UInt64 := 0xc020
/-- `.str.7` (static, 27 bytes) -/
def addr'_str_7_c3e0 : UInt64 := 0xc3e0
/-- `.str.8` (static, 34 bytes) -/
def addr'_str_8_c400 : UInt64 := 0xc400
/-- `.str.9` (static, 28 bytes) -/
def addr'_str_9_c428 : UInt64 := 0xc428
/-- `.str.10` (static, 19 bytes) -/
def addr'_str_10_c448 : UInt64 := 0xc448
/-- `.str.11` (static, 22 bytes) -/
def addr'_str_11_c460 : UInt64 := 0xc460
/-- `.str.12` (static, 25 bytes) -/
def addr'_str_12_c478 : UInt64 := 0xc478
/-- `.str.13` (static, 28 bytes) -/
def addr'_str_13_c498 : UInt64 := 0xc498
/-- `.str.14` (static, 30 bytes) -/
def addr'_str_14_c4b8 : UInt64 := 0xc4b8
/-- `.str.15` (static, 41 bytes) -/
def addr'_str_15_c4d8 : UInt64 := 0xc4d8
/-- `.str.16` (static, 43 bytes) -/
def addr'_str_16_c508 : UInt64 := 0xc508
/-- `.str.17` (static, 16 bytes) -/
def addr'_str_17 : UInt64 := 0xc538
/-- `.str.18` (static, 22 bytes) -/
def addr'_str_18 : UInt64 := 0xc548
/-- `.str.19` (static, 15 bytes) -/
def addr'_str_19 : UInt64 := 0xc560
/-- `.str.20` (static, 28 bytes) -/
def addr'_str_20 : UInt64 := 0xc570
/-- `.str.21` (static, 26 bytes) -/
def addr'_str_21 : UInt64 := 0xc590
/-- `.str.22` (static, 26 bytes) -/
def addr'_str_22 : UInt64 := 0xc5b0
/-- `.str.23` (static, 24 bytes) -/
def addr'_str_23 : UInt64 := 0xc5d0
/-- `.str.24` (static, 24 bytes) -/
def addr'_str_24 : UInt64 := 0xc5e8
/-- `.str.25` (static, 30 bytes) -/
def addr'_str_25 : UInt64 := 0xc600
/-- `.str.26` (static, 22 bytes) -/
def addr'_str_26 : UInt64 := 0xc620
/-- `.str.27` (static, 20 bytes) -/
def addr'_str_27 : UInt64 := 0xc638
/-- `.str.28` (static, 18 bytes) -/
def addr'_str_28 : UInt64 := 0xc650
/-- `.str.29` (static, 24 bytes) -/
def addr'_str_29 : UInt64 := 0xc668
/-- `.str.30` (static, 24 bytes) -/
def addr'_str_30 : UInt64 := 0xc680
/-- `.str.31` (static, 22 bytes) -/
def addr'_str_31 : UInt64 := 0xc698
/-- `.str.32` (static, 23 bytes) -/
def addr'_str_32 : UInt64 := 0xc6b0
/-- `.str.33` (static, 27 bytes) -/
def addr'_str_33 : UInt64 := 0xc6c8
/-- `.str.34` (static, 20 bytes) -/
def addr'_str_34 : UInt64 := 0xc6e8
/-- `.str.35` (static, 17 bytes) -/
def addr'_str_35 : UInt64 := 0xc700
/-- `.str.36` (static, 28 bytes) -/
def addr'_str_36 : UInt64 := 0xc718
/-- `GCS::_singleton` (static, 8 bytes) -/
def addr'GCS___singleton : UInt64 := 0xc738
/-- `GCS_MAVLINK::routing` (static, 328 bytes) -/
def addr'GCS_MAVLINK__routing : UInt64 := 0xc740
/-- `GCS_MAVLINK::reserve_param_space_start_ms` (static, 4 bytes) -/
def addr'GCS_MAVLINK__reserve_param_space_start_ms : UInt64 := 0xc888
/-- `GCS_MAVLINK::all_stream_entries` (static, 264 bytes) -/
def addr'GCS_MAVLINK__all_stream_entries : UInt64 := 0xc890
/-- `STREAM_RAW_SENSORS_msgs` (static, 6 bytes) -/
def addr'STREAM_RAW_SENSORS_msgs : UInt64 := 0xc998
/-- `STREAM_EXTENDED_STATUS_msgs` (static, 8 bytes) -/
def addr'STREAM_EXTENDED_STATUS_msgs : UInt64 := 0xc9a0
/-- `STREAM_POSITION_msgs` (static, 2 bytes) -/
def addr'STREAM_POSITION_msgs : UInt64 := 0xc9a8
/-- `STREAM_RAW_CONTROLLER_msgs` (static, 0 bytes) -/
def addr'STREAM_RAW_CONTROLLER_msgs : UInt64 := 0xc9b0
/-- `STREAM_RC_CHANNELS_msgs` (static, 3 bytes) -/
def addr'STREAM_RC_CHANNELS_msgs : UInt64 := 0xc9b8
/-- `STREAM_EXTRA1_msgs` (static, 4 bytes) -/
def addr'STREAM_EXTRA1_msgs : UInt64 := 0xc9c0
/-- `STREAM_EXTRA2_msgs` (static, 1 bytes) -/
def addr'STREAM_EXTRA2_msgs : UInt64 := 0xc9c8
/-- `STREAM_EXTRA3_msgs` (static, 7 bytes) -/
def addr'STREAM_EXTRA3_msgs : UInt64 := 0xc9d0
/-- `STREAM_PARAMS_msgs` (static, 2 bytes) -/
def addr'STREAM_PARAMS_msgs : UInt64 := 0xc9d8
/-- `STREAM_ADSB_msgs` (static, 1 bytes) -/
def addr'STREAM_ADSB_msgs : UInt64 := 0xc9e0
/-- `mavlink_comm_port` (static, 128 bytes) -/
def addr'mavlink_comm_port : UInt64 := 0xc9e8
/-- `fwver` (static, 92 bytes) -/
def addr'fwver : UInt64 := 0xca68
/-- `.str.3` (static, 33 bytes) -/
def addr'_str_3_cac8 : UInt64 := 0xcac8
/-- `.str.4` (static, 9 bytes) -/
def addr'_str_4_caf0 : UInt64 := 0xcaf0
/-- `.str.5` (static, 22 bytes) -/
def addr'_str_5_cb00 : UInt64 := 0xcb00
/-- `ModeRTL::convert_params(...)::conversion_info` (static, 96 bytes) -/
def addr'ModeRTL__convert_params_______conversion_info : UInt64 := 0xcb18
/-- `.str.8` (static, 10 bytes) -/
def addr'_str_8_cb78 : UInt64 := 0xcb78
/-- `.str.9` (static, 13 bytes) -/
def addr'_str_9_cb88 : UInt64 := 0xcb88
/-- `.str.10` (static, 16 bytes) -/
def addr'_str_10_cb98 : UInt64 := 0xcb98
/-- `.str.11` (static, 16 bytes) -/
def addr'_str_11_cba8 : UInt64 := 0xcba8
/-- `ModeLand::convert_params(...)::conversion_info` (static, 72 bytes) -/
def addr'ModeLand__convert_params_______conversion_info : UInt64 := 0xcbb8
/-- `.str.7` (static, 12 bytes) -/
def addr'_str_7_cc00 : UInt64 := 0xcc00
/-- `.str.8` (static, 17 bytes) -/
def addr'_str_8_cc10 : UInt64 := 0xcc10
/-- `.str.9` (static, 15 bytes) -/
def addr'_str_9_cc28 : UInt64 := 0xcc28
/-- `AP_Vehicle::scheduler_tasks` (static, 128 bytes) -/
def addr'AP_Vehicle__scheduler_tasks : UInt64 := 0xcc38
/-- `AP_Scheduler::_singleton` (static, 8 bytes) -/
def addr'AP_Scheduler___singleton : UInt64 := 0xccb8
/-- `flags` (static, 29 bytes) -/
def addr'flags : UInt64 := 0xccc0
/-- `AP_GPS::convert_parameters(...)::conversion_info` (static, 160 bytes) -/
def addr'AP_GPS__convert_parameters_______conversion_info : UInt64 := 0xcce0
/-- `.str.17` (static, 10 bytes) -/
def addr'_str_17_cd80 : UInt64 := 0xcd80
/-- `.str.18` (static, 10 bytes) -/
def addr'_str_18_cd90 : UInt64 := 0xcd90
/-- `.str.19` (static, 15 bytes) -/
def addr'_str_19_cda0 : UInt64 := 0xcda0
/-- `.str.20` (static, 15 bytes) -/
def addr'_str_20_cdb0 : UInt64 := 0xcdb0
/-- `.str.21` (static, 13 bytes) -/
def addr'_str_21_cdc0 : UInt64 := 0xcdc0
/-- `.str.22` (static, 13 bytes) -/
def addr'_str_22_cdd0 : UInt64 := 0xcdd0
/-- `.str.23` (static, 9 bytes) -/
def addr'_str_23_cde0 : UInt64 := 0xcde0
/-- `.str.24` (static, 9 bytes) -/
def addr'_str_24_cdf0 : UInt64 := 0xcdf0
/-- `.str.25` (static, 14 bytes) -/
def addr'_str_25_ce00 : UInt64 := 0xce00
/-- `.str.26` (static, 14 bytes) -/
def addr'_str_26_ce10 : UInt64 := 0xce10
/-- `land_detector_count` (static, 4 bytes) -/
def addr'land_detector_count : UInt64 := 0xce20
/-- `failsafe_enabled` (static, 1 bytes) -/
def addr'failsafe_enabled : UInt64 := 0xce28
/-- `failsafe_last_timestamp` (static, 4 bytes) -/
def addr'failsafe_last_timestamp : UInt64 := 0xce30
/-- `AP_Notify::events` (static, 4 bytes) -/
def addr'AP_Notify__events : UInt64 := 0xce38
/-- `AP_Arming::_singleton` (static, 8 bytes) -/
def addr'AP_Arming___singleton : UInt64 := 0xce40
/-- `mavlink_get_msg_entry(...)::mavlink_message_crcs` (static, 4284 bytes) -/
def addr'mavlink_get_msg_entry_______mavlink_message_crcs : UInt64 := 0xce48
/-- `GCS_MAVLINK::mavlink_private` (static, 4 bytes) -/
def addr'GCS_MAVLINK__mavlink_private : UInt64 := 0xdf08
/-- `GCS::send_textv(...)::msgid` (static, 2 bytes) -/
def addr'GCS__send_textv_______msgid : UInt64 := 0xdf10
/-- `AP_Vehicle::_singleton` (static, 8 bytes) -/
def addr'AP_Vehicle___singleton : UInt64 := 0xdf18
/-- `AP_MotorsMatrix::_singleton` (static, 8 bytes) -/
def addr'AP_MotorsMatrix___singleton : UInt64 := 0xdf20
/-- `AC_AttitudeControl::convert_parameters(...)::conversion_info_001` (static, 120 bytes) -/
def addr'AC_AttitudeControl__convert_parameters_______conversion_info_001 : UInt64 := 0xdf28
/-- `.str.22` (static, 14 bytes) -/
def addr'_str_22_dfa0 : UInt64 := 0xdfa0
/-- `.str.23` (static, 17 bytes) -/
def addr'_str_23_dfb0 : UInt64 := 0xdfb0
/-- `.str.24` (static, 14 bytes) -/
def addr'_str_24_dfc8 : UInt64 := 0xdfc8
/-- `.str.25` (static, 14 bytes) -/
def addr'_str_25_dfd8 : UInt64 := 0xdfd8
/-- `.str.26` (static, 14 bytes) -/
def addr'_str_26_dfe8 : UInt64 := 0xdfe8
/-- `AC_PosControl::convert_parameters(...)::conversion_info` (static, 336 bytes) -/
def addr'AC_PosControl__convert_parameters_______conversion_info : UInt64 := 0xdff8
/-- `.str.17` (static, 12 bytes) -/
def addr'_str_17_e148 : UInt64 := 0xe148
/-- `.str.18` (static, 12 bytes) -/
def addr'_str_18_e158 : UInt64 := 0xe158
/-- `.str.19` (static, 12 bytes) -/
def addr'_str_19_e168 : UInt64 := 0xe168
/-- `.str.20` (static, 15 bytes) -/
def addr'_str_20_e178 : UInt64 := 0xe178
/-- `.str.21` (static, 15 bytes) -/
def addr'_str_21_e188 : UInt64 := 0xe188
/-- `.str.22` (static, 13 bytes) -/
def addr'_str_22_e198 : UInt64 := 0xe198
/-- `.str.23` (static, 13 bytes) -/
def addr'_str_23_e1a8 : UInt64 := 0xe1a8
/-- `.str.24` (static, 15 bytes) -/
def addr'_str_24_e1b8 : UInt64 := 0xe1b8
/-- `.str.25` (static, 15 bytes) -/
def addr'_str_25_e1c8 : UInt64 := 0xe1c8
/-- `.str.26` (static, 15 bytes) -/
def addr'_str_26_e1d8 : UInt64 := 0xe1d8
/-- `.str.27` (static, 15 bytes) -/
def addr'_str_27_e1e8 : UInt64 := 0xe1e8
/-- `.str.28` (static, 15 bytes) -/
def addr'_str_28_e1f8 : UInt64 := 0xe1f8
/-- `.str.29` (static, 15 bytes) -/
def addr'_str_29_e208 : UInt64 := 0xe208
/-- `.str.30` (static, 14 bytes) -/
def addr'_str_30_e218 : UInt64 := 0xe218
/-- `.str.31` (static, 14 bytes) -/
def addr'_str_31_e228 : UInt64 := 0xe228
/-- `.str.32` (static, 13 bytes) -/
def addr'_str_32_e238 : UInt64 := 0xe238
/-- `.str.33` (static, 13 bytes) -/
def addr'_str_33_e248 : UInt64 := 0xe248
/-- `.str.34` (static, 13 bytes) -/
def addr'_str_34_e258 : UInt64 := 0xe258
/-- `.str.35` (static, 16 bytes) -/
def addr'_str_35_e268 : UInt64 := 0xe268
/-- `.str.36` (static, 16 bytes) -/
def addr'_str_36_e278 : UInt64 := 0xe278
/-- `.str.37` (static, 14 bytes) -/
def addr'_str_37 : UInt64 := 0xe288
/-- `AC_PosControl::convert_parameters(...)::conversion_info_01` (static, 48 bytes) -/
def addr'AC_PosControl__convert_parameters_______conversion_info_01 : UInt64 := 0xe298
/-- `.str.38` (static, 12 bytes) -/
def addr'_str_38 : UInt64 := 0xe2c8
/-- `.str.39` (static, 12 bytes) -/
def addr'_str_39 : UInt64 := 0xe2d8
/-- `.str.40` (static, 12 bytes) -/
def addr'_str_40 : UInt64 := 0xe2e8
/-- `AC_PosControl::convert_parameters(...)::conversion_info_001` (static, 32 bytes) -/
def addr'AC_PosControl__convert_parameters_______conversion_info_001 : UInt64 := 0xe2f8
/-- `.str.41` (static, 15 bytes) -/
def addr'_str_41 : UInt64 := 0xe318
/-- `.str.42` (static, 16 bytes) -/
def addr'_str_42 : UInt64 := 0xe328
/-- `AC_PosControl::convert_parameters(...)::conversion_info_0001` (static, 16 bytes) -/
def addr'AC_PosControl__convert_parameters_______conversion_info_0001 : UInt64 := 0xe338
/-- `.str.43` (static, 15 bytes) -/
def addr'_str_43 : UInt64 := 0xe348
/-- `AC_WPNav::convert_parameters(...)::conversion_info` (static, 168 bytes) -/
def addr'AC_WPNav__convert_parameters_______conversion_info : UInt64 := 0xe358
/-- `.str.14` (static, 7 bytes) -/
def addr'_str_14_e400 : UInt64 := 0xe400
/-- `.str.15` (static, 12 bytes) -/
def addr'_str_15_e408 : UInt64 := 0xe408
/-- `.str.16` (static, 10 bytes) -/
def addr'_str_16_e418 : UInt64 := 0xe418
/-- `.str.17` (static, 10 bytes) -/
def addr'_str_17_e428 : UInt64 := 0xe428
/-- `.str.18` (static, 7 bytes) -/
def addr'_str_18_e438 : UInt64 := 0xe438
/-- `.str.19` (static, 9 bytes) -/
def addr'_str_19_e440 : UInt64 := 0xe440
/-- `.str.20` (static, 11 bytes) -/
def addr'_str_20_e450 : UInt64 := 0xe450
/-- `AC_Loiter::convert_parameters(...)::conversion_info` (static, 96 bytes) -/
def addr'AC_Loiter__convert_parameters_______conversion_info : UInt64 := 0xe460
/-- `.str.11` (static, 14 bytes) -/
def addr'_str_11_e4c0 : UInt64 := 0xe4c0
/-- `.str.12` (static, 15 bytes) -/
def addr'_str_12_e4d0 : UInt64 := 0xe4d0
/-- `.str.13` (static, 15 bytes) -/
def addr'_str_13_e4e0 : UInt64 := 0xe4e0
/-- `.str.14` (static, 15 bytes) -/
def addr'_str_14_e4f0 : UInt64 := 0xe4f0
/-- `AC_Circle::convert_parameters(...)::conversion_info` (static, 24 bytes) -/
def addr'AC_Circle__convert_parameters_______conversion_info : UInt64 := 0xe500
/-- `.str.7` (static, 16 bytes) -/
def addr'_str_7_e518 : UInt64 := 0xe518
/-- `RC_Channels::_singleton` (static, 8 bytes) -/
def addr'RC_Channels___singleton : UInt64 := 0xe528
/-- `SRV_Channels::disabled_mask` (static, 4 bytes) -/
def addr'SRV_Channels__disabled_mask : UInt64 := 0xe530
/-- `SRV_Channels::function_mask` (static, 24 bytes) -/
def addr'SRV_Channels__function_mask : UInt64 := 0xe538
/-- `SRV_Channels::functions` (static, 1520 bytes) -/
def addr'SRV_Channels__functions : UInt64 := 0xe550
/-- `SRV_Channels::invalid_mask` (static, 4 bytes) -/
def addr'SRV_Channels__invalid_mask : UInt64 := 0xeb40
/-- `SRV_Channels::initialised` (static, 1 bytes) -/
def addr'SRV_Channels__initialised : UInt64 := 0xeb48
/-- `failsafe_last_ticks` (static, 2 bytes) -/
def addr'failsafe_last_ticks : UInt64 := 0xeb50
/-- `in_failsafe` (static, 1 bytes) -/
def addr'in_failsafe : UInt64 := 0xeb58
/-- `Copter::gcs_mode_enabled(...)::mode_list` (static, 24 bytes) -/
def addr'Copter__gcs_mode_enabled_______mode_list : UInt64 := 0xeb60
/-- `Mode::auto_yaw` (static, 48 bytes) -/
def addr'Mode__auto_yaw : UInt64 := 0xeb78
/-- `guided_vel_target_ned_ms` (static, 12 bytes) -/
def addr'guided_vel_target_ned_ms : UInt64 := 0xeba8
/-- `guided_accel_target_ned_mss` (static, 12 bytes) -/
def addr'guided_accel_target_ned_mss : UInt64 := 0xebb8
/-- `chan_discard` (static, 16 bytes) -/
def addr'chan_discard : UInt64 := 0xebc8
/-- `GCS_MAVLINK::mavlink_active` (static, 4 bytes) -/
def addr'GCS_MAVLINK__mavlink_active : UInt64 := 0xebd8
/-- `GCS_MAVLINK::mavlink_id_to_ap_message_id(...)::map` (static, 384 bytes) -/
def addr'GCS_MAVLINK__mavlink_id_to_ap_message_id_______map : UInt64 := 0xebe0
/-- `AP_SerialManager::_singleton` (static, 8 bytes) -/
def addr'AP_SerialManager___singleton : UInt64 := 0xed60
/-- `AP_Notify::_singleton` (static, 8 bytes) -/
def addr'AP_Notify___singleton : UInt64 := 0xed68
/-- `dummy_rcchannel` (static, 56 bytes) -/
def addr'dummy_rcchannel : UInt64 := 0xed70
/-- `SRV_Channels::digital_mask` (static, 4 bytes) -/
def addr'SRV_Channels__digital_mask : UInt64 := 0xeda8
/-- `Copter::set_throttle_zero_flag(...)::last_nonzero_throttle_ms` (static, 4 bytes) -/
def addr'Copter__set_throttle_zero_flag_______last_nonzero_throttle_ms : UInt64 := 0xedb0
/-- `guided_limit` (static, 48 bytes) -/
def addr'guided_limit : UInt64 := 0xedb8
/-- `Mode::takeoff` (static, 12 bytes) -/
def addr'Mode__takeoff : UInt64 := 0xede8
/-- `fill_nanf(...)::created` (static, 1 bytes) -/
def addr'fill_nanf_______created : UInt64 := 0xedf8
/-- `fill_nanf(...)::many_nanfs` (static, 16384 bytes) -/
def addr'fill_nanf_______many_nanfs : UInt64 := 0xee00
/-- `guided_angle_state` (static, 44 bytes) -/
def addr'guided_angle_state : UInt64 := 0x12e00
/-- `update_time_ms` (static, 4 bytes) -/
def addr'update_time_ms : UInt64 := 0x12e30
/-- `guided_pos_target_ned_m` (static, 24 bytes) -/
def addr'guided_pos_target_ned_m : UInt64 := 0x12e38
/-- `guided_is_terrain_alt` (static, 1 bytes) -/
def addr'guided_is_terrain_alt : UInt64 := 0x12e50
/-- `GCS_MAVLINK::send_position_target_global_int(...)::POSITION_TARGET_TYPEMASK_LAST_BYTE` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_position_target_global_int_______POSITION_TARGET_TYPEMASK_LAST_BYTE : UInt64 := 0x12e58
/-- `GCS_MAVLINK::send_position_target_global_int(...)::TYPE_MASK` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_position_target_global_int_______TYPE_MASK : UInt64 := 0x12e60
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XACC` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_XACC : UInt64 := 0x12e68
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YACC` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_YACC : UInt64 := 0x12e70
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZACC` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_ZACC : UInt64 := 0x12e78
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XGYRO` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_XGYRO : UInt64 := 0x12e80
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YGYRO` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_YGYRO : UInt64 := 0x12e88
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZGYRO` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_ZGYRO : UInt64 := 0x12e90
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XMAG` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_XMAG : UInt64 := 0x12e98
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YMAG` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_YMAG : UInt64 := 0x12ea0
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZMAG` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_ZMAG : UInt64 := 0x12ea8
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ABS_PRESSURE` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_ABS_PRESSURE : UInt64 := 0x12eb0
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_DIFF_PRESSURE` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_DIFF_PRESSURE : UInt64 := 0x12eb8
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_PRESSURE_ALT` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_PRESSURE_ALT : UInt64 := 0x12ec0
/-- `GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_TEMPERATURE` (static, 2 bytes) -/
def addr'GCS_MAVLINK__send_highres_imu_______HIGHRES_IMU_UPDATED_TEMPERATURE : UInt64 := 0x12ec8
/-- `GCS_MAVLINK::send_servo_output_raw(...)::max_channels` (static, 1 bytes) -/
def addr'GCS_MAVLINK__send_servo_output_raw_______max_channels : UInt64 := 0x12ed0
/-- `GCS_MAVLINK_Copter::send_pid_tuning(...)::axes` (static, 16 bytes) -/
def addr'GCS_MAVLINK_Copter__send_pid_tuning_______axes : UInt64 := 0x12ed8
/-- `RCMapper::_singleton` (static, 8 bytes) -/
def addr'RCMapper___singleton : UInt64 := 0x12ee8
/-- `AP_Motors::_singleton` (static, 8 bytes) -/
def addr'AP_Motors___singleton : UInt64 := 0x12ef0
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors` (static, 64 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors : UInt64 := 0x12ef8
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_0` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_0 : UInt64 := 0x12f38
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_1` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_1 : UInt64 := 0x12f68
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_2` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_2 : UInt64 := 0x12f98
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_3` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_3 : UInt64 := 0x12fc8
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_4` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_4 : UInt64 := 0x12ff8
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_5` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_5 : UInt64 := 0x13028
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_6` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_6 : UInt64 := 0x13058
/-- `AP_MotorsMatrix::setup_quad_matrix(...)::motors_7` (static, 48 bytes) -/
def addr'AP_MotorsMatrix__setup_quad_matrix_______motors_7 : UInt64 := 0x13088
/-- `SRV_Channels::disabled_passthrough` (static, 1 bytes) -/
def addr'SRV_Channels__disabled_passthrough : UInt64 := 0x130b8
/-- `SRV_Channels::emergency_stop` (static, 1 bytes) -/
def addr'SRV_Channels__emergency_stop : UInt64 := 0x130c0
/-- `GCS_MAVLINK::param_timer_registered` (static, 1 bytes) -/
def addr'GCS_MAVLINK__param_timer_registered : UInt64 := 0x130c8
/-- `GCS_MAVLINK::last_radio_status` (static, 16 bytes) -/
def addr'GCS_MAVLINK__last_radio_status : UInt64 := 0x130d0
/-- `exponentTable` (static, 32 bytes) -/
def addr'exponentTable : UInt64 := 0x130e0
/-- `factorTable` (static, 128 bytes) -/
def addr'factorTable : UInt64 := 0x13100
/-- `AP_Arming_Copter::arm(...)::in_arm_motors` (static, 1 bytes) -/
def addr'AP_Arming_Copter__arm_______in_arm_motors : UInt64 := 0x13180
/-- `AP_BattMonitor::_singleton` (static, 8 bytes) -/
def addr'AP_BattMonitor___singleton : UInt64 := 0x13188
/-- `GCS_MAVLINK::mav_frame_for_command_long(...)::frame_map` (static, 32 bytes) -/
def addr'GCS_MAVLINK__mav_frame_for_command_long_______frame_map : UInt64 := 0x13190
/-- `Mode::auto_takeoff` (static, 40 bytes) -/
def addr'Mode__auto_takeoff : UInt64 := 0x131b0
/-- `ModeGuided::takeoff_complete` (static, 1 bytes) -/
def addr'ModeGuided__takeoff_complete : UInt64 := 0x131d8
/-- `AP_Param::num_read_only` (static, 2 bytes) -/
def addr'AP_Param__num_read_only : UInt64 := 0x131e0
/-- `StorageManager::last_io_failed` (static, 1 bytes) -/
def addr'StorageManager__last_io_failed : UInt64 := 0x131e8
/-- `error_bit_descriptions` (static, 240 bytes) -/
def addr'error_bit_descriptions : UInt64 := 0x131f0
/-- `.str.2` (static, 11 bytes) -/
def addr'_str_2 : UInt64 := 0x132e0
/-- `.str.3` (static, 12 bytes) -/
def addr'_str_3_132f0 : UInt64 := 0x132f0
/-- `.str.4` (static, 13 bytes) -/
def addr'_str_4_13300 : UInt64 := 0x13300
/-- `.str.5` (static, 13 bytes) -/
def addr'_str_5_13310 : UInt64 := 0x13310
/-- `.str.6` (static, 12 bytes) -/
def addr'_str_6_13320 : UInt64 := 0x13320
/-- `.str.7` (static, 6 bytes) -/
def addr'_str_7_13330 : UInt64 := 0x13330
/-- `.str.8` (static, 13 bytes) -/
def addr'_str_8_13338 : UInt64 := 0x13338
/-- `.str.9` (static, 13 bytes) -/
def addr'_str_9_13348 : UInt64 := 0x13348
/-- `.str.10` (static, 11 bytes) -/
def addr'_str_10_13358 : UInt64 := 0x13358
/-- `.str.11` (static, 11 bytes) -/
def addr'_str_11_13368 : UInt64 := 0x13368
/-- `.str.12` (static, 13 bytes) -/
def addr'_str_12_13378 : UInt64 := 0x13378
/-- `.str.13` (static, 13 bytes) -/
def addr'_str_13_13388 : UInt64 := 0x13388
/-- `.str.14` (static, 12 bytes) -/
def addr'_str_14_13398 : UInt64 := 0x13398
/-- `.str.15` (static, 11 bytes) -/
def addr'_str_15_133a8 : UInt64 := 0x133a8
/-- `.str.16` (static, 9 bytes) -/
def addr'_str_16_133b8 : UInt64 := 0x133b8
/-- `.str.17` (static, 14 bytes) -/
def addr'_str_17_133c8 : UInt64 := 0x133c8
/-- `.str.18` (static, 13 bytes) -/
def addr'_str_18_133d8 : UInt64 := 0x133d8
/-- `.str.19` (static, 14 bytes) -/
def addr'_str_19_133e8 : UInt64 := 0x133e8
/-- `.str.20` (static, 11 bytes) -/
def addr'_str_20_133f8 : UInt64 := 0x133f8
/-- `.str.21` (static, 8 bytes) -/
def addr'_str_21_13408 : UInt64 := 0x13408
/-- `.str.22` (static, 13 bytes) -/
def addr'_str_22_13410 : UInt64 := 0x13410
/-- `.str.23` (static, 14 bytes) -/
def addr'_str_23_13420 : UInt64 := 0x13420
/-- `.str.24` (static, 13 bytes) -/
def addr'_str_24_13430 : UInt64 := 0x13430
/-- `.str.25` (static, 13 bytes) -/
def addr'_str_25_13440 : UInt64 := 0x13440
/-- `.str.26` (static, 10 bytes) -/
def addr'_str_26_13450 : UInt64 := 0x13450
/-- `.str.27` (static, 9 bytes) -/
def addr'_str_27_13460 : UInt64 := 0x13460
/-- `.str.28` (static, 10 bytes) -/
def addr'_str_28_13470 : UInt64 := 0x13470
/-- `.str.29` (static, 9 bytes) -/
def addr'_str_29_13480 : UInt64 := 0x13480
/-- `.str.30` (static, 16 bytes) -/
def addr'_str_30_13490 : UInt64 := 0x13490
/-- `.str.31` (static, 18 bytes) -/
def addr'_str_31_134a0 : UInt64 := 0x134a0
/-- `AP_CANManager::_singleton` (static, 8 bytes) -/
def addr'AP_CANManager___singleton : UInt64 := 0x134b8
/-- `auto_disarm_begin` (static, 4 bytes) -/
def addr'auto_disarm_begin : UInt64 := 0x134c0
/-- `ekf_check_state` (static, 256 bytes) -/
def addr'ekf_check_state : UInt64 := 0x134c8
/-- `Copter::lost_vehicle_check(...)::soundalarm_counter` (static, 1 bytes) -/
def addr'Copter__lost_vehicle_check_______soundalarm_counter : UInt64 := 0x135c8
/-- `AC_AttitudeControl::VECTORF_111` (static, 12 bytes) -/
def addr'AC_AttitudeControl__VECTORF_111 : UInt64 := 0x135d0
/-- `Copter::crash_check(...)::crash_counter` (static, 2 bytes) -/
def addr'Copter__crash_check_______crash_counter : UInt64 := 0x135e0
/-- `Copter::thrust_loss_check(...)::thrust_loss_counter` (static, 2 bytes) -/
def addr'Copter__thrust_loss_check_______thrust_loss_counter : UInt64 := 0x135e8
/-- `SRV_Channels::_slew` (static, 8 bytes) -/
def addr'SRV_Channels___slew : UInt64 := 0x135f0
/-- `SRV_Channels::override_counter` (static, 64 bytes) -/
def addr'SRV_Channels__override_counter : UInt64 := 0x135f8
/-- `motor_test_start_ms` (static, 4 bytes) -/
def addr'motor_test_start_ms : UInt64 := 0x13638
/-- `motor_test_timeout_ms` (static, 4 bytes) -/
def addr'motor_test_timeout_ms : UInt64 := 0x13640
/-- `motor_test_count` (static, 1 bytes) -/
def addr'motor_test_count : UInt64 := 0x13648
/-- `motor_test_seq` (static, 1 bytes) -/
def addr'motor_test_seq : UInt64 := 0x13650
/-- `motor_test_throttle_type` (static, 1 bytes) -/
def addr'motor_test_throttle_type : UInt64 := 0x13658
/-- `motor_test_throttle_value` (static, 4 bytes) -/
def addr'motor_test_throttle_value : UInt64 := 0x13660
/-- `RC_Channel::lookuptable` (static, 304 bytes) -/
def addr'RC_Channel__lookuptable : UInt64 := 0x13668
/-- `.str.11` (static, 13 bytes) -/
def addr'_str_11_13798 : UInt64 := 0x13798
/-- `.str.12` (static, 13 bytes) -/
def addr'_str_12_137a8 : UInt64 := 0x137a8
/-- `.str.13` (static, 11 bytes) -/
def addr'_str_13_137b8 : UInt64 := 0x137b8
/-- `.str.14` (static, 15 bytes) -/
def addr'_str_14_137c8 : UInt64 := 0x137c8
/-- `.str.15` (static, 16 bytes) -/
def addr'_str_15_137d8 : UInt64 := 0x137d8
/-- `.str.16` (static, 15 bytes) -/
def addr'_str_16_137e8 : UInt64 := 0x137e8
/-- `.str.17` (static, 14 bytes) -/
def addr'_str_17_137f8 : UInt64 := 0x137f8
/-- `.str.18` (static, 13 bytes) -/
def addr'_str_18_13808 : UInt64 := 0x13808
/-- `.str.19` (static, 13 bytes) -/
def addr'_str_19_13818 : UInt64 := 0x13818
/-- `.str.20` (static, 11 bytes) -/
def addr'_str_20_13828 : UInt64 := 0x13828
/-- `.str.21` (static, 14 bytes) -/
def addr'_str_21_13838 : UInt64 := 0x13838
/-- `.str.22` (static, 14 bytes) -/
def addr'_str_22_13848 : UInt64 := 0x13848
/-- `.str.23` (static, 16 bytes) -/
def addr'_str_23_13858 : UInt64 := 0x13858
/-- `.str.24` (static, 8 bytes) -/
def addr'_str_24_13868 : UInt64 := 0x13868
/-- `.str.25` (static, 20 bytes) -/
def addr'_str_25_13870 : UInt64 := 0x13870
/-- `.str.26` (static, 18 bytes) -/
def addr'_str_26_13888 : UInt64 := 0x13888
/-- `.str.27` (static, 12 bytes) -/
def addr'_str_27_138a0 : UInt64 := 0x138a0
/-- `.str.28` (static, 14 bytes) -/
def addr'_str_28_138b0 : UInt64 := 0x138b0
/-- `.str.29` (static, 17 bytes) -/
def addr'_str_29_138c0 : UInt64 := 0x138c0
/-- `vehicle` (static, 8 bytes) -/
def addr'vehicle : UInt64 := 0x138d8
/-- `Copter::_failsafe_priorities` (static, 7 bytes) -/
def addr'Copter___failsafe_priorities : UInt64 := 0x138e0
/-- `AP_Notify::_num_devices` (static, 1 bytes) -/
def addr'AP_Notify___num_devices : UInt64 := 0x138e8
/-- `AP_Notify::_devices` (static, 96 bytes) -/
def addr'AP_Notify___devices : UInt64 := 0x138f0

/-- The constant data: each table, string and static at its address, as its bytes (hex). -/
def image : Array (UInt64 × String) := #[
  
    /- Copter::var_info (ArduCopter/Parameters.cpp):
       {"FORMAT_VERSION", copter+6776, def_value=0.0, flags=0, key=0, type=2}
       {"PILOT_THR_FILT", copter+6780, def_value=0.0, flags=0, key=62, type=4}
       {"PILOT_THR_BHV", copter+6784, def_value=0.0, flags=0, key=63, type=2}
       {"GCS_PID_MASK", copter+6836, def_value=0.0, flags=0, key=126, type=2}
       {"RTL_CONE_SLOPE", copter+6788, def_value=3.0, flags=0, key=137, type=4}
       {"RTL_LOIT_TIME", copter+6792, def_value=5000.0, flags=0, key=162, type=3}
       {"RTL_ALT_TYPE", copter+6796, def_value=0.0, flags=0, key=94, type=1}
       {"FS_GCS_ENABLE", copter+6797, def_value=0.0, flags=0, key=198, type=1}
       {"GPS_HDOP_GOOD", copter+6798, def_value=140.0, flags=0, key=35, type=2}
       {"SUPER_SIMPLE", copter+6800, def_value=0.0, flags=0, key=155, type=1}
       {"WP_YAW_BEHAVIOR", copter+6801, def_value=2.0, flags=0, key=26, type=1}
       {"FS_THR_ENABLE", copter+6802, def_value=1.0, flags=0, key=182, type=1}
       {"FS_THR_VALUE", copter+6804, def_value=975.0, flags=0, key=184, type=2}
       {"THR_DZ", copter+6806, def_value=100.0, flags=0, key=57, type=2}
       {"FLTMODE1", copter+6808, def_value=0.0, flags=0, key=200, type=1}
       {"FLTMODE2", copter+6809, def_value=0.0, flags=0, key=201, type=1}
       {"FLTMODE3", copter+6810, def_value=0.0, flags=0, key=202, type=1}
       {"FLTMODE4", copter+6811, def_value=0.0, flags=0, key=203, type=1}
       {"FLTMODE5", copter+6812, def_value=0.0, flags=0, key=204, type=1}
       {"FLTMODE6", copter+6813, def_value=0.0, flags=0, key=205, type=1}
       {"FLTMODE_CH", copter+6815, def_value=5.0, flags=0, key=207, type=1}
       {"INITIAL_MODE", copter+6816, def_value=0.0, flags=0, key=208, type=1}
       {"SIMPLE", copter+6814, def_value=0.0, flags=0, key=206, type=1}
       {"LOG_BITMASK", copter+6820, def_value=180222.0, flags=0, key=60, type=3}
       {"ESC_CALIBRATION", copter+6824, def_value=0.0, flags=0, key=186, type=1}
       {"FRAME_TYPE", copter+6825, def_value=1.0, flags=0, key=149, type=1}
       {"ARMING_", copter+8768, group_info=AP_Arming::var_info, flags=0, key=252, type=6}
       {"DISARM_DELAY", copter+6826, def_value=10.0, flags=0, key=91, type=1}
       {"LAND_REPOSITION", copter+6827, def_value=1.0, flags=0, key=52, type=1}
       {"FS_EKF_ACTION", copter+6828, def_value=1.0, flags=0, key=248, type=1}
       {"FS_EKF_THRESH", copter+6832, def_value=0.800000011920929, flags=0, key=54, type=4}
       {"FS_CRASH_CHECK", copter+6829, def_value=1.0, flags=0, key=92, type=1}
       {"RC_SPEED", copter+6838, def_value=490.0, flags=0, key=192, type=2}
       {"COMPASS_", copter+1512, group_info=Compass::var_info, flags=0, key=147, type=6}
       {"INS", copter+2344, group_info=AP_InertialSensor::var_info, flags=0, key=3, type=6}
       {"WP_", copter+11192, group_info=AC_WPNav::var_info, flags=2, key=101, type=6}
       {"LOIT_", copter+11200, group_info=AC_Loiter::var_info, flags=2, key=105, type=6}
       {"CIRCLE_", copter+11208, group_info=AC_Circle::var_info, flags=2, key=104, type=6}
       {"ATC_", copter+11168, group_info_ptr=copter+11176, flags=18, key=102, type=6}
       {"PSC", copter+11184, group_info=AC_PosControl::var_info, flags=2, key=103, type=6}
       {"AHRS_", copter+4080, group_info=AP_AHRS::var_info, flags=0, key=159, type=6}
       {"BATT", copter+9584, group_info=AP_BattMonitor::var_info, flags=0, key=36, type=6}
       {"BRD_", copter+8, group_info=AP_BoardConfig::var_info, flags=0, key=15, type=6}
       {"CAN_", copter+96, group_info=AP_CANManager::var_info, flags=0, key=8, type=6}
       {"SIM_", copter+6360, group_info=SITL::SIM::var_info, flags=0, key=10, type=6}
       {"BARO", copter+1200, group_info=AP_Baro::var_info, flags=0, key=11, type=6}
       {"GPS", copter+384, group_info=AP_GPS::var_info, flags=0, key=16, type=6}
       {"SCHED_", copter+208, group_info=AP_Scheduler::var_info, flags=0, key=12, type=6}
       {"MOT_", copter+9528, group_info_ptr=copter+9536, flags=18, key=90, type=6}
       {"RCMAP_", copter+9496, group_info=RCMapper::var_info, flags=0, key=199, type=6}
       {"EK3_", AP_AHRS_NavEKF3::EKF3, group_info=NavEKF3::var_info, flags=0, key=7, type=6}
       {"MIS_", copter+11480, group_info=AP_Mission::var_info, flags=0, key=42, type=6}
       {"NTF_", copter+3992, group_info=AP_Notify::var_info, flags=0, key=73, type=6}
       {"", copter+6840, group_info=ParametersG2::var_info, flags=0, key=6, type=6}
       {"", copter, group_info=AP_Vehicle::var_info, flags=0, key=257, type=6}
       {"MAV", copter+8904, group_info=GCS::var_info, flags=0, key=260, type=6}
       {"", null, def_value=0.0, flags=0, key=0, type=0} -/
    (0x1000, "201700000000000050a100000000000000000000000000000000000002000000301700000000000054a1000000000000000000000000000000003e0004000000401700000000000058a1000000000000000000000000000000003f000200000050170000000000008ca1000000000000000000000000000000007e000200000060170000000000005ca100000000000000004040000000000000890004000000701700000000000060a100000000000000409c45000000000000a20003000000801700000000000064a1000000000000000000000000000000005e0001000000901700000000000065a100000000000000000000000000000000c60001000000a01700000000000066a100000000000000000c43000000000000230002000000b01700000000000068a1000000000000000000000000000000009b0001000000c01700000000000069a1000000000000000000400000000000001a0001000000d0170000000000006aa10000000000000000803f000000000000b60001000000e0170000000000006ca100000000000000c07344000000000000b80002000000f0170000000000006ea10000000000000000c842000000000000390002000000f81700000000000070a100000000000000000000000000000000c80001000000081800000000000071a100000000000000000000000000000000c90001000000181800000000000072a100000000000000000000000000000000ca0001000000281800000000000073a100000000000000000000000000000000cb0001000000381800000000000074a100000000000000000000000000000000cc0001000000481800000000000075a100000000000000000000000000000000cd0001000000581800000000000077a10000000000000000a040000000000000cf0001000000681800000000000078a100000000000000000000000000000000d00001000000781800000000000076a100000000000000000000000000000000ce000100000080180000000000007ca100000000000080ff2f480000000000003c0003000000901800000000000080a100000000000000000000000000000000ba0001000000a01800000000000081a10000000000000000803f000000000000950001000000b01800000000000018a900000000000068210000000000000000fc0006000000b81800000000000082a1000000000000000020410000000000005b0001000000c81800000000000083a10000000000000000803f000000000000340001000000d81800000000000084a10000000000000000803f000000000000f80001000000e81800000000000088a1000000000000cdcc4c3f000000000000360004000000f81800000000000085a10000000000000000803f0000000000005c000100000008190000000000008ea10000000000000000f543000000000000c000020000001819000000000000c08c000000000000f022000000000000000093000600000028190000000000000090000000000000302a0000000000000000030006000000301900000000000090b2000000000000e82f0000000000000200650006000000381900000000000098b2000000000000b83100000000000002006900060000004019000000000000a0b200000000000020330000000000000200680006000000481900000000000078b200000000000080b20000000000001200660006000000501900000000000088b2000000000000c83300000000000002006700060000005819000000000000c896000000000000503500000000000000009f0006000000601900000000000048ac000000000000f03700000000000000002400060000006819000000000000e086000000000000a03a00000000000000000f000600000070190000000000003887000000000000483e00000000000000000800060000007819000000000000b09f000000000000403f00000000000000000a00060000008019000000000000888b000000000000683f00000000000000000b000600000088190000000000005888000000000000484200000000000000001000060000009019000000000000a887000000000000a04400000000000000000c0006000000981900000000000010ac00000000000018ac00000000000012005a0006000000a019000000000000f0ab00000000000048450000000000000000c70006000000a819000000000000308400000000000068460000000000000000070006000000b019000000000000b0b3000000000000805100000000000000002a0006000000b819000000000000709600000000000020520000000000000000490006000000c01900000000000090a1000000000000c0530000000000000000060006000000c019000000000000d88600000000000020570000000000000000010106000000c819000000000000a0a9000000000000a8570000000000000000040106000000c019000000000000000000000000000000000000000000000000000000000000"),
  (0x1720, "464f524d41545f56455253494f4e00"),
  (0x1730, "50494c4f545f5448525f46494c5400"),
  (0x1740, "50494c4f545f5448525f42485600"),
  (0x1750, "4743535f5049445f4d41534b00"),
  (0x1760, "52544c5f434f4e455f534c4f504500"),
  (0x1770, "52544c5f4c4f49545f54494d4500"),
  (0x1780, "52544c5f414c545f5459504500"),
  (0x1790, "46535f4743535f454e41424c4500"),
  (0x17a0, "4750535f48444f505f474f4f4400"),
  (0x17b0, "53555045525f53494d504c4500"),
  (0x17c0, "57505f5941575f4245484156494f5200"),
  (0x17d0, "46535f5448525f454e41424c4500"),
  (0x17e0, "46535f5448525f56414c554500"),
  (0x17f0, "5448525f445a00"),
  (0x17f8, "464c544d4f44453100"),
  (0x1808, "464c544d4f44453200"),
  (0x1818, "464c544d4f44453300"),
  (0x1828, "464c544d4f44453400"),
  (0x1838, "464c544d4f44453500"),
  (0x1848, "464c544d4f44453600"),
  (0x1858, "464c544d4f44455f434800"),
  (0x1868, "494e495449414c5f4d4f444500"),
  (0x1878, "53494d504c4500"),
  (0x1880, "4c4f475f4249544d41534b00"),
  (0x1890, "4553435f43414c4942524154494f4e00"),
  (0x18a0, "4652414d455f5459504500"),
  (0x18b0, "41524d494e475f00"),
  (0x18b8, "44495341524d5f44454c415900"),
  (0x18c8, "4c414e445f5245504f534954494f4e00"),
  (0x18d8, "46535f454b465f414354494f4e00"),
  (0x18e8, "46535f454b465f54485245534800"),
  (0x18f8, "46535f43524153485f434845434b00"),
  (0x1908, "52435f535045454400"),
  (0x1918, "434f4d504153535f00"),
  (0x1928, "494e5300"),
  (0x1930, "57505f00"),
  (0x1938, "4c4f49545f00"),
  (0x1940, "434952434c455f00"),
  (0x1948, "4154435f00"),
  (0x1950, "50534300"),
  (0x1958, "414852535f00"),
  (0x1960, "4241545400"),
  (0x1968, "4252445f00"),
  (0x1970, "43414e5f00"),
  (0x1978, "53494d5f00"),
  (0x1980, "4241524f00"),
  (0x1988, "47505300"),
  (0x1990, "53434845445f00"),
  (0x1998, "4d4f545f00"),
  (0x19a0, "52434d41505f00"),
  (0x19a8, "454b335f00"),
  (0x19b0, "4d49535f00"),
  (0x19b8, "4e54465f00"),
  (0x19c8, "4d415600"),
  
    /- AC_AttitudeControl_Multi::var_info (libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp):
       {"", 0, group_info=AC_AttitudeControl::var_info, flags=0, idx=0, type=6}
       {"RAT_RLL_", 376, group_info=AC_PID::var_info, flags=1, idx=1, type=6}
       {"RAT_PIT_", 616, group_info=AC_PID::var_info, flags=1, idx=2, type=6}
       {"RAT_YAW_", 856, group_info=AC_PID::var_info, flags=1, idx=3, type=6}
       {"THR_MIX_MIN", 1100, def_value=0.10000000149011612, flags=0, idx=4, type=4}
       {"THR_MIX_MAX", 1104, def_value=0.5, flags=0, idx=5, type=4}
       {"THR_MIX_MAN", 1096, def_value=0.10000000149011612, flags=0, idx=6, type=4}
       {"THR_G_BOOST", 1108, def_value=0.0, flags=0, idx=7, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x19d0, "f01a0000000000000000000000000000385b0000000000000000000600000000f81a0000000000007801000000000000c05e0000000000000100010600000000081b0000000000006802000000000000c05e0000000000000100020600000000181b0000000000005803000000000000c05e0000000000000100030600000000281b0000000000004c04000000000000cdcccc3d000000000000040400000000381b00000000000050040000000000000000003f000000000000050400000000481b0000000000004804000000000000cdcccc3d000000000000060400000000581b000000000000540400000000000000000000000000000000070400000000f01a000000000000000000000000000000000000000000000000ff0000000000"),
  (0x1af8, "5241545f524c4c5f00"),
  (0x1b08, "5241545f5049545f00"),
  (0x1b18, "5241545f5941575f00"),
  (0x1b28, "5448525f4d49585f4d494e00"),
  (0x1b38, "5448525f4d49585f4d415800"),
  (0x1b48, "5448525f4d49585f4d414e00"),
  (0x1b58, "5448525f475f424f4f535400"),
  
    /- AP_MotorsMulticopter::var_info (libraries/AP_Motors/AP_MotorsMulticopter.cpp):
       {"YAW_HEADROOM", 280, def_value=200.0, flags=0, idx=6, type=2}
       {"THST_EXPO", 224, def_value=0.6499999761581421, flags=0, idx=8, type=4}
       {"SPIN_MAX", 232, def_value=0.949999988079071, flags=0, idx=9, type=4}
       {"BAT_VOLT_MAX", 240, def_value=0.0, flags=0, idx=10, type=4}
       {"BAT_VOLT_MIN", 244, def_value=0.0, flags=0, idx=11, type=4}
       {"BAT_CURR_MAX", 300, def_value=0.0, flags=0, idx=12, type=4}
       {"PWM_TYPE", 204, def_value=0.0, flags=0, idx=15, type=1}
       {"PWM_MIN", 308, def_value=1000.0, flags=0, idx=16, type=2}
       {"PWM_MAX", 310, def_value=2000.0, flags=0, idx=17, type=2}
       {"SPIN_MIN", 228, def_value=0.15000000596046448, flags=0, idx=18, type=4}
       {"SPIN_ARM", 296, def_value=0.10000000149011612, flags=0, idx=19, type=4}
       {"BAT_CURR_TC", 304, def_value=5.0, flags=0, idx=20, type=4}
       {"THST_HOVER", 312, def_value=0.3499999940395355, flags=0, idx=21, type=4}
       {"HOVER_LEARN", 316, def_value=2.0, flags=0, idx=22, type=1}
       {"SAFE_DISARM", 317, def_value=0.0, flags=0, idx=23, type=1}
       {"YAW_SV_ANGLE", 320, def_value=30.0, flags=4096, idx=35, type=4}
       {"SPOOL_TIME", 324, def_value=0.5, flags=0, idx=36, type=4}
       {"BOOST_SCALE", 336, def_value=0.0, flags=0, idx=37, type=4}
       {"BAT_IDX", 236, def_value=0.0, flags=0, idx=39, type=1}
       {"SLEW_UP_TIME", 284, def_value=0.0, flags=0, idx=40, type=4}
       {"SLEW_DN_TIME", 288, def_value=0.0, flags=0, idx=41, type=4}
       {"SAFE_TIME", 292, def_value=1.0, flags=0, idx=42, type=4}
       {"OPTIONS", 212, def_value=0.0, flags=0, idx=43, type=2}
       {"SPOOL_TIM_DN", 328, def_value=0.0, flags=0, idx=44, type=4}
       {"IDLE_SEC", 332, def_value=0.0, flags=0, idx=45, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x1b68, "a81e000000000000180100000000000000004843000000000000060200000000b81e000000000000e0000000000000006666263f000000000000080400000000c81e000000000000e8000000000000003333733f000000000000090400000000d81e000000000000f000000000000000000000000000000000000a0400000000e81e000000000000f400000000000000000000000000000000000b0400000000f81e0000000000002c01000000000000000000000000000000000c0400000000081f000000000000cc00000000000000000000000000000000000f0100000000181f000000000000340100000000000000007a44000000000000100200000000201f00000000000036010000000000000000fa44000000000000110200000000281f000000000000e4000000000000009a99193e000000000000120400000000381f0000000000002801000000000000cdcccc3d000000000000130400000000481f00000000000030010000000000000000a040000000000000140400000000581f00000000000038010000000000003333b33e000000000000150400000000681f0000000000003c0100000000000000000040000000000000160100000000781f0000000000003d0100000000000000000000000000000000170100000000881f00000000000040010000000000000000f041000000000010230400000000981f00000000000044010000000000000000003f000000000000240400000000a81f000000000000500100000000000000000000000000000000250400000000b81f000000000000ec0000000000000000000000000000000000270100000000c01f0000000000001c0100000000000000000000000000000000280400000000d01f000000000000200100000000000000000000000000000000290400000000e01f00000000000024010000000000000000803f0000000000002a0400000000f01f000000000000d400000000000000000000000000000000002b0200000000f81f0000000000004801000000000000000000000000000000002c040000000008200000000000004c01000000000000000000000000000000002d04000000001820000000000000000000000000000000000000000000000000ff0000000000"),
  (0x1ea8, "5941575f48454144524f4f4d00"),
  (0x1eb8, "544853545f4558504f00"),
  (0x1ec8, "5350494e5f4d415800"),
  (0x1ed8, "4241545f564f4c545f4d415800"),
  (0x1ee8, "4241545f564f4c545f4d494e00"),
  (0x1ef8, "4241545f435552525f4d415800"),
  (0x1f08, "50574d5f5459504500"),
  (0x1f18, "50574d5f4d494e00"),
  (0x1f20, "50574d5f4d415800"),
  (0x1f28, "5350494e5f4d494e00"),
  (0x1f38, "5350494e5f41524d00"),
  (0x1f48, "4241545f435552525f544300"),
  (0x1f58, "544853545f484f56455200"),
  (0x1f68, "484f5645525f4c4541524e00"),
  (0x1f78, "534146455f44495341524d00"),
  (0x1f88, "5941575f53565f414e474c4500"),
  (0x1f98, "53504f4f4c5f54494d4500"),
  (0x1fa8, "424f4f53545f5343414c4500"),
  (0x1fb8, "4241545f49445800"),
  (0x1fc0, "534c45575f55505f54494d4500"),
  (0x1fd0, "534c45575f444e5f54494d4500"),
  (0x1fe0, "534146455f54494d4500"),
  (0x1ff0, "4f5054494f4e5300"),
  (0x1ff8, "53504f4f4c5f54494d5f444e00"),
  (0x2008, "49444c455f53454300"),
  
    /- AP_BattMonitor_Analog::var_info (libraries/AP_BattMonitor/AP_BattMonitor_Analog.cpp):
       {"VOLT_PIN", 88, def_value=13.0, flags=0, idx=1, type=1}
       {"CURR_PIN", 89, def_value=12.0, flags=0, idx=2, type=1}
       {"VOLT_MULT", 72, def_value=10.100000381469727, flags=0, idx=3, type=4}
       {"AMP_PERVLT", 76, def_value=17.0, flags=0, idx=4, type=4}
       {"AMP_OFFSET", 80, def_value=0.0, flags=0, idx=5, type=4}
       {"VLT_OFFSET", 84, def_value=0.0, flags=0, idx=6, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x2020, "00210000000000005800000000000000000050410000000000000101000000001021000000000000590000000000000000004041000000000000020100000000202100000000000048000000000000009a99214100000000000003040000000030210000000000004c0000000000000000008841000000000000040400000000402100000000000050000000000000000000000000000000000005040000000050210000000000005400000000000000000000000000000000000604000000006021000000000000000000000000000000000000000000000000ff0000000000"),
  (0x2100, "564f4c545f50494e00"),
  (0x2110, "435552525f50494e00"),
  (0x2120, "564f4c545f4d554c5400"),
  (0x2130, "414d505f504552564c5400"),
  (0x2140, "414d505f4f464653455400"),
  (0x2150, "564c545f4f464653455400"),
  
    /- AP_Arming::var_info (libraries/AP_Arming/AP_Arming.cpp):
       {"REQUIRE", 8, def_value=1.0, flags=1544, idx=0, type=1}
       {"ACCTHRESH", 16, def_value=0.75, flags=0, idx=3, type=4}
       {"RUDDER", 20, def_value=2.0, flags=30464, idx=6, type=1}
       {"MIS_ITEMS", 24, def_value=0.0, flags=0, idx=7, type=3}
       {"OPTIONS", 28, def_value=0.0, flags=0, idx=9, type=3}
       {"MAGTHRESH", 32, def_value=100.0, flags=0, idx=10, type=2}
       {"NEED_LOC", 34, def_value=0.0, flags=0, idx=12, type=1}
       {"SKIPCHK", 12, def_value=0.0, flags=0, idx=13, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x2168, "882200000000000008000000000000000000803f000000000806000100000000902200000000000010000000000000000000403f000000000000030400000000a022000000000000140000000000000000000040000000000077060100000000a822000000000000180000000000000000000000000000000000070300000000b8220000000000001c0000000000000000000000000000000000090300000000c02200000000000020000000000000000000c8420000000000000a0200000000d0220000000000002200000000000000000000000000000000000c0100000000e0220000000000000c00000000000000000000000000000000000d0300000000e822000000000000000000000000000000000000000000000000ff0000000000"),
  (0x2288, "5245515549524500"),
  (0x2290, "41434354485245534800"),
  (0x22a0, "52554444455200"),
  (0x22a8, "4d49535f4954454d5300"),
  (0x22b8, "4f5054494f4e5300"),
  (0x22c0, "4d414754485245534800"),
  (0x22d0, "4e4545445f4c4f4300"),
  (0x22e0, "534b495043484b00"),
  
    /- Compass::var_info (libraries/AP_Compass/AP_Compass.cpp):
       {"OFS", 60, def_value=0.0, flags=0, idx=1, type=5}
       {"DEC", 32, def_value=0.0, flags=0, idx=2, type=4}
       {"USE", 548, def_value=1.0, flags=0, idx=4, type=1}
       {"AUTODEC", 36, def_value=1.0, flags=0, idx=5, type=1}
       {"MOTCT", 44, def_value=0.0, flags=0, idx=6, type=1}
       {"MOT", 112, def_value=0.0, flags=0, idx=7, type=5}
       {"ORIENT", 56, def_value=0.0, flags=0, idx=8, type=1}
       {"EXTERNAL", 52, def_value=0.0, flags=0, idx=9, type=1}
       {"OFS2", 184, def_value=0.0, flags=0, idx=10, type=5}
       {"MOT2", 236, def_value=0.0, flags=0, idx=11, type=5}
       {"OFS3", 308, def_value=0.0, flags=0, idx=13, type=5}
       {"MOT3", 360, def_value=0.0, flags=0, idx=14, type=5}
       {"DEV_ID", 100, def_value=0.0, flags=0, idx=15, type=3}
       {"DEV_ID2", 224, def_value=0.0, flags=0, idx=16, type=3}
       {"DEV_ID3", 348, def_value=0.0, flags=0, idx=17, type=3}
       {"USE2", 549, def_value=1.0, flags=0, idx=18, type=1}
       {"ORIENT2", 180, def_value=0.0, flags=0, idx=19, type=1}
       {"EXTERN2", 176, def_value=0.0, flags=0, idx=20, type=1}
       {"USE3", 550, def_value=1.0, flags=0, idx=21, type=1}
       {"ORIENT3", 304, def_value=0.0, flags=0, idx=22, type=1}
       {"EXTERN3", 300, def_value=0.0, flags=0, idx=23, type=1}
       {"DIA", 72, def_value=1.0, flags=0, idx=24, type=5}
       {"ODI", 84, def_value=0.0, flags=0, idx=25, type=5}
       {"DIA2", 196, def_value=1.0, flags=0, idx=26, type=5}
       {"ODI2", 208, def_value=0.0, flags=0, idx=27, type=5}
       {"DIA3", 320, def_value=1.0, flags=0, idx=28, type=5}
       {"ODI3", 332, def_value=0.0, flags=0, idx=29, type=5}
       {"OFFS_MAX", 576, def_value=1800.0, flags=0, idx=31, type=2}
       {"PMOT", 584, group_info=Compass_PerMotor::var_info, flags=1, idx=32, type=6}
       {"DISBLMSK", 764, def_value=0.0, flags=0, idx=33, type=3}
       {"FLTR_RNG", 808, def_value=0.0, flags=0, idx=34, type=1}
       {"PRIO1_ID", 552, def_value=0.0, flags=0, idx=36, type=3}
       {"PRIO2_ID", 556, def_value=0.0, flags=0, idx=37, type=3}
       {"PRIO3_ID", 560, def_value=0.0, flags=0, idx=38, type=3}
       {"ENABLE", 25, def_value=1.0, flags=0, idx=39, type=1}
       {"SCALE", 96, def_value=0.0, flags=0, idx=40, type=4}
       {"SCALE2", 220, def_value=0.0, flags=0, idx=41, type=4}
       {"SCALE3", 344, def_value=0.0, flags=0, idx=42, type=4}
       {"OPTIONS", 578, def_value=0.0, flags=0, idx=43, type=2}
       {"DEV_ID4", 768, def_value=0.0, flags=0, idx=44, type=3}
       {"DEV_ID5", 772, def_value=0.0, flags=0, idx=45, type=3}
       {"DEV_ID6", 776, def_value=0.0, flags=0, idx=46, type=3}
       {"DEV_ID7", 780, def_value=0.0, flags=0, idx=47, type=3}
       {"DEV_ID8", 784, def_value=0.0, flags=0, idx=48, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x22f0, "90280000000000003c00000000000000000000000000000000000105000000009828000000000000200000000000000000000000000000000000020400000000a02800000000000024020000000000000000803f000000000000040100000000a82800000000000024000000000000000000803f000000000000050100000000b0280000000000002c0000000000000000000000000000000000060100000000b828000000000000700000000000000000000000000000000000070500000000c028000000000000380000000000000000000000000000000000080100000000c828000000000000340000000000000000000000000000000000090100000000d828000000000000b800000000000000000000000000000000000a0500000000e028000000000000ec00000000000000000000000000000000000b0500000000e8280000000000003401000000000000000000000000000000000d0500000000f0280000000000006801000000000000000000000000000000000e0500000000f8280000000000006400000000000000000000000000000000000f03000000000029000000000000e0000000000000000000000000000000000010030000000008290000000000005c0100000000000000000000000000000000110300000000102900000000000025020000000000000000803f0000000000001201000000001829000000000000b400000000000000000000000000000000001301000000002029000000000000b00000000000000000000000000000000000140100000000282900000000000026020000000000000000803f000000000000150100000000302900000000000030010000000000000000000000000000000016010000000038290000000000002c0100000000000000000000000000000000170100000000402900000000000048000000000000000000803f00000000000018050000000048290000000000005400000000000000000000000000000000001905000000005029000000000000c4000000000000000000803f0000000000001a05000000005829000000000000d000000000000000000000000000000000001b0500000000602900000000000040010000000000000000803f0000000000001c050000000068290000000000004c01000000000000000000000000000000001d0500000000702900000000000040020000000000000000e1440000000000001f020000000080290000000000004802000000000000a06000000000000001002006000000008829000000000000fc02000000000000000000000000000000002103000000009829000000000000280300000000000000000000000000000000220100000000a829000000000000280200000000000000000000000000000000240300000000b8290000000000002c0200000000000000000000000000000000250300000000c829000000000000300200000000000000000000000000000000260300000000d82900000000000019000000000000000000803f000000000000270100000000e029000000000000600000000000000000000000000000000000280400000000e829000000000000dc0000000000000000000000000000000000290400000000f0290000000000005801000000000000000000000000000000002a0400000000f8290000000000004202000000000000000000000000000000002b0200000000002a0000000000000003000000000000000000000000000000002c0300000000082a0000000000000403000000000000000000000000000000002d0300000000102a0000000000000803000000000000000000000000000000002e0300000000182a0000000000000c03000000000000000000000000000000002f0300000000202a000000000000100300000000000000000000000000000000300300000000282a000000000000000000000000000000000000000000000000ff0000000000"),
  (0x2890, "4f465300"),
  (0x2898, "44454300"),
  (0x28a0, "55534500"),
  (0x28a8, "4155544f44454300"),
  (0x28b0, "4d4f54435400"),
  (0x28b8, "4d4f5400"),
  (0x28c0, "4f5249454e5400"),
  (0x28c8, "45585445524e414c00"),
  (0x28d8, "4f46533200"),
  (0x28e0, "4d4f543200"),
  (0x28e8, "4f46533300"),
  (0x28f0, "4d4f543300"),
  (0x28f8, "4445565f494400"),
  (0x2900, "4445565f49443200"),
  (0x2908, "4445565f49443300"),
  (0x2910, "5553453200"),
  (0x2918, "4f5249454e543200"),
  (0x2920, "45585445524e3200"),
  (0x2928, "5553453300"),
  (0x2930, "4f5249454e543300"),
  (0x2938, "45585445524e3300"),
  (0x2940, "44494100"),
  (0x2948, "4f444900"),
  (0x2950, "4449413200"),
  (0x2958, "4f44493200"),
  (0x2960, "4449413300"),
  (0x2968, "4f44493300"),
  (0x2970, "4f4646535f4d415800"),
  (0x2980, "504d4f5400"),
  (0x2988, "444953424c4d534b00"),
  (0x2998, "464c54525f524e4700"),
  (0x29a8, "5052494f315f494400"),
  (0x29b8, "5052494f325f494400"),
  (0x29c8, "5052494f335f494400"),
  (0x29d8, "454e41424c4500"),
  (0x29e0, "5343414c4500"),
  (0x29e8, "5343414c453200"),
  (0x29f0, "5343414c453300"),
  (0x29f8, "4f5054494f4e5300"),
  (0x2a00, "4445565f49443400"),
  (0x2a08, "4445565f49443500"),
  (0x2a10, "4445565f49443600"),
  (0x2a18, "4445565f49443700"),
  (0x2a20, "4445565f49443800"),
  
    /- AP_InertialSensor::var_info (libraries/AP_InertialSensor/AP_InertialSensor.cpp):
       {"_GYROFFS", 968, def_value=0.0, flags=0, idx=3, type=5}
       {"_GYR2OFFS", 980, def_value=0.0, flags=0, idx=7, type=5}
       {"_GYR3OFFS", 992, def_value=0.0, flags=0, idx=10, type=5}
       {"_ACCSCAL", 896, def_value=1.0, flags=0, idx=12, type=5}
       {"_ACCOFFS", 932, def_value=0.0, flags=0, idx=13, type=5}
       {"_ACC2SCAL", 908, def_value=1.0, flags=0, idx=14, type=5}
       {"_ACC2OFFS", 944, def_value=0.0, flags=0, idx=15, type=5}
       {"_ACC3SCAL", 920, def_value=1.0, flags=0, idx=16, type=5}
       {"_ACC3OFFS", 956, def_value=0.0, flags=0, idx=17, type=5}
       {"_GYRO_FILTER", 1174, def_value=20.0, flags=0, idx=18, type=2}
       {"_ACCEL_FILTER", 1172, def_value=20.0, flags=0, idx=19, type=2}
       {"_USE", 1177, def_value=1.0, flags=0, idx=20, type=1}
       {"_USE2", 1178, def_value=1.0, flags=0, idx=21, type=1}
       {"_USE3", 1179, def_value=1.0, flags=0, idx=22, type=1}
       {"_STILL_THRESH", 1404, def_value=2.5, flags=0, idx=23, type=4}
       {"_GYR_CAL", 1176, def_value=1.0, flags=0, idx=24, type=1}
       {"_TRIM_OPTION", 1409, def_value=1.0, flags=0, idx=25, type=1}
       {"_ACC_BODYFIX", 1408, def_value=2.0, flags=0, idx=26, type=1}
       {"_POS1", 1004, def_value=0.0, flags=0, idx=27, type=5}
       {"_POS2", 1016, def_value=0.0, flags=0, idx=28, type=5}
       {"_POS3", 1028, def_value=0.0, flags=0, idx=29, type=5}
       {"_GYR_ID", 884, def_value=0.0, flags=0, idx=30, type=3}
       {"_GYR2_ID", 888, def_value=0.0, flags=0, idx=31, type=3}
       {"_GYR3_ID", 892, def_value=0.0, flags=0, idx=32, type=3}
       {"_ACC_ID", 872, def_value=0.0, flags=0, idx=33, type=3}
       {"_ACC2_ID", 876, def_value=0.0, flags=0, idx=34, type=3}
       {"_ACC3_ID", 880, def_value=0.0, flags=0, idx=35, type=3}
       {"_FAST_SAMPLE", 1180, def_value=1.0, flags=0, idx=36, type=1}
       {"_ENABLE_MASK", 1182, def_value=127.0, flags=0, idx=40, type=1}
       {"_GYRO_RATE", 1181, def_value=0.0, flags=0, idx=42, type=1}
       {"_RAW_LOG_OPT", 1480, def_value=0.0, flags=0, idx=56, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x2a30, "302e000000000000c80300000000000000000000000000000000030500000000402e000000000000d40300000000000000000000000000000000070500000000502e000000000000e003000000000000000000000000000000000a0500000000602e00000000000080030000000000000000803f0000000000000c0500000000702e000000000000a403000000000000000000000000000000000d0500000000802e0000000000008c030000000000000000803f0000000000000e0500000000902e000000000000b003000000000000000000000000000000000f0500000000a02e00000000000098030000000000000000803f000000000000100500000000b02e000000000000bc0300000000000000000000000000000000110500000000c02e00000000000096040000000000000000a041000000000000120200000000d02e00000000000094040000000000000000a041000000000000130200000000e02e00000000000099040000000000000000803f000000000000140100000000e82e0000000000009a040000000000000000803f000000000000150100000000f02e0000000000009b040000000000000000803f000000000000160100000000f82e0000000000007c0500000000000000002040000000000000170400000000082f00000000000098040000000000000000803f000000000000180100000000182f00000000000081050000000000000000803f000000000000190100000000282f0000000000008005000000000000000000400000000000001a0100000000382f000000000000ec03000000000000000000000000000000001b0500000000402f000000000000f803000000000000000000000000000000001c0500000000482f0000000000000404000000000000000000000000000000001d0500000000502f0000000000007403000000000000000000000000000000001e0300000000582f0000000000007803000000000000000000000000000000001f0300000000682f0000000000007c0300000000000000000000000000000000200300000000782f000000000000680300000000000000000000000000000000210300000000802f0000000000006c0300000000000000000000000000000000220300000000902f000000000000700300000000000000000000000000000000230300000000a02f0000000000009c040000000000000000803f000000000000240100000000b02f0000000000009e040000000000000000fe42000000000000280100000000c02f0000000000009d04000000000000000000000000000000002a0100000000d02f000000000000c80500000000000000000000000000000000380200000000e02f000000000000000000000000000000000000000000000000ff0000000000"),
  (0x2e30, "5f4759524f46465300"),
  (0x2e40, "5f475952324f46465300"),
  (0x2e50, "5f475952334f46465300"),
  (0x2e60, "5f4143435343414c00"),
  (0x2e70, "5f4143434f46465300"),
  (0x2e80, "5f414343325343414c00"),
  (0x2e90, "5f414343324f46465300"),
  (0x2ea0, "5f414343335343414c00"),
  (0x2eb0, "5f414343334f46465300"),
  (0x2ec0, "5f4759524f5f46494c54455200"),
  (0x2ed0, "5f414343454c5f46494c54455200"),
  (0x2ee0, "5f55534500"),
  (0x2ee8, "5f5553453200"),
  (0x2ef0, "5f5553453300"),
  (0x2ef8, "5f5354494c4c5f54485245534800"),
  (0x2f08, "5f4759525f43414c00"),
  (0x2f18, "5f5452494d5f4f5054494f4e00"),
  (0x2f28, "5f4143435f424f445946495800"),
  (0x2f38, "5f504f533100"),
  (0x2f40, "5f504f533200"),
  (0x2f48, "5f504f533300"),
  (0x2f50, "5f4759525f494400"),
  (0x2f58, "5f475952325f494400"),
  (0x2f68, "5f475952335f494400"),
  (0x2f78, "5f4143435f494400"),
  (0x2f80, "5f414343325f494400"),
  (0x2f90, "5f414343335f494400"),
  (0x2fa0, "5f464153545f53414d504c4500"),
  (0x2fb0, "5f454e41424c455f4d41534b00"),
  (0x2fc0, "5f4759524f5f5241544500"),
  (0x2fd0, "5f5241575f4c4f475f4f505400"),
  
    /- AC_WPNav::var_info (libraries/AC_WPNav/AC_WPNav.cpp):
       {"RFND_USE", 2495, def_value=1.0, flags=0, idx=10, type=1}
       {"JERK", 68, def_value=1.0, flags=0, idx=11, type=4}
       {"TER_MARGIN", 72, def_value=10.0, flags=0, idx=12, type=4}
       {"SPD", 40, def_value=10.0, flags=0, idx=14, type=4}
       {"RADIUS_M", 52, def_value=2.0, flags=0, idx=15, type=4}
       {"SPD_UP", 44, def_value=2.5, flags=0, idx=16, type=4}
       {"SPD_DN", 48, def_value=1.5, flags=0, idx=17, type=4}
       {"ACC", 56, def_value=2.5, flags=0, idx=18, type=4}
       {"ACC_Z", 64, def_value=1.0, flags=0, idx=19, type=4}
       {"ACC_CNR", 60, def_value=0.0, flags=0, idx=20, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x2fe8, "4831000000000000bf090000000000000000803f0000000000000a0100000000583100000000000044000000000000000000803f0000000000000b040000000060310000000000004800000000000000000020410000000000000c040000000070310000000000002800000000000000000020410000000000000e040000000078310000000000003400000000000000000000400000000000000f040000000088310000000000002c0000000000000000002040000000000000100400000000903100000000000030000000000000000000c03f0000000000001104000000009831000000000000380000000000000000002040000000000000120400000000a03100000000000040000000000000000000803f000000000000130400000000a8310000000000003c0000000000000000000000000000000000140400000000b031000000000000000000000000000000000000000000000000ff0000000000"),
  (0x3148, "52464e445f55534500"),
  (0x3158, "4a45524b00"),
  (0x3160, "5445525f4d415247494e00"),
  (0x3170, "53504400"),
  (0x3178, "5241444955535f4d00"),
  (0x3188, "5350445f555000"),
  (0x3190, "5350445f444e00"),
  (0x3198, "41434300"),
  (0x31a0, "4143435f5a00"),
  (0x31a8, "4143435f434e5200"),
  
    /- AC_Loiter::var_info (libraries/AC_WPNav/AC_Loiter.cpp):
       {"ANG_MAX", 24, def_value=0.0, flags=0, idx=1, type=4}
       {"BRK_DELAY", 44, def_value=1.0, flags=0, idx=6, type=4}
       {"OPTIONS", 48, def_value=0.0, flags=0, idx=7, type=1}
       {"SPEED_MS", 28, def_value=12.5, flags=0, idx=8, type=4}
       {"ACC_MAX_M", 32, def_value=5.0, flags=0, idx=9, type=4}
       {"BRK_ACC_M", 36, def_value=2.5, flags=0, idx=10, type=4}
       {"BRK_JRK_M", 40, def_value=5.0, flags=0, idx=11, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x31b8, "b832000000000000180000000000000000000000000000000000010400000000c0320000000000002c000000000000000000803f000000000000060400000000d032000000000000300000000000000000000000000000000000070100000000d8320000000000001c0000000000000000004841000000000000080400000000e83200000000000020000000000000000000a040000000000000090400000000f8320000000000002400000000000000000020400000000000000a0400000000083300000000000028000000000000000000a0400000000000000b04000000001833000000000000000000000000000000000000000000000000ff0000000000"),
  (0x32b8, "414e475f4d415800"),
  (0x32c0, "42524b5f44454c415900"),
  (0x32d0, "4f5054494f4e5300"),
  (0x32d8, "53504545445f4d5300"),
  (0x32e8, "4143435f4d41585f4d00"),
  (0x32f8, "42524b5f4143435f4d00"),
  (0x3308, "42524b5f4a524b5f4d00"),
  
    /- AC_Circle::var_info (libraries/AC_WPNav/AC_Circle.cpp):
       {"RATE", 20, def_value=20.0, flags=0, idx=1, type=4}
       {"OPTIONS", 24, def_value=1.0, flags=0, idx=2, type=2}
       {"RADIUS_M", 16, def_value=10.0, flags=0, idx=3, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3320, "a03300000000000014000000000000000000a041000000000000010400000000a83300000000000018000000000000000000803f000000000000020200000000b033000000000000100000000000000000002041000000000000030400000000c033000000000000000000000000000000000000000000000000ff0000000000"),
  (0x33a0, "5241544500"),
  (0x33a8, "4f5054494f4e5300"),
  (0x33b0, "5241444955535f4d00"),
  
    /- AC_PosControl::var_info (libraries/AC_AttitudeControl/AC_PosControl.cpp):
       {"_D_POS_", 60, group_info=AC_P_1D::var_info, flags=1, idx=2, type=6}
       {"_NE_POS_", 36, group_info=AC_P_2D::var_info, flags=1, idx=5, type=6}
       {"_ANGLE_MAX", 24, def_value=0.0, flags=0, idx=7, type=4}
       {"_NE_JERK", 28, def_value=5.0, flags=0, idx=10, type=4}
       {"_D_JERK", 32, def_value=5.0, flags=0, idx=11, type=4}
       {"_D_VEL_", 264, group_info=AC_PID_Basic::var_info, flags=1, idx=12, type=6}
       {"_D_ACC_", 384, group_info=AC_PID::var_info, flags=1, idx=13, type=6}
       {"_NE_VEL_", 84, group_info=AC_PID_2D::var_info, flags=1, idx=14, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x33c8, "e8340000000000003c00000000000000b8610000000000000100020600000000f034000000000000240000000000000008620000000000000100050600000000003500000000000018000000000000000000000000000000000007040000000010350000000000001c000000000000000000a0400000000000000a0400000000203500000000000020000000000000000000a0400000000000000b040000000028350000000000000801000000000000586200000000000001000c060000000030350000000000008001000000000000c05e00000000000001000d060000000038350000000000005400000000000000986300000000000001000e06000000004835000000000000000000000000000000000000000000000000ff0000000000"),
  (0x34e8, "5f445f504f535f00"),
  (0x34f0, "5f4e455f504f535f00"),
  (0x3500, "5f414e474c455f4d415800"),
  (0x3510, "5f4e455f4a45524b00"),
  (0x3520, "5f445f4a45524b00"),
  (0x3528, "5f445f56454c5f00"),
  (0x3530, "5f445f4143435f00"),
  (0x3538, "5f4e455f56454c5f00"),
  
    /- AP_AHRS::var_info (libraries/AP_AHRS/AP_AHRS.cpp):
       {"GPS_GAIN", 156, def_value=1.0, flags=0, idx=2, type=4}
       {"GPS_USE", 164, def_value=1.0, flags=0, idx=3, type=1}
       {"YAW_P", 148, def_value=0.20000000298023224, flags=0, idx=4, type=4}
       {"RP_P", 152, def_value=0.20000000298023224, flags=0, idx=5, type=4}
       {"WIND_MAX", 144, def_value=0.0, flags=0, idx=6, type=1}
       {"TRIM", 248, def_value=0.0, flags=0, idx=8, type=5}
       {"ORIENTATION", 145, def_value=0.0, flags=0, idx=9, type=1}
       {"COMP_BETA", 160, def_value=0.10000000149011612, flags=0, idx=10, type=4}
       {"GPS_MINSATS", 165, def_value=6.0, flags=0, idx=11, type=1}
       {"EKF_TYPE", 146, def_value=3.0, flags=0, idx=14, type=1}
       {"OPTIONS", 2208, def_value=0.0, flags=0, idx=18, type=2}
       {"ORIGIN_LAT", 168, def_value=0.0, flags=0, idx=19, type=4}
       {"ORIGIN_LON", 172, def_value=0.0, flags=0, idx=20, type=4}
       {"ORIGIN_ALT", 176, def_value=0.0, flags=0, idx=21, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3550, "30370000000000009c000000000000000000803f0000000000000204000000004037000000000000a4000000000000000000803f00000000000003010000000048370000000000009400000000000000cdcc4c3e00000000000004040000000050370000000000009800000000000000cdcc4c3e00000000000005040000000058370000000000009000000000000000000000000000000000000601000000006837000000000000f8000000000000000000000000000000000008050000000070370000000000009100000000000000000000000000000000000901000000008037000000000000a000000000000000cdcccc3d0000000000000a04000000009037000000000000a5000000000000000000c0400000000000000b0100000000a0370000000000009200000000000000000040400000000000000e0100000000b037000000000000a00800000000000000000000000000000000120200000000b837000000000000a80000000000000000000000000000000000130400000000c837000000000000ac0000000000000000000000000000000000140400000000d837000000000000b00000000000000000000000000000000000150400000000e837000000000000000000000000000000000000000000000000ff0000000000"),
  (0x3730, "4750535f4741494e00"),
  (0x3740, "4750535f55534500"),
  (0x3748, "5941575f5000"),
  (0x3750, "52505f5000"),
  (0x3758, "57494e445f4d415800"),
  (0x3768, "5452494d00"),
  (0x3770, "4f5249454e544154494f4e00"),
  (0x3780, "434f4d505f4245544100"),
  (0x3790, "4750535f4d494e5341545300"),
  (0x37a0, "454b465f5459504500"),
  (0x37b0, "4f5054494f4e5300"),
  (0x37b8, "4f524947494e5f4c415400"),
  (0x37c8, "4f524947494e5f4c4f4e00"),
  (0x37d8, "4f524947494e5f414c5400"),
  
    /- AP_BattMonitor::var_info (libraries/AP_BattMonitor/AP_BattMonitor.cpp):
       {"_", 8, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=23, type=6}
       {"_", 1416, group_info_ptr=AP_BattMonitor::backend_var_info, flags=18, idx=41, type=6}
       {"2_", 52, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=24, type=6}
       {"2_", 1424, group_info_ptr=AP_BattMonitor::backend_var_info+8, flags=18, idx=42, type=6}
       {"3_", 96, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=25, type=6}
       {"3_", 1432, group_info_ptr=AP_BattMonitor::backend_var_info+16, flags=18, idx=43, type=6}
       {"4_", 140, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=26, type=6}
       {"4_", 1440, group_info_ptr=AP_BattMonitor::backend_var_info+24, flags=18, idx=44, type=6}
       {"5_", 184, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=27, type=6}
       {"5_", 1448, group_info_ptr=AP_BattMonitor::backend_var_info+32, flags=18, idx=45, type=6}
       {"6_", 228, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=28, type=6}
       {"6_", 1456, group_info_ptr=AP_BattMonitor::backend_var_info+40, flags=18, idx=46, type=6}
       {"7_", 272, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=29, type=6}
       {"7_", 1464, group_info_ptr=AP_BattMonitor::backend_var_info+48, flags=18, idx=47, type=6}
       {"8_", 316, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=30, type=6}
       {"8_", 1472, group_info_ptr=AP_BattMonitor::backend_var_info+56, flags=18, idx=48, type=6}
       {"9_", 360, group_info=AP_BattMonitor_Params::var_info, flags=1, idx=31, type=6}
       {"9_", 1480, group_info_ptr=AP_BattMonitor::backend_var_info+64, flags=18, idx=49, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x37f0, "503a0000000000000800000000000000d8640000000000000100170600000000503a000000000000880500000000000010860000000000001200290600000000583a0000000000003400000000000000d8640000000000000100180600000000583a0000000000009005000000000000188600000000000012002a0600000000603a0000000000006000000000000000d8640000000000000100190600000000603a0000000000009805000000000000208600000000000012002b0600000000683a0000000000008c00000000000000d86400000000000001001a0600000000683a000000000000a005000000000000288600000000000012002c0600000000703a000000000000b800000000000000d86400000000000001001b0600000000703a000000000000a805000000000000308600000000000012002d0600000000783a000000000000e400000000000000d86400000000000001001c0600000000783a000000000000b005000000000000388600000000000012002e0600000000803a0000000000001001000000000000d86400000000000001001d0600000000803a000000000000b805000000000000408600000000000012002f0600000000883a0000000000003c01000000000000d86400000000000001001e0600000000883a000000000000c00500000000000048860000000000001200300600000000903a0000000000006801000000000000d86400000000000001001f0600000000903a000000000000c80500000000000050860000000000001200310600000000983a000000000000000000000000000000000000000000000000ff0000000000"),
  (0x3a50, "5f00"),
  (0x3a58, "325f00"),
  (0x3a60, "335f00"),
  (0x3a68, "345f00"),
  (0x3a70, "355f00"),
  (0x3a78, "365f00"),
  (0x3a80, "375f00"),
  (0x3a88, "385f00"),
  (0x3a90, "395f00"),
  
    /- AP_BoardConfig::var_info (libraries/AP_BoardConfig/AP_BoardConfig.cpp):
       {"SER1_RTSCTS", 13, def_value=0.0, flags=0, idx=1, type=1}
       {"SER2_RTSCTS", 14, def_value=0.0, flags=0, idx=2, type=1}
       {"SER3_RTSCTS", 15, def_value=0.0, flags=0, idx=26, type=1}
       {"SER4_RTSCTS", 16, def_value=0.0, flags=0, idx=27, type=1}
       {"SER5_RTSCTS", 17, def_value=0.0, flags=0, idx=25, type=1}
       {"SER6_RTSCTS", 18, def_value=0.0, flags=0, idx=30, type=1}
       {"SER7_RTSCTS", 19, def_value=0.0, flags=0, idx=31, type=1}
       {"SER8_RTSCTS", 20, def_value=0.0, flags=0, idx=32, type=1}
       {"SAFETY_DEFLT", 4, def_value=0.0, flags=0, idx=3, type=1}
       {"SERIAL_NUM", 0, def_value=0.0, flags=0, idx=5, type=3}
       {"SAFETY_MASK", 8, def_value=0.0, flags=0, idx=7, type=3}
       {"SAFETYOPTION", 6, def_value=3.0, flags=0, idx=13, type=2}
       {"RTC", 32, group_info=AP_RTC::var_info, flags=1, idx=14, type=6}
       {"VBUS_MIN", 64, def_value=4.300000190734863, flags=0, idx=15, type=4}
       {"VSERVO_MIN", 68, def_value=0.0, flags=0, idx=16, type=4}
       {"OPTIONS", 76, def_value=0.0, flags=0, idx=19, type=3}
       {"BOOT_DELAY", 74, def_value=0.0, flags=0, idx=20, type=2}
       {"SD_MISSION", 24, def_value=0.0, flags=0, idx=24, type=2}
       {"SD_FENCE", 26, def_value=0.0, flags=0, idx=29, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3aa0, "203d0000000000000d0000000000000000000000000000000000010100000000303d0000000000000e0000000000000000000000000000000000020100000000403d0000000000000f00000000000000000000000000000000001a0100000000503d0000000000001000000000000000000000000000000000001b0100000000603d000000000000110000000000000000000000000000000000190100000000703d0000000000001200000000000000000000000000000000001e0100000000803d0000000000001300000000000000000000000000000000001f0100000000903d000000000000140000000000000000000000000000000000200100000000a03d000000000000040000000000000000000000000000000000030100000000b03d000000000000000000000000000000000000000000000000050300000000c03d000000000000080000000000000000000000000000000000070300000000d03d0000000000000600000000000000000040400000000000000d0200000000e03d0000000000002000000000000000a86700000000000001000e0600000000e83d00000000000040000000000000009a9989400000000000000f0400000000f83d000000000000440000000000000000000000000000000000100400000000083e0000000000004c0000000000000000000000000000000000130300000000103e0000000000004a0000000000000000000000000000000000140200000000203e000000000000180000000000000000000000000000000000180200000000303e0000000000001a00000000000000000000000000000000001d0200000000403e000000000000000000000000000000000000000000000000ff0000000000"),
  (0x3d20, "534552315f52545343545300"),
  (0x3d30, "534552325f52545343545300"),
  (0x3d40, "534552335f52545343545300"),
  (0x3d50, "534552345f52545343545300"),
  (0x3d60, "534552355f52545343545300"),
  (0x3d70, "534552365f52545343545300"),
  (0x3d80, "534552375f52545343545300"),
  (0x3d90, "534552385f52545343545300"),
  (0x3da0, "5341464554595f4445464c5400"),
  (0x3db0, "53455249414c5f4e554d00"),
  (0x3dc0, "5341464554595f4d41534b00"),
  (0x3dd0, "5341464554594f5054494f4e00"),
  (0x3de0, "52544300"),
  (0x3de8, "564255535f4d494e00"),
  (0x3df8, "56534552564f5f4d494e00"),
  (0x3e08, "4f5054494f4e5300"),
  (0x3e10, "424f4f545f44454c415900"),
  (0x3e20, "53445f4d495353494f4e00"),
  (0x3e30, "53445f46454e434500"),
  
    /- AP_CANManager::var_info (libraries/AP_CANManager/AP_CANManager.cpp):
       {"P1_", 0, group_info=AP_CANManager::CANIface_Params::var_info, flags=1, idx=1, type=6}
       {"P2_", 16, group_info=AP_CANManager::CANIface_Params::var_info, flags=1, idx=2, type=6}
       {"D1_", 48, group_info=AP_CANManager::CANDriver_Params::var_info, flags=1, idx=4, type=6}
       {"D2_", 72, group_info=AP_CANManager::CANDriver_Params::var_info, flags=1, idx=5, type=6}
       {"LOGLEVEL", 98, def_value=0.0, flags=0, idx=8, type=1}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3e48, "083f000000000000000000000000000020680000000000000100010600000000103f000000000000100000000000000020680000000000000100020600000000183f0000000000003000000000000000f0680000000000000100040600000000203f0000000000004800000000000000f0680000000000000100050600000000283f000000000000620000000000000000000000000000000000080100000000383f000000000000000000000000000000000000000000000000ff0000000000"),
  (0x3f08, "50315f00"),
  (0x3f10, "50325f00"),
  (0x3f18, "44315f00"),
  (0x3f20, "44325f00"),
  (0x3f28, "4c4f474c4556454c00"),
  
    /- SITL::SIM::var_info (reference/hal/sensors.cpp):
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3f40, "603f000000000000000000000000000000000000000000000000ff0000000000"),
  
    /- AP_Baro::var_info (libraries/AP_Baro/AP_Baro.cpp):
       {"1_GND_PRESS", 64, def_value=0.0, flags=32, idx=2, type=4}
       {"_GND_TEMP", 276, def_value=0.0, flags=0, idx=3, type=4}
       {"_ALT_OFFSET", 164, def_value=0.0, flags=0, idx=5, type=4}
       {"_PRIMARY", 188, def_value=0.0, flags=0, idx=6, type=1}
       {"_EXT_BUS", 189, def_value=-1.0, flags=0, idx=7, type=1}
       {"_SPEC_GRAV", 272, def_value=1.0, flags=2048, idx=8, type=4}
       {"2_GND_PRESS", 104, def_value=0.0, flags=32, idx=9, type=4}
       {"3_GND_PRESS", 144, def_value=0.0, flags=32, idx=11, type=4}
       {"_FLTR_RNG", 288, def_value=0.0, flags=0, idx=13, type=1}
       {"1_DEVID", 80, def_value=0.0, flags=32, idx=15, type=3}
       {"2_DEVID", 120, def_value=0.0, flags=32, idx=16, type=3}
       {"3_DEVID", 160, def_value=0.0, flags=32, idx=17, type=3}
       {"_FIELD_ELV", 176, def_value=0.0, flags=0, idx=22, type=4}
       {"_ALTERR_MAX", 296, def_value=2000.0, flags=0, idx=23, type=4}
       {"_OPTIONS", 300, def_value=0.0, flags=0, idx=24, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x3f68, "684100000000000040000000000000000000000000000000200002040000000078410000000000001401000000000000000000000000000000000304000000008841000000000000a400000000000000000000000000000000000504000000009841000000000000bc0000000000000000000000000000000000060100000000a841000000000000bd00000000000000000080bf000000000000070100000000b84100000000000010010000000000000000803f000000000008080400000000c841000000000000680000000000000000000000000000002000090400000000d8410000000000009000000000000000000000000000000020000b0400000000e8410000000000002001000000000000000000000000000000000d0100000000f8410000000000005000000000000000000000000000000020000f030000000000420000000000007800000000000000000000000000000020001003000000000842000000000000a000000000000000000000000000000020001103000000001042000000000000b00000000000000000000000000000000000160400000000204200000000000028010000000000000000fa4400000000000017040000000030420000000000002c01000000000000000000000000000000001802000000004042000000000000000000000000000000000000000000000000ff0000000000"),
  (0x4168, "315f474e445f505245535300"),
  (0x4178, "5f474e445f54454d5000"),
  (0x4188, "5f414c545f4f464653455400"),
  (0x4198, "5f5052494d41525900"),
  (0x41a8, "5f4558545f42555300"),
  (0x41b8, "5f535045435f4752415600"),
  (0x41c8, "325f474e445f505245535300"),
  (0x41d8, "335f474e445f505245535300"),
  (0x41e8, "5f464c54525f524e4700"),
  (0x41f8, "315f444556494400"),
  (0x4200, "325f444556494400"),
  (0x4208, "335f444556494400"),
  (0x4210, "5f4649454c445f454c5600"),
  (0x4220, "5f414c544552525f4d415800"),
  (0x4230, "5f4f5054494f4e5300"),
  
    /- AP_GPS::var_info (libraries/AP_GPS/AP_GPS.cpp):
       {"_NAVFILTER", 72, def_value=8.0, flags=0, idx=2, type=1}
       {"_AUTO_SWITCH", 73, def_value=1.0, flags=0, idx=3, type=1}
       {"_SBAS_MODE", 84, def_value=2.0, flags=0, idx=5, type=1}
       {"_MIN_ELEV", 85, def_value=-100.0, flags=0, idx=6, type=1}
       {"_INJECT_TO", 76, def_value=127.0, flags=0, idx=7, type=1}
       {"_RAW_DATA", 86, def_value=0.0, flags=0, idx=9, type=1}
       {"_SAVE_CFG", 87, def_value=2.0, flags=0, idx=11, type=1}
       {"_AUTO_CONFIG", 88, def_value=1.0, flags=0, idx=13, type=1}
       {"_DRV_OPTIONS", 90, def_value=0.0, flags=0, idx=22, type=2}
       {"_PRIMARY", 92, def_value=0.0, flags=0, idx=27, type=1}
       {"1_", 0, group_info=AP_GPS::Params::var_info, flags=1, idx=32, type=6}
       {"2_", 24, group_info=AP_GPS::Params::var_info, flags=1, idx=33, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x4248, "e843000000000000480000000000000000000041000000000000020100000000f84300000000000049000000000000000000803f0000000000000301000000000844000000000000540000000000000000000040000000000000050100000000184400000000000055000000000000000000c8c200000000000006010000000028440000000000004c000000000000000000fe42000000000000070100000000384400000000000056000000000000000000000000000000000009010000000048440000000000005700000000000000000000400000000000000b0100000000584400000000000058000000000000000000803f0000000000000d010000000068440000000000005a000000000000000000000000000000000016020000000078440000000000005c00000000000000000000000000000000001b0100000000884400000000000000000000000000007869000000000000010020060000000090440000000000001800000000000000786900000000000001002106000000009844000000000000000000000000000000000000000000000000ff0000000000"),
  (0x43e8, "5f4e415646494c54455200"),
  (0x43f8, "5f4155544f5f53574954434800"),
  (0x4408, "5f534241535f4d4f444500"),
  (0x4418, "5f4d494e5f454c455600"),
  (0x4428, "5f494e4a4543545f544f00"),
  (0x4438, "5f5241575f4441544100"),
  (0x4448, "5f534156455f43464700"),
  (0x4458, "5f4155544f5f434f4e46494700"),
  (0x4468, "5f4452565f4f5054494f4e5300"),
  (0x4478, "5f5052494d41525900"),
  (0x4488, "315f00"),
  (0x4490, "325f00"),
  
    /- AP_Scheduler::var_info (libraries/AP_Scheduler/AP_Scheduler.cpp):
       {"DEBUG", 56, def_value=0.0, flags=0, idx=0, type=1}
       {"LOOP_RATE", 58, def_value=400.0, flags=0, idx=1, type=2}
       {"OPTIONS", 62, def_value=0.0, flags=0, idx=2, type=1}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x44a0, "204500000000000038000000000000000000000000000000000000010000000028450000000000003a000000000000000000c84300000000000001020000000038450000000000003e00000000000000000000000000000000000201000000004045000000000000000000000000000000000000000000000000ff0000000000"),
  (0x4520, "444542554700"),
  (0x4528, "4c4f4f505f5241544500"),
  (0x4538, "4f5054494f4e5300"),
  
    /- RCMapper::var_info (libraries/AP_RCMapper/AP_RCMapper.cpp):
       {"ROLL", 0, def_value=1.0, flags=0, idx=0, type=1}
       {"PITCH", 1, def_value=2.0, flags=0, idx=1, type=1}
       {"THROTTLE", 3, def_value=3.0, flags=0, idx=2, type=1}
       {"YAW", 2, def_value=4.0, flags=0, idx=3, type=1}
       {"FORWARD", 4, def_value=6.0, flags=2048, idx=4, type=1}
       {"LATERAL", 5, def_value=7.0, flags=2048, idx=5, type=1}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x4548, "284600000000000000000000000000000000803f000000000000000100000000304600000000000001000000000000000000004000000000000001010000000038460000000000000300000000000000000040400000000000000201000000004846000000000000020000000000000000008040000000000000030100000000504600000000000004000000000000000000c040000000000008040100000000584600000000000005000000000000000000e0400000000000080501000000006046000000000000000000000000000000000000000000000000ff0000000000"),
  (0x4628, "524f4c4c00"),
  (0x4630, "504954434800"),
  (0x4638, "5448524f54544c4500"),
  (0x4648, "59415700"),
  (0x4650, "464f525741524400"),
  (0x4658, "4c41544552414c00"),
  
    /- NavEKF3::var_info (libraries/AP_NavEKF3/AP_NavEKF3.cpp):
       {"ENABLE", 29, def_value=1.0, flags=4, idx=0, type=1}
       {"VELNE_M_NSE", 32, def_value=0.30000001192092896, flags=0, idx=2, type=4}
       {"VELD_M_NSE", 36, def_value=0.5, flags=0, idx=3, type=4}
       {"VEL_I_GATE", 90, def_value=500.0, flags=0, idx=4, type=2}
       {"POSNE_M_NSE", 40, def_value=0.5, flags=0, idx=5, type=4}
       {"POS_I_GATE", 92, def_value=500.0, flags=0, idx=6, type=2}
       {"GLITCH_RAD", 101, def_value=25.0, flags=0, idx=7, type=1}
       {"ALT_M_NSE", 44, def_value=2.0, flags=0, idx=10, type=4}
       {"HGT_I_GATE", 94, def_value=500.0, flags=0, idx=11, type=2}
       {"HGT_DELAY", 88, def_value=60.0, flags=0, idx=12, type=2}
       {"MAG_M_NSE", 48, def_value=0.05000000074505806, flags=0, idx=13, type=4}
       {"MAG_CAL", 100, def_value=3.0, flags=0, idx=14, type=1}
       {"MAG_I_GATE", 96, def_value=300.0, flags=0, idx=15, type=2}
       {"EAS_M_NSE", 52, def_value=1.399999976158142, flags=0, idx=16, type=4}
       {"EAS_I_GATE", 98, def_value=400.0, flags=0, idx=17, type=2}
       {"RNG_M_NSE", 124, def_value=0.5, flags=0, idx=18, type=4}
       {"RNG_I_GATE", 112, def_value=500.0, flags=0, idx=19, type=2}
       {"FLOW_MAX", 116, def_value=2.5, flags=0, idx=20, type=4}
       {"FLOW_M_NSE", 104, def_value=0.25, flags=0, idx=21, type=4}
       {"FLOW_I_GATE", 108, def_value=300.0, flags=0, idx=22, type=2}
       {"FLOW_DELAY", 110, def_value=10.0, flags=0, idx=23, type=1}
       {"GYRO_P_NSE", 72, def_value=0.014999999664723873, flags=0, idx=24, type=4}
       {"ACC_P_NSE", 76, def_value=0.3499999940395355, flags=0, idx=25, type=4}
       {"GBIAS_P_NSE", 80, def_value=0.0010000000474974513, flags=0, idx=26, type=4}
       {"ABIAS_P_NSE", 84, def_value=0.019999999552965164, flags=0, idx=28, type=4}
       {"WIND_P_NSE", 56, def_value=0.20000000298023224, flags=0, idx=30, type=4}
       {"WIND_PSCALE", 60, def_value=1.0, flags=0, idx=31, type=4}
       {"GPS_CHECK", 128, def_value=31.0, flags=0, idx=32, type=1}
       {"IMU_MASK", 129, def_value=3.0, flags=0, idx=33, type=1}
       {"CHECK_SCALE", 130, def_value=100.0, flags=0, idx=34, type=2}
       {"NOAID_M_NSE", 132, def_value=10.0, flags=0, idx=35, type=4}
       {"BETA_MASK", 220, def_value=0.0, flags=0, idx=36, type=1}
       {"YAW_M_NSE", 136, def_value=0.5, flags=0, idx=37, type=4}
       {"YAW_I_GATE", 140, def_value=300.0, flags=0, idx=38, type=2}
       {"TAU_OUTPUT", 142, def_value=25.0, flags=0, idx=39, type=1}
       {"MAGE_P_NSE", 64, def_value=0.0010000000474974513, flags=0, idx=40, type=4}
       {"MAGB_P_NSE", 68, def_value=9.999999747378752e-05, flags=0, idx=41, type=4}
       {"RNG_USE_HGT", 143, def_value=-1.0, flags=0, idx=42, type=1}
       {"TERR_GRAD", 144, def_value=0.10000000149011612, flags=0, idx=43, type=4}
       {"BCN_M_NSE", 148, def_value=1.0, flags=0, idx=44, type=4}
       {"BCN_I_GTE", 152, def_value=500.0, flags=0, idx=45, type=2}
       {"BCN_DELAY", 154, def_value=50.0, flags=0, idx=46, type=1}
       {"RNG_USE_SPD", 156, def_value=2.0, flags=0, idx=47, type=4}
       {"ACC_BIAS_LIM", 160, def_value=1.0, flags=0, idx=48, type=4}
       {"MAG_MASK", 164, def_value=0.0, flags=0, idx=49, type=1}
       {"OGN_HGT_MASK", 165, def_value=0.0, flags=0, idx=50, type=1}
       {"VIS_VERR_MIN", 172, def_value=0.10000000149011612, flags=0, idx=51, type=4}
       {"VIS_VERR_MAX", 168, def_value=0.8999999761581421, flags=0, idx=52, type=4}
       {"WENC_VERR", 176, def_value=0.10000000149011612, flags=0, idx=53, type=4}
       {"FLOW_USE", 180, def_value=1.0, flags=0, idx=54, type=1}
       {"HRT_FILT", 184, def_value=2.0, flags=0, idx=55, type=4}
       {"MAG_EF_LIM", 188, def_value=50.0, flags=0, idx=56, type=2}
       {"GSF_RUN_MASK", 190, def_value=3.0, flags=0, idx=57, type=1}
       {"GSF_USE_MASK", 191, def_value=3.0, flags=0, idx=58, type=1}
       {"FLOW_GAIN_H", 120, def_value=4.0, flags=0, idx=59, type=4}
       {"GSF_RST_MAX", 192, def_value=2.0, flags=0, idx=60, type=1}
       {"ERR_THRESH", 196, def_value=0.20000000298023224, flags=0, idx=61, type=4}
       {"AFFINITY", 200, def_value=0.0, flags=0, idx=62, type=3}
       {"", 0, group_info=NavEKF3::var_info2, flags=1, idx=63, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x4668, "e84d0000000000001d000000000000000000803f000000000400000100000000f04d00000000000020000000000000009a99993e000000000000020400000000004e00000000000024000000000000000000003f000000000000030400000000104e0000000000005a000000000000000000fa43000000000000040200000000204e00000000000028000000000000000000003f000000000000050400000000304e0000000000005c000000000000000000fa43000000000000060200000000404e00000000000065000000000000000000c841000000000000070100000000504e0000000000002c00000000000000000000400000000000000a0400000000604e0000000000005e000000000000000000fa430000000000000b0200000000704e0000000000005800000000000000000070420000000000000c0200000000804e0000000000003000000000000000cdcc4c3d0000000000000d0400000000904e0000000000006400000000000000000040400000000000000e0100000000984e0000000000006000000000000000000096430000000000000f0200000000a84e00000000000034000000000000003333b33f000000000000100400000000b84e00000000000062000000000000000000c843000000000000110200000000c84e0000000000007c000000000000000000003f000000000000120400000000d84e00000000000070000000000000000000fa43000000000000130200000000e84e000000000000740000000000000000002040000000000000140400000000f84e00000000000068000000000000000000803e000000000000150400000000084f0000000000006c0000000000000000009643000000000000160200000000184f0000000000006e0000000000000000002041000000000000170100000000284f00000000000048000000000000008fc2753c000000000000180400000000384f0000000000004c000000000000003333b33e000000000000190400000000484f00000000000050000000000000006f12833a0000000000001a0400000000584f00000000000054000000000000000ad7a33c0000000000001c0400000000684f0000000000003800000000000000cdcc4c3e0000000000001e0400000000784f0000000000003c000000000000000000803f0000000000001f0400000000884f00000000000080000000000000000000f841000000000000200100000000984f000000000000810000000000000000004040000000000000210100000000a84f00000000000082000000000000000000c842000000000000220200000000b84f000000000000840000000000000000002041000000000000230400000000c84f000000000000dc0000000000000000000000000000000000240100000000d84f00000000000088000000000000000000003f000000000000250400000000e84f0000000000008c0000000000000000009643000000000000260200000000f84f0000000000008e000000000000000000c841000000000000270100000000085000000000000040000000000000006f12833a0000000000002804000000001850000000000000440000000000000017b7d13800000000000029040000000028500000000000008f00000000000000000080bf0000000000002a010000000038500000000000009000000000000000cdcccc3d0000000000002b0400000000485000000000000094000000000000000000803f0000000000002c0400000000585000000000000098000000000000000000fa430000000000002d020000000068500000000000009a00000000000000000048420000000000002e010000000078500000000000009c00000000000000000000400000000000002f04000000008850000000000000a0000000000000000000803f0000000000003004000000009850000000000000a40000000000000000000000000000000000310100000000a850000000000000a50000000000000000000000000000000000320100000000b850000000000000ac00000000000000cdcccc3d000000000000330400000000c850000000000000a8000000000000006666663f000000000000340400000000d850000000000000b000000000000000cdcccc3d000000000000350400000000e850000000000000b4000000000000000000803f000000000000360100000000f850000000000000b800000000000000000000400000000000003704000000000851000000000000bc00000000000000000048420000000000003802000000001851000000000000be00000000000000000040400000000000003901000000002851000000000000bf00000000000000000040400000000000003a010000000038510000000000007800000000000000000080400000000000003b04000000004851000000000000c000000000000000000000400000000000003c01000000005851000000000000c400000000000000cdcc4c3e0000000000003d04000000006851000000000000c800000000000000000000000000000000003e030000000078510000000000000000000000000000786a00000000000001003f06000000007851000000000000000000000000000000000000000000000000ff0000000000"),
  (0x4de8, "454e41424c4500"),
  (0x4df0, "56454c4e455f4d5f4e534500"),
  (0x4e00, "56454c445f4d5f4e534500"),
  (0x4e10, "56454c5f495f4741544500"),
  (0x4e20, "504f534e455f4d5f4e534500"),
  (0x4e30, "504f535f495f4741544500"),
  (0x4e40, "474c495443485f52414400"),
  (0x4e50, "414c545f4d5f4e534500"),
  (0x4e60, "4847545f495f4741544500"),
  (0x4e70, "4847545f44454c415900"),
  (0x4e80, "4d41475f4d5f4e534500"),
  (0x4e90, "4d41475f43414c00"),
  (0x4e98, "4d41475f495f4741544500"),
  (0x4ea8, "4541535f4d5f4e534500"),
  (0x4eb8, "4541535f495f4741544500"),
  (0x4ec8, "524e475f4d5f4e534500"),
  (0x4ed8, "524e475f495f4741544500"),
  (0x4ee8, "464c4f575f4d415800"),
  (0x4ef8, "464c4f575f4d5f4e534500"),
  (0x4f08, "464c4f575f495f4741544500"),
  (0x4f18, "464c4f575f44454c415900"),
  (0x4f28, "4759524f5f505f4e534500"),
  (0x4f38, "4143435f505f4e534500"),
  (0x4f48, "47424941535f505f4e534500"),
  (0x4f58, "41424941535f505f4e534500"),
  (0x4f68, "57494e445f505f4e534500"),
  (0x4f78, "57494e445f505343414c4500"),
  (0x4f88, "4750535f434845434b00"),
  (0x4f98, "494d555f4d41534b00"),
  (0x4fa8, "434845434b5f5343414c4500"),
  (0x4fb8, "4e4f4149445f4d5f4e534500"),
  (0x4fc8, "424554415f4d41534b00"),
  (0x4fd8, "5941575f4d5f4e534500"),
  (0x4fe8, "5941575f495f4741544500"),
  (0x4ff8, "5441555f4f555450555400"),
  (0x5008, "4d4147455f505f4e534500"),
  (0x5018, "4d4147425f505f4e534500"),
  (0x5028, "524e475f5553455f48475400"),
  (0x5038, "544552525f4752414400"),
  (0x5048, "42434e5f4d5f4e534500"),
  (0x5058, "42434e5f495f47544500"),
  (0x5068, "42434e5f44454c415900"),
  (0x5078, "524e475f5553455f53504400"),
  (0x5088, "4143435f424941535f4c494d00"),
  (0x5098, "4d41475f4d41534b00"),
  (0x50a8, "4f474e5f4847545f4d41534b00"),
  (0x50b8, "5649535f564552525f4d494e00"),
  (0x50c8, "5649535f564552525f4d415800"),
  (0x50d8, "57454e435f5645525200"),
  (0x50e8, "464c4f575f55534500"),
  (0x50f8, "4852545f46494c5400"),
  (0x5108, "4d41475f45465f4c494d00"),
  (0x5118, "4753465f52554e5f4d41534b00"),
  (0x5128, "4753465f5553455f4d41534b00"),
  (0x5138, "464c4f575f4741494e5f4800"),
  (0x5148, "4753465f5253545f4d415800"),
  (0x5158, "4552525f54485245534800"),
  (0x5168, "414646494e49545900"),
  
    /- AP_Mission::var_info (libraries/AP_Mission/AP_Mission.cpp):
       {"TOTAL", 80, def_value=0.0, flags=32, idx=0, type=2}
       {"RESTART", 84, def_value=0.0, flags=0, idx=1, type=1}
       {"OPTIONS", 82, def_value=0.0, flags=0, idx=2, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x5180, "0052000000000000500000000000000000000000000000002000000200000000085200000000000054000000000000000000000000000000000001010000000010520000000000005200000000000000000000000000000000000202000000001852000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5200, "544f54414c00"),
  (0x5208, "5245535441525400"),
  (0x5210, "4f5054494f4e5300"),
  
    /- AP_Notify::var_info (libraries/AP_Notify/AP_Notify.cpp):
       {"LED_BRIGHT", 8, def_value=3.0, flags=0, idx=0, type=1}
       {"BUZZ_TYPES", 10, def_value=5.0, flags=0, idx=1, type=1}
       {"LED_OVERRIDE", 9, def_value=0.0, flags=0, idx=2, type=1}
       {"BUZZ_PIN", 13, def_value=-1.0, flags=0, idx=5, type=1}
       {"LED_TYPES", 16, def_value=123079.0, flags=0, idx=6, type=3}
       {"BUZZ_ON_LVL", 20, def_value=1.0, flags=0, idx=7, type=1}
       {"BUZZ_VOLUME", 21, def_value=100.0, flags=0, idx=8, type=1}
       {"LED_LEN", 22, def_value=1.0, flags=0, idx=9, type=1}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x5220, "405300000000000008000000000000000000404000000000000000010000000050530000000000000a000000000000000000a040000000000000010100000000605300000000000009000000000000000000000000000000000002010000000070530000000000000d00000000000000000080bf000000000000050100000000805300000000000010000000000000008063f047000000000000060300000000905300000000000014000000000000000000803f000000000000070100000000a05300000000000015000000000000000000c842000000000000080100000000b05300000000000016000000000000000000803f000000000000090100000000b853000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5340, "4c45445f42524947485400"),
  (0x5350, "42555a5a5f545950455300"),
  (0x5360, "4c45445f4f5645525249444500"),
  (0x5370, "42555a5a5f50494e00"),
  (0x5380, "4c45445f545950455300"),
  (0x5390, "42555a5a5f4f4e5f4c564c00"),
  (0x53a0, "42555a5a5f564f4c554d4500"),
  (0x53b0, "4c45445f4c454e00"),
  
    /- ParametersG2::var_info (ArduCopter/Parameters.cpp):
       {"WP_NAVALT_MIN", 0, def_value=0.0, flags=0, idx=1, type=4}
       {"DEV_OPTIONS", 8, def_value=0.0, flags=0, idx=7, type=3}
       {"FRAME_CLASS", 12, def_value=0.0, flags=0, idx=15, type=1}
       {"SERVO", 960, group_info=SRV_Channels::var_info, flags=1, idx=16, type=6}
       {"RC", 16, group_info=RC_Channels::var_info, flags=1, idx=17, type=6}
       {"FS_VIBE_ENABLE", 1648, def_value=1.0, flags=0, idx=35, type=1}
       {"FS_OPTIONS", 1652, def_value=16.0, flags=0, idx=36, type=3}
       {"AUTO_OPTIONS", 1680, def_value=0.0, flags=0, idx=40, type=3}
       {"GUID_OPTIONS", 1684, def_value=0.0, flags=0, idx=41, type=3}
       {"FS_GCS_TIMEOUT", 1688, def_value=5.0, flags=0, idx=42, type=4}
       {"RTL_OPTIONS", 1692, def_value=0.0, flags=0, idx=43, type=3}
       {"FLIGHT_OPTIONS", 1696, def_value=0.0, flags=0, idx=44, type=3}
       {"GUID_TIMEOUT", 1700, def_value=3.0, flags=0, idx=46, type=4}
       {"FS_DR_ENABLE", 1705, def_value=2.0, flags=0, idx=52, type=1}
       {"FS_DR_TIMEOUT", 1706, def_value=30.0, flags=0, idx=53, type=2}
       {"PILOT_Y_", 1656, group_info=AC_CommandModel::var_info, flags=1, idx=56, type=6}
       {"TKOFF_SLEW_TIME", 1720, def_value=2.0, flags=0, idx=57, type=4}
       {"", 0, group_info=ParametersG2::var_info2, flags=1, idx=61, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x53c0, "2056000000000000000000000000000000000000000000000000010400000000305600000000000008000000000000000000000000000000000007030000000040560000000000000c00000000000000000000000000000000000f01000000005056000000000000c003000000000000906c00000000000001001006000000005856000000000000100000000000000000730000000000000100110600000000605600000000000070060000000000000000803f000000000000230100000000705600000000000074060000000000000000804100000000000024030000000080560000000000009006000000000000000000000000000000002803000000009056000000000000940600000000000000000000000000000000290300000000a05600000000000098060000000000000000a0400000000000002a0400000000b0560000000000009c06000000000000000000000000000000002b0300000000c056000000000000a006000000000000000000000000000000002c0300000000d056000000000000a406000000000000000040400000000000002e0400000000e056000000000000a90600000000000000000040000000000000340100000000f056000000000000aa060000000000000000f04100000000000035020000000000570000000000007806000000000000687600000000000001003806000000001057000000000000b80600000000000000000040000000000000390400000000c0190000000000000000000000000000087700000000000001003d0600000000c019000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5620, "57505f4e4156414c545f4d494e00"),
  (0x5630, "4445565f4f5054494f4e5300"),
  (0x5640, "4652414d455f434c41535300"),
  (0x5650, "534552564f00"),
  (0x5658, "524300"),
  (0x5660, "46535f564942455f454e41424c4500"),
  (0x5670, "46535f4f5054494f4e5300"),
  (0x5680, "4155544f5f4f5054494f4e5300"),
  (0x5690, "475549445f4f5054494f4e5300"),
  (0x56a0, "46535f4743535f54494d454f555400"),
  (0x56b0, "52544c5f4f5054494f4e5300"),
  (0x56c0, "464c494748545f4f5054494f4e5300"),
  (0x56d0, "475549445f54494d454f555400"),
  (0x56e0, "46535f44525f454e41424c4500"),
  (0x56f0, "46535f44525f54494d454f555400"),
  (0x5700, "50494c4f545f595f00"),
  (0x5710, "544b4f46465f534c45575f54494d4500"),
  
    /- AP_Vehicle::var_info (libraries/AP_Vehicle/AP_Vehicle.cpp):
       {"FLTMODE_GCSBLOCK", 6756, def_value=0.0, flags=0, idx=20, type=3}
       {"SERIAL", 3848, group_info=AP_SerialManager::var_info, flags=1, idx=31, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x5720, "8057000000000000641a000000000000000000000000000000001403000000009857000000000000080f000000000000c87800000000000001001f0600000000a057000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5780, "464c544d4f44455f474353424c4f434b00"),
  (0x5798, "53455249414c00"),
  
    /- GCS::var_info (libraries/GCS_MAVLink/GCS.cpp):
       {"_SYSID", 160, def_value=1.0, flags=0, idx=1, type=3}
       {"_GCS_SYSID", 164, def_value=255.0, flags=0, idx=2, type=3}
       {"_GCS_SYSID_HI", 168, def_value=0.0, flags=0, idx=5, type=3}
       {"_OPTIONS", 172, def_value=0.0, flags=0, idx=3, type=2}
       {"_TELEM_DELAY", 174, def_value=0.0, flags=0, idx=4, type=1}
       {"1", 32, group_info_ptr=GCS::_chan_var_info, flags=18, idx=11, type=6}
       {"2", 40, group_info_ptr=GCS::_chan_var_info+8, flags=18, idx=12, type=6}
       {"3", 48, group_info_ptr=GCS::_chan_var_info+16, flags=18, idx=13, type=6}
       {"4", 56, group_info_ptr=GCS::_chan_var_info+24, flags=18, idx=14, type=6}
       {"5", 64, group_info_ptr=GCS::_chan_var_info+32, flags=18, idx=15, type=6}
       {"6", 72, group_info_ptr=GCS::_chan_var_info+40, flags=18, idx=16, type=6}
       {"7", 80, group_info_ptr=GCS::_chan_var_info+48, flags=18, idx=17, type=6}
       {"8", 88, group_info_ptr=GCS::_chan_var_info+56, flags=18, idx=18, type=6}
       {"9", 96, group_info_ptr=GCS::_chan_var_info+64, flags=18, idx=19, type=6}
       {"10", 104, group_info_ptr=GCS::_chan_var_info+72, flags=18, idx=20, type=6}
       {"11", 112, group_info_ptr=GCS::_chan_var_info+80, flags=18, idx=21, type=6}
       {"12", 120, group_info_ptr=GCS::_chan_var_info+88, flags=18, idx=22, type=6}
       {"13", 128, group_info_ptr=GCS::_chan_var_info+96, flags=18, idx=23, type=6}
       {"14", 136, group_info_ptr=GCS::_chan_var_info+104, flags=18, idx=24, type=6}
       {"15", 144, group_info_ptr=GCS::_chan_var_info+112, flags=18, idx=25, type=6}
       {"16", 152, group_info_ptr=GCS::_chan_var_info+120, flags=18, idx=26, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x57a8, "685a000000000000a0000000000000000000803f000000000000010300000000705a000000000000a40000000000000000007f43000000000000020300000000805a000000000000a80000000000000000000000000000000000050300000000905a000000000000ac0000000000000000000000000000000000030200000000a05a000000000000ae0000000000000000000000000000000000040100000000b05a0000000000002000000000000000588600000000000012000b0600000000b85a0000000000002800000000000000608600000000000012000c0600000000c05a0000000000003000000000000000688600000000000012000d0600000000c85a0000000000003800000000000000708600000000000012000e0600000000d05a0000000000004000000000000000788600000000000012000f0600000000d85a000000000000480000000000000080860000000000001200100600000000e05a000000000000500000000000000088860000000000001200110600000000e85a000000000000580000000000000090860000000000001200120600000000f05a000000000000600000000000000098860000000000001200130600000000f85a0000000000006800000000000000a0860000000000001200140600000000005b0000000000007000000000000000a8860000000000001200150600000000085b0000000000007800000000000000b0860000000000001200160600000000105b0000000000008000000000000000b8860000000000001200170600000000185b0000000000008800000000000000c0860000000000001200180600000000205b0000000000009000000000000000c8860000000000001200190600000000285b0000000000009800000000000000d08600000000000012001a0600000000305b000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5a68, "5f535953494400"),
  (0x5a70, "5f4743535f535953494400"),
  (0x5a80, "5f4743535f53595349445f484900"),
  (0x5a90, "5f4f5054494f4e5300"),
  (0x5aa0, "5f54454c454d5f44454c415900"),
  (0x5ab0, "3100"),
  (0x5ab8, "3200"),
  (0x5ac0, "3300"),
  (0x5ac8, "3400"),
  (0x5ad0, "3500"),
  (0x5ad8, "3600"),
  (0x5ae0, "3700"),
  (0x5ae8, "3800"),
  (0x5af0, "3900"),
  (0x5af8, "313000"),
  (0x5b00, "313100"),
  (0x5b08, "313200"),
  (0x5b10, "313300"),
  (0x5b18, "313400"),
  (0x5b20, "313500"),
  (0x5b28, "313600"),
  
    /- AC_AttitudeControl::var_info (libraries/AC_AttitudeControl/AC_AttitudeControl.cpp):
       {"RATE_FF_ENAB", 36, def_value=1.0, flags=0, idx=5, type=1}
       {"ANGLE_BOOST", 37, def_value=1.0, flags=0, idx=12, type=1}
       {"ANG_RLL_", 40, group_info=AC_P::var_info, flags=1, idx=13, type=6}
       {"ANG_PIT_", 48, group_info=AC_P::var_info, flags=1, idx=14, type=6}
       {"ANG_YAW_", 56, group_info=AC_P::var_info, flags=1, idx=15, type=6}
       {"ANG_LIM_TC", 64, def_value=1.0, flags=0, idx=16, type=4}
       {"RATE_R_MAX", 12, def_value=0.0, flags=0, idx=17, type=4}
       {"RATE_P_MAX", 16, def_value=0.0, flags=0, idx=18, type=4}
       {"RATE_Y_MAX", 20, def_value=0.0, flags=0, idx=19, type=4}
       {"INPUT_TC", 68, def_value=0.10000000149011612, flags=0, idx=20, type=4}
       {"LAND_R_MULT", 72, def_value=1.0, flags=0, idx=21, type=4}
       {"LAND_P_MULT", 76, def_value=1.0, flags=0, idx=22, type=4}
       {"LAND_Y_MULT", 80, def_value=1.0, flags=0, idx=23, type=4}
       {"ANGLE_MAX", 84, def_value=30.0, flags=0, idx=24, type=4}
       {"RATE_WPY_MAX", 8, def_value=60.0, flags=0, idx=25, type=4}
       {"ACC_Y_MAX", 32, def_value=270.0, flags=0, idx=26, type=4}
       {"ACC_R_MAX", 24, def_value=1100.0, flags=0, idx=27, type=4}
       {"ACC_P_MAX", 28, def_value=1100.0, flags=0, idx=28, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x5b38, "985d00000000000024000000000000000000803f000000000000050100000000a85d00000000000025000000000000000000803f0000000000000c0100000000b85d0000000000002800000000000000807d00000000000001000d0600000000c85d0000000000003000000000000000807d00000000000001000e0600000000d85d0000000000003800000000000000807d00000000000001000f0600000000e85d00000000000040000000000000000000803f000000000000100400000000f85d0000000000000c0000000000000000000000000000000000110400000000085e000000000000100000000000000000000000000000000000120400000000185e000000000000140000000000000000000000000000000000130400000000285e0000000000004400000000000000cdcccc3d000000000000140400000000385e00000000000048000000000000000000803f000000000000150400000000485e0000000000004c000000000000000000803f000000000000160400000000585e00000000000050000000000000000000803f000000000000170400000000685e00000000000054000000000000000000f041000000000000180400000000785e000000000000080000000000000000007042000000000000190400000000885e0000000000002000000000000000000087430000000000001a0400000000985e0000000000001800000000000000008089440000000000001b0400000000a85e0000000000001c00000000000000008089440000000000001c0400000000b85e000000000000000000000000000000000000000000000000ff0000000000"),
  (0x5d98, "524154455f46465f454e414200"),
  (0x5da8, "414e474c455f424f4f535400"),
  (0x5db8, "414e475f524c4c5f00"),
  (0x5dc8, "414e475f5049545f00"),
  (0x5dd8, "414e475f5941575f00"),
  (0x5de8, "414e475f4c494d5f544300"),
  (0x5df8, "524154455f525f4d415800"),
  (0x5e08, "524154455f505f4d415800"),
  (0x5e18, "524154455f595f4d415800"),
  (0x5e28, "494e5055545f544300"),
  (0x5e38, "4c414e445f525f4d554c5400"),
  (0x5e48, "4c414e445f505f4d554c5400"),
  (0x5e58, "4c414e445f595f4d554c5400"),
  (0x5e68, "414e474c455f4d415800"),
  (0x5e78, "524154455f5750595f4d415800"),
  (0x5e88, "4143435f595f4d415800"),
  (0x5e98, "4143435f525f4d415800"),
  (0x5ea8, "4143435f505f4d415800"),
  
    /- AC_PID::var_info (libraries/AC_PID/AC_PID.cpp):
       {"P", 0, def_value_offset=-200, flags=128, idx=0, type=4}
       {"I", 4, def_value_offset=-200, flags=128, idx=1, type=4}
       {"D", 8, def_value_offset=-200, flags=128, idx=2, type=4}
       {"FF", 12, def_value_offset=-200, flags=128, idx=4, type=4}
       {"IMAX", 16, def_value_offset=-204, flags=128, idx=5, type=4}
       {"FLTT", 24, def_value_offset=-200, flags=128, idx=9, type=4}
       {"FLTE", 28, def_value_offset=-200, flags=128, idx=10, type=4}
       {"FLTD", 32, def_value_offset=-200, flags=128, idx=11, type=4}
       {"SMAX", 36, def_value_offset=-200, flags=128, idx=12, type=4}
       {"PDMX", 20, def_value=0.0, flags=0, idx=13, type=4}
       {"D_FF", 40, def_value_offset=-176, flags=128, idx=14, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x5ec0, "4060000000000000000000000000000038ffffffffffffff80000004000000004860000000000000040000000000000038ffffffffffffff80000104000000005060000000000000080000000000000038ffffffffffffff800002040000000058600000000000000c0000000000000038ffffffffffffff80000404000000006060000000000000100000000000000034ffffffffffffff80000504000000006860000000000000180000000000000038ffffffffffffff800009040000000070600000000000001c0000000000000038ffffffffffffff80000a04000000007860000000000000200000000000000038ffffffffffffff80000b04000000008060000000000000240000000000000038ffffffffffffff80000c040000000088600000000000001400000000000000000000000000000000000d04000000009060000000000000280000000000000050ffffffffffffff80000e04000000009860000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6040, "5000"),
  (0x6048, "4900"),
  (0x6050, "4400"),
  (0x6058, "464600"),
  (0x6060, "494d415800"),
  (0x6068, "464c545400"),
  (0x6070, "464c544500"),
  (0x6078, "464c544400"),
  (0x6080, "534d415800"),
  (0x6088, "50444d5800"),
  (0x6090, "445f464600"),
  
    /- Compass_PerMotor::var_info (libraries/AP_Compass/Compass_PerMotor.cpp):
       {"_EN", 8, def_value=0.0, flags=4, idx=1, type=1}
       {"_EXP", 12, def_value=0.6499999761581421, flags=0, idx=2, type=4}
       {"1", 16, def_value=0.0, flags=0, idx=3, type=5}
       {"2", 28, def_value=0.0, flags=0, idx=4, type=5}
       {"3", 40, def_value=0.0, flags=0, idx=5, type=5}
       {"4", 52, def_value=0.0, flags=0, idx=6, type=5}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x60a0, "806100000000000008000000000000000000000000000000040001010000000088610000000000000c000000000000006666263f000000000000020400000000906100000000000010000000000000000000000000000000000003050000000098610000000000001c0000000000000000000000000000000000040500000000a061000000000000280000000000000000000000000000000000050500000000a861000000000000340000000000000000000000000000000000060500000000b061000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6180, "5f454e00"),
  (0x6188, "5f45585000"),
  (0x6190, "3100"),
  (0x6198, "3200"),
  (0x61a0, "3300"),
  (0x61a8, "3400"),
  
    /- AC_P_1D::var_info (libraries/AC_PID/AC_P_1D.cpp):
       {"P", 0, def_value_offset=-20, flags=128, idx=0, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x61b8, "f8610000000000000000000000000000ecffffffffffffff80000004000000000062000000000000000000000000000000000000000000000000ff0000000000"),
  (0x61f8, "5000"),
  
    /- AC_P_2D::var_info (libraries/AC_PID/AC_P_2D.cpp):
       {"P", 0, def_value_offset=-20, flags=128, idx=0, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6208, "48620000000000000000000000000000ecffffffffffffff80000004000000005062000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6248, "5000"),
  
    /- AC_PID_Basic::var_info (libraries/AC_PID/AC_PID_Basic.cpp):
       {"P", 0, def_value_offset=-92, flags=128, idx=0, type=4}
       {"I", 4, def_value_offset=-92, flags=128, idx=1, type=4}
       {"IMAX", 16, def_value_offset=-92, flags=128, idx=2, type=4}
       {"FLTE", 20, def_value_offset=-92, flags=128, idx=3, type=4}
       {"D", 8, def_value_offset=-92, flags=128, idx=4, type=4}
       {"FLTD", 24, def_value_offset=-92, flags=128, idx=5, type=4}
       {"FF", 12, def_value_offset=-92, flags=128, idx=6, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6258, "58630000000000000000000000000000a4ffffffffffffff800000040000000060630000000000000400000000000000a4ffffffffffffff800001040000000068630000000000001000000000000000a4ffffffffffffff800002040000000070630000000000001400000000000000a4ffffffffffffff800003040000000078630000000000000800000000000000a4ffffffffffffff800004040000000080630000000000001800000000000000a4ffffffffffffff800005040000000088630000000000000c00000000000000a4ffffffffffffff80000604000000009063000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6358, "5000"),
  (0x6360, "4900"),
  (0x6368, "494d415800"),
  (0x6370, "464c544500"),
  (0x6378, "4400"),
  (0x6380, "464c544400"),
  (0x6388, "464600"),
  
    /- AC_PID_2D::var_info (libraries/AC_PID/AC_PID_2D.cpp):
       {"P", 0, def_value_offset=-152, flags=128, idx=0, type=4}
       {"I", 4, def_value_offset=-152, flags=128, idx=1, type=4}
       {"IMAX", 16, def_value_offset=-152, flags=128, idx=2, type=4}
       {"FLTE", 20, def_value_offset=-152, flags=128, idx=3, type=4}
       {"D", 8, def_value_offset=-152, flags=128, idx=4, type=4}
       {"FLTD", 24, def_value_offset=-152, flags=128, idx=5, type=4}
       {"FF", 12, def_value_offset=-152, flags=128, idx=6, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6398, "9864000000000000000000000000000068ffffffffffffff8000000400000000a064000000000000040000000000000068ffffffffffffff8000010400000000a864000000000000100000000000000068ffffffffffffff8000020400000000b064000000000000140000000000000068ffffffffffffff8000030400000000b864000000000000080000000000000068ffffffffffffff8000040400000000c064000000000000180000000000000068ffffffffffffff8000050400000000c8640000000000000c0000000000000068ffffffffffffff8000060400000000d064000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6498, "5000"),
  (0x64a0, "4900"),
  (0x64a8, "494d415800"),
  (0x64b0, "464c544500"),
  (0x64b8, "4400"),
  (0x64c0, "464c544400"),
  (0x64c8, "464600"),
  
    /- AP_BattMonitor_Params::var_info (libraries/AP_BattMonitor/AP_BattMonitor_Params.cpp):
       {"MONITOR", 38, def_value=0.0, flags=4, idx=1, type=1}
       {"CAPACITY", 0, def_value=3300.0, flags=0, idx=7, type=3}
       {"WATT_MAX", 36, def_value=0.0, flags=1536, idx=8, type=2}
       {"SERIAL_NUM", 4, def_value=-1.0, flags=0, idx=9, type=3}
       {"LOW_TIMER", 39, def_value=10.0, flags=0, idx=10, type=1}
       {"FS_VOLTSRC", 40, def_value=0.0, flags=0, idx=11, type=1}
       {"LOW_VOLT", 8, def_value=10.5, flags=0, idx=12, type=4}
       {"LOW_MAH", 12, def_value=0.0, flags=0, idx=13, type=4}
       {"CRT_VOLT", 16, def_value=0.0, flags=0, idx=14, type=4}
       {"CRT_MAH", 20, def_value=0.0, flags=0, idx=15, type=4}
       {"FS_LOW_ACT", 41, def_value=0.0, flags=0, idx=16, type=1}
       {"FS_CRT_ACT", 42, def_value=0.0, flags=0, idx=17, type=1}
       {"ARM_VOLT", 28, def_value=0.0, flags=0, idx=18, type=4}
       {"ARM_MAH", 24, def_value=0.0, flags=0, idx=19, type=3}
       {"OPTIONS", 32, def_value=0.0, flags=0, idx=21, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x64d8, "d866000000000000260000000000000000000000000000000400010100000000e066000000000000000000000000000000404e45000000000000070300000000f06600000000000024000000000000000000000000000000000608020000000000670000000000000400000000000000000080bf00000000000009030000000010670000000000002700000000000000000020410000000000000a010000000020670000000000002800000000000000000000000000000000000b010000000030670000000000000800000000000000000028410000000000000c040000000040670000000000000c00000000000000000000000000000000000d040000000048670000000000001000000000000000000000000000000000000e040000000058670000000000001400000000000000000000000000000000000f0400000000606700000000000029000000000000000000000000000000000010010000000070670000000000002a000000000000000000000000000000000011010000000080670000000000001c000000000000000000000000000000000012040000000090670000000000001800000000000000000000000000000000001303000000009867000000000000200000000000000000000000000000000000150300000000a067000000000000000000000000000000000000000000000000ff0000000000"),
  (0x66d8, "4d4f4e49544f5200"),
  (0x66e0, "434150414349545900"),
  (0x66f0, "574154545f4d415800"),
  (0x6700, "53455249414c5f4e554d00"),
  (0x6710, "4c4f575f54494d455200"),
  (0x6720, "46535f564f4c5453524300"),
  (0x6730, "4c4f575f564f4c5400"),
  (0x6740, "4c4f575f4d414800"),
  (0x6748, "4352545f564f4c5400"),
  (0x6758, "4352545f4d414800"),
  (0x6760, "46535f4c4f575f41435400"),
  (0x6770, "46535f4352545f41435400"),
  (0x6780, "41524d5f564f4c5400"),
  (0x6790, "41524d5f4d414800"),
  (0x6798, "4f5054494f4e5300"),
  
    /- AP_RTC::var_info (libraries/AP_RTC/AP_RTC.cpp):
       {"_TYPES", 0, def_value=1.0, flags=0, idx=1, type=1}
       {"_TZ_MIN", 2, def_value=0.0, flags=0, idx=2, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x67a8, "086800000000000000000000000000000000803f00000000000001010000000010680000000000000200000000000000000000000000000000000202000000001868000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6808, "5f545950455300"),
  (0x6810, "5f545a5f4d494e00"),
  
    /- AP_CANManager::CANIface_Params::var_info (libraries/AP_CANManager/AP_CANIfaceParams.cpp):
       {"DRIVER", 0, def_value=0.0, flags=4, idx=1, type=1}
       {"BITRATE", 4, def_value=1000000.0, flags=0, idx=2, type=3}
       {"FDBITRATE", 8, def_value=8.0, flags=0, idx=3, type=3}
       {"OPTIONS", 12, def_value=0.0, flags=0, idx=4, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6820, "c068000000000000000000000000000000000000000000000400010100000000c868000000000000040000000000000000247449000000000000020300000000d068000000000000080000000000000000000041000000000000030300000000e0680000000000000c0000000000000000000000000000000000040300000000e868000000000000000000000000000000000000000000000000ff0000000000"),
  (0x68c0, "44524956455200"),
  (0x68c8, "4249545241544500"),
  (0x68d0, "46444249545241544500"),
  (0x68e0, "4f5054494f4e5300"),
  
    /- AP_CANManager::CANDriver_Params::var_info (libraries/AP_CANManager/AP_CANManager_CANDriver_Params.cpp):
       {"PROTOCOL", 0, def_value=1.0, flags=0, idx=1, type=1}
       {"PROTOCOL2", 1, def_value=0.0, flags=0, idx=6, type=1}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x68f0, "506900000000000000000000000000000000803f00000000000001010000000060690000000000000100000000000000000000000000000000000601000000007069000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6950, "50524f544f434f4c00"),
  (0x6960, "50524f544f434f4c3200"),
  
    /- AP_GPS::Params::var_info (libraries/AP_GPS/AP_GPS_Params.cpp):
       {"TYPE", 0, def_value=0.0, flags=4, idx=1, type=1}
       {"GNSS_MODE", 2, def_value=0.0, flags=0, idx=2, type=2}
       {"RATE_MS", 4, def_value=200.0, flags=0, idx=3, type=2}
       {"POS", 8, def_value=0.0, flags=0, idx=4, type=5}
       {"DELAY_MS", 20, def_value=0.0, flags=0, idx=5, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6978, "386a000000000000000000000000000000000000000000000400010100000000406a000000000000020000000000000000000000000000000000020200000000506a000000000000040000000000000000004843000000000000030200000000586a000000000000080000000000000000000000000000000000040500000000606a000000000000140000000000000000000000000000000000050200000000706a000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6a38, "5459504500"),
  (0x6a40, "474e53535f4d4f444500"),
  (0x6a50, "524154455f4d5300"),
  (0x6a58, "504f5300"),
  (0x6a60, "44454c41595f4d5300"),
  
    /- NavEKF3::var_info2 (libraries/AP_NavEKF3/AP_NavEKF3.cpp):
       {"SRC", 458, group_info=AP_NavEKF_Source::var_info, flags=1, idx=1, type=6}
       {"DRAG_BCOEF_X", 208, def_value=0.0, flags=0, idx=2, type=4}
       {"DRAG_BCOEF_Y", 212, def_value=0.0, flags=0, idx=3, type=4}
       {"DRAG_M_NSE", 204, def_value=0.5, flags=0, idx=4, type=4}
       {"DRAG_MCOEF", 216, def_value=0.0, flags=0, idx=5, type=4}
       {"OGNM_TEST_SF", 224, def_value=2.0, flags=0, idx=6, type=4}
       {"GND_EFF_DZ", 228, def_value=4.0, flags=0, idx=7, type=4}
       {"PRIMARY", 232, def_value=0.0, flags=0, idx=8, type=1}
       {"LOG_LEVEL", 233, def_value=0.0, flags=0, idx=9, type=1}
       {"GPS_VACC_MAX", 236, def_value=0.0, flags=0, idx=10, type=4}
       {"OPTIONS", 240, def_value=0.0, flags=0, idx=11, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6a78, "f86b000000000000ca01000000000000d07d0000000000000100010600000000006c000000000000d00000000000000000000000000000000000020400000000106c000000000000d40000000000000000000000000000000000030400000000206c000000000000cc000000000000000000003f000000000000040400000000306c000000000000d80000000000000000000000000000000000050400000000406c000000000000e00000000000000000000040000000000000060400000000506c000000000000e40000000000000000008040000000000000070400000000606c000000000000e80000000000000000000000000000000000080100000000686c000000000000e90000000000000000000000000000000000090100000000786c000000000000ec00000000000000000000000000000000000a0400000000886c000000000000f000000000000000000000000000000000000b03000000007851000000000000000000000000000000000000000000000000ff0000000000"),
  (0x6bf8, "53524300"),
  (0x6c00, "445241475f42434f45465f5800"),
  (0x6c10, "445241475f42434f45465f5900"),
  (0x6c20, "445241475f4d5f4e534500"),
  (0x6c30, "445241475f4d434f454600"),
  (0x6c40, "4f474e4d5f544553545f534600"),
  (0x6c50, "474e445f4546465f445a00"),
  (0x6c60, "5052494d41525900"),
  (0x6c68, "4c4f475f4c4556454c00"),
  (0x6c78, "4750535f564143435f4d415800"),
  (0x6c88, "4f5054494f4e5300"),
  
    /- SRV_Channels::var_info (libraries/SRV_Channel/SRV_Channels.cpp):
       {"1_", 4, group_info=SRV_Channel::var_info, flags=1, idx=1, type=6}
       {"2_", 24, group_info=SRV_Channel::var_info, flags=1, idx=2, type=6}
       {"3_", 44, group_info=SRV_Channel::var_info, flags=1, idx=3, type=6}
       {"4_", 64, group_info=SRV_Channel::var_info, flags=1, idx=4, type=6}
       {"5_", 84, group_info=SRV_Channel::var_info, flags=1, idx=5, type=6}
       {"6_", 104, group_info=SRV_Channel::var_info, flags=1, idx=6, type=6}
       {"7_", 124, group_info=SRV_Channel::var_info, flags=1, idx=7, type=6}
       {"8_", 144, group_info=SRV_Channel::var_info, flags=1, idx=8, type=6}
       {"9_", 164, group_info=SRV_Channel::var_info, flags=1, idx=9, type=6}
       {"10_", 184, group_info=SRV_Channel::var_info, flags=1, idx=10, type=6}
       {"11_", 204, group_info=SRV_Channel::var_info, flags=1, idx=11, type=6}
       {"12_", 224, group_info=SRV_Channel::var_info, flags=1, idx=12, type=6}
       {"13_", 244, group_info=SRV_Channel::var_info, flags=1, idx=13, type=6}
       {"14_", 264, group_info=SRV_Channel::var_info, flags=1, idx=14, type=6}
       {"15_", 284, group_info=SRV_Channel::var_info, flags=1, idx=15, type=6}
       {"16_", 304, group_info=SRV_Channel::var_info, flags=1, idx=16, type=6}
       {"_AUTO_TRIM", 644, def_value=0.0, flags=1024, idx=17, type=1}
       {"_RATE", 646, def_value=50.0, flags=0, idx=18, type=2}
       {"_DSHOT_RATE", 648, def_value=0.0, flags=0, idx=23, type=1}
       {"_DSHOT_ESC", 649, def_value=0.0, flags=0, idx=24, type=1}
       {"_GPIO_MASK", 652, def_value=0.0, flags=0, idx=26, type=3}
       {"_RC_FS_MSK", 656, def_value=0.0, flags=0, idx=44, type=3}
       {"_32_ENABLE", 660, def_value=0.0, flags=4, idx=43, type=1}
       {"17_", 324, group_info=SRV_Channel::var_info, flags=1, idx=27, type=6}
       {"18_", 344, group_info=SRV_Channel::var_info, flags=1, idx=28, type=6}
       {"19_", 364, group_info=SRV_Channel::var_info, flags=1, idx=29, type=6}
       {"20_", 384, group_info=SRV_Channel::var_info, flags=1, idx=30, type=6}
       {"21_", 404, group_info=SRV_Channel::var_info, flags=1, idx=31, type=6}
       {"22_", 424, group_info=SRV_Channel::var_info, flags=1, idx=32, type=6}
       {"23_", 444, group_info=SRV_Channel::var_info, flags=1, idx=33, type=6}
       {"24_", 464, group_info=SRV_Channel::var_info, flags=1, idx=34, type=6}
       {"25_", 484, group_info=SRV_Channel::var_info, flags=1, idx=35, type=6}
       {"26_", 504, group_info=SRV_Channel::var_info, flags=1, idx=36, type=6}
       {"27_", 524, group_info=SRV_Channel::var_info, flags=1, idx=37, type=6}
       {"28_", 544, group_info=SRV_Channel::var_info, flags=1, idx=38, type=6}
       {"29_", 564, group_info=SRV_Channel::var_info, flags=1, idx=39, type=6}
       {"30_", 584, group_info=SRV_Channel::var_info, flags=1, idx=40, type=6}
       {"31_", 604, group_info=SRV_Channel::var_info, flags=1, idx=41, type=6}
       {"32_", 624, group_info=SRV_Channel::var_info, flags=1, idx=42, type=6}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x6c90, "90710000000000000400000000000000808000000000000001000106000000009871000000000000180000000000000080800000000000000100020600000000a0710000000000002c0000000000000080800000000000000100030600000000a871000000000000400000000000000080800000000000000100040600000000b071000000000000540000000000000080800000000000000100050600000000b871000000000000680000000000000080800000000000000100060600000000c0710000000000007c0000000000000080800000000000000100070600000000c871000000000000900000000000000080800000000000000100080600000000d071000000000000a40000000000000080800000000000000100090600000000d871000000000000b800000000000000808000000000000001000a0600000000e071000000000000cc00000000000000808000000000000001000b0600000000e871000000000000e000000000000000808000000000000001000c0600000000f071000000000000f400000000000000808000000000000001000d0600000000f8710000000000000801000000000000808000000000000001000e060000000000720000000000001c01000000000000808000000000000001000f06000000000872000000000000300100000000000080800000000000000100100600000000107200000000000084020000000000000000000000000000000411010000000020720000000000008602000000000000000048420000000000001202000000002872000000000000880200000000000000000000000000000000170100000000387200000000000089020000000000000000000000000000000018010000000048720000000000008c02000000000000000000000000000000001a030000000058720000000000009002000000000000000000000000000000002c030000000068720000000000009402000000000000000000000000000004002b010000000078720000000000004401000000000000808000000000000001001b060000000080720000000000005801000000000000808000000000000001001c060000000088720000000000006c01000000000000808000000000000001001d060000000090720000000000008001000000000000808000000000000001001e060000000098720000000000009401000000000000808000000000000001001f0600000000a072000000000000a80100000000000080800000000000000100200600000000a872000000000000bc0100000000000080800000000000000100210600000000b072000000000000d00100000000000080800000000000000100220600000000b872000000000000e40100000000000080800000000000000100230600000000c072000000000000f80100000000000080800000000000000100240600000000c8720000000000000c0200000000000080800000000000000100250600000000d072000000000000200200000000000080800000000000000100260600000000d872000000000000340200000000000080800000000000000100270600000000e072000000000000480200000000000080800000000000000100280600000000e8720000000000005c0200000000000080800000000000000100290600000000f0720000000000007002000000000000808000000000000001002a0600000000f872000000000000000000000000000000000000000000000000ff0000000000"),
  (0x7190, "315f00"),
  (0x7198, "325f00"),
  (0x71a0, "335f00"),
  (0x71a8, "345f00"),
  (0x71b0, "355f00"),
  (0x71b8, "365f00"),
  (0x71c0, "375f00"),
  (0x71c8, "385f00"),
  (0x71d0, "395f00"),
  (0x71d8, "31305f00"),
  (0x71e0, "31315f00"),
  (0x71e8, "31325f00"),
  (0x71f0, "31335f00"),
  (0x71f8, "31345f00"),
  (0x7200, "31355f00"),
  (0x7208, "31365f00"),
  (0x7210, "5f4155544f5f5452494d00"),
  (0x7220, "5f5241544500"),
  (0x7228, "5f4453484f545f5241544500"),
  (0x7238, "5f4453484f545f45534300"),
  (0x7248, "5f4750494f5f4d41534b00"),
  (0x7258, "5f52435f46535f4d534b00"),
  (0x7268, "5f33325f454e41424c4500"),
  (0x7278, "31375f00"),
  (0x7280, "31385f00"),
  (0x7288, "31395f00"),
  (0x7290, "32305f00"),
  (0x7298, "32315f00"),
  (0x72a0, "32325f00"),
  (0x72a8, "32335f00"),
  (0x72b0, "32345f00"),
  (0x72b8, "32355f00"),
  (0x72c0, "32365f00"),
  (0x72c8, "32375f00"),
  (0x72d0, "32385f00"),
  (0x72d8, "32395f00"),
  (0x72e0, "33305f00"),
  (0x72e8, "33315f00"),
  (0x72f0, "33325f00"),
  
    /- RC_Channels::var_info (ArduCopter/RC_Channel_Copter.cpp):
       {"1_", 48, group_info=RC_Channel::var_info, flags=1, idx=1, type=6}
       {"2_", 104, group_info=RC_Channel::var_info, flags=1, idx=2, type=6}
       {"3_", 160, group_info=RC_Channel::var_info, flags=1, idx=3, type=6}
       {"4_", 216, group_info=RC_Channel::var_info, flags=1, idx=4, type=6}
       {"5_", 272, group_info=RC_Channel::var_info, flags=1, idx=5, type=6}
       {"6_", 328, group_info=RC_Channel::var_info, flags=1, idx=6, type=6}
       {"7_", 384, group_info=RC_Channel::var_info, flags=1, idx=7, type=6}
       {"8_", 440, group_info=RC_Channel::var_info, flags=1, idx=8, type=6}
       {"9_", 496, group_info=RC_Channel::var_info, flags=1, idx=9, type=6}
       {"10_", 552, group_info=RC_Channel::var_info, flags=1, idx=10, type=6}
       {"11_", 608, group_info=RC_Channel::var_info, flags=1, idx=11, type=6}
       {"12_", 664, group_info=RC_Channel::var_info, flags=1, idx=12, type=6}
       {"13_", 720, group_info=RC_Channel::var_info, flags=1, idx=13, type=6}
       {"14_", 776, group_info=RC_Channel::var_info, flags=1, idx=14, type=6}
       {"15_", 832, group_info=RC_Channel::var_info, flags=1, idx=15, type=6}
       {"16_", 888, group_info=RC_Channel::var_info, flags=1, idx=16, type=6}
       {"_OVERRIDE_TIME", 20, def_value=3.0, flags=0, idx=32, type=4}
       {"_OPTIONS", 24, def_value=32.0, flags=0, idx=33, type=3}
       {"_PROTOCOLS", 28, def_value=1.0, flags=0, idx=34, type=3}
       {"_FS_TIMEOUT", 32, def_value=1.0, flags=0, idx=35, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x7300, "a075000000000000300000000000000080810000000000000100010600000000a875000000000000680000000000000080810000000000000100020600000000b075000000000000a00000000000000080810000000000000100030600000000b875000000000000d80000000000000080810000000000000100040600000000c075000000000000100100000000000080810000000000000100050600000000c875000000000000480100000000000080810000000000000100060600000000d075000000000000800100000000000080810000000000000100070600000000d875000000000000b80100000000000080810000000000000100080600000000e075000000000000f00100000000000080810000000000000100090600000000e8750000000000002802000000000000808100000000000001000a0600000000f0750000000000006002000000000000808100000000000001000b0600000000f8750000000000009802000000000000808100000000000001000c06000000000076000000000000d002000000000000808100000000000001000d060000000008760000000000000803000000000000808100000000000001000e060000000010760000000000004003000000000000808100000000000001000f060000000018760000000000007803000000000000808100000000000001001006000000002076000000000000140000000000000000004040000000000000200400000000307600000000000018000000000000000000004200000000000021030000000040760000000000001c000000000000000000803f000000000000220300000000507600000000000020000000000000000000803f0000000000002304000000006076000000000000000000000000000000000000000000000000ff0000000000"),
  (0x75a0, "315f00"),
  (0x75a8, "325f00"),
  (0x75b0, "335f00"),
  (0x75b8, "345f00"),
  (0x75c0, "355f00"),
  (0x75c8, "365f00"),
  (0x75d0, "375f00"),
  (0x75d8, "385f00"),
  (0x75e0, "395f00"),
  (0x75e8, "31305f00"),
  (0x75f0, "31315f00"),
  (0x75f8, "31325f00"),
  (0x7600, "31335f00"),
  (0x7608, "31345f00"),
  (0x7610, "31355f00"),
  (0x7618, "31365f00"),
  (0x7620, "5f4f564552524944455f54494d4500"),
  (0x7630, "5f4f5054494f4e5300"),
  (0x7640, "5f50524f544f434f4c5300"),
  (0x7650, "5f46535f54494d454f555400"),
  
    /- AC_CommandModel::var_info (libraries/AC_AttitudeControl/AC_CommandModel.cpp):
       {"RATE", 4, def_value_offset=-12, flags=128, idx=1, type=4}
       {"EXPO", 8, def_value_offset=-12, flags=128, idx=2, type=4}
       {"RATE_TC", 0, def_value_offset=-12, flags=128, idx=3, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x7668, "e8760000000000000400000000000000f4ffffffffffffff8000010400000000f0760000000000000800000000000000f4ffffffffffffff8000020400000000f8760000000000000000000000000000f4ffffffffffffff80000304000000000077000000000000000000000000000000000000000000000000ff0000000000"),
  (0x76e8, "5241544500"),
  (0x76f0, "4558504f00"),
  (0x76f8, "524154455f544300"),
  
    /- ParametersG2::var_info2 (ArduCopter/Parameters.cpp):
       {"SURFTRAK_TC", 1708, def_value=1.0, flags=0, idx=5, type=4}
       {"TKOFF_THR_MAX", 1724, def_value=0.8999999761581421, flags=0, idx=6, type=4}
       {"FS_EKF_FILT", 1728, def_value=5.0, flags=0, idx=8, type=4}
       {"RTL_", 1736, group_info=ModeRTL::var_info, flags=2, idx=14, type=6}
       {"LAND_", 1744, group_info=ModeLand::var_info, flags=2, idx=15, type=6}
       {"PILOT_ACC_Z", 1632, def_value=2.5, flags=0, idx=17, type=4}
       {"PILOT_SPD_UP", 1636, def_value=2.5, flags=0, idx=18, type=4}
       {"PILOT_SPD_DN", 1640, def_value=0.0, flags=0, idx=19, type=4}
       {"PILOT_TKO_ALT_M", 1644, def_value=0.0, flags=0, idx=20, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x7708, "4878000000000000ac060000000000000000803f0000000000000504000000005878000000000000bc060000000000006666663f0000000000000604000000006878000000000000c0060000000000000000a0400000000000000804000000007878000000000000c806000000000000a08200000000000002000e06000000008078000000000000d006000000000000808300000000000002000f060000000088780000000000006006000000000000000020400000000000001104000000009878000000000000640600000000000000002040000000000000120400000000a878000000000000680600000000000000000000000000000000130400000000b8780000000000006c0600000000000000000000000000000000140400000000c019000000000000000000000000000000000000000000000000ff0000000000"),
  (0x7848, "535552465452414b5f544300"),
  (0x7858, "544b4f46465f5448525f4d415800"),
  (0x7868, "46535f454b465f46494c5400"),
  (0x7878, "52544c5f00"),
  (0x7880, "4c414e445f00"),
  (0x7888, "50494c4f545f4143435f5a00"),
  (0x7898, "50494c4f545f5350445f555000"),
  (0x78a8, "50494c4f545f5350445f444e00"),
  (0x78b8, "50494c4f545f544b4f5f414c545f4d00"),
  
    /- AP_SerialManager::var_info (libraries/AP_SerialManager/AP_SerialManager.cpp):
       {"0_BAUD", 16, def_value=115.0, flags=0, idx=0, type=3}
       {"0_PROTOCOL", 24, def_value=2.0, flags=0, idx=11, type=1}
       {"1_PROTOCOL", 36, def_value=2.0, flags=0, idx=1, type=1}
       {"1_BAUD", 28, def_value=57.0, flags=0, idx=2, type=3}
       {"2_PROTOCOL", 48, def_value=2.0, flags=0, idx=3, type=1}
       {"2_BAUD", 40, def_value=57.0, flags=0, idx=4, type=3}
       {"3_PROTOCOL", 60, def_value=5.0, flags=0, idx=5, type=1}
       {"3_BAUD", 52, def_value=230.0, flags=0, idx=6, type=3}
       {"4_PROTOCOL", 72, def_value=5.0, flags=0, idx=7, type=1}
       {"4_BAUD", 64, def_value=230.0, flags=0, idx=8, type=3}
       {"5_PROTOCOL", 84, def_value=-1.0, flags=0, idx=9, type=1}
       {"5_BAUD", 76, def_value=57.0, flags=0, idx=10, type=3}
       {"6_PROTOCOL", 96, def_value=-1.0, flags=0, idx=12, type=1}
       {"6_BAUD", 88, def_value=57.0, flags=0, idx=13, type=3}
       {"1_OPTIONS", 32, def_value=0.0, flags=0, idx=14, type=3}
       {"2_OPTIONS", 44, def_value=0.0, flags=0, idx=15, type=3}
       {"3_OPTIONS", 56, def_value=0.0, flags=0, idx=16, type=3}
       {"4_OPTIONS", 68, def_value=0.0, flags=0, idx=17, type=3}
       {"5_OPTIONS", 80, def_value=0.0, flags=0, idx=18, type=3}
       {"6_OPTIONS", 92, def_value=0.0, flags=0, idx=19, type=3}
       {"_PASS1", 136, def_value=0.0, flags=0, idx=20, type=1}
       {"_PASS2", 137, def_value=-1.0, flags=0, idx=21, type=1}
       {"_PASSTIMO", 138, def_value=15.0, flags=0, idx=22, type=1}
       {"7_PROTOCOL", 108, def_value=-1.0, flags=0, idx=23, type=1}
       {"7_BAUD", 100, def_value=57.0, flags=0, idx=24, type=3}
       {"7_OPTIONS", 104, def_value=0.0, flags=0, idx=25, type=3}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x78c8, "287c00000000000010000000000000000000e642000000000000000300000000307c0000000000001800000000000000000000400000000000000b0100000000407c000000000000240000000000000000000040000000000000010100000000507c0000000000001c0000000000000000006442000000000000020300000000587c000000000000300000000000000000000040000000000000030100000000687c000000000000280000000000000000006442000000000000040300000000707c0000000000003c000000000000000000a040000000000000050100000000807c000000000000340000000000000000006643000000000000060300000000887c00000000000048000000000000000000a040000000000000070100000000987c000000000000400000000000000000006643000000000000080300000000a07c0000000000005400000000000000000080bf000000000000090100000000b07c0000000000004c00000000000000000064420000000000000a0300000000b87c0000000000006000000000000000000080bf0000000000000c0100000000c87c0000000000005800000000000000000064420000000000000d0300000000d07c0000000000002000000000000000000000000000000000000e0300000000e07c0000000000002c00000000000000000000000000000000000f0300000000f07c000000000000380000000000000000000000000000000000100300000000007d000000000000440000000000000000000000000000000000110300000000107d000000000000500000000000000000000000000000000000120300000000207d0000000000005c0000000000000000000000000000000000130300000000307d000000000000880000000000000000000000000000000000140100000000387d0000000000008900000000000000000080bf000000000000150100000000407d0000000000008a0000000000000000007041000000000000160100000000507d0000000000006c00000000000000000080bf000000000000170100000000607d000000000000640000000000000000006442000000000000180300000000687d000000000000680000000000000000000000000000000000190300000000787d000000000000000000000000000000000000000000000000ff0000000000"),
  (0x7c28, "305f4241554400"),
  (0x7c30, "305f50524f544f434f4c00"),
  (0x7c40, "315f50524f544f434f4c00"),
  (0x7c50, "315f4241554400"),
  (0x7c58, "325f50524f544f434f4c00"),
  (0x7c68, "325f4241554400"),
  (0x7c70, "335f50524f544f434f4c00"),
  (0x7c80, "335f4241554400"),
  (0x7c88, "345f50524f544f434f4c00"),
  (0x7c98, "345f4241554400"),
  (0x7ca0, "355f50524f544f434f4c00"),
  (0x7cb0, "355f4241554400"),
  (0x7cb8, "365f50524f544f434f4c00"),
  (0x7cc8, "365f4241554400"),
  (0x7cd0, "315f4f5054494f4e5300"),
  (0x7ce0, "325f4f5054494f4e5300"),
  (0x7cf0, "335f4f5054494f4e5300"),
  (0x7d00, "345f4f5054494f4e5300"),
  (0x7d10, "355f4f5054494f4e5300"),
  (0x7d20, "365f4f5054494f4e5300"),
  (0x7d30, "5f504153533100"),
  (0x7d38, "5f504153533200"),
  (0x7d40, "5f5041535354494d4f00"),
  (0x7d50, "375f50524f544f434f4c00"),
  (0x7d60, "375f4241554400"),
  (0x7d68, "375f4f5054494f4e5300"),
  
    /- AC_P::var_info (libraries/AC_PID/AC_P.cpp):
       {"P", 0, def_value_offset=-4, flags=128, idx=0, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x7d80, "c07d0000000000000000000000000000fcffffffffffffff8000000400000000c87d000000000000000000000000000000000000000000000000ff0000000000"),
  (0x7dc0, "5000"),
  
    /- AP_NavEKF_Source::var_info (libraries/AP_NavEKF/AP_NavEKF_Source.cpp):
       {"1_POSXY", 0, def_value=3.0, flags=0, idx=1, type=1}
       {"1_VELXY", 1, def_value=3.0, flags=0, idx=2, type=1}
       {"1_POSZ", 2, def_value=1.0, flags=0, idx=3, type=1}
       {"1_VELZ", 3, def_value=3.0, flags=0, idx=4, type=1}
       {"1_YAW", 4, def_value=1.0, flags=0, idx=5, type=1}
       {"2_POSXY", 5, def_value=0.0, flags=0, idx=6, type=1}
       {"2_VELXY", 6, def_value=0.0, flags=0, idx=7, type=1}
       {"2_POSZ", 7, def_value=1.0, flags=0, idx=8, type=1}
       {"2_VELZ", 8, def_value=0.0, flags=0, idx=9, type=1}
       {"2_YAW", 9, def_value=0.0, flags=0, idx=10, type=1}
       {"3_POSXY", 10, def_value=0.0, flags=0, idx=11, type=1}
       {"3_VELXY", 11, def_value=0.0, flags=0, idx=12, type=1}
       {"3_POSZ", 12, def_value=1.0, flags=0, idx=13, type=1}
       {"3_VELZ", 13, def_value=0.0, flags=0, idx=14, type=1}
       {"3_YAW", 14, def_value=0.0, flags=0, idx=15, type=1}
       {"_OPTIONS", 16, def_value=0.0, flags=0, idx=16, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x7dd0, "f07f000000000000000000000000000000004040000000000000010100000000f87f000000000000010000000000000000004040000000000000020100000000008000000000000002000000000000000000803f0000000000000301000000000880000000000000030000000000000000004040000000000000040100000000108000000000000004000000000000000000803f00000000000005010000000018800000000000000500000000000000000000000000000000000601000000002080000000000000060000000000000000000000000000000000070100000000288000000000000007000000000000000000803f000000000000080100000000308000000000000008000000000000000000000000000000000009010000000038800000000000000900000000000000000000000000000000000a010000000040800000000000000a00000000000000000000000000000000000b010000000048800000000000000b00000000000000000000000000000000000c010000000050800000000000000c000000000000000000803f0000000000000d010000000058800000000000000d00000000000000000000000000000000000e010000000060800000000000000e00000000000000000000000000000000000f010000000068800000000000001000000000000000000000000000000000001002000000007880000000000000000000000000000000000000000000000000ff0000000000"),
  (0x7ff0, "315f504f53585900"),
  (0x7ff8, "315f56454c585900"),
  (0x8000, "315f504f535a00"),
  (0x8008, "315f56454c5a00"),
  (0x8010, "315f59415700"),
  (0x8018, "325f504f53585900"),
  (0x8020, "325f56454c585900"),
  (0x8028, "325f504f535a00"),
  (0x8030, "325f56454c5a00"),
  (0x8038, "325f59415700"),
  (0x8040, "335f504f53585900"),
  (0x8048, "335f56454c585900"),
  (0x8050, "335f504f535a00"),
  (0x8058, "335f56454c5a00"),
  (0x8060, "335f59415700"),
  (0x8068, "5f4f5054494f4e5300"),
  
    /- SRV_Channel::var_info (libraries/SRV_Channel/SRV_Channel.cpp):
       {"MIN", 0, def_value=1100.0, flags=0, idx=1, type=2}
       {"MAX", 2, def_value=1900.0, flags=0, idx=2, type=2}
       {"TRIM", 4, def_value=1500.0, flags=0, idx=3, type=2}
       {"REVERSED", 6, def_value=0.0, flags=0, idx=4, type=1}
       {"FUNCTION", 8, def_value=0.0, flags=0, idx=5, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x8080, "4081000000000000000000000000000000808944000000000000010200000000488100000000000002000000000000000080ed44000000000000020200000000508100000000000004000000000000000080bb44000000000000030200000000588100000000000006000000000000000000000000000000000004010000000068810000000000000800000000000000000000000000000000000502000000007881000000000000000000000000000000000000000000000000ff0000000000"),
  (0x8140, "4d494e00"),
  (0x8148, "4d415800"),
  (0x8150, "5452494d00"),
  (0x8158, "524556455253454400"),
  (0x8168, "46554e4354494f4e00"),
  
    /- RC_Channel::var_info (libraries/RC_Channel/RC_Channel.cpp):
       {"MIN", 18, def_value=1100.0, flags=0, idx=1, type=2}
       {"TRIM", 20, def_value=1500.0, flags=0, idx=2, type=2}
       {"MAX", 22, def_value=1900.0, flags=0, idx=3, type=2}
       {"REVERSED", 24, def_value=0.0, flags=0, idx=4, type=1}
       {"DZ", 26, def_value=0.0, flags=0, idx=5, type=2}
       {"OPTION", 8, def_value=0.0, flags=0, idx=6, type=2}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x8180, "6082000000000000120000000000000000808944000000000000010200000000688200000000000014000000000000000080bb44000000000000020200000000708200000000000016000000000000000080ed44000000000000030200000000788200000000000018000000000000000000000000000000000004010000000088820000000000001a000000000000000000000000000000000005020000000090820000000000000800000000000000000000000000000000000602000000009882000000000000000000000000000000000000000000000000ff0000000000"),
  (0x8260, "4d494e00"),
  (0x8268, "5452494d00"),
  (0x8270, "4d415800"),
  (0x8278, "524556455253454400"),
  (0x8288, "445a00"),
  (0x8290, "4f5054494f4e00"),
  
    /- ModeRTL::var_info (ArduCopter/mode_rtl.cpp):
       {"ALT_M", 112, def_value=15.0, flags=0, idx=1, type=4}
       {"ALT_FINAL_M", 120, def_value=0.0, flags=0, idx=2, type=4}
       {"CLIMB_MIN_M", 124, def_value=0.0, flags=0, idx=3, type=4}
       {"SPEED_MS", 116, def_value=0.0, flags=0, idx=4, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x82a0, "4083000000000000700000000000000000007041000000000000010400000000488300000000000078000000000000000000000000000000000002040000000058830000000000007c000000000000000000000000000000000003040000000068830000000000007400000000000000000000000000000000000404000000007883000000000000000000000000000000000000000000000000ff0000000000"),
  (0x8340, "414c545f4d00"),
  (0x8348, "414c545f46494e414c5f4d00"),
  (0x8358, "434c494d425f4d494e5f4d00"),
  (0x8368, "53504545445f4d5300"),
  
    /- ModeLand::var_info (ArduCopter/mode_land.cpp):
       {"SPD_MS", 116, def_value=0.5, flags=0, idx=1, type=4}
       {"SPD_HIGH_MS", 120, def_value=0.0, flags=0, idx=2, type=4}
       {"ALT_LOW_M", 124, def_value=10.0, flags=0, idx=3, type=4}
       {"", 0, def_value=0.0, flags=0, idx=255, type=0} -/
    (0x8380, "008400000000000074000000000000000000003f000000000000010400000000088400000000000078000000000000000000000000000000000002040000000018840000000000007c00000000000000000020410000000000000304000000002884000000000000000000000000000000000000000000000000ff0000000000"),
  (0x8400, "5350445f4d5300"),
  (0x8408, "5350445f484947485f4d5300"),
  (0x8418, "414c545f4c4f575f4d00"),
  (0xbbc8, "0000000000000006030000000006760902000000760f5a0001000000d00f300000000000001000050200000000152c01010000002c160001030000002c17540804000000801f400005000000c01f380000000000002000050200000000252c01010000002c260001030000002c27541406000000803b0004"),
  (0xbc50, "0700000001"),
  (0xbc70, "30be0000000000002c000000000000000000000000000000000001020000000040be0000000000002e000000000000000000000000000000000002020000000050be00000000000030000000000000000000000000000000000003020000000060be00000000000032000000000000000000000000000000000004020000000070be00000000000034000000000000000000000000000000000005020000000080be00000000000036000000000000000000000000000000000006020000000088be00000000000038000000000000000000000000000000000007020000000090be0000000000003a000000000000000000000000000000000008020000000098be0000000000003c0000000000000000000000000000000000090200000000a0be0000000000003e00000000000000000000000000000000000a0200000000a8be000000000000440000000000000000000000000000000000140200000000b8be000000000000460000000000000000000000000000004000150100000000c8be000000000000400000000000000000000000000000002000160300000000d0be000000000000000000000000000000000000000000000000ff0000000000"),
  (0xbe30, "5f5241575f53454e5300"),
  (0xbe40, "5f4558545f5354415400"),
  (0xbe50, "5f52435f4348414e00"),
  (0xbe60, "5f5241575f4354524c00"),
  (0xbe70, "5f504f534954494f4e00"),
  (0xbe80, "5f45585452413100"),
  (0xbe88, "5f45585452413200"),
  (0xbe90, "5f45585452413300"),
  (0xbe98, "5f504152414d5300"),
  (0xbea0, "5f4144534200"),
  (0xbea8, "5f4f5054494f4e5300"),
  (0xbeb8, "5f4f5054494f4e53434e5600"),
  (0xbec8, "5f444556494400"),
  (0xbf60, "01"),
  (0xbfc0, "1c000000000000000200000000000000987800000000000030000000000000000200000000000000887800000000000040000000000000000400000000000000b87800000000000006000000180000000200000000000000a878000000000000"),
  (0xc020, "00900000000000005000007f00000000e0c30000000000000000000000000000d8860000000000006000007f0000000000c40000000000000000000000000000d8860000000000007000007f0000000028c40000000000000000000000000000d8860000000000008000007f0000000048c40000000000000000000000000000d8860000000000009000007f0000000060c40000000000000000000000000000d886000000000000a000007f0000000078c40000000000000000000000000000d886000000000000b000007f0000000098c40000000000000000000000000000d886000000000000c000007f00000000b8c40000000000000000000000000000d886000000000000d000007f00000000d8c40000000000000000000000000000d886000000000000e000007f0000000008c50000000000000000000000000000d886000000000000f000007f0000000038c500000000000000007a4382000300d8860000000000000001007f0000000048c5000000000000000048424b00060058880000000000001001007f0000000060c500000000000000004842c8000900d8860000000000002001007f0000000070c50000000000000000204178000f00a0a10000000000003001007f0000000090c50000000000000000204132001200d8860000000000004001007f00000000b0c50000000000000000204132001b00d8860000000000005001007f00000000d0c50000000000000000204164002a00d8860000000000006001007f00000000e8c50000000000000000484264002d00d8860000000000007001007f0000000000c60000000000000000c8425a003000d8860000000000008001007f0000000020c6000000000000000040404b003900d8860000000000009001007f0000000038c60000000000000000803f64005100d886000000000000a001007f0000000050c6000000000000000020414b005400d886000000000000b001007f0000000068c60000000000000000204132005700d886000000000000c001007f0000000080c60000000000000000204132005a00d886000000000000d001007f0000000098c60000000000000000484232005b00d886000000000000e001007f00000000b0c60000000000000000c8424b006000d886000000000000f001007f00000000c8c60000000000000000204132006300a0a90000000000000002007f00000000e8c60000000000000000c843b4006600a0a90000000000001002007f0000000000c70000000000000000c8432602690000900000000000002002007f0000000018c70000000000000000c84332007b00"),
  (0xc3e0, "41505f496e65727469616c53656e736f723a3a7570646174652a00"),
  (0xc400, "436f707465723a3a72756e5f726174655f636f6e74726f6c6c65725f6d61696e2a00"),
  (0xc428, "436f707465723a3a6d6f746f72735f6f75747075745f6d61696e2a00"),
  (0xc448, "436f707465723a3a726561645f414852532a00"),
  (0xc460, "436f707465723a3a726561645f696e65727469612a00"),
  (0xc478, "436f707465723a3a636865636b5f656b665f72657365742a00"),
  (0xc498, "436f707465723a3a7570646174655f666c696768745f6d6f64652a00"),
  (0xc4b8, "436f707465723a3a7570646174655f686f6d655f66726f6d5f454b462a00"),
  (0xc4d8, "436f707465723a3a7570646174655f6c616e645f616e645f63726173685f6465746563746f72732a00"),
  (0xc508, "436f707465723a3a7570646174655f72616e676566696e6465725f7465727261696e5f6f66667365742a00"),
  (0xc538, "436f707465723a3a72635f6c6f6f7000"),
  (0xc548, "436f707465723a3a7468726f74746c655f6c6f6f7000"),
  (0xc560, "41505f4750533a3a75706461746500"),
  (0xc570, "436f707465723a3a7570646174655f626174745f636f6d7061737300"),
  (0xc590, "52435f4368616e6e656c733a3a726561645f6175785f616c6c00"),
  (0xc5b0, "436f707465723a3a6175746f5f64697361726d5f636865636b00"),
  (0xc5d0, "436f707465723a3a7570646174655f616c74697475646500"),
  (0xc5e8, "436f707465723a3a72756e5f6e61765f7570646174657300"),
  (0xc600, "436f707465723a3a7570646174655f7468726f74746c655f686f76657200"),
  (0xc620, "436f707465723a3a74687265655f687a5f6c6f6f7000"),
  (0xc638, "436f707465723a3a6f6e655f687a5f6c6f6f7000"),
  (0xc650, "436f707465723a3a656b665f636865636b00"),
  (0xc668, "436f707465723a3a636865636b5f766962726174696f6e00"),
  (0xc680, "436f707465723a3a677073676c697463685f636865636b00"),
  (0xc698, "436f707465723a3a74616b656f66665f636865636b00"),
  (0xc6b0, "436f707465723a3a7374616e6462795f75706461746500"),
  (0xc6c8, "436f707465723a3a6c6f73745f76656869636c655f636865636b00"),
  (0xc6e8, "4743533a3a7570646174655f7265636569766500"),
  (0xc700, "4743533a3a7570646174655f73656e6400"),
  (0xc718, "41505f496e65727469616c53656e736f723a3a706572696f64696300"),
  (0xc890, "000000000000000098c900000000000006000000000000000100000000000000a0c900000000000008000000000000000400000000000000a8c900000000000002000000000000000300000000000000b0c900000000000000000000000000000200000000000000b8c900000000000003000000000000000500000000000000c0c900000000000004000000000000000600000000000000c8c900000000000001000000000000000700000000000000d0c900000000000007000000000000000800000000000000d8c900000000000002000000000000000900000000000000e0c90000000000000100000000000000000000000000000000000000000000000000000000000000"),
  (0xc998, "0f1112131415"),
  (0xc9a0, "0708090b16180a3e"),
  (0xc9a8, "0538"),
  (0xc9b8, "0c0d0e"),
  (0xc9c0, "03210239"),
  (0xc9c8, "06"),
  (0xc9d0, "0124261a41373a"),
  (0xc9d8, "1f62"),
  (0xc9e0, "40"),
  (0xca68, "fb72657677667061000208000203ffff0408000000000000c8ca000000000000f0ca0000000000009db12d80000000000000000000cb0000000000000000000000000000000000000000000000000000000000000000000000000000"),
  (0xcac8, "41726475436f707465722056342e382e302d646576202838303264623139642900"),
  (0xcaf0, "383032646231396400"),
  (0xcb00, "41726475436f707465722056342e382e302d64657600"),
  (0xcb18, "a000000000000000030000000000000078cb0000000000008700000000000000020000000000000088cb000000000000a300000000000000020000000000000098cb000000000000f9000000000000000200000000000000a8cb000000000000"),
  (0xcb78, "52544c5f414c545f4d00"),
  (0xcb88, "52544c5f53504545445f4d5300"),
  (0xcb98, "52544c5f414c545f46494e414c5f4d00"),
  (0xcba8, "52544c5f434c494d425f4d494e5f4d00"),
  (0xcbb8, "d900000000000000020000000000000000cc000000000000dc00000000000000020000000000000010cc0000000000000600000019000000020000000000000028cc000000000000"),
  (0xcc00, "4c414e445f5350445f4d5300"),
  (0xcc10, "4c414e445f5350445f484947485f4d5300"),
  (0xcc28, "4c414e445f414c545f4c4f575f4d00"),
  (0xcce0, "000000000100000080cd000000000000010000000100000090cd0000000000000a00000001000000a0cd0000000000000c00000001000000b0cd0000000000000e00000002000000c0cd0000000000000f00000002000000d0cd0000000000001000000005000000e0cd0000000000001100000005000000f0cd000000000000120000000200000000ce000000000000130000000200000010ce000000000000"),
  (0xcd80, "475053315f5459504500"),
  (0xcd90, "475053325f5459504500"),
  (0xcda0, "475053315f474e53535f4d4f444500"),
  (0xcdb0, "475053325f474e53535f4d4f444500"),
  (0xcdc0, "475053315f524154455f4d5300"),
  (0xcdd0, "475053325f524154455f4d5300"),
  (0xcde0, "475053315f504f5300"),
  (0xcdf0, "475053325f504f5300"),
  (0xce00, "475053315f44454c41595f4d5300"),
  (0xce10, "475053325f44454c41595f4d5300"),
  (0xce48, "000000003209090000000000010000007c1f2b000000000002000000890c0c000000000004000000ed0e0e030c0d000005000000d91c1c01000000000600000068030300000000000700000077202000000000000b000000590606010400000014000000d614140302030000150000009f0202030001000016000000dc1919000000000017000000a81717030405000018000000181e3400000000001900000017656500000000001a000000aa161800000000001b000000901a1d00000000001c00000043101000000000001d000000730e1000000000001e000000271c1c00000000001f000000f62030000000000020000000b91c1c000000000021000000681c1c000000000022000000ed1616000000000023000000f41616000000000024000000de1525000000000025000000d40607030405000026000000090607030405000027000000fe2526032021000028000000e604050302030000290000001c040403020300002a0000001c020600000000002b00000084020303000100002c000000dd040503020300002d000000e8020303000100002e0000000b020200000000002f000000990304030001000030000000290d15010c00000031000000270c140000000000320000004e2525031213000033000000c404050302030000350000000305050000000000360000000f1b1b03181900003700000003191900000000003d000000a7484800000000003e000000b71a1a00000000003f00000077b5b5000000000040000000bfe1e1000000000041000000762a2a000000000042000000940606030203000043000000150404000000000045000000f30b1e010a000000460000007c122603101100004900000026252603202100004a00000014141400000000004b0000009e2323031e1f00004c000000982121031e1f00004d0000008f030a0308090000510000006a16160000000000520000003127270324250000530000001625250000000000540000008f35350332330000550000008c3333000000000056000000053535033233000057000000963333000000000059000000e71c1c00000000005a000000b7383800000000005b0000003f2a2a00000000005c00000036212100000000005d0000002f5151000000000064000000af1a220000000000650000006620750000000000660000009e2075000000000067000000d014390000000000680000003820740000000000690000005d3e3f00000000006a0000008a2c2c00000000006b0000006c404100000000006c00000020545c00000000006d000000b9090900000000006e00000054fefe03010200006f000000221010000000000070000000ae0c0c0000000000710000007c2427000000000072000000ed2c2c0000000000730000000440400000000000740000004c1618000000000075000000800606030405000076000000380e0e000000000077000000740c0c030a0b000078000000866161000000000079000000ed020203000100007a000000cb020203000100007b000000fa717103000100007c00000057233900000000007d000000cb060600000000007e000000dc4f4f00000000007f000000192323000000000080000000e223230000000000810000002e16180000000000820000001d0d0d000000000083000000dfffff000000000084000000550e27000000000085000000061212000000000086000000e52b2b000000000087000000cb0808000000000088000000011616000000000089000000c30e1000000000008a0000006d247800000000008b000000a82b2b03292a00008c000000b5292900000000008d0000002f202000000000008e00000048f3f300000000008f000000830e100000000000900000007f5d5d0000000000920000006764640000000000930000009a2436000000000094000000b23c4e000000000095000000c81e3c000000000096000000862a2a000000000097000000db0808030607000098000000d00408000000000099000000bc0c0c00000000009a000000540f0f03060700009b000000160d0d03040500009c00000013060603000100009d000000150f0f030c0d00009e000000860e0f030c0d0000a00000004e0c0c0308090000a10000004403030300010000a2000000bd08090000000000a30000007f1c1c0000000000a40000009a2c2c0000000000a50000001503030000000000a60000001509090000000000a70000009016160000000000a8000000010c0c0000000000a9000000ea12120000000000aa0000004922220000000000ab000000b542420000000000ac0000001662620000000000ad0000005308080000000000ae000000a730300000000000af0000008a1313030e0f0000b0000000ea03030300010000b1000000f014140000000000b20000002f18180000000000b3000000bd1d1d011a000000b4000000342d2f012a000000b5000000ae04040000000000b6000000e528280000000000b70000005502020300010000b80000009fcece0304050000b9000000ba07070304050000ba000000481d1d0300010000bf0000005c1b1b0000000000c0000000242c360000000000c100000047161a0000000000c20000006219210000000000c30000007825250000000000c8000000862a2a0328290000c9000000cd0e0e030c0d0000d60000004508080306070000d70000006503030000000000d80000003203030300010000d9000000ca06060000000000da0000001107070300010000db000000a202020000000000df000000772f2f032a2b0000e0000000662d2d032a2b0000e1000000d041490000000000e2000000cf08080000000000e6000000a32a2a0000000000e70000006928280000000000e8000000973f410000000000e900000023b6b60000000000ea0000009628280000000000eb000000b32a2a0000000000f10000005a20200000000000f200000068343c0000000000f300000055353d0134000000f40000005f06060000000000f50000008202020000000000f6000000b826260000000000f70000005113130000000000f800000008fefe0303040000f9000000cc24240000000000fa000000311e1e0000000000fb000000aa12120000000000fc0000002c12120000000000fd0000005333360000000000fe0000002e0909000000000000010000472a2a030809000001010000830909000000000002010000bb20e80300010000030100005cebed00000000000401000092050e000000000005010000b31b3d0000000000060100000c121700000000000701000085ffff000000000008010000311c200000000000090100001a101400000000000a010000c1ffff03020300000b01000023ffff03020300000c0100000e040403020300000d0100006dd5d900000000000e0100003b131600000000000f0100001634360000000000130100007e1f200000000000140100001231320000000000150100003e1e1e000000000018010000462121000000000019010000300d0d00000000001a0100007b232303202100001b0100004a909500000000001c010000632020031e1f00001d01000089283103262700001e010000d2353903323300001f010000011717031415000020010000141717031415000027010000ea0c0c0000000000280100009e292903242500002b01000013606000000000002d010000f33a3a0000000000360100001c11110000000000370100005f7474000000000040010000f31414030203000041010000580202030001000042010000f395950000000000430100004e939303000100004401000084929200000000004a010000179ea700000000004b0100005be6e900000000004c010000ecefef00000000004d010000e76d6d00000000004f010000e11818000000000053010000c70505000000000054010000634646000000000059010000d1151503020300005e010000e814fc0000000000680100000b19190000000000720100004b576d000000000075010000752a2a000000000077010000fb8c8c000000000078010000c708080000000000810100009385850302030000820100008410100304050000830100000448480304050000840100000825250320210000860100009ceef00000000000a40100001409490306070000b3010000862e2e0000000000b4010000c109090000000000b50100001e01010000000000b9010000a91111000000000001020000632d2d0328290000421f0000da10100000000000431f0000e729290000000000441f0000ac62620000000000451f0000fb26260000000000461f0000610e0e0000000000471f00004020200000000000481f0000ea21210000000000491f000090101000000000004a1f00009b292900000000004b1f000014666600000000004c1f000036101000000000004d1f0000de2e2e00000000004e1f0000c80e0e00000000004f1f00001718180000000000501f000095121200000000002823000071898900000000002d230000752222000000000011270000d11414000000000012270000ba2929000000000013270000040101000000000014270000850909000000000015270000670909000000000016270000c10404000000000017270000471111000000000018270000f00e0e0000000000a7270000c355550000000000f82a00008633340304050000f92a00000f87880000000000fa2a0000eab3b40304050000fb2a00004005050000000000fc2a00000be8e80308090000fd2a00005de6e60000000000022b00002e31310000000000032b00006a2c2c00000000000c2b0000cd10100000000000162b0000902c2c0000000000172b0000852c2c0000000000182b0000552c2c0000000000192b0000c3252503101100001a2b00004f050500000000001b2b000080080803040500001c2b0000b1222200000000001d2b0000821c1c00000000001e2b00002f262600000000001f2b00008e09090000000000202b0000842c2c0000000000212b0000d02c2c0000000000222b0000c92c2c0000000000232b0000c12c2c0000000000242b0000bd2c2c0000000000342b0000a24e4e000000000064320000722c2c030001000065320000fe3b3b031e1f0000663200008c3535030405000067320000f92e2e0300010000683200004d3636031c1d000069320000312b2b0300010000733200005ef9f90300010000763200008b333300000000007732000007121203101100007832000014050500000000006842000067b3b30000000000fe4200001a21210000000000ff4200004810100000000000014300001311110000000000024300005911110000000000034300001b0a0a0000000000044300000e5b5b000000000005430000bb54540000000000064300006a1818000000000010a40000e30101000000000011a40000ef2e2e000000000051c30000f62020000000000052c30000b5f6f6000000000053c300003e1313000000000054c30000f00a0a030809000055c30000980606030405000020cb00000d6464000000000021cb0000ef0101000000000015cd0000f01111000000000016cd0000584e4e000000000017cd0000605555000000000018cd0000b11c1c000000000019cd0000d73232000000000078cd0000b52626032021000079cd0000662424000000000060ea000004161603141500006aea0000d0212100000000006bea0000b7070700000000006cea000063242403202100006dea000081181803141500006eea0000860808030405000074ea0000ca0404000000000088ea00009cf5f5000000000089ea0000bfffff00000000008dea00000e0f1703020300008eea0000ab1c1c03080900008fea0000370707000000000092ea0000dc0e0e000000000093ea0000f51818000000000094ea0000652c2c000000000095ea00002d06060000000000"),
  (0xdf28, "22000000000000000200000000000000a0df00000000000066000000800000000400000000000000b0df00000000000066000000000100000400000000000000c8df00000000000066000000800100000400000000000000d8df00000000000066000000c00100000400000000000000e8df000000000000"),
  (0xdfa0, "4154435f414e474c455f4d415800"),
  (0xdfb0, "4154435f524154455f5750595f4d415800"),
  (0xdfc8, "4154435f4143435f595f4d415800"),
  (0xdfd8, "4154435f4143435f525f4d415800"),
  (0xdfe8, "4154435f4143435f505f4d415800"),
  (0xdff8, "c30f00000400000048e1000000000000430000000400000058e1000000000000030100000400000068e1000000000000c30000000400000078e1000000000000430100000400000088e1000000000000830100000400000098e10000000000000401000004000000a8e10000000000004402000004000000b8e10000000000008402000004000000c8e1000000000000c402000004000000d8e10000000000000403000004000000e8e10000000000004403000004000000f8e1000000000000840300000400000008e2000000000000040400000100000018e2000000000000c40300000100000028e2000000000000c60f00000400000038e2000000000000460000000400000048e2000000000000060100000400000058e2000000000000c60000000400000068e2000000000000460100000400000078e2000000000000860100000400000088e2000000000000"),
  (0xe148, "5053435f445f56454c5f5000"),
  (0xe158, "5053435f445f56454c5f4900"),
  (0xe168, "5053435f445f56454c5f4400"),
  (0xe178, "5053435f445f56454c5f464c544500"),
  (0xe188, "5053435f445f56454c5f464c544400"),
  (0xe198, "5053435f445f56454c5f464600"),
  (0xe1a8, "5053435f445f4143435f464600"),
  (0xe1b8, "5053435f445f4143435f464c545400"),
  (0xe1c8, "5053435f445f4143435f464c544500"),
  (0xe1d8, "5053435f445f4143435f464c544400"),
  (0xe1e8, "5053435f445f4143435f534d415800"),
  (0xe1f8, "5053435f445f4143435f50444d5800"),
  (0xe208, "5053435f445f4143435f445f464600"),
  (0xe218, "5053435f445f4143435f4e454600"),
  (0xe228, "5053435f445f4143435f4e544600"),
  (0xe238, "5053435f4e455f56454c5f5000"),
  (0xe248, "5053435f4e455f56454c5f4900"),
  (0xe258, "5053435f4e455f56454c5f4400"),
  (0xe268, "5053435f4e455f56454c5f464c544500"),
  (0xe278, "5053435f4e455f56454c5f464c544400"),
  (0xe288, "5053435f4e455f56454c5f464600"),
  (0xe298, "c40f000004000000c8e20000000000004400000004000000d8e20000000000008400000004000000e8e2000000000000"),
  (0xe2c8, "5053435f445f4143435f5000"),
  (0xe2d8, "5053435f445f4143435f4900"),
  (0xe2e8, "5053435f445f4143435f4400"),
  (0xe2f8, "830000000400000018e3000000000000860000000400000028e3000000000000"),
  (0xe318, "5053435f445f56454c5f494d415800"),
  (0xe328, "5053435f4e455f56454c5f494d415800"),
  (0xe338, "440100000400000048e3000000000000"),
  (0xe348, "5053435f445f4143435f494d415800"),
  (0xe358, "6500000000000000040000000000000000e40000000000006500000001000000040000000000000008e40000000000006500000002000000040000000000000018e40000000000006500000003000000040000000000000028e40000000000006500000005000000040000000000000038e40000000000006500000006000000040000000000000040e4000000000000650000000d000000040000000000000050e4000000000000"),
  (0xe400, "57505f53504400"),
  (0xe408, "57505f5241444955535f4d00"),
  (0xe418, "57505f5350445f555000"),
  (0xe428, "57505f5350445f444e00"),
  (0xe438, "57505f41434300"),
  (0xe440, "57505f4143435f5a00"),
  (0xe450, "57505f4143435f434e5200"),
  (0xe460, "69000000020000000400000000000000c0e400000000000069000000030000000400000000000000d0e400000000000069000000040000000400000000000000e0e400000000000069000000050000000400000000000000f0e4000000000000"),
  (0xe4c0, "4c4f49545f53504545445f4d5300"),
  (0xe4d0, "4c4f49545f4143435f4d41585f4d00"),
  (0xe4e0, "4c4f49545f42524b5f4143435f4d00"),
  (0xe4f0, "4c4f49545f42524b5f4a524b5f4d00"),
  (0xe500, "6800000000000000040000000000000018e5000000000000"),
  (0xe518, "434952434c455f5241444955535f4d00"),
  (0xeb60, "000102030405070b0d0e0f101112131415161718191a1b1c"),
  (0xebe0, "0000000000000000f200000046000000310000004500000001000000070000007d0000000800000098000000090000003e0000000a0000002a0000000b000000240000000c000000410000000d000000230000000e0000001b0000000f0000001a000000100000007400000011000000810000001200000069000000600000001d0000001300000089000000140000008f0000001500000018000000160000007c00000018000000020000001a000000160000001f000000a4000000210000006c00000022000000b200000002000000a3000000010000001e000000030000001f00000004000000210000000500000020000000380000004a00000006000000a8000000240000008400000026000000c100000037000000c200000039000000f10000003a0000002e0000003d000000530000005c000000570000003e000000550000003f0000009300000041000000f5000000480000009400000049000000b301000062000000b50100006300000008010000640000005401000065000000"),
  (0x12e58, "00f0"),
  (0x12e60, "f8fd"),
  (0x12e68, "0100"),
  (0x12e70, "0200"),
  (0x12e78, "0400"),
  (0x12e80, "0800"),
  (0x12e88, "1000"),
  (0x12e90, "2000"),
  (0x12e98, "4000"),
  (0x12ea0, "8000"),
  (0x12ea8, "0001"),
  (0x12eb0, "0002"),
  (0x12eb8, "0004"),
  (0x12ec0, "0008"),
  (0x12ec8, "0010"),
  (0x12ed0, "20"),
  (0x12ed8, "01000000020000000300000004000000"),
  (0x12ef8, "000080bf0000803f0000803f0100000000000000000080bf000080bf0200000000000000000080bf0000803f030000000000803f0000803f000080bf04000000"),
  (0x12f38, "000034420000803f01000000000007c30000803f03000000000034c2000080bf0400000000000743000080bf02000000"),
  (0x12f68, "00000743000080bf02000000000034420000803f01000000000007c30000803f03000000000034c2000080bf04000000"),
  (0x12f98, "000007430000803f0200000000003442000080bf01000000000007c3000080bf03000000000034c20000803f04000000"),
  (0x12fc8, "000034420000803f01000000000034c2000080bf04000000000007c30000803f0300000000000743000080bf02000000"),
  (0x12ff8, "000034420000803f0100000000000743000080bf02000000000007c30000803f03000000000034c2000080bf04000000"),
  (0x13028, "0000344248504c3f01000000000007c30000803f03000000000034c248504cbf0400000000000743000080bf02000000"),
  (0x13058, "00003442000080bf01000000000007c3000080bf03000000000034c20000803f04000000000007430000803f02000000"),
  (0x13088, "0000b442000080bf020000000000b4c2000080bf04000000000000000000803f01000000000034430000803f03000000"),
  (0x130e0, "dcdfe1e3e6e8ebedeff2f4f7f9fcfe000305080a0c0f111416181b1d20222427"),
  (0x13100, "2c76d888674f0823c1dfae59b1b796e5e453c63a51997696e6c28426898c9b62407c6ffcbc9c9f40baa56fa590055a2a5c936b6c676dc11be0e40d47f520e6b5d0ed902e009435770080841e0000204e000000c833333333986e128341ef8d21893be655cffee6dbd1844b38f77c1d90a4bbe4243284725e8100c9f1eca1e53d"),
  (0x13190, "16a4000003000000c900000003000000c300000003000000b300000000000000"),
  (0x131f0, "e032010000000000f03201000000000000330100000000001033010000000000203301000000000030330100000000003833010000000000483301000000000058330100000000006833010000000000783301000000000088330100000000009833010000000000a833010000000000b833010000000000c833010000000000d833010000000000e833010000000000f8330100000000000834010000000000103401000000000020340100000000003034010000000000403401000000000050340100000000006034010000000000703401000000000080340100000000009034010000000000a034010000000000"),
  (0x132e0, "6d61706661696c75726500"),
  (0x132f0, "6d6973735f73747275637400"),
  (0x13300, "77726974655f6d7373666d7400"),
  (0x13310, "6d616e795f64656c6574657300"),
  (0x13320, "6261645f67657466696c6500"),
  (0x13330, "70616e696300"),
  (0x13338, "666c7573685f6e6f5f73656d00"),
  (0x13348, "6261645f637572725f626c6b00"),
  (0x13358, "626c6b636e745f62616400"),
  (0x13368, "64715f6661696c75726500"),
  (0x13378, "636e737472696e675f6e616e00"),
  (0x13388, "7761746368646f675f72737400"),
  (0x13398, "696f6d63755f726573657400"),
  (0x133a8, "696f6d63755f6661696c00"),
  (0x133b8, "7370695f6661696c00"),
  (0x133c8, "6d61696e5f6c6f6f705f73746b00"),
  (0x133d8, "6763735f6261645f6c696e6b00"),
  (0x133e8, "6269746d61736b5f72616e676500"),
  (0x133f8, "6763735f6f666673657400"),
  (0x13408, "6932635f69737200"),
  (0x13410, "666c6f775f6f665f6374726c00"),
  (0x13420, "7366735f726563757273696f6e00"),
  (0x13430, "6261645f726f746174696f6e00"),
  (0x13440, "737461636b5f6f7672666c7700"),
  (0x13450, "696d755f726573657400"),
  (0x13460, "6770696f5f69737200"),
  (0x13470, "6d656d5f677561726400"),
  (0x13480, "646d615f6661696c00"),
  (0x13490, "706172616d735f726573746f72656400"),
  (0x134a0, "696e76616c696420617267756d656e747300"),
  (0x135d0, "0000803f0000803f0000803f"),
  (0x13668, "070000000000000098370100000000001800000000000000a8370100000000001f00000000000000b8370100000000002000000000000000c8370100000000002700000000000000d8370100000000002800000000000000e8370100000000003a00000000000000f8370100000000003e0000000000000008380100000000003f00000000000000183801000000000041000000000000002838010000000000690000000000000038380100000000004a0000000000000048380100000000004b00000000000000583801000000000054000000000000006838010000000000ac0000000000000070380100000000009d000000000000008838010000000000a000000000000000a038010000000000a100000000000000b038010000000000a200000000000000c038010000000000"),
  (0x13798, "53617665576179706f696e7400"),
  (0x137a8, "4d697373696f6e526573657400"),
  (0x137b8, "4d6f746f724553746f7000"),
  (0x137c8, "4d6f746f72496e7465726c6f636b00"),
  (0x137d8, "507265636973696f6e4c6f6974657200"),
  (0x137e8, "41766f696450726f78696d69747900"),
  (0x137f8, "436c656172576179706f696e7400"),
  (0x13808, "436f6d706173734c6561726e00"),
  (0x13818, "5361696c626f61745461636b00"),
  (0x13828, "47505344697361626c6500"),
  (0x13838, "47505344697361626c6559617700"),
  (0x13848, "5361696c626f61744d6f746f7200"),
  (0x13858, "53757266616365547261636b696e6700"),
  (0x13868, "4169724d6f646500"),
  (0x13870, "42617474657279204d50505420456e61626c6500"),
  (0x13888, "456d657267656e6379204c616e64696e6700"),
  (0x138a0, "5765617468657276616e6500"),
  (0x138b0, "54757262696e6520537461727400"),
  (0x138c0, "464654204e6f7463682054756e696e6700"),
  (0x138d8, "d886000000000000"),
  (0x138e0, "050102040300ff"),
  (0x13950, "3078343135320053797374656d206e6f7420696e697469616c6973656400496e7465726c6f636b2f452d53746f7020436f6e666c696374004d6f746f7220496e7465726c6f636b20456e61626c6564004d6f746f72733a202573005468726f74746c65005243206e6f7420666f756e640025732062656c6f77206661696c7361666500416c7469747564652064697370617269747900454b46206174746974756465206973206261640042617474657279206661696c7361666500436865636b2046535f5448525f56414c55450046535f4743535f454e41424c453d322072656d6f7665642c207365652046535f4f5054494f4e5300436865636b2050494c4f545f5350445f555000496e76616c6964204d756c7469436f70746572204652414d455f434c4153530052544c5f414c545f545950452069732061626f76652d7465727261696e20627574202573006e6f207465727261696e20646174610072616e676566696e646572206e6f7420696e206669726d77617265005053430042616420706172616d657465723a202573004154430048696768204750532048444f5000414852533a202573004e65656420506f736974696f6e20457374696d6174650047505320676c69746368696e6700636f6d7061737300706f736974696f6e0076656c6f636974790068656967687400454b462025732076617269616e636500474353206661696c73616665206f6e004e65656420416c7420457374696d6174650041485253206e6f74206865616c74687900436f6d70617373202564206e6f74206865616c746879002573206d6f6465206e6f742061726d61626c65004c65616e696e6700257320746f6f206869676800536166657479205377697463680041726d696e67206d6f746f72730044697361726d696e67206d6f746f72730053494d504c45206d6f6465206f66660053494d504c45206d6f6465206f6e00535550455253494d504c45206d6f6465206f6e0041726475436f707465722056342e382e302d64657620283830326462313964290038303264623139640041726475436f707465722056342e382e302d6465760041505f496e65727469616c53656e736f723a3a7570646174652a00436f707465723a3a72756e5f726174655f636f6e74726f6c6c65725f6d61696e2a00436f707465723a3a6d6f746f72735f6f75747075745f6d61696e2a00436f707465723a3a726561645f414852532a00436f707465723a3a726561645f696e65727469612a00436f707465723a3a636865636b5f656b665f72657365742a00436f707465723a3a7570646174655f666c696768745f6d6f64652a00436f707465723a3a7570646174655f686f6d655f66726f6d5f454b462a00436f707465723a3a7570646174655f6c616e645f616e645f63726173685f6465746563746f72732a00436f707465723a3a7570646174655f72616e676566696e6465725f7465727261696e5f6f66667365742a00436f707465723a3a72635f6c6f6f7000436f707465723a3a7468726f74746c655f6c6f6f700041505f4750533a3a75706461746500436f707465723a3a7570646174655f626174745f636f6d706173730052435f4368616e6e656c733a3a726561645f6175785f616c6c00436f707465723a3a6175746f5f64697361726d5f636865636b00436f707465723a3a7570646174655f616c74697475646500436f707465723a3a72756e5f6e61765f7570646174657300436f707465723a3a7570646174655f7468726f74746c655f686f76657200436f707465723a3a74687265655f687a5f6c6f6f7000436f707465723a3a6f6e655f687a5f6c6f6f7000436f707465723a3a656b665f636865636b00436f707465723a3a636865636b5f766962726174696f6e00436f707465723a3a677073676c697463685f636865636b00436f707465723a3a74616b656f66665f636865636b00436f707465723a3a7374616e6462795f75706461746500436f707465723a3a6c6f73745f76656869636c655f636865636b004743533a3a7570646174655f72656365697665004743533a3a7570646174655f73656e640041505f496e65727469616c53656e736f723a3a706572696f64696300546f6f206d616e792056656869636c657300474353206d7573742062652073696e676c65746f6e0041505f506172616d206d7573742062652073696e676c65746f6e004d697373696f6e206d7573742062652073696e676c65746f6e004d756c7469436f70746572006d6f746f7273206e6f7420616c6c6f6361746564002573005265626f6f742072656a65637465642c204553432063616c206f6e207265626f6f74004661696c656420746f207061757365004661696c656420746f20726573756d65004175746f2052544c004175746f00464f524d41545f56455253494f4e0050494c4f545f5448525f46494c540050494c4f545f5448525f424856004743535f5049445f4d41534b0052544c5f434f4e455f534c4f50450052544c5f4c4f49545f54494d450052544c5f414c545f545950450046535f4743535f454e41424c45004750535f48444f505f474f4f440053555045525f53494d504c450057505f5941575f4245484156494f520046535f5448525f454e41424c450046535f5448525f56414c5545005448525f445a00464c544d4f44453100464c544d4f44453200464c544d4f44453300464c544d4f44453400464c544d4f44453500464c544d4f44453600464c544d4f44455f434800494e495449414c5f4d4f44450053494d504c45004c4f475f4249544d41534b004553435f43414c4942524154494f4e004652414d455f545950450041524d494e475f0044495341524d5f44454c4159004c414e445f5245504f534954494f4e0046535f454b465f414354494f4e0046535f454b465f5448524553480046535f43524153485f434845434b0052435f535045454400434f4d504153535f00494e530057505f004c4f49545f00434952434c455f004154435f00414852535f0042415454004252445f0043414e5f0053494d5f004241524f004750530053434845445f004d4f545f0052434d41505f00454b335f004d49535f004e54465f00004d41560057505f4e4156414c545f4d494e004445565f4f5054494f4e53004652414d455f434c41535300534552564f0052430046535f564942455f454e41424c450046535f4f5054494f4e53004155544f5f4f5054494f4e5300475549445f4f5054494f4e530046535f4743535f54494d454f55540052544c5f4f5054494f4e5300464c494748545f4f5054494f4e5300475549445f54494d454f55540046535f44525f454e41424c450046535f44525f54494d454f55540050494c4f545f595f00544b4f46465f534c45575f54494d4500535552465452414b5f544300544b4f46465f5448525f4d41580046535f454b465f46494c540052544c5f004c414e445f0050494c4f545f4143435f5a0050494c4f545f5350445f55500050494c4f545f5350445f444e0050494c4f545f544b4f5f414c545f4d004d41565f5359534944004d41565f4743535f5359534944004d41565f4f5054494f4e53004d41565f54454c454d5f44454c415900315f00325f00335f00345f00355f00365f00375f00385f00395f0031305f0031315f0031325f0031335f0031345f0031355f0031365f005f4f564552524944455f54494d45005f4f5054494f4e53005f50524f544f434f4c53005f46535f54494d454f5554005374616e6420427920456e61626c6564005374616e642042792044697361626c656400466c69676874204d6f6465205061757365206661696c65640053696d706c652068656164696e67207265736574005472696d20736176656400436f6d706173732064697361626c656400436865636b20636f6d70617373005243206e6f742063616c69627261746564005468726f74746c65206e6f74207a65726f004e6f74206c616e646564005374617274696e672063616c6962726174696f6e0043757272656e740043616c6962726174696f6e207375636365737366756c004661696c65640043726173683a2044697361726d696e673a20416e674572723d252e30663e252e30662c20416363656c3d252e31663c252e316600506f74656e7469616c20546872757374204c6f737320282564290059617720496d62616c616e63652025302e3066252500454b462076617269616e63653a202573006f766572207468726573686f6c647300706f736974696f6e206c6f737400454b46204661696c7361666500454b46204661696c736166653a206368616e67656420746f202573204d6f646500454b46204661696c7361666520436c656172656400566962726174696f6e20636f6d70656e736174696f6e204f4e00566962726174696f6e20636f6d70656e736174696f6e204f4646004553432063616c6962726174696f6e3a205265737461727420626f617264004553432063616c6962726174696f6e3a2050617373696e672070696c6f74207468726f74746c6520746f2045534373004553432063616c6962726174696f6e3a204175746f2063616c6962726174696f6e004553432063616c6962726174696f6e3a2050757368207361666574792073776974636800526164696f0044697361726d696e6700526164696f202b204261747465727900436f6e74696e75696e67204c616e64696e6700436f6e74696e75696e67204175746f00436f6e74696e75696e6720477569646564204d6f646500526164696f204661696c7361666520436c6561726564002573204661696c73616665202d202573002573204661696c7361666500426174746572790047435300474353202b204261747465727900436f6e74696e75696e67204175746f204d6f646500436f6e74696e75696e672050696c6f7420436f6e74726f6c00474353204661696c7361666520436c6561726564004661696c736166653a205465727261696e2025730064617461206d697373696e670052616e676566696e64657220556e6865616c74687900556e617661696c61626c650047505320476c69746368206f7220436f6d70617373206572726f7200476c6974636820636c65617265640044656164205265636b6f6e696e6700257320737461727465640025732073746f707065640025732074696d656f757400536d61727452544c20556e617661696c61626c652c205573696e67204c616e64204d6f646500536d61727452544c20556e617661696c61626c652c20547279696e672052544c204d6f646500547279696e672052544c204d6f646500547279696e67204c616e64204d6f6465004d6f6465206368616e676520746f202573206661696c65643a2025730047435320656e7472792064697361626c65642028464c544d4f44455f474353424c4f434b29007468726f74746c6520746f6f206869676800726571756972657320706f736974696f6e006e65656420616c7420657374696d61746500696e205243206661696c7361666500696e6974206661696c656400416c74697475646520486f6c6400414c5448004175746f3a204d697373696e672054616b656f666620436d64004175746f206d697373696f6e206368616e6765642c2072657374617274656420636f6d6d616e64004175746f206d697373696f6e206368616e67656420627574206661696c656420746f207265737461727420636f6d6d616e64004d6f6465206368616e676520746f204155544f2052544c206661696c65643a204e6f206c616e64696e672073657175656e636520666f756e64004d6f6465206368616e676520746f204155544f2052544c206661696c65643a204e6f2072657475726e207061746820666f756e64004d6f6465206368616e676520746f204155544f2052544c206661696c65643a204e6f2072657475726e2070617468206f72206c616e64696e672073657175656e636520666f756e64004d697373696f6e3a20636972636c696e6720252e3166207475726e7300536b697070696e6720696e76616c696420636d64202325690062616420646f5f6c6f697465725f746f5f616c740044656c6179696e6720257520736563005265616368656420636f6d6d616e6420232569004d697373696f6e3a20636972636c65642025752f252e3166207475726e73004152544c004155544f004272616b65004252414b00436972636c650043495243004775696465640047554944005350445f4d53005350445f484947485f4d5300414c545f4c4f575f4d004c414e445f5350445f4d53004c414e445f5350445f484947485f4d53004c414e445f414c545f4c4f575f4d004c616e64004c414e44004c6f69746572004c4f495400414c545f4d00414c545f46494e414c5f4d00434c494d425f4d494e5f4d0053504545445f4d530052544c5f414c545f4d0052544c5f53504545445f4d530052544c5f414c545f46494e414c5f4d0052544c5f434c494d425f4d494e5f4d0052657374617274696e672052544c202d205465727261696e2064617461206d697373696e670052544c3a20756e6578706563746564206572726f722073657474696e6720636c696d62207461726765740052544c3a206e6f207465727261696e20646174612c207573696e6720616c742d61626f76652d686f6d650052544c3a2072616e676566696e64657220756e6865616c7468792c207573696e6720616c742d61626f76652d686f6d650052544c3a20756e6578706563746564206572726f722063616c63756c6174696e672074617267657420616c740052544c0052544c200053746162696c697a650053544142004d6f746f7220546573743a2063616e63656c6c65640025733a20426f61726420696e697469616c6973696e670025733a2025730025733a205243206e6f742063616c696272617465640025733a2076656869636c65206e6f74206c616e646564004d6f746f722054657374007374617274696e67206d6f746f7220746573740066696e6973686564206d6f746f722074657374004c6f6361746520436f7074657220616c61726d004652414d455f434c4153533d25750041505f414852535f56696577004174746974756465436f6e74726f6c00506f73436f6e74726f6c0057504e6176004c6f697465724e617600436972636c654e61760041505f4d6f746f72734d6174726978206d7573742062652073696e676c65746f6e0054616b656f666620626c6f636b65643a00257320435055206f7665726c6f6164202825342e31662525290050414e49433a20000a0074696d65206d75737420696e637265617365002d2d73746f72616765002d2d73746f726167652d6f7574002d2d696d7573002d2d696d752d72617465002d2d74696d696e67002d2d70726f66696c65002d2d657374006c6f636b737465703a2063616e6e6f742077726974652025730a002d2d706172616d2d64756d70002d2d706172616d2d74657374002d2d74696d696e672d66696c650077006c6f636b737465703a2063616e6e6f742072656164207468652073746f7261676520696d61676520257320282575206279746573206578706563746564290a00743d256c6c752070776d3d002c2575002575003031323334353637383961626364656600743d006c696e65206d757374207374617274207769746820743d00746f6b656e20776974686f757420273d2700696d753000696d753100746f6f206d616e7920494d552073616d706c6573006261726f006d6167006770730072630072632076616c7565206f7574206f662072616e67650062617400757000756e6b6e6f776e206b657900747261696c696e672063686172616374657273006578706563746564206120646563696d616c206e756d62657200657870656374656420272563270062616420686578206469676974006c6f636b737465703a20696e707574206c696e6520256c6c753a2025730a006c6f636b737465703a2025752075706c696e6b2062797465732064726f707065642028726563656976652071756575652066756c6c290a006c6f636b737465702074696d696e673a20257a752073746570732c2076656869636c6520636f6d7075746520706572207374657020287573293a206d65616e20252e32662070353020252e32662070393020252e32662070393920252e3266206d617820252e32662c20746f74616c20252e336620730a0025750a0061007461736b2025732025750a007363686564756c65722d6265747765656e2d7461736b732025750a007363686564756c65722d776169745f666f725f73616d706c652025750a007363686564756c65722d6f746865722025750a0068616c2d70726f746f636f6c2025750a68616c2d74696d65722d70726f63732025750a68616c2d696f2d70726f63732025750a00737465707320256c6c750a0077620075736167653a20636f707465725f726566205b2d2d73746f726167652046494c455d205b2d2d73746f726167652d6f75742046494c455d205b2d2d696d7573204e5d205b2d2d696d752d7261746520485a5d205b2d2d74696d696e675d205b2d2d74696d696e672d66696c652046494c455d205b2d2d70726f66696c652046494c455d205b2d2d6573742046494c455d205b2d2d706172616d2d64756d702046494c45205b2d2d706172616d2d74657374205343524950545d5d0a20207265616473206f6e6520696e707574206c696e6520706572206c6f636b2d737465702073746570206f6e20737464696e2c20777269746573206f6e65206f7574707574206c696e652070657220696e707574206c696e65206f6e207374646f75740a0072620050414e49433a207363686564756c65722073797374656d20696e697469616c697a65642063616c6c6564206d6f7265207468616e206f6e636500637070326c65616e2d6c6f636b7374657000546f6f206d616e79205349544c20696e7374616e63657300434f4d504153535f5343414c4500434f4d504153535f5343414c453200434f4d504153535f5343414c4533005349544c00435050324c45414e5f4743535f44554d5000256c642c256c6400435050324c45414e5f504152414d5f534e415053484f5400706172616d736e617020256c6420257320256420253038780a0067637364756d7020256c6420002530327800696e697400696e00646362007469636b007461736b73002d0061726d656400666c79696e6700746b64007468677400686f6d650063666700636f6d700062676e640071007270790064636d0076656c00706f73006c6f63006779726f00616363656600726573657473006865616c74687900696e697469616c69736564006f726967696e00656b660066730025303878007072696d617279006e636f72657300676269617300616269617300766172006325752e78006325752e6673006325752e50006325752e6f7574006325752e696d75006325752e766172006325752e677366006576006576780063696e002320706172616d73006261726f6d657465722e73656e736f72735b25755d2e67726f756e645f7072657373757265006261726f6d657465722e73656e736f72735b25755d2e6275735f6964006261726f6d657465722e5f616c745f6f6666736574006261726f6d657465722e5f6669656c645f656c65766174696f6e006261726f6d657465722e5f7072696d6172795f6261726f006261726f6d657465722e5f6578745f627573006261726f6d657465722e5f73706563696669635f67726176697479006261726f6d657465722e5f757365725f67726f756e645f74656d7065726174757265006261726f6d657465722e5f66696c7465725f72616e6765006261726f6d657465722e5f616c745f6572726f725f6d6178006261726f6d657465722e5f6f7074696f6e7300636f6d706173732e5f656e61626c656400636f6d706173732e5f6c6561726e00636f6d706173732e5f6465636c696e6174696f6e00636f6d706173732e5f6175746f5f6465636c696e6174696f6e00636f6d706173732e5f6d6f746f725f636f6d705f7479706500636f6d706173732e5f726f746174655f6175746f00636f6d706173732e5f73746174652e5f707269765f696e7374616e63655b25755d2e0065787465726e616c006f7269656e746174696f6e006f666673657400646961676f6e616c73006f6666646961676f6e616c73006d6f746f725f636f6d70656e736174696f6e002e78002e79002e7a007363616c655f666163746f72006465765f696400636f6d706173732e5f7573655f666f725f7961772e5f707269765f696e7374616e63655b25755d00636f6d706173732e5f7072696f726974795f6469645f73746f7265645f6c6973742e5f707269765f696e7374616e63655b25755d00636f6d706173732e65787472615f6465765f69645b25755d00636f6d706173732e5f6f66667365745f6d617800636f6d706173732e5f6472697665725f747970655f6d61736b00636f6d706173732e5f66696c7465725f72616e676500636f6d706173732e5f6f7074696f6e7300636f6d706173732e5f7065725f6d6f746f722e656e61626c6500636f6d706173732e5f7065725f6d6f746f722e6578706f005b25755d00696e732e5f6779726f5f6f66667365745f6f6c645f706172616d00696e732e5f616363656c5f7363616c655f6f6c645f706172616d00696e732e5f616363656c5f6f66667365745f6f6c645f706172616d00696e732e5f7573655f6f6c645f706172616d00696e732e5f616363656c5f706f735f6f6c645f706172616d00696e732e5f6779726f5f69645f6f6c645f706172616d00696e732e5f616363656c5f69645f6f6c645f706172616d00696e732e5f6779726f5f66696c7465725f6375746f666600696e732e5f616363656c5f66696c7465725f6375746f666600696e732e5f7374696c6c5f7468726573686f6c6400696e732e5f6779726f5f63616c5f74696d696e6700696e732e5f7472696d5f6f7074696f6e00696e732e5f6163635f626f64795f616c69676e656400696e732e5f666173745f73616d706c696e675f6d61736b00696e732e5f656e61626c655f6d61736b00696e732e5f666173745f73616d706c696e675f7261746500696e732e7261775f6c6f6767696e675f6f7074696f6e73006770732e5f6e617666696c746572006770732e5f6175746f5f737769746368006770732e5f736261735f6d6f6465006770732e5f6d696e5f656c65766174696f6e006770732e5f696e6a6563745f746f006770732e5f7362705f6c6f676d61736b006770732e5f7261775f64617461006770732e5f736176655f636f6e666967006770732e5f6175746f5f636f6e666967006770732e5f626c656e645f6d61736b006770732e5f6472697665725f6f7074696f6e73006770732e5f7072696d617279006770732e706172616d735b25755d2e007479706500676e73735f6d6f646500726174655f6d7300616e74656e6e615f6f66667365740064656c61795f6d7300636f6d5f706f727400454b46332e5f656e61626c6500454b46332e5f677073486f72697a56656c4e6f69736500454b46332e5f6770735665727456656c4e6f69736500454b46332e5f67707356656c496e6e6f764761746500454b46332e5f677073486f72697a506f734e6f69736500454b46332e5f677073506f73496e6e6f764761746500454b46332e5f677073476c697463685261646975734d617800454b46332e5f6261726f416c744e6f69736500454b46332e5f686774496e6e6f764761746500454b46332e5f68677444656c61795f6d7300454b46332e5f6d61674e6f69736500454b46332e5f6d616743616c00454b46332e5f6d6167496e6e6f764761746500454b46332e5f6561734e6f69736500454b46332e5f746173496e6e6f764761746500454b46332e5f726e674e6f69736500454b46332e5f726e67496e6e6f764761746500454b46332e5f6d6178466c6f775261746500454b46332e5f666c6f774e6f69736500454b46332e5f666c6f77496e6e6f764761746500454b46332e5f666c6f7744656c61795f6d7300454b46332e5f6779724e6f69736500454b46332e5f6163634e6f69736500454b46332e5f6779726f4269617350726f636573734e6f69736500454b46332e5f616363656c4269617350726f636573734e6f69736500454b46332e5f77696e6456656c50726f636573734e6f69736500454b46332e5f776e64566172486774526174655363616c6500454b46332e5f677073436865636b00454b46332e5f696d754d61736b00454b46332e5f677073436865636b5363616c657200454b46332e5f6e6f616964486f72697a4e6f69736500454b46332e5f626574614d61736b00454b46332e5f7961774e6f69736500454b46332e5f796177496e6e6f764761746500454b46332e5f74617556656c506f734f757470757400454b46332e5f6d6167456172746850726f636573734e6f69736500454b46332e5f6d6167426f647950726f636573734e6f69736500454b46332e5f757365526e67537748677400454b46332e5f74657272477261644d617800454b46332e5f726e6742636e4e6f69736500454b46332e5f726e6742636e496e6e6f764761746500454b46332e5f726e6742636e44656c61795f6d7300454b46332e5f757365526e67537753706400454b46332e5f616363426961734c696d00454b46332e5f6d61674d61736b00454b46332e5f6f726967696e4867744d6f646500454b46332e5f7669734f646d56656c4572724d696e00454b46332e5f7669734f646d56656c4572724d617800454b46332e5f77656e634f646d56656c45727200454b46332e5f666c6f7755736500454b46332e5f6872745f66696c745f6672657100454b46332e5f6d61675f65665f6c696d697400454b46332e5f67736652756e4d61736b00454b46332e5f6773665573654d61736b00454b46332e5f666c6f774e61764761696e48677400454b46332e5f67736652657365744d6178436f756e7400454b46332e5f6572725f74687265736800454b46332e5f616666696e69747900454b46332e5f62616c6c6973746963436f65665f7800454b46332e5f62616c6c6973746963436f65665f7900454b46332e5f647261674f62734e6f69736500454b46332e5f6d6f6d656e74756d44726167436f656600454b46332e5f6f676e6d546573745363616c65466163746f7200454b46332e5f6261726f476e64456666656374446561645a6f6e6500454b46332e5f7072696d6172795f636f726500454b46332e5f6c6f675f6c6576656c00454b46332e5f677073564163635468726573686f6c6400454b46332e5f6f7074696f6e7300454b46332e736f75726365732e5f736f757263655f7365745b25755d2e00706f7378790076656c787900706f737a0076656c7a0079617700454b46332e736f75726365732e5f6f7074696f6e7300616872732e6770735f6761696e00616872732e5f6770735f75736500616872732e5f6b705f79617700616872732e5f6b7000616872732e5f77696e645f6d617800616872732e5f7472696d00616872732e5f626f6172645f6f7269656e746174696f6e00616872732e6265746100616872732e5f6770735f6d696e7361747300616872732e5f656b665f7479706500616872732e5f6f7074696f6e7300616872732e5f6f726967696e5f6c617400616872732e5f6f726967696e5f6c6f6e00616872732e5f6f726967696e5f616c74002025733d25303878002025733d256c6c6400256c6c7500256c6c640023207461736b73002025753d2573402575003f00253031366c6c7800696e7300696d75257500677073257500706172616d5f64756d703a2063616e6e6f742077726974652025730a0064656661756c7473006c6f6164656400706172616d5f64756d703a206c6f61645f616c6c20252e31662075733b20656e756d65726174696f6e20252e31662075732070657220706173732028257520706172616d6574657273290a007200706172616d5f746573743a2063616e6e6f74206f70656e202573206f722025730a00626f6f7420256420253031366c6c780a002533317300656e756d00252a73202575202575202575006e616d6500252a732025363373002066696e6420256420257500696e64657800252a732025750073657400252a7320253633732025752025782025750020253031366c6c78006c6f61640020256400636f756e740064756d70006c6f6164616c6c00256420253031366c6c7800232025730a002320636f756e742025750a002320636f756e745f706172616d65746572732025750a00232073746f7261676520253031366c6c780a0025752025752c25752c2575202573202575200025640a00253038780a003f0a006e756c6c0025752c25752c25752025732025752000256400454b4633207072696d617279206368616e6765643a256400454b4633206e6f74207374617274656400454b46330053494d00556e737570706f7274656420414852532076696577202575004750535f4741494e004750535f555345005941575f500052505f500057494e445f4d4158004f5249454e544154494f4e00434f4d505f42455441004750535f4d494e5341545300454b465f54595045004f524947494e5f4c4154004f524947494e5f4c4f4e004f524947494e5f414c5400454b4631206e6f7420617661696c61626c6500756e696e697469616c69736564206c6f636174696f6e2072657475726e6564206279205f6765745f6c6f636174696f6e00414852533a2025732061637469766500414852533a207573696e67207265636f72646564206f726967696e3a252e37662c252e37662c252e3166004e6f74206865616c746879006e6f74207573696e6720636f6e666967757265642041485253207479706500257320257320696e636f6e73697374656e74202564206465672e2057616974206f72207265626f6f7400526f6c6c2f5069746368005961770044434d00526573746f726564207761746368646f6720686f6d6500526573746f726564207761746368646f6720617474697475646520252e306620252e306620252e306600315f474e445f5052455353005f474e445f54454d50005f414c545f4f4646534554005f4558545f425553005f535045435f4752415600325f474e445f505245535300335f474e445f5052455353005f464c54525f524e4700315f444556494400325f444556494400335f4445564944005f4649454c445f454c56005f414c544552525f4d4158004261726f3a20736b697070696e672063616c6962726174696f6e206166746572205744472072657365740043616c6962726174696e67206261726f6d65746572004261726f3a20756e61626c6520746f2063616c696272617465004261726f6d657465722025752063616c6962726174696f6e20636f6d706c657465004261726f3a20616c6c2073656e736f727320756e63616c6962726174656400546f6f206d616e79206261726f6d657465722064726976657273004e6f205349544c20706f696e746572004661696c656420746f20536574204669656c6420456c65766174696f6e3a2041726d6564004669656c6420456c65766174696f6e205365743a20252e30666d00546f6f206d616e79206261726f6d6574657273006e6f74206865616c7468790047505320616c74206572726f7220252e30666d2028736565204241524f5f414c544552525f4d41582900564f4c545f50494e00435552525f50494e00564f4c545f4d554c5400414d505f504552564c5400414d505f4f464653455400564c545f4f4646534554004e6f20616e616c6f6720766f6c74616765206368616e6e656c20666f722062617474657279202564004e6f20616e616c6f672063757272656e74206368616e6e656c20666f7220626174746572792025640062656c6f77206d696e696d756d2061726d696e6720766f6c746167650062656c6f77206d696e696d756d2061726d696e6720636170616369747900637269746963616c20766f6c74616765206661696c7361666500637269746963616c206361706163697479206661696c73616665006c6f7720766f6c74616765206661696c73616665006c6f77206361706163697479206661696c73616665006361706163697479206661696c7361666520637269746963616c203e3d206c6f7700766f6c74616765206661696c7361666520637269746963616c203e3d206c6f77005f0041505f426174744d6f6e69746f72206d7573742062652073696e676c65746f6e006d697373696e672c206c6173743a006c6f7700637269746963616c004261747465727920256420697320257320252e326656207573656420252e3066206d41680042617474657279202564202573006665617475726520424154544552595f53554d206e6f7420617661696c61626c6500756e6865616c7468790056656869636c65202575206261747465727920256420697320706f776572696e67206f6666004d4f4e49544f5200434150414349545900574154545f4d4158004c4f575f54494d45520046535f564f4c54535243004c4f575f564f4c54004c4f575f4d4148004352545f564f4c54004352545f4d41480046535f4c4f575f4143540046535f4352545f4143540041524d5f564f4c540041524d5f4d414800466f7263696e6720736166657479206f666620666f72207761746368646f6700534552315f52545343545300534552325f52545343545300534552335f52545343545300534552345f52545343545300534552355f52545343545300534552365f52545343545300534552375f52545343545300534552385f525453435453005341464554595f4445464c540053455249414c5f4e554d005341464554595f4d41534b005341464554594f5054494f4e0052544300564255535f4d494e0056534552564f5f4d494e00424f4f545f44454c41590053445f4d495353494f4e0053445f46454e43450025733a2025730a00556e61626c6520746f20616c6c6f6361746520257300416c6c6f636174696f6e204572726f7200436f6e666967204572726f72007465727261696e206c6f63206d7573742062652072656c61746976655f616c74310053686f756c64206e6f742062652063616c6c6564206f6e20696e76616c6964206c6f636174696f6e3a204c6f636174696f6e2063616e6e6f742062652028302c20302c203029007465727261696e206c6f63206d7573742062652072656c61746976655f616c7432004f46530044454300555345004155544f444543004d4f544354004d4f54004f5249454e540045585445524e414c004f465332004d4f5432004f465333004d4f5433004445565f4944004445565f494432004445565f4944330055534532004f5249454e54320045585445524e320055534533004f5249454e54330045585445524e3300444941004f44490044494132004f4449320044494133004f444933004f4646535f4d415800504d4f5400444953424c4d534b00464c54525f524e47005052494f315f4944005052494f325f4944005052494f335f494400454e41424c45005343414c45005343414c4532005343414c4533004445565f494434004445565f494435004445565f494436004445565f494437004445565f49443800436f6d70617373206d7573742062652073696e676c65746f6e004e6f20436f6d70617373206261636b656e647320617661696c61626c650a00436f6d70617373202564206e6f7420666f756e6400436f6d70617373206f72646572206368616e6765207265717569726573207265626f6f7400436f6d70617373206e6f742063616c69627261746564005f454e005f455850005f4e415646494c544552005f4155544f5f535749544348005f534241535f4d4f4445005f4d494e5f454c4556005f494e4a4543545f544f005f5241575f44415441005f534156455f434647005f4155544f5f434f4e464947005f4452565f4f5054494f4e53005f5052494d4152590041505f475053206d7573742062652073696e676c65746f6e00475053315f5459504500475053325f5459504500475053315f474e53535f4d4f444500475053325f474e53535f4d4f444500475053315f524154455f4d5300475053325f524154455f4d5300475053315f504f5300475053325f504f5300475053315f44454c41595f4d5300475053325f44454c41595f4d53004750532025643a206465746563746564202573004750532025643a20776173206e6f7420666f756e64004750535b25755d20796177206e6f7420617661696c61626c65005459504500474e53535f4d4f444500524154455f4d5300504f530044454c41595f4d53004750532025643a2070726f62696e6720666f722025732061742025642062617564004750532025643a20737065636966696564206173202573004e6f7420656e6f75676820636865636b65642072656769737465727320666f722072656720307825303278206f6e2064657669636520307825780a00696e66006e616e005f4759524f464653005f475952324f464653005f475952334f464653005f4143435343414c005f4143434f464653005f414343325343414c005f414343324f464653005f414343335343414c005f414343334f464653005f4759524f5f46494c544552005f414343454c5f46494c544552005f555345005f55534532005f55534533005f5354494c4c5f544852455348005f4759525f43414c005f5452494d5f4f5054494f4e005f4143435f424f4459464958005f504f5331005f504f5332005f504f5333005f4759525f4944005f475952325f4944005f475952335f4944005f4143435f4944005f414343325f4944005f414343335f4944005f464153545f53414d504c45005f454e41424c455f4d41534b005f4759524f5f52415445005f5241575f4c4f475f4f505400546f6f206d616e7920696e65727469616c2073656e736f7273004661696c656420746f207265676973746572206779726f206964202575004661696c656420746f20726567697374657220616363656c20696420257500546f6f206d616e7920494e53206261636b656e6473005472696d204f4b3a20726f6c6c3d252e32662070697463683d252e3266207961773d252e3266007472696d206f766572206d6178696d756d206f662031302064656772656573004779726f2025642072617465202564487a203c206c6f6f7020726174652a312e38202564487a00496e6974204779726f002a006779726f5b25755d20646964206e6f7420636f6e76657267653a20646966663d25662064707320286578706563746564203c202566290a004552523a205472696d206f766572206d6178696d756d206f6620252e316620646567726565732121000a5041535345440a000a4641494c45440a00546f6f2062696720616e206172656120746f2066696c6c0053706c696e6543757276653a3a63616c635f64745f73706565645f6d61782076656c2c20616363656c20616e64206a65726b2061726520616c6c207a65726f0a0053706c696e6543757276653a3a63616c635f64745f73706565645f6d61782074616e67656e7469616c5f73706565645f6d6178206973207a65726f0a0053706c696e6543757276653a3a63616c635f64745f73706565645f6d617820616363656c5f6d6178206973207a65726f0a005343757276653a3a67656e65726174655f706174682063726561746564207a65726f206c656e67746820706174680a005343757276653a3a67656e65726174655f7061746820696e76616c696420706174680a005343757276653a3a7365745f73706565645f6d617820696e76616c696420706174680a005343757276653a3a7365745f6f726967696e5f73706565645f6d617820696e76616c696420706174680a005343757276653a3a7365745f64657374696e6174696f6e5f73706565645f6d617820696e76616c696420706174680a005343757276653a3a2041726320726164697573206973206e65676174697665206f72207a65726f0a005343757276653a3a63616c63756c6174655f7061746820696e76616c696420696e707574730a005343757276653a3a63616c63756c6174655f7061746820696e76616c6964206f7574707574730a006e756d5f736567733a25752c2074696d653a25342e32662c20736e61705f6d61783a25342e32662c206a65726b5f6d61783a25342e32662c20616363656c5f6d61783a25342e32662c2076656c5f6d61783a25342e32660a00542c204a742c204a2c20412c20562c2050200a00693a25752c20543a25342e32662c204a747970653a25342e32662c204a3a25342e32662c20413a25342e32662c20563a2025342e32662c20503a2025342e32660a00747261636b20783a25342e32662c20793a25342e32662c207a3a25342e32660a006172635f63656e7465725f6e6520783a25342e32662c20793a25342e32660a00526573756d652072657065617420646973742073657420746f202575206d00544f54414c0052455354415254004f5054494f4e53006d697373696f6e2e73746700436c656172696e67204d697373696f6e004d697373696f6e3a202575202573202575004d697373696f6e3a202575202573004d6179206e6f742073746f7265206c6f636174696f6e20666f722031362d62697420636f6d6d616e6473004d697373696f6e3a2052657475726e656420746f20696e746572727570746564205750004d697373696f6e3a202575204a756d702025692f756e6c696d69746564004d697373696f6e3a202575204a756d702025692f2569004c616e64696e672073657175656e636520737461727400556e61626c6520746f207374617274206c616e64696e672073657175656e6365004c616e64696e672073657175656e6365206163746976650052657475726e2070617468206163746976650052657475726e207061746820737461727465640057500053706c696e655750004172635750004c6f6974556e6c696d004c6f697454696d6500477569646564456e61626c65004c6f69745475726e73004c6f6974416c7469747564650053657459617753706400436f6e6444656c617900436f6e6444697374004368616e6765537065656400536574486f6d6500536574536572766f0053657452656c617900526570656174536572766f0052657065617452656c6179004469676943616d436667004469676943616d4374726c0053657443616d5472696744737400536574524f494c6f636174696f6e00536574524f494e6f6e6500536574524f4900536574526576657273650053657452657065617444697374004775696465644c696d6974730054616b656f666600436f6e74696e7565416e644368616e6765416c7400416c746974756465576169740056544f4c54616b656f66660056544f4c4c616e6400496e766572746564466c696768740046656e6365456e61626c65004175746f54756e65456e61626c650056544f4c5472616e736974696f6e00456e67696e65436f6e74726f6c00436f6e645961770052657475726e506174685374617274004c616e6453746172740044656c61790050617261636875746500537072617965720041757846756e6374696f6e004d6f756e74436f6e74726f6c0057696e636800536372697074696e67004a756d70004a756d70546f5461670054616700476f2041726f756e64004e6176417474697475646554696d65005061757365436f6e74696e75650047696d62616c506974636859617700496d61676553746172744361707475726500496d61676553746f70436170747572650053657443616d6572615a6f6f6d0053657443616d657261466f6375730053657443616d657261536f7572636500566964656f53746172744361707475726500566964656f53746f704361707475726500524f4957504e6578744f6666736574004d697373696f6e20636f6d6d616e64207769746820494420257520686173206e6f20737472696e6700315f504f53585900315f56454c585900315f504f535a00315f56454c5a00315f59415700325f504f53585900325f56454c585900325f504f535a00325f56454c5a00325f59415700335f504f53585900335f56454c585900335f504f535a00335f56454c5a00335f59415700436865636b20454b335f53524325645f504f53585900436865636b20454b335f53524325645f56454c585900436865636b20454b335f53524325645f504f535a00436865636b20454b335f53524325645f56454c5a00436865636b20454b335f53524325645f59415700454b3320736f75726365732072657175697265202573004261726f00426561636f6e00436f6d70617373004f70746963616c466c6f770052616e676546696e6465720056697375616c4f646f6d00576865656c456e636f6465720056454c4e455f4d5f4e53450056454c445f4d5f4e53450056454c5f495f4741544500504f534e455f4d5f4e534500504f535f495f4741544500474c495443485f52414400414c545f4d5f4e5345004847545f495f47415445004847545f44454c4159004d41475f4d5f4e5345004d41475f43414c004d41475f495f47415445004541535f4d5f4e5345004541535f495f4741544500524e475f4d5f4e534500524e475f495f4741544500464c4f575f4d415800464c4f575f4d5f4e534500464c4f575f495f4741544500464c4f575f44454c4159004759524f5f505f4e5345004143435f505f4e53450047424941535f505f4e53450041424941535f505f4e53450057494e445f505f4e53450057494e445f505343414c45004750535f434845434b00494d555f4d41534b00434845434b5f5343414c45004e4f4149445f4d5f4e534500424554415f4d41534b005941575f4d5f4e5345005941575f495f47415445005441555f4f5554505554004d4147455f505f4e5345004d4147425f505f4e534500524e475f5553455f48475400544552525f475241440042434e5f4d5f4e53450042434e5f495f4754450042434e5f44454c415900524e475f5553455f535044004143435f424941535f4c494d004d41475f4d41534b004f474e5f4847545f4d41534b005649535f564552525f4d494e005649535f564552525f4d41580057454e435f5645525200464c4f575f555345004852545f46494c54004d41475f45465f4c494d004753465f52554e5f4d41534b004753465f5553455f4d41534b00464c4f575f4741494e5f48004753465f5253545f4d4158004552525f54485245534800414646494e4954590053524300445241475f42434f45465f5800445241475f42434f45465f5900445241475f4d5f4e534500445241475f4d434f4546004f474e4d5f544553545f534600474e445f4546465f445a005052494d415259004c4f475f4c4556454c004750535f564143435f4d415800454b4633206e6f7420656e6f756768206d656d6f727900454b463320616c6c6f636174696f6e206661696c656400454b4633206c616e652073776974636820257500454b335f4d41475f43414c20616e6420454b335f535243315f59415720696e636f6e73697374656e74006e6f20454b463320636f72657300454b463320636f726520256420756e6865616c74687900454b46333a206f726967696e20616c72656164792073657400454b463320494d5525752073746f7070656420616964696e6700454b463320494d55257520737461727465642072656c617469766520616964696e6700454b463320494d552575206973207573696e672047505300454b463320494d5525752074696c7420616c69676e6d656e7420636f6d706c65746500454b463320494d552575206f726967696e2073657400454b463320494d552575204d4147257520696e697469616c2079617720616c69676e6d656e7420636f6d706c65746500454b463320494d552575204d4147257520696e2d666c696768742079617720616c69676e6d656e7420636f6d706c65746500454b463320494d552575204d414725752067726f756e64206d616720616e6f6d616c792c207961772072652d616c69676e656400454b463320494d5525752079617720616c69676e656420746f204750532076656c6f6369747900454b463320494d5525752079617720616c69676e656400454b463320494d552575207961772065787465726e616c00454b463320494d552575207961772066616c6c6261636b2061637469766500454b463320494d5525752079617720616c69676e6564207573696e672047505300454b463320494d55257520656d657267656e63792079617720726573657400454b463320494d55257520737769746368696e6720746f20636f6d706173732025750057616974696e6720666f722033442066697800454b46335b25755d2076656c206572726f7220252e316600454b463320494d55257520667573696e67206f646f6d657472790047505320647269667420252e31666d20286e6565647320252e3166290047505320766572746963616c20737065656420252e32666d2f7320286e6565647320252e3266290047505320686f72697a6f6e74616c20737065656420252e32666d2f7320286e6565647320252e3266290047505320686f72697a206572726f7220252e31666d20286e6565647320252e316629004750532076657274206572726f7220252e31666d20286e65656473203c20252e31662900475053207370656564206572726f7220252e316620286e65656473203c20252e316629004750532048444f5020252e316620286e6565647320322e352900475053206e756d7361747320257520286e65656473203629004d616720796177206572726f7220783d252e316620793d252e316600454b46207374617274696e672047505320636865636b7300454b46332077616974696e6720666f722047505320636f6e666967206461746100454b463320494d552575204753463a206e6f7420656e6f756768206d656d6f727900454b463320494d5525754753463a20616c6c6f636174696f6e206661696c656400454b4633207374696c6c20696e697469616c6973696e6700454b463320696e6974206661696c7572653a204e6f20475053206c6f636b00454b463320494d55257520696e697469616c6973656400454b463320494d55257520666f72636564207265736574004c45445f4252494748540042555a5a5f5459504553004c45445f4f564552524944450042555a5a5f50494e004c45445f54595045530042555a5a5f4f4e5f4c564c0042555a5a5f564f4c554d45004c45445f4c454e0041505f4e6f74696679206d7573742062652073696e676c65746f6e002e0042616420706172616d65746572207461626c6500454550524f4d2066756c6c0a004c6f616465642064656661756c74732066726f6d2025730a004661696c656420746f206c6f61642064656661756c74732066726f6d202573004552524f523a20556e61626c6520746f2066696e6420706172616d20706f696e7465720a00556e6b6e6f776e20636f6e76657273696f6e20272573270a0042616420636f6e76657273696f6e207479706520272573270a002c203d090d0a005761726e696e673a2049676e6f72696e6720464f524d41545f56455253494f4e20696e20706172616d2066696c650a0040524541444f4e4c590041505f506172616d3a204661696c656420746f2072652d6f70656e2064656661756c74732066696c650041505f506172616d3a204661696c656420746f20616c6c6f63617465206d757461626c6520737472696e67002c0041505f506172616d3a204661696c656420746f20616c6c6f63617465206f766572726964657300556e61626c6520746f20616c6c6f63617465207363686564756c6572205461736b496e666f0a004445425547004c4f4f505f5241544500546f6f206d616e79207363686564756c657273005363686564756c6572206f76657272756e207461736b5b25752d25735d202825752f2575290a00305f4241554400305f50524f544f434f4c00315f50524f544f434f4c00315f4241554400325f50524f544f434f4c00325f4241554400335f50524f544f434f4c00335f4241554400345f50524f544f434f4c00345f4241554400355f50524f544f434f4c00355f4241554400365f50524f544f434f4c00365f4241554400315f4f5054494f4e5300325f4f5054494f4e5300335f4f5054494f4e5300345f4f5054494f4e5300355f4f5054494f4e5300365f4f5054494f4e53005f5041535331005f5041535332005f5041535354494d4f00375f50524f544f434f4c00375f4241554400375f4f5054494f4e5300556e61626c6520746f207365747570206f7074696f6e7320666f722053657269616c25750a0053455249414c25755f4f5054494f4e53206269742031302028276e6f20666f7277617264206d61766c696e6b2729206d757374206e6f74206265207365743b20757365204d41566e5f4f5054494f4e5320626974203120696e73746561640053455249414c25755f4f5054494f4e53206269742031322028276e6f2073747265616d206f76657272696465732729206d757374206e6f74206265207365743b20757365204d41566e5f4f5054494f4e5320626974203220696e7374656164004669726d77617265206368616e67653a2065726173696e6720454550524f4d2e2e2e0a00646f6e652e0a00464c544d4f44455f474353424c4f434b0053455249414c000a0a496e69742025730a0a467265652052414d3a2025750a004172647550696c6f7420526561647900496e7465726e616c204572726f727320307825780041505f4e6f746966793a3a7570646174650041505f56656869636c653a3a73656e645f7761746368646f675f72657365745f737461747573746578740041505f56656869636c653a3a6f6e655f487a5f7570646174650041505f56656869636c653a3a7570646174655f61726d696e6700436f6e666967204572726f723a206669782070726f626c656d207468656e207265626f6f7400496e697469616c6973696e67204172647550696c6f74005744473a2054256420534c257520464c25752046542575204641257820465450257520464c5225782046494353522575204d4d2575204d432575204945257520494543257520544e3a252e3473004e6f2073756368206d6f6465202575002c2573006d61706661696c757265006d6973735f7374727563740077726974655f6d7373666d74006d616e795f64656c65746573006261645f67657466696c650070616e696300666c7573685f6e6f5f73656d006261645f637572725f626c6b00626c6b636e745f6261640064715f6661696c75726500636e737472696e675f6e616e007761746368646f675f72737400696f6d63755f726573657400696f6d63755f6661696c007370695f6661696c006d61696e5f6c6f6f705f73746b006763735f6261645f6c696e6b006269746d61736b5f72616e6765006763735f6f6666736574006932635f69737200666c6f775f6f665f6374726c007366735f726563757273696f6e006261645f726f746174696f6e00737461636b5f6f7672666c7700696d755f7265736574006770696f5f697372006d656d5f677561726400646d615f6661696c00706172616d735f726573746f72656400696e76616c696420617267756d656e74730053686f7274207772697465206f6e20554152543a20256c75203c20257500506172616d2077726974652064656e6965642028257329005369676e696e67206973206e6f7420656e61626c656420696e2074686973206669726d7761726500506173736564207061636b6574206d657373616765206c656e67746820282575203e20257529004e656564206d61766c696e6b3220666f72206974656d207472616e73666572004f6e6c79202575206974656d732061726520737570706f7274656400676f74204d495353494f4e5f524551554553543b20757365204d495353494f4e5f524551554553545f494e542100676f74204d495353494f4e5f4954454d3b204743532073686f756c642073656e64204d495353494f4e5f4954454d5f494e5400466c6967687420706c616e207570646174652072656a656374656400466c6967687420706c616e207265636569766564004d697373696f6e2075706c6f61642074696d656f7574005f5359534944005f4743535f5359534944005f4743535f53595349445f4849005f54454c454d5f44454c4159003100320033003400350036003700380039003130003131003132003133003134003135003136004e6f2061705f6d65737361676520666f72206d61766c696e6b2069642028257529006e6578745f64656665727265645f6275636b65745f6d6573736167655f746f5f73656e642063616c6c6564206f6e20656d707479206275636b6574004275636b657420257520686173207a65726f20696e74657276616c2062757420776974682069647320736574006e6f206275636b6574733f210a004661696c656420746f20637265617465204d41564c696e6b20636f6e736f6c65206261636b656e64004661696c656420746f20637265617465204d41564c696e6b206261636b656e6420257500526571756573746564207261746520666f72206d65737361676520494420257520746f6f20666173742e20496e6372656173652053434845445f4c4f4f505f524154450025733a2025732025733a202573005570646174696e67206261726f6d657465722063616c6962726174696f6e004261726f6d657465722063616c6962726174696f6e20636f6d706c6574650044697361726d20746f20616c6c6f772063616c6962726174696f6e00416c6c20706172616d65746572732072657365742c207265626f6f7420626f6172640053656e64696e6720756e6b6e6f776e206d65737361676520282575290053656e64696e6720756e6b6e6f776e2061705f6d6573736167652025750020000d0a0040524f4d46532f6d6573736167652d696e74657276616c732d6368616e25752e747874006d6573736167652d696e74657276616c732d6368616e25752e74787400506173737468727520656e61626c65640050617373746872752064697361626c65640050617373746872752074696d6564206f757400556e6b6e6f776e206d61766c696e6b20636f6f7264696e617465206672616d65202575005f5241575f53454e53005f4558545f53544154005f52435f4348414e005f5241575f4354524c005f504f534954494f4e005f455854524131005f455854524132005f455854524133005f504152414d53005f41445342005f4f5054494f4e53434e56005f44455649440052435f4368616e6e656c73206d7573742062652073696e676c65746f6e005243206f766572726964657320636c65617265642062792070696c6f7420696e707574004d494e005452494d004d415800524556455253454400445a004f5054494f4e004661696c656420746f20696e69743a20524325755f4f5054494f4e3a2025750053617665576179706f696e74004d697373696f6e5265736574004d6f746f724553746f70004d6f746f72496e7465726c6f636b00507265636973696f6e4c6f697465720041766f696450726f78696d69747900436c656172576179706f696e7400436f6d706173734c6561726e005361696c626f61745461636b0047505344697361626c650047505344697361626c65596177005361696c626f61744d6f746f720053757266616365547261636b696e67004169724d6f64650042617474657279204d50505420456e61626c6500456d657267656e6379204c616e64696e67005765617468657276616e650054757262696e6520537461727400464654204e6f7463682054756e696e670048494748004d4944444c45004c4f5700524325693a202573202573005573696e6720454b4620536f757263652053657420257500454b462072657365742069676e6f7265643a2076656869636c652061726d656400454b4620626f6f74737472617020726573657420706572666f726d656400454b4620626f6f747374726170207265736574206661696c656400496e76616c6964206368616e6e656c206f7074696f6e20282575290046554e4354494f4e004368616e6e656c20257520616c72656164792061737369676e65642066756e6374696f6e2025750a005f4155544f5f5452494d005f52415445005f4453484f545f52415445005f4453484f545f455343005f4750494f5f4d41534b005f52435f46535f4d534b005f33325f454e41424c450031375f0031385f0031395f0032305f0032315f0032325f0032335f0032345f0032355f0032365f0032375f0032385f0032395f0033305f0033315f0033325f0053746f726167654d616e616765723a206572617365206661696c65640a0053746f7261676546696c65004d697373696f6e2073746f72616765206661696c6564004d697373696f6e2073746f72616765204f4b006175746f746573745f66697874757265732e747874006175746f746573745f66697874757265732f6c6f6e675f6e616d65732f6464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464642f66696c65006175746f746573745f66697874757265732f6c6f6e675f6e616d65732f666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666006175746f746573745f66697874757265732f6e65737465642f7375622e747874006175746f746573745f66697874757265732f6e65737465642f7375622f66696c650064656661756c745f706172616d732f61697273696d2d71756164582e7061726d0064656661756c745f706172616d732f61697273696d2d726f7665722e7061726d0064656661756c745f706172616d732f61702d63616d65726167696d62616c2e7061726d0064656661756c745f706172616d732f62616c616e6365626f742e7061726d0064656661756c745f706172616d732f626c696d702d6d6f746f722e7061726d0064656661756c745f706172616d732f626c696d702e7061726d0064656661756c745f706172616d732f636f707465722d582e7061726d0064656661756c745f706172616d732f636f707465722d626561636f6e2e7061726d0064656661756c745f706172616d732f636f707465722d6266782e7061726d0064656661756c745f706172616d732f636f707465722d636f61782e7061726d0064656661756c745f706172616d732f636f707465722d6377782e7061726d0064656661756c745f706172616d732f636f707465722d646563612d6377782e7061726d0064656661756c745f706172616d732f636f707465722d646563612e7061726d0064656661756c745f706172616d732f636f707465722d646a69782e7061726d0064656661756c745f706172616d732f636f707465722d646f64656361686578612e7061726d0064656661756c745f706172616d732f636f707465722d646f74726961636f6e74615f6f637461717561645f782e7061726d0064656661756c745f706172616d732f636f707465722d67696d62616c2e7061726d0064656661756c745f706172616d732f636f707465722d6770732d666f722d7961772d6e6d65612e7061726d0064656661756c745f706172616d732f636f707465722d6770732d666f722d7961772e7061726d0064656661756c745f706172616d732f636f707465722d68656c692d646466707461696c2e7061726d0064656661756c745f706172616d732f636f707465722d68656c692d646476707461696c2e7061726d0064656661756c745f706172616d732f636f707465722d68656c692d6475616c2e7061726d0064656661756c745f706172616d732f636f707465722d68656c692d6761732e7061726d0064656661756c745f706172616d732f636f707465722d68656c692e7061726d0064656661756c745f706172616d732f636f707465722d68656c69717561642e7061726d0064656661756c745f706172616d732f636f707465722d686578612d6377782e7061726d0064656661756c745f706172616d732f636f707465722d686578612d646a692e7061726d0064656661756c745f706172616d732f636f707465722d686578612e7061726d0064656661756c745f706172616d732f636f707465722d68657861646563615f6f6374612e7061726d0064656661756c745f706172616d732f636f707465722d68657861646563615f6f6374615f6377782e7061726d0064656661756c745f706172616d732f636f707465722d6f6374612d6377782e7061726d0064656661756c745f706172616d732f636f707465722d6f6374612d646a692e7061726d0064656661756c745f706172616d732f636f707465722d6f6374612e7061726d0064656661756c745f706172616d732f636f707465722d6f637461717561642d636f722e7061726d0064656661756c745f706172616d732f636f707465722d6f637461717561642d63772d636f722e7061726d0064656661756c745f706172616d732f636f707465722d6f637461717561642d6377782e7061726d0064656661756c745f706172616d732f636f707465722d6f637461717561642e7061726d0064656661756c745f706172616d732f636f707465722d6f7074666c6f772e7061726d0064656661756c745f706172616d732f636f707465722d7070702d7065726970682e7061726d0064656661756c745f706172616d732f636f707465722d7070702e7061726d0064656661756c745f706172616d732f636f707465722d72616e676566696e6465722e7061726d0064656661756c745f706172616d732f636f707465722d73696e676c652e7061726d0064656661756c745f706172616d732f636f707465722d7472692e7061726d0064656661756c745f706172616d732f636f707465722d7669636f6e2e7061726d0064656661756c745f706172616d732f636f707465722d77696e63682e7061726d0064656661756c745f706172616d732f636f707465722d77696e642d657374696d617465732e7061726d0064656661756c745f706172616d732f636f707465722d79362e7061726d0064656661756c745f706172616d732f636f707465722e7061726d0064656661756c745f706172616d732f66697265666c792e7061726d0064656661756c745f706172616d732f67617a65626f2d697269732e7061726d0064656661756c745f706172616d732f67617a65626f2d7a65706879722e7061726d0064656661756c745f706172616d732f676c696465722e7061726d0064656661756c745f706172616d732f6d6f746f72626f61742e7061726d0064656661756c745f706172616d732f6d73706f73642e7061726d0064656661756c745f706172616d732f7065726970682d626174746d6f6e2e7061726d0064656661756c745f706172616d732f7065726970682d636f6d706173732e7061726d0064656661756c745f706172616d732f7065726970682d7070702e7061726d0064656661756c745f706172616d732f7065726970682e7061726d0064656661756c745f706172616d732f706c616e652d6473706f696c6572732e7061726d0064656661756c745f706172616d732f706c616e652d656c65766f6e732e7061726d0064656661756c745f706172616d732f706c616e652d6963652e7061726d0064656661756c745f706172616d732f706c616e652d6a65742e7061726d0064656661756c745f706172616d732f706c616e652d726564756e64616e742e7061726d0064656661756c745f706172616d732f706c616e652d736f6172696e672e7061726d0064656661756c745f706172616d732f706c616e652d7461696c7369747465722e7061726d0064656661756c745f706172616d732f706c616e652d767461696c2e7061726d0064656661756c745f706172616d732f717561642d63616e2e7061726d0064656661756c745f706172616d732f717561642d7065726970682e7061726d0064656661756c745f706172616d732f71756164706c616e652d63616e2e7061726d0064656661756c745f706172616d732f71756164706c616e652d636c38342e7061726d0064656661756c745f706172616d732f71756164706c616e652d636f707465725f7461696c7369747465722e7061726d0064656661756c745f706172616d732f71756164706c616e652d6963652e7061726d0064656661756c745f706172616d732f71756164706c616e652d7065726970682e7061726d0064656661756c745f706172616d732f71756164706c616e652d7070702d7065726970682e7061726d0064656661756c745f706172616d732f71756164706c616e652d7070702e7061726d0064656661756c745f706172616d732f71756164706c616e652d74696c742e7061726d0064656661756c745f706172616d732f71756164706c616e652d74696c74687665632e7061726d0064656661756c745f706172616d732f71756164706c616e652d74696c747472692e7061726d0064656661756c745f706172616d732f71756164706c616e652d74696c747472697665632e7061726d0064656661756c745f706172616d732f71756164706c616e652d7472692e7061726d0064656661756c745f706172616d732f71756164706c616e652e7061726d0064656661756c745f706172616d732f726f7665722d6f6d6e69336d6563616e756d2e7061726d0064656661756c745f706172616d732f726f7665722d736b69642e7061726d0064656661756c745f706172616d732f726f7665722d766563746f7265642e7061726d0064656661756c745f706172616d732f726f7665722e7061726d0064656661756c745f706172616d732f7361696c626f61742d6d6f746f722e7061726d0064656661756c745f706172616d732f7361696c626f61742e7061726d0064656661756c745f706172616d732f73747261746f626c696d702e7061726d0064656661756c745f706172616d732f7375622d36646f662e7061726d0064656661756c745f706172616d732f7375622d6770732d666f722d7961772d6e6d65612e7061726d0064656661756c745f706172616d732f7375622e7061726d0064656661756c745f706172616d732f747261636b65722d6770732d666f722d7961772e7061726d006c6f636174696f6e732e747874006d6f64656c732f43616c6c6973746f2e6a736f6e006d6f64656c732f43616c6c6973746f2e7061726d006d6f64656c732f667265657374796c652e6a736f6e006d6f64656c732f667265657374796c652e7061726d006d6f64656c732f68656c69717561642e6a736f6e006d6f64656c732f6d7431315f746865726d616c2e68323634006d6f64656c732f6d7431315f76697369626c652e68323634006d6f64656c732f706c616e652d33642e7061726d006d6f64656c732f706c616e652d726576657273652d72632d70697463682d7961772e7061726d006d6f64656c732f706c616e652d726576657273652d736572766f2d70697463682d7961772e7061726d006d6f64656c732f706c616e652e7061726d006d6f64656c732f736b7977616c6b65725f323031332e6a736f6e006d6f64656c732f78706c616e655f68656c692e6a736f6e006d6f64656c732f78706c616e655f706c616e652e6a736f6e0076656869636c65696e666f2e6a736f6e005f5459504553005f545a5f4d494e0040524f4d4653002f00500049004400464600494d415800464c545400464c544500464c544400534d41580050444d5800445f464600524551554952450041434354485245534800525544444552004d49535f4954454d53004d4147544852455348004e4545445f4c4f4300534b495043484b00546f6f206d616e792041505f41726d696e6720696e7374616e6365730050726541726d3a2025730041726d3a202573004261726f3a202573004779726f73206e6f74206865616c746879004779726f73206e6f742063616c6962726174656400416363656c73206e6f74206865616c74687900334420416363656c2063616c6962726174696f6e206e656564656400416363656c732063616c69627261746564207265717569726573207265626f6f7400416363656c7320696e636f6e73697374656e74004779726f7320696e636f6e73697374656e740074656d70657261747572652063616c2072756e6e696e6700436f6d70617373206f66667365747320746f6f206869676800436865636b206d6167206669656c643a2025342e30662c206d61782025642c206d696e20256400436f6d70617373657320696e636f6e73697374656e7400436865636b206d6167206669656c642028787920646966663a252e30663e25642900436865636b206d6167206669656c6420287a20646966663a252e30663e256429004750532025693a207072696d6172792062757420545950452030004750532025693a2042616420666978004750532025693a206e6f74206865616c74687900414852533a2077616974696e6720666f7220686f6d650047505320706f736974696f6e73206469666665722062792025342e31666d0047505320616e642041485253206469666665722062792025342e31666d00475053202564207374696c6c20636f6e6669677572696e6720746869732047505300526f6c6c00506974636800257320285243256429206973206e6f74206e65757472616c0056544f4c20467764205468726f74746c65206973206e6f74207a65726f004475706c69636174652041757820537769746368204f7074696f6e73004d6f6465206368616e6e656c20616e6420524325645f4f5054494f4e20636f6e666c69637400524325645f4d494e2069732067726561746572207468616e20524325645f5452494d00524325645f4d4158206973206c657373207468616e20524325645f5452494d0052432063616c6962726174696e6700526164696f206661696c73616665206f6e006c616e640076746f6c206c616e6400646f206c616e642073746172740074616b656f66660076746f6c2074616b656f6666004d697373696e67206d697373696f6e206974656d3a202573004e6f2072616c6c79206c6962726172792070726573656e74004d697373696f6e3a205a65726f2074616b656f666620616c746974756465004661696c656420746f206f70656e202573004d6f6465207265717569726573206d697373696f6e00534552564f25645f4d494e2069732067726561746572207468616e20534552564f25645f5452494d00534552564f25645f4d4158206973206c657373207468616e20534552564f25645f5452494d00534552564f25755f46554e4354494f4e3d2575206f6e2064697361626c6564206368616e6e656c00426f617264202825312e31667629206f7574206f662072616e67652025312e31662d25312e31667600536572766f20766f6c7461676520746f206c6f77202825312e326676203c2025312e3266762900506172616d2073746f72616765206661696c656400706172616d657465722073746f726167652066756c6c004d61696e206c6f6f7020736c6f7720282575487a203c202575487a2900496e7465726e616c206572726f72732030782578206c3a2575202573007465727261696e207265717569726564206275742064697361626c656400506963636f6c6f43414e206e6f7420656e61626c65640053616d652072666e64206f6e20646966666572656e742043414e20706f727473004d756c7469706c652053455249414c20706f72747320636f6e6669677572656420666f7220524320696e707574004d6f746f727320456d657267656e63792053746f70706564004750535f4155544f5f5357495443483d3d3220627574206e6f20626c656e64696e67005761726e696e673a2041726d696e6720436865636b732044697361626c65640044697361726d3a207275646465722064697361726d2064697361626c656400257320726164696f206d696e20746f6f206869676800257320726164696f206d617820746f6f206c6f770044697361726d20537769746368206f6e00524f4c4c005049544348005448524f54544c450059415700464f5257415244004c41544552414c0052434d6170706572206d7573742062652073696e676c65746f6e004452495645520042495452415445004644424954524154450050315f0050325f0044315f0044325f004c4f474c4556454c0041505f43414e4d616e61676572206d7573742062652073696e676c65746f6e0043414e4d616e616765723a205349544c206e6f7420696e697469616c6973656421004d6178206e756d626572206f662043414e20447269766572732065786365656465640a0d0043414e4d616e616765722075736564206265666f726520616c6c6f636174696f6e2e0050524f544f434f4c0050524f544f434f4c32005241545f524c4c5f005241545f5049545f005241545f5941575f005448525f4d49585f4d494e005448525f4d49585f4d4158005448525f4d49585f4d414e005448525f475f424f4f53540052415445004558504f00524154455f544300524154455f46465f454e414200414e474c455f424f4f535400414e475f524c4c5f00414e475f5049545f00414e475f5941575f00414e475f4c494d5f544300524154455f525f4d415800524154455f505f4d415800524154455f595f4d415800494e5055545f5443004c414e445f525f4d554c54004c414e445f505f4d554c54004c414e445f595f4d554c5400414e474c455f4d415800524154455f5750595f4d4158004143435f595f4d4158004143435f525f4d4158004143435f505f4d4158004154435f414e474c455f4d4158004154435f524154455f5750595f4d4158004154435f4143435f595f4d4158004154435f4143435f525f4d4158004154435f4143435f505f4d415800414e475f50495400414e475f524c4c00414e475f5941570025735f25735f50206d757374206265203e2030005241545f524c4c005241545f504954005241545f5941570025735f25735f50206d757374206265203e3d20300025735f25735f49206d757374206265203e3d20300025735f25735f49206d757374206265203e20300025735f25735f44206d757374206265203e3d20300025735f414e474c455f4d4158206d757374206265203e3d20313020616e64203c3d20383000726174655f636f6e74726f6c6c65725f72756e5f64742829206d75737420626520646566696e6564005f445f504f535f005f4e455f504f535f005f414e474c455f4d4158005f4e455f4a45524b005f445f4a45524b005f445f56454c5f005f445f4143435f005f4e455f56454c5f0025735f4e455f504f535f50206d757374206265203e20300025735f445f504f535f50206d757374206265203e20300025735f445f56454c5f50206d757374206265203e20300025735f445f4143435f50206d757374206265203e20300025735f445f4143435f49206d757374206265203e2030005053435f445f56454c5f50005053435f445f56454c5f49005053435f445f56454c5f44005053435f445f56454c5f464c5445005053435f445f56454c5f464c5444005053435f445f56454c5f4646005053435f445f4143435f4646005053435f445f4143435f464c5454005053435f445f4143435f464c5445005053435f445f4143435f464c5444005053435f445f4143435f534d4158005053435f445f4143435f50444d58005053435f445f4143435f445f4646005053435f445f4143435f4e4546005053435f445f4143435f4e5446005053435f4e455f56454c5f50005053435f4e455f56454c5f49005053435f4e455f56454c5f44005053435f4e455f56454c5f464c5445005053435f4e455f56454c5f464c5444005053435f4e455f56454c5f4646005053435f445f4143435f50005053435f445f4143435f49005053435f445f4143435f44005053435f445f56454c5f494d4158005053435f4e455f56454c5f494d4158005053435f445f4143435f494d415800434952434c455f5241444955535f4d00414e475f4d41580042524b5f44454c4159004143435f4d41585f4d0042524b5f4143435f4d0042524b5f4a524b5f4d004c4f49545f53504545445f4d53004c4f49545f4143435f4d41585f4d004c4f49545f42524b5f4143435f4d004c4f49545f42524b5f4a524b5f4d0052464e445f555345004a45524b005445525f4d415247494e00535044005241444955535f4d005350445f5550005350445f444e00414343004143435f5a004143435f434e520057505f5350440057505f5241444955535f4d0057505f5350445f55500057505f5350445f444e0057505f4143430057505f4143435f5a0057505f4143435f434e52004672616d653a2025732f2573004672616d653a20257300436865636b206672616d6520636c61737320616e6420747970650053616665747920737769746368004d6f746f7220456d657267656e63792053746f70706564005155414400504c555300580042465f5800585f52455600444a495f580043575f580056004800565441494c00415441494c00504c555352455600593400554e535550504f52544544005941575f48454144524f4f4d00544853545f4558504f005350494e5f4d4158004241545f564f4c545f4d4158004241545f564f4c545f4d494e004241545f435552525f4d41580050574d5f545950450050574d5f4d494e0050574d5f4d4158005350494e5f4d494e005350494e5f41524d004241545f435552525f544300544853545f484f56455200484f5645525f4c4541524e00534146455f44495341524d005941575f53565f414e474c450053504f4f4c5f54494d4500424f4f53545f5343414c45004241545f49445800534c45575f55505f54494d4500534c45575f444e5f54494d4500534146455f54494d450053504f4f4c5f54494d5f444e0049444c455f534543006e6f20534552564f785f46554e4354494f4e2073657420746f204d6f746f7225750025735350494e5f4d494e20746f6f206869676820252e3266203e20302e330025735350494e5f41524d203e2025735350494e5f4d494e00436865636b20257350574d5f4d494e20616e6420257350574d5f4d415800"),
  (0x1b050, "46656e636520656e61626c65642c206e65656420706f736974696f6e20657374696d61746500")
]

/-- A fresh memory with the constant data placed, over the HAL storage `st`. -/
def initMem (st : ByteArray) : PMem.Mem := Id.run do
  let s0 := PMem.fresh memSize stackBase heapBase st
  let ((), s) := (do for (a, h) in image do PMem.place a h : PMem.M Unit).run s0
  return s

end Vehicle_lib
