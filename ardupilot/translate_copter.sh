#!/usr/bin/env bash
# The controllers of the vehicle as one World (cpp2lean --world, README.md "The World"):
# unity_copter.cpp -> out/Copter/Copter_lib.lean. Replaces the four separate translations of
# AP_Motors, AC_AttitudeControl, AC_PosControl and AC_WPNav, whose edges were per-class boundaries.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/Copter"

CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0 -DAP_AVOIDANCE_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
H=()
for f in AP_Motors/AP_Motors_Class AP_Motors/AP_MotorsMulticopter AP_Motors/AP_MotorsMatrix AP_Motors/AP_Motors_Thrust_Linearization \
         AC_AttitudeControl/AC_AttitudeControl AC_AttitudeControl/AC_AttitudeControl_Multi AC_AttitudeControl/AC_PosControl AC_WPNav/AC_WPNav AC_WPNav/AC_Loiter AC_WPNav/AC_Circle; do
  H+=(--header "$L/$f.cpp" --header "$L/$f.h")
done
SRCS=()
while read -r inc; do SRCS+=("$L/$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_copter.cpp")
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_copter.cpp" "${SRCS[@]}" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_copter.cpp" -o "$OUT" --namespace Copter_lib --nest --world "${H[@]}" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" --lib-dir "$L/AC_PID" --lib-dir "$STUBS/GCS_MAVLink" --lib-dir "$L/SRV_Channel" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ap-param --boundary AP_AHRS_View,AP_AHRS,SRV_Channels,AP_BattMonitor,AP_Notify,AP_Logger,AP_Scheduler,AP_HAL::HAL \
  --boundary-fn AP_HAL::micros --boundary-fn AP_HAL::millis --boundary-fn AP_HAL::micros64 \
  --boundary-query AP_AHRS_View::get_position_NE_reset_count --boundary-query AP_AHRS_View::get_position_D_reset_count \
  --boundary-call AP_Motors::rc_write --boundary-call AP_Motors::rc_write_angle --boundary-call AP_Motors::rc_set_freq \
  --boundary-call AP_Motors::add_motor_num --boundary-call AP_Motors::motor_mask_to_srv_channel_mask \
  --boundary-call AC_PosControl::has_good_timing \
  --drop AP_InternalError::error --drop AP_HAL::panic --drop AP_BoardConfig::config_error \
  --drop printf --drop SCurve::debug --drop AP_Logger::Write --drop AP_Logger::Write_Error --drop SCurve::calculate_path::logged_scve \
  --drop AP_Motors::_singleton --drop AP_MotorsMatrix::_singleton --drop AP_Motors::get_singleton --drop AP_MotorsMatrix::get_singleton \
  --drop AP_MotorsMulticopter::_thrust_compensation_callback --drop AP_MotorsMulticopter::set_thrust_compensation_callback \
  --drop AP_MotorsMatrix::thrust_compensation \
  --drop AP_Motors::custom_frame_string --drop AP_Motors::set_frame_string --drop AP_Motors::get_frame_string \
  --drop AP_Motors::get_frame_and_type_string --drop AP_Motors::arming_checks --drop AP_Motors::motor_test_checks \
  --drop AP_MotorsMulticopter::arming_checks --drop AP_Motors::Log_Write_SPOL --drop AP_Motors::Log_Write \
  --drop AP_MotorsMulticopter::Log_Write --drop AP::motors \
  --drop AC_AttitudeControl::_singleton --drop AC_AttitudeControl::get_singleton \
  --drop AC_AttitudeControl::pre_arm_checks --drop AC_AttitudeControl::convert_parameters \
  --drop AC_PosControl::_singleton --drop AC_PosControl::get_singleton --drop AC_PosControl::write_log \
  --drop AC_PosControl::pre_arm_checks --drop AC_PosControl::convert_parameters \
  --drop AC_WPNav::set_wp_destination_loc --drop AC_WPNav::set_wp_destination_next_loc \
  --drop AC_WPNav::get_wp_destination_loc --drop AC_WPNav::get_oa_wp_destination \
  --drop AC_WPNav::set_spline_destination_loc --drop AC_WPNav::set_spline_destination_next_loc \
  --drop AC_WPNav::get_vector_NED_m --drop AC_WPNav::convert_parameters \
  --drop AC_Loiter::convert_parameters --drop AC_Circle::convert_parameters --drop 'AC_Circle::set_center(const Location &)' \
  --output-log --array-params --site-inputs \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
