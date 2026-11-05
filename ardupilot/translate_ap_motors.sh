#!/usr/bin/env bash
# Translate ArduPilot's AP_Motors classes (AP_Motors, AP_MotorsMulticopter, AP_MotorsMatrix,
# Thrust_Linearization, and what they use from AP_Math and Filter) to Lean with cpp2lean, from the
# unmodified sources, with the reference compiler flags and the stub headers (ardupilot/stubs).
# Output: ardupilot/out/AP_Motors/. Usage: ardupilot/translate_ap_motors.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_Motors"

# the reference build: DEFINES, INCLUDES, and the dialect flags of COMMON/CLANG_FLAGS that change the AST
CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
M="$L/AP_Motors"
H=()
for f in AP_Motors_Class AP_MotorsMulticopter AP_MotorsMatrix AP_Motors_Thrust_Linearization; do
  H+=(--header "$M/$f.cpp" --header "$M/$f.h")
done

# every translated file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ap_motors.cpp" "$M/AP_Motors_Thrust_Linearization.cpp" "$M/AP_Motors_Class.cpp" "$M/AP_MotorsMulticopter.cpp" "$M/AP_MotorsMatrix.cpp" "$L/Filter/LowPassFilter.cpp" "$L/Filter/DerivativeFilter.cpp" "$L/AP_Math/AP_Math.cpp" "$M/AP_Motors_Class.h" "$M/AP_MotorsMulticopter.h" "$M/AP_MotorsMatrix.h" "$M/AP_Motors_Thrust_Linearization.h" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ap_motors.cpp" -o "$OUT" --namespace AP_Motors_lib --nest "${H[@]}" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" --lib-dir "$STUBS/GCS_MAVLink" \
  --ap-param --boundary-fn AP_HAL::micros --boundary-fn AP_HAL::millis \
  --boundary SRV_Channels,AP_BattMonitor,AP_Notify,AP_Logger,AP_AHRS,AP_HAL::HAL \
  --drop AP_InternalError::error --drop AP_HAL::panic \
  --drop AP_Motors::_singleton --drop AP_MotorsMatrix::_singleton --drop AP_Motors::get_singleton --drop AP_MotorsMatrix::get_singleton \
  --drop AP_MotorsMulticopter::_thrust_compensation_callback --drop AP_MotorsMulticopter::set_thrust_compensation_callback \
  --drop AP_MotorsMatrix::thrust_compensation \
  --drop AP_Motors::custom_frame_string --drop AP_Motors::set_frame_string --drop AP_Motors::get_frame_string \
  --drop AP_Motors::get_frame_and_type_string --drop AP_Motors::arming_checks --drop AP_Motors::motor_test_checks \
  --drop AP_MotorsMulticopter::arming_checks --drop AP_Motors::Log_Write_SPOL --drop AP_Motors::Log_Write \
  --drop AP_MotorsMulticopter::Log_Write --drop AP::motors \
  --output-log --array-params --site-inputs --boundary-call AP_Motors::rc_write --boundary-call AP_Motors::rc_write_angle --boundary-call AP_Motors::rc_set_freq \
  --boundary-call AP_Motors::add_motor_num --boundary-call AP_Motors::motor_mask_to_srv_channel_mask --lib-dir "$L/SRV_Channel" \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
