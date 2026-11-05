#!/usr/bin/env bash
# Translate ArduPilot's AC_AttitudeControl and AC_AttitudeControl_Multi (and what they use: AC_PID,
# AC_P, SlewLimiter, LowPassFilter, AP_Math's functions, Vector2/Vector3/Matrix3/Quaternion) to Lean
# with cpp2lean, from the unmodified sources, with the oracle's compiler flags and stub headers
# (ardupilot/stubs). The AHRS view and the motors are the boundary: what the attitude
# controller reads from them is `Inputs`, what it writes into the motors (set_roll, set_throttle,
# ...) is `Outputs` (README.md, "AC_AttitudeControl and AC_PosControl").
# Output: ardupilot/out/AC_Attitude/. Usage: ardupilot/translate_ac_attitude.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AC_Attitude"

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
A="$L/AC_AttitudeControl"

# every translated file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ac_attitude.cpp" "$A/AC_AttitudeControl.cpp" "$A/AC_AttitudeControl_Multi.cpp" "$L/AC_PID/AC_PID.cpp" "$L/AC_PID/AC_P.cpp" "$L/Filter/SlewLimiter.cpp" "$L/Filter/LowPassFilter.cpp" "$L/AP_Math/AP_Math.cpp" "$L/AP_Math/control.cpp" "$L/AP_Math/vector2.cpp" "$L/AP_Math/vector3.cpp" "$L/AP_Math/matrix3.cpp" "$L/AP_Math/quaternion.cpp" "$A/AC_AttitudeControl.h" "$A/AC_AttitudeControl_Multi.h" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

# Boundary: the AHRS view (_ahrs), the motors (_motors, _motors_multi), the scheduler
# (AP::scheduler().get_filtered_loop_time() in max_rate_step_bf_*), the HAL (`extern const
# AP_HAL::HAL& hal`, declared, not used on any translated path), the clock AP_HAL::micros64
# (_rate_gyro_time_us) and AP_HAL::millis (AC_PID's slew limiter).
# Left out (--drop), each an effect outside the model: the singleton (_singleton, get_singleton),
# pre_arm_checks (formats text into a char buffer), convert_parameters (parameter storage),
# AP_BoardConfig::config_error (the abort in the base's rate_controller_run_dt, which
# AC_AttitudeControl_Multi overrides) and AP_InternalError::error (INTERNAL_ERROR).
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ac_attitude.cpp" -o "$OUT" --namespace AC_Attitude_lib --nest \
  --header "$A/AC_AttitudeControl.cpp" --header "$A/AC_AttitudeControl.h" \
  --header "$A/AC_AttitudeControl_Multi.cpp" --header "$A/AC_AttitudeControl_Multi.h" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" --lib-dir "$L/AC_PID" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ap-param --boundary AP_AHRS_View,AP_Motors,AP_MotorsMulticopter,AP_Scheduler,AP_HAL::HAL \
  --boundary-fn AP_HAL::millis --boundary-fn AP_HAL::micros64 \
  --drop AP_InternalError::error --drop AP_BoardConfig::config_error \
  --drop AC_AttitudeControl::_singleton --drop AC_AttitudeControl::get_singleton \
  --drop AC_AttitudeControl::pre_arm_checks --drop AC_AttitudeControl::convert_parameters \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
