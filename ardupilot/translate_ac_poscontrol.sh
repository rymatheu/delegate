#!/usr/bin/env bash
# Translate ArduPilot's AC_PosControl (and what it uses: AC_PID, AC_P_1D, AC_P_2D, AC_PID_Basic,
# AC_PID_2D, SlewLimiter, LowPassFilter, AP_Math's functions, Vector2/Vector3) to Lean with cpp2lean,
# from the unmodified sources, with the reference compiler flags and the stub headers
# (ardupilot/stubs). The AHRS (the view and AP::ahrs()), the motors and the attitude controller are the
# boundary: what the position controller reads from them is `Inputs`, its one write into the
# attitude controller (set_throttle_out) is an `Output` event (--output-log), so that the caller
# applies it to the attitude controller in order (README.md, "AC_AttitudeControl and AC_PosControl").
# Output: ardupilot/out/AC_PosControl/. Usage: ardupilot/translate_ac_poscontrol.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AC_PosControl"

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
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ac_poscontrol.cpp" "$A/AC_PosControl.cpp" "$L/AC_PID/AC_PID.cpp" "$L/AC_PID/AC_P_1D.cpp" "$L/AC_PID/AC_P_2D.cpp" "$L/AC_PID/AC_PID_Basic.cpp" "$L/AC_PID/AC_PID_2D.cpp" "$L/Filter/SlewLimiter.cpp" "$L/Filter/LowPassFilter.cpp" "$L/AP_Math/AP_Math.cpp" "$L/AP_Math/control.cpp" "$L/AP_Math/vector2.cpp" "$L/AP_Math/vector3.cpp" "$A/AC_PosControl.h" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

# Boundary: the AHRS view (_ahrs) and AP::ahrs(), the motors (_motors), the attitude controller
# (_attitude_control: its getters are inputs, set_throttle_out an output), the scheduler
# (AP::scheduler().ticks32()), the HAL (`extern const AP_HAL::HAL& hal`, not used on any translated
# path), the clock AP_HAL::millis. Getters of boundary classes that are not marked const but do not
# change the object (--boundary-query): AC_AttitudeControl::get_bf_feedforward (`return
# _rate_bf_ff_enabled;`, AC_AttitudeControl.h:396), AP_AHRS_View::get_position_NE/D_reset_count (the
# AHRS's const counters, ardupilot/stubs/AP_AHRS/AP_AHRS_View.h). has_good_timing (SITL's lock-step
# flag through the AP::sitl() pointer, AC_PosControl.cpp:1797-1807) is an input (--boundary-call); it
# only guards INTERNAL_ERROR.
# Left out (--drop), each an effect outside the model: the singleton (_singleton, get_singleton),
# write_log (logging), pre_arm_checks (formats text into a char buffer), convert_parameters
# (parameter storage), AP_InternalError::error (INTERNAL_ERROR).
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ac_poscontrol.cpp" -o "$OUT" --namespace AC_PosControl_lib --nest \
  --header "$A/AC_PosControl.cpp" --header "$A/AC_PosControl.h" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" --lib-dir "$L/AC_PID" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ap-param --boundary AP_AHRS_View,AP_AHRS,AP_Motors,AC_AttitudeControl,AP_Scheduler,AP_HAL::HAL \
  --boundary-fn AP_HAL::millis \
  --boundary-query AC_AttitudeControl::get_bf_feedforward \
  --boundary-query AP_AHRS_View::get_position_NE_reset_count --boundary-query AP_AHRS_View::get_position_D_reset_count \
  --boundary-call AC_PosControl::has_good_timing \
  --drop AP_InternalError::error \
  --drop AC_PosControl::_singleton --drop AC_PosControl::get_singleton --drop AC_PosControl::write_log \
  --drop AC_PosControl::pre_arm_checks --drop AC_PosControl::convert_parameters --output-log \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
