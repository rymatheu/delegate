#!/usr/bin/env bash
# Translate ArduPilot's AC_WPNav (and what it uses: SCurve, SplineCurve, the shaping functions of
# AP_Math/control.cpp, AP_Math's functions, Vector2/Vector3) to Lean with cpp2lean, from the unmodified
# sources, with the reference compiler flags and the stub headers (ardupilot/stubs), plus
# -DAP_TERRAIN_AVAILABLE=0 (the terrain database is compiled out; see below). The position controller
# and the attitude controller are the boundary: what the navigator reads from them is `Inputs`, its
# calls into the position controller are `Output` events (--output-log), in order. Since the navigator
# reads the position controller after calling into it within one member function (the stopping point
# after NE_set_max_speed_accel_m, the speed limits after a re-initialization), the position
# controller's reads are live (--boundary-live): an input is a function of the calls made so far in the
# member function (README.md, "AC_WPNav, the AHRS view, and the two vehicles").
# Output: ardupilot/out/AC_WPNav/. Usage: ardupilot/translate_ac_wpnav.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AC_WPNav"

# the reference build: DEFINES, INCLUDES, and the dialect flags that change the AST; AP_TERRAIN_AVAILABLE 0
# (AP_Terrain.h needs MAVLink's message types, which the stub GCS_MAVLink does not declare; with the
# database compiled out, AC_WPNav's terrain source is the rangefinder or none, AC_WPNav.cpp:186-205)
CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
W="$L/AC_WPNav"
M="$L/AP_Math"

# every translated file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ac_wpnav.cpp" "$W/AC_WPNav.cpp" "$M/SCurve.cpp" "$M/SplineCurve.cpp" "$M/AP_Math.cpp" "$M/control.cpp" "$M/vector2.cpp" "$M/vector3.cpp" "$M/location.cpp" "$W/AC_WPNav.h" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ac_wpnav.cpp" -o "$OUT" --namespace AC_WPNav_lib --nest \
  --header "$W/AC_WPNav.cpp" --header "$W/AC_WPNav.h" \
  --lib-dir "$L/AP_Math" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ap-param --boundary AP_AHRS_View,AP_AHRS,AC_PosControl,AC_AttitudeControl,AP_HAL::HAL \
  --boundary-fn AP_HAL::millis --boundary-fn AP_HAL::micros64 \
  --drop AP_InternalError::error --drop printf --drop SCurve::debug --drop AP_Logger::Write --drop SCurve::calculate_path::logged_scve \
  --drop AC_WPNav::set_wp_destination_loc --drop AC_WPNav::set_wp_destination_next_loc \
  --drop AC_WPNav::get_wp_destination_loc --drop AC_WPNav::get_oa_wp_destination \
  --drop AC_WPNav::set_spline_destination_loc --drop AC_WPNav::set_spline_destination_next_loc \
  --drop AC_WPNav::get_vector_NED_m --drop AC_WPNav::convert_parameters \
  --boundary-live AC_PosControl --boundary-query AC_PosControl::NE_get_pos_p --boundary-query AC_P_2D::kP \
  --output-log \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
