#!/usr/bin/env bash
# Translate ArduPilot's AC_PID family (AC_PID, AC_P, AC_P_1D, AC_PID_Basic, AC_PID_2D, AC_P_2D,
# AP_PIDInfo, and what they use: SlewLimiter, LowPassFilter, AP_Math's functions and Vector2) to Lean with
# cpp2lean, with the reference compiler flags and the stub headers (ardupilot/stubs).
# Output: ardupilot/out/AC_PID/. Usage: ardupilot/translate_ac_pid.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AC_PID"

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

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ac_pid.cpp" -o "$OUT" --namespace AC_PID_lib \
  --header "$L/AC_PID/AC_PID.cpp" --header "$L/AC_PID/AC_PID.h" --header "$L/AC_PID/AP_PIDInfo.h" \
  --header "$L/AC_PID/AC_P.cpp" --header "$L/AC_PID/AC_P.h" --header "$L/AC_PID/AC_P_1D.cpp" --header "$L/AC_PID/AC_P_1D.h" \
  --header "$L/AC_PID/AC_PID_Basic.cpp" --header "$L/AC_PID/AC_PID_Basic.h" \
  --header "$L/AC_PID/AC_PID_2D.cpp" --header "$L/AC_PID/AC_PID_2D.h" --header "$L/AC_PID/AC_P_2D.cpp" --header "$L/AC_PID/AC_P_2D.h" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" \
  --ap-param --boundary-fn AP_HAL::millis --drop AP_InternalError::error --src-root "$L" \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
