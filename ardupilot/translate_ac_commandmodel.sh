#!/usr/bin/env bash
# Translate ArduPilot's AC_CommandModel (AC_AttitudeControl/AC_CommandModel.cpp, its three parameters
# with their var_info defaults) to Lean with cpp2lean, from the unmodified sources, with the reference
# compiler flags and the stub headers (ardupilot/stubs) (README.md, "Phase 2"). `extern const
# AP_HAL::HAL& hal` (declared, not used) is the boundary. Output: ardupilot/out/AC_CommandModel/.
# Usage: ardupilot/translate_ac_commandmodel.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AC_CommandModel"

# the reference build: DEFINES, INCLUDES, and the dialect flags of COMMON/CLANG_FLAGS that change the AST;
# AP_TERRAIN_AVAILABLE 0 and AP_CUSTOMROTATIONS_ENABLED 0 as the reference vehicle's hwdef (reference/cfg/ref.hwdef)
CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0 -DAP_CUSTOMROTATIONS_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
# every translated file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ac_commandmodel.cpp" "$L/AC_AttitudeControl/AC_CommandModel.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ac_commandmodel.cpp" -o "$OUT" --namespace AC_CommandModel_lib --nest \
  --header "$L/AC_AttitudeControl/AC_CommandModel.h" --header "$L/AC_AttitudeControl/AC_CommandModel.cpp" \
  --lib-dir "$L/AP_Math" --boundary AP_HAL::HAL \
  --ap-param --drop AP_InternalError::error --src-root "$L" \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
