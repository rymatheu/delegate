#!/usr/bin/env bash
# Translate ArduPilot's AP_InternalError (AP_InternalError/AP_InternalError.cpp) to Lean with
# cpp2lean, from the unmodified sources, with the reference compiler flags and the stub headers
# (README.md, "Phase 2b"), with the text formatter that errors_as_string reaches through
# `hal.util->snprintf` (as translate_text.sh: print_vprintf, ftoa_engine, utoa_invert, Util.cpp's
# snprintf/vsnprintf; same options), and the test function of ardupilot/unity_internalerror.cpp.
# error() writes `hal.util->persistent_data`, a boundary object's data members: output events
# (--output-log). Left out (--drop): the file-scope `instance` and `AP::internalerror()`, the
# singleton (World singleton support); error_to_string (log2f, not among the translated C library
# functions; called only under HAL_DEBUG_BUILD).
# Output: ardupilot/out/AP_InternalError/. Usage: ardupilot/translate_internalerror.sh [cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_InternalError"

CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0 -DAP_CUSTOMROTATIONS_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
# every included ArduPilot file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_internalerror.cpp" "$L/AP_HAL/utility/print_vprintf.cpp" "$L/AP_HAL/utility/ftoa_engine.cpp" "$L/AP_HAL/utility/utoa_invert.cpp" "$L/AP_HAL/Util.cpp" "$L/AP_InternalError/AP_InternalError.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_internalerror.cpp" -o "$OUT" --namespace AP_InternalError_lib --nest \
  --header "$L/AP_InternalError/AP_InternalError.h" --header "$L/AP_InternalError/AP_InternalError.cpp" --lib-dir "$L/AP_HAL" --boundary AP_HAL::Util,AP_HAL::HAL \
  --boundary-static AP_HAL::Util::snprintf --boundary-static AP_HAL::Util::vsnprintf \
  --pointer-params --runtime-loops --c-strings --byte-objects --gotos --general-loops --uninit-reads --output-log \
  --drop instance --drop AP::internalerror --drop AP_InternalError::error_to_string \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
