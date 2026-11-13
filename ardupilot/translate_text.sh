#!/usr/bin/env bash
# Translate ArduPilot's text formatter to Lean with cpp2lean (README.md, "Phase 2b"): print_vprintf
# (AP_HAL/utility/print_vprintf.cpp), ftoa_engine (ftoa_engine.cpp), ultoa_invert/ulltoa_invert
# (utoa_invert.cpp), AP_HAL::Util::snprintf/vsnprintf and its BufferPrinter (AP_HAL/Util.cpp), from
# the unmodified sources, with the reference compiler flags and the stub headers, as the library
# code that the generated test functions of ardupilot/unity_text.cpp (ardupilot/gen_unity_text.py)
# call. AP_HAL::HAL and AP_HAL::Util are the boundary (`hal`); snprintf and vsnprintf read nothing of
# their Util object (--boundary-static). Options: --pointer-params --c-strings (char, string
# literals, char pointers, the C string runtime, va_list), --byte-objects (ftoa_engine's byte view
# of its float and its float/uint32 union), --gotos (print_vprintf's goto flt_oper/non_string/ultoa/
# tail, `continue` in its do loop, its switch fallthroughs; ftoa_engine's goto roundup),
# --general-loops (the loops over the format string and the digit loops), --uninit-reads (locals
# assigned on every path the gotos take, which the definite-assignment check does not follow).
# Output: ardupilot/out/Text/. Usage: ardupilot/translate_text.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/Text"

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
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_text.cpp" "$L/AP_HAL/utility/print_vprintf.cpp" "$L/AP_HAL/utility/ftoa_engine.cpp" "$L/AP_HAL/utility/utoa_invert.cpp" "$L/AP_HAL/Util.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_text.cpp" -o "$OUT" --namespace Text_lib --nest \
  --lib-dir "$L/AP_HAL" --boundary AP_HAL::Util,AP_HAL::HAL \
  --boundary-static AP_HAL::Util::snprintf --boundary-static AP_HAL::Util::vsnprintf \
  --pointer-params --runtime-loops --c-strings --byte-objects --gotos --general-loops --uninit-reads \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
