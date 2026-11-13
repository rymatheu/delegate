#!/usr/bin/env bash
# Translate ArduPilot's LowPassFilter2p (Filter/LowPassFilter2p.cpp: DigitalBiquadFilter<T> and
# LowPassFilter2p<T> at the five types the file instantiates, int, long, float, Vector2f, Vector3f) to
# Lean with cpp2lean, from the unmodified sources, with the reference compiler flags and the stub
# headers (ardupilot/stubs) (README.md, "Phase 2"). LowPassFilter2p.cpp defines AP_INLINE_VECTOR_OPS
# before it includes AP_Math.h, so its Vector3 operators are vector3.h's inline ones; vector2.cpp
# provides Vector2's. Output: ardupilot/out/LowPassFilter2p/.
# Usage: ardupilot/translate_lowpassfilter2p.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/LowPassFilter2p"

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
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_lowpassfilter2p.cpp" "$L/Filter/LowPassFilter2p.cpp" "$L/AP_Math/vector2.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_lowpassfilter2p.cpp" -o "$OUT" --namespace LowPassFilter2p_lib --nest \
  --lib-dir "$L/AP_Math" --lib-dir "$L/Filter" --use @"$HERE/LowPassFilter2p.use" \
  --ap-param --drop AP_InternalError::error --src-root "$L" \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
