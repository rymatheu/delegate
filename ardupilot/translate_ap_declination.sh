#!/usr/bin/env bash
# Translate ArduPilot's AP_Declination (AP_Declination.cpp: get_mag_field_ef, get_declination,
# get_earth_field_ga; tables.cpp: the sampling constants and the three 19x37 tables, static const
# members defined out of line) and what they use (constrain_int32, radians, Matrix3<float>::from_euler
# and operator*, Location's lat and lng) to Lean with cpp2lean, from the unmodified sources, with the
# reference compiler flags and the stub headers (ardupilot/stubs) (README.md, "Phase 2").
# Output: ardupilot/out/AP_Declination/.
# Usage: ardupilot/translate_ap_declination.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_Declination"

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
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ap_declination.cpp" "$L/AP_Declination/AP_Declination.cpp" "$L/AP_Declination/tables.cpp" "$L/AP_Math/AP_Math.cpp" "$L/AP_Math/vector3.cpp" "$L/AP_Math/matrix3.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ap_declination.cpp" -o "$OUT" --namespace AP_Declination_lib --nest \
  --header "$L/AP_Declination/AP_Declination.h" --header "$L/AP_Declination/AP_Declination.cpp" --header "$L/AP_Declination/tables.cpp" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/AP_Common" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' --type-name 'Matrix3<double>=Matrix3p' \
  --ap-param --drop AP_InternalError::error --src-root "$L" \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
