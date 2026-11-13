#!/usr/bin/env bash
# Translate ArduPilot's AP_Math library to Lean with cpp2lean: the functions, member functions and
# constructors listed in ardupilot/AP_Math.use (what the control classes use, and what
# they call), from the unmodified sources (AP_Math.cpp, control.cpp, vector2.cpp, vector3.cpp,
# matrix3.cpp, quaternion.cpp, location.cpp and their headers; since phase 2 also matrix_alg.cpp, crc.cpp,
# location_double.cpp and div1000.h, with --pointer-params and --runtime-loops), with the reference
# compiler flags (ardupilot/vehicle/build.sh) and AP_CUSTOMROTATIONS_ENABLED 0, as the reference
# vehicle's hwdef (reference/cfg/ref.hwdef:67): Vector3::rotate and Quaternion::from_rotation then
# have no call into the custom rotations singleton. fedisableexcept/feenableexcept (inverse4x4 under
# SITL) only change the floating-point trap mask, outside the model (the default environment):
# --drop. Output: ardupilot/out/AP_Math/. Usage: ardupilot/translate_ap_math.sh [extra options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_Math"

# the reference build: DEFINES, INCLUDES, and the dialect flags of COMMON/CLANG_FLAGS that change the AST
CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_CUSTOMROTATIONS_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done

# Vector2<double> and Vector3<double> have three typedefs each (Vector2d, Vector2p, Vector2F; the
# position code's name is Vector2p, control.h:9-10), Matrix3<double> two: the Lean names are given.
# every translated file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ap_math.cpp" "$L/AP_Math/AP_Math.cpp" "$L/AP_Math/control.cpp" "$L/AP_Math/vector2.cpp" "$L/AP_Math/vector3.cpp" "$L/AP_Math/matrix3.cpp" "$L/AP_Math/quaternion.cpp" "$L/AP_Math/location.cpp" "$L/AP_Math/matrix_alg.cpp" "$L/AP_Math/crc.cpp" "$L/AP_Math/location_double.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ap_math.cpp" -o "$OUT" --namespace AP_Math_lib --nest \
  --lib-dir "$L/AP_Math" --use @"$HERE/AP_Math.use" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' --type-name 'Matrix3<double>=Matrix3p' \
  --ap-param --drop AP_InternalError::error --src-root "$L" \
  --pointer-params --runtime-loops --drop fedisableexcept --drop feenableexcept \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
