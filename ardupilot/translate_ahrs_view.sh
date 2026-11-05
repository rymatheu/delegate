#!/usr/bin/env bash
# Translate the AHRS view derivation to Lean with cpp2lean: AP_AHRS_View::update (AP_AHRS_View.cpp:61-83)
# and AP_AHRS::calc_trig (AP_AHRS_Backend.cpp:93-135), copied unmodified out of the ArduPilot sources by
# ardupilot/ahrs/extract.py (the two .cpp files do not compile against the stub headers), with the
# declarations of ardupilot/ahrs/AP_AHRS_View_decls.h and the AP_Math functions they call, plus
# QuaternionT<float>::rotation_matrix (--use), the rotation of the AHRS estimate's quaternion that the
# vehicle hands to the view. The AHRS (AP_AHRS) is the boundary: its rotation matrix and gyro are
# inputs; calc_trig reads nothing of the AHRS object and is translated as a function of its
# arguments (--boundary-static). The real headers' flags and defines as for the other translations.
# Output: ardupilot/out/AHRS_View/. Usage: ardupilot/translate_ahrs_view.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AHRS_View"

python3 "$HERE/ahrs/extract.py" "$L" > /dev/null

# the reference build: DEFINES, INCLUDES, and the dialect flags that change the AST
CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
M="$L/AP_Math"

CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ahrs_view.cpp" "$M/AP_Math.cpp" "$M/vector2.cpp" "$M/vector3.cpp" "$M/matrix3.cpp" "$M/quaternion.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" -I "$HERE")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ahrs_view.cpp" -o "$OUT" --namespace AHRS_View_lib --nest \
  --header "$HERE/ahrs/AP_AHRS_View.cpp" --header "$HERE/ahrs/AP_AHRS_View_decls.h" \
  --lib-dir "$L/AP_Math" --use 'QuaternionT<float>::rotation_matrix(Matrix3<float>)' \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --boundary AP_AHRS --boundary-static AP_AHRS::calc_trig \
  --drop AP_InternalError::error --drop AP_HAL::panic \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" -I "$HERE" "${CA[@]}" "$@"
