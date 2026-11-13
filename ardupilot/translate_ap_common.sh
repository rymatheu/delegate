#!/usr/bin/env bash
# Translate ArduPilot's AP_Common Location (Location.h, Location.cpp) and Bitmask<N> (Bitmask.h, at the
# sizes the vehicle's classes use: 32 = NUM_SERVO_CHANNELS, 102 = MSG_LAST, 190 =
# SRV_Channel::k_nr_aux_servo_functions, 317 = RC_Channel::AUX_FUNCTION_MAX, 634 = 2 * AUX_FUNCTION_MAX)
# to Lean with cpp2lean, from the unmodified sources, with the reference compiler flags and the stub
# headers (ardupilot/stubs), --pointer-params (Bitmask's memset/memcpy/memcmp over its words) and
# --runtime-loops (its loops over NUMWORDS) (README.md, "Phase 2").
# Left out with --drop (not part of the model; a call whose result is used is rejected):
# - the members that read the AHRS singleton (`AP::ahrs()`: home, EKF origin): the constructors from
#   an EKF offset, from_ekf_offset_NED_m, get_alt_cm, the get_vector_* templates. (With the stub
#   headers, AP_AHRS_ENABLED is 0 where Location.cpp tests it: the stub AP_AHRS.h does not include
#   AP_AHRS_config.h, so the C++ of these members is the AHRS-less variant, and the constructors,
#   from_ekf_offset_NED_m and the templates are compiled out. Every member that is translated is the
#   same code in either configuration.);
# - get_alt_frame and linearly_interpolate_alt, which call AP_HAL::panic under SITL (the process
#   aborts; no outcome of the model stands for that);
# - is_zero, a memcmp of the object representation (the unused bits of the bit-field byte and the
#   padding are not modeled);
# - their callers whose results depend on them: get_alt_m, change_alt_frame, get_height_above,
#   same_alt_as, same_loc_as, sanitize, get_distance_NED_alt_frame.
# Output: ardupilot/out/AP_Common/. Usage: ardupilot/translate_ap_common.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_Common"

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
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_ap_common.cpp" "$L/AP_Common/Location.cpp" "$L/AP_Math/location.cpp" "$L/AP_Math/vector2.cpp" "$L/AP_Math/vector3.cpp" "$L/AP_Math/AP_Math.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
DROP=(--drop 'Location::Location(const Vector3f &, Location::AltFrame)' --drop 'Location::Location(const Vector3d &, Location::AltFrame)'
  --drop Location::from_ekf_offset_NED_m --drop Location::get_alt_cm
  --drop Location::get_vector_xy_from_origin_NE_cm --drop Location::get_vector_from_origin_NEU_cm --drop Location::get_vector_from_origin_NEU
  --drop Location::get_vector_xy_from_origin_NE_m --drop Location::get_vector_from_origin_NEU_m --drop Location::get_vector_from_origin_NED_m
  --drop Location::get_alt_frame --drop Location::linearly_interpolate_alt --drop Location::is_zero
  --drop Location::get_alt_m --drop Location::change_alt_frame --drop Location::get_height_above --drop Location::same_alt_as
  --drop Location::same_loc_as --drop Location::sanitize --drop Location::get_distance_NED_alt_frame)
python3 cpp2lean.py "$HERE/unity_ap_common.cpp" -o "$OUT" --namespace AP_Common_lib --nest \
  --header "$L/AP_Common/Location.h" --header "$L/AP_Common/Location.cpp" \
  --lib-dir "$L/AP_Math" --lib-dir "$L/AP_Common" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' --type-name 'Matrix3<double>=Matrix3p' \
  --pointer-params --runtime-loops "${DROP[@]}" \
  --ap-param --drop AP_InternalError::error --src-root "$L" \
  -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
