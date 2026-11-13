#!/usr/bin/env bash
# The rejection survey of the estimation pipeline (README.md, "Phase 3: EKF data structures"):
# cpp2lean --keep-going over every source of AP_NavEKF3, AP_NavEKF and AP_DAL (unity_ekf3_survey.cpp)
# with the Phase 3 options, against the real headers and the reference configuration; prints the
# rejections (file:line:col: rejected: ...) to OUT (default build/survey_ekf3.log), then the summary by
# feature (ardupilot/survey_group.py). The translation itself is not used (build/survey_ekf3_out).
# Usage: ardupilot/survey_ekf3.sh [OUT] [extra cpp2lean options]
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="${1:-$ROOT/build/survey_ekf3.log}"
shift || true
ekf_flags AP_NavEKF3/AP_NavEKF3_core.cpp
SRCS=()
while read -r inc; do SRCS+=("$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_ekf3_survey.cpp")
ekf_check_unity "$HERE/unity_ekf3_survey.cpp" "${SRCS[@]}" || exit 1
H=()
for f in "${SRCS[@]}"; do H+=(--header "$RL/$f"); done
for f in AP_NavEKF/EKF_Buffer.h AP_NavEKF/EKFGSF_yaw.h AP_NavEKF/AP_NavEKF_Source.h AP_NavEKF/AP_NavEKF_core_common.h \
         AP_NavEKF/AP_Nav_Common.h AP_NavEKF3/AP_NavEKF3.h AP_NavEKF3/AP_NavEKF3_core.h AP_DAL/AP_DAL.h AP_DAL/AP_DAL_InertialSensor.h \
         AP_DAL/AP_DAL_Baro.h AP_DAL/AP_DAL_GPS.h AP_DAL/AP_DAL_Compass.h AP_DAL/AP_DAL_Airspeed.h AP_DAL/AP_DAL_RangeFinder.h \
         AP_DAL/AP_DAL_Beacon.h AP_DAL/AP_DAL_VisualOdom.h AP_DAL/LogStructure.h AP_NavEKF3/LogStructure.h AP_NavEKF/LogStructure.h; do H+=(--header "$RL/$f"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ekf3_survey.cpp" -o "$ROOT/build/survey_ekf3_out" --namespace EKF3_survey --nest --keep-going --survey \
  "${H[@]}" --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_Common" --lib-dir "$RL/AP_Logger" --lib-dir "$RL/AP_GPS" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ekf-types --ekf-arrays --ring-buffers --runtime-loops --pointer-params --world --ap-param --c-strings --byte-objects \
  --drop AP_InternalError::error \
  --src-root "$RL" "${EKF_CA[@]}" "$@" > "$OUT" 2>&1
echo "cpp2lean exit status $?" >> "$OUT"
python3 "$HERE/survey_group.py" "$OUT"
