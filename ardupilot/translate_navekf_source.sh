#!/usr/bin/env bash
# Phase 3: AP_NavEKF_Source with AP_Param in arrays of structs (README.md "Phase 3: AP_InertialSensor, AP_GPS and
# AP_NavEKF_Source"), against ArduPilot's real headers and the reference build's flags:
# ardupilot/unity_navekf_source.cpp -> ardupilot/out/NavEKF_Source/NavEKF_Source_lib.lean.
# AP_NavEKF, AP_Param and AP_Math are libraries: only what the entry points of ardupilot/navekf_source.use reach is
# translated. AP_DAL (the counts of enabled compasses and barometers it reads) and the logger are the boundary.
# Usage: ardupilot/translate_navekf_source.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="$ROOT/ardupilot/out/NavEKF_Source"
ekf_flags AP_NavEKF/AP_NavEKF_Source.cpp
ekf_check_unity "$HERE/unity_navekf_source.cpp" AP_NavEKF/AP_NavEKF_Source.cpp AP_Param/AP_ParamT.cpp
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_navekf_source.cpp" -o "$OUT" --namespace NavEKF_Source_lib --nest --world --world-pointers \
  --lib-dir "$RL/AP_NavEKF" --lib-dir "$RL/AP_Param" --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_Common" --use @"$HERE/navekf_source.use" \
  --front-ends --ins-gps --param-ext --ap-param --ekf-types --ekf-arrays --pointer-params --runtime-loops --general-loops \
  --boundary AP_HAL::HAL,AP_DAL,AP_DAL_Compass,AP_DAL_Baro,AP_Logger --boundary-query AP_DAL::compass,AP_DAL::baro --output-log --drop AP_Param::save --drop AP_Param::notify \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
