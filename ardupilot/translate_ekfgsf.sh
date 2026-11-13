#!/usr/bin/env bash
# Translate AP_NavEKF's EKFGSF_yaw (EKFGSF_yaw.{h,cpp}, double precision) against the real ArduPilot
# headers and the reference build's configuration (README.md, "Phase 3: EKF data structures"):
# ardupilot/unity_ekfgsf.cpp -> ardupilot/out/EKFGSF/EKFGSF_lib.lean.
# Usage: ardupilot/translate_ekfgsf.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="$ROOT/ardupilot/out/EKFGSF"
ekf_flags AP_NavEKF/EKFGSF_yaw.cpp
ekf_check_unity "$HERE/unity_ekfgsf.cpp" AP_NavEKF/EKFGSF_yaw.cpp AP_Math/AP_Math.cpp AP_Math/vector2.cpp AP_Math/vector3.cpp AP_Math/matrix3.cpp
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ekfgsf.cpp" -o "$OUT" --namespace EKFGSF_lib --nest \
  --header "$RL/AP_NavEKF/EKFGSF_yaw.h" --header "$RL/AP_NavEKF/EKFGSF_yaw.cpp" \
  --lib-dir "$RL/AP_Math" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ekf-types --ekf-arrays --runtime-loops --drop AP_InternalError::error \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
