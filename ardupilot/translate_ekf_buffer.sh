#!/usr/bin/env bash
# Translate AP_NavEKF's ring buffers (EKF_Buffer.{h,cpp}) monomorphized at the ten wrapper
# specializations EKF3 instantiates, with the element structs of AP_NavEKF3_core.h, against the real
# ArduPilot headers and the reference build's configuration (README.md, "Phase 3: EKF data
# structures"): ardupilot/unity_ekf_buffer.cpp -> ardupilot/out/EKF_Buffer/EKF_Buffer_lib.lean.
# Usage: ardupilot/translate_ekf_buffer.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="$ROOT/ardupilot/out/EKF_Buffer"
ekf_flags AP_NavEKF3/AP_NavEKF3_core.cpp
ekf_check_unity "$HERE/unity_ekf_buffer.cpp" AP_NavEKF/EKF_Buffer.cpp
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ekf_buffer.cpp" -o "$OUT" --namespace EKF_Buffer_lib --nest \
  --header "$RL/AP_NavEKF/EKF_Buffer.h" --header "$RL/AP_NavEKF/EKF_Buffer.cpp" \
  --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_NavEKF3" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ekf-types --ekf-arrays --ring-buffers --runtime-loops --drop AP_InternalError::error \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
