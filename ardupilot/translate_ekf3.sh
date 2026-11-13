#!/usr/bin/env bash
# Translate AP_DAL, AP_NavEKF and AP_NavEKF3 (README.md, "Phase 3: AP_DAL and NavEKF3") against the real
# ArduPilot headers and the reference build's configuration: ardupilot/unity_ekf3.cpp (the sources
# included unmodified, the NavEKF3 front end a file-scope object) -> ardupilot/out/EKF3/EKF3_lib.lean.
# --reachable: what the entry points of ardupilot/ekf3.use reach is translated; AP_Math and AP_Common are --lib-dir.
# Usage: ardupilot/translate_ekf3.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="${EKF3_OUT:-$ROOT/ardupilot/out/EKF3}"
ekf_flags AP_NavEKF3/AP_NavEKF3_core.cpp
SRCS=()
while read -r inc; do SRCS+=("$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_ekf3.cpp")
ekf_check_unity "$HERE/unity_ekf3.cpp" "${SRCS[@]}"
# sizeof(NavEKF3_core) as clang computes it with the unit's flags (AP_NavEKF3.cpp:842 compares it with the free memory)
SZ=$(printf '#include <AP_NavEKF3/AP_NavEKF3_core.h>\nunsigned long cpp2lean_sizeof = sizeof(NavEKF3_core);\n' |
     clang++ "${EKF_FLAGS[@]}" -x c++ -S -emit-llvm -o - - 2>/dev/null | sed -n 's/^@cpp2lean_sizeof = global i64 \([0-9]*\).*/\1/p')
[ -n "$SZ" ] || { echo "sizeof(NavEKF3_core) not found" >&2; exit 1; }
H=()
for f in "${SRCS[@]}"; do case "$f" in AP_Math/*|AP_Common/*|AP_Declination/*) ;; *) H+=(--header "$RL/$f");; esac; done
for f in AP_GPS/AP_GPS_FixType.h AP_NavEKF/EKF_Buffer.h AP_NavEKF/EKFGSF_yaw.h AP_NavEKF/AP_NavEKF_Source.h AP_NavEKF/AP_NavEKF_core_common.h \
         AP_NavEKF/AP_Nav_Common.h AP_NavEKF3/AP_NavEKF3.h AP_NavEKF3/AP_NavEKF3_core.h AP_DAL/AP_DAL.h AP_DAL/AP_DAL_InertialSensor.h \
         AP_DAL/AP_DAL_Baro.h AP_DAL/AP_DAL_GPS.h AP_DAL/AP_DAL_Compass.h AP_DAL/AP_DAL_Airspeed.h AP_DAL/AP_DAL_RangeFinder.h \
         AP_DAL/AP_DAL_Beacon.h AP_DAL/AP_DAL_VisualOdom.h AP_DAL/LogStructure.h AP_NavEKF3/LogStructure.h AP_NavEKF/LogStructure.h; do H+=(--header "$RL/$f"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ekf3.cpp" -o "$OUT" --namespace EKF3_lib --nest --reachable \
  "${H[@]}" --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_Common" --lib-dir "$RL/AP_Declination" --lib-dir "$REF/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/common" \
  --use @"$HERE/ekf3.use" --sizeof NavEKF3_core="$SZ" \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ekf-types --ekf-arrays --ring-buffers --runtime-loops --pointer-params --array-offsets --world --world-pointers --swap-out --ap-param \
  --heap-alloc AP_DAL::malloc_type --drop AP_InternalError::error --drop GCS::send_text --drop AP_BoardConfig::allocation_error --drop AP_HAL::panic --drop AP_DAL::snprintf --drop NavEKF3_core::prearm_fail_string \
  --boundary AP_HAL::HAL,AP_HAL::Util,AP_AHRS,AP_Vehicle,AP_InertialSensor,AP_Baro,Compass,AP_GPS,AP_Airspeed,AP_WheelEncoder,AP_Logger --indexed-inputs \
  --boundary-call @"$HERE/ekf3_sources.boundary" --boundary-query AP_HAL::Util::available_memory \
  --boundary-fn AP_HAL::micros64,AP_HAL::micros,AP_HAL::millis,AP_HAL::millis64 --uninit-reads \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
