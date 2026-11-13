#!/usr/bin/env bash
# Translate AP_AHRS with its EKF3 and DCM backends and the view, on top of AP_DAL, AP_NavEKF and AP_NavEKF3
# (README.md, "Phase 3: AP_AHRS, and speed"), against the real ArduPilot headers and the reference build's
# configuration: ardupilot/unity_ahrs.cpp (the sources included unmodified, the AHRS a file-scope object, the
# NavEKF3 front end its backend's static member) -> ardupilot/out/AHRS/AHRS_lib.lean. One World: the AHRS
# (with the DCM and EKF3 backends' state), the front end EKF3, AP_DAL's heap singleton, the cores, the
# EKFGSF_yaw slots, the view's heap slot.
# --reachable: what the entry points of ardupilot/ahrs.use reach is translated; AP_Math and AP_Common are --lib-dir.
# --member-pointers: AP_AHRS's pointers and references to its member backends and estimates; --ahrs-ext: AP_AHRS's and
# DCM's other constructs (README.md, "Phase 3: AP_AHRS translated"). The sensor front ends, the vehicle, the HAL, GCS,
# AP_Notify, AP_Mission, SITL::SIM and AP_AHRS_SIM are the boundary (AP_AHRS_SIM::get_results dropped: AHRS_EKF_TYPE 3).
# Usage: ardupilot/translate_ahrs.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="${AHRS_OUT:-$ROOT/ardupilot/out/AHRS}"
ekf_flags AP_NavEKF3/AP_NavEKF3_core.cpp
SRCS=()
while read -r inc; do SRCS+=("$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_ahrs.cpp")
ekf_check_unity "$HERE/unity_ahrs.cpp" "${SRCS[@]}"
# sizeof(NavEKF3_core) as clang computes it with the unit's flags (AP_NavEKF3.cpp:842 compares it with the free memory)
SZ=$(printf '#include <AP_NavEKF3/AP_NavEKF3_core.h>\nunsigned long cpp2lean_sizeof = sizeof(NavEKF3_core);\n' |
     clang++ "${EKF_FLAGS[@]}" -x c++ -S -emit-llvm -o - - 2>/dev/null | sed -n 's/^@cpp2lean_sizeof = global i64 \([0-9]*\).*/\1/p')
[ -n "$SZ" ] || { echo "sizeof(NavEKF3_core) not found" >&2; exit 1; }
H=()
for f in "${SRCS[@]}"; do case "$f" in AP_Math/*|AP_Common/*|AP_Declination/*) ;; *) H+=(--header "$RL/$f");; esac; done
for f in AP_GPS/AP_GPS_FixType.h AP_NavEKF/EKF_Buffer.h AP_NavEKF/EKFGSF_yaw.h AP_NavEKF/AP_NavEKF_Source.h AP_NavEKF/AP_NavEKF_core_common.h \
         AP_NavEKF/AP_Nav_Common.h AP_NavEKF3/AP_NavEKF3.h AP_NavEKF3/AP_NavEKF3_core.h AP_DAL/AP_DAL.h AP_DAL/AP_DAL_InertialSensor.h \
         AP_DAL/AP_DAL_Baro.h AP_DAL/AP_DAL_GPS.h AP_DAL/AP_DAL_Compass.h AP_DAL/AP_DAL_Airspeed.h AP_DAL/AP_DAL_RangeFinder.h \
         AP_DAL/AP_DAL_Beacon.h AP_DAL/AP_DAL_VisualOdom.h AP_DAL/LogStructure.h AP_NavEKF3/LogStructure.h AP_NavEKF/LogStructure.h \
         AP_AHRS/AP_AHRS.h AP_AHRS/AP_AHRS_Backend.h AP_AHRS/AP_AHRS_DCM.h AP_AHRS/AP_AHRS_NavEKF3.h AP_AHRS/AP_AHRS_View.h AP_AHRS/AP_AHRS_SIM.h; do H+=(--header "$RL/$f"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_ahrs.cpp" -o "$OUT" --namespace AHRS_lib --nest --reachable \
  "${H[@]}" --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_Common" --lib-dir "$RL/AP_Declination" --lib-dir "$REF/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/common" \
  --use @"$HERE/ahrs.use" --sizeof NavEKF3_core="$SZ" --member-objects --member-pointers --ahrs-ext --general-loops \
  --semaphores HALSITL::Semaphore,WithSemaphore,AP_HAL::Semaphore \
  --drop AP_AHRS_SIM::get_results --drop AP_BoardConfig::config_error --drop GCS::send_message \
  --boundary-fn random --site-inputs \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --ekf-types --ekf-arrays --ring-buffers --runtime-loops --pointer-params --array-offsets --world --world-pointers --swap-out --ap-param \
  --heap-alloc AP_DAL::malloc_type --drop AP_InternalError::error --drop GCS::send_text --drop AP_BoardConfig::allocation_error --drop AP_HAL::panic --drop AP_DAL::snprintf --drop NavEKF3_core::prearm_fail_string \
  --boundary AP_HAL::HAL,AP_HAL::Util,AP_AHRS_SIM,SITL::SIM,AP_Notify,AP_Mission,AP_Vehicle,AP_InertialSensor,AP_Baro,Compass,AP_GPS,AP_Airspeed,AP_WheelEncoder,AP_Logger --indexed-inputs \
  --boundary-call @"$HERE/ekf3_sources.boundary" --boundary-query AP_HAL::Util::available_memory \
  --boundary-fn AP_HAL::micros64,AP_HAL::micros,AP_HAL::millis,AP_HAL::millis64 --uninit-reads \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
