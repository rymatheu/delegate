#!/usr/bin/env bash
# Phase 4: AP_Mission (README.md "Phase 4: AP_Mission"): command storage, the conversions between Mission_Command and
# MAVLink, init/add/replace/read/clear/truncate and the jump tracking of get_next_nav_cmd, from ArduPilot's unmodified
# AP_Mission.cpp with the reference build's flags of its unit (ardupilot/ref_flags.py) and
# AP_SDCARD_STORAGE_ENABLED 0 (as StorageManager in Phase 2b: the reference's microSD block runs only with
# BRD_SD_MISSION > 0, default 0): ardupilot/unity_mission.cpp -> ardupilot/out/Mission/Mission_lib.lean.
# AP_Mission's own files are translated as far as the entry points (ardupilot/mission.use) reach (--reachable);
# StorageManager, AP_Param, AP_Math, AP_Common and the generated MAVLink headers are libraries. Boundary: the HAL
# (storage: --hal-storage 16384; `get_soft_armed`), AP_HAL::millis, AP_AHRS (`get_home`), GCS text, AP_HAL::panic and
# INTERNAL_ERROR (left out). The three callbacks into ModeAuto (`_cmd_start_fn`, `_cmd_verify_fn`,
# `_mission_complete_fn`) are left out with the execution state machine (Phase 5). Also checks the unity
# (check_unity.py) and the record layouts the translation computed against clang's (check_layouts.py).
# Usage: ardupilot/translate_mission.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="${MISSION_OUT:-$ROOT/ardupilot/out/Mission}"
ekf_flags AP_Mission/AP_Mission.cpp
EKF_FLAGS+=(-DAP_SDCARD_STORAGE_ENABLED=0 -fno-access-control)
EKF_CA+=(--clang-arg=-DAP_SDCARD_STORAGE_ENABLED=0 --clang-arg=-fno-access-control)
# the unity check of ekf_common.sh, each file's own flags with the same two additions
SRCS=(AP_Mission/AP_Mission.cpp StorageManager/StorageManager.cpp AP_Param/AP_ParamT.cpp AP_Math/location.cpp AP_Common/Location.cpp AP_Math/AP_Math.cpp)
for s in "${SRCS[@]}"; do
  cmp -s "$RL/$s" "$AP/libraries/$s" || { echo "$s differs from ArduPilot's checkout" >&2; exit 1; }
  own=()
  while IFS= read -r a; do own+=("$a"); done < <(python3 "$ROOT/ardupilot/ref_flags.py" --ast "$s")
  if ! cmp -s <(clang++ "${own[@]}" -DAP_SDCARD_STORAGE_ENABLED=0 -fno-access-control -E -P "$RL/$s" 2>/dev/null) <(clang++ "${EKF_FLAGS[@]}" -E -P "$RL/$s" 2>/dev/null); then
    echo "$s preprocesses differently with the unity's flags than in its own unit" >&2; exit 1
  fi
done
CHECK=(python3 "$ROOT/ardupilot/check_unity.py" "$HERE/unity_mission.cpp" "${SRCS[@]/#/$RL/}" -- "${EKF_FLAGS[@]}")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_mission.cpp" -o "$OUT" --namespace Mission_lib --nest --world --world-pointers --member-objects \
  --header "$RL/AP_Mission/AP_Mission.h" --header "$RL/AP_Mission/AP_Mission.cpp" \
  --lib-dir "$REF/build/sitl/libraries/GCS_MAVLink/include" --lib-dir "$RL/StorageManager" --lib-dir "$RL/AP_Param" \
  --lib-dir "$RL/AP_Math" --lib-dir "$RL/AP_Common" --use @"$HERE/mission.use" --reachable \
  --mavlink --mission --c-strings --gotos --param-ext --ap-param --ekf-types --front-ends \
  --pointer-params --runtime-loops --general-loops --byte-objects --hal-storage 16384 \
  --boundary AP_HAL::HAL,AP_HAL::Util,AP_AHRS,GCS --boundary-fn AP_HAL::millis \
  --drop AP_Param::save --drop AP_Param::notify --drop AP_HAL::panic --drop AP_InternalError::error --drop GCS::send_text \
  --drop AP_Mission::_cmd_start_fn --drop AP_Mission::_cmd_verify_fn --drop AP_Mission::_mission_complete_fn \
  --semaphores HAL_Semaphore,WithSemaphore,AP_HAL::Semaphore,HALSITL::Semaphore \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
python3 "$HERE/check_layouts.py" "$OUT/Mission_lib.signatures.json" -- "${EKF_FLAGS[@]}"
