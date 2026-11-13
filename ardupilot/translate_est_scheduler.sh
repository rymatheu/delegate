#!/usr/bin/env bash
# Phase 3: the HAL scheduler stand-in of the estimator (reference/hal/est_scheduler.cpp) as a World, with
# ArduPilot's real headers and the reference configuration (build/reference/ap, waf's ap_config.h and
# hwdef.h; reference/hal first on the include path, as reference/build.py compiles):
# unity_est_scheduler.cpp -> out/EstScheduler/EstScheduler_lib.lean.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${REF_AP:-$ROOT/build/reference/ap}"
B="$AP/build/sitl"
L="$AP/libraries"
OUT="$HERE/out/EstScheduler"
# the include path of reference/build.py: reference/hal first, then waf's (generated headers, libraries)
INC=(-I "$ROOT/reference/hal" -I "$B/libraries" -I "$B/libraries/GCS_MAVLink" -I "$B" -I "$L" -I "$L/AP_Common/missing")
CLANG_ARGS=(-std=gnu++11 -fsigned-char -cl-single-precision-constant -ftrapping-math -D__AP_LINE__=__LINE__
  -DHAL_NAVEKF2_AVAILABLE=1 -DARDUPILOT_BUILD -DAP_NETWORKING_ENABLED=0 -include ap_config.h -DAP_ROMFS_ENABLED=1
  -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DAP_DDS_ENABLED=0 -DAP_SCRIPTING_CHECKS=1 -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"' -Wno-invalid-offsetof -Wno-macro-redefined)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_est_scheduler.cpp" -o "$OUT" --namespace EstScheduler_lib --nest --world --world-pointers \
  --header "$ROOT/reference/hal/est_scheduler.cpp" --header "$ROOT/reference/hal/est_scheduler.h" --header "$ROOT/reference/hal/est_input.h" \
  --lib-dir "$L/AP_HAL" --lib-dir "$L/AP_Math" --pointer-params --runtime-loops --general-loops --front-ends \
  --drop AP_HAL::Scheduler::_delay_cb --drop AP_HAL::Scheduler::disable_interrupts_save --drop AP_HAL::Scheduler::restore_interrupts \
  --drop AP_HAL::Scheduler::thread_create --drop AP_HAL::Scheduler::register_delay_callback --drop AP_HAL::Scheduler::call_delay_cb \
  --drop EstScheduler::register_timer_failsafe \
  --src-root "$L" "${INC[@]}" "${CA[@]}" "$@"
