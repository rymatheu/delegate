#!/usr/bin/env bash
# Translate ArduPilot's AP_RTC (AP_RTC/AP_RTC.cpp) to Lean with cpp2lean, from the unmodified
# sources, with the reference compiler flags and the stub headers (README.md, "Phase 2b"): the member
# functions that do not depend on the singleton or on the C library's time functions. Left out
# (--drop; README.md, "Phase 2b", what each needs):
# - the constructor (`_singleton = this` after `if (_singleton != nullptr) return;`), get_singleton,
#   _singleton, AP::rtc(): the singleton accessor (World singleton support);
# - rsem, get_semaphore, set_utc_usec (WITH_SEMAPHORE(rsem): a HAL semaphore object, F11; set_utc_usec
#   also reads hal.util->get_soft_armed() and writes hal.util->set_hw_rtc(), boundary reads/outputs);
# - _timegm, date_fields_to_clock_s (C's `struct tm`, which on the reference platform has a
#   `char *tm_zone` member), clock_s_to_date_fields, get_date_and_time_utc (C's gmtime_r: musl's
#   __secs_to_tm is not among the translated C library functions).
# AP_RTC_LOGGING_ENABLED and AP_MAVLINK_SIGNING_ENABLED are 0 for the AST: the stub headers have neither
# AP_Logger::Write_RTC nor GCS_MAVLINK::update_signing_timestamp; both are called only in set_utc_usec,
# which is left out. Output: ardupilot/out/AP_RTC/. Usage: ardupilot/translate_rtc.sh [cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/AP_RTC"

CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0 -DAP_CUSTOMROTATIONS_ENABLED=0
  -DAP_RTC_LOGGING_ENABLED=0 -DAP_MAVLINK_SIGNING_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
# every included ArduPilot file must preprocess in the unity exactly as in its own translation unit
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_rtc.cpp" "$L/AP_RTC/AP_RTC.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_rtc.cpp" -o "$OUT" --namespace AP_RTC_lib --nest \
  --header "$L/AP_RTC/AP_RTC.h" --header "$L/AP_RTC/AP_RTC.cpp" --lib-dir "$L/AP_Math" --ap-param --boundary-fn AP_HAL::micros64 \
  --drop AP::rtc --drop AP_RTC::AP_RTC --drop AP_RTC::get_singleton --drop AP_RTC::_singleton \
  --drop AP_RTC::rsem --drop AP_RTC::get_semaphore --drop AP_RTC::set_utc_usec \
  --drop AP_RTC::_timegm --drop AP_RTC::date_fields_to_clock_s --drop AP_RTC::clock_s_to_date_fields --drop AP_RTC::get_date_and_time_utc --boundary AP_HAL::Util,AP_HAL::HAL \
  --pointer-params --runtime-loops \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
