#!/usr/bin/env bash
# Phase 3: the estimator as one World (README.md "Phase 3: the estimator World and the EKF3 replay"): the sensor World of
# ardupilot/translate_sensors.sh (front ends, stand-ins, scheduler stand-in) and AP_DAL + NavEKF3 of
# ardupilot/translate_ekf3.sh (with AP_NavEKF_Source translated, not a boundary), against ArduPilot's real headers and
# the reference build's flags: ardupilot/unity_estimation.cpp -> ardupilot/out/Estimation/Estimation_lib.lean.
# The options are the union of both scripts': --front-ends --ins-gps --param-ext for the front ends and AP_Param (EKF3's
# parameters are state too), --reachable and the EKF options for NavEKF3; the front ends are no longer --boundary (AP_DAL
# reads the World's objects), nor is the HAL clock (the scheduler stand-in's), nor the source selection.
# Usage: ardupilot/translate_estimation.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="${ESTIMATION_OUT:-$ROOT/ardupilot/out/Estimation}"
ekf_flags AP_NavEKF3/AP_NavEKF3_core.cpp
SRCS=()
while read -r inc; do SRCS+=("$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_estimation.cpp")
ekf_check_unity "$HERE/unity_estimation.cpp" "${SRCS[@]}" --rename=AP_Compass/AP_Compass_Backend.cpp:FILTER_KOEF=FILTER_KOEF_compass
# sizeof(NavEKF3_core) as clang computes it with the unit's flags (AP_NavEKF3.cpp:842 compares it with the free memory)
SZ=$(printf '#include <AP_NavEKF3/AP_NavEKF3_core.h>\nunsigned long cpp2lean_sizeof = sizeof(NavEKF3_core);\n' |
     clang++ "${EKF_FLAGS[@]}" -x c++ -S -emit-llvm -o - - 2>/dev/null | sed -n 's/^@cpp2lean_sizeof = global i64 \([0-9]*\).*/\1/p')
[ -n "$SZ" ] || { echo "sizeof(NavEKF3_core) not found" >&2; exit 1; }
HAL="$ROOT/reference/hal"
# the EKF sources and headers are translated files (as in translate_ekf3.sh); the front ends and libraries are --lib-dirs
H=()
for f in "${SRCS[@]}"; do case "$f" in AP_NavEKF/*|AP_NavEKF3/*|AP_DAL/*) H+=(--header "$RL/$f");; esac; done
for f in AP_NavEKF/EKF_Buffer.h AP_NavEKF/EKFGSF_yaw.h AP_NavEKF/AP_NavEKF_Source.h AP_NavEKF/AP_NavEKF_core_common.h \
         AP_NavEKF/AP_Nav_Common.h AP_NavEKF3/AP_NavEKF3.h AP_NavEKF3/AP_NavEKF3_core.h AP_DAL/AP_DAL.h AP_DAL/AP_DAL_InertialSensor.h \
         AP_DAL/AP_DAL_Baro.h AP_DAL/AP_DAL_GPS.h AP_DAL/AP_DAL_Compass.h AP_DAL/AP_DAL_Airspeed.h AP_DAL/AP_DAL_RangeFinder.h \
         AP_DAL/AP_DAL_Beacon.h AP_DAL/AP_DAL_VisualOdom.h AP_DAL/LogStructure.h AP_NavEKF3/LogStructure.h AP_NavEKF/LogStructure.h; do H+=(--header "$RL/$f"); done
LIBS=()
for d in AP_Baro AP_Compass AP_InertialSensor AP_GPS AP_RTC AP_AccelCal AP_Param AP_Math Filter AP_Common AP_HAL AP_Declination; do LIBS+=(--lib-dir "$RL/$d"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_estimation.cpp" -o "$OUT" --namespace Estimation_lib --nest --world --world-pointers --reachable --est-world \
  "${H[@]}" --header "$HAL/est_scheduler.cpp" --header "$HAL/est_scheduler.h" --header "$HAL/est_input.h" \
  "${LIBS[@]}" --lib-dir "$HAL" --lib-dir "$REF/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/common" \
  --use @"$HERE/estimation.use" --sizeof NavEKF3_core="$SZ" \
  --front-ends --ins-gps --gotos --param-ext --ap-param --ekf-types --ekf-arrays --ring-buffers --pointer-params --array-offsets \
  --runtime-loops --general-loops --swap-out --uninit-reads --indexed-inputs --output-log \
  --semaphores HAL_Semaphore,WithSemaphore,AP_HAL::Semaphore,HALSITL::Semaphore \
  --world-class SITL::SIM,CompassLearn,AP_AccelCal,AccelCalibrator \
  --param-name COMPASS_SCALE=compass._state._priv_instance[0].scale_factor --param-name COMPASS_SCALE2=compass._state._priv_instance[1].scale_factor --param-name COMPASS_SCALE3=compass._state._priv_instance[2].scale_factor \
  --boundary-query RCOutput::read_last_sent --boundary-query AP_HAL::Util::available_memory --site-inputs \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --heap-alloc AP_DAL::malloc_type \
  --boundary AP_HAL::HAL,AP_HAL::Util,AP_AHRS,AP_Vehicle,AP_Airspeed,AP_WheelEncoder,AP_Logger,GCS,AP_Notify,SRV_Channels,AP_BattMonitor,AP_SerialManager \
  --drop AP_HAL::Scheduler::_delay_cb --drop AP_HAL::Scheduler::disable_interrupts_save --drop AP_HAL::Scheduler::restore_interrupts \
  --drop AP_HAL::Scheduler::thread_create --drop AP_HAL::Scheduler::register_delay_callback --drop AP_HAL::Scheduler::call_delay_cb \
  --drop EstScheduler::register_timer_failsafe --drop AP_HAL::panic --drop GCS::send_text --drop AP_InternalError::error \
  --drop AP_Param::save --drop AP_Param::notify --drop AP_BoardConfig::config_error --drop AP_BoardConfig::allocation_error --drop BetterStream::printf \
  --drop AP_InertialSensor::fast_rate_buffer --drop AP_InertialSensor::send_uart_data --drop OpticalFlow::push_gyro \
  --drop AP_Param::convert_parameter_width --drop AP_GPS::convert_parameters --drop AP_GPS::send_blob_start --drop AP_GPS::send_blob_update \
  --drop AP_GPS_Backend::broadcast_gps_type --drop AP_GPS::rtcm_buffer --drop AP_HAL::UARTDriver::_monitor_read_buffer \
  --drop AP_DAL::snprintf --drop NavEKF3_core::prearm_fail_string --drop AP_Param::add_default \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
