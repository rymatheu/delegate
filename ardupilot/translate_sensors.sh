#!/usr/bin/env bash
# Phase 3: the sensor front ends with the reference's sensor stand-ins and the HAL scheduler stand-in as one
# World (README.md "Phase 3: sensor front ends and AP_Param"; AP_InertialSensor, AP_GPS, AP_RTC and the GPS port
# stand-in: "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source"), against ArduPilot's real headers and the
# reference build's flags: ardupilot/unity_sensors.cpp -> ardupilot/out/Sensors/Sensors_lib.lean.
# The front ends, AP_Param, AP_Math, Filter, AP_Common, AP_HAL and the stand-ins (reference/hal/sensors*.cpp)
# are libraries: only what the entry points of ardupilot/Sensors.use reach is translated (the vehicle's init
# and scheduled updates, the getters AP_DAL and AP_AHRS read); the scheduler stand-in is translated whole.
# Usage: ardupilot/translate_sensors.sh [extra cpp2lean options]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
. "$HERE/ekf_common.sh"
OUT="$ROOT/ardupilot/out/Sensors"
ekf_flags AP_Baro/AP_Baro.cpp
SRCS=()
while read -r inc; do SRCS+=("$inc"); done < <(sed -n 's/^#include <\(.*\.cpp\)>$/\1/p' "$HERE/unity_sensors.cpp")
ekf_check_unity "$HERE/unity_sensors.cpp" "${SRCS[@]}" --rename=AP_Compass/AP_Compass_Backend.cpp:FILTER_KOEF=FILTER_KOEF_compass
HAL="$ROOT/reference/hal"
LIBS=()
for d in AP_Baro AP_Compass AP_InertialSensor AP_GPS AP_RTC AP_AccelCal AP_Param AP_Math Filter AP_Common AP_HAL AP_Declination; do LIBS+=(--lib-dir "$RL/$d"); done
cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_sensors.cpp" -o "$OUT" --namespace Sensors_lib --nest --world --world-pointers \
  --header "$HAL/est_scheduler.cpp" --header "$HAL/est_scheduler.h" --header "$HAL/est_input.h" \
  "${LIBS[@]}" --lib-dir "$HAL" --use @"$HERE/Sensors.use" \
  --front-ends --ins-gps --gotos --param-ext --ap-param --ekf-types --ekf-arrays --pointer-params --runtime-loops --general-loops \
  --semaphores HAL_Semaphore,WithSemaphore,AP_HAL::Semaphore,HALSITL::Semaphore \
  --world-class SITL::SIM,CompassLearn,AP_AccelCal,AccelCalibrator --param-name COMPASS_SCALE=compass._state._priv_instance[0].scale_factor --param-name COMPASS_SCALE2=compass._state._priv_instance[1].scale_factor --param-name COMPASS_SCALE3=compass._state._priv_instance[2].scale_factor --boundary-query RCOutput::read_last_sent --site-inputs \
  --type-name 'Vector2<double>=Vector2p' --type-name 'Vector3<double>=Vector3p' \
  --boundary AP_HAL::HAL,AP_AHRS,GCS,AP_Notify,SRV_Channels,AP_BattMonitor,AP_SerialManager --output-log \
  --drop AP_HAL::Scheduler::_delay_cb --drop AP_HAL::Scheduler::disable_interrupts_save --drop AP_HAL::Scheduler::restore_interrupts \
  --drop AP_HAL::Scheduler::thread_create --drop AP_HAL::Scheduler::register_delay_callback --drop AP_HAL::Scheduler::call_delay_cb \
  --drop EstScheduler::register_timer_failsafe --drop AP_HAL::panic --drop GCS::send_text --drop AP_InternalError::error \
  --drop AP_Param::save --drop AP_Param::notify --drop AP_BoardConfig::config_error --drop BetterStream::printf \
  --drop AP_InertialSensor::fast_rate_buffer --drop AP_InertialSensor::send_uart_data --drop OpticalFlow::push_gyro \
  --drop AP_Param::convert_parameter_width --drop AP_GPS::convert_parameters --drop AP_GPS::send_blob_start --drop AP_GPS::send_blob_update --drop AP_GPS_Backend::broadcast_gps_type --drop AP_GPS::rtcm_buffer --drop AP_HAL::UARTDriver::_monitor_read_buffer \
  --src-root "$RL" "${EKF_CA[@]}" "$@"
