# the estimator translation: ArduPilot source file to Lean module

`lean/Estimator_lib.lean` (936 items, 29278 lines) split into 49 modules by `tools/split_modules.py`; `tools/check_split.py` rebuilds it byte for byte from `INDEX.json`. A function is in the folder of the ArduPilot source file its doc comment cites (or of its C++ class). Modules of one folder are numbered in dependency order (`AC_PID.lean` before `AC_PID_2.lean`); the cross-library modules hold the top of the call graph, where the libraries call each other in a cycle.

## Modules

| module | lines | items | ArduPilot sources (by size) |
|---|---:|---:|---|
| `libraries/AP_AccelCal/AP_AccelCal` | 17 | 2 | `libraries/AP_AccelCal/AccelCalibrator.h` |
| `libraries/AP_HAL/AP_HAL` | 79 | 6 | `libraries/AP_HAL/Device.h`, `libraries/AP_HAL/Device.cpp`, `libraries/AP_HAL/Scheduler.h`, `libraries/AP_HAL/UARTDriver.h`, `libraries/AP_HAL/system.h` |
| `libraries/GCS_MAVLink/GCS_MAVLink` | 185 | 2 | `libraries/GCS_MAVLink/ap_message.h` |
| `mavlink/mavlink` | 91 | 7 | `(generated)` |
| `libraries/AP_Math/AP_Math` | 2321 | 152 | `libraries/AP_Math/vector3.cpp`, `libraries/AP_Math/quaternion.cpp`, `libraries/AP_Math/matrix3.cpp`, `libraries/AP_Math/matrix3.h`, `libraries/AP_Math/rotations.h`, `libraries/AP_Math/AP_Math.h` (+7) |
| `World` | 445 | 27 | `(generated)` |
| `libraries/Filter/Filter` | 324 | 16 | `libraries/Filter/LowPassFilter2p.cpp`, `libraries/Filter/LowPassFilter.cpp`, `libraries/Filter/DerivativeFilter.h`, `libraries/Filter/LowPassFilter2p.h`, `libraries/Filter/DerivativeFilter.cpp`, `libraries/Filter/FilterWithBuffer.h` |
| `libraries/AP_Common/AP_Common` | 380 | 27 | `libraries/AP_Common/Location.cpp`, `libraries/AP_Common/TSIndex.h`, `libraries/AP_Common/Location.h` |
| `libraries/AP_Declination/AP_Declination` | 109 | 2 | `libraries/AP_Declination/AP_Declination.cpp`, `libraries/AP_Declination/AP_Declination.h` |
| `libraries/AP_Param/AP_Param` | 407 | 43 | `libraries/AP_Param/AP_Param.h`, `libraries/AP_Param/AP_ParamT.cpp` |
| `libraries/SITL/SITL` | 166 | 5 | `libraries/SITL/SITL.h` |
| `libraries/AP_NavEKF/AP_NavEKF` | 1338 | 23 | `libraries/AP_NavEKF/EKFGSF_yaw.cpp`, `libraries/AP_NavEKF/AP_NavEKF_Source.h`, `libraries/AP_NavEKF/AP_Nav_Common.h`, `libraries/AP_NavEKF/EKFGSF_yaw.h`, `libraries/AP_NavEKF/LogStructure.h`, `libraries/AP_NavEKF/AP_NavEKF_Source.cpp` (+2) |
| `libraries/AP_RTC/AP_RTC` | 68 | 3 | `libraries/AP_RTC/AP_RTC.h`, `libraries/AP_RTC/JitterCorrection.h`, `libraries/AP_RTC/JitterCorrection.cpp` |
| `libraries/AP_Compass/AP_Compass` | 234 | 10 | `libraries/AP_Compass/Compass_PerMotor.h`, `libraries/AP_Compass/AP_Compass.h`, `libraries/AP_Compass/Compass_PerMotor.cpp`, `libraries/AP_Compass/AP_Compass_SITL.h`, `libraries/AP_Compass/AP_Compass_Backend.cpp` |
| `libraries/AP_GPS/AP_GPS` | 587 | 19 | `libraries/AP_GPS/AP_GPS.h`, `libraries/AP_GPS/GPS_Backend.h`, `libraries/AP_GPS/AP_GPS_FixType.h`, `libraries/AP_GPS/AP_GPS_SITL.h`, `libraries/AP_GPS/AP_GPS.cpp`, `libraries/AP_GPS/GPS_Backend.cpp` |
| `libraries/AP_InertialSensor/AP_InertialSensor` | 701 | 18 | `libraries/AP_InertialSensor/AP_InertialSensor.h`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.h`, `libraries/AP_InertialSensor/AP_InertialSensor.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor_SITL.h`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.cpp` |
| `libraries/AP_NavEKF3/AP_NavEKF3` | 1173 | 32 | `libraries/AP_NavEKF3/LogStructure.h`, `libraries/AP_NavEKF3/AP_NavEKF3.h`, `libraries/AP_NavEKF3/AP_NavEKF3_core.h`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp` |
| `libraries/AP_AHRS/AP_AHRS` | 1055 | 34 | `libraries/AP_AHRS/AP_AHRS_Backend.h`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_DCM.h`, `libraries/AP_AHRS/AP_AHRS_Backend.cpp`, `libraries/AP_AHRS/AP_AHRS_View.h`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h` (+2) |
| `libraries/AP_Baro/AP_Baro` | 384 | 19 | `libraries/AP_Baro/AP_Baro.h`, `libraries/AP_Baro/AP_Baro_atmosphere.cpp`, `libraries/AP_Baro/AP_Baro_Backend.h`, `libraries/AP_Baro/AP_Baro.cpp`, `libraries/AP_Baro/AP_Baro_SITL.h` |
| `libraries/AP_DAL/AP_DAL` | 1284 | 76 | `libraries/AP_DAL/LogStructure.h`, `libraries/AP_DAL/AP_DAL.h`, `libraries/AP_DAL/AP_DAL_GPS.h`, `libraries/AP_DAL/AP_DAL_InertialSensor.h`, `libraries/AP_DAL/AP_DAL_Compass.h`, `libraries/AP_DAL/AP_DAL.cpp` (+4) |
| `libraries/AP_Math/AP_Math_2` | 51 | 9 | `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/vectorN.h` |
| `World_2` | 61 | 2 | `(generated)` |
| `libraries/AP_Common/AP_Common_2` | 38 | 4 | `libraries/AP_Common/TSIndex.h` |
| `libraries/AP_Param/AP_Param_2` | 177 | 15 | `libraries/AP_Param/AP_ParamT.cpp`, `libraries/AP_Param/AP_Param.h` |
| `libraries/AP_NavEKF/AP_NavEKF_2` | 1306 | 56 | `libraries/AP_NavEKF/EKF_Buffer.cpp`, `libraries/AP_NavEKF/EKF_Buffer.h`, `libraries/AP_NavEKF/AP_NavEKF_Source.cpp`, `libraries/AP_NavEKF/AP_NavEKF_Source.h` |
| `libraries/AP_Compass/AP_Compass_2` | 496 | 10 | `libraries/AP_Compass/AP_Compass.cpp`, `libraries/AP_Compass/AP_Compass.h` |
| `libraries/AP_NavEKF3/AP_NavEKF3_2` | 1229 | 38 | `libraries/AP_NavEKF3/AP_NavEKF3_core.h`, `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_GyroBias.cpp` (+4) |
| `libraries/AP_Baro/AP_Baro_2` | 45 | 2 | `libraries/AP_Baro/AP_Baro_SITL.h`, `libraries/AP_Baro/AP_Baro_Backend.cpp` |
| `World_3` | 141 | 12 | `(generated)` |
| `libraries/AP_Param/AP_Param_3` | 42 | 2 | `libraries/AP_Param/AP_Param.h` |
| `libraries/AP_RTC/AP_RTC_2` | 129 | 2 | `libraries/AP_RTC/AP_RTC.cpp` |
| `libraries/AP_Compass/AP_Compass_3` | 438 | 16 | `libraries/AP_Compass/AP_Compass_Backend.cpp`, `libraries/AP_Compass/AP_Compass.h`, `libraries/AP_Compass/AP_Compass.cpp` |
| `libraries/AP_GPS/AP_GPS_2` | 889 | 16 | `libraries/AP_GPS/AP_GPS.cpp`, `libraries/AP_GPS/GPS_Backend.h`, `libraries/AP_GPS/GPS_Backend.cpp`, `libraries/AP_GPS/AP_GPS.h`, `libraries/AP_GPS/AP_GPS_SITL.h` |
| `libraries/AP_InertialSensor/AP_InertialSensor_2` | 773 | 20 | `libraries/AP_InertialSensor/AP_InertialSensor_Backend.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.h` |
| `libraries/AP_NavEKF3/AP_NavEKF3_3` | 3902 | 75 | `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp` (+4) |
| `libraries/AP_AHRS/AP_AHRS_2` | 1397 | 37 | `libraries/AP_AHRS/AP_AHRS.cpp`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS_Backend.cpp`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h`, `libraries/AP_AHRS/AP_AHRS_View.cpp` (+1) |
| `libraries/AP_Baro/AP_Baro_3` | 145 | 7 | `libraries/AP_Baro/AP_Baro_Backend.cpp`, `libraries/AP_Baro/AP_Baro.cpp` |
| `libraries/AP_DAL/AP_DAL_2` | 301 | 10 | `libraries/AP_DAL/AP_DAL.cpp`, `libraries/AP_DAL/AP_DAL.h`, `libraries/AP_DAL/AP_DAL_GPS.cpp`, `libraries/AP_DAL/AP_DAL_InertialSensor.cpp`, `libraries/AP_DAL/AP_DAL_Baro.cpp`, `libraries/AP_DAL/AP_DAL_Compass.cpp` |
| `libraries/AP_Math/AP_Math_3` | 17 | 1 | `libraries/AP_Math/AP_Math.cpp` |
| `World_4` | 153 | 6 | `(generated)` |
| `libraries/AP_Common/AP_Common_3` | 83 | 1 | `libraries/AP_Common/Location.cpp` |
| `libraries/AP_NavEKF/AP_NavEKF_3` | 181 | 3 | `libraries/AP_NavEKF/AP_NavEKF_Source.cpp`, `libraries/AP_NavEKF/AP_NavEKF_core_common.cpp` |
| `libraries/AP_InertialSensor/AP_InertialSensor_3` | 607 | 5 | `libraries/AP_InertialSensor/AP_InertialSensor.cpp` |
| `libraries/AP_NavEKF3/AP_NavEKF3_4` | 3051 | 26 | `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_MagFusion.cpp` (+2) |
| `libraries/AP_AHRS/AP_AHRS_3` | 982 | 23 | `libraries/AP_AHRS/AP_AHRS.cpp`, `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.cpp`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h`, `libraries/AP_AHRS/AP_AHRS_View.h` |
| `libraries/AP_Baro/AP_Baro_4` | 365 | 4 | `libraries/AP_Baro/AP_Baro.cpp`, `libraries/AP_Baro/AP_Baro_atmosphere.cpp` |
| `World_5` | 15 | 1 | `(generated)` |
| `libraries/AP_Compass/AP_Compass_4` | 228 | 3 | `libraries/AP_Compass/AP_Compass.cpp` |
| `libraries/AP_AHRS/AP_AHRS_4` | 650 | 7 | `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS.cpp` |

## ArduPilot source files

| source file | modules (items) |
|---|---|
| `(World: generated)` | `World` (27), `World_2` (2), `World_3` (12), `World_4` (6), `World_5` (1) |
| `(mavlink: generated)` | `mavlink/mavlink` (7) |
| `libraries/AP_AHRS/AP_AHRS.cpp` | `libraries/AP_AHRS/AP_AHRS` (3), `libraries/AP_AHRS/AP_AHRS_2` (16), `libraries/AP_AHRS/AP_AHRS_3` (10), `libraries/AP_AHRS/AP_AHRS_4` (1) |
| `libraries/AP_AHRS/AP_AHRS.h` | `libraries/AP_AHRS/AP_AHRS` (3), `libraries/AP_AHRS/AP_AHRS_2` (4), `libraries/AP_AHRS/AP_AHRS_3` (1) |
| `libraries/AP_AHRS/AP_AHRS_Backend.cpp` | `libraries/AP_AHRS/AP_AHRS` (2), `libraries/AP_AHRS/AP_AHRS_2` (4) |
| `libraries/AP_AHRS/AP_AHRS_Backend.h` | `libraries/AP_AHRS/AP_AHRS` (17) |
| `libraries/AP_AHRS/AP_AHRS_DCM.cpp` | `libraries/AP_AHRS/AP_AHRS_2` (5), `libraries/AP_AHRS/AP_AHRS_3` (4), `libraries/AP_AHRS/AP_AHRS_4` (6) |
| `libraries/AP_AHRS/AP_AHRS_DCM.h` | `libraries/AP_AHRS/AP_AHRS` (5) |
| `libraries/AP_AHRS/AP_AHRS_NavEKF3.cpp` | `libraries/AP_AHRS/AP_AHRS_2` (1), `libraries/AP_AHRS/AP_AHRS_3` (4) |
| `libraries/AP_AHRS/AP_AHRS_NavEKF3.h` | `libraries/AP_AHRS/AP_AHRS` (1), `libraries/AP_AHRS/AP_AHRS_2` (5), `libraries/AP_AHRS/AP_AHRS_3` (3) |
| `libraries/AP_AHRS/AP_AHRS_SIM.h` | `libraries/AP_AHRS/AP_AHRS` (1) |
| `libraries/AP_AHRS/AP_AHRS_View.cpp` | `libraries/AP_AHRS/AP_AHRS_2` (2) |
| `libraries/AP_AHRS/AP_AHRS_View.h` | `libraries/AP_AHRS/AP_AHRS` (2), `libraries/AP_AHRS/AP_AHRS_3` (1) |
| `libraries/AP_AccelCal/AccelCalibrator.h` | `libraries/AP_AccelCal/AP_AccelCal` (2) |
| `libraries/AP_Baro/AP_Baro.cpp` | `libraries/AP_Baro/AP_Baro` (2), `libraries/AP_Baro/AP_Baro_3` (2), `libraries/AP_Baro/AP_Baro_4` (3) |
| `libraries/AP_Baro/AP_Baro.h` | `libraries/AP_Baro/AP_Baro` (6) |
| `libraries/AP_Baro/AP_Baro_Backend.cpp` | `libraries/AP_Baro/AP_Baro_2` (1), `libraries/AP_Baro/AP_Baro_3` (5) |
| `libraries/AP_Baro/AP_Baro_Backend.h` | `libraries/AP_Baro/AP_Baro` (1) |
| `libraries/AP_Baro/AP_Baro_SITL.h` | `libraries/AP_Baro/AP_Baro` (1), `libraries/AP_Baro/AP_Baro_2` (1) |
| `libraries/AP_Baro/AP_Baro_atmosphere.cpp` | `libraries/AP_Baro/AP_Baro` (9), `libraries/AP_Baro/AP_Baro_4` (1) |
| `libraries/AP_Common/Location.cpp` | `libraries/AP_Common/AP_Common` (11), `libraries/AP_Common/AP_Common_3` (1) |
| `libraries/AP_Common/Location.h` | `libraries/AP_Common/AP_Common` (3) |
| `libraries/AP_Common/TSIndex.h` | `libraries/AP_Common/AP_Common` (13), `libraries/AP_Common/AP_Common_2` (4) |
| `libraries/AP_Compass/AP_Compass.cpp` | `libraries/AP_Compass/AP_Compass_2` (6), `libraries/AP_Compass/AP_Compass_3` (4), `libraries/AP_Compass/AP_Compass_4` (3) |
| `libraries/AP_Compass/AP_Compass.h` | `libraries/AP_Compass/AP_Compass` (1), `libraries/AP_Compass/AP_Compass_2` (4), `libraries/AP_Compass/AP_Compass_3` (3) |
| `libraries/AP_Compass/AP_Compass_Backend.cpp` | `libraries/AP_Compass/AP_Compass` (3), `libraries/AP_Compass/AP_Compass_3` (9) |
| `libraries/AP_Compass/AP_Compass_SITL.h` | `libraries/AP_Compass/AP_Compass` (1) |
| `libraries/AP_Compass/Compass_PerMotor.cpp` | `libraries/AP_Compass/AP_Compass` (2) |
| `libraries/AP_Compass/Compass_PerMotor.h` | `libraries/AP_Compass/AP_Compass` (3) |
| `libraries/AP_DAL/AP_DAL.cpp` | `libraries/AP_DAL/AP_DAL` (3), `libraries/AP_DAL/AP_DAL_2` (2) |
| `libraries/AP_DAL/AP_DAL.h` | `libraries/AP_DAL/AP_DAL` (9), `libraries/AP_DAL/AP_DAL_2` (3) |
| `libraries/AP_DAL/AP_DAL_Airspeed.cpp` | `libraries/AP_DAL/AP_DAL` (1) |
| `libraries/AP_DAL/AP_DAL_Airspeed.h` | `libraries/AP_DAL/AP_DAL` (5) |
| `libraries/AP_DAL/AP_DAL_Baro.cpp` | `libraries/AP_DAL/AP_DAL_2` (2) |
| `libraries/AP_DAL/AP_DAL_Baro.h` | `libraries/AP_DAL/AP_DAL` (3) |
| `libraries/AP_DAL/AP_DAL_Compass.cpp` | `libraries/AP_DAL/AP_DAL_2` (1) |
| `libraries/AP_DAL/AP_DAL_Compass.h` | `libraries/AP_DAL/AP_DAL` (7) |
| `libraries/AP_DAL/AP_DAL_GPS.cpp` | `libraries/AP_DAL/AP_DAL_2` (1) |
| `libraries/AP_DAL/AP_DAL_GPS.h` | `libraries/AP_DAL/AP_DAL` (8) |
| `libraries/AP_DAL/AP_DAL_InertialSensor.cpp` | `libraries/AP_DAL/AP_DAL` (1), `libraries/AP_DAL/AP_DAL_2` (1) |
| `libraries/AP_DAL/AP_DAL_InertialSensor.h` | `libraries/AP_DAL/AP_DAL` (8) |
| `libraries/AP_DAL/LogStructure.h` | `libraries/AP_DAL/AP_DAL` (31) |
| `libraries/AP_Declination/AP_Declination.cpp` | `libraries/AP_Declination/AP_Declination` (1) |
| `libraries/AP_Declination/AP_Declination.h` | `libraries/AP_Declination/AP_Declination` (1) |
| `libraries/AP_GPS/AP_GPS.cpp` | `libraries/AP_GPS/AP_GPS` (1), `libraries/AP_GPS/AP_GPS_2` (10) |
| `libraries/AP_GPS/AP_GPS.h` | `libraries/AP_GPS/AP_GPS` (8), `libraries/AP_GPS/AP_GPS_2` (2) |
| `libraries/AP_GPS/AP_GPS_FixType.h` | `libraries/AP_GPS/AP_GPS` (3) |
| `libraries/AP_GPS/AP_GPS_SITL.h` | `libraries/AP_GPS/AP_GPS` (1), `libraries/AP_GPS/AP_GPS_2` (1) |
| `libraries/AP_GPS/GPS_Backend.cpp` | `libraries/AP_GPS/AP_GPS` (1), `libraries/AP_GPS/AP_GPS_2` (2) |
| `libraries/AP_GPS/GPS_Backend.h` | `libraries/AP_GPS/AP_GPS` (5), `libraries/AP_GPS/AP_GPS_2` (1) |
| `libraries/AP_HAL/Device.cpp` | `libraries/AP_HAL/AP_HAL` (2) |
| `libraries/AP_HAL/Device.h` | `libraries/AP_HAL/AP_HAL` (1) |
| `libraries/AP_HAL/Scheduler.h` | `libraries/AP_HAL/AP_HAL` (1) |
| `libraries/AP_HAL/UARTDriver.h` | `libraries/AP_HAL/AP_HAL` (1) |
| `libraries/AP_HAL/system.h` | `libraries/AP_HAL/AP_HAL` (1) |
| `libraries/AP_InertialSensor/AP_InertialSensor.cpp` | `libraries/AP_InertialSensor/AP_InertialSensor` (3), `libraries/AP_InertialSensor/AP_InertialSensor_2` (8), `libraries/AP_InertialSensor/AP_InertialSensor_3` (5) |
| `libraries/AP_InertialSensor/AP_InertialSensor.h` | `libraries/AP_InertialSensor/AP_InertialSensor` (7) |
| `libraries/AP_InertialSensor/AP_InertialSensor_Backend.cpp` | `libraries/AP_InertialSensor/AP_InertialSensor` (2), `libraries/AP_InertialSensor/AP_InertialSensor_2` (10) |
| `libraries/AP_InertialSensor/AP_InertialSensor_Backend.h` | `libraries/AP_InertialSensor/AP_InertialSensor` (5), `libraries/AP_InertialSensor/AP_InertialSensor_2` (2) |
| `libraries/AP_InertialSensor/AP_InertialSensor_SITL.h` | `libraries/AP_InertialSensor/AP_InertialSensor` (1) |
| `libraries/AP_Math/AP_Math.cpp` | `libraries/AP_Math/AP_Math` (16), `libraries/AP_Math/AP_Math_3` (1) |
| `libraries/AP_Math/AP_Math.h` | `libraries/AP_Math/AP_Math` (35), `libraries/AP_Math/AP_Math_2` (8) |
| `libraries/AP_Math/ftype.h` | `libraries/AP_Math/AP_Math` (2) |
| `libraries/AP_Math/location.cpp` | `libraries/AP_Math/AP_Math` (2) |
| `libraries/AP_Math/matrix3.cpp` | `libraries/AP_Math/AP_Math` (13) |
| `libraries/AP_Math/matrix3.h` | `libraries/AP_Math/AP_Math` (11) |
| `libraries/AP_Math/quaternion.cpp` | `libraries/AP_Math/AP_Math` (14) |
| `libraries/AP_Math/quaternion.h` | `libraries/AP_Math/AP_Math` (6) |
| `libraries/AP_Math/rotations.h` | `libraries/AP_Math/AP_Math` (3) |
| `libraries/AP_Math/vector2.cpp` | `libraries/AP_Math/AP_Math` (7) |
| `libraries/AP_Math/vector2.h` | `libraries/AP_Math/AP_Math` (8) |
| `libraries/AP_Math/vector3.cpp` | `libraries/AP_Math/AP_Math` (24) |
| `libraries/AP_Math/vector3.h` | `libraries/AP_Math/AP_Math` (11) |
| `libraries/AP_Math/vectorN.h` | `libraries/AP_Math/AP_Math_2` (1) |
| `libraries/AP_NavEKF/AP_NavEKF_Source.cpp` | `libraries/AP_NavEKF/AP_NavEKF` (3), `libraries/AP_NavEKF/AP_NavEKF_2` (3), `libraries/AP_NavEKF/AP_NavEKF_3` (2) |
| `libraries/AP_NavEKF/AP_NavEKF_Source.h` | `libraries/AP_NavEKF/AP_NavEKF` (4), `libraries/AP_NavEKF/AP_NavEKF_2` (1) |
| `libraries/AP_NavEKF/AP_NavEKF_core_common.cpp` | `libraries/AP_NavEKF/AP_NavEKF_3` (1) |
| `libraries/AP_NavEKF/AP_NavEKF_core_common.h` | `libraries/AP_NavEKF/AP_NavEKF` (1) |
| `libraries/AP_NavEKF/AP_Nav_Common.h` | `libraries/AP_NavEKF/AP_NavEKF` (5) |
| `libraries/AP_NavEKF/EKFGSF_yaw.cpp` | `libraries/AP_NavEKF/AP_NavEKF` (6) |
| `libraries/AP_NavEKF/EKFGSF_yaw.h` | `libraries/AP_NavEKF/AP_NavEKF` (1) |
| `libraries/AP_NavEKF/EKF_Buffer.cpp` | `libraries/AP_NavEKF/AP_NavEKF_2` (33) |
| `libraries/AP_NavEKF/EKF_Buffer.h` | `libraries/AP_NavEKF/AP_NavEKF` (1), `libraries/AP_NavEKF/AP_NavEKF_2` (19) |
| `libraries/AP_NavEKF/LogStructure.h` | `libraries/AP_NavEKF/AP_NavEKF` (2) |
| `libraries/AP_NavEKF3/AP_NavEKF3.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3` (2), `libraries/AP_NavEKF3/AP_NavEKF3_2` (2), `libraries/AP_NavEKF3/AP_NavEKF3_3` (35), `libraries/AP_NavEKF3/AP_NavEKF3_4` (11) |
| `libraries/AP_NavEKF3/AP_NavEKF3.h` | `libraries/AP_NavEKF3/AP_NavEKF3` (4), `libraries/AP_NavEKF3/AP_NavEKF3_3` (1) |
| `libraries/AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (1) |
| `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3` (1), `libraries/AP_NavEKF3/AP_NavEKF3_2` (1), `libraries/AP_NavEKF3/AP_NavEKF3_3` (3), `libraries/AP_NavEKF3/AP_NavEKF3_4` (4) |
| `libraries/AP_NavEKF3/AP_NavEKF3_GyroBias.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (1), `libraries/AP_NavEKF3/AP_NavEKF3_3` (1), `libraries/AP_NavEKF3/AP_NavEKF3_4` (1) |
| `libraries/AP_NavEKF3/AP_NavEKF3_MagFusion.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (1), `libraries/AP_NavEKF3/AP_NavEKF3_3` (1), `libraries/AP_NavEKF3/AP_NavEKF3_4` (1) |
| `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3` (1), `libraries/AP_NavEKF3/AP_NavEKF3_3` (13), `libraries/AP_NavEKF3/AP_NavEKF3_4` (2) |
| `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (16), `libraries/AP_NavEKF3/AP_NavEKF3_3` (11), `libraries/AP_NavEKF3/AP_NavEKF3_4` (2) |
| `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (2), `libraries/AP_NavEKF3/AP_NavEKF3_3` (3), `libraries/AP_NavEKF3/AP_NavEKF3_4` (2) |
| `libraries/AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (1), `libraries/AP_NavEKF3/AP_NavEKF3_3` (1) |
| `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp` | `libraries/AP_NavEKF3/AP_NavEKF3_2` (3), `libraries/AP_NavEKF3/AP_NavEKF3_3` (6), `libraries/AP_NavEKF3/AP_NavEKF3_4` (3) |
| `libraries/AP_NavEKF3/AP_NavEKF3_core.h` | `libraries/AP_NavEKF3/AP_NavEKF3` (10), `libraries/AP_NavEKF3/AP_NavEKF3_2` (10) |
| `libraries/AP_NavEKF3/LogStructure.h` | `libraries/AP_NavEKF3/AP_NavEKF3` (14) |
| `libraries/AP_Param/AP_Param.h` | `libraries/AP_Param/AP_Param` (41), `libraries/AP_Param/AP_Param_2` (6), `libraries/AP_Param/AP_Param_3` (2) |
| `libraries/AP_Param/AP_ParamT.cpp` | `libraries/AP_Param/AP_Param` (2), `libraries/AP_Param/AP_Param_2` (9) |
| `libraries/AP_RTC/AP_RTC.cpp` | `libraries/AP_RTC/AP_RTC_2` (2) |
| `libraries/AP_RTC/AP_RTC.h` | `libraries/AP_RTC/AP_RTC` (1) |
| `libraries/AP_RTC/JitterCorrection.cpp` | `libraries/AP_RTC/AP_RTC` (1) |
| `libraries/AP_RTC/JitterCorrection.h` | `libraries/AP_RTC/AP_RTC` (1) |
| `libraries/Filter/DerivativeFilter.cpp` | `libraries/Filter/Filter` (1) |
| `libraries/Filter/DerivativeFilter.h` | `libraries/Filter/Filter` (1) |
| `libraries/Filter/FilterWithBuffer.h` | `libraries/Filter/Filter` (1) |
| `libraries/Filter/LowPassFilter.cpp` | `libraries/Filter/Filter` (4) |
| `libraries/Filter/LowPassFilter2p.cpp` | `libraries/Filter/Filter` (7) |
| `libraries/Filter/LowPassFilter2p.h` | `libraries/Filter/Filter` (2) |
| `libraries/GCS_MAVLink/ap_message.h` | `libraries/GCS_MAVLink/GCS_MAVLink` (2) |
| `libraries/SITL/SITL.h` | `libraries/SITL/SITL` (5) |
