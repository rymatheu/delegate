// EKF3's ring buffers (README.md, "Phase 3: EKF data structures"; PORT-PLAN.md F12): AP_NavEKF's
// type-erased ekf_ring_buffer and ekf_imu_buffer (EKF_Buffer.cpp, included unmodified) at every
// typed wrapper EKF3 instantiates in the reference configuration (the buffer members of
// AP_NavEKF3_core.h, preprocessed with the reference build's flags: two IMU buffers, eight
// observation buffers), with the element structs of AP_NavEKF3_core.h. The explicit instantiations
// below instantiate every member function of each wrapper (as the core's uses do for those it calls).
// EKF_Buffer.h has no include guard and both EKF_Buffer.cpp and AP_NavEKF3_core.h include it: `#import`
// (clang: a file once imported is not entered again by a later #include) keeps it to one copy, as in
// each file's own translation unit (check_unity.py). The flags are those of AP_NavEKF3_core.cpp's unit
// (EKF_Buffer.cpp's unit lacks only APM_BUILD_DIRECTORY, which EKF_Buffer.cpp does not test: checked).
#import <AP_NavEKF/EKF_Buffer.h>
#include <AP_NavEKF/EKF_Buffer.cpp>
#include <AP_NavEKF3/AP_NavEKF3_core.h>

template class EKF_IMU_buffer_t<NavEKF3_core::imu_elements>;
template class EKF_IMU_buffer_t<NavEKF3_core::output_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::gps_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::mag_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::baro_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::tas_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::of_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>;
template class EKF_obs_buffer_t<NavEKF3_core::yaw_elements>;
