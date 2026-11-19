// stubs_logger.cpp: logging and the ground-station link, and what stands in.
//
// Logging (AP_Logger, the *_Logging.cpp files of the libraries, the IMU batch sampler) and the
// MAVLink ground-station link (GCS) are outside the module: the estimator writes to them and reads
// three answers back. The stand-ins drop every write and answer as a vehicle that is not logging.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP::logger(), AP_Logger::_singleton      logging. A logger object in zeroed storage that is
//                                            never constructed; the singleton pointer is null, as
//                                            the code that tests it expects of "no logger".
//   AP_Logger::Write*, WriteBlock,           log writes (ArduCopter's LOG_BITMASK logs them in
//   WriteStreaming, WriteReplayBlock,        SITL). Dropped. WriteReplayBlock returns true.
//   Write_Error, Write_Event, Write_Message
//   AP_Logger::should_log                    false: no log is being written.
//   AP_Logger::logging_started               false.
//   AP_Logger::allow_start_ekf               true, as AP_Logger answers when LOG_REPLAY is 0 (its
//                                            default): EKF3 starts without waiting for a log.
//   AP_InertialSensor::BatchSampler          IMU batch sampling for logs (INS_LOG_BAT_MASK 0):
//   (init, sample, var_info)                 no-ops, an empty parameter table (its INS_LOG_BAT_
//                                            parameters stay 0, as at their defaults but
//                                            INS_LOG_BAT_CNT, which only sizes the log buffer).
//   AP_InertialSensor_Backend::Write_ACC,    the libraries' log writers (AP_InertialSensor_Logging,
//   Write_GYR, AP_Baro::Write_Baro,          AP_Baro_Logging, AP_Compass_Logging,
//   Compass::Write_Compass,                  AP_AHRS_Logging). Dropped.
//   AP_AHRS::Write_Origin
//   gcs(), GCS::send_message                 the ground-station link's messages (MSG_ORIGIN, ...).
//                                            Dropped.
//   GCS::send_text                           status texts ("EKF3 IMU0 initialised", "EKF3 IMU0 is
//                                            using GPS", ...): formatted as GCS::send_textv formats
//                                            them (50 characters) and queued (up to 8); the adapter
//                                            hands one per tick to the supervisor (est_text_*),
//                                            whose GCS sends it, as the one GCS of ArduCopter does.
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <AP_Logger/AP_Logger.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_InertialSensor/AP_InertialSensor_Backend.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_AHRS/AP_AHRS.h>
#include <GCS_MAVLink/GCS.h>

// --- the logger
AP_Logger *AP_Logger::_singleton = nullptr;
alignas(AP_Logger) static unsigned char logger_storage[sizeof(AP_Logger)];

namespace AP {
AP_Logger &logger()
{
    return *reinterpret_cast<AP_Logger *>(logger_storage);
}
}

void AP_Logger::WriteBlock(const void *pBuffer, uint16_t size) {}
bool AP_Logger::WriteReplayBlock(uint8_t msg_id, const void *pBuffer, uint16_t size) { return true; }
void AP_Logger::Write_Event(LogEvent id) {}
void AP_Logger::Write_Error(LogErrorSubsystem sub_system, LogErrorCode error_code) {}
void AP_Logger::Write_Message(const char *message) {}
void AP_Logger::Write(const char *name, const char *labels, const char *fmt, ...) {}
void AP_Logger::Write(const char *name, const char *labels, const char *units, const char *mults,
                      const char *fmt, ...) {}
void AP_Logger::WriteStreaming(const char *name, const char *labels, const char *fmt, ...) {}
void AP_Logger::WriteStreaming(const char *name, const char *labels, const char *units,
                               const char *mults, const char *fmt, ...) {}
bool AP_Logger::should_log(uint32_t mask) const { return false; }
bool AP_Logger::logging_started(void) const { return false; }
bool AP_Logger::allow_start_ekf() const { return true; }

// --- the IMU batch sampler
const struct AP_Param::GroupInfo AP_InertialSensor::BatchSampler::var_info[] = {
    AP_GROUPEND
};
void AP_InertialSensor::BatchSampler::init() {}
void AP_InertialSensor::BatchSampler::sample(uint8_t instance, IMU_SENSOR_TYPE _type,
                                             uint64_t sample_us, const Vector3f &sample) {}

// --- the libraries' log writers
void AP_InertialSensor_Backend::Write_ACC(const uint8_t instance, const uint64_t sample_us,
                                          const Vector3f &accel) const {}
void AP_InertialSensor_Backend::Write_GYR(const uint8_t instance, const uint64_t sample_us,
                                          const Vector3f &gyro, bool use_sample_timestamp) const {}
void AP_Baro::Write_Baro(void) {}
void Compass::Write_Compass(void) {}
void AP_AHRS::Write_Origin(LogOriginType origin_type, const Location &loc) const {}

// --- the ground-station link
alignas(GCS) static unsigned char gcs_storage[sizeof(GCS)];

GCS &gcs()
{
    return *reinterpret_cast<GCS *>(gcs_storage);
}

static const unsigned TEXT_QUEUE = 8;
static char text_queue[TEXT_QUEUE][51];
static uint8_t text_severity[TEXT_QUEUE];
static unsigned text_head, text_count;

void GCS::send_text(MAV_SEVERITY severity, const char *fmt, ...)
{
    if (text_count == TEXT_QUEUE) {
        return;   // more than 8 texts waiting: dropped, as a full GCS queue drops them
    }
    const unsigned k = (text_head + text_count) % TEXT_QUEUE;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(text_queue[k], sizeof text_queue[k], fmt, ap);
    va_end(ap);
    text_severity[k] = uint8_t(severity);
    text_count++;
}

// the oldest queued text (at most 50 characters, NUL-terminated in buf[51]) and its severity
bool harness_est_text_pop(char *buf, uint8_t &severity)
{
    if (text_count == 0) {
        return false;
    }
    memcpy(buf, text_queue[text_head], 51);
    severity = text_severity[text_head];
    text_head = (text_head + 1) % TEXT_QUEUE;
    text_count--;
    return true;
}
void GCS::send_message(enum ap_message id) {}
