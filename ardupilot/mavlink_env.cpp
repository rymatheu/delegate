// The C++ environment of the MAVLink difftest (ardupilot/Mavlink.json, README.md "Phase 4: the MAVLink C
// library"): what the library calls outside the translation. comm_send_lock/unlock (GCS_MAVLink.cpp:192-215:
// the channel semaphore, and a txspace check that discards the frame when the UART is full) are left out of
// the model (cpp2lean --drop): one thread, and the tests' byte queue (comm_send_buffer in
// ardupilot/unity_mavlink.cpp) has room for every frame they send.
#include <GCS_MAVLink/GCS_MAVLink.h>

void comm_send_lock(mavlink_channel_t chan, uint16_t size) {}
void comm_send_unlock(mavlink_channel_t chan) {}
