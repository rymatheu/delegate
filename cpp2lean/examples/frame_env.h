// The C++ environment of examples/frame.cpp for its class driver: the boundary functions record
// each call in the output log, as the Lean side's `Output` events; the queries return the driver's
// inputs.
#include "../ardupilot/cpp2lean_events.h"
#include <string>

std::string cpp2lean_events;
bool frame_param_configured;            // input `_gain_configured` (and `lin.expo`'s)
bool frame_param_storage() { return frame_param_configured; }
float frame_sensor_value;               // input `read_at`
uint32_t frame_channel_mask;            // input `channel_mask_2`

void Servo::write(uint8_t chan, uint16_t pwm) { cpp2lean_ev("write"); cpp2lean_ev_u(chan); cpp2lean_ev_u(pwm); }
uint32_t Servo::channel_mask(uint8_t chan) { return frame_channel_mask; }
float Sensor::read_at(int i) const { return frame_sensor_value; }
static Sensor frame_sensor;
Sensor &AP::sensor() { return frame_sensor; }
Notify::Flags Notify::flags;
void Host::emit(uint8_t code) { cpp2lean_ev("emit"); cpp2lean_ev_u(code); }
