// ORACLE STUB: replaces libraries/AP_Notify/AP_Notify.h.
// Why: LEDs, buzzers and MAVLink. AP_Motors::armed() writes AP_Notify::flags.armed
// (AP_Motors_Class.cpp:81); the stub keeps that one flag and nothing reads it.
#pragma once
#include <stdint.h>

class AP_Notify {
public:
    struct notify_flags_and_values_type {
        bool armed;
    };
    static struct notify_flags_and_values_type flags;
};
