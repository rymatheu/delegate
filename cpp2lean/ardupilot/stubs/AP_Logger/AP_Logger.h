// ORACLE STUB: replaces libraries/AP_Logger/AP_Logger.h.
// Why: the real logger pulls in AP_Mission, AP_Rally, the backends and MAVLink. The compiled code
// only calls AP::logger().WriteBlock (AP_MotorsMulticopter.cpp:454, AP_Motors_Class.cpp:303, in
// logging methods the oracle never calls) and AP::logger().Write. The stub drops every record.
// The real AP_Logger/LogStructure.h and AP_Logger_config.h are used unchanged.
#pragma once

#include <AP_Logger/AP_Logger_config.h>
#include <AP_Logger/LogStructure.h>

class AP_Logger {
public:
    void WriteBlock(const void *pBuffer, uint16_t size) {}
    void WriteCriticalBlock(const void *pBuffer, uint16_t size) {}
    void Write(const char *name, const char *labels, const char *fmt, ...) {}
    void Write(const char *name, const char *labels, const char *units, const char *mults, const char *fmt, ...) {}
    bool should_log(uint32_t mask) const { return false; }
};

namespace AP {
    AP_Logger &logger();
};
