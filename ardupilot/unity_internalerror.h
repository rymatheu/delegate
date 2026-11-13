// The function of ardupilot/unity_internalerror.cpp that the difftest drives.
#pragma once
#include <stdint.h>
uint64_t ie_string(uint8_t buf[64], uint32_t errors, uint32_t count, uint16_t line, uint8_t len);
