// The functions of ardupilot/unity_storage.cpp that the difftest drives.
#pragma once
#include <stdint.h>
uint64_t sm_size(uint8_t type);
uint64_t sm_byte(uint32_t seed, uint8_t type, uint16_t loc, uint8_t v, uint16_t at);
uint64_t sm_u16(uint32_t seed, uint8_t type, uint16_t loc, uint16_t v, uint16_t at);
uint64_t sm_u32(uint32_t seed, uint8_t type, uint16_t loc, uint32_t v, uint16_t at);
float sm_float(uint32_t seed, uint8_t type, uint16_t loc, float v, uint16_t at);
uint64_t sm_block(uint32_t seed, uint8_t type, uint16_t src, uint16_t dst, uint8_t n);
uint64_t sm_copy(uint32_t seed, uint8_t from, uint8_t to);
