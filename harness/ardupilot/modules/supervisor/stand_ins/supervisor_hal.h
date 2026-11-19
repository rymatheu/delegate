// supervisor_hal.h: the HAL stand-in's state the adapter reads and writes (stubs_hal.cpp).
#pragma once

#include <stdint.h>
#include <stddef.h>

// the clock: AP_HAL::micros() = harness_now_us, AP_HAL::millis() = harness_now_ms, frozen during
// a step as SITL's simulated clock is; micros64 widens micros with a wrap count
extern uint32_t harness_now_us;
extern uint32_t harness_now_ms;
void harness_set_clock(uint32_t now_us, uint32_t now_ms);

// SERIAL0, the ground-station port: bytes in from the record, bytes out to the record
#define HARNESS_UART_RING 4096
size_t harness_gcs_push_rx(const uint8_t *buf, size_t n);   // returns bytes accepted
size_t harness_gcs_pull_tx(uint8_t *buf, size_t max);      // returns bytes taken
size_t harness_gcs_tx_pending();

// RC input: up to 16 channels; fresh = a new frame this tick
void harness_rcin_set(const uint16_t *pwm, uint8_t nchan, bool fresh);
// RC output (SRV_Channels -> hal.rcout): last PWM written per channel
uint16_t harness_rcout_read(uint8_t chan);

// the registered timer and io callbacks (AP_Param's save handler, StorageManager), run once at
// the end of each step
void harness_run_io();
// called by AP_Param::load_all through hal.util->set_cmdline_parameters (as SITL's --param)
extern void (*harness_cmdline_params)();

// reset everything at init (storage zeroed: every parameter at its default)
void harness_hal_reset();
