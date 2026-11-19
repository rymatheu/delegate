// stubs_hal.cpp: the hardware abstraction layer the vehicle code runs on, in place of AP_HAL_SITL.
//
//   symbol / driver                     what stands in
//   AP_HAL::micros, millis, micros64,   the harness clock (input now_us, now_ms), frozen during a
//   millis16, millis64                  step as SITL's simulated clock is between loop samples
//   AP_HAL::panic                       prints and aborts
//   AP_HAL::get_HAL, hal                HarnessHAL below (built on first use)
//   SERIAL0 (hal.serial(0))             HarnessUART: 4096-byte rings; rx filled from gcs_rx_*,
//                                       tx drained into gcs_tx_* (adapter.cpp)
//   SERIAL1..9                          HarnessUART with no traffic (reads nothing, accepts
//                                       writes and discards them)
//   hal.storage                         16384 bytes of RAM (HAL_STORAGE_SIZE of board/sitl.h),
//                                       zeroed at init: every parameter at its default
//   hal.rcin                            channels from the input record (rc_1..rc_8)
//   hal.rcout                           records the last PWM per channel (SRV_Channels output);
//                                       not an output port yet (the motors' PWM is the mixer's)
//   hal.scheduler                       no threads: the registered timer and io callbacks run
//                                       once at the end of each step (harness_run_io), and from
//                                       delay() (as the io thread would run meanwhile); delays do
//                                       not move the clock (the harness's); more than 10000
//                                       delays in one step abort (a wait that cannot end);
//                                       the main-loop failsafe callback is not run
//   hal.util                            AP_HAL::Util defaults; RTC 0; 256 kB available memory;
//                                       set_cmdline_parameters applies the parameter record as
//                                       parameter defaults, as SITL's --param does
//   hal.analogin                        every channel reads 0 V; board voltage 5 V
//   hal.gpio                            no pins
//   HALSITL::Semaphore                  single-threaded: take always succeeds
//   i2c_mgr, spi, wspi, opticalflow,    absent (nullptr): no driver in the supervisor uses them
//   flash, simstate, CAN
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <AP_HAL/AP_HAL.h>
#include <AP_HAL/utility/RingBuffer.h>
#include <AP_HAL_SITL/Semaphores.h>

#include "supervisor_hal.h"

uint32_t harness_now_us;
uint32_t harness_now_ms;
static uint32_t wraps, last_us;

void harness_set_clock(uint32_t now_us, uint32_t now_ms)
{
    if (now_us < last_us) {
        wraps++;
    }
    last_us = now_us;
    harness_now_us = now_us;
    harness_now_ms = now_ms;
}

uint32_t AP_HAL::micros() { return harness_now_us; }
uint32_t AP_HAL::millis() { return harness_now_ms; }
uint16_t AP_HAL::millis16() { return uint16_t(harness_now_ms); }
uint64_t AP_HAL::micros64() { return (uint64_t(wraps) << 32) | harness_now_us; }
uint64_t AP_HAL::millis64() { return AP_HAL::micros64() / 1000U; }

void AP_HAL::panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "supervisor: panic: ");
    vfprintf(stderr, errormsg, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    abort();
}

// ---- semaphores (single-threaded)
HALSITL::Semaphore::Semaphore() : take_count(0) {}
bool HALSITL::Semaphore::give()
{
    if (take_count > 0) {
        take_count--;
    }
    return true;
}
bool HALSITL::Semaphore::take(uint32_t timeout_ms)
{
    take_count++;
    return true;
}
bool HALSITL::Semaphore::take_nonblocking()
{
    take_count++;
    return true;
}
void HALSITL::Semaphore::check_owner() const {}

// ---- UART
class HarnessUART : public AP_HAL::UARTDriver {
public:
    explicit HarnessUART(bool traffic = false) : traffic(traffic), rx(HARNESS_UART_RING),
                                         tx(HARNESS_UART_RING) {}
    bool is_initialized() override { return true; }
    bool tx_pending() override { return tx.available() > 0; }
    uint32_t txspace() override { return traffic ? tx.space() : HARNESS_UART_RING; }
    size_t push_rx(const uint8_t *b, size_t n) { return rx.write(b, n); }
    size_t pull_tx(uint8_t *b, size_t n) { return tx.read(b, n); }
    size_t pending() const { return tx.available(); }
    void reset() { rx.clear(); tx.clear(); }
protected:
    void _begin(uint32_t baud, uint16_t rxSpace, uint16_t txSpace) override {}
    size_t _write(const uint8_t *buffer, size_t size) override
    {
        return traffic ? tx.write(buffer, size) : size;
    }
    ssize_t _read(uint8_t *buffer, uint16_t count) override
    {
        return ssize_t(rx.read(buffer, count));
    }
    void _end() override {}
    void _flush() override {}
    uint32_t _available() override { return rx.available(); }
    bool _discard_input() override { rx.clear(); return true; }
private:
    bool traffic;
    ByteBuffer rx, tx;
};

// ---- storage
class HarnessStorage : public AP_HAL::Storage {
public:
    void init() override {}
    void read_block(void *dst, uint16_t src, size_t n) override
    {
        if (size_t(src) + n <= sizeof mem) {
            memcpy(dst, &mem[src], n);
        }
    }
    void write_block(uint16_t dst, const void *src, size_t n) override
    {
        if (size_t(dst) + n <= sizeof mem) {
            memcpy(&mem[dst], src, n);
        }
    }
    bool healthy(void) override { return true; }
    void reset() { memset(mem, 0, sizeof mem); }
private:
    uint8_t mem[HAL_STORAGE_SIZE];
};

// ---- RC in and out
class HarnessRCInput : public AP_HAL::RCInput {
public:
    void init() override {}
    bool new_input(void) override { bool f = fresh; fresh = false; return f; }
    uint8_t num_channels() override { return nchan; }
    uint16_t read(uint8_t c) override { return c < nchan ? pwm[c] : 0; }
    uint8_t read(uint16_t *periods, uint8_t len) override
    {
        for (uint8_t k = 0; k < len; k++) {
            periods[k] = read(k);
        }
        return len;
    }
    uint16_t pwm[16];
    uint8_t nchan;
    bool fresh;
};

class HarnessRCOutput : public AP_HAL::RCOutput {
public:
    void init() override {}
    void set_freq(uint32_t chmask, uint16_t freq_hz) override {}
    uint16_t get_freq(uint8_t chan) override { return 50; }
    void enable_ch(uint8_t chan) override {}
    void disable_ch(uint8_t chan) override {}
    void write(uint8_t chan, uint16_t period_us) override
    {
        if (chan < 32) {
            pwm[chan] = period_us;
        }
    }
    void cork() override {}
    void push() override {}
    uint16_t read(uint8_t chan) override { return chan < 32 ? pwm[chan] : 0; }
    void read(uint16_t *period_us, uint8_t len) override
    {
        for (uint8_t k = 0; k < len; k++) {
            period_us[k] = read(k);
        }
    }
    uint16_t pwm[32];
};

// ---- scheduler, util, analog, gpio
class HarnessScheduler : public AP_HAL::Scheduler {
public:
    void init() override {}
    void delay(uint16_t ms) override { waited(); }
    void delay_microseconds(uint16_t us) override { waited(); }
    void register_timer_process(AP_HAL::MemberProc p) override { add(p); }
    void register_io_process(AP_HAL::MemberProc p) override { add(p); }
    void run_procs()
    {
        if (running) {
            return;
        }
        running = true;
        for (uint8_t k = 0; k < nprocs; k++) {
            procs[k]();
        }
        running = false;
    }
    uint32_t delays;
    AP_HAL::MemberProc procs[16];
    uint8_t nprocs;
    bool running;
private:
    void add(AP_HAL::MemberProc p)
    {
        if (nprocs < 16) {
            procs[nprocs++] = p;
        }
    }
    void waited()
    {
        if (++delays > 10000) {
            fprintf(stderr, "supervisor: more than 10000 delays in one step\n");
            abort();
        }
        run_procs();
    }
public:
    void register_timer_failsafe(AP_HAL::Proc, uint32_t period_us) override {}
    void set_system_initialized() override { initialized = true; }
    bool is_system_initialized() override { return initialized; }
    void reboot(bool hold_in_bootloader) override
    {
        fprintf(stderr, "supervisor: reboot requested\n");
        abort();
    }
    bool in_main_thread() const override { return true; }
    bool initialized;
};

void (*harness_cmdline_params)();

class HarnessUtil : public AP_HAL::Util {
public:
    void set_cmdline_parameters() override
    {
        if (harness_cmdline_params != nullptr) {
            harness_cmdline_params();
        }
    }
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
    uint32_t available_memory(void) override { return 256 * 1024; }
};

class HarnessAnalogSource : public AP_HAL::AnalogSource {
public:
    float read_average() override { return 0; }
    float read_latest() override { return 0; }
    bool set_pin(uint8_t p) override { return true; }
    float voltage_average() override { return 0; }
    float voltage_latest() override { return 0; }
    float voltage_average_ratiometric() override { return 0; }
};

class HarnessAnalogIn : public AP_HAL::AnalogIn {
public:
    void init() override {}
    AP_HAL::AnalogSource *channel(int16_t n) override { return &src; }
    float board_voltage(void) override { return 5.0f; }
private:
    HarnessAnalogSource src;
};

class HarnessGPIO : public AP_HAL::GPIO {
public:
    void init() override {}
    void pinMode(uint8_t pin, uint8_t output) override {}
    uint8_t read(uint8_t pin) override { return 0; }
    void write(uint8_t pin, uint8_t value) override {}
    void toggle(uint8_t pin) override {}
    AP_HAL::DigitalSource *channel(uint16_t n) override { return nullptr; }
    bool usb_connected(void) override { return false; }
};

// ---- the HAL object
struct HarnessDrivers {
    HarnessUART serial0{true};
    HarnessUART serialN[9];
    HarnessStorage storage;
    HarnessRCInput rcin;
    HarnessRCOutput rcout;
    HarnessScheduler scheduler;
    HarnessUtil util;
    HarnessAnalogIn analogin;
    HarnessGPIO gpio;
};

static HarnessDrivers &drivers()
{
    static HarnessDrivers d;
    return d;
}

class HarnessHAL : public AP_HAL::HAL {
public:
    explicit HarnessHAL(HarnessDrivers &d) :
        AP_HAL::HAL(&d.serial0, &d.serialN[0], &d.serialN[1], &d.serialN[2], &d.serialN[3],
                    &d.serialN[4], &d.serialN[5], &d.serialN[6], &d.serialN[7], &d.serialN[8],
                    nullptr, nullptr, nullptr, &d.analogin, &d.storage, &d.serial0, &d.gpio,
                    &d.rcin, &d.rcout, &d.scheduler, &d.util, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char * const argv[], Callbacks *callbacks) const override
    {
        fprintf(stderr, "supervisor: HAL::run is not used (the adapter drives setup/loop)\n");
        abort();
    }
};

void AP_HAL::init() {}

const AP_HAL::HAL &AP_HAL::get_HAL()
{
    static HarnessHAL h(drivers());
    return h;
}

size_t harness_gcs_push_rx(const uint8_t *buf, size_t n) { return drivers().serial0.push_rx(buf, n); }
size_t harness_gcs_pull_tx(uint8_t *buf, size_t max) { return drivers().serial0.pull_tx(buf, max); }
size_t harness_gcs_tx_pending() { return drivers().serial0.pending(); }

void harness_rcin_set(const uint16_t *pwm, uint8_t nchan, bool fresh)
{
    HarnessRCInput &r = drivers().rcin;
    r.nchan = nchan > 16 ? 16 : nchan;
    memcpy(r.pwm, pwm, r.nchan * sizeof(uint16_t));
    r.fresh = r.fresh || fresh;
}

uint16_t harness_rcout_read(uint8_t chan) { return drivers().rcout.read(chan); }

void harness_run_io()
{
    drivers().scheduler.run_procs();
    drivers().scheduler.delays = 0;
}

void harness_hal_reset()
{
    HarnessDrivers &d = drivers();
    d.serial0.reset();
    d.storage.reset();
    memset(d.rcin.pwm, 0, sizeof d.rcin.pwm);
    d.rcin.nchan = 0;
    d.rcin.fresh = false;
    memset(d.rcout.pwm, 0, sizeof d.rcout.pwm);
    d.scheduler.initialized = false;
    d.scheduler.delays = 0;
    harness_now_us = harness_now_ms = 0;
    wraps = last_us = 0;
}
