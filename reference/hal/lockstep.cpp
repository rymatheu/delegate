/* cpp2lean reference vehicle: the lock-step HAL (see lockstep.h and REFERENCE.md).

   Compiled in place of libraries/AP_HAL_SITL. The drivers mirror what HALSITL does for a SITL vehicle
   in lock-step mode, with the simulator and the sockets replaced by the per-step protocol:
     clock       AP_HAL::micros64() is a counter set from the input lines (never wall time)
     Scheduler   delay/delay_microseconds consume input lines until the requested time has passed;
                 timer processes, the timer failsafe and IO processes run once per consumed line
                 (HALSITL::Scheduler::timer_event), IO processes also after every loop() (HAL_SITL::run)
     UART        SERIAL0 (also the console, as in SITL): byte queues, the uplink bytes of each line
                 appended to the receive queue, the transmit queue emptied into each output line;
                 SERIAL1..9 exist but are not connected (no space, no bytes), as unconnected SITL ports
     Storage     a byte array of HAL_STORAGE_SIZE, optionally loaded from and saved to a file (D12)
     RCInput     the 16 PWM values of the line's rc record; new_input() is true once per record (D7)
     RCOutput    SITL's RCOutput logic (cork/push, safety switch); the pushed PWM goes to the output line
     AnalogIn    the battery voltage and current of the line on SITL's pins 13 and 12 (D8)
     Util        SITL's answers, except get_hw_rtc (a fixed epoch plus the clock)
   GPIO, I2C, SPI, WSPI, optical flow and flash are AP_HAL_Empty's drivers (no devices). */

#include <AP_HAL/AP_HAL.h>
#include <AP_HAL/utility/RingBuffer.h>
#include <AP_Math/div1000.h>
#include <AP_HAL_Empty/AP_HAL_Empty.h>
#include <AP_HAL_Empty/AP_HAL_Empty_Private.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include <SITL/SITL.h>
#include <AP_Vehicle/AP_Vehicle.h>
#include <AP_Scheduler/AP_Scheduler.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <pthread.h>
#include <vector>
#include <algorithm>

#include "lockstep.h"

extern const AP_HAL::HAL& hal;

namespace ParamDump {
void run(const char *path);    // param_dump.cpp
void test(const char *script, const char *path);
}

namespace Lockstep {

Input in;
uint8_t num_imus = 1;
uint16_t imu_rate_hz = 1200;

// the start of the simulated UTC time: 2026-01-01T00:00:00Z (SITL uses the host's wall clock)
static const uint64_t START_UTC_S = 1767225600ULL;

static uint64_t clock_us = 1;          // SITL starts its stopped clock at 1 us (SITL_State::init)
static uint64_t step_period = 2500;    // time between the last two input lines (us)
static uint64_t lines_read;
static bool have_line;                 // an input line has been consumed and its output is due
static const char *storage_in_path;
static const char *storage_out_path;
static const char *param_dump_path;    // --param-dump (README.md, "Phase 4: AP_Param")
static const char *param_test_path;    // --param-test (with --param-dump: the output)
static bool timing;
static FILE *timing_file;

// --- timing (wall clock, measurement only: never read by the vehicle) ------------------------------
static uint64_t wall_ns()
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return uint64_t(ts.tv_sec) * 1000000000ULL + uint64_t(ts.tv_nsec);
}
static uint64_t compute_start_ns;
static std::vector<uint32_t> compute_ns;   // per consumed line: vehicle time between steps

// --- profile (--profile FILE; measurement only): a wall-clock sampler that attributes each sample to
// the HAL phase, or, in the vehicle, to the scheduler task running then
// (AP_HAL::Util::persistent_data.scheduler_task, which AP_Scheduler sets around every task)
enum { PHASE_VEHICLE = 0, PHASE_PROTOCOL = 1, PHASE_TIMER = 2, PHASE_IO = 3 };
static volatile sig_atomic_t phase;
static const char *profile_path;
static volatile uint32_t prof_phase[4];
static volatile uint32_t prof_task[256 + 8];

static void finish(int code);

}  // namespace Lockstep

// ------------------------------------------------------------------------------------------------
// clock and system functions (AP_HAL/system.h; HALSITL's are in AP_HAL_SITL/system.cpp)

namespace AP_HAL {

void init() {}

void panic(const char *errormsg, ...)
{
    va_list ap;
    fflush(stdout);
    fprintf(stderr, "PANIC: ");
    va_start(ap, errormsg);
    vfprintf(stderr, errormsg, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    // the Halted outcome of PORT-PLAN.md 4.13: the run ends here
    Lockstep::finish(3);
    for (;;) {}
}

void dump_stack_trace() {}
void dump_core_file() {}

uint64_t micros64() { return Lockstep::clock_us; }
uint64_t millis64() { return uint64_div1000(micros64()); }
uint32_t micros() { return micros64() & 0xFFFFFFFF; }
uint32_t millis() { return millis64() & 0xFFFFFFFF; }

}  // namespace AP_HAL

// ------------------------------------------------------------------------------------------------
// drivers

namespace Lockstep {

#define MAX_PROCS 8   // SITL_SCHEDULER_MAX_TIMER_PROCS

class Scheduler : public AP_HAL::Scheduler {
public:
    void init() override {}

    // HALSITL::Scheduler::delay_microseconds with SITL_State::wait_clock: step until the time has passed
    void delay_microseconds(uint16_t usec) override {
        const uint64_t start = AP_HAL::micros64();
        while (AP_HAL::micros64() - start < usec) {
            step();
        }
    }

    // HALSITL::Scheduler::delay, verbatim in its logic
    void delay(uint16_t ms) override {
        uint32_t start = AP_HAL::millis();
        uint32_t now = start;
        do {
            delay_microseconds(1000);
            if (_min_delay_cb_ms <= (ms - (now - start))) {
                if (in_main_thread()) {
                    delay_callbacks++;   // counted for --est only
                    call_delay_cb();
                }
            }
            now = AP_HAL::millis();
        } while (now - start < ms);
    }

    void register_timer_process(AP_HAL::MemberProc proc) override {
        for (uint8_t i = 0; i < num_timer; i++) {
            if (timer_proc[i] == proc) {
                return;
            }
        }
        if (num_timer < MAX_PROCS) {
            timer_proc[num_timer++] = proc;
        }
    }
    void register_io_process(AP_HAL::MemberProc proc) override {
        for (uint8_t i = 0; i < num_io; i++) {
            if (io_proc[i] == proc) {
                return;
            }
        }
        if (num_io < MAX_PROCS) {
            io_proc[num_io++] = proc;
        }
    }
    void register_timer_failsafe(AP_HAL::Proc fs, uint32_t period_us) override { failsafe = fs; }

    void set_system_initialized() override {
        if (initialized) {
            AP_HAL::panic("PANIC: scheduler system initialized called more than once");
        }
        initialized = true;
    }
    bool is_system_initialized() override { return initialized; }

    uint32_t delay_callbacks;   // delay callbacks run since the last output line (--est only)

    // a reboot ends the run (PORT-PLAN.md 3.2)
    void reboot(bool hold_in_bootloader) override { finish(4); }

    bool in_main_thread() const override { return true; }

    // HALSITL::Scheduler::_run_timer_procs
    void run_timer_procs() {
        if (in_timer_proc) {
            if (failsafe != nullptr) {
                failsafe();
            }
            return;
        }
        in_timer_proc = true;
        for (uint8_t i = 0; i < num_timer; i++) {
            if (timer_proc[i]) {
                timer_proc[i]();
            }
        }
        if (failsafe != nullptr) {
            failsafe();
        }
        in_timer_proc = false;
    }

    // HALSITL::Scheduler::_run_io_procs (the UART, storage and I2C ticks do nothing here)
    void run_io_procs() {
        if (in_io_proc) {
            return;
        }
        in_io_proc = true;
        for (uint8_t i = 0; i < num_io; i++) {
            if (io_proc[i]) {
                io_proc[i]();
            }
        }
        in_io_proc = false;
    }

private:
    AP_HAL::MemberProc timer_proc[MAX_PROCS];
    AP_HAL::MemberProc io_proc[MAX_PROCS];
    uint8_t num_timer, num_io;
    AP_HAL::Proc failsafe;
    bool in_timer_proc, in_io_proc, initialized;
};

static const uint32_t UART_RX_SIZE = 16384;
static const uint32_t UART_TX_SIZE = 16384;

class UART : public AP_HAL::UARTDriver {
public:
    explicit UART(uint8_t port) : portnum(port), connected(port == 0), rx(0), tx(0) {}

    bool is_initialized() override { return initialized; }
    bool tx_pending() override { return false; }
    uint32_t txspace() override { return connected ? tx.space() : 0; }
    uint32_t bw_in_bytes_per_second() const override { return connected ? 1000000 : baud / 10; }
    uint32_t get_baud_rate() const override { return baud; }

    // the receive side of the protocol: append the uplink bytes of a line (dropped when full)
    void deliver(const uint8_t *data, uint32_t n) {
        if (!connected) {
            return;
        }
        const uint32_t w = rx.write(data, n);
        rx_dropped += n - w;
    }
    // the transmit side: everything written since the last call
    void take_tx(std::vector<uint8_t> &out) {
        out.resize(tx.available());
        if (!out.empty()) {
            tx.read(out.data(), out.size());
        }
    }
    uint32_t rx_dropped;

protected:
    void _begin(uint32_t b, uint16_t rxSpace, uint16_t txSpace) override {
        if (b == 0 && rxSpace == 0 && txSpace == 0) {
            return;
        }
        if (b != 0) {
            baud = b;
        }
        if (!initialized && connected) {
            rx.set_size(UART_RX_SIZE);
            tx.set_size(UART_TX_SIZE);
        }
        initialized = true;
    }
    size_t _write(const uint8_t *buffer, size_t size) override {
        if (!connected) {
            return 0;
        }
        return tx.write(buffer, size);
    }
    ssize_t _read(uint8_t *buffer, uint16_t count) override {
        if (!connected) {
            return -1;
        }
        return rx.read(buffer, count);
    }
    void _end() override {}
    void _flush() override {}
    uint32_t _available() override { return connected ? rx.available() : 0; }
    bool _discard_input() override { rx.clear(); return true; }

private:
    uint8_t portnum;
    bool connected;
    bool initialized;
    uint32_t baud = 115200;
    ByteBuffer rx, tx;
};

class Storage : public AP_HAL::Storage {
public:
    void init() override {}
    void read_block(void *dst, uint16_t src, size_t n) override {
        if (size_t(src) + n > sizeof(buf)) {
            return;
        }
        memcpy(dst, &buf[src], n);
    }
    void write_block(uint16_t dst, const void *src, size_t n) override {
        if (size_t(dst) + n > sizeof(buf)) {
            return;
        }
        memcpy(&buf[dst], src, n);
    }
    bool healthy() override { return true; }
    bool load(const char *path) {
        FILE *f = fopen(path, "rb");
        if (f == nullptr) {
            return false;
        }
        const size_t n = fread(buf, 1, sizeof(buf), f);
        fclose(f);
        return n == sizeof(buf);
    }
    bool save(const char *path) const {
        FILE *f = fopen(path, "wb");
        if (f == nullptr) {
            return false;
        }
        const size_t n = fwrite(buf, 1, sizeof(buf), f);
        fclose(f);
        return n == sizeof(buf);
    }
private:
    uint8_t buf[HAL_STORAGE_SIZE];
};

class RCInput : public AP_HAL::RCInput {
public:
    void init() override {}
    bool new_input() override { const bool r = fresh; fresh = false; return r; }
    uint8_t num_channels() override { return have ? RC_CHANNELS : 0; }
    uint16_t read(uint8_t ch) override { return ch < RC_CHANNELS ? pwm[ch] : 0; }
    uint8_t read(uint16_t *periods, uint8_t len) override {
        const uint8_t n = MIN(len, num_channels());
        for (uint8_t i = 0; i < n; i++) {
            periods[i] = pwm[i];
        }
        return n;
    }
    void frame(const uint16_t *v) {
        memcpy(pwm, v, sizeof(pwm));
        fresh = true;
        have = true;
    }
private:
    uint16_t pwm[RC_CHANNELS];
    bool fresh, have;
};

#define NUM_OUT_CHANNELS 32   // SITL_NUM_CHANNELS

class RCOutput : public AP_HAL::RCOutput {
public:
    void init() override {}
    void set_freq(uint32_t chmask, uint16_t freq_hz) override { freq = freq_hz; }
    uint16_t get_freq(uint8_t ch) override { return freq; }
    void enable_ch(uint8_t ch) override { enable_mask |= (1U << ch); }
    void disable_ch(uint8_t ch) override { enable_mask &= ~(1U << ch); }
    // HALSITL::RCOutput::write
    void write(uint8_t ch, uint16_t period_us) override {
        if (safety_state == AP_HAL::Util::SAFETY_DISARMED) {
            const auto *board_config = AP_BoardConfig::get_singleton();
            const uint32_t safety_mask = board_config != nullptr ? board_config->get_safety_mask() : 0;
            if (!(safety_mask & (1U << ch))) {
                period_us = 0;
            }
        }
        if (ch < NUM_OUT_CHANNELS) {
            if (corked) {
                pending[ch] = period_us;
            } else {
                out[ch] = period_us;
            }
        }
    }
    uint16_t read(uint8_t ch) override { return ch < NUM_OUT_CHANNELS ? out[ch] : 0; }
    void read(uint16_t *period_us, uint8_t len) override {
        memcpy(period_us, out, MIN(len, NUM_OUT_CHANNELS) * sizeof(uint16_t));
    }
    void cork() override {
        if (!corked) {
            memcpy(pending, out, sizeof(out));
            corked = true;
        }
    }
    void push() override {
        if (corked) {
            memcpy(out, pending, sizeof(out));
            corked = false;
        }
    }
    bool force_safety_on() override { safety_state = AP_HAL::Util::SAFETY_DISARMED; return true; }
    void force_safety_off() override { safety_state = AP_HAL::Util::SAFETY_ARMED; }

    uint16_t out[NUM_OUT_CHANNELS];
    AP_HAL::Util::safety_state safety_state = AP_HAL::Util::SAFETY_DISARMED;
private:
    uint16_t pending[NUM_OUT_CHANNELS];
    uint16_t freq = 50;
    uint32_t enable_mask;
    bool corked;
};

// HALSITL::ADCSource: pin voltages of SITL_State_common::update_voltage_current
#define ADC_MAX_PIN_VALUE ((1 << 16) - 1)   // SITL_ADC_MAX_PIN_VALUE
#define ADC_FULL_SCALE_VOLTAGE 5.0f
class AnalogSource : public AP_HAL::AnalogSource {
public:
    explicit AnalogSource(int16_t p) : pin(p) {}
    float read_average() override { return read_latest(); }
    float read_latest() override {
        return constrain_float(voltage_latest() * (ADC_MAX_PIN_VALUE / ADC_FULL_SCALE_VOLTAGE), 0, ADC_MAX_PIN_VALUE);
    }
    bool set_pin(uint8_t p) override { pin = p; return p != ANALOG_INPUT_NONE; }
    float voltage_average() override { return voltage_latest(); }
    float voltage_latest() override {
        const float volt_pin = in.batt_v / 10.1f;
        const float curr_pin = in.batt_a / 17.0f;
        switch (pin) {
        case ANALOG_INPUT_BOARD_VCC:
            return ADC_MAX_PIN_VALUE;
        case 12:
            return curr_pin;
        case 13:
            return volt_pin;
        case 14:
            return curr_pin * 0.25f;
        case 15:
            return volt_pin * 0.25f;
        default:
            return 0.0f;
        }
    }
    float voltage_average_ratiometric() override { return voltage_latest(); }
private:
    int16_t pin;
};

class AnalogIn : public AP_HAL::AnalogIn {
public:
    void init() override {}
    AP_HAL::AnalogSource *channel(int16_t pin) override { return NEW_NOTHROW AnalogSource(pin); }
    float board_voltage(void) override { return 5.0f; }
};

class Util : public AP_HAL::Util {
public:
    uint32_t available_memory(void) override { return 512 * 1024; }
    uint64_t get_hw_rtc() const override { return START_UTC_S * 1000000ULL + AP_HAL::micros64(); }
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    bool get_system_id(char buf[50]) override {
        strncpy(buf, "cpp2lean-lockstep", 50);
        return true;
    }
    bool get_system_id_unformatted(uint8_t buf[], uint8_t &len) override {
        const char *id = "cpp2lean-lockstep";
        len = MIN(len, uint8_t(strlen(id)));
        memcpy(buf, id, len);
        return true;
    }
    enum safety_state safety_switch_state(void) override;
    bool was_watchdog_reset() const override { return false; }
};

static Scheduler d_scheduler;
static UART d_serial0(0), d_serial1(1), d_serial2(2), d_serial3(3), d_serial4(4), d_serial5(5), d_serial6(6),
    d_serial7(7), d_serial8(8), d_serial9(9);
static Storage d_storage;
static RCInput d_rcin;
static RCOutput d_rcout;
static AnalogIn d_analogin;
static Util d_util;
static Empty::GPIO d_gpio;
static Empty::I2CDeviceManager d_i2c_mgr;
static Empty::SPIDeviceManager d_spi_mgr;
static Empty::WSPIDeviceManager d_wspi_mgr;
static Empty::OpticalFlow d_opticalflow;
static Empty::Flash d_flash;
#if HAL_WITH_DSP
static Empty::DSP d_dsp;
#endif

AP_HAL::Util::safety_state Util::safety_switch_state(void) { return d_rcout.safety_state; }

// ------------------------------------------------------------------------------------------------
// the protocol (REFERENCE.md, "Protocol")

// the protocol's output stream: the process's original standard output; file descriptor 1 is pointed at
// standard error in run(), so that a printf anywhere in the vehicle cannot corrupt the output lines
static FILE *proto_out;

static char *line_buf;
static size_t line_cap;
static std::vector<uint8_t> uplink, downlink;
static std::vector<char> out_buf;

[[noreturn]] static void bad_line(const char *what)
{
    fprintf(stderr, "lockstep: input line %llu: %s\n", (unsigned long long)(lines_read), what);
    finish(2);
    abort();
}

static int hexval(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static uint64_t parse_hex(const char *&p, unsigned ndigits)
{
    uint64_t v = 0;
    for (unsigned i = 0; i < ndigits; i++) {
        const int h = hexval(p[i]);
        if (h < 0) {
            bad_line("bad hex digit");
        }
        v = (v << 4) | uint64_t(h);
    }
    p += ndigits;
    return v;
}

static float parse_f32(const char *&p)
{
    const uint32_t b = uint32_t(parse_hex(p, 8));
    float f;
    memcpy(&f, &b, 4);
    return f;
}

static double parse_f64(const char *&p)
{
    const uint64_t b = parse_hex(p, 16);
    double d;
    memcpy(&d, &b, 8);
    return d;
}

static uint64_t parse_dec(const char *&p)
{
    if (*p < '0' || *p > '9') {
        bad_line("expected a decimal number");
    }
    uint64_t v = 0;
    while (*p >= '0' && *p <= '9') {
        v = v * 10 + uint64_t(*p - '0');
        p++;
    }
    return v;
}

static void expect(const char *&p, char c)
{
    if (*p != c) {
        char msg[64];
        snprintf(msg, sizeof(msg), "expected '%c'", c);
        bad_line(msg);
    }
    p++;
}

static void parse_vec3(const char *&p, Vector3f &v)
{
    v.x = parse_f32(p); expect(p, ',');
    v.y = parse_f32(p); expect(p, ',');
    v.z = parse_f32(p);
}

static void parse_line(const char *p)
{
    Input &x = in;
    x.imu_n[0] = x.imu_n[1] = 0;
    x.baro = x.mag = x.gps = x.rc = false;
    uplink.clear();
    // t=<us> first
    if (strncmp(p, "t=", 2) != 0) {
        bad_line("line must start with t=");
    }
    p += 2;
    x.t_us = parse_dec(p);
    while (*p == ' ') {
        p++;
        const char *key = p;
        const char *eq = strchr(p, '=');
        if (eq == nullptr) {
            bad_line("token without '='");
        }
        const size_t klen = size_t(eq - key);
        p = eq + 1;
        if ((klen == 4 && strncmp(key, "imu0", 4) == 0) || (klen == 4 && strncmp(key, "imu1", 4) == 0)) {
            const uint8_t i = uint8_t(key[3] - '0');
            uint8_t n = 0;
            while (true) {
                if (n >= MAX_IMU_SAMPLES) {
                    bad_line("too many IMU samples");
                }
                parse_vec3(p, x.accel[i * MAX_IMU_SAMPLES + n]); expect(p, ',');
                parse_vec3(p, x.gyro[i * MAX_IMU_SAMPLES + n]);
                n++;
                if (*p != ';') {
                    break;
                }
                p++;
            }
            x.imu_n[i] = n;
        } else if (klen == 4 && strncmp(key, "baro", 4) == 0) {
            x.baro_pa = parse_f32(p); expect(p, ',');
            x.baro_degc = parse_f32(p);
            x.baro = true;
        } else if (klen == 3 && strncmp(key, "mag", 3) == 0) {
            parse_vec3(p, x.mag_mgauss);
            x.mag = true;
        } else if (klen == 3 && strncmp(key, "gps", 3) == 0) {
            x.gps_lat_deg = parse_f64(p); expect(p, ',');
            x.gps_lon_deg = parse_f64(p); expect(p, ',');
            x.gps_alt_m = parse_f64(p); expect(p, ',');
            x.gps_vn = parse_f64(p); expect(p, ',');
            x.gps_ve = parse_f64(p); expect(p, ',');
            x.gps_vd = parse_f64(p);
            x.gps = true;
        } else if (klen == 2 && strncmp(key, "rc", 2) == 0) {
            for (uint8_t i = 0; i < RC_CHANNELS; i++) {
                if (i > 0) {
                    expect(p, ',');
                }
                const uint64_t v = parse_dec(p);
                if (v > 65535) {
                    bad_line("rc value out of range");
                }
                x.rc_pwm[i] = uint16_t(v);
            }
            x.rc = true;
        } else if (klen == 3 && strncmp(key, "bat", 3) == 0) {
            x.batt_v = parse_f32(p); expect(p, ',');
            x.batt_a = parse_f32(p);
        } else if (klen == 2 && strncmp(key, "up", 2) == 0) {
            while (hexval(p[0]) >= 0) {
                const uint8_t b = uint8_t(parse_hex(p, 2));
                uplink.push_back(b);
            }
        } else {
            bad_line("unknown key");
        }
    }
    if (*p != '\0' && *p != '\n' && *p != '\r') {
        bad_line("trailing characters");
    }
}

static void emit_output()
{
    d_serial0.take_tx(downlink);
    out_buf.clear();
    char tmp[64];
    int n = snprintf(tmp, sizeof(tmp), "t=%llu pwm=", (unsigned long long)clock_us);
    out_buf.insert(out_buf.end(), tmp, tmp + n);
    for (uint8_t i = 0; i < 16; i++) {
        n = snprintf(tmp, sizeof(tmp), i ? ",%u" : "%u", unsigned(d_rcout.out[i]));
        out_buf.insert(out_buf.end(), tmp, tmp + n);
    }
    if (!downlink.empty()) {
        static const char hexd[] = "0123456789abcdef";
        out_buf.insert(out_buf.end(), {' ', 'd', 'o', 'w', 'n', '='});
        for (uint8_t b : downlink) {
            out_buf.push_back(hexd[b >> 4]);
            out_buf.push_back(hexd[b & 15]);
        }
    }
    out_buf.push_back('\n');
    fwrite(out_buf.data(), 1, out_buf.size(), proto_out);
    fflush(proto_out);
}

uint64_t step_period_us() { return step_period; }

// the GPS latch (est_input.h): a line's GPS record waits for the next AP_GPS_SITL::read
static bool gps_pending;
static EstRecord gps_record;

static void latch_gps()
{
    if (in.gps) {
        gps_record = in;
        gps_pending = true;
    }
}

void step()
{
    phase = PHASE_PROTOCOL;
    if (have_line) {
        if (timing) {
            compute_ns.push_back(uint32_t(MIN(wall_ns() - compute_start_ns, uint64_t(UINT32_MAX))));
        }
        emit_output();
        if (EstProbe::enabled()) {
            EstProbe::emit(clock_us, d_scheduler.delay_callbacks);
        }
        d_scheduler.delay_callbacks = 0;
    }
    const ssize_t n = getline(&line_buf, &line_cap, stdin);
    if (n <= 0) {
        finish(0);
    }
    lines_read++;
    parse_line(line_buf);
    if (in.t_us <= clock_us) {
        bad_line("time must increase");
    }
    if (lines_read > 1) {
        step_period = in.t_us - clock_us;
    }
    clock_us = in.t_us;
    have_line = true;
    if (!uplink.empty()) {
        d_serial0.deliver(uplink.data(), uint32_t(uplink.size()));
    }
    if (in.rc) {
        d_rcin.frame(in.rc_pwm);
    }
    latch_gps();
    if (EstProbe::enabled()) {
        EstProbe::consumed(!d_scheduler.is_system_initialized(), d_util.persistent_data.scheduler_task);
    }
    if (timing) {
        compute_start_ns = wall_ns();
    }
    // HALSITL::Scheduler::timer_event
    phase = PHASE_TIMER;
    d_scheduler.run_timer_procs();
    phase = PHASE_IO;
    d_scheduler.run_io_procs();
    phase = PHASE_VEHICLE;
}

// the sampler: a second thread (profiling only) that reads the main thread's phase and scheduler task
// every ~20 us of wall time; signals (SIGPROF) are not used because macOS delivers them at system calls
static volatile bool prof_running;
static pthread_t prof_thread;
static uint64_t prof_samples;

static void *prof_main(void *)
{
    const volatile int8_t *task = &d_util.persistent_data.scheduler_task;
    struct timespec ts {0, 20000};
    while (prof_running) {
        const int ph = phase;
        if (ph != PHASE_VEHICLE) {
            prof_phase[ph]++;
        } else {
            prof_task[uint8_t(int(*task) + 8)]++;
        }
        prof_samples++;
        nanosleep(&ts, nullptr);
    }
    return nullptr;
}

static void profile_start()
{
    prof_running = true;
    pthread_create(&prof_thread, nullptr, prof_main, nullptr);
}

// append "name samples" lines: the scheduler's merged task order (AP_Scheduler::run), then the rest
static void profile_report()
{
    prof_running = false;
    pthread_join(prof_thread, nullptr);
    FILE *f = fopen(profile_path, "a");
    if (f == nullptr) {
        return;
    }
    const AP_Scheduler::Task *vt = nullptr, *ct = nullptr;
    uint8_t nv = 0, nc = 0;
    uint32_t log_bit;
    AP_Vehicle *v = AP_Vehicle::get_singleton();
    if (v != nullptr) {
        v->get_scheduler_tasks(vt, nv, log_bit);
        v->get_common_scheduler_tasks(ct, nc);
    }
    uint8_t vo = 0, co = 0;
    for (uint16_t i = 0; i < uint16_t(nv) + nc; i++) {
        bool veh;
        if (vo < nv && co < nc) {
            veh = vt[vo].priority <= ct[co].priority;
        } else {
            veh = vo < nv;
        }
        const AP_Scheduler::Task &task = veh ? vt[vo++] : ct[co++];
        if (i < 120) {
            fprintf(f, "task %s %u\n", task.name, unsigned(prof_task[uint8_t(int(i) + 8)]));
        }
    }
    fprintf(f, "scheduler-between-tasks %u\n", unsigned(prof_task[uint8_t(-1 + 8)]));
    fprintf(f, "scheduler-wait_for_sample %u\n", unsigned(prof_task[uint8_t(-3 + 8)]));
    uint32_t other = 0;
    for (int i = -8; i < -3; i++) other += prof_task[uint8_t(i + 8)];
    other += prof_task[uint8_t(-2 + 8)];
    fprintf(f, "scheduler-other %u\n", unsigned(other));
    fprintf(f, "hal-protocol %u\nhal-timer-procs %u\nhal-io-procs %u\n",
            unsigned(prof_phase[PHASE_PROTOCOL]), unsigned(prof_phase[PHASE_TIMER]), unsigned(prof_phase[PHASE_IO]));
    fprintf(f, "steps %llu\n", (unsigned long long)lines_read);
    fclose(f);
}

static void finish(int code)
{
    if (profile_path != nullptr) {
        profile_report();
    }
    if (proto_out != nullptr) {
        fflush(proto_out);
    }
    EstProbe::close();
    fflush(stdout);
    if (storage_out_path != nullptr && code == 0) {
        if (!d_storage.save(storage_out_path)) {
            fprintf(stderr, "lockstep: cannot write %s\n", storage_out_path);
            code = 1;
        }
    }
    if (d_serial0.rx_dropped) {
        fprintf(stderr, "lockstep: %u uplink bytes dropped (receive queue full)\n", unsigned(d_serial0.rx_dropped));
    }
    if (timing && !compute_ns.empty()) {
        std::vector<uint32_t> v = compute_ns;
        std::sort(v.begin(), v.end());
        double sum = 0;
        for (uint32_t x : v) {
            sum += x;
        }
        FILE *f = timing_file ? timing_file : stderr;
        fprintf(f, "lockstep timing: %zu steps, vehicle compute per step (us): mean %.2f p50 %.2f p90 %.2f p99 %.2f max %.2f, total %.3f s\n",
                v.size(), sum / v.size() / 1e3, v[v.size() / 2] / 1e3, v[v.size() * 9 / 10] / 1e3,
                v[v.size() * 99 / 100] / 1e3, v.back() / 1e3, sum / 1e9);
        if (timing_file) {
            for (uint32_t x : compute_ns) {
                fprintf(timing_file, "%u\n", x);
            }
            fclose(timing_file);
        }
    }
    fflush(stderr);
    _exit(code);
}

// ------------------------------------------------------------------------------------------------
// the HAL

class HAL_Lockstep : public AP_HAL::HAL {
public:
    HAL_Lockstep() : AP_HAL::HAL(
        &d_serial0, &d_serial1, &d_serial2, &d_serial3, &d_serial4, &d_serial5, &d_serial6, &d_serial7, &d_serial8, &d_serial9,
        &d_i2c_mgr, &d_spi_mgr, &d_wspi_mgr, &d_analogin, &d_storage,
        &d_serial0,           // console: SERIAL0, as in SITL
        &d_gpio, &d_rcin, &d_rcout, &d_scheduler, &d_util, &d_opticalflow, &d_flash,
#if AP_SIM_ENABLED
        nullptr,            // AP_HAL::SIMState (simulation on hardware boards only)
#endif
#if HAL_WITH_DSP
        &d_dsp,
#endif
        nullptr) {}

    void run(int argc, char * const argv[], Callbacks *callbacks) const override;
};

static void usage()
{
    fprintf(stderr,
            "usage: copter_ref [--storage FILE] [--storage-out FILE] [--imus N] [--imu-rate HZ] [--timing] [--timing-file FILE] [--profile FILE] [--est FILE] [--param-dump FILE [--param-test SCRIPT]]\n"
            "  reads one input line per lock-step step on stdin, writes one output line per input line on stdout\n");
    _exit(2);
}

void HAL_Lockstep::run(int argc, char * const argv[], Callbacks *callbacks) const
{
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        const bool more = i + 1 < argc;
        if (strcmp(a, "--storage") == 0 && more) {
            storage_in_path = argv[++i];
        } else if (strcmp(a, "--storage-out") == 0 && more) {
            storage_out_path = argv[++i];
        } else if (strcmp(a, "--imus") == 0 && more) {
            num_imus = uint8_t(atoi(argv[++i]));
            if (num_imus < 1 || num_imus > MAX_IMUS) {
                usage();
            }
        } else if (strcmp(a, "--imu-rate") == 0 && more) {
            imu_rate_hz = uint16_t(atoi(argv[++i]));
        } else if (strcmp(a, "--timing") == 0) {
            timing = true;
        } else if (strcmp(a, "--profile") == 0 && more) {
            profile_path = argv[++i];
        } else if (strcmp(a, "--est") == 0 && more) {
            const char *est_path = argv[++i];
            if (!EstProbe::open(est_path)) {
                fprintf(stderr, "lockstep: cannot write %s\n", est_path);
                _exit(2);
            }
        } else if (strcmp(a, "--param-dump") == 0 && more) {
            param_dump_path = argv[++i];
        } else if (strcmp(a, "--param-test") == 0 && more) {
            param_test_path = argv[++i];
        } else if (strcmp(a, "--timing-file") == 0 && more) {
            timing = true;
            timing_file = fopen(argv[++i], "w");
        } else {
            usage();
        }
    }
    if (storage_in_path != nullptr && !d_storage.load(storage_in_path)) {
        fprintf(stderr, "lockstep: cannot read the storage image %s (%u bytes expected)\n",
                storage_in_path, unsigned(HAL_STORAGE_SIZE));
        _exit(2);
    }
    fflush(stdout);
    proto_out = fdopen(dup(1), "w");
    dup2(2, 1);
    SITL::SIM *sim = AP::sitl();
    sim->imu_count.set(num_imus);
    if (profile_path != nullptr) {
        profile_start();
    }

    // HAL_SITL::run
    d_scheduler.init();
    if (param_dump_path != nullptr) {
        // README.md, "Phase 4: AP_Param": AP_Param's boot sequence to load_all, the parameters before and after
        if (param_test_path != nullptr) {
            ParamDump::test(param_test_path, param_dump_path);
        } else {
            ParamDump::run(param_dump_path);
        }
        _exit(0);
    }
    d_serial0.begin(115200);
    d_rcin.init();
    d_rcout.init();
    d_analogin.init();
    callbacks->setup();
    d_scheduler.set_system_initialized();
    while (true) {
        callbacks->loop();
        d_scheduler.run_io_procs();
    }
}

static HAL_Lockstep hal_inst;

}  // namespace Lockstep

// the sensor stand-ins' accessors (est_input.h) on the lock-step HAL
EstRecord est_input() { return Lockstep::in; }
uint64_t est_step_period_us() { return Lockstep::step_period; }
uint16_t est_imu_rate_hz() { return Lockstep::imu_rate_hz; }
bool est_gps_pending() { return Lockstep::gps_pending; }
void est_event(uint8_t ev) { EstProbe::event(ev); }
EstRecord est_gps_take()
{
    Lockstep::gps_pending = false;
    return Lockstep::gps_record;
}

const AP_HAL::HAL& AP_HAL::get_HAL() { return Lockstep::hal_inst; }
AP_HAL::HAL& AP_HAL::get_HAL_mutable() { return Lockstep::hal_inst; }
