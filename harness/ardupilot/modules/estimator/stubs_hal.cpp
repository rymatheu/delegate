// stubs_hal.cpp: the hardware abstraction layer the estimation chain reaches for, and what stands in.
//
// Every symbol here belongs to the HAL (libraries/AP_HAL and the SITL board's AP_HAL_SITL), which
// is outside the module: the clock, the scheduler's delays and timer thread, the Util object, the
// console, the semaphores, the panic.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP_HAL::micros, millis, micros64,        the clock (HAL). The input port t_us, extended to 64
//   millis64                                 bits across a wrap of the 32-bit count.
//   AP_HAL::panic                            HAL. Prints and aborts (the harness sees the process
//                                            end; no estimator path reaches it in a sane run).
//   hal (AP_HAL::HAL)                        the HAL object: scheduler, util and console are the
//                                            stand-ins below; every other driver pointer is null
//                                            (SPI, I2C, storage, GPIO, RC, UARTs: the estimator's
//                                            front ends reach the sensors only through the driver
//                                            stand-ins of backend_*.cpp).
//   Scheduler::delay, delay_microseconds,    In the boot thread (adapter.cpp: init_ardupilot's
//   delay_microseconds_boost                 sensor part blocks in delays while it calibrates), a
//                                            delay waits until the steps have brought the clock to
//                                            its end, as SITL's delay waits for the simulator. In
//                                            the 400 Hz loop a delay returns at once: the tick
//                                            happens at t_us (wait_for_sample's wait, SITL's
//                                            SIM_LOOP_DELAY and SIM_TIME_JITTER, both 0).
//   Scheduler::register_timer_process        the HAL's 1 kHz timer thread. The stand-in keeps the
//                                            drivers' timers and runs each once per step, before
//                                            the front ends (harness_run_timer_processes).
//   Scheduler::register_io_process,          the HAL's other threads and the failsafe timer; the
//   register_timer_failsafe                  estimator registers none. Recorded nowhere.
//   Scheduler::in_main_thread                true outside the boot thread.
//   Util::set_soft_armed, get_soft_armed     the arming state the HAL holds (AP_Arming writes it,
//                                            AP_DAL reads it for EKF3). The input port armed,
//                                            through set_soft_armed as AP_HAL/Util.cpp has it
//                                            (without the watchdog's persistent copy).
//   the base classes' code: Scheduler::       as AP_HAL/Scheduler.cpp, Util.cpp, Device.cpp and
//   register_delay_callback, call_delay_cb,  Semaphores.cpp (call_delay_cb: no vehicle callback,
//   ExpectDelay, Util::snprintf, vsnprintf,  the GCS and logging it would run are outside;
//   Device::make_bus_id, change_bus_id,      WithSemaphore without the watchdog's line record)
//   WithSemaphore
//   HALSITL::BinarySemaphore::signal         the fast-rate gyro thread (FSTRATE_ENABLE 0). Abort.
//   UARTDriver::begin                        opens a port (AP_GPS's detection opens the GPS port):
//                                            the sink's _begin.
//   AP_BoardConfig::config_error,            fatal configuration errors: in the boot thread, as
//   allocation_error                         ArduPilot, delay forever (the boot never ends; output
//                                            est_config_error); from the loop, abort.
//   Util::available_memory                   SITL's value, 512 KiB (AP_HAL_SITL/Util.h); EKF3
//                                            checks it before allocating its cores.
//   Util::was_watchdog_reset                 false, as SITL without SITL_WATCHDOG_RESET.
//   Util::get_hw_rtc, set_hw_rtc             the real-time clock: not read by the estimator. 0.
//   the GPS port (UARTDriver)                SITL's SERIAL3: AP_GPS detects a driver only on a port
//                                            (AP_GPS::_detect_instance). A sink; the SITL GPS
//                                            driver's data comes from backend_gps.cpp.
//   console (UARTDriver), DEV_PRINTF         the console. Discards its output (the out-of-line
//                                            members of BetterStream and UARTDriver as a sink).
//   HALSITL::Semaphore                       the SITL board's mutex (HAL_Semaphore). The boot thread
//                                            and the steps never run at the same time (each waits
//                                            for the other), so take and give succeed at once.
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include <AP_HAL_SITL/Semaphores.h>

#include "harness_cut.h"

HarnessTick harness_tick;

static bool config_error_raised;   // see the board configuration errors below

// --- the clock
static uint64_t clock_us;      // t_us extended to 64 bits
static uint32_t clock_last_t_us;

void harness_set_time(uint32_t t_us)
{
    const uint32_t hi = uint32_t(clock_us >> 32) + (t_us < clock_last_t_us ? 1 : 0);
    clock_us = (uint64_t(hi) << 32) | t_us;
    clock_last_t_us = t_us;
}

uint32_t AP_HAL::micros() { return uint32_t(clock_us); }
uint32_t AP_HAL::millis() { return uint32_t(clock_us / 1000U); }
uint64_t AP_HAL::micros64() { return clock_us; }
uint64_t AP_HAL::millis64() { return clock_us / 1000U; }

void AP_HAL::panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "estimator: AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    abort();
}

// --- the boot thread
static pthread_mutex_t boot_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t boot_cv = PTHREAD_COND_INITIALIZER;
static int boot_turn;              // 1 while the boot thread runs, 0 while a step runs
static uint32_t boot_generation;   // incremented when a boot is abandoned
static bool boot_finished;
static bool boot_exists;
static void (*boot_fn)();
static __thread bool tls_is_boot;
static __thread uint32_t tls_generation;

static bool in_boot_thread() { return tls_is_boot; }

// wait for this thread's turn; a boot thread whose boot was abandoned ends here
static void boot_wait_turn_locked()
{
    while (boot_turn != 1 || boot_generation != tls_generation) {
        if (boot_generation != tls_generation) {
            pthread_mutex_unlock(&boot_mtx);
            pthread_exit(nullptr);
        }
        pthread_cond_wait(&boot_cv, &boot_mtx);
    }
}

static void *boot_main(void *arg)
{
    tls_is_boot = true;
    tls_generation = uint32_t(uintptr_t(arg));
    pthread_mutex_lock(&boot_mtx);
    boot_wait_turn_locked();
    pthread_mutex_unlock(&boot_mtx);
    boot_fn();
    pthread_mutex_lock(&boot_mtx);
    if (boot_generation == tls_generation) {
        boot_finished = true;
        boot_turn = 0;
        pthread_cond_broadcast(&boot_cv);
    }
    pthread_mutex_unlock(&boot_mtx);
    return nullptr;
}

// the boot thread hands the turn back to the step and waits for the next one
static void boot_yield()
{
    pthread_mutex_lock(&boot_mtx);
    boot_turn = 0;
    pthread_cond_broadcast(&boot_cv);
    boot_wait_turn_locked();
    pthread_mutex_unlock(&boot_mtx);
}

void harness_boot_start(void (*boot)())
{
    pthread_mutex_lock(&boot_mtx);
    boot_fn = boot;
    boot_finished = false;
    boot_turn = 0;
    boot_exists = true;
    const uint32_t gen = boot_generation;
    pthread_mutex_unlock(&boot_mtx);
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 16u << 20);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    pthread_t tid;
    if (pthread_create(&tid, &attr, boot_main, (void *)uintptr_t(gen)) != 0) {
        AP_HAL::panic("cannot start the boot thread");
    }
    pthread_attr_destroy(&attr);
}

bool harness_boot_resume()
{
    pthread_mutex_lock(&boot_mtx);
    if (!boot_finished) {
        boot_turn = 1;
        pthread_cond_broadcast(&boot_cv);
        while (boot_turn != 0) {
            pthread_cond_wait(&boot_cv, &boot_mtx);
        }
    }
    const bool done = boot_finished;
    pthread_mutex_unlock(&boot_mtx);
    return done;
}

void harness_boot_abandon()
{
    pthread_mutex_lock(&boot_mtx);
    if (boot_exists) {
        boot_generation++;
        boot_turn = 0;
        boot_finished = false;
        boot_exists = false;
        pthread_cond_broadcast(&boot_cv);
    }
    pthread_mutex_unlock(&boot_mtx);
}

// --- the scheduler
static const uint8_t MAX_TIMER_PROCS = 16;
static AP_HAL::MemberProc timer_procs[MAX_TIMER_PROCS];
static uint8_t num_timer_procs;

void harness_run_timer_processes()
{
    for (uint8_t i = 0; i < num_timer_procs; i++) {
        timer_procs[i]();
    }
}

class HarnessScheduler : public AP_HAL::Scheduler {
public:
    void init() override {}
    void delay(uint16_t ms) override { wait_us(uint64_t(ms) * 1000U); }
    void delay_microseconds(uint16_t us) override { wait_us(us); }
    void delay_microseconds_boost(uint16_t us) override { wait_us(us); }
    void register_timer_process(AP_HAL::MemberProc proc) override
    {
        if (num_timer_procs == MAX_TIMER_PROCS) {
            AP_HAL::panic("too many timer processes");
        }
        timer_procs[num_timer_procs++] = proc;
    }
    void register_io_process(AP_HAL::MemberProc proc) override {}
    void register_timer_failsafe(AP_HAL::Proc, uint32_t period_us) override {}
    void set_system_initialized() override {}
    bool is_system_initialized() override { return true; }
    void reboot(bool hold_in_bootloader) override { AP_HAL::panic("reboot"); }
    bool in_main_thread() const override { return !in_boot_thread(); }

private:
    // in the boot thread: wait for the steps that bring the clock past the end of the delay
    static void wait_us(uint64_t us)
    {
        if (!in_boot_thread()) {
            return;
        }
        const uint64_t end = clock_us + us;
        while (clock_us < end) {
            boot_yield();
        }
    }
};

// --- Util
class HarnessUtil : public AP_HAL::Util {
public:
    uint32_t available_memory(void) override { return 512 * 1024; }
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

// --- the HAL object
static HarnessScheduler harness_scheduler;
static HarnessUtil harness_util;
// the console: a UART that discards its output (DEV_PRINTF, hal.console->printf)
class HarnessConsole : public AP_HAL::UARTDriver {
public:
    bool is_initialized() override { return true; }
    bool tx_pending() override { return false; }
    uint32_t txspace() override { return 1024; }
protected:
    void _begin(uint32_t baud, uint16_t rxSpace, uint16_t txSpace) override {}
    size_t _write(const uint8_t *buffer, size_t size) override { return size; }
    ssize_t _read(uint8_t *buffer, uint16_t count) override { return 0; }
    void _end() override {}
    void _flush() override {}
    uint32_t _available() override { return 0; }
    bool _discard_input(void) override { return true; }
};
static HarnessConsole harness_console;
// the GPS's serial port (SERIAL3 in SITL): the SITL GPS driver neither reads nor writes it, but
// AP_GPS detects a driver only on a port; a sink like the console
static HarnessConsole harness_gps_uart;
AP_HAL::UARTDriver *harness_gps_port() { return &harness_gps_uart; }

class HarnessHAL : public AP_HAL::HAL {
public:
    HarnessHAL() :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr,                                    // serial9
                    nullptr, nullptr, nullptr, nullptr, nullptr,   // i2c, spi, wspi, analogin, storage
                    &harness_console, nullptr, nullptr,
                    nullptr, &harness_scheduler, &harness_util, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char *const argv[], Callbacks *callbacks) const override
    {
        AP_HAL::panic("HAL::run");
    }
};

static HarnessHAL harness_hal;
const AP_HAL::HAL &hal = harness_hal;

void AP_HAL::init() {}

void harness_set_vehicle_state_hal(bool armed)
{
    harness_util.set_soft_armed(armed);
}

void harness_reset_hal()
{
    config_error_raised = false;
    clock_us = 0;
    clock_last_t_us = 0;
    num_timer_procs = 0;
    // the arming state of a fresh HAL: disarmed, never changed
    memset(timer_procs, 0, sizeof timer_procs);
    harness_util.~HarnessUtil();
    new (&harness_util) HarnessUtil();
}

// the console's output (DEV_PRINTF), discarded: the out-of-line members of AP_HAL::BetterStream
// and AP_HAL::UARTDriver (AP_HAL/utility/BetterStream.cpp, AP_HAL/UARTDriver.cpp) as a sink
void AP_HAL::BetterStream::printf(const char *fmt, ...) {}
void AP_HAL::BetterStream::vprintf(const char *fmt, va_list ap) {}
size_t AP_HAL::BetterStream::write(const char *str) { return strlen(str); }
int16_t AP_HAL::BetterStream::read(void) { return -1; }
ssize_t AP_HAL::BetterStream::read(uint8_t *buffer, uint16_t count) { return 0; }
size_t AP_HAL::UARTDriver::write(uint8_t c) { return 1; }
size_t AP_HAL::UARTDriver::write(const uint8_t *buffer, size_t size) { return size; }
size_t AP_HAL::UARTDriver::write(const char *str) { return strlen(str); }
int16_t AP_HAL::UARTDriver::read(void) { return -1; }
bool AP_HAL::UARTDriver::read(uint8_t &b) { return false; }
ssize_t AP_HAL::UARTDriver::read(uint8_t *buffer, uint16_t count) { return 0; }
uint32_t AP_HAL::UARTDriver::available() { return 0; }
bool AP_HAL::UARTDriver::discard_input() { return true; }
uint64_t AP_HAL::UARTDriver::receive_time_constraint_us(uint16_t nbytes) { return 0; }

// --- semaphores (HAL_Semaphore is HALSITL::Semaphore on the SITL board)
HALSITL::Semaphore::Semaphore() : _lock(), owner(), take_count(0) {}
bool HALSITL::Semaphore::give() { return true; }
bool HALSITL::Semaphore::take(uint32_t timeout_ms) { return true; }
bool HALSITL::Semaphore::take_nonblocking() { return true; }
void HALSITL::Semaphore::check_owner() const {}

// --- the HAL's base-class code the stand-ins above inherit (AP_HAL/Scheduler.cpp, Util.cpp,
// Device.cpp, Semaphores.cpp), as there
void AP_HAL::Scheduler::register_delay_callback(AP_HAL::Proc proc, uint16_t min_time_ms)
{
    _delay_cb = proc;
    _min_delay_cb_ms = min_time_ms;
}

void AP_HAL::Scheduler::call_delay_cb()
{
    // the vehicle's delay callback (GCS and logging during long delays) is outside: none here
}

ExpectDelay::ExpectDelay(uint32_t ms)
{
    hal.scheduler->expect_delay_ms(ms);
}

ExpectDelay::~ExpectDelay()
{
    hal.scheduler->expect_delay_ms(0);
}

void AP_HAL::Util::set_soft_armed(const bool b)
{
    if (b != soft_armed) {
        soft_armed = b;
        last_armed_change_ms = AP_HAL::millis();
    }
}

int AP_HAL::Util::snprintf(char *str, size_t size, const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    const int r = ::vsnprintf(str, size, format, ap);
    va_end(ap);
    return r;
}

int AP_HAL::Util::vsnprintf(char *str, size_t size, const char *format, va_list ap)
{
    return ::vsnprintf(str, size, format, ap);
}

uint32_t AP_HAL::Device::make_bus_id(enum BusType bus_type, uint8_t bus, uint8_t address, uint8_t devtype)
{
    union DeviceId d {};
    d.devid_s.bus_type = bus_type;
    d.devid_s.bus = bus;
    d.devid_s.address = address;
    d.devid_s.devtype = devtype;
    return d.devid;
}

uint32_t AP_HAL::Device::change_bus_id(uint32_t old_id, uint8_t devtype)
{
    union DeviceId d;
    d.devid = old_id;
    d.devid_s.devtype = devtype;
    return d.devid;
}

WithSemaphore::WithSemaphore(AP_HAL::Semaphore &mtx, uint32_t line) :
    _mtx(mtx)
{
    _mtx.take_blocking();
}

WithSemaphore::~WithSemaphore()
{
    _mtx.give();
}

// --- HAL pieces referenced off the estimator's path
void HALSITL::BinarySemaphore::signal(void)
{
    AP_HAL::panic("BinarySemaphore::signal (the fast-rate gyro thread, FSTRATE_ENABLE 0)");
}

void AP_HAL::UARTDriver::begin(uint32_t baud, uint16_t rxSpace, uint16_t txSpace)
{
    _begin(baud, rxSpace, txSpace);
}

// --- board configuration errors (AP_BoardConfig::config_error, allocation_error): ArduPilot never
// returns from them; throw_error repeats the message every 5 s and delays forever
// (AP_BoardConfig.cpp:550-589). In the boot thread the stand-in does the same: it delays forever,
// so the boot never finishes and every later step reports est_booted false and
// est_config_error true. Reached from the 400 Hz loop it would hang the step: abort.
#include <AP_BoardConfig/AP_BoardConfig.h>

bool harness_config_error()
{
    return config_error_raised;
}

static void error_loop(const char *what, const char *fmt, va_list ap)
{
    fprintf(stderr, "estimator: %s: ", what);
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    config_error_raised = true;
    if (!in_boot_thread()) {
        abort();
    }
    for (;;) {
        hal.scheduler->delay(5);
    }
}

void AP_BoardConfig::config_error(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    error_loop("Config Error", fmt, ap);
    va_end(ap);
}

void AP_BoardConfig::allocation_error(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    error_loop("Allocation Error", fmt, ap);
    va_end(ap);
}
