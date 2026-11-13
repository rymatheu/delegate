/* cpp2lean Phase 3: the HAL scheduler of the estimator translation (PORT-PLAN.md, "Phase 3:" decision on
   delays; README.md "Phase 3: World pointers, sensor front ends, HAL delays").

   The lock-step scheduler of reference/hal/lockstep.cpp (SITL's semantics: the clock moves only when the
   vehicle waits; a wait consumes input lines until the requested time has passed; per consumed line the
   clock is set and the timer processes run in registration order), as a class of ArduPilot's
   AP_HAL::Scheduler interface whose input records are data of the object (the input lines, parsed
   beforehand by the harness and fed into a ring of MAX_RECORDS), so that the translation runs `delay`
   as code of the World instead of a boundary call. Both sides of a difftest compile this file; it is
   not part of the reference vehicle (copter_ref keeps lockstep.cpp, which reads stdin).

   Differences from lockstep.cpp's Scheduler, none observable by the estimator: no delay callbacks
   (Copter's scheduler_delay_callback runs GCS and notify code, outside the estimator's World), no IO
   processes and no timer failsafe (AP_Param's saving and Copter's failsafe_check, idem), no output line;
   at the end of the records a wait returns instead of ending the process (`exhausted()`). The record type
   and the accessors through which the sensor stand-ins read the current record (est_input.h) are shared
   with lockstep.cpp; est_scheduler.cpp defines the accessors on this object, as lockstep.cpp does on its
   globals (the GPS latch of lockstep.cpp's step is here too). The names are global (the translator does
   not translate class definitions inside a namespace). */
#pragma once

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>

#include "est_input.h"

static const uint16_t EST_MAX_RECORDS = 1024;   // boot init consumes 915 lines inside delays (REFERENCE.md)
static const uint8_t EST_MAX_PROCS = 8;         // SITL_SCHEDULER_MAX_TIMER_PROCS

class EstScheduler : public AP_HAL::Scheduler {
public:
    void init() override {}

    // the harness: append one parsed input line (false if the ring is full)
    bool feed(const EstRecord &r);
    // the World difftest's harness (difftest.py drives member functions with scalar arguments): append a
    // line dt_us + 1 after the last line fed (or the clock), with n0 (at most 3) samples of IMU 0, the
    // barometer, compass and GPS values if their flags are set
    bool feed_line(uint16_t dt_us, uint8_t n0, float ax0, float ay0, float az0, float gx0, float gy0, float gz0,
                   float ax1, float ay1, float az1, float gx1, float gy1, float gz1,
                   float ax2, float ay2, float az2, float gx2, float gy2, float gz2,
                   bool baro, float pa, float degc, bool mag, float mx, float my, float mz,
                   bool gps, double lat, double lon, double alt, double vn, double ve, double vd);
    // ... and n lines 2500 us apart, a barometer sample on every k-th (k > 0) with pressure pa + i * dpa,
    // no other sample (the barometer's calibration consumes about 640 lines)
    uint16_t feed_baro_lines(uint16_t n, uint8_t k, float pa, float dpa, float degc);
    // ... and n lines 2500 us apart with 3 samples of each IMU (the same accel and gyro values), a barometer sample on
    // every k-th (k > 0), no other sample (AP_InertialSensor's gyro calibration consumes about 220 such lines)
    uint16_t feed_imu_lines(uint16_t n, uint8_t k, float ax, float ay, float az, float gx, float gy, float gz, float pa, float degc);

    // HALSITL::Scheduler::delay_microseconds with SITL_State::wait_clock: step until the time has passed
    void delay_microseconds(uint16_t usec) override;
    // HALSITL::Scheduler::delay, without delay callbacks
    void delay(uint16_t ms) override;

    void register_timer_process(AP_HAL::MemberProc proc) override;
    void register_io_process(AP_HAL::MemberProc proc) override {}
    void register_timer_failsafe(AP_HAL::Proc fs, uint32_t period_us) override {}
    void set_system_initialized() override { _initialized = true; }
    bool is_system_initialized() override { return _initialized; }
    void reboot(bool hold_in_bootloader) override {}
    bool in_main_thread() const override { return true; }

    uint64_t clock_us() const { return _clock_us; }
    uint64_t step_period_us() const { return _step_period; }
    const EstRecord &current() const { return _in; }
    bool exhausted() const { return _exhausted; }
    // the GPS latch (est_input.h)
    bool gps_pending() const { return _gps_pending; }
    EstRecord gps_take() { _gps_pending = false; return _gps; }
    // the stand-ins' events since the last consumed line (est_input.h: EST_EV_*)
    void note_event(uint8_t ev) { _events |= ev; }
    uint8_t events() const { return _events; }
    // the IMU stand-in's sample rate (copter_ref --imu-rate)
    uint16_t imu_rate_hz() const { return _imu_rate_hz; }
    void set_imu_rate_hz(uint16_t hz) { _imu_rate_hz = hz; }

private:
    // consume one line: set the clock, run the timer processes (HALSITL::Scheduler::timer_event)
    void step();

    EstRecord _recs[EST_MAX_RECORDS];
    uint16_t _head;
    uint16_t _count;
    EstRecord _in;
    uint64_t _clock_us = 1;         // SITL starts its stopped clock at 1 us
    uint64_t _step_period = 2500;
    uint32_t _lines;
    bool _exhausted;
    bool _initialized;
    AP_HAL::MemberProc _timer_proc[EST_MAX_PROCS];
    uint8_t _num_timer;
    bool _in_timer_proc;
    EstRecord _gps;
    bool _gps_pending;
    uint16_t _imu_rate_hz = 1200;
    uint64_t _fed_t_us;             // the time of the last line fed (0: none yet)
    uint8_t _events;                // the stand-ins' events since the last consumed line
#ifdef EST_MARKS
    EstRecord _synth;               // (Phase 5c) the last line's samples (the last barometer and compass samples kept)
#endif
};

extern EstScheduler est_scheduler;

#ifdef EST_MARKS
// (Phase 5c) the lock-step points of the World's waits, as events of the translation (cpp2lean.py --output-fn est_mark,
// ardupilot/translate_estimator.sh only): the harness of the whole vehicle runs the vehicle's part of lockstep.cpp's step
// and of Scheduler::delay at them (README.md "Phase 5c summary"). kind 0: the line `line` consumed (its record popped);
// 1: the timer processes of that line have run; 2: `delay` would run the delay callback if `_min_delay_cb_ms <= line`
// (here `line` is the remaining time, ms - (now - start), as lockstep.cpp's delay computes it); 3: the records ran out
// (the harness discards the call and feeds the next line). C++ builds: a function without effect.
void est_mark(uint8_t kind, uint32_t line);
#endif
