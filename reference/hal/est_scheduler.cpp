/* cpp2lean Phase 3: the HAL scheduler of the estimator translation (est_scheduler.h). */
#include "est_scheduler.h"

EstScheduler est_scheduler;

#ifdef EST_MARKS
void est_mark(uint8_t kind, uint32_t line) {}
#endif

bool EstScheduler::feed(const EstRecord &r)
{
    if (_count >= EST_MAX_RECORDS) {
        return false;
    }
    _recs[(_head + _count) % EST_MAX_RECORDS] = r;
    _count++;
    _fed_t_us = r.t_us;
    _exhausted = false;
    return true;
}

bool EstScheduler::feed_line(uint16_t dt_us, uint8_t n0, float ax0, float ay0, float az0, float gx0, float gy0, float gz0,
                             float ax1, float ay1, float az1, float gx1, float gy1, float gz1,
                             float ax2, float ay2, float az2, float gx2, float gy2, float gz2,
                             bool baro, float pa, float degc, bool mag, float mx, float my, float mz,
                             bool gps, double lat, double lon, double alt, double vn, double ve, double vd)
{
    EstRecord r {};
    const uint64_t last = _fed_t_us > _clock_us ? _fed_t_us : _clock_us;
    r.t_us = last + uint64_t(dt_us) + 1;
    r.imu_n[0] = n0 > 3 ? 3 : n0;
    r.accel[0] = Vector3f(ax0, ay0, az0);
    r.gyro[0] = Vector3f(gx0, gy0, gz0);
    r.accel[1] = Vector3f(ax1, ay1, az1);
    r.gyro[1] = Vector3f(gx1, gy1, gz1);
    r.accel[2] = Vector3f(ax2, ay2, az2);
    r.gyro[2] = Vector3f(gx2, gy2, gz2);
    r.baro = baro;
    r.baro_pa = pa;
    r.baro_degc = degc;
    r.mag = mag;
    r.mag_mgauss = Vector3f(mx, my, mz);
    r.gps = gps;
    r.gps_lat_deg = lat;
    r.gps_lon_deg = lon;
    r.gps_alt_m = alt;
    r.gps_vn = vn;
    r.gps_ve = ve;
    r.gps_vd = vd;
    return feed(r);
}

uint16_t EstScheduler::feed_baro_lines(uint16_t n, uint8_t k, float pa, float dpa, float degc)
{
    uint16_t fed = 0;
    for (uint16_t i = 0; i < n; i++) {
        EstRecord r {};
        const uint64_t last = _fed_t_us > _clock_us ? _fed_t_us : _clock_us;
        r.t_us = last + 2500;
        r.baro = k > 0 && i % k == 0;
        r.baro_pa = pa + float(i) * dpa;
        r.baro_degc = degc;
        if (!feed(r)) {
            break;
        }
        fed++;
    }
    return fed;
}

uint16_t EstScheduler::feed_imu_lines(uint16_t n, uint8_t k, float ax, float ay, float az, float gx, float gy, float gz, float pa, float degc)
{
    uint16_t fed = 0;
    for (uint16_t i = 0; i < n; i++) {
        EstRecord r {};
        const uint64_t last = _fed_t_us > _clock_us ? _fed_t_us : _clock_us;
        r.t_us = last + 2500;
        for (uint8_t m = 0; m < EST_MAX_IMUS; m++) {
            r.imu_n[m] = 3;
            for (uint8_t j = 0; j < 3; j++) {
                r.accel[m * EST_MAX_IMU_SAMPLES + j] = Vector3f(ax, ay, az);
                r.gyro[m * EST_MAX_IMU_SAMPLES + j] = Vector3f(gx, gy, gz);
            }
        }
        r.baro = k > 0 && i % k == 0;
        r.baro_pa = pa;
        r.baro_degc = degc;
        if (!feed(r)) {
            break;
        }
        fed++;
    }
    return fed;
}

void EstScheduler::step()
{
    if (_count == 0) {
        _exhausted = true;
#ifdef EST_MARKS
        // (Phase 5c) the records ran out inside a wait: the harness discards this call (est_mark 3) and repeats it with
        // the next line; until the call returns, synthetic lines (the last samples, one step period apart) keep its
        // waits finite
        est_mark(3, _lines);
        _in = _synth;
        _in.t_us = _clock_us + _step_period;
        _in.gps = false;
        _clock_us = _in.t_us;
        _events = 0;
        if (_in_timer_proc) {
            return;
        }
        _in_timer_proc = true;
        for (uint8_t i = 0; i < _num_timer; i++) {
            if (_timer_proc[i]) {
                _timer_proc[i]();
            }
        }
        _in_timer_proc = false;
#endif
        return;
    }
    _in = _recs[_head];
    if (_lines > 0) {
        _step_period = _in.t_us - _clock_us;
    }
    _head = (_head + 1) % EST_MAX_RECORDS;
    _count--;
    _lines++;
    _events = 0;
    _clock_us = _in.t_us;
#ifdef EST_MARKS
    est_mark(0, _lines);
    _synth.imu_n[0] = _in.imu_n[0];
    _synth.imu_n[1] = _in.imu_n[1];
    for (uint8_t j = 0; j < EST_MAX_IMUS * EST_MAX_IMU_SAMPLES; j++) {
        _synth.accel[j] = _in.accel[j];
        _synth.gyro[j] = _in.gyro[j];
    }
    if (_in.baro) {
        _synth.baro = true;
        _synth.baro_pa = _in.baro_pa;
        _synth.baro_degc = _in.baro_degc;
    }
    if (_in.mag) {
        _synth.mag = true;
        _synth.mag_mgauss = _in.mag_mgauss;
    }
#endif
    // lockstep.cpp's latch_gps: the record waits for the next AP_GPS_SITL::read
    if (_in.gps) {
        _gps = _in;
        _gps_pending = true;
    }
    // HALSITL::Scheduler::_run_timer_procs
    if (_in_timer_proc) {
#ifdef EST_MARKS
        est_mark(1, _lines);
#endif
        return;
    }
    _in_timer_proc = true;
    for (uint8_t i = 0; i < _num_timer; i++) {
        if (_timer_proc[i]) {
            _timer_proc[i]();
        }
    }
    _in_timer_proc = false;
#ifdef EST_MARKS
    est_mark(1, _lines);
#endif
}

void EstScheduler::delay_microseconds(uint16_t usec)
{
    const uint64_t start = _clock_us;
#ifdef EST_MARKS
    // (Phase 5c) out of records, step() goes on with synthetic lines (the harness repeats the call with the next line)
    while (_clock_us - start < usec) {
        step();
    }
#else
    while (_clock_us - start < usec && !_exhausted) {
        step();
    }
#endif
}

void EstScheduler::delay(uint16_t ms)
{
    const uint32_t start = uint32_t(_clock_us / 1000);
    uint32_t now = start;
    do {
        delay_microseconds(1000);
#ifdef EST_MARKS
        est_mark(2, ms - (now - start));
#endif
        now = uint32_t(_clock_us / 1000);
#ifdef EST_MARKS
    } while (now - start < ms);
#else
    } while (now - start < ms && !_exhausted);
#endif
}

void EstScheduler::register_timer_process(AP_HAL::MemberProc proc)
{
    for (uint8_t i = 0; i < _num_timer; i++) {
        if (_timer_proc[i] == proc) {
            return;
        }
    }
    if (_num_timer < EST_MAX_PROCS) {
        _timer_proc[_num_timer++] = proc;
    }
}

namespace AP_HAL {
// the clock of the estimator's World (lockstep.cpp's, read from the scheduler stand-in)
uint64_t micros64() { return est_scheduler.clock_us(); }
uint64_t millis64() { return est_scheduler.clock_us() / 1000; }
uint32_t micros() { return uint32_t(est_scheduler.clock_us() & 0xFFFFFFFF); }
uint32_t millis() { return uint32_t((est_scheduler.clock_us() / 1000) & 0xFFFFFFFF); }
}

// the sensor stand-ins' accessors (est_input.h) on the scheduler's records
EstRecord est_input() { return est_scheduler.current(); }
uint64_t est_step_period_us() { return est_scheduler.step_period_us(); }
uint16_t est_imu_rate_hz() { return est_scheduler.imu_rate_hz(); }
bool est_gps_pending() { return est_scheduler.gps_pending(); }
EstRecord est_gps_take() { return est_scheduler.gps_take(); }

// the stand-ins' events (est_input.h), as the reference's estimation output has them per line: the events
// since the last consumed line (a replay checks where the World ran the front ends)
void est_event(uint8_t ev) { est_scheduler.note_event(ev); }
