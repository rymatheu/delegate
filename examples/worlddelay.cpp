// The HAL boundary of the estimator with delays (cpp2lean --world --world-pointers; README.md "Phase 3:
// World pointers, sensor front ends, HAL delays"; PORT-PLAN "Phase 3:" decision on delays): a lock-step
// scheduler stand-in whose `delay` consumes input records held in the World and, per record, sets the
// clock and runs the registered timer processes in registration order (the logic of
// reference/hal/lockstep.cpp's Scheduler, which is SITL's); timer processes are functors bound to back
// ends (`FUNCTOR_BIND_MEMBER`, AP_HAL::MemberProc); a front end that calibrates through delays
// (AP_Baro::calibrate, AP_Baro.cpp:339-363) while its back end, run by the delay, calls back into it;
// the clock read through free functions of a namespace (AP_HAL::micros64, AP_HAL::millis).
#include <cstdint>
#include <new>
#include <type_traits>

#define NEW_NOTHROW new (std::nothrow)

// AP_HAL/utility/functor.h (ArduPilot 802db19de1), the parts used
template <class RetType, class... Args>
class Functor
{
public:
    constexpr Functor(void *obj, RetType (*method)(void *obj, Args...)) : _obj(obj), _method(method) {}
    constexpr Functor(decltype(nullptr)) : Functor(nullptr, nullptr) {}
    constexpr Functor() : Functor(nullptr, nullptr) {}
    RetType operator()(Args... args) const { return _method(_obj, args...); }
    inline bool operator==(const Functor<RetType, Args...>& rhs) { return _obj == rhs._obj && _method == rhs._method; }
    explicit operator bool() const { return _method != nullptr; }
    template<class T, RetType (T::*method)(Args...)>
    static constexpr Functor bind(T *obj) { return { obj, method_wrapper<T, method> }; }
private:
    void *_obj;
    RetType (*_method)(void *obj, Args...);
    template<class T, RetType (T::*method)(Args...)>
    static RetType method_wrapper(void *obj, Args... args) { T *t = static_cast<T*>(obj); return (t->*method)(args...); }
};

#define FUNCTOR_BIND_MEMBER(func, rettype, ...) \
    Functor<rettype, ## __VA_ARGS__>::bind<std::remove_reference<decltype(*this)>::type, func>(this)

typedef Functor<void> MemberProc;

// one input record (a protocol line): its time and the sample it carries
struct Record {
    uint64_t t_us;
    bool baro;
    float pressure;
};

// the lock-step scheduler: the clock moves only when the vehicle waits, by consuming records
class Scheduler {
public:
    // the harness appends a record dt_us + 1 after the last one (the line arrives); 48 records at most wait
    void feed(uint16_t dt_us, bool baro, float pressure) {
        if (_count < 48) {
            const uint16_t k = (_head + _count) % 48;
            _last_t += uint64_t(dt_us) + 1;
            _recs[k].t_us = _last_t;
            _recs[k].baro = baro;
            _recs[k].pressure = pressure;
            _count++;
            _exhausted = false;
        }
    }
    uint64_t micros64() const { return _clock_us; }
    // HALSITL::Scheduler::delay_microseconds with SITL_State::wait_clock: step until the time has passed
    void delay_microseconds(uint16_t usec) {
        const uint64_t start = _clock_us;
        while (_clock_us - start < usec && !_exhausted) {
            step();
        }
    }
    // HALSITL::Scheduler::delay (without delay callbacks)
    void delay(uint16_t ms) {
        const uint32_t start = uint32_t(_clock_us / 1000);
        uint32_t now = start;
        do {
            delay_microseconds(1000);
            now = uint32_t(_clock_us / 1000);
        } while (now - start < ms && !_exhausted);
    }
    void register_timer_process(MemberProc proc) {
        for (uint8_t i = 0; i < _num_timer; i++) {
            if (_timer_proc[i] == proc) {
                return;
            }
        }
        if (_num_timer < 4) {
            _timer_proc[_num_timer++] = proc;
        }
    }
    bool has_sample() const { return _in.baro; }
    float sample() const { return _in.pressure; }
    uint16_t pending() const { return _count; }
    bool exhausted() const { return _exhausted; }
private:
    // consume one record: set the clock, run the timer processes (HALSITL::Scheduler::timer_event)
    void step() {
        if (_count == 0) {
            _exhausted = true;
            return;
        }
        _in = _recs[_head];
        _head = (_head + 1) % 48;
        _count--;
        _clock_us = _in.t_us;
        for (uint8_t i = 0; i < _num_timer; i++) {
            if (_timer_proc[i]) {
                _timer_proc[i]();
            }
        }
    }
    Record _recs[48];
    uint16_t _head;
    uint16_t _count;
    uint64_t _last_t;
    Record _in;
    uint64_t _clock_us;
    bool _exhausted;
    MemberProc _timer_proc[4];
    uint8_t _num_timer;
};

Scheduler hal_scheduler;

namespace HAL {
uint64_t micros64() { return hal_scheduler.micros64(); }
uint32_t millis() { return uint32_t(hal_scheduler.micros64() / 1000); }
}

class Baro;

class Backend {
public:
    explicit Backend(Baro &frontend) : _frontend(frontend) {}
    virtual ~Backend() {}
    virtual void update() = 0;
protected:
    Baro &_frontend;
    uint8_t _instance;
};

class Baro {
public:
    void init();
    void calibrate();
    void update() {
        for (uint8_t i = 0; i < _num_drivers; i++) {
            drivers[i]->update();
        }
    }
    uint8_t register_sensor() { return _num_sensors++; }
    void copy(uint8_t instance, float pressure) {
        if (instance < 2) {
            _pressure[instance] = pressure;
            _last_ms[instance] = HAL::millis();
            _count++;
        }
    }
    bool healthy() const { return _num_sensors > 0 && HAL::millis() - _last_ms[0] < 100 && _count > 0; }
    float ground() const { return _ground; }
    bool failed() const { return _failed; }
private:
    Backend *drivers[2];
    uint8_t _num_drivers;
    uint8_t _num_sensors;
    float _pressure[2];
    uint32_t _last_ms[2];
    uint32_t _count;
    float _ground;
    bool _failed;
};

// the back end: latches the sample in its timer process, copies it to the front end in update()
class SimBaro : public Backend {
public:
    explicit SimBaro(Baro &baro) : Backend(baro) {
        _instance = _frontend.register_sensor();
        hal_scheduler.register_timer_process(FUNCTOR_BIND_MEMBER(&SimBaro::_timer, void));
    }
    void update() override {
        if (!_has_sample) {
            return;
        }
        _frontend.copy(_instance, _recent);
        _has_sample = false;
    }
private:
    void _timer() {
        if (!hal_scheduler.has_sample()) {
            return;
        }
        _recent = hal_scheduler.sample();
        _has_sample = true;
        _frontend.update();          // (a back end reaching the front end during the front end's own delay)
    }
    float _recent;
    bool _has_sample;
};

void Baro::init()
{
    if (_num_drivers < 2) {
        drivers[_num_drivers++] = NEW_NOTHROW SimBaro(*this);
    }
}

// AP_Baro::calibrate's shape: wait until healthy in steps of 10 ms, then average 3 samples 20 ms apart
void Baro::calibrate()
{
    _failed = false;
    for (uint8_t i = 0; i < 2; i++) {
        const uint32_t tstart = HAL::millis();
        do {
            update();
            if (HAL::millis() - tstart > 50 || hal_scheduler.exhausted()) {
                _failed = true;
                return;
            }
            hal_scheduler.delay(10);
        } while (!healthy());
    }
    float sum = 0;
    for (uint8_t c = 0; c < 3; c++) {
        update();
        sum += _pressure[0];
        hal_scheduler.delay(20);
    }
    _ground = sum / 3;
}

Baro barometer;
