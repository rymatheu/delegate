// The World (--world): file-scope objects of translated classes, reference members between them
// resolved at translation time, a virtual call through a reference to a base class dispatched to
// the object's class, parameters of another object read through a reference, and the two singleton
// patterns of ArduPilot: a static `_singleton` pointer set by the constructor with `get_singleton()`
// and an `AP::` accessor (AP_RTC.cpp:15-25, :329), and a file-static object with an accessor
// (AP_InternalError.cpp:15, :110).
#include <cstdint>

class Clock {
public:
    Clock() {
        if (_singleton != nullptr) {
            return;
        }
        _singleton = this;
    }
    static Clock *get_singleton() { return _singleton; }
    void advance(uint32_t dt_ms) { _now_ms += dt_ms; }
    uint32_t now_ms() const { return _now_ms; }
private:
    static Clock *_singleton;
    uint32_t _now_ms;
};

Clock *Clock::_singleton;

namespace AP {
Clock &clock() { return *Clock::get_singleton(); }
}

class Logbook {
public:
    void note(int32_t code) { _last = code; _count++; }
    int32_t count() const { return _count; }
private:
    int32_t _last;
    int32_t _count;
};

static Logbook book;

namespace AP {
Logbook &logbook() { return book; }
}

class Motors {
public:
    explicit Motors(float gain) : _gain(gain) {}
    void set_roll(float roll) { _roll = roll; }
    void output() { _out = _roll * _gain; _count++; }
    float get_out() const { return _out; }
    int32_t get_count() const { return _count; }
    float _limit = 4.0f;
private:
    float _gain;
    float _roll;
    float _out;
    int32_t _count;
};

class Attitude {
public:
    explicit Attitude(Motors &motors) : _motors(motors) {}
    virtual ~Attitude() {}
    virtual float rate_gain() const { return 1.0f; }
    void run(float target) {
        _err = target - _last;
        _last = target;
        float r = _err * rate_gain();
        if (r > _motors._limit) {
            r = _motors._limit;
        }
        _motors.set_roll(r);
    }
    float last() const { return _last; }
protected:
    Motors &_motors;
    float _err;
    float _last;
};

class AttitudeMulti : public Attitude {
public:
    explicit AttitudeMulti(Motors &motors) : Attitude(motors), _motors_multi(motors) {}
    float rate_gain() const override { return 2.0f; }
    float out() const { return _motors_multi.get_out(); }
private:
    Motors &_motors_multi;
};

class Nav {
public:
    Nav(Attitude &att, const Motors &motors) : _att(att), _motors(motors) {}
    float update(float x) {
        _target += x * 0.5f;
        _att.run(_target);
        if (_att.last() > 10.0f) {
            _target = 0.0f;
        }
        _steps++;
        Clock::get_singleton()->advance(10);
        if (AP::clock().now_ms() % 1000 == 0) {
            AP::logbook().note(_steps);
        }
        return _motors.get_out() + (float)_motors.get_count() + (float)AP::logbook().count();
    }
    float target() const { return _target; }
private:
    Attitude &_att;
    const Motors &_motors;
    float _target;
    int32_t _steps;
};

Clock clock_obj;
Motors motors(0.75f);
AttitudeMulti attitude(motors);
Nav nav(attitude, motors);
