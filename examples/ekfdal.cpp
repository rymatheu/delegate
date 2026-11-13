// --ekf-types together with --world-pointers and --reachable (README.md, "Phase 3: AP_DAL and NavEKF3"): the
// patterns of AP_DAL and NavEKF3 in small. A data-abstraction layer allocated as a heap singleton on first use
// (`static Dal *_singleton = nullptr`, AP_DAL.cpp:20) with mutable static members (World fields under
// --ekf-types); a front end, a file-scope object whose reference member is bound to the singleton through
// an accessor (`dal{AP::dal()}`, AP_NavEKF3.cpp:783: the constructor allocates it); cores in raw memory
// (placement new) that bind a reference parameter to the singleton and a reference member to a member of
// the front end through their pointer (`public_origin(frontend->common_EKF_origin)`); a static local in a
// member function (NavEKF3::UpdateFilter's `lastUnhealthyTime_us`); loops bounded by `<=` a data member whose
// every write is a constant (`stateIndexLim`); a const reference into the state (`const ftype &q0 =
// stateStruct.quat[0]`); a getter returning an element of a member array by its argument (AP_DAL_GPS's
// `location(i)`); a value of a struct member of class type default-constructed (`Quaternion quat;` of a log
// record); a brace-initialized log record.
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>

class Quat {
public:
    Quat() { q1 = 1; q2 = q3 = q4 = 0; }
    float q1, q2, q3, q4;
};

struct log_REC {
    uint8_t head;
    float value;
    Quat quat;
    uint8_t _end;
};

class Dal {
public:
    static Dal *get_singleton() {
        if (!_singleton) {
            _singleton = new Dal();
        }
        return _singleton;
    }
    void start_frame(uint32_t t) {
        if (t != _last) {
            _last = t;
            _frames++;
            for (uint8_t i = 0; i < 3; i++) {
                _loc[i] = _loc[i] + (float)i + 0.5f;
            }
        }
        force_write = !force_write;
    }
    void log_event(float v) {
        struct log_REC pkt{ 7, v };
        _rec = pkt;
        events++;
    }
    const float &location(uint8_t i) const { return _loc[i]; }
    uint32_t frames() const { return _frames; }
    static bool force_write;
    static uint32_t events;
    log_REC _rec;
private:
    static Dal *_singleton;
    uint32_t _last;
    uint32_t _frames;
    float _loc[3];
};

Dal *Dal::_singleton = nullptr;
bool Dal::force_write;
uint32_t Dal::events;

namespace AP {
Dal &dal() { return *Dal::get_singleton(); }
}

class Front;

class Origin {
public:
    float get() const { return alt + 1.0f; }
    float alt;
};

class Core {
public:
    Core(Front *_frontend, Dal &_dal);
    void update(uint32_t t, float x);
    void set_lim(uint8_t which) {
        if (which == 0) {
            lim = 2;
        } else if (which == 1) {
            lim = 5;
        } else {
            lim = 7;
        }
    }
private:
    Dal &dal;
    Front *frontend;
    Origin &origin;
    uint8_t lim;
    float states[8];
    float sum;
};

class Front {
public:
    Front() : dal{AP::dal()} {}
    bool init(uint8_t n) {
        if (core != nullptr || n == 0 || n > 2) {
            return false;
        }
        core = (Core *)malloc(sizeof(Core) * n);
        num_cores = n;
        for (uint8_t i = 0; i < num_cores; i++) {
            new (&core[i]) Core(this, dal);
            core[i].set_lim(i);
        }
        return true;
    }
    void update(uint32_t t, float x) {
        dal.start_frame(t);
        static uint32_t lastTime;
        if (lastTime == 0 || x > 5.0f) {
            lastTime = t;
        }
        selected = (t - lastTime) > 1000;
        for (uint8_t i = 0; i < num_cores; i++) {
            core[i].update(t, x);
        }
    }
    void move_origin(float d) { origin.alt += d; dal.log_event(d); }
    Origin origin;
    bool selected;
private:
    Dal &dal;
    Core *core;
    uint8_t num_cores;
};

Core::Core(Front *_frontend, Dal &_dal) :
    dal(_dal),
    frontend(_frontend),
    origin(frontend->origin)
{
    sum = 0;
}

void Core::update(uint32_t t, float x)
{
    const float &s0 = states[0];
    for (uint8_t i = 0; i <= lim; i++) {
        states[i] = states[i] * 0.5f + x + s0 + dal.location(i % 3);
    }
    sum = 0;
    for (auto k = 0; k <= lim; k++) {
        for (auto j = 0; j <= k; j++) {
            sum += states[j] * origin.get();
        }
    }
    if (sum > 1.0e6f) {
        set_lim(2);
    }
}

Front front;
