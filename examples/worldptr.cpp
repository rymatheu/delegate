// The World with pointers (cpp2lean --world --world-pointers; PORT-PLAN F1, F2, F4, F11; README.md
// "Phase 3: World pointers, sensor front ends, HAL delays"), on the patterns of ArduPilot's sensor
// front ends: a front end allocates its back ends at init (`NEW_NOTHROW`, AP_Baro.cpp:600; a static
// `detect` that deletes a back end whose init fails, AP_InertialSensor_SITL.cpp), keeps them in an
// array of base-class pointers (`AP_Baro_Backend *drivers[]`) and calls them virtually; each back end
// holds a reference to its front end and calls back into it while the front end's own `update()` runs
// (`_copy_to_frontend`, the self-reach cycle); a singleton allocated on first call
// (`AP_DAL::get_singleton()`); cores placement-constructed in `malloc`ed memory and called by index
// (AP_NavEKF3.cpp:842-860); semaphores (`WITH_SEMAPHORE`, a semaphore member) that do nothing.
#include <cstdint>
#include <cstddef>
#include <cstdlib>
#include <new>

#define NEW_NOTHROW new (std::nothrow)

// F11: semaphores (named by --semaphores): one thread, every operation succeeds and does nothing
class Semaphore {
public:
    bool take(uint32_t timeout_ms) { return true; }
    bool take_nonblocking() { return true; }
    void take_blocking() {}
    bool give() { return true; }
};

class WithSemaphore {
public:
    WithSemaphore(Semaphore &sem, uint32_t line) : _sem(sem) { _sem.take_blocking(); }
    ~WithSemaphore() { _sem.give(); }
private:
    Semaphore &_sem;
};

#define WITH_SEMAPHORE(sem) WithSemaphore _getsem(sem, __LINE__)

class Baro;

class Backend {
public:
    explicit Backend(Baro &frontend) : _frontend(frontend) {}
    virtual ~Backend() {}
    virtual void update() = 0;
    virtual bool healthy() const { return _count > 0; }
    virtual float scale() const { return 1.0f; }
    void accumulate(float pressure);
    uint8_t instance() const { return _instance; }
protected:
    void copy_to_frontend(float pressure);
    Baro &_frontend;
    uint8_t _instance;
    float _sum;
    uint32_t _count;
    Semaphore _sem;
};

class Baro {
public:
    Baro() {}
    void init(uint8_t nsim, bool with_bad);
    void update();
    void accumulate(float pressure) {
        for (uint8_t i = 0; i < _num_drivers; i++) {
            if (drivers[i] != nullptr) {
                drivers[i]->accumulate(pressure);
            }
        }
    }
    uint8_t register_sensor() { return _num_sensors++; }
    void set_pressure(uint8_t instance, float pressure) {
        if (instance < 3) {
            _pressure[instance] = pressure;
            _updates++;
        }
    }
    float pressure(uint8_t i) const { return i < 3 ? _pressure[i] : 0.0f; }
    uint8_t num_drivers() const { return _num_drivers; }
    bool all_healthy() const {
        for (uint8_t i = 0; i < _num_drivers; i++) {
            if (drivers[i] == nullptr || !drivers[i]->healthy()) {
                return false;
            }
        }
        return true;
    }
    float first_scale() const {
        const Backend *b = drivers[0];
        if (b == nullptr) {
            return -1.0f;
        }
        return b->scale();
    }
    bool same_first(uint8_t i) const { return i < 3 && drivers[i] == drivers[0]; }
private:
    bool _add_backend(Backend *backend) {
        if (!backend) {
            return false;
        }
        if (_num_drivers >= 3) {
            return false;
        }
        drivers[_num_drivers++] = backend;
        return true;
    }
    Backend *drivers[3];
    uint8_t _num_drivers;
    uint8_t _num_sensors;
    float _pressure[3];
    uint32_t _updates;
    Semaphore _rsem;
};

void Backend::accumulate(float pressure)
{
    WITH_SEMAPHORE(_sem);
    _sum += pressure * scale();
    _count++;
}

void Backend::copy_to_frontend(float pressure)
{
    _frontend.set_pressure(_instance, pressure);
}

class SimBaro : public Backend {
public:
    explicit SimBaro(Baro &baro) : Backend(baro) {
        _instance = _frontend.register_sensor();
    }
    void update() override {
        if (_count == 0) {
            return;
        }
        WITH_SEMAPHORE(_sem);
        copy_to_frontend(_sum / (float)_count);
        _sum = 0;
        _count = 0;
    }
};

class ScaledBaro : public Backend {
public:
    ScaledBaro(Baro &baro, float k) : Backend(baro), _k(k) {}
    static Backend *detect(Baro &baro, float k) {
        ScaledBaro *b = NEW_NOTHROW ScaledBaro(baro, k);
        if (b == nullptr) {
            return nullptr;
        }
        if (!b->init_sensor()) {
            delete b;
            return nullptr;
        }
        return b;
    }
    bool init_sensor() {
        if (_k <= 0.0f) {
            return false;
        }
        _instance = _frontend.register_sensor();
        return true;
    }
    void update() override {
        if (_count > 1) {
            copy_to_frontend(_sum / (float)_count);
            _sum = 0;
            _count = 0;
        }
    }
    float scale() const override { return _k; }
    bool healthy() const override { return _count > 1; }
private:
    float _k;
};

void Baro::init(uint8_t nsim, bool with_bad)
{
    for (uint8_t i = 0; i < nsim; i++) {
        _add_backend(NEW_NOTHROW SimBaro(*this));
    }
    _add_backend(ScaledBaro::detect(*this, 0.5f));
    if (with_bad) {
        _add_backend(ScaledBaro::detect(*this, -1.0f));
    }
}

void Baro::update()
{
    WITH_SEMAPHORE(_rsem);
    for (uint8_t i = 0; i < _num_drivers; i++) {
        drivers[i]->update();
    }
}

// a singleton allocated on its first use (AP_DAL::get_singleton, AP_DAL.h)
class Store {
public:
    static Store *get_singleton() {
        if (!_singleton) {
            _singleton = NEW_NOTHROW Store();
        }
        return _singleton;
    }
    void note(float v) { _last = v; _n++; }
    float last() const { return _last; }
private:
    static Store *_singleton;
    float _last;
    uint32_t _n;
};

Store *Store::_singleton;

// cores in `malloc`ed memory, placement-constructed, called by index (AP_NavEKF3.cpp:842-860)
class Filter;

class Core {
public:
    Core(Filter *frontend, uint8_t idx) : frontend(frontend), _idx(idx) {}
    void step(float x);
    float state() const { return _x; }
private:
    Filter *frontend;
    uint8_t _idx;
    float _x;
};

class Filter {
public:
    bool init(uint8_t n) {
        if (core != nullptr || n == 0 || n > 2) {
            return false;
        }
        core = (Core *)malloc(sizeof(Core) * n);
        if (core == nullptr) {
            return false;
        }
        num_cores = n;
        for (uint8_t i = 0; i < num_cores; i++) {
            new (&core[i]) Core(this, i);
        }
        return true;
    }
    void update(float x) {
        for (uint8_t i = 0; i < num_cores; i++) {
            core[i].step(x);
        }
        Store::get_singleton()->note(x);
    }
    float core_state(uint8_t i) const { return i < num_cores ? core[i].state() : 0.0f; }
    float gain = 0.25f;
private:
    Core *core;
    uint8_t num_cores;
};

void Core::step(float x)
{
    _x += frontend->gain * (x - _x) + (float)_idx;
}

Baro barometer;
Filter filter;
