// cpp2lean-options: --boundary-fn clock_ms --drop log_event --param-class Param=float --boundary Sink
// cpp2lean rejection test (phase 3): constructs added for ArduPilot, used outside their limits. Each
// line marked expect-reject must be reported (reject_phase3.expected), and no other line.
#include <cstring>
#include <cstdint>

uint32_t clock_ms(int unit = 0);
int log_event(int code);

class Param {
public:
    float get() const { return _v; }
    void set(float v) { _v = v; }
private:
    float _v;
};

struct Pair { float a = 0; float b = 0; };

class Owner {
public:
    float k = 1.0f;
};

class Child {
public:
    Child(const Owner &owner, const float &gain) : _owner(owner), _gain(gain) {}
    float scaled(float x) const { return x * _gain; }
private:
    const Owner &_owner;  // expect-reject
    const float &_gain;
};

class Clock {
public:
    uint32_t elapsed(uint32_t since) const { return clock_ms() - since; }
    uint32_t stamp(int k) const { return clock_ms() + (uint32_t)k; }
    void clear() { memset(&_pair, 1, sizeof(_pair)); }  // expect-reject
    int logged() { return log_event(3); }  // expect-reject
    float clock_arg() const { return (float)clock_ms(); }
private:
    Pair _pair;
};

class Scaler {
public:
    float scale(float k) const { return k * _kp.get(); }
private:
    Param _kp;
};

class Gains {
public:
    float weight(float k) const { return Scaler().scale(k); }  // expect-reject
    uint32_t in_us() const { return clock_ms(1); }  // expect-reject
};

class Aliased {
public:
    Aliased() : _ref(_base) {}  // expect-reject
    float get() const { return _ref; }
private:
    float _base = 1.0f;
    const float &_ref;
};

// Outputs to a boundary object: non-const `void` calls with value arguments, and const calls whose
// reference parameters are inputs.
class Sink {
public:
    void put(float v) { _v = v; }
    int take(float v) { _v = v; return 1; }
    void swap_out(float &v) { v = _v; }
    void ping() {}
    void get_into(float &v) const { v = _v; }
    float read_into(float &v) const { v = _v; return _v; }
    void nothing() const {}
    float _v;
};

class Emitter {
public:
    Emitter(Sink &sink) : _sink(sink) { _sink.put(0.0f); }  // expect-reject
    void put(float x) { _sink.put(x); }
    int take(float x) { return _sink.take(x); }  // expect-reject
    void swap(float x) { _sink.swap_out(x); }  // expect-reject
    void ping() { _sink.ping(); }  // expect-reject
    float element() { float arr[2] = {0, 0}; _sink.get_into(arr[1]); return arr[1]; }
    float both() { float v; float w = _sink.read_into(v); return v + w; }
    void idle() { _sink.nothing(); }  // expect-reject
private:
    Sink &_sink;
};
