// cpp2lean-options: --world
// cpp2lean rejection test (the World, --world): the composition model used outside its limits.
// Each line marked expect-reject must be reported, and nothing else.
#include <cstdint>

class Sink {
public:
    void put(float v) { _v = v; }
    float get() const { return _v; }
    const float &scaled(float k) const { return _v; }
private:
    float _v;
};

// two objects of one class whose reference members refer to different objects
class Tap {
public:
    explicit Tap(Sink &sink) : _sink(sink) {}
    void push(float v) { _sink.put(v); }
    // a local reference to the result of a call with arguments on a World object
    float peek(float k) { const float &r = _sink.scaled(k); _sink.put(k); return r; }    // expect-reject
private:
    Sink &_sink;
};

// a call that reaches the caller's own object through the World
class Loop;
class Back {
public:
    explicit Back(Loop &loop) : _loop(loop) {}
    void poke();
private:
    Loop &_loop;
};
class Loop {
public:
    explicit Loop(Back &back) : _back(back) {}
    void run() { _back.poke(); }    // expect-reject
    void touch() { _n++; }
private:
    Back &_back;
    int32_t _n;
};
void Back::poke() { _loop.touch(); }

// a constructor that calls another World object
class Eager {
public:
    explicit Eager(Sink &sink) : _sink(sink) { _sink.put(1.0f); }    // expect-reject
private:
    Sink &_sink;
};

// a singleton pointer assigned something other than `this`
class Odd {
public:
    Odd() { _singleton = nullptr; }    // expect-reject
    static Odd *_singleton;
private:
    int32_t _x;
};
Odd *Odd::_singleton;

extern Back back_obj;
Sink sink_a;
Sink sink_b;
Tap tap_a(sink_a);
Tap tap_b(sink_b);    // expect-reject
Loop loop_obj(back_obj);
Back back_obj(loop_obj);
Eager eager(sink_a);
Odd odd;
