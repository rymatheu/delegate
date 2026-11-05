// cpp2lean-options: --boundary Sensor --param-class Param=float
// cpp2lean rejection test (phase 2): class constructs outside the subset, one per declaration. Each
// line marked expect-reject must be reported (reject_classes.expected), and no other line.
#include <cmath>

class Param {
public:
    float get() const { return _v; }
    void set(float v) { _v = v; }
    void set_and_save(float v) { _v = v; }
private:
    float _v;
};

class Sensor {
public:
    float read() const { return 1.0f; }
    float read_at(int i) const { return (float)i; }
    void write(float) {}
};

class PointerMember {
    float *_p;  // expect-reject
};

class Outputs {
public:
    Outputs(Sensor &s) : _s(s) {}
    void push(float v) { _s.write(v); }   // accepted since phase 3: an Outputs field
    float sample(int i) const { return _s.read_at(i); }  // expect-reject
private:
    Sensor &_s;
};

class Counter {
public:
    static int count;  // expect-reject
    int get() const { return 1; }
};

struct A { float a = 0; };
struct B { float b = 0; };
struct AB : A, B {};  // expect-reject

class Flags {
    mutable int _hits = 0;  // expect-reject
    unsigned _bits : 3;  // expect-reject
};

class Vec2 {
public:
    float x = 0, y = 0;
    float operator()(float k) const { return k * x + y; }  // expect-reject
};

class Switchy {
public:
    int fall(int k)
    {
        int r = 0;
        switch (k) {
        case 0:
            r = 1;  // expect-reject
        case 1:
            r += 2;
            break;
        }
        return r;
    }
    int nested_break(int k)
    {
        switch (k) {
        case 0:
            if (k == 0) { break; } else { k++; }  // expect-reject
            return 1;
        default:
            return 2;
        }
        return 0;
    }
};

enum class Level { Low, High };
class Ordered {
public:
    bool above(Level l) const { return l > _level; }  // expect-reject
private:
    Level _level = Level::Low;
};

class WithParams {
public:
    float gain() const { return _k.get(); }
    void save(float v) { _k.set_and_save(v); }  // expect-reject
private:
    Param _k;
};

class UsesLocal {
public:
    float f() { WithParams w; return w.gain(); }  // expect-reject
};

class Delegating {
public:
    Delegating() : Delegating(1.0f) {}  // accepted since phase 3 (delegating constructor)
    Delegating(float v) : _v(v) {}
    float get() const { return _v; }
private:
    float _v;
};

class Recursive {
public:
    int down(int n) { return n > 0 ? down(n - 1) : 0; }  // expect-reject
};

class WithDtor {
public:
    ~WithDtor() { _v = 0; }  // expect-reject
    float get() const { return _v; }
private:
    float _v = 1;
};

class Hiding : public Delegating {
    float _v = 2;  // expect-reject
};

union Bits {  // expect-reject
    float f;
    int i;
};

template <typename T> class Box {  // expect-reject
    T _x;
};

class RefMember {
public:
    RefMember(float &r) : _r(r) {}
    float &_r;  // expect-reject
};
