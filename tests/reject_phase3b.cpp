// cpp2lean-options: --boundary Sink,Probe --array-params --site-inputs --output-log --drop Keeper::_hidden
// cpp2lean rejection test (phase 3, AP_Math and AP_Motors constructs): the constructs added for
// AP_Math and AP_Motors, used outside their limits. Each line marked expect-reject must be reported
// (reject_phase3b.expected), and no other line.
#include <cstdint>

class Sink {
public:
    void put(float v);
    int take(float v);
};
class Probe {
public:
    float at(int i) const;
};
namespace AP {
    Probe &probe();
}

struct V2 {
    float x, y;
    void zero() { x = 0; y = 0; }
};
struct Other {
    float a, b;
};

class V3 {
public:
    float x, y, z;
    V2 &xy() { return *(V2 *)this; }
    const Other &bad_view() const { return *(const Other *)this; }  // expect-reject
    float &operator[](uint8_t i) { float *_v = &x; return _v[i]; }
    float pick(uint8_t k) { return (*this)[k]; }  // expect-reject
    float first() { return (*this)[0] + (*this)[2]; }
    void clear_xy(bool a) { (a ? xy() : xy()).zero(); }  // expect-reject
};

float head(const float *p) { return *p; }  // expect-reject

class Host;
class Part {
public:
    Part(Host &h) : host(h) {}
    float scaled(float v) const;
    void poke();
private:
    Host &host;
};

class Host {
public:
    float gain() const { return _g; }
    void bump() { _g += 1.0f; }
    Part part {*this};
    float run(float v) { part.poke(); return part.scaled(v); }
private:
    float _g = 1.0f;
};

float Part::scaled(float v) const { return v * host.gain(); }
void Part::poke() { host.bump(); }  // expect-reject

struct Pair { float a; float b; };

class Keeper {
public:
    float total(const Pair *ps, uint8_t n)
    {
        float t = 0.0f;
        for (uint8_t i = 0; i < n; i++) {  // expect-reject
            t += ps[i].a;
            n--;
        }
        return t;
    }
    float alias(float v)
    {
        const float &r = _level;  // expect-reject
        _level = v;
        return r;
    }
    float hidden() const { return _hidden; }  // expect-reject
    float probe_all() const
    {
        float sum = 0.0f;
        for (int i = 0; i < 4; i++) {
            sum += AP::probe().at(i);  // expect-reject
        }
        return sum;
    }
    float probe_one(int i) const { return AP::probe().at(i); }
    void send(Sink &k, float v) { k.put(v); }
    int keep(Sink &k, float v) { return k.take(v); }  // expect-reject
    float table() const
    {
        static const Pair t[2] { {1.0f, 2.0f}, {3.0f} };
        return t[0].a + t[1].b;
    }
    const char *_label;  // expect-reject
private:
    float _level;
    float _hidden;
};
