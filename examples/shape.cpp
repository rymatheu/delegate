// cpp2lean demo (phase 2): inheritance with a virtual override and an explicit base call, an
// enum with a switch, an array member updated in bounded loops, a reference out-parameter,
// overloaded methods, constructors with initializer lists, default arguments, static members,
// do/while, the comma operator, the NAN/INFINITY/HUGE_VALF constants, a plain struct, an
// unscoped enum nested in a class, local structs and arrays, overloaded free functions and a free
// function with results through reference parameters.
#include <cmath>
#include <cstdint>

// Free functions: an overloaded name; results through reference parameters.
static float half(float x) { return 0.5f * x; }
static int half(int x) { return x / 2; }
static void split(float v, float &whole, float &frac)
{
    whole = floorf(v);
    frac = v - whole;
}

// A plain struct with default member initializers.
struct Stats {
    float sum = 0;
    float peak = 0;
    int n = 0;
};

enum class Kind : uint8_t { Square, Circle, Triangle = 5 };

class Shape {
public:
    static constexpr float kPi = 3.14159265f;
    static constexpr int kHistory = 4;

    Shape(Kind kind, float size) : _kind(kind), _size(size) {}

    virtual float area() const
    {
        switch (_kind) {
        case Kind::Square:
            return _size * _size;
        case Kind::Circle:
            return kPi * _size * _size;
        default:
            return 0.4330127f * _size * _size;
        }
    }

    // Overloads: suffixed by signature in Lean.
    void scale(float f) { _size *= f; record(_size); }
    void scale(float f, int times)
    {
        for (int i = 0; i < 3; i++) {
            if (i >= times) break;
            scale(f);
        }
    }

    // A reference out-parameter and a virtual call: area() is the most-derived override.
    float scale_report(float f, float &before)
    {
        before = area();
        scale(f);
        return area();
    }

    float history_sum(int n = kHistory) const
    {
        float sum = 0.0f;
        int i = 0;
        do {
            if (i < n) sum += _history[i];
            i++;
        } while (i < kHistory);
        return sum;
    }

    static float clamp_size(float v) { return isnan(v) ? NAN : (v > 1e6f ? INFINITY : v); }
    void resize(float v) { _size = clamp_size(v); }

    int kind_code() const { return (int)_kind; }

protected:
    void record(float v)
    {
        for (int i = kHistory - 1; i > 0; i--) {
            _history[i] = _history[i - 1];
        }
        _history[0] = v, _count++;
    }

    Kind _kind;
    float _size;
    float _history[kHistory] = {};
    int _count = 0;
};

class Tile : public Shape {
public:
    enum Mode { MODE_IDLE, MODE_SPIN = 3, MODE_HOLD };

    Tile(float size, int rotation) : Shape(Kind::Square, size), _rotation(rotation & 3) {}

    float area() const override { return Shape::area() * 0.5f + (float)_rotation; }

    void rotate(int steps)
    {
        _rotation = (_rotation + (steps & 7)) & 3;
        switch (_rotation) {
        case 0:
            _kind = Kind::Square;
            break;
        case 1:
        case 3:
            _kind = Kind::Circle;
            break;
        default:
            _kind = Kind::Triangle;
            break;
        }
    }

    void set_kind(int k) { _kind = static_cast<Kind>((k & 1) * 5); }

    // A local struct and a local array, updated in a bounded loop; a struct copied into a member.
    float stats(float x)
    {
        Stats st;
        float buf[3] = {x, half(x), 0.0f};
        for (uint8_t i = 0; i < 3; i++) {
            buf[i] += (float)half(i + 3);
            st.sum += buf[i];
            if (fabsf(buf[i]) > st.peak) st.peak = fabsf(buf[i]);
            st.n++;
        }
        float whole, frac;
        split(st.sum, whole, frac);
        _last = st;
        return frac >= 0.5f ? whole : -HUGE_VALF;
    }

    void set_mode(int m)
    {
        switch (m & 3) {
        case 1:
            _mode = MODE_SPIN;
            break;
        case 2:
            _mode = MODE_HOLD;
            break;
        default:
            _mode = MODE_IDLE;
        }
    }

    int mode_code() const
    {
        switch (_mode) {
        case MODE_SPIN:
            return 30;
        case MODE_HOLD:
            return 40 + _last.n;
        default:
            return -1;
        }
    }

private:
    int _rotation;
    Mode _mode = MODE_IDLE;
    Stats _last;
};
