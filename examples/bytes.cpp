// cpp2lean demo (phase 2b, control flow and bytes), written for the demo: the constructs added for
// ArduPilot's formatter (print_vprintf, ftoa_engine, utoa_invert, AP_HAL::Util::vsnprintf) and for
// StorageManager, through functions of numbers that the difftest drives.
// --gotos: a forward `goto` out of nested statements to a label later in an enclosing block, a `goto`
// from one branch of an `if` into the other, a `goto` into a `switch` case from before the switch and
// from another case, a `goto` out of a loop into the body of a later `if`, `continue` in a `do` loop,
// a `switch` case that falls through into the next.
// --byte-objects: `&x` passed as bytes (`void *`, `uint8_t *`) and written through (stored back into
// x), a pointer to the bytes of a float read as bytes, a union of a float and its bit pattern, a struct
// copied to and from bytes with `memcpy` at the target's record layout (padding included), `sizeof`.
// --c-strings: a function returning a pointer into the array it is passed, the difference of two
// pointers into one array, an object holding a `char *const` into its caller's buffer, a pointer
// parameter of a base class whose calls pass an object of a derived class (a virtual call through it).
#include <cstdint>
#include <cstring>

// ---- gotos
int32_t g_forward(int32_t a, int32_t b, uint8_t n)
{
    int32_t r = 0;
    a &= 0xffff;        // (no signed overflow below: the C++ would be undefined)
    b &= 0xffff;
    for (uint8_t i = 0; i < (n & 7); i++) {
        if (a > b) {
            r += 1;
            goto tail;
        } else if (a == b) {
            r += 2;
        }
        switch (b & 3) {
        case 0:
            r += 5;
            [[fallthrough]];
        case 1:
            r += 7;
            break;
        case 2:
            goto tail;
        default:
            r -= 1;
            break;
        }
        r += a;
    tail:
        a = a - 3;
    }
    return r;
}

int32_t g_branches(int32_t c, int32_t x)
{
    int32_t flags = 0;
    if (c >= 'E' && c <= 'G') {
        flags |= 16;
        c += 'e' - 'E';
        goto lower;
    } else if (c >= 'e' && c <= 'g') {
        int32_t k;
        flags &= ~16;
    lower:
        k = c - 'e';
        flags += k * 100 + (x & 0xffff);
    }
    return flags;
}

int32_t g_switch(int32_t c, uint32_t v)
{
    int32_t base;
    int32_t r = 0;
    if (c == 'u') {
        base = 10;
        goto conv;
    }
    switch (c) {
    case 'o':
        base = 8;
        goto conv;
    case 'p':
        r = 1;
        [[fallthrough]];
    case 'x':
        base = 16;
        goto conv;
    case 'X':
        r = 2;
        base = 16 | 0x200;
    conv:
        r += (int32_t)(v % (uint32_t)(base & 0xff));
        break;
    default:
        return -1;
    }
    return r * 1000 + base;
}

int32_t g_loop(int32_t a, int32_t b)
{
    int32_t out = 0;
    int32_t i = 0;
    do {
        if (i == b) {
            for (int32_t j = 0; j < 3; j++) {
                out += j;
            }
            goto round;
        }
        out += a & 0xff;
        i++;
    } while (i < 8);
    out *= 2;
    if (out > 100) {
    round:
        out += 1000;
    }
    return out;
}

int32_t g_continue(int32_t a, uint8_t n)
{
    int32_t r = 0;
    uint8_t i = 0;
    do {
        i++;
        switch (i % 3) {
        case 0:
            r += a & 0xff;
            continue;
        case 1:
            r -= 1;
            break;
        default:
            break;
        }
        if (r > 50) {
            break;
        }
        r *= 2;
    } while (i < (n & 15));
    return r;
}

// ---- bytes
static bool read_bytes(void *dst, uint16_t at, uint8_t n)
{
    uint8_t *b = (uint8_t *)dst;
    for (uint8_t i = 0; i < n; i++) {
        b[i] = (uint8_t)(at * 7 + i * 13);
    }
    return n > 0;
}

uint32_t b_scalar(uint16_t at, uint8_t which)
{
    uint32_t v = 0;
    uint16_t w = 1;
    float f = 1.0f;
    bool ok = read_bytes(&v, at, 4);
    if (which & 1) {
        ok = read_bytes(&w, at + 1, 2) && ok;
    }
    if (which & 2) {
        read_bytes(&f, at, 4);
    }
    return v + w + (ok ? 1 : 0) + (uint32_t)(f == f ? 0 : 5);
}

uint32_t b_float(float x)
{
    const uint8_t *bytes = (const uint8_t *)&x;
    union {
        float f;
        uint32_t u;
    } un;
    un.f = x;
    return (uint32_t)bytes[3] * 16777216U + bytes[0] + (un.u & 0xffff0000U) + (uint32_t)sizeof(un);
}

struct Record {
    uint8_t kind;
    float value;
    uint16_t id;
    int8_t delta[3];
};

uint64_t b_struct(uint8_t kind, float value, uint16_t id, int8_t d0)
{
    Record r{};
    r.kind = kind;
    r.value = value;
    r.id = id;
    r.delta[0] = d0;
    r.delta[1] = (int8_t)(d0 + 1);
    r.delta[2] = (int8_t)(d0 * 2);
    uint8_t raw[sizeof(Record)];
    memset(raw, 0x55, sizeof(raw));
    memcpy(raw, &r, sizeof(r));
    raw[4] ^= 1;
    Record back;
    memcpy(&back, raw, sizeof(back));
    uint64_t h = sizeof(Record);
    for (uint8_t i = 0; i < sizeof(raw); i++) {
        if (i == 12) {
            continue;   // (a `continue` in a counted loop)
        }
        h = h * 31 + raw[i];    // every byte, padding (1-3, 13-15) included: `Record r{}` zero-initializes it
    }
    return h + back.id + (uint64_t)(back.value > 0.0f) + (uint64_t)(int64_t)back.delta[2];
}

// ---- pointers that are values
static char *put_digits(uint32_t v, char *s)
{
    do {
        *s++ = '0' + (v % 10);
        v /= 10;
    } while (v);
    return s;
}

uint32_t p_digits(uint32_t v)
{
    char buf[12];
    uint8_t n = put_digits(v, buf) - buf;
    uint32_t h = n;
    for (uint8_t i = 0; i < n; i++) {
        h = h * 10 + (uint8_t)(buf[i] - '0');
    }
    return h;
}

class Sink {
public:
    virtual void put(char c) = 0;
};

class BufSink : public Sink {
public:
    BufSink(char *buf, uint8_t size) : _buf(buf), _size(size) {}
    void put(char c) override {
        if (_n < _size) {
            _buf[_n] = c;
        }
        _n++;
    }
    uint8_t _n = 0;
private:
    char *const _buf;
    const uint8_t _size;
};

static void emit(Sink *s, uint32_t v)
{
    for (uint8_t i = 0; i < 6; i++) {
        s->put('a' + (v & 7));
        v >>= 3;
    }
}

uint64_t p_sink(uint32_t v, uint8_t size)
{
    char out[8];
    memset(out, '.', sizeof(out));
    BufSink sink(out, size & 7);
    emit(&sink, v);
    sink.put('!');
    uint64_t h = sink._n;
    for (uint8_t i = 0; i < 8; i++) {
        h = h * 131 + (uint8_t)out[i];
    }
    return h;
}
