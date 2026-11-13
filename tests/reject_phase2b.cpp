// cpp2lean-options: --pointer-params --runtime-loops --c-strings --byte-objects --gotos --general-loops --hal-storage 64 --boundary HALStub,StorageStub
// The limits of the phase 2b constructs (C strings, varargs, gotos, byte-level objects, the HAL
// storage): each function is rejected at the line marked expect-reject.
#include <cstdarg>
#include <cstdint>
#include <cstring>

class StorageStub {
public:
    virtual bool erase();
    virtual void read_block(void *dst, uint16_t src, size_t n) = 0;
    virtual void write_block(uint16_t dst, const void *src, size_t n) = 0;
};
struct HALStub {
    StorageStub *storage;
};
extern const HALStub &hal;

// a backward goto
int32_t r_backward(int32_t a)
{
    int32_t r = 0;
again:
    r += a;
    if (r < 100) {
        goto again;  // expect-reject
    }
    return r;
}

// a goto into a loop body
int32_t r_into_loop(int32_t a)
{
    int32_t r = 0;
    int32_t i = 0;
    if (a > 3) {
        goto inside;
    }
    while (i < 4) {
        r += i;
    inside:  // expect-reject
        r *= 2;
        i++;
    }
    return r;
}

// a label in a switch case whose statements from the label do not end in `break`
int32_t r_switch_tail(int32_t c)
{
    int32_t r = 0;
    switch (c) {
    case 1:
        goto mid;
    case 2:
        r = 5;
    mid:  // expect-reject
        r += 1;
        return r;
    default:
        break;
    }
    return r;
}

// a write through a pointer to a string literal
uint32_t r_literal_write(uint8_t i)
{
    char *p = (char *)"abc";
    p[i & 1] = 'x';  // expect-reject
    return p[0];
}

// va_arg of a type the variadic slots do not hold
static int32_t r_va(int32_t n, ...)
{
    va_list ap;
    va_start(ap, n);
    int32_t r = (int32_t)va_arg(ap, long double);  // expect-reject
    va_end(ap);
    return r;
}

int32_t r_va_call(int32_t a) { return r_va(1, a); }

// a variadic argument that is a struct
struct Pair {
    int32_t a;
    int32_t b;
};

static int32_t r_va2(int32_t n, ...) { return n; }

int32_t r_va2_call(int32_t x)
{
    Pair p{};
    p.a = x;
    return r_va2(1, p);  // expect-reject
}

// the result of strncpy used
uint32_t r_strncpy_value(uint8_t i)
{
    char a[4] = "ab";
    char b[4];
    char *p = strncpy(b, a, i & 3);  // expect-reject
    return p[0];
}

// a local pointer to the bytes of a variable that is assigned afterwards
uint32_t r_view_changes(uint32_t x)
{
    const uint8_t *b = (const uint8_t *)&x;  // expect-reject
    x = x + 1;
    return b[0];
}

// a union of members of different widths
uint32_t r_union(float f)
{
    union {
        float f;
        uint64_t u;  // expect-reject
    } un;
    un.f = f;
    return (uint32_t)un.u;
}

// the HAL storage: only read_block and write_block
bool r_erase(uint8_t x)
{
    return hal.storage->erase();  // expect-reject
}

// a class with a vtable as bytes
class Virt {
public:
    virtual uint8_t get() { return v; }
    uint8_t v;
};

uint32_t r_vtable_bytes(uint8_t x)
{
    Virt o;
    uint8_t raw[16];
    memcpy(raw, (void *)&o, sizeof(raw));  // expect-reject
    return raw[0] + x;
}

// a `const char *` holding a copy of a buffer that is written while it may point into it
uint32_t r_copy_stale(uint8_t i)
{
    char buf[4] = "ab";
    const char *p = "x";
    if (i & 1) {
        p = buf;
    }
    buf[0] = 'z';  // expect-reject
    return p[0];
}

// memcmp over the padding of a struct
struct Padded {
    uint8_t a;
    uint32_t b;
};

int32_t r_memcmp_padding(uint8_t x)
{
    Padded p{};
    Padded q{};
    p.a = x;
    return memcmp(&p, &q, sizeof(p));  // expect-reject
}
