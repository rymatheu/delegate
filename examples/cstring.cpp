// cpp2lean demo (phase 2b, text): `char`, `char[N]` buffers and string literals as byte arrays, byte
// pointers that move, a `const char *` assigned different strings, tables of string literals, the C
// string runtime (CString.lean: strlen, strnlen, strncpy, strcmp, strncmp, strcasecmp, strncasecmp,
// memcpy, memset, memcmp on bytes), `char` arithmetic (signed on the reference target), variadic
// functions with `va_list`/`va_arg`, written for the demo (--c-strings). Every function the difftest
// drives takes numbers; the strings are built from them, so the C library and CString.lean see the
// same bytes.
#include <cstdarg>
#include <cstdint>
#include <cstring>

static const char *const names[] = {"zero", "One", "TWO", "three", ""};

// a string of len characters (len < 8) from an alphabet with letters of both cases, digits and high bytes
static void fill(char *s, uint32_t seed, uint8_t len)
{
    const char alphabet[12] = "aAbBzZ09_\x80\xff";
    for (uint8_t i = 0; i < len; i++) {
        s[i] = alphabet[seed % 11];
        seed /= 11;
    }
    s[len] = 0;
}

uint32_t t_strlen(uint32_t seed, uint8_t len, uint8_t max)
{
    char buf[8];
    fill(buf, seed, len & 7);
    return strlen(buf) + 100 * strnlen(buf, max & 15);
}

int32_t t_strcmp(uint32_t sa, uint32_t sb, uint8_t la, uint8_t lb)
{
    char a[8];
    char b[8];
    fill(a, sa, la & 7);
    fill(b, sb % 4 == 0 ? sa : sb, lb & 7);
    return strcmp(a, b);
}

int32_t t_strncmp(uint32_t sa, uint32_t sb, uint8_t la, uint8_t n)
{
    char a[8];
    char b[8];
    fill(a, sa, la & 7);
    fill(b, sb % 3 == 0 ? sa : sb, (la + sb) & 7);
    return strncmp(a, b, n & 15) + 1000 * strncasecmp(a, b, n & 15) + 1000000 * strcasecmp(a, b);
}

int32_t t_memcmp(uint32_t sa, uint32_t sb, uint8_t n)
{
    char a[8];
    char b[8];
    fill(a, sa, 7);
    fill(b, sb % 2 == 0 ? sa ^ 1 : sb, 7);
    return memcmp(a, b, n & 7);
}

// the bytes of a buffer, folded (so that the difftest compares every byte)
static uint64_t fold(const char *p, uint8_t n)
{
    uint64_t h = 1469598103934665603ULL;
    for (uint8_t i = 0; i < n; i++) {
        h = (h ^ (uint8_t)p[i]) * 1099511628211ULL;
    }
    return h;
}

uint64_t t_strncpy(uint32_t seed, uint8_t len, uint8_t n, uint8_t at)
{
    char src[8];
    char dst[16];
    fill(src, seed, len & 7);
    memset(dst, 'x', sizeof(dst));
    strncpy(&dst[at & 3], src, n % 12);
    memcpy(dst + 12, src + 1, 3);
    return fold(dst, 16);
}

// `char` arithmetic: a char is signed here (-fsigned-char), promoted with sign extension
int32_t t_char(uint8_t v, uint8_t w)
{
    char c = (char)v;
    unsigned char u = (unsigned char)c;
    char d = c - '0';
    if (c < 0) {
        return c * 2 + u;
    }
    return d + (w > 'm' ? 'A' : 'a') + (c == '\n');
}

// a pointer into a string literal or a table of them, moved and reassigned
uint32_t t_literals(uint8_t which, uint8_t skip)
{
    const char *p = "inf";
    if (which & 1) {
        p = "nan";
    }
    if (which & 2) {
        p = names[(which >> 2) % 5];
    }
    uint32_t h = strlen(p);
    for (uint8_t i = 0; i < (skip & 3) && *p != 0; i++) {
        h = h * 31 + (uint8_t)*p++;
    }
    char buf[8] = "abc";
    buf[5] = *p;
    return h * 7 + fold(buf, 8) % 1000;
}

// a variadic function: the kinds string says what each argument is
static int64_t mix(const char *kinds, ...)
{
    va_list ap;
    va_start(ap, kinds);
    int64_t r = 0;
    char k;
    while ((k = *kinds++) != 0) {
        if (k == 'i') {
            r = r * 3 + va_arg(ap, int);
        } else if (k == 'u') {
            r = r * 5 + va_arg(ap, unsigned);
        } else if (k == 'l') {
            r = r * 7 + va_arg(ap, long long);
        } else if (k == 's') {
            const char *s = va_arg(ap, char *);
            r = r * 11 + strlen(s);
        } else {
            double d = va_arg(ap, double);
            r = r * 13 + (int64_t)(d * 16.0);
        }
    }
    va_end(ap);
    return r;
}

int64_t t_varargs(int32_t a, uint32_t b, float c, int16_t d, uint8_t which)
{
    if (which & 1) {
        return mix("iudl", a, b, c, (long long)d);
    }
    return mix("dsiu", (double)c * 2, names[which % 5], d, b);
}
