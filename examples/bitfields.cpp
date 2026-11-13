// Bit-fields and packed structs as bytes (cpp2lean --mavlink; README.md, "Phase 4: the MAVLink C library"):
// the layout rules of the reference targets (AAPCS64, x86-64: bit-fields allocated from the least significant
// bit, a field that would cross an aligned unit of its type starts the next unit unless the struct is packed),
// `memcpy` between such structs and bytes in both directions, writes stored modulo 2^width. `Header` is
// AP_Param's Param_header (AP_Param.h:669-675), `Frame` the shape of MAVLink's mavlink_message_t (a packed
// struct with `uint32_t msgid:24` and a member array of wider numbers), `Cross` fields that cross units.
#include <stdint.h>
#include <string.h>

struct Header {
    uint32_t key_low : 8;
    uint32_t type : 5;
    uint32_t key_high : 1;
    uint32_t group_element : 18;
};

struct __attribute__((packed)) Frame {
    uint16_t checksum;
    uint8_t len;
    uint32_t sysid;
    uint32_t msgid : 24;
    uint8_t payload[5];
    uint16_t words[2];
    uint32_t target;
};

struct Cross {
    uint8_t a;
    uint16_t b : 3;
    uint16_t c : 12;
    uint8_t d;
    uint32_t e : 20;
    uint32_t f : 20;
    uint8_t g : 7;
};

// the header word AP_Param stores for a key, a type and a group element (set_key, AP_Param.cpp)
uint32_t header_word(uint16_t key, uint8_t type, uint32_t group)
{
    struct Header h;
    memset(&h, 0, sizeof(h));
    h.key_low = key & 0xFF;
    h.key_high = key >> 8;
    h.type = type;
    h.group_element = group;
    uint32_t w;
    memcpy(&w, &h, sizeof(w));
    return w;
}

// the fields of a header word read back (writes truncate to the width)
uint64_t header_fields(uint32_t w, uint8_t type)
{
    struct Header h;
    memcpy(&h, &w, sizeof(h));
    uint64_t r = h.key_low + ((uint64_t)h.key_high << 8) + ((uint64_t)h.type << 9) + ((uint64_t)h.group_element << 14);
    h.type = type;
    h.group_element += 3;
    memcpy(&w, &h, sizeof(w));
    return (r << 32) ^ w;
}

static uint64_t hash_bytes(const uint8_t *b, uint16_t n)
{
    uint64_t h = 1469598103934665603ULL;
    for (uint16_t i = 0; i < n; i++) {
        h = (h ^ b[i]) * 1099511628211ULL;
    }
    return h;
}

// a packed frame to bytes and back
uint64_t frame_bytes(uint16_t checksum, uint32_t sysid, uint32_t msgid, uint8_t p, uint16_t w, uint32_t target)
{
    struct Frame f;
    memset(&f, 0, sizeof(f));
    f.checksum = checksum;
    f.len = p;
    f.sysid = sysid;
    f.msgid = msgid;
    f.msgid |= (uint32_t)p << 16;
    for (uint8_t i = 0; i < 5; i++) {
        f.payload[i] = (uint8_t)(p + i);
    }
    f.words[0] = w;
    f.words[1] = (uint16_t)(w ^ 0x5a5a);
    f.target = target;
    uint8_t b[sizeof(struct Frame)];
    memcpy(b, &f, sizeof(f));
    struct Frame g;
    memcpy(&g, b, sizeof(g));
    return hash_bytes(b, sizeof(b)) ^ ((uint64_t)g.msgid << 40) ^ g.words[1] ^ ((uint64_t)sizeof(struct Frame) << 56);
}

// bit-fields that cross the units of their type, to bytes and back
uint64_t cross_bytes(uint8_t a, uint16_t b, uint16_t c, uint32_t e, uint32_t f, uint8_t g)
{
    struct Cross x;
    memset(&x, 0, sizeof(x));
    x.a = a;
    x.b = b;
    x.c = c;
    x.d = (uint8_t)(a ^ 0xff);
    x.e = e;
    x.f = f;
    x.g = g;
    uint8_t bytes[sizeof(struct Cross)];
    memcpy(bytes, &x, sizeof(x));
    struct Cross y;
    memcpy(&y, bytes, sizeof(y));
    return hash_bytes(bytes, sizeof(bytes)) ^ ((uint64_t)y.c << 48) ^ ((uint64_t)y.f << 20) ^ y.g ^ ((uint64_t)sizeof(struct Cross) << 60);
}
