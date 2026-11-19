// module_protocol.h: the generic C++ side of a harness module.
//
// It supplies main(), which speaks the harness protocol on stdin/stdout. A module provides two
// functions, in its adapter:
//
//   void module_init(const Params &p);          // build the real objects from a parameter record
//   void module_step(const Input &in, Output &out);   // one tick of the real code
//
// The record types Params, Input, Output, their byte layout and the schema text come from
// module_records.h, which `harness gen NAME` writes from the module's Lean declaration.
//
// Protocol (all integers little-endian; records are packed field by field, f32/i32/u32 as 4 bytes,
// floats as their bit patterns, bool as one byte 0 or 1):
//
//   request             reply
//   'D'                 'K', u32 length, manifest (JSON text: name, code hash, build flags, schemas)
//   'I' params-record   'K'
//   'S' input-record    'K' output-record          ('E' if no init has been done)
//   'Q'                 'K', then the process exits
//
// Include this header in exactly one translation unit (the adapter).
#pragma once

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "module_records.h"

void module_init(const Params &p);
void module_step(const Input &in, Output &out);

// written by the build into codehash.cpp: SHA-256 of every file the compiler read for the module,
// the flags and the compiler version (ardupilot/build.sh)
extern const char harness_code_hash[];
extern const char harness_build_flags[];
extern const char harness_compiler[];

namespace harness_protocol {

static bool read_exact(uint8_t *buf, size_t n)
{
    return fread(buf, 1, n, stdin) == n;
}

static void write_bytes(const void *buf, size_t n)
{
    fwrite(buf, 1, n, stdout);
}

static void write_u32(uint32_t v)
{
    const uint8_t b[4] = {uint8_t(v), uint8_t(v >> 8), uint8_t(v >> 16), uint8_t(v >> 24)};
    write_bytes(b, 4);
}

// JSON string body with the characters that need it escaped
static void append_json_string(char *dst, size_t cap, const char *s)
{
    size_t n = strlen(dst);
    for (; *s != 0 && n + 3 < cap; s++) {
        if (*s == '"' || *s == '\\') {
            dst[n++] = '\\';
        }
        dst[n++] = (*s == '\n') ? ' ' : *s;
    }
    dst[n] = 0;
}

static void describe()
{
    // the schemas plus room for the name, hash, flags and compiler (a PX4 module has hundreds of fields)
    static char m[sizeof(HARNESS_SCHEMA_JSON) + 8192];
    m[0] = 0;
    strcat(m, "{\"name\":\"");
    append_json_string(m, sizeof m, HARNESS_MODULE_NAME);
    strcat(m, "\",\"code_hash\":\"");
    append_json_string(m, sizeof m, harness_code_hash);
    strcat(m, "\",\"flags\":\"");
    append_json_string(m, sizeof m, harness_build_flags);
    strcat(m, "\",\"compiler\":\"");
    append_json_string(m, sizeof m, harness_compiler);
    strcat(m, "\",");
    strcat(m, HARNESS_SCHEMA_JSON);
    strcat(m, "}");
    const uint8_t k = 'K';
    write_bytes(&k, 1);
    write_u32(uint32_t(strlen(m)));
    write_bytes(m, strlen(m));
}

} // namespace harness_protocol

int main()
{
    using namespace harness_protocol;
    static uint8_t pbuf[HARNESS_PARAMS_BYTES + 1];
    static uint8_t ibuf[HARNESS_INPUT_BYTES + 1];
    static uint8_t obuf[HARNESS_OUTPUT_BYTES + 1];
    static char iobuf_in[1 << 16];
    static char iobuf_out[1 << 16];
    setvbuf(stdin, iobuf_in, _IOFBF, sizeof iobuf_in);
    setvbuf(stdout, iobuf_out, _IOFBF, sizeof iobuf_out);
    bool initialized = false;
    for (;;) {
        const int op = getchar();
        if (op == EOF) {
            return 0;
        }
        const uint8_t ok = 'K', err = 'E';
        switch (op) {
        case 'D':
            describe();
            break;
        case 'I': {
            if (!read_exact(pbuf, HARNESS_PARAMS_BYTES)) {
                return 1;
            }
            Params p;
            harness_unpack_params(pbuf, p);
            module_init(p);
            initialized = true;
            write_bytes(&ok, 1);
            break;
        }
        case 'S': {
            if (!read_exact(ibuf, HARNESS_INPUT_BYTES)) {
                return 1;
            }
            if (!initialized) {
                write_bytes(&err, 1);
                break;
            }
            Input in;
            harness_unpack_input(ibuf, in);
            Output out;
            memset(&out, 0, sizeof out);
            module_step(in, out);
            harness_pack_output(out, obuf);
            write_bytes(&ok, 1);
            write_bytes(obuf, HARNESS_OUTPUT_BYTES);
            break;
        }
        case 'Q':
            write_bytes(&ok, 1);
            fflush(stdout);
            return 0;
        default:
            write_bytes(&err, 1);
            fflush(stdout);
            return 2;
        }
        fflush(stdout);
    }
}
