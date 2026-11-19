// cpp2lean per-tick composition check (ardupilot/compose/compose.sh): the environment of the
// translated classes on the oracle's recorded flight. For each input line (a sample of the
// flight, sim/PROTOCOL.md) and the navigator's targets of the same tick (ardupilot/data/trace.txt,
// as the reference harness reads them), prints the values the translated classes read from outside
// the translations, as hex bit patterns:
//   dt_us | gyro (3) | the AHRS view after AP_AHRS_View::update() of the sample: quaternion (4),
//   roll, pitch, yaw, cos_roll, cos_pitch, cos_yaw, sin_roll, sin_pitch, sin_yaw | the sample's
//   position (3, double), velocity (3), earth-frame acceleration (3) | the navigator's target
//   position (3, double), velocity (3), acceleration (3)
// The AHRS is the stub (ardupilot/stubs/AP_AHRS/AP_AHRS_View.h, compiled here unchanged), so
// these are exactly the values the oracle's control classes read. Input parsing is copied from
// the reference harness (`to_micros`, `parse_sample`, the navigator columns); nothing else is computed.
// Usage: compose_env INPUTS TRACE N > env.txt

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>

// ---- what AP_Math's sources call outside AP_Math (never reached on these paths), as oracle_env.cpp
namespace AP_HAL {
void panic(const char *errormsg, ...) { va_list ap; va_start(ap, errormsg); vfprintf(stderr, errormsg, ap); va_end(ap); abort(); }
}
static AP_InternalError env_internalerror;
AP_InternalError &AP::internalerror() { return env_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line) { fprintf(stderr, "INTERNAL_ERROR\n"); abort(); }
static AP_CustomRotations *env_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *env_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }

// ---- copied from the reference harness: to_micros, Sample, parse_sample
static bool to_micros(const std::string &tok, uint64_t &us)
{
    std::string mant;
    long exp10 = 0;
    size_t i = 0;
    bool neg = false;
    if (i < tok.size() && (tok[i] == '+' || tok[i] == '-')) {
        neg = tok[i] == '-';
        i++;
    }
    bool seen_dot = false;
    for (; i < tok.size(); i++) {
        char c = tok[i];
        if (c >= '0' && c <= '9') {
            mant.push_back(c);
            if (seen_dot) {
                exp10--;
            }
        } else if (c == '.' && !seen_dot) {
            seen_dot = true;
        } else if (c == 'e' || c == 'E') {
            exp10 += strtol(tok.c_str() + i + 1, nullptr, 10);
            break;
        } else {
            return false;
        }
    }
    if (mant.empty()) {
        return false;
    }
    // strip leading zeros
    size_t nz = mant.find_first_not_of('0');
    mant = (nz == std::string::npos) ? "0" : mant.substr(nz);
    if (neg && mant != "0") {
        return false;
    }
    long e = exp10 + 6;
    unsigned __int128 m = 0;
    for (char c : mant) {
        m = m * 10 + (c - '0');
    }
    if (e >= 0) {
        for (long k = 0; k < e; k++) {
            m *= 10;
        }
        us = (uint64_t)m;
    } else {
        unsigned __int128 q = 1;
        for (long k = 0; k < -e; k++) {
            q *= 10;
        }
        us = (uint64_t)((2 * m + q) / (2 * q));
    }
    return true;
}

struct Sample {
    Vector3p pos;
    Vector3f vel, accel_ef, gyro;
    Quaternion quat;
    uint64_t dt_us;
};

static bool parse_sample(const std::string &line, Sample &s)
{
    std::istringstream is(line);
    std::vector<std::string> w;
    std::string t;
    while (is >> t) {
        w.push_back(t);
    }
    if (w.size() != 17) {
        return false;
    }
    auto f = [&](int i) { return strtof(w[i].c_str(), nullptr); };    // correctly rounded, once
    auto d = [&](int i) { return strtod(w[i].c_str(), nullptr); };
    s.pos = Vector3p(d(0), d(1), d(2));
    s.vel = Vector3f(f(3), f(4), f(5));
    s.accel_ef = Vector3f(f(6), f(7), f(8));
    s.quat = Quaternion(f(9), f(10), f(11), f(12));
    s.gyro = Vector3f(f(13), f(14), f(15));
    if (!to_micros(w[16], s.dt_us) || s.dt_us == 0) {
        return false;
    }
    return true;
}

// ---- printing
static void pf(float f) { uint32_t u; memcpy(&u, &f, 4); printf(" %08x", u); }
static void pd(double d) { uint64_t u; memcpy(&u, &d, 8); printf(" %016llx", (unsigned long long)u); }

AP_AHRS env_ahrs;

int main(int argc, char **argv)
{
    if (argc != 4) {
        fprintf(stderr, "usage: compose_env INPUTS TRACE N\n");
        return 2;
    }
    std::ifstream fin(argv[1]), fnav(argv[2]);
    const long n = strtol(argv[3], nullptr, 10);
    AP_AHRS_View view(env_ahrs, ROTATION_NONE);
    std::string line, nl;
    for (long k = 0; k < n && std::getline(fin, line) && std::getline(fnav, nl); k++) {
        Sample smp;
        if (!parse_sample(line, smp)) {
            fprintf(stderr, "compose_env: bad input line %ld\n", k + 1);
            return 1;
        }
        // the navigator's targets: columns 1-9 of the trace
        std::istringstream is(nl);
        std::vector<std::string> w;
        std::string t;
        while (is >> t) {
            w.push_back(t);
        }
        if (w.size() == 22) {
            w.erase(w.begin(), w.begin() + 4);
        }
        if (w.size() != 18) {
            fprintf(stderr, "compose_env: navigator trace line %ld has %zu numbers\n", k + 1, w.size());
            return 1;
        }
        // Copter::read_AHRS: the sample, then the view's update
        env_ahrs.sample.pos_ned = smp.pos;
        env_ahrs.sample.vel_ned = smp.vel;
        env_ahrs.sample.accel_ef = smp.accel_ef;
        env_ahrs.sample.quat = smp.quat;
        env_ahrs.sample.gyro = smp.gyro;
        view.update();
        Quaternion q;
        view.get_quat_body_to_ned(q);
        printf("%llu", (unsigned long long)smp.dt_us);
        pf(smp.gyro.x); pf(smp.gyro.y); pf(smp.gyro.z);
        pf(q.q1); pf(q.q2); pf(q.q3); pf(q.q4);
        pf(view.roll); pf(view.pitch); pf(view.yaw);
        pf(view.cos_roll()); pf(view.cos_pitch()); pf(view.cos_yaw());
        pf(view.sin_roll()); pf(view.sin_pitch()); pf(view.sin_yaw());
        pd(smp.pos.x); pd(smp.pos.y); pd(smp.pos.z);
        pf(smp.vel.x); pf(smp.vel.y); pf(smp.vel.z);
        pf(smp.accel_ef.x); pf(smp.accel_ef.y); pf(smp.accel_ef.z);
        pd(strtod(w[0].c_str(), nullptr)); pd(strtod(w[1].c_str(), nullptr)); pd(strtod(w[2].c_str(), nullptr));
        for (int i = 3; i < 9; i++) {
            pf(strtof(w[i].c_str(), nullptr));
        }
        printf("\n");
    }
    return 0;
}
