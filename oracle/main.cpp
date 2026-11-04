// oracle/main.cpp: the C++ oracle for the Lean ArduCopter port.
//
// Runs ArduPilot's own control classes (AC_PosControl, AC_AttitudeControl(_Multi), AP_MotorsMatrix /
// AP_MotorsMulticopter / Thrust_Linearization, AC_PID family, AP_Math), compiled unmodified from
// /Users/ryan/Research/delegate/ardupilot at 802db19de1, on the samples recorded from a flight of
// the Lean port, and prints per tick what the port prints (Copter/PROTOCOL.md): the four actuators
// and the 18 trace numbers, as exact decimals, then '|' and the bit patterns of the same 22 values.
//
// Everything in this file is harness, not ArduPilot code. It mirrors the Lean harness line for line:
//   Copter/Loop.lean   `loop` (scheduler_loop, ins_update, run_rate_controller_main,
//                      motors_output_main, read_AHRS, read_inertia, enter_auto, update_flight_mode),
//                      `takeover`, `enter_auto`;
//   Copter/ModeAuto.lean `init` -> AC_WPNav::wp_and_spline_init_m (its calls into AC_PosControl),
//                      `wp_run`, `loiter_start` (AutoYaw HOLD);
//   Copter/AutoYaw.lean `set_mode`, `yaw_rad`, `rate_rads`, `get_heading`;
//   Copter/Main.lean   input parsing (position as double, the rest as float, dt to microseconds,
//                      half up), exact printing.
// The navigator (AC_WPNav, which the port replaces by SimplePath) is not under test: its per-tick
// outputs, the position/velocity/acceleration it hands to AC_PosControl::set_pos_vel_accel_NED_m,
// are read from the port's trace (--nav FILE, the 18-column trace of `copter --trace`; columns 1-9).
// The trace holds the target after the tick; that equals what AC_WPNav sent unless the position
// error clamp of AC_P_2D/AC_P_1D::update_all moved it (AC_P_2D.cpp:32-34, AC_P_1D.cpp:32-38). The
// oracle counts the ticks on which the clamp fires on the fed value (stderr summary).
// The submode schedule (the tick at which the mission completes and ModeAuto::loiter_start switches
// AutoYaw to HOLD) is navigator state too; it is given by --hold-from N (1-based tick), obtained
// from the Lean port by oracle/probe/ModeSchedule.lean.

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_Motors/AP_MotorsMatrix.h>
#include <AC_AttitudeControl/AC_AttitudeControl_Multi.h>
#include <AC_AttitudeControl/AC_PosControl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>

extern AP_AHRS oracle_ahrs;              // oracle_env.cpp
extern AP_Scheduler oracle_scheduler;    // oracle_env.cpp
extern uint64_t oracle_micros;           // oracle_env.cpp: the HAL clock (sum of loop times)
extern uint32_t oracle_internal_errors;  // oracle_env.cpp
extern uint32_t oracle_param_saves;      // oracle_env.cpp

// ---------------------------------------------------------------------------------------------
// Access to protected members, for the harness only. These subclasses add no virtual overrides
// and no data, so the objects behave exactly as the ArduPilot classes.

class OracleMotors : public AP_MotorsMatrix {
public:
    OracleMotors(uint16_t speed_hz) : AP_MotorsMatrix(speed_hz) {}
    float actuator(uint8_t i) const { return _actuator[i]; }
    // the Lean port's environment assumption (AP_MotorsMulticopter.lean header): THROTTLE_UNLIMITED
    void force_spool_state_throttle_unlimited() { _spool_state = SpoolState::THROTTLE_UNLIMITED; }
    // Copter.takeover: "the motors' throttle filter output is set to the throttle it stores"
    void preset_throttle_filter() { _throttle_filter.reset(_throttle_in); }
    float throttle_in() const { return _throttle_in; }
    float throttle_filter() const { return _throttle_filter.get(); }
};

class OraclePosControl : public AC_PosControl {
public:
    OraclePosControl(AP_AHRS_View &ahrs, const AP_Motors &motors, AC_AttitudeControl &att) :
        AC_PosControl(ahrs, motors, att) {}
    const Vector3f &accel_desired() const { return _accel_desired_ned_mss; }
};

// ---------------------------------------------------------------------------------------------
// Parameters by ArduPilot name, through the real var_info tables (the AP_Param tree of
// ArduCopter/Parameters.cpp: "ATC_" -> attitude_control_var_info = AC_AttitudeControl_Multi::var_info,
// "PSC" -> AC_PosControl::var_info, "MOT_" -> motors_var_info = AP_MotorsMatrix::var_info).

struct ParamRef {
    std::string name;
    void *ptr;
    uint8_t type;
};

static void collect_params(std::vector<ParamRef> &out, const std::string &prefix, const void *object,
                           const AP_Param::GroupInfo *info)
{
    const ptrdiff_t base = (ptrdiff_t)object;
    for (uint8_t i = 0; info[i].type != AP_PARAM_NONE; i++) {
        const AP_Param::GroupInfo &g = info[i];
        const std::string name = prefix + g.name;
        if (g.type == AP_PARAM_GROUP) {
            const AP_Param::GroupInfo *sub = (g.flags & AP_PARAM_FLAG_INFO_POINTER) ? *g.group_info_ptr : g.group_info;
            const void *subobj = (const void *)(base + g.offset);
            if (g.flags & AP_PARAM_FLAG_POINTER) {
                subobj = *(const void * const *)subobj;
                if (subobj == nullptr) {
                    continue;
                }
            }
            collect_params(out, name, subobj, sub);
        } else {
            out.push_back(ParamRef{name, (void *)(base + g.offset), g.type});
        }
    }
}

static float param_get(const ParamRef &p)
{
    switch (p.type) {
    case AP_PARAM_INT8: return ((AP_Int8 *)p.ptr)->get();
    case AP_PARAM_INT16: return ((AP_Int16 *)p.ptr)->get();
    case AP_PARAM_INT32: return ((AP_Int32 *)p.ptr)->get();
    case AP_PARAM_FLOAT: return ((AP_Float *)p.ptr)->get();
    default: return 0;
    }
}

// set as AP_Param::set_value does (AP_Param.cpp:1501-1519)
static void param_set(const ParamRef &p, float v)
{
    switch (p.type) {
    case AP_PARAM_INT8: ((AP_Int8 *)p.ptr)->set(v); break;
    case AP_PARAM_INT16: ((AP_Int16 *)p.ptr)->set(v); break;
    case AP_PARAM_INT32: ((AP_Int32 *)p.ptr)->set(v); break;
    case AP_PARAM_FLOAT: ((AP_Float *)p.ptr)->set(v); break;
    default: break;
    }
}

// ---------------------------------------------------------------------------------------------
// Exact decimal printing (Copter/Text.lean `exactDecimal`: no exponent, trailing zeros dropped,
// the sign of zero dropped). Apple's printf prints the exact binary value for %.Nf.

static std::string exact_decimal(double x)
{
    if (isnan(x)) {
        return "nan";
    }
    if (isinf(x)) {
        return x < 0 ? "-inf" : "inf";
    }
    if (x == 0) {
        return "0";
    }
    static char buf[1400];
    snprintf(buf, sizeof(buf), "%.1100f", x);
    std::string s(buf);
    size_t dot = s.find('.');
    if (dot != std::string::npos) {
        size_t end = s.find_last_not_of('0');
        if (end == dot) {
            end--;
        }
        s.erase(end + 1);
    }
    return s;
}

static std::string bits32(float f)
{
    uint32_t u;
    memcpy(&u, &f, 4);
    char b[16];
    snprintf(b, sizeof(b), "%08x", u);
    return b;
}

static std::string bits64(double d)
{
    uint64_t u;
    memcpy(&u, &d, 8);
    char b[24];
    snprintf(b, sizeof(b), "%016llx", (unsigned long long)u);
    return b;
}

// ---------------------------------------------------------------------------------------------
// Input parsing (Copter/Main.lean parseInput?, toMicros)

// round an exact non-negative decimal number of seconds to whole microseconds, half up
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

// ---------------------------------------------------------------------------------------------
// Harness values that are not parameters of the compiled classes (Copter/Parameters.lean): the
// AC_WPNav parameters the navigator's calls into AC_PosControl use, the vehicle scalars, run values.

struct HarnessParams {
    float WP_SPD = 10.0f;        // AC_WPNav.cpp:57 default (WP_SPD_DEFAULT)
    float WP_SPD_UP = 2.5f;      // :75
    float WP_SPD_DN = 1.5f;      // :84
    float WP_ACC = 2.5f;         // :93 (WPNAV_ACCELERATION_MS)
    float WP_ACC_Z = 1.0f;       // :102
    int WP_YAW_BEHAVIOR = 2;     // ArduCopter Parameters.cpp:123, LOOK_AT_NEXT_WP_EXCEPT_RTL
    float PILOT_Y_RATE_TC = 0.0f;
    float ACRO_RP_RATE_TC = 0.0f;
    float air_density_ratio = 1.0f;
    int start_hover = 1;
};

static bool set_harness_param(HarnessParams &h, const std::string &name, float v)
{
    if (name == "WP_SPD") h.WP_SPD = v;
    else if (name == "WP_SPD_UP") h.WP_SPD_UP = v;
    else if (name == "WP_SPD_DN") h.WP_SPD_DN = v;
    else if (name == "WP_ACC") h.WP_ACC = v;
    else if (name == "WP_ACC_Z") h.WP_ACC_Z = v;
    else if (name == "WP_YAW_BEHAVIOR") h.WP_YAW_BEHAVIOR = (int)v;
    else if (name == "PILOT_Y_RATE_TC") h.PILOT_Y_RATE_TC = v;
    else if (name == "ACRO_RP_RATE_TC") h.ACRO_RP_RATE_TC = v;
    else if (name == "run.air_density_ratio") h.air_density_ratio = v;
    else if (name == "run.start_hover") h.start_hover = (int)v;
    else if (name == "WP_RFND_USE" || name == "WP_JERK" || name == "WP_TER_MARGIN" ||
             name == "WP_RADIUS_M" || name == "WP_ACC_CNR") {
        // navigator-only parameters: the navigator's outputs come from the trace
    } else return false;
    return true;
}

// ---------------------------------------------------------------------------------------------
// --bench (oracle/bench.py, BENCH.md): the execution time of one control tick, without parsing or
// printing. All inputs and navigator targets are parsed first; every pass builds fresh objects
// (construction, parameters copied from the reference objects of main(), boot, takeover on the first
// sample: all untimed), then times only the per-tick cascade of the loop in main() (scheduler and
// gyro, rate controller, motors output, AHRS view, estimates, first-tick Auto entry, AutoYaw,
// position controller, attitude controller) with std::chrono::steady_clock. WARMUP untimed passes,
// then PASSES passes timed around the whole tick loop and PASSES passes timed per tick. The
// checksum, the XOR of the 4 actuator bit patterns over all ticks of a pass, is printed so the work
// cannot be optimized away; it is the same for every pass and equals the port's (Copter/Bench.lean).

#include <chrono>
#include <algorithm>
#include <cmath>

struct BenchNav {
    Vector3p pos;
    Vector3f vel, acc;
};

static void copy_param(const ParamRef &dst, const ParamRef &src)
{
    switch (src.type) {
    case AP_PARAM_INT8: ((AP_Int8 *)dst.ptr)->set(((AP_Int8 *)src.ptr)->get()); break;
    case AP_PARAM_INT16: ((AP_Int16 *)dst.ptr)->set(((AP_Int16 *)src.ptr)->get()); break;
    case AP_PARAM_INT32: ((AP_Int32 *)dst.ptr)->set(((AP_Int32 *)src.ptr)->get()); break;
    case AP_PARAM_FLOAT: ((AP_Float *)dst.ptr)->set(((AP_Float *)src.ptr)->get()); break;
    default: break;
    }
}

// AP_MotorsMatrix's constructor panics if its private static _singleton is set (AP_MotorsMatrix.h:20-24);
// a fresh object per pass needs it cleared. An explicit instantiation may name a private member
// ([temp.explicit]), which gives the harness its address without editing ArduPilot code.
struct BenchMotorsSingleton {
    typedef AP_MotorsMatrix **type;
    friend type bench_get(BenchMotorsSingleton);
};
template <typename Tag, typename Tag::type M> struct BenchRob {
    friend typename Tag::type bench_get(Tag) { return M; }
};
template struct BenchRob<BenchMotorsSingleton, &AP_MotorsMatrix::_singleton>;

static int run_bench(const std::vector<ParamRef> &ref, const HarnessParams &h,
                     const std::vector<std::vector<std::string>> &navtxt, long hold_from, int warmup, int passes)
{
    using clk = std::chrono::steady_clock;
    // ---- parse everything first
    const clk::time_point tp0 = clk::now();
    std::vector<Sample> smps;
    {
        std::string line;
        while (std::getline(std::cin, line)) {
            if (line.find_first_not_of(" \t\r\n") == std::string::npos) {
                continue;
            }
            Sample smp;
            if (!parse_sample(line, smp)) {
                fprintf(stderr, "oracle: bad input line %zu\n", smps.size() + 1);
                return 1;
            }
            smps.push_back(smp);
        }
    }
    if (smps.empty() || navtxt.size() < smps.size()) {
        fprintf(stderr, "oracle: no input, or navigator trace shorter than the input\n");
        return 1;
    }
    std::vector<BenchNav> nav(smps.size());
    for (size_t i = 0; i < smps.size(); i++) {
        const std::vector<std::string> &n = navtxt[i];
        nav[i].pos = Vector3p(strtod(n[0].c_str(), nullptr), strtod(n[1].c_str(), nullptr), strtod(n[2].c_str(), nullptr));
        nav[i].vel = Vector3f(strtof(n[3].c_str(), nullptr), strtof(n[4].c_str(), nullptr), strtof(n[5].c_str(), nullptr));
        nav[i].acc = Vector3f(strtof(n[6].c_str(), nullptr), strtof(n[7].c_str(), nullptr), strtof(n[8].c_str(), nullptr));
    }
    const size_t N = smps.size();
    const int64_t parse_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clk::now() - tp0).count();

    // one pass; per_tick != nullptr: time every tick into it; returns the checksum, *total_ns the loop
    auto pass = [&](std::vector<int64_t> *per_tick, int64_t *total_ns) -> uint32_t {
        // ---- untimed: fresh objects and globals, parameters, boot, takeover (as main())
        oracle_scheduler._tick_counter32 = 0;
        oracle_scheduler._tick_counter = 0;
        oracle_scheduler._last_loop_time_s = 0.0f;
        oracle_micros = 0;
        oracle_ahrs.sample = AP_AHRS::Sample();
        *bench_get(BenchMotorsSingleton()) = nullptr;
        OracleMotors *motors = new OracleMotors(oracle_scheduler.get_loop_rate_hz());
        AP_AHRS_View *ahrs_view = new AP_AHRS_View(oracle_ahrs, ROTATION_NONE);
        AC_AttitudeControl_Multi *attitude_control = new AC_AttitudeControl_Multi(*ahrs_view, *motors);
        OraclePosControl *pos_control = new OraclePosControl(*ahrs_view, *motors, *attitude_control);
        std::vector<ParamRef> mine;
        collect_params(mine, "ATC_", attitude_control, AC_AttitudeControl_Multi::var_info);
        collect_params(mine, "PSC", pos_control, AC_PosControl::var_info);
        collect_params(mine, "MOT_", motors, AP_MotorsMatrix::var_info);
        for (size_t i = 0; i < mine.size(); i++) {
            copy_param(mine[i], ref[i]);
        }
        motors->init(AP_Motors::MOTOR_FRAME_QUAD, AP_Motors::MOTOR_FRAME_TYPE_X);
        motors->armed(true);
        motors->set_interlock(true);
        motors->set_desired_spool_state(AP_Motors::DesiredSpoolState::THROTTLE_UNLIMITED);
        motors->force_spool_state_throttle_unlimited();
        enum class YawMode { HOLD, LOOK_AT_NEXT_WP } yaw_mode = YawMode::LOOK_AT_NEXT_WP;
        float yaw_angle_rad = 0.0f;
        bool in_auto = false;
        {
            const Sample &smp = smps[0];
            oracle_ahrs.sample.pos_ned = smp.pos;
            oracle_ahrs.sample.vel_ned = smp.vel;
            oracle_ahrs.sample.accel_ef = smp.accel_ef;
            oracle_ahrs.sample.quat = smp.quat;
            oracle_ahrs.sample.gyro = smp.gyro;
            ahrs_view->update();
            attitude_control->relax_attitude_controllers();
            if (h.start_hover) {
                const float hover = motors->get_throttle_hover();
                attitude_control->set_throttle_out(hover, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ);
                motors->preset_throttle_filter();
            }
        }
        uint32_t ck = 0;
        const clk::time_point t_start = clk::now();
        for (size_t k = 0; k < N; k++) {
            const clk::time_point t0 = per_tick ? clk::now() : clk::time_point();
            const Sample &smp = smps[k];
            const long tick = (long)k + 1;
            // ---- the cascade of main()'s loop, verbatim but for the printing and the clamp counts
            const bool first_tick = oracle_scheduler._tick_counter32 == 0;
            oracle_scheduler._tick_counter32++;
            oracle_scheduler._tick_counter++;
            oracle_micros += smp.dt_us;
            oracle_scheduler._last_loop_time_s = first_tick ? 1.0f / 400.0f : float(smp.dt_us) * 1.0e-6f;
            oracle_ahrs.sample.gyro = smp.gyro;
            const float last_loop_time_s = AP::scheduler().get_last_loop_time_s();
            pos_control->set_dt_s(last_loop_time_s);
            attitude_control->set_dt_s(last_loop_time_s);
            motors->set_dt_s(last_loop_time_s);
            attitude_control->rate_controller_run();
            attitude_control->rate_controller_target_reset();
            oracle_ahrs.sample.air_density_ratio = h.air_density_ratio;
            motors->output();
            uint32_t a[4];
            for (int i = 0; i < 4; i++) {
                const float f = motors->actuator(i);
                memcpy(&a[i], &f, 4);
            }
            oracle_ahrs.sample.pos_ned = smp.pos;
            oracle_ahrs.sample.vel_ned = smp.vel;
            oracle_ahrs.sample.accel_ef = smp.accel_ef;
            oracle_ahrs.sample.quat = smp.quat;
            ahrs_view->update();
            pos_control->update_estimates(false);
            const float wp_accel = is_positive(h.WP_ACC) ? h.WP_ACC : 2.5f;
            if (!in_auto) {
                const float wp_speed = MAX(h.WP_SPD, 0.01f);
                const float wp_desired_speed_ne_ms = MAX(wp_speed, 0.01f);
                pos_control->D_init_controller_stopping_point();
                pos_control->NE_init_controller_stopping_point();
                pos_control->NE_set_max_speed_accel_m(wp_desired_speed_ne_ms, wp_accel);
                pos_control->NE_set_correction_speed_accel_m(wp_desired_speed_ne_ms, wp_accel);
                pos_control->D_set_max_speed_accel_m(fabsf(h.WP_SPD_DN), h.WP_SPD_UP, h.WP_ACC_Z);
                pos_control->D_set_correction_speed_accel_m(fabsf(h.WP_SPD_DN), h.WP_SPD_UP, h.WP_ACC_Z);
                attitude_control->set_roll_pitch_rate_tc(h.ACRO_RP_RATE_TC);
                attitude_control->set_yaw_rate_tc(h.PILOT_Y_RATE_TC);
                in_auto = true;
            }
            if (hold_from > 0 && tick == hold_from && yaw_mode != YawMode::HOLD) {
                yaw_mode = YawMode::HOLD;
                yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;
            }
            pos_control->set_pos_terrain_target_D_m(0.0f);
            pos_control->set_pos_vel_accel_NED_m(nav[k].pos, nav[k].vel, nav[k].acc);
            pos_control->NE_update_controller();
            pos_control->D_update_controller();
            AC_AttitudeControl::HeadingCommand heading;
            if (yaw_mode == YawMode::LOOK_AT_NEXT_WP) {
                yaw_angle_rad = pos_control->get_yaw_rad();
                heading.yaw_angle_rad = yaw_angle_rad;
                heading.yaw_rate_rads = pos_control->get_yaw_rate_rads();
                heading.heading_mode = AC_AttitudeControl::HeadingMode::Angle_And_Rate;
            } else {
                yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;
                heading.yaw_angle_rad = yaw_angle_rad;
                heading.yaw_rate_rads = 0.0f;
                heading.heading_mode = AC_AttitudeControl::HeadingMode::Rate_Only;
            }
            attitude_control->input_thrust_vector_heading(pos_control->get_thrust_vector(), heading);
            ck ^= a[0] ^ a[1] ^ a[2] ^ a[3];
            if (per_tick) {
                const clk::time_point t1 = clk::now();
                (*per_tick)[k] = std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count();
            }
        }
        const clk::time_point t_end = clk::now();
        *total_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t_end - t_start).count();
        // the objects are left allocated (no virtual destructors are relied on; 43 passes)
        return ck;
    };

    int64_t tot = 0;
    uint32_t ck0 = 0;
    bool ck_same = true;
    for (int i = 0; i < warmup; i++) {
        const uint32_t c = pass(nullptr, &tot);
        if (i == 0) ck0 = c;
        ck_same = ck_same && c == ck0;
    }
    std::vector<double> pass_mean;
    std::vector<int64_t> totals;
    for (int i = 0; i < passes; i++) {
        const uint32_t c = pass(nullptr, &tot);
        if (warmup == 0 && i == 0) ck0 = c;
        ck_same = ck_same && c == ck0;
        totals.push_back(tot);
        pass_mean.push_back((double)tot / N);
    }
    std::vector<int64_t> all, one(N);
    std::vector<double> timed_mean;
    for (int i = 0; i < passes; i++) {
        const uint32_t c = pass(&one, &tot);
        ck_same = ck_same && c == ck0;
        all.insert(all.end(), one.begin(), one.end());
        int64_t s = 0;
        for (int64_t v : one) s += v;
        timed_mean.push_back((double)s / N);
    }
    // timer overhead: two consecutive reads
    std::vector<int64_t> ovh(100000);
    for (auto &v : ovh) {
        const clk::time_point a = clk::now();
        const clk::time_point b = clk::now();
        v = std::chrono::duration_cast<std::chrono::nanoseconds>(b - a).count();
    }
    auto mean_sd = [](const std::vector<double> &x, double &m, double &sd) {
        m = 0;
        for (double v : x) m += v;
        m /= x.size();
        sd = 0;
        for (double v : x) sd += (v - m) * (v - m);
        sd = x.size() > 1 ? sqrt(sd / (x.size() - 1)) : 0;
    };
    double m, sd, tm, tsd;
    mean_sd(pass_mean, m, sd);
    mean_sd(timed_mean, tm, tsd);
    std::sort(all.begin(), all.end());
    std::sort(ovh.begin(), ovh.end());
    int64_t ttot = 0;
    for (int64_t v : totals) ttot += v;
    auto pct = [&](double q) { return all[std::min(all.size() - 1, (size_t)floor(q * (all.size() - 1)))]; };
    printf("program oracle-cpp\n");
    printf("ticks %zu\nwarmup %d\npasses %d\n", N, warmup, passes);
    printf("total_ns_mean %.0f\n", (double)ttot / passes);
    printf("per_tick_mean_ns %.3f\nper_tick_sd_over_passes_ns %.3f\n", m, sd);
    std::vector<double> pms = pass_mean;
    std::sort(pms.begin(), pms.end());
    printf("per_tick_mean_pass_median_ns %.3f\nper_tick_mean_pass_min_ns %.3f\n", pms[pms.size() / 2], pms[0]);
    printf("timed_per_tick_mean_ns %.3f\ntimed_per_tick_sd_over_passes_ns %.3f\n", tm, tsd);
    printf("per_tick_median_ns %lld\nper_tick_p99_ns %lld\nper_tick_max_ns %lld\nper_tick_min_ns %lld\n",
           (long long)pct(0.5), (long long)pct(0.99), (long long)all.back(), (long long)all.front());
    printf("timer_overhead_median_ns %lld\n", (long long)ovh[ovh.size() / 2]);
    printf("parse_ns %lld\n", (long long)parse_ns);
    printf("checksum %08x\nchecksum_same_every_pass %s\n", ck0, ck_same ? "true" : "false");
    return ck_same ? 0 : 1;
}

// ---------------------------------------------------------------------------------------------

static void usage()
{
    fprintf(stderr,
            "usage: oracle --nav TRACE [--params FILE]... [--set \"NAME VALUE\"]... [--hold-from N]\n"
            "              [--vehicle-calls] [--print-params] < inputs.txt > out.txt\n"
            "       oracle --nav TRACE [--params FILE]... [--hold-from N] --bench [--warmup W] [--passes P] < inputs.txt\n"
            "  --bench: time the per-tick cascade only (oracle/bench.py, BENCH.md); W=3, P=20 by default\n"
            "  --vehicle-calls: also make the three ArduCopter calls the Lean harness leaves out as\n"
            "  no-ops (landed_gain_reduction(false), set_reset_handling_method, set_desired_spool_state)\n"
            "  per input line: m1 m2 m3 m4 and the 18 trace numbers of `copter --trace` as exact decimals,\n"
            "  then '|' and the same 22 values as hex bit patterns (float32; float64 for the position)\n");
}

int main(int argc, char **argv)
{
    std::vector<std::string> param_lines;
    std::string nav_path;
    long hold_from = -1;
    bool print_params = false;
    bool vehicle_calls = false;
    bool bench = false;
    int bench_warmup = 3, bench_passes = 20;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--params" && i + 1 < argc) {
            std::ifstream f(argv[++i]);
            if (!f) {
                fprintf(stderr, "oracle: cannot read %s\n", argv[i]);
                return 2;
            }
            std::string l;
            while (std::getline(f, l)) {
                param_lines.push_back(l);
            }
        } else if (a == "--set" && i + 1 < argc) {
            param_lines.push_back(argv[++i]);
        } else if (a == "--nav" && i + 1 < argc) {
            nav_path = argv[++i];
        } else if (a == "--hold-from" && i + 1 < argc) {
            hold_from = strtol(argv[++i], nullptr, 10);
        } else if (a == "--print-params") {
            print_params = true;
        } else if (a == "--vehicle-calls") {
            vehicle_calls = true;
        } else if (a == "--bench") {
            bench = true;
        } else if (a == "--warmup" && i + 1 < argc) {
            bench_warmup = (int)strtol(argv[++i], nullptr, 10);
        } else if (a == "--passes" && i + 1 < argc) {
            bench_passes = (int)strtol(argv[++i], nullptr, 10);
        } else {
            usage();
            return 2;
        }
    }

    // ---- construction, as ArduCopter/system.cpp allocate_motors (:387, :467, :479), zero-filled
    // (operator new is calloc, AP_Common/c++.cpp:60-75; see oracle_env.cpp)
    OracleMotors *motors = new OracleMotors(oracle_scheduler.get_loop_rate_hz());
    AP_AHRS_View *ahrs_view = new AP_AHRS_View(oracle_ahrs, ROTATION_NONE);
    AC_AttitudeControl_Multi *attitude_control = new AC_AttitudeControl_Multi(*ahrs_view, *motors);
    OraclePosControl *pos_control = new OraclePosControl(*ahrs_view, *motors, *attitude_control);

    std::vector<ParamRef> params;
    collect_params(params, "ATC_", attitude_control, AC_AttitudeControl_Multi::var_info);
    collect_params(params, "PSC", pos_control, AC_PosControl::var_info);
    collect_params(params, "MOT_", motors, AP_MotorsMatrix::var_info);

    // Copter/Parameters.lean `defaults`: run deviations from the code defaults
    HarnessParams h;
    auto set_by_name = [&](const std::string &name, float v) -> bool {
        bool found = false;
        for (auto &p : params) {
            if (p.name == name) {
                param_set(p, v);
                found = true;
            }
        }
        return found;
    };
    set_by_name("ATC_RAT_YAW_P", 0.3f);     // SITL copter.parm:5-6
    set_by_name("ATC_RAT_YAW_I", 0.02f);
    set_by_name("MOT_HOVER_LEARN", 0);      // hover learning off
    set_by_name("MOT_THST_HOVER", 0.39f);   // SITL copter.parm:71
    set_by_name("MOT_BAT_VOLT_MAX", 0.0f);  // code default, kept

    // override lines (Copter/Main.lean applyLines)
    for (auto line : param_lines) {
        size_t hash = line.find('#');
        if (hash != std::string::npos) {
            line = line.substr(0, hash);
        }
        for (auto &c : line) {
            if (c == ',') {
                c = ' ';
            }
        }
        std::istringstream is(line);
        std::vector<std::string> w;
        std::string t;
        while (is >> t) {
            w.push_back(t);
        }
        if (w.empty() || w[0] == "mission.clear" || w[0] == "waypoint") {
            continue;   // the mission is navigator state
        }
        if (w.size() != 2) {
            fprintf(stderr, "oracle: expected NAME VALUE: %s\n", line.c_str());
            return 2;
        }
        const float v = strtof(w[1].c_str(), nullptr);
        if (!set_by_name(w[0], v) && !set_harness_param(h, w[0], v)) {
            fprintf(stderr, "oracle: unknown parameter %s\n", w[0].c_str());
            return 2;
        }
    }

    if (print_params) {
        for (auto &p : params) {
            printf("%s %s\n", p.name.c_str(), exact_decimal(param_get(p)).c_str());
        }
        printf("WP_SPD %s\nWP_SPD_UP %s\nWP_SPD_DN %s\nWP_ACC %s\nWP_ACC_Z %s\nWP_YAW_BEHAVIOR %d\n"
               "PILOT_Y_RATE_TC %s\nACRO_RP_RATE_TC %s\nrun.air_density_ratio %s\nrun.start_hover %d\n",
               exact_decimal(h.WP_SPD).c_str(), exact_decimal(h.WP_SPD_UP).c_str(),
               exact_decimal(h.WP_SPD_DN).c_str(), exact_decimal(h.WP_ACC).c_str(),
               exact_decimal(h.WP_ACC_Z).c_str(), h.WP_YAW_BEHAVIOR,
               exact_decimal(h.PILOT_Y_RATE_TC).c_str(), exact_decimal(h.ACRO_RP_RATE_TC).c_str(),
               exact_decimal(h.air_density_ratio).c_str(), h.start_hover);
        return 0;
    }
    if (h.WP_YAW_BEHAVIOR != 2 && h.WP_YAW_BEHAVIOR != 1) {
        fprintf(stderr, "oracle: only WP_YAW_BEHAVIOR 1 or 2 (LOOK_AT_NEXT_WP) is mirrored\n");
        return 2;
    }

    // ---- navigator outputs from the port's trace
    std::vector<std::vector<std::string>> nav;
    {
        if (nav_path.empty()) {
            usage();
            return 2;
        }
        std::ifstream f(nav_path);
        if (!f) {
            fprintf(stderr, "oracle: cannot read %s\n", nav_path.c_str());
            return 2;
        }
        std::string l;
        while (std::getline(f, l)) {
            std::istringstream is(l);
            std::vector<std::string> w;
            std::string t;
            while (is >> t) {
                w.push_back(t);
            }
            if (w.size() == 22) {
                w.erase(w.begin(), w.begin() + 4);   // a full `--trace` line: drop the actuators
            }
            if (w.size() != 18) {
                fprintf(stderr, "oracle: navigator trace line %zu has %zu numbers\n", nav.size() + 1, w.size());
                return 2;
            }
            nav.push_back(w);
        }
    }

    if (bench) {
        return run_bench(params, h, nav, hold_from, bench_warmup, bench_passes);
    }

    // ---- boot: AP_MotorsMatrix::init(QUAD, X) (radio.cpp:56, AP_MotorsMatrix.cpp:23-41)
    motors->init(AP_Motors::MOTOR_FRAME_QUAD, AP_Motors::MOTOR_FRAME_TYPE_X);
    // armed, interlocked, THROTTLE_UNLIMITED (the AP_Motors port's environment assumption)
    motors->armed(true);
    motors->set_interlock(true);
    motors->set_desired_spool_state(AP_Motors::DesiredSpoolState::THROTTLE_UNLIMITED);
    motors->force_spool_state_throttle_unlimited();

    // AutoYaw (mode.h:311-410), initial _mode LOOK_AT_NEXT_WP
    enum class YawMode { HOLD, LOOK_AT_NEXT_WP } yaw_mode = YawMode::LOOK_AT_NEXT_WP;
    float yaw_angle_rad = 0.0f;

    bool started = false;
    bool in_auto = false;
    size_t tick = 0;
    uint32_t clamp_ne = 0, clamp_d = 0;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.find_first_not_of(" \t\r\n") == std::string::npos) {
            continue;
        }
        Sample smp;
        if (!parse_sample(line, smp)) {
            fprintf(stderr, "oracle: bad input line %zu\n", tick + 1);
            return 1;
        }
        if (tick >= nav.size()) {
            fprintf(stderr, "oracle: navigator trace shorter than the input\n");
            return 1;
        }

        if (!started) {
            // Copter.takeover (Loop.lean): view of the first sample, relax, hover throttle
            oracle_ahrs.sample.pos_ned = smp.pos;
            oracle_ahrs.sample.vel_ned = smp.vel;
            oracle_ahrs.sample.accel_ef = smp.accel_ef;
            oracle_ahrs.sample.quat = smp.quat;
            oracle_ahrs.sample.gyro = smp.gyro;
            ahrs_view->update();
            attitude_control->relax_attitude_controllers();
            if (h.start_hover) {
                const float hover = motors->get_throttle_hover();
                attitude_control->set_throttle_out(hover, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ);
                motors->preset_throttle_filter();
            }
            started = true;
        }
        tick++;

        // scheduler_loop (AP_Scheduler.cpp:348-377)
        const bool first_tick = oracle_scheduler._tick_counter32 == 0;
        oracle_scheduler._tick_counter32++;
        oracle_scheduler._tick_counter++;
        oracle_micros += smp.dt_us;
        oracle_scheduler._last_loop_time_s = first_tick ? 1.0f / 400.0f : float(smp.dt_us) * 1.0e-6f;

        // AP_InertialSensor::update: the tick's gyro
        oracle_ahrs.sample.gyro = smp.gyro;

        // Copter::run_rate_controller_main (Attitude.cpp:10-24)
        const float last_loop_time_s = AP::scheduler().get_last_loop_time_s();
        pos_control->set_dt_s(last_loop_time_s);
        attitude_control->set_dt_s(last_loop_time_s);
        motors->set_dt_s(last_loop_time_s);
        attitude_control->rate_controller_run();
        attitude_control->rate_controller_target_reset();

        // Copter::motors_output_main -> AP_MotorsMulticopter::output
        oracle_ahrs.sample.air_density_ratio = h.air_density_ratio;
        motors->output();
        const float act[4] = {motors->actuator(0), motors->actuator(1), motors->actuator(2), motors->actuator(3)};

        // Copter::read_AHRS
        oracle_ahrs.sample.pos_ned = smp.pos;
        oracle_ahrs.sample.vel_ned = smp.vel;
        oracle_ahrs.sample.accel_ef = smp.accel_ef;
        oracle_ahrs.sample.quat = smp.quat;
        ahrs_view->update();

        // Copter::read_inertia
        pos_control->update_estimates(false);

        // enter_auto on the first tick: ModeAuto::init -> wp_nav->wp_and_spline_init_m()
        // (AC_WPNav.cpp:213-267, its calls into AC_PosControl), then mode.cpp:467-469
        const float wp_accel = is_positive(h.WP_ACC) ? h.WP_ACC : 2.5f;     // get_wp_acceleration_mss
        if (!in_auto) {
            const float wp_speed = MAX(h.WP_SPD, 0.01f);                     // WP_SPD_MIN
            const float wp_desired_speed_ne_ms = MAX(wp_speed, 0.01f);
            pos_control->D_init_controller_stopping_point();
            pos_control->NE_init_controller_stopping_point();
            pos_control->NE_set_max_speed_accel_m(wp_desired_speed_ne_ms, wp_accel);
            pos_control->NE_set_correction_speed_accel_m(wp_desired_speed_ne_ms, wp_accel);
            pos_control->D_set_max_speed_accel_m(fabsf(h.WP_SPD_DN), h.WP_SPD_UP, h.WP_ACC_Z);
            pos_control->D_set_correction_speed_accel_m(fabsf(h.WP_SPD_DN), h.WP_SPD_UP, h.WP_ACC_Z);
            attitude_control->set_roll_pitch_rate_tc(h.ACRO_RP_RATE_TC);
            attitude_control->set_yaw_rate_tc(h.PILOT_Y_RATE_TC);
            in_auto = true;
        }

        // Copter::update_flight_mode (mode.cpp:502-513): landed_gain_reduction and the EKF reset
        // method, which the Lean harness leaves out (Loop.lean: identity / reset handling not ported)
        if (vehicle_calls) {
            attitude_control->landed_gain_reduction(false);
            pos_control->set_reset_handling_method(yaw_mode == YawMode::HOLD ?
                AC_PosControl::EKFResetMethod::MoveTarget : AC_PosControl::EKFResetMethod::MoveVehicle);
        }

        // ModeAuto::run: mission bookkeeping is navigator state; at the tick the mission completes,
        // exit_mission -> loiter_start -> auto_yaw.set_mode(HOLD) (mode_auto.cpp:374-395)
        if (hold_from > 0 && (long)tick == hold_from && yaw_mode != YawMode::HOLD) {
            yaw_mode = YawMode::HOLD;
            yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;   // autoyaw.cpp:72-74
        }

        // ModeAuto::wp_run (mode_auto.cpp:1134-1154)
        // wp_nav->update_wpnav(): advance_wp_target_along_track's calls into AC_PosControl
        // (AC_WPNav.cpp:566-640), with the navigator's targets from the trace, then
        // NE_update_controller (AC_WPNav.cpp:740)
        if (vehicle_calls) {
            // mode_auto.cpp:1143
            motors->set_desired_spool_state(AP_Motors::DesiredSpoolState::THROTTLE_UNLIMITED);
        }
        const std::vector<std::string> &n = nav[tick - 1];
        const Vector3p nav_pos(strtod(n[0].c_str(), nullptr), strtod(n[1].c_str(), nullptr), strtod(n[2].c_str(), nullptr));
        const Vector3f nav_vel(strtof(n[3].c_str(), nullptr), strtof(n[4].c_str(), nullptr), strtof(n[5].c_str(), nullptr));
        const Vector3f nav_acc(strtof(n[6].c_str(), nullptr), strtof(n[7].c_str(), nullptr), strtof(n[8].c_str(), nullptr));
        pos_control->set_pos_terrain_target_D_m(0.0f);
        pos_control->set_pos_vel_accel_NED_m(nav_pos, nav_vel, nav_acc);
        pos_control->NE_update_controller();
        if (pos_control->get_pos_desired_NED_m().x != nav_pos.x || pos_control->get_pos_desired_NED_m().y != nav_pos.y) {
            clamp_ne++;
        }
        pos_control->D_update_controller();
        if (pos_control->get_pos_desired_NED_m().z != nav_pos.z) {
            clamp_d++;
        }
        // auto_yaw.get_heading() (autoyaw.cpp:378-417, AutoYaw.lean)
        AC_AttitudeControl::HeadingCommand heading;
        if (yaw_mode == YawMode::LOOK_AT_NEXT_WP) {
            yaw_angle_rad = pos_control->get_yaw_rad();
            heading.yaw_angle_rad = yaw_angle_rad;
            heading.yaw_rate_rads = pos_control->get_yaw_rate_rads();
            heading.heading_mode = AC_AttitudeControl::HeadingMode::Angle_And_Rate;
        } else {
            yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;
            heading.yaw_angle_rad = yaw_angle_rad;
            heading.yaw_rate_rads = 0.0f;
            heading.heading_mode = AC_AttitudeControl::HeadingMode::Rate_Only;
        }
        attitude_control->input_thrust_vector_heading(pos_control->get_thrust_vector(), heading);

        // ---- output
        const Vector3p &pd = pos_control->get_pos_desired_NED_m();
        const Vector3f &vd = pos_control->get_vel_desired_NED_ms();
        const Vector3f &ad = pos_control->accel_desired();
        const Vector3f tv = pos_control->get_thrust_vector();
        const Vector3f &eu = attitude_control->get_att_target_euler_rad();
        const Vector3f rb = attitude_control->rate_bf_targets();
        std::string out;
        for (int i = 0; i < 4; i++) {
            out += exact_decimal(act[i]) + " ";
        }
        out += exact_decimal(pd.x) + " " + exact_decimal(pd.y) + " " + exact_decimal(pd.z);
        const Vector3f *v3[] = {&vd, &ad, &tv, &eu, &rb};
        for (const Vector3f *v : v3) {
            out += " " + exact_decimal(v->x) + " " + exact_decimal(v->y) + " " + exact_decimal(v->z);
        }
        out += " |";
        for (int i = 0; i < 4; i++) {
            out += " " + bits32(act[i]);
        }
        out += " " + bits64(pd.x) + " " + bits64(pd.y) + " " + bits64(pd.z);
        for (const Vector3f *v : v3) {
            out += " " + bits32(v->x) + " " + bits32(v->y) + " " + bits32(v->z);
        }
        puts(out.c_str());
    }
    fprintf(stderr, "oracle: %zu ticks; position clamp fired on %u (NE) and %u (D) ticks; "
            "INTERNAL_ERROR reports %u; parameter saves %u\n",
            tick, clamp_ne, clamp_d, oracle_internal_errors, oracle_param_saves);
    return 0;
}
