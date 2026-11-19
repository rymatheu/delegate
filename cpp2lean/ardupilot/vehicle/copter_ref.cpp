// ardupilot/vehicle/copter_ref.cpp: the reference vehicle. ArduPilot's own classes (AP_MotorsMatrix,
// AC_AttitudeControl_Multi, AC_PosControl, AC_WPNav, with AC_PID, Filter, SCurve, SplineCurve and
// AP_Math), compiled unmodified with the stub headers of ardupilot/stubs (ardupilot/vehicle/build.sh),
// run one 400 Hz tick of Auto mode per input line of the lock-step protocol (sim/PROTOCOL.md).
//
// Everything in this file is harness. lean/Vehicle.lean is the same harness over the Lean
// translations of the same classes; the two are kept parallel, function by function, in the same
// order and with the same names:
//   - input parsing and exact printing (the protocol);
//   - parameters by ArduPilot name through the classes' own var_info tables (ArduCopter/Parameters.cpp
//     prefixes ATC_, PSC, MOT_, WP_) and a few harness values;
//   - construction, boot and takeover;
//   - the tick: Copter's fast-loop order (scheduler, rate controller, motors output, AHRS, inertial
//     estimates), entry into Auto on the first tick, Copter::update_flight_mode -> ModeAuto::run;
//   - a thin mission harness written from ArduCopter's C++ (mode_auto.cpp, autoyaw.cpp, and the
//     parts of AP_Mission.cpp that a list of waypoints uses), each function marked with the file
//     and lines it mirrors.
// The AHRS is the stub of ardupilot/stubs/AP_AHRS: its estimate is the input line's sample, and the
// view derives roll, pitch, yaw and their sines and cosines from it as AP_AHRS_View::update does.

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_Motors/AP_MotorsMatrix.h>
#include <AC_AttitudeControl/AC_AttitudeControl_Multi.h>
#include <AC_AttitudeControl/AC_PosControl.h>
#include <AC_WPNav/AC_WPNav.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <chrono>

extern AP_AHRS oracle_ahrs;              // ardupilot/stubs/oracle_env.cpp: the AHRS stub
extern AP_Scheduler oracle_scheduler;    // oracle_env.cpp: the scheduler stub
extern uint64_t oracle_micros;           // oracle_env.cpp: the HAL clock (sum of loop times)

// ---------------------------------------------------------------------------------------------
// Access to protected members, for the harness only (no virtual overrides, no data).

class RefMotors : public AP_MotorsMatrix {
public:
    RefMotors(uint16_t speed_hz) : AP_MotorsMatrix(speed_hz) {}
    float actuator(uint8_t i) const { return _actuator[i]; }
    void force_spool_state_throttle_unlimited() { _spool_state = SpoolState::THROTTLE_UNLIMITED; }
    void preset_throttle_filter() { _throttle_filter.reset(_throttle_in); }
};

class RefPosControl : public AC_PosControl {
public:
    RefPosControl(AP_AHRS_View &ahrs, const AP_Motors &motors, AC_AttitudeControl &att) : AC_PosControl(ahrs, motors, att) {}
    const Vector3f &accel_desired() const { return _accel_desired_ned_mss; }
};

// ---------------------------------------------------------------------------------------------
// Parameters by ArduPilot name, through the real var_info tables

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
            collect_params(out, name, (const void *)(base + g.offset), sub);
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

// as AP_Param::set_value (AP_Param.cpp:1501-1519)
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

// Harness values that are not parameters of the compiled classes (ArduCopter/Parameters.cpp:123 and
// the command models), and two run values.
struct HarnessParams {
    int WP_YAW_BEHAVIOR = 2;            // Parameters.cpp:123, LOOK_AT_NEXT_WP_EXCEPT_RTL
    float PILOT_Y_RATE_TC = 0.0f;       // command_model_pilot_y rate time constant
    float ACRO_RP_RATE_TC = 0.0f;       // command_model_acro_rp rate time constant
    float air_density_ratio = 1.0f;     // the AHRS stub's air density ratio
    int start_hover = 1;                // take over hovering at MOT_THST_HOVER
};

static bool set_harness_param(HarnessParams &h, const std::string &name, float v)
{
    if (name == "WP_YAW_BEHAVIOR") h.WP_YAW_BEHAVIOR = (int)v;
    else if (name == "PILOT_Y_RATE_TC") h.PILOT_Y_RATE_TC = v;
    else if (name == "ACRO_RP_RATE_TC") h.ACRO_RP_RATE_TC = v;
    else if (name == "run.air_density_ratio") h.air_density_ratio = v;
    else if (name == "run.start_hover") h.start_hover = (int)v;
    else return false;
    return true;
}

// ---------------------------------------------------------------------------------------------
// Exact decimal printing (no exponent, trailing zeros dropped, the sign of zero dropped), six
// decimals otherwise, and bit patterns. Apple's printf prints the exact binary value for %.Nf.

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

static std::string six_decimals(double x)
{
    char b[512];
    snprintf(b, sizeof(b), "%.6f", x);
    return b;
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
// Input parsing: position by strtod, the rest by strtof (each decimal rounded once), dt to whole
// microseconds, half up, from the exact decimal.

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
    auto f = [&](int i) { return strtof(w[i].c_str(), nullptr); };
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
// The objects (ArduCopter/system.cpp:387, :454, :467, :479; Copter.h wp_nav), zero-filled
// (operator new is calloc, oracle_env.cpp)

static RefMotors *motors;
static AP_AHRS_View *ahrs_view;
static AC_AttitudeControl_Multi *attitude_control;
static RefPosControl *pos_control;
static AC_WPNav *wp_nav;
static HarnessParams h;
static std::vector<Vector3p> mission;   // the waypoints, NED m from the EKF origin

// ---------------------------------------------------------------------------------------------
// The mission harness: ModeAuto in the WP and LOITER submodes, AutoYaw in LOOK_AT_NEXT_WP and HOLD,
// and AP_Mission for a list of waypoints (MAV_CMD_NAV_WAYPOINT, no delay, absolute NED positions).

enum class SubMode { STARTING, WP, LOITER };                  // mode.h ModeAuto::SubMode (the ones used)
enum class YawMode { HOLD, LOOK_AT_NEXT_WP };                 // mode.h AutoYaw::Mode (the ones used)
enum class MissionState { STOPPED, RUNNING, COMPLETE };       // AP_Mission.h mission_state

struct Auto {
    SubMode mode = SubMode::STARTING;           // ModeAuto::_mode
    bool waiting_to_start = false;              // ModeAuto::waiting_to_start
    uint32_t loiter_time = 0;                   // ModeAuto::loiter_time (ms)
    uint16_t loiter_time_max = 0;               // ModeAuto::loiter_time_max (s): waypoint p1, 0
    YawMode yaw_mode = YawMode::HOLD;           // AutoYaw::_mode (zero-filled: the first enumerator)
    float yaw_angle_rad = 0.0f;                 // AutoYaw::_yaw_angle_rad
    float yaw_rate_rads = 0.0f;                 // AutoYaw::_yaw_rate_rads
    MissionState state = MissionState::STOPPED; // AP_Mission::_flags.state
    int nav_index = -1;                         // AP_Mission::_nav_cmd.index (-1: AP_MISSION_CMD_INDEX_NONE)
    bool nav_cmd_loaded = false;                // AP_Mission::_flags.nav_cmd_loaded
};
static Auto au;

// autoyaw.cpp:36-58 AutoYaw::default_mode(rtl = false)
static YawMode auto_yaw_default_mode()
{
    if (h.WP_YAW_BEHAVIOR == 0) {               // WPYawBehavior::NONE
        return YawMode::HOLD;
    }
    return YawMode::LOOK_AT_NEXT_WP;            // LOOK_AT_NEXT_WP, LOOK_AT_NEXT_WP_EXCEPT_RTL
}

// autoyaw.cpp:60-113 AutoYaw::set_mode
static void auto_yaw_set_mode(YawMode yaw_mode)
{
    if (au.yaw_mode == yaw_mode) {
        return;
    }
    au.yaw_mode = yaw_mode;
    if (yaw_mode == YawMode::HOLD) {
        au.yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;
    }
}

// autoyaw.cpp:234-323 AutoYaw::yaw_rad
static float auto_yaw_yaw_rad()
{
    if (au.yaw_mode == YawMode::HOLD) {
        au.yaw_angle_rad = attitude_control->get_att_target_euler_rad().z;
    } else {
        au.yaw_angle_rad = pos_control->get_yaw_rad();
    }
    return au.yaw_angle_rad;
}

// autoyaw.cpp:325-354 AutoYaw::rate_rads
static float auto_yaw_rate_rads()
{
    if (au.yaw_mode == YawMode::HOLD) {
        au.yaw_rate_rads = 0.0f;
    } else {
        au.yaw_rate_rads = pos_control->get_yaw_rate_rads();
    }
    return au.yaw_rate_rads;
}

// autoyaw.cpp:356-401 AutoYaw::get_heading (no RC input: no pilot yaw)
static AC_AttitudeControl::HeadingCommand auto_yaw_get_heading()
{
    AC_AttitudeControl::HeadingCommand heading;
    heading.yaw_angle_rad = auto_yaw_yaw_rad();
    heading.yaw_rate_rads = auto_yaw_rate_rads();
    heading.heading_mode = au.yaw_mode == YawMode::HOLD ? AC_AttitudeControl::HeadingMode::Rate_Only
                                                         : AC_AttitudeControl::HeadingMode::Angle_And_Rate;
    return heading;
}

// mode_auto.cpp:465-500 ModeAuto::wp_start (with the NED destination: set_wp_destination_NED_m)
static bool wp_start(const Vector3p &dest)
{
    if (!wp_nav->is_active()) {
        Vector3p stopping_point_ned_m;
        wp_nav->wp_and_spline_init_m(0.0f, stopping_point_ned_m);
    }
    if (!wp_nav->set_wp_destination_NED_m(dest)) {
        return false;
    }
    auto_yaw_set_mode(auto_yaw_default_mode());
    au.mode = SubMode::WP;
    return true;
}

// mode_auto.cpp:1623-1676 ModeAuto::set_next_wp (the next command a waypoint)
static bool set_next_wp(int index)
{
    if (index + 1 >= (int)mission.size()) {
        return true;
    }
    return wp_nav->set_wp_destination_next_NED_m(mission[index + 1]);
}

// mode_auto.cpp:1578-1620 ModeAuto::do_nav_wp
static void do_nav_wp(int index)
{
    if (!wp_start(mission[index])) {
        return;
    }
    au.loiter_time = 0;
    au.loiter_time_max = 0;
    set_next_wp(index);
}

// mode_auto.cpp:2297-2321 ModeAuto::verify_nav_wp
static bool verify_nav_wp()
{
    if (!wp_nav->reached_wp_destination()) {
        return false;
    }
    if (au.loiter_time == 0) {
        au.loiter_time = AP_HAL::millis();
    }
    if (((AP_HAL::millis() - au.loiter_time) / 1000) >= au.loiter_time_max) {
        return true;
    }
    return false;
}

// mode_auto.cpp:374-395 ModeAuto::loiter_start
static bool loiter_start()
{
    Vector3p stopping_point_ned_m;
    wp_nav->get_wp_stopping_point_NED_m(stopping_point_ned_m);
    wp_nav->set_wp_destination_NED_m(stopping_point_ned_m);
    auto_yaw_set_mode(YawMode::HOLD);
    au.mode = SubMode::LOITER;
    return true;
}

// AP_Mission.cpp:2142-2152 AP_Mission::complete -> mode_auto.cpp:904-919 ModeAuto::exit_mission (not landed)
static void mission_complete()
{
    au.state = MissionState::COMPLETE;
    loiter_start();
}

// AP_Mission.cpp:2157-2240 AP_Mission::advance_current_nav_cmd (only navigation commands)
static bool mission_advance()
{
    if (au.state != MissionState::RUNNING || au.nav_cmd_loaded) {
        return false;
    }
    const int index = au.nav_index < 0 ? 0 : au.nav_index + 1;
    if (index >= (int)mission.size()) {
        return false;
    }
    au.nav_index = index;
    do_nav_wp(index);                           // AP_Mission::start_command -> ModeAuto::start_command
    au.nav_cmd_loaded = true;
    return true;
}

// AP_Mission.cpp:109-119 AP_Mission::start
static void mission_start()
{
    au.state = MissionState::RUNNING;
    au.nav_index = -1;
    au.nav_cmd_loaded = false;
    if (!mission_advance()) {
        mission_complete();
    }
}

// AP_Mission.cpp:310-345 AP_Mission::update (navigation commands)
static void mission_update()
{
    if (au.state != MissionState::RUNNING || mission.empty()) {
        return;
    }
    if (!au.nav_cmd_loaded || au.nav_index < 0) {
        if (!mission_advance()) {
            mission_complete();
            return;
        }
    } else if (verify_nav_wp()) {
        au.nav_cmd_loaded = false;
        if (!mission_advance()) {
            mission_complete();
            return;
        }
    }
}

// mode_auto.cpp:23-80 ModeAuto::init
static void auto_init()
{
    au.mode = SubMode::STARTING;
    wp_nav->wp_and_spline_init_m();
    au.waiting_to_start = true;
}

// mode_auto.cpp:1134-1153 ModeAuto::wp_run (also loiter_run, :1194-1198)
static void wp_run()
{
    motors->set_desired_spool_state(AP_Motors::DesiredSpoolState::THROTTLE_UNLIMITED);
    wp_nav->update_wpnav();
    pos_control->D_update_controller();
    attitude_control->input_thrust_vector_heading(pos_control->get_thrust_vector(), auto_yaw_get_heading());
}

// mode_auto.cpp:91-150 ModeAuto::run (the EKF origin is always known)
static void auto_run()
{
    if (au.waiting_to_start) {
        mission_start();
        au.waiting_to_start = false;
    } else {
        mission_update();
    }
    wp_run();                                   // STARTING, WP and LOITER all run the waypoint controller
}

// ---------------------------------------------------------------------------------------------
// One tick (Copter's fast loop, Copter.cpp:113-130, with read_AHRS before the flight mode)

static bool in_auto = false;

static void tick(const Sample &smp, float act[4])
{
    // AP_Scheduler::loop (AP_Scheduler.cpp:348-377): tick counter, loop time
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
    for (int i = 0; i < 4; i++) {
        act[i] = motors->actuator(i);
    }

    // Copter::read_AHRS: the sample, the view's update
    oracle_ahrs.sample.pos_ned = smp.pos;
    oracle_ahrs.sample.vel_ned = smp.vel;
    oracle_ahrs.sample.accel_ef = smp.accel_ef;
    oracle_ahrs.sample.quat = smp.quat;
    ahrs_view->update();

    // Copter::read_inertia
    pos_control->update_estimates(false);

    // on the first tick: Copter::set_mode(AUTO) -> ModeAuto::init, then the rate time constants (mode.cpp:465-469)
    if (!in_auto) {
        auto_init();
        attitude_control->set_roll_pitch_rate_tc(h.ACRO_RP_RATE_TC);
        attitude_control->set_yaw_rate_tc(h.PILOT_Y_RATE_TC);
        in_auto = true;
    }

    // Copter::update_flight_mode (mode.cpp:502-513): not landed; ModeAuto moves the vehicle on an EKF reset
    attitude_control->landed_gain_reduction(false);
    pos_control->set_reset_handling_method(AC_PosControl::EKFResetMethod::MoveVehicle);
    auto_run();
}

// ---------------------------------------------------------------------------------------------

static void usage()
{
    fprintf(stderr,
            "usage: copter_ref [--params FILE]... [--set \"NAME VALUE\"]... [--exact] [--trace] [--bits] [--print-params] [--bench]\n"
            "  the lock-step protocol of sim/PROTOCOL.md on standard input and output\n"
            "  --bench: read every input line first, then time the ticks alone (sim/BENCH.md); prints\n"
            "           \"ns ticks checksum\" with the elapsed nanoseconds and a checksum of the actuator bits\n");
}

int main(int argc, char **argv)
{
    std::vector<std::string> param_lines;
    bool print_params = false, exact = false, trace = false, bits = false, bench = false;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--params" && i + 1 < argc) {
            std::ifstream f(argv[++i]);
            if (!f) {
                fprintf(stderr, "copter_ref: cannot read %s\n", argv[i]);
                return 2;
            }
            std::string l;
            while (std::getline(f, l)) {
                param_lines.push_back(l);
            }
        } else if (a == "--set" && i + 1 < argc) {
            param_lines.push_back(argv[++i]);
        } else if (a == "--print-params") {
            print_params = true;
        } else if (a == "--exact") {
            exact = true;
        } else if (a == "--trace") {
            trace = true;
        } else if (a == "--bits") {
            bits = true;
        } else if (a == "--bench") {
            bench = true;
        } else {
            usage();
            return 2;
        }
    }

    // construction (zero-filled objects: operator new is calloc)
    motors = new RefMotors(oracle_scheduler.get_loop_rate_hz());
    ahrs_view = new AP_AHRS_View(oracle_ahrs, ROTATION_NONE);
    attitude_control = new AC_AttitudeControl_Multi(*ahrs_view, *motors);
    pos_control = new RefPosControl(*ahrs_view, *motors, *attitude_control);
    wp_nav = new AC_WPNav(*ahrs_view, *pos_control, *attitude_control);

    std::vector<ParamRef> params;
    collect_params(params, "ATC_", attitude_control, AC_AttitudeControl_Multi::var_info);
    collect_params(params, "PSC", pos_control, AC_PosControl::var_info);
    collect_params(params, "MOT_", motors, AP_MotorsMatrix::var_info);
    collect_params(params, "WP_", wp_nav, AC_WPNav::var_info);
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
    // run deviations from the code defaults (SITL's copter.parm:5-6, :71; MOT_BAT_VOLT_MAX's code default)
    set_by_name("ATC_RAT_YAW_P", 0.3f);
    set_by_name("ATC_RAT_YAW_I", 0.02f);
    set_by_name("MOT_HOVER_LEARN", 0);
    set_by_name("MOT_THST_HOVER", 0.39f);
    set_by_name("MOT_BAT_VOLT_MAX", 0.0f);
    // the built-in mission (sim/PROTOCOL.md)
    mission = {Vector3p(0, 0, -5), Vector3p(10, 0, -5), Vector3p(10, 10, -5)};
    bool mission_given = false;

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
        if (w.empty()) {
            continue;
        }
        if (w[0] == "mission.clear") {
            mission.clear();
            mission_given = true;
            continue;
        }
        if (w[0] == "waypoint") {
            if (w.size() < 4) {
                fprintf(stderr, "copter_ref: expected waypoint N E D: %s\n", line.c_str());
                return 2;
            }
            if (!mission_given) {
                mission.clear();
                mission_given = true;
            }
            mission.push_back(Vector3p(strtod(w[1].c_str(), nullptr), strtod(w[2].c_str(), nullptr), strtod(w[3].c_str(), nullptr)));
            continue;
        }
        if (w.size() != 2) {
            fprintf(stderr, "copter_ref: expected NAME VALUE: %s\n", line.c_str());
            return 2;
        }
        const float v = strtof(w[1].c_str(), nullptr);
        if (!set_by_name(w[0], v) && !set_harness_param(h, w[0], v)) {
            fprintf(stderr, "copter_ref: unknown parameter %s\n", w[0].c_str());
            return 2;
        }
    }

    if (print_params) {
        for (auto &p : params) {
            printf("%s %s\n", p.name.c_str(), exact_decimal(param_get(p)).c_str());
        }
        printf("WP_YAW_BEHAVIOR %d\nPILOT_Y_RATE_TC %s\nACRO_RP_RATE_TC %s\nrun.air_density_ratio %s\nrun.start_hover %d\n",
               h.WP_YAW_BEHAVIOR, exact_decimal(h.PILOT_Y_RATE_TC).c_str(), exact_decimal(h.ACRO_RP_RATE_TC).c_str(),
               exact_decimal(h.air_density_ratio).c_str(), h.start_hover);
        for (auto &wp : mission) {
            printf("waypoint %s %s %s\n", exact_decimal(wp.x).c_str(), exact_decimal(wp.y).c_str(), exact_decimal(wp.z).c_str());
        }
        return 0;
    }
    if (h.WP_YAW_BEHAVIOR < 0 || h.WP_YAW_BEHAVIOR > 2) {
        fprintf(stderr, "copter_ref: only WP_YAW_BEHAVIOR 0, 1 or 2 is mirrored\n");
        return 2;
    }
    if (mission.empty()) {
        fprintf(stderr, "copter_ref: empty mission\n");
        return 2;
    }

    // boot: AP_MotorsMatrix::init(QUAD, X) (radio.cpp:56), armed, interlocked, THROTTLE_UNLIMITED
    motors->init(AP_Motors::MOTOR_FRAME_QUAD, AP_Motors::MOTOR_FRAME_TYPE_X);
    motors->armed(true);
    motors->set_interlock(true);
    motors->set_desired_spool_state(AP_Motors::DesiredSpoolState::THROTTLE_UNLIMITED);
    motors->force_spool_state_throttle_unlimited();

    // takeover on the first sample: the view of the sample, relax, hover throttle
    auto takeover = [&](const Sample &smp) {
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
    };

    bool started = false;
    std::string line;
    if (bench) {
        // sim/BENCH.md: parse every line first, then time the ticks alone (no parsing, no printing)
        std::vector<Sample> samples;
        while (std::getline(std::cin, line)) {
            if (line.find_first_not_of(" \t\r\n") == std::string::npos) {
                continue;
            }
            Sample smp;
            if (!parse_sample(line, smp)) {
                fprintf(stderr, "copter_ref: bad input line: %s\n", line.c_str());
                return 2;
            }
            samples.push_back(smp);
        }
        uint64_t checksum = 0;
        const auto t0 = std::chrono::steady_clock::now();
        for (const Sample &smp : samples) {
            if (!started) {
                takeover(smp);
                started = true;
            }
            float act[4];
            tick(smp, act);
            for (int i = 0; i < 4; i++) {
                uint32_t b;
                memcpy(&b, &act[i], 4);
                checksum += b;
            }
        }
        const auto t1 = std::chrono::steady_clock::now();
        printf("%lld %zu %016llx\n", (long long)std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count(),
               samples.size(), (unsigned long long)checksum);
        return 0;
    }
    while (std::getline(std::cin, line)) {
        if (line.find_first_not_of(" \t\r\n") == std::string::npos) {
            continue;
        }
        Sample smp;
        if (!parse_sample(line, smp)) {
            fprintf(stderr, "copter_ref: bad input line: %s\n", line.c_str());
            puts(trace ? "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" : "0 0 0 0");
            fflush(stdout);
            continue;
        }
        if (!started) {
            takeover(smp);
            started = true;
        }
        float act[4];
        tick(smp, act);

        // output: the actuators, then with --trace the 18 numbers of the trace
        std::vector<double> vals = {act[0], act[1], act[2], act[3]};
        std::vector<std::string> hex = {bits32(act[0]), bits32(act[1]), bits32(act[2]), bits32(act[3])};
        if (trace) {
            const Vector3p &pd = pos_control->get_pos_desired_NED_m();
            const Vector3f &vd = pos_control->get_vel_desired_NED_ms();
            const Vector3f &ad = pos_control->accel_desired();
            const Vector3f tv = pos_control->get_thrust_vector();
            const Vector3f &eu = attitude_control->get_att_target_euler_rad();
            const Vector3f rb = attitude_control->rate_bf_targets();
            vals.insert(vals.end(), {pd.x, pd.y, pd.z});
            hex.insert(hex.end(), {bits64(pd.x), bits64(pd.y), bits64(pd.z)});
            const Vector3f *v3[] = {&vd, &ad, &tv, &eu, &rb};
            for (const Vector3f *v : v3) {
                vals.insert(vals.end(), {v->x, v->y, v->z});
                hex.insert(hex.end(), {bits32(v->x), bits32(v->y), bits32(v->z)});
            }
        }
        std::string out;
        for (size_t i = 0; i < vals.size(); i++) {
            out += (i ? " " : "") + (exact ? exact_decimal(vals[i]) : six_decimals(vals[i]));
        }
        if (bits) {
            out += " |";
            for (auto &x : hex) {
                out += " " + x;
            }
        }
        puts(out.c_str());
        fflush(stdout);
    }
    return 0;
}
