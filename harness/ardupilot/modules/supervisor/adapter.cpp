// adapter.cpp: the cut between the harness records and ArduCopter's vehicle code.
//
// The vehicle is the real `Copter copter` object of ArduCopter/Copter.cpp (a static, constructed
// at program start as in ArduPilot), on the HAL of stand_ins/stubs_hal.cpp. The objects of the
// other stages it holds are shadows (DESIGN.md): real headers, stand-in out-of-line methods
// (gen/out/shadow_*.cpp, stand_ins/stubs_*.cpp), state written here from the input record.
//
// init (first in this process): HAL reset (RAM storage zeroed: every parameter at its default),
//   clock 0, the parameter record applied as parameter defaults when AP_Param::load_all asks the
//   HAL for its command-line parameters (as SITL's --param), then AP_Vehicle::setup()
//   (load_parameters, scheduler, GCS, serial ports, Copter::init_ardupilot). A second init in the
//   same process re-executes the program (see reexec below): every static starts fresh, as at boot.
// step: clock = now_us/now_ms; shadows filled from the record; RC frame and ground-station bytes
//   handed to the HAL; Copter::loop() (AP_Scheduler with Copter's task table); the HAL's io
//   callbacks; outputs read back (arming and spool from the motors shadow, the command log, the
//   ground-station bytes).
#include "module_protocol.h"

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <mach-o/dyld.h>   // _NSGetExecutablePath: the path to re-execute

#include "Copter.h"
#include "supervisor_hal.h"
#include "supervisor_shadow.h"

// ---- access to Copter's private state the outputs report (explicit-instantiation rule, as the
// mixer adapter reaches AP_MotorsMatrix::_singleton)
bool &harness_copter_land_complete();
template <typename T, T M>
struct CopterAp {
    friend bool &harness_copter_land_complete() { return (copter.*M).land_complete; }
};
template struct CopterAp<decltype(&Copter::ap), &Copter::ap>;

bool &harness_motors_spoolup_block(AP_Motors &m);
template <typename T, T M>
struct MotorsSpoolupBlock {
    friend bool &harness_motors_spoolup_block(AP_Motors &m) { return m.*M; }
};
template struct MotorsSpoolupBlock<decltype(&AP_Motors::_spoolup_block), &AP_Motors::_spoolup_block>;

AP_Motors::SpoolState &harness_motors_spool_state(AP_Motors &m);
template <typename T, T M>
struct MotorsSpoolState {
    friend AP_Motors::SpoolState &harness_motors_spool_state(AP_Motors &m) { return m.*M; }
};
template struct MotorsSpoolState<decltype(&AP_Motors::_spool_state), &AP_Motors::_spool_state>;

// ---- parameters
struct ParamEntry {
    const char *name;
    size_t off;
    char kind;
};
static const ParamEntry param_table[] = {
#include "param_table.inc"
};
static Params cur_params;
static uint32_t params_applied;

static void apply_params()
{
    for (const ParamEntry &e : param_table) {
        const uint8_t *base = reinterpret_cast<const uint8_t *>(&cur_params) + e.off;
        float v = 0;
        switch (e.kind) {
        case 'f': memcpy(&v, base, 4); break;
        case 'u': { uint32_t x; memcpy(&x, base, 4); v = float(x); break; }
        case 'i': { int32_t x; memcpy(&x, base, 4); v = float(x); break; }
        case 'b': v = *base ? 1.0f : 0.0f; break;
        }
        char name[AP_MAX_NAME_SIZE + 1];
        size_t k = 0;
        for (; e.name[k] != 0 && k < AP_MAX_NAME_SIZE; k++) {
            name[k] = char(toupper((unsigned char)e.name[k]));
        }
        name[k] = 0;
        if (getenv("SUP_TRACE") != nullptr && params_applied == 0) {
            fprintf(stderr, "init: %s = %g\n", name, v);
        }
        if (!AP_Param::set_default_by_name(name, v)) {
            fprintf(stderr, "supervisor: no parameter %s\n", name);
            abort();
        }
    }
    params_applied++;
}

// ---- the trace (SUP_TRACE=1 prints each tick's command log to stderr)
static bool trace;
static uint32_t tick;

static void trace_commands()
{
    for (uint32_t k = 0; k < sup_cmd_count; k++) {
        const SupCmd &c = sup_cmd_log[k];
        const char *stage = "?";
        const char *method = sup_cmd_method(c.id, &stage);
        fprintf(stderr, "tick %u cmd %s %s(", tick, stage, method ? method : "?");
        for (uint32_t a = 0; a < c.nargs; a++) {
            if (c.arg_is_float[a]) {
                float f;
                memcpy(&f, &c.arg[a], 4);
                fprintf(stderr, "%s%g", a ? ", " : "", f);
            } else {
                fprintf(stderr, "%s%d", a ? ", " : "", int32_t(c.arg[a]));
            }
        }
        fprintf(stderr, ")\n");
    }
}

// ---- a second init re-executes the program with the parameter record in the environment; the
// new process's static constructor (below) runs module_init from it and sends the 'K' that the
// protocol's main loop would have sent, then the main loop continues with the next request
static bool initialized_once;
static const char *self_path;

static void reexec(const Params &p)
{
    char hex[2 * sizeof(Params) + 1];
    const uint8_t *b = reinterpret_cast<const uint8_t *>(&p);
    for (size_t k = 0; k < sizeof(Params); k++) {
        snprintf(&hex[2 * k], 3, "%02x", b[k]);
    }
    setenv("SUPERVISOR_REINIT", hex, 1);
    fflush(stdout);
    char *const argv[] = {const_cast<char *>(self_path), nullptr};
    execv(self_path, argv);
    fprintf(stderr, "supervisor: re-exec failed\n");
    abort();
}

static void boot(const Params &p);
static void reset_held();
static bool poison_mode;
static uint32_t poisoned_reads;
static void fill_shadows(const Input &in);
uint32_t harness_params_readonly_init();
void harness_param_scan(const uint8_t *b, size_t n);
extern uint32_t harness_param_set_refused;

static void find_self()
{
    static char buf[4096];
    uint32_t size = sizeof buf;
    if (_NSGetExecutablePath(buf, &size) == 0) {
        self_path = buf;
    }
}

void module_init(const Params &p)
{
    if (initialized_once) {
        reexec(p);
    }
    boot(p);
}

static void boot(const Params &p)
{
    initialized_once = true;
    find_self();
    trace = getenv("SUP_TRACE") != nullptr;
    poison_mode = getenv("SUP_POISON") != nullptr;
    poisoned_reads = 0;
    reset_held();
    harness_hal_reset();
    harness_set_clock(0, 0);
    cur_params = p;
    harness_cmdline_params = apply_params;
    sup_cmd_count = 0;
    // the shadows' state before the first step: an empty record (estimator not initialised, no
    // position), so that boot-time calls (init_ardupilot's set_mode, e.g. LAND's init asking
    // position_ok) read a defined state; controllers allocated in setup are filled from step 1
    {
        static Input zero;
        memset(&zero, 0, sizeof zero);
        fill_shadows(zero);
    }
    // the motors shadow exists from Copter::allocate_motors (in setup); its frame strings are
    // needed by the banner sent at the first ground-station connection, after setup
    copter.setup();
    // what HAL_SITL::run does after the sketch's setup (HAL_SITL_Class.cpp)
    hal.scheduler->set_system_initialized();
    harness_mixer_boot();
    // decision 3: other stages' parameters read-only from the ground station
    const uint32_t nro = harness_params_readonly_init();
    // SITL's simulator object is empty here (stubs_sitl.cpp): SIM_BARO_COUNT's default
    if (AP::sitl() != nullptr) {
        AP::sitl()->baro_count.set(1);
    }
    harness_run_io();
    if (trace) {
        fprintf(stderr, "init: parameter record applied %u time(s); %u parameters of other "
                "stages read-only\n", params_applied, nro);
        trace_commands();
    }
    sup_cmd_count = 0;
}

// A re-executed process: its static constructor (below; adapter.o is linked last, so it runs after
// every other static constructor, `copter` included) boots from the environment's record, sends
// the 'K' that answers the init request, and serves the rest of the session with the same loop
// as module_protocol.h's main(), already initialized; it exits instead of returning to main().
static void serve_initialized()
{
    using namespace harness_protocol;
    static uint8_t ibuf[HARNESS_INPUT_BYTES + 1];
    static uint8_t obuf[HARNESS_OUTPUT_BYTES + 1];
    static uint8_t pbuf[HARNESS_PARAMS_BYTES + 1];
    const uint8_t ok = 'K', err = 'E';
    write_bytes(&ok, 1);
    fflush(stdout);
    for (;;) {
        const int op = getchar();
        if (op == EOF) {
            exit(0);
        }
        switch (op) {
        case 'D':
            describe();
            break;
        case 'I': {
            if (!read_exact(pbuf, HARNESS_PARAMS_BYTES)) {
                exit(1);
            }
            Params p;
            harness_unpack_params(pbuf, p);
            module_init(p);   // re-executes again
            write_bytes(&ok, 1);
            break;
        }
        case 'S': {
            if (!read_exact(ibuf, HARNESS_INPUT_BYTES)) {
                exit(1);
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
            exit(0);
        default:
            write_bytes(&err, 1);
            fflush(stdout);
            exit(2);
        }
        fflush(stdout);
    }
}

struct ReinitAtStart {
    ReinitAtStart()
    {
        const char *hex = getenv("SUPERVISOR_REINIT");
        if (hex == nullptr) {
            return;
        }
        if (strlen(hex) != 2 * sizeof(Params)) {
            fprintf(stderr, "supervisor: bad SUPERVISOR_REINIT\n");
            exit(1);
        }
        Params p;
        uint8_t *b = reinterpret_cast<uint8_t *>(&p);
        for (size_t k = 0; k < sizeof(Params); k++) {
            unsigned v;
            sscanf(&hex[2 * k], "%2x", &v);
            b[k] = uint8_t(v);
        }
        unsetenv("SUPERVISOR_REINIT");
        boot(p);
        serve_initialized();
    }
};
static ReinitAtStart reinit_at_start;

// DESIGN.md 2: a method called twice in one tick with different arguments, unless it is an
// idempotent setter (the last call wins, as in ArduCopter when nothing reads between the calls)
static bool idempotent(const char *m)
{
    static const char *const setters[] = {"_set_max_speed_accel_m", "_set_correction_speed_accel_m",
                                          "::set_speed_", "::set_desired_spool_state",
                                          "::set_throttle_out"};
    for (const char *k : setters) {
        if (m != nullptr && strstr(m, k) != nullptr) {
            return true;
        }
    }
    return false;
}

static uint32_t count_conflicts()
{
    uint32_t n = 0;
    for (uint32_t i = 0; i < sup_cmd_count; i++) {
        for (uint32_t j = i + 1; j < sup_cmd_count; j++) {
            const SupCmd &a = sup_cmd_log[i], &b = sup_cmd_log[j];
            if (a.id != b.id || idempotent(sup_cmd_method(a.id, nullptr))) {
                continue;
            }
            if (a.nargs != b.nargs || memcmp(a.arg, b.arg, a.nargs * sizeof(uint32_t)) != 0) {
                n++;
                if (trace) {
                    fprintf(stderr, "tick %u conflict %s\n", tick, sup_cmd_method(a.id, nullptr));
                }
            }
        }
    }
    return n;
}

void harness_sensors_fill(const Input &in);
uint32_t harness_params_readonly_init();
void harness_param_scan(const uint8_t *b, size_t n);
extern uint32_t harness_param_set_refused;
void harness_attitude_before();
// the poison trap (supervisor_shadow.h): generated per class in gen/out/shadow_*.cpp
void harness_poison_AC_PosControl(AC_PosControl &o);
void harness_poison_AC_AttitudeControl(AC_AttitudeControl &o);
void harness_poison_AC_AttitudeControl_Multi(AC_AttitudeControl_Multi &o);
void harness_poison_AC_WPNav(AC_WPNav &o);
void harness_poison_AC_Loiter(AC_Loiter &o);
void harness_poison_AC_Circle(AC_Circle &o);
void harness_poison_AP_Motors(AP_Motors &o);
void harness_poison_AP_MotorsMulticopter(AP_MotorsMulticopter &o);
void harness_poison_AP_MotorsMatrix(AP_MotorsMatrix &o);
HARNESS_ADDR(Copter, attitude_control)
HARNESS_ADDR(Copter, pos_control)
HARNESS_ADDR(Copter, wp_nav)
HARNESS_ADDR(Copter, loiter_nav)
HARNESS_ADDR(Copter, circle_nav)

static void poison_shadows()
{
    if (AC_PosControl *p = HARNESS_REF(AC_PosControl *, copter, Copter, pos_control)) {
        harness_poison_AC_PosControl(*p);
    }
    if (AC_AttitudeControl *a = HARNESS_REF(AC_AttitudeControl *, copter, Copter, attitude_control)) {
        harness_poison_AC_AttitudeControl(*a);
        harness_poison_AC_AttitudeControl_Multi(static_cast<AC_AttitudeControl_Multi &>(*a));
    }
    if (AC_WPNav *w = HARNESS_REF(AC_WPNav *, copter, Copter, wp_nav)) {
        harness_poison_AC_WPNav(*w);
    }
    if (AC_Loiter *l = HARNESS_REF(AC_Loiter *, copter, Copter, loiter_nav)) {
        harness_poison_AC_Loiter(*l);
    }
    if (AC_Circle *c = HARNESS_REF(AC_Circle *, copter, Copter, circle_nav)) {
        harness_poison_AC_Circle(*c);
    }
    if (AP_Motors *m = AP::motors()) {
        harness_poison_AP_Motors(*m);
        harness_poison_AP_MotorsMulticopter(static_cast<AP_MotorsMulticopter &>(*m));
        harness_poison_AP_MotorsMatrix(static_cast<AP_MotorsMatrix &>(*m));
    }
}

struct OutF32 {
    const char *name;
    size_t off;
};
static const OutF32 out_f32[] = {
#include "output_f32.inc"
};

static void scan_poison(const Output &out)
{
    const uint8_t *b = reinterpret_cast<const uint8_t *>(&out);
    for (const OutF32 &f : out_f32) {
        float v;
        memcpy(&v, b + f.off, 4);
        if (isnan(v)) {
            poisoned_reads++;
            if (trace || sup_strict()) {
                fprintf(stderr, "tick %u poisoned value reached output %s\n", tick, f.name);
            }
            if (sup_strict()) {
                abort();
            }
        }
    }
}
void harness_attitude_after();
void harness_guidance_after();
void harness_mixer_after();

static void fill_shadows(const Input &in)
{
    harness_estimator_fill(in);
    harness_attitude_fill(in);
    // test knob for the poison trap: SUP_SKIP_POSITION_FILL=1 leaves the position shadow unfilled
    static const bool skip_pos = getenv("SUP_SKIP_POSITION_FILL") != nullptr;
    if (!skip_pos) {
        harness_position_fill(in);
    }
    harness_guidance_fill(in);
    harness_mixer_fill(in);
    harness_sensors_fill(in);

    AP_Motors *m = AP::motors();
    if (m == nullptr) {   // before Copter::allocate_motors
        return;
    }
    // mixer outputs of this tick (stage-owned shadow state)
    harness_motors_spool_state(*m) = AP_Motors::SpoolState(in.spool_state);
    m->limit.roll = in.limit_roll;
    m->limit.pitch = in.limit_pitch;
    m->limit.yaw = in.limit_yaw;
    m->limit.throttle_lower = in.limit_throttle_lower;
    m->limit.throttle_upper = in.limit_throttle_upper;
    harness_motors_spoolup_block(*m) = in.spoolup_block;
}

// ---- inline setters of supervisor-owned position state: a change is the command
HARNESS_ADDR(AC_PosControl, _vibe_comp_enabled)
static bool vibe_comp_last;

static void position_after()
{
    AC_PosControl *pc = AC_PosControl::get_singleton();
    if (pc == nullptr) {
        return;
    }
    const bool v = HARNESS_REF(bool, *pc, AC_PosControl, _vibe_comp_enabled);
    if (v != vibe_comp_last) {
        sup_cmd_begin_named("AC_PosControl::set_vibe_comp", "position");
        sup_arg(v);
        sup_cmd_end();
        vibe_comp_last = v;
    }
}

// ---- the command fields (gen/out/cmd_emit.inc from commands.txt)
#include "cmd_emit.inc"

static uint32_t first_seq(const char *prefix)
{
    for (uint32_t k = 0; k < sup_cmd_count; k++) {
        const char *m = sup_cmd_method(sup_cmd_log[k].id, nullptr);
        if (m != nullptr && strncmp(m, prefix, strlen(prefix)) == 0) {
            return k + 1;
        }
    }
    return 0;
}

// the argument fields held between calls, starting at the values the position stage's own
// constructor uses (AC_PosControl.h: POSCONTROL_SPEED_MS 5, POSCONTROL_SPEED_UP_MS 2.5,
// POSCONTROL_SPEED_DOWN_MS 1.5, POSCONTROL_ACCEL_NE_MSS 1, POSCONTROL_ACCEL_D_MSS 2.5), so that
// a field read before its first call holds a value the controller would accept
static Output held;
static void reset_held()
{
    memset(&held, 0, sizeof held);
    held.cmd_position_NE_set_max_speed_accel_m_speed = 5.0f;
    held.cmd_position_NE_set_max_speed_accel_m_accel = 1.0f;
    held.cmd_position_NE_set_correction_speed_accel_m_speed = 5.0f;
    held.cmd_position_NE_set_correction_speed_accel_m_accel = 1.0f;
    held.cmd_position_D_set_max_speed_accel_m_down = 1.5f;
    held.cmd_position_D_set_max_speed_accel_m_up = 2.5f;
    held.cmd_position_D_set_max_speed_accel_m_accel = 2.5f;
    held.cmd_position_D_set_correction_speed_accel_m_down = 1.5f;
    held.cmd_position_D_set_correction_speed_accel_m_up = 2.5f;
    held.cmd_position_D_set_correction_speed_accel_m_accel = 2.5f;
}

static void emit_commands(Output &out)
{
    uint32_t unmapped = 0;
    for (uint32_t k = 0; k < sup_cmd_count; k++) {
        const char *method = sup_cmd_method(sup_cmd_log[k].id, nullptr);
        if (method == nullptr || !sup_emit_one(method, sup_cmd_log[k], k + 1, out)) {
            unmapped++;
            if (trace) {
                fprintf(stderr, "tick %u unmapped %s\n", tick, method ? method : "?");
            }
        }
    }
    out.cmd_unmapped = unmapped + sup_cmd_overflow;
    sup_hold_args(out, held);
    held = out;
    // the attitude stage's two order flags, derived from the call order (its documented use)
    const uint32_t input_seq = first_seq("AC_AttitudeControl::input_");
    out.cmd_attitude_set_throttle_out_before_input =
        out.cmd_attitude_set_throttle_out && input_seq != 0 &&
        out.cmd_attitude_set_throttle_out_seq < input_seq;
    out.cmd_attitude_pos_throttle_after_input =
        out.cmd_position_D_update_controller && input_seq != 0 &&
        out.cmd_position_D_update_controller_seq > input_seq;
}

void module_step(const Input &in, Output &out)
{
    tick++;
    harness_set_clock(in.now_us, in.now_ms);
    sup_cmd_count = 0;
    sup_cmd_overflow = 0;
    if (poison_mode) {
        poison_shadows();
    }
    fill_shadows(in);
    harness_attitude_before();
    AP_Motors *m = AP::motors();
    const bool block_before = harness_motors_spoolup_block(*m);

    const uint16_t rc[8] = {uint16_t(in.rc_1), uint16_t(in.rc_2), uint16_t(in.rc_3),
                            uint16_t(in.rc_4), uint16_t(in.rc_5), uint16_t(in.rc_6),
                            uint16_t(in.rc_7), uint16_t(in.rc_8)};
    harness_rcin_set(rc, in.rc_1 == 0 ? 0 : 8, in.rc_fresh);

    uint8_t rx[4 * 64];
    const uint32_t nrx = in.gcs_rx_len > sizeof rx ? sizeof rx : in.gcs_rx_len;
    for (uint32_t k = 0; k < nrx; k++) {
        rx[k] = uint8_t((&in.gcs_rx_w00)[k / 4] >> (8 * (k % 4)));
    }
    out.gcs_rx_dropped = uint32_t(nrx - harness_gcs_push_rx(rx, nrx));
    harness_param_scan(rx, nrx);

    // the estimator's status text of this tick ("EKF3 IMU0 is using GPS", ...): sent by this
    // vehicle's GCS, as ArduCopter's one GCS sends the texts of every library
    static uint32_t est_text_seen;
    if (in.est_text_seq != est_text_seen && in.est_text_len > 0) {
        char text[51] = {};
        const uint32_t n = in.est_text_len > 50 ? 50 : in.est_text_len;
        for (uint32_t k = 0; k < n; k++) {
            text[k] = char(uint8_t((&in.est_text_w00)[k / 4] >> (8 * (k % 4))));
        }
        gcs().send_text(MAV_SEVERITY(in.est_text_severity), "%s", text);
    }
    est_text_seen = in.est_text_seq;

    copter.loop();
    harness_run_io();
    harness_attitude_after();
    harness_guidance_after();
    harness_mixer_after();
    position_after();

    out.armed = m->armed();
    out.interlock = m->get_interlock();
    out.spool_desired = uint32_t(m->get_desired_spool_state());
    out.clear_spoolup_block = block_before && !harness_motors_spoolup_block(*m);
    out.mode = static_cast<AP_Vehicle &>(copter).get_mode();
    out.land_complete = harness_copter_land_complete();

    uint32_t h = 2166136261u;
    for (uint32_t k = 0; k < sup_cmd_count; k++) {
        const SupCmd &c = sup_cmd_log[k];
        h = (h ^ c.id) * 16777619u;
        for (uint32_t a = 0; a < c.nargs; a++) {
            h = (h ^ c.arg[a]) * 16777619u;
        }
    }
    out.cmd_log_count = sup_cmd_count + sup_cmd_overflow;
    out.cmd_log_hash = h;
    out.sup_cmd_conflicts = count_conflicts();
    emit_commands(out);
    out.likely_flying = static_cast<AP_Vehicle &>(copter).get_likely_flying();

    uint8_t tx[4 * 64];
    const size_t ntx = harness_gcs_pull_tx(tx, sizeof tx);
    memset(tx + ntx, 0, sizeof tx - ntx);
    out.gcs_tx_len = uint32_t(ntx);
    for (uint32_t w = 0; w < 64; w++) {
        (&out.gcs_tx_w00)[w] = uint32_t(tx[4 * w]) | (uint32_t(tx[4 * w + 1]) << 8) |
                               (uint32_t(tx[4 * w + 2]) << 16) | (uint32_t(tx[4 * w + 3]) << 24);
    }
    out.sup_internal_errors = AP::internalerror().count();
    out.sup_internal_error_bits = AP::internalerror().errors();
    out.sup_internal_error_line = AP::internalerror().last_error_line();
    out.unanswered = sup_unanswered_count;
    out.param_set_refused = harness_param_set_refused;
    if (poison_mode) {
        scan_poison(out);
    }
    out.poisoned_reads = poisoned_reads;
    if (trace) {
        trace_commands();
    }
}
