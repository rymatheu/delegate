// stubs_mixer.cpp: hand-written stand-ins of the mixer's (AP_Motors) methods whose effect on the
// shadow's own state the vehicle code reads back through inline getters. Each body is the real
// one (cited), followed by the command record the generated stand-ins would have made; the
// mixer applies the same call from its input fields (armed, spool_desired), so the two copies of
// the state are computed by the same code from the same inputs.
//
//   AP_Motors::armed(bool)                     AP_Motors_Class.cpp: sets _armed (motors->armed()
//                                              is read everywhere), AP_Notify::flags.armed, and on
//                                              disarm calls save_params_on_disarm (virtual; its
//                                              stand-in records a command)
//   AP_MotorsMulticopter::set_desired_spool_state
//                                              AP_MotorsMulticopter.cpp:570-581: sets
//                                              _spool_desired, SHUT_DOWN unless armed and interlock
#include <AP_Motors/AP_MotorsMulticopter.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_HAL/AP_HAL.h>
extern const AP_HAL::HAL &hal;
#include "supervisor_shadow.h"

void AP_Motors::armed(bool arm)
{
    if (_armed != arm) {
        _armed = arm;
        AP_Notify::flags.armed = arm;
        if (!arm) {
            save_params_on_disarm();
        }
    }
    sup_cmd_begin(SUP_CMD_HAND_MOTORS_ARMED);
    sup_arg(arm);
    sup_cmd_end();
}

void AP_MotorsMulticopter::set_desired_spool_state(DesiredSpoolState desired)
{
    sup_cmd_begin(SUP_CMD_HAND_MOTORS_SET_DESIRED_SPOOL_STATE);
    sup_arg(desired);
    sup_cmd_end();
    if (!armed() || !get_interlock()) {
        _spool_desired = DesiredSpoolState::SHUT_DOWN;
        return;
    }
    _spool_desired = desired;
}

// Frame facts the vehicle code asks the mixer for. The mixer module is configured once, as quad X
// with SERVOn_FUNCTION = Motor n (ardupilot/modules/mixer/adapter.cpp), and the shadow's frame set-up
// (AP_MotorsMatrix::init, the mixer's own work) is not run here, so these are that configuration
// written out, not computed:
//   AP_MotorsMatrix::get_motor_mask   motors 1..4 on outputs 1..4: 0x0F (AP_MotorsMatrix.cpp
//                                     builds it from motor_enabled[] and rc_map_mask)
#include <AP_Motors/AP_MotorsMatrix.h>
uint32_t AP_MotorsMatrix::get_motor_mask()
{
    return 0x0F;
}

// The frame strings AP_MotorsMatrix::setup_motors sets for quad X (AP_MotorsMatrix.cpp:579, 594);
// set on the shadow at boot by harness_mixer_boot (the shadow's init is the mixer's work, not run)
HARNESS_ADDR(AP_Motors, _mav_type)
typedef const char *harness_cstr;
HARNESS_PRIVATE(AP_MotorsMatrix, harness_cstr, _frame_class_string)
HARNESS_PRIVATE(AP_MotorsMatrix, harness_cstr, _frame_type_string)
void harness_mixer_boot()
{
    AP_MotorsMatrix *m = AP_MotorsMatrix::get_singleton();
    if (m != nullptr) {
        HARNESS_FIELD(*m, AP_MotorsMatrix, _frame_class_string) = "QUAD";
        HARNESS_FIELD(*m, AP_MotorsMatrix, _frame_type_string) = "X";
        HARNESS_REF(MAV_TYPE, *m, AP_Motors, _mav_type) = MAV_TYPE_QUADROTOR;
    }
}

// AP_MotorsMulticopter::arming_checks (AP_MotorsMulticopter.cpp): the real parameter checks
// (MOT_SPIN_MIN, MOT_SPIN_ARM, MOT_PWM_MIN/MAX via check_mot_pwm_params, copied by gen/), on the
// shadow's parameters. Its other two checks are answered from the mixer module's fixed set-up,
// not computed: AP_Motors::arming_checks' initialised_ok() (the mixer always initializes quad X)
// and the SERVOn_FUNCTION check (the mixer maps motor n to output n): both pass. PLACEHOLDER
// until the mixer outputs its own arming-check verdict.
#define AP_MOTORS_PARAM_PREFIX "MOT_"   // AP_MotorsMulticopter.cpp:30 (Copter)
bool AP_MotorsMulticopter::arming_checks(size_t buflen, char *buffer) const
{
    if (thr_lin.get_spin_min() > 0.3) {
        hal.util->snprintf(buffer, buflen, "%sSPIN_MIN too high %.2f > 0.3", AP_MOTORS_PARAM_PREFIX,
                           thr_lin.get_spin_min());
        return false;
    }
    if (_spin_arm > thr_lin.get_spin_min()) {
        hal.util->snprintf(buffer, buflen, "%sSPIN_ARM > %sSPIN_MIN", AP_MOTORS_PARAM_PREFIX,
                           AP_MOTORS_PARAM_PREFIX);
        return false;
    }
    if (!check_mot_pwm_params()) {
        hal.util->snprintf(buffer, buflen, "Check %sPWM_MIN and %sPWM_MAX", AP_MOTORS_PARAM_PREFIX,
                           AP_MOTORS_PARAM_PREFIX);
        return false;
    }
    return true;
}

// harness_mixer_fill: the mixer's outputs of this tick into the fields the inline getters read
//   _throttle_hover                        throttle_hover (get_throttle_hover; learned by the
//                                          mixer through cmd_mixer_update_throttle_hover)
//   _spool_state, limit, _spoolup_block   spool_state, limit_*, spoolup_block (adapter.cpp)
//   _throttle_filter                       throttle_filtered (reset to it: get_throttle)
//   _throttle_out                          throttle_out (get_throttle_out)
// set once at boot from the mixer's fixed frame (AP_MotorsMatrix::setup_motors for quad X):
//   _mav_type = MAV_TYPE_QUADROTOR (get_frame_mav_type, the HEARTBEAT type)
// get_lost_motor (AP_MotorsMatrix, _motor_lost_index) is read only with thrust boost, which
// the mixer does not report: the shadow keeps 0 and _thrust_boost false (supervisor-owned via
// set_thrust_boost, not emitted: the mixer has no input for it).
#include "module_records.h"
HARNESS_ADDR(AP_Motors, _throttle_filter)
HARNESS_ADDR(AP_Motors, _throttle_out)
HARNESS_ADDR(AP_MotorsMulticopter, _throttle_hover)
void harness_mixer_fill(const Input &in)
{
    AP_Motors *m = AP::motors();
    if (m == nullptr) {
        return;
    }
    HARNESS_REF(LowPassFilterFloat, *m, AP_Motors, _throttle_filter).reset(in.throttle_filtered);
    HARNESS_REF(float, *m, AP_Motors, _throttle_out) = in.throttle_out;
    // the hover throttle the mixer learns (update_throttle_hover is the mixer's command now)
    HARNESS_REF(AP_Float, *static_cast<AP_MotorsMulticopter *>(m), AP_MotorsMulticopter,
                _throttle_hover).set(in.throttle_hover);
}

// set_thrust_boost is an inline setter of supervisor-owned state (crash_check.cpp:172): a change
// during the tick is the mixer's command set_thrust_boost(enable)
HARNESS_ADDR(AP_Motors, _thrust_boost)
static bool thrust_boost_last;
void harness_mixer_after()
{
    AP_Motors *m = AP::motors();
    if (m == nullptr) {
        return;
    }
    const bool b = HARNESS_REF(bool, *m, AP_Motors, _thrust_boost);
    if (b != thrust_boost_last) {
        sup_cmd_begin_named("AP_Motors::set_thrust_boost", "mixer");
        sup_arg(b);
        sup_cmd_end();
        thrust_boost_last = b;
    }
}
