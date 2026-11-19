// adapter.cpp: the cut between the harness records and one real ArduPilot AC_PID.
//
// init builds a fresh AC_PID and sets every one of its AP_Param members from the parameter record
// (the feed-forward gains and notch-filter indices, which do not enter update_all's result, to 0).
// step makes one call of AC_PID::update_all, exactly as ArduCopter's rate controller does
// (AC_AttitudeControl_Multi::rate_controller_run), and reads the state the contract mentions.
#include "module_protocol.h"

#include <new>
#include <string.h>

#include <AC_PID/AC_PID.h>

// the cut, defined in stubs.cpp
extern uint32_t harness_clock_ms;
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();

// ArduCopter's controllers live in statically allocated objects, so their storage starts zeroed;
// AC_PID's constructor leaves several members (the integrator, the filter states, the slew
// limiter's state, the notch-filter pointers) to that zeroing. A fresh object is built the same way.
alignas(AC_PID) static unsigned char pid_storage[sizeof(AC_PID)];
static AC_PID *pid;

void module_init(const Params &p)
{
    memset(pid_storage, 0, sizeof pid_storage);
    harness_reset_internal_errors();
    // the constructor's defaults only feed AP_Param's default loader (cut); srtau = 1.0 is Copter's
    pid = new (pid_storage) AC_PID(0, 0, 0, 0, 0, 0, 0, 0, 0, 1.0f, 0);
    // set as the parameter system stores a value: no sign correction (set_imax would apply fabsf)
    pid->kP().set(p.kp);
    pid->kI().set(p.ki);
    pid->kD().set(p.kd);
    pid->ff().set(0.0f);
    pid->kIMAX().set(p.kimax);
    pid->kPDMAX().set(p.kpdmax);
    pid->filt_T_hz().set(p.filt_T_hz);
    pid->filt_E_hz().set(p.filt_E_hz);
    pid->filt_D_hz().set(p.filt_D_hz);
    pid->slew_limit().set(p.slew_max);
    pid->kDff().set(0.0f);
    // NTF and NEF (notch filter indices) are zero after the zeroed storage; set_notch_sample_rate
    // is not called, so the notch filters stay disabled
}

// AC_ATTITUDE_RATE_RELAX_TC (AC_AttitudeControl.h:27), the time constant
// AC_AttitudeControl::reset_rate_controller_I_terms_smoothly passes to relax_integrator; copied
// here so that the module does not compile the attitude controller's header
static const float rate_relax_tc = 0.16f;

void module_step(const Input &in, Output &out)
{
    harness_clock_ms = in.now_ms;   // AP_HAL::millis(), read by the slew limiter
    // the attitude controller's calls on this PID since the previous update_all, in the order
    // relax_attitude_controllers makes them (reset_filter, then reset_I, AC_AttitudeControl.cpp:
    // 263-277), then reset_rate_controller_I_terms_smoothly's relax_integrator (:283-285). In
    // ArduCopter they run after the rate controller of the previous tick (update_flight_mode)
    // and nothing touches the PID in between, so applying them here, before update_all, is the
    // same sequence of calls. relax_integrator uses this step's dt where ArduCopter uses the
    // attitude controller's _dt_s of the previous tick: equal when the loop time is steady.
    if (in.reset_filter) {
        pid->reset_filter();
    }
    if (in.reset_i) {
        pid->reset_I();
    }
    if (in.relax_i) {
        pid->relax_integrator(0.0f, in.dt, rate_relax_tc);
    }
    out.command = pid->update_all(in.target, in.measurement, in.dt, in.limit, in.pd_scale, in.i_scale);
    out.integrator = pid->get_i();
    out.p_term = pid->get_p();
    out.d_term = pid->get_d();
    out.dmod = pid->get_pid_info().Dmod;
    out.pd_limit = pid->get_pid_info().PD_limit;
    out.internal_errors = harness_internal_error_count();
}
