// stubs_motors.cpp: what the motors stand-in's class reaches for, all of it on the mixer's paths.
//
// The motors object is a real AP_MotorsMatrix (adapter.cpp), constructed but never initialised or
// output: the attitude controller only calls its inline setters and getters. Everything below is
// referenced from the motors' output, arming, motor-test and logging code (kept by its vtable),
// which is the mixer module's and never runs here.
//
//   symbol                                   why it is outside the stage, and what stands in
//   SRV_Channels::set_output_pwm,            the servo-output library (motor PWM, pass-through
//   set_output_scaled, set_aux_channel_      outputs, channel set-up, arming checks). Abort; the
//   default, get_output_channel_mask,        two static members are storage only.
//   find_channel, set_range, set_angle,
//   _singleton, emergency_stop
//   AP::battery(), AP_BattMonitor::voltage,  the battery monitor (current limit, voltage
//   voltage_resting_estimate, current_amps   compensation). Abort.
//   AP::logger(), AP_Logger::WriteBlock      logging. Abort.
#include <SRV_Channel/SRV_Channel.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_Logger/AP_Logger.h>

void SRV_Channels::set_output_pwm(SRV_Channel::Function function, uint16_t value)
{
    unreachable("SRV_Channels::set_output_pwm");
}

void SRV_Channels::set_output_scaled(SRV_Channel::Function function, float value)
{
    unreachable("SRV_Channels::set_output_scaled");
}

bool SRV_Channels::set_aux_channel_default(SRV_Channel::Function function, uint8_t channel)
{
    unreachable("SRV_Channels::set_aux_channel_default");
}

uint32_t SRV_Channels::get_output_channel_mask(SRV_Channel::Function function)
{
    unreachable("SRV_Channels::get_output_channel_mask");
}

bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan)
{
    unreachable("SRV_Channels::find_channel");
}

void SRV_Channels::set_range(SRV_Channel::Function function, uint16_t range)
{
    unreachable("SRV_Channels::set_range");
}

void SRV_Channels::set_angle(SRV_Channel::Function function, uint16_t angle)
{
    unreachable("SRV_Channels::set_angle");
}

SRV_Channels *SRV_Channels::_singleton;
bool SRV_Channels::emergency_stop;

namespace AP {
AP_BattMonitor &battery()
{
    unreachable("AP::battery");
}
AP_Logger &logger()
{
    unreachable("AP::logger");
}
}

float AP_BattMonitor::voltage(uint8_t instance) const
{
    unreachable("AP_BattMonitor::voltage");
}

float AP_BattMonitor::voltage_resting_estimate(uint8_t instance) const
{
    unreachable("AP_BattMonitor::voltage_resting_estimate");
}

bool AP_BattMonitor::current_amps(float &current, const uint8_t instance) const
{
    unreachable("AP_BattMonitor::current_amps");
}

void AP_Logger::WriteBlock(const void *pBuffer, uint16_t size)
{
    unreachable("AP_Logger::WriteBlock");
}
