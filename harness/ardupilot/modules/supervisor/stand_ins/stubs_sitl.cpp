// stubs_sitl.cpp: SITL's simulator objects that AP_Vehicle holds on the SITL board.
//
// AP_Vehicle has a `SITL::SIM sitl` member (AP_SIM_ENABLED, which the SITL board requires); its
// constructor (inline, SITL.h) registers the singleton AP::sitl() returns and sets its parameter
// defaults from tables in libraries/SITL/*.cpp; its sub-simulators (buzzer, ESCs, generators,
// ship, tether, payload) are members too. The simulator is the module plant_sim, so none of this
// runs here:
//   SITL::SIM::var_info and its sub-tables, the sub-simulators' var_info   empty: no SIM_*
//                                                                          parameters are served
//   the sub-simulators' constructors                                     no-ops
//   SITL::SIM::simstate_send, sim_state_send                             no-ops (SIMSTATE and
//                                                                          SIM_STATE messages are
//                                                                          not sent)
//   SITL::SIM::_singleton, AP::sitl()                                    the vehicle's member
// The values vehicle-side code reads from it: AP_Arming::barometer_checks skips its checks if
// baro_count is 0 (AP_Arming.cpp:400), and AP_Scheduler::loop reads loop_delay. With empty
// tables these stay 0, so the adapter sets baro_count to its default 1 (SIM_BARO_COUNT,
// SITL.cpp) after construction.
#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>

namespace SITL {

const AP_Param::GroupInfo SIM::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_info2[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_info3[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_gps[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_mag[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_ins[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::var_sonar[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::GPSParms::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::ServoParams::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM::ViconParms::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo SIM_Precland::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo Gripper_EPM::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo Gripper_Servo::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo Parachute::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo Sprayer::var_info[] = { AP_GROUPEND };
const AP_Param::GroupInfo ToneAlarm::var_info[] = { AP_GROUPEND };

SIM *SIM::_singleton;

Buzzer::Buzzer() {}
FETtecOneWireESC::FETtecOneWireESC() {}
IntelligentEnergy24::IntelligentEnergy24() {}
Loweheiser::Loweheiser() {}
RichenPower::RichenPower() {}
ShipSim::ShipSim() {}
SlungPayloadSim::SlungPayloadSim() {}
TetherSim::TetherSim() {}
Volz::Volz() {}

void SIM::simstate_send(mavlink_channel_t chan) const {}
void SIM::sim_state_send(mavlink_channel_t chan) const {}

}  // namespace SITL

namespace AP {
SITL::SIM *sitl()
{
    return SITL::SIM::get_singleton();
}
}

// SITL's serial-device base and the one serial sub-simulator held by value (SIM_SerialDevice.h,
// SIM_IntelligentEnergy24.h): constructors and the key functions that carry their vtables
#include <SITL/SIM_SerialDevice.h>
#include <SITL/SIM_IntelligentEnergy24.h>
namespace SITL {
SerialDevice::SerialDevice(uint16_t tx_bufsize, uint16_t rx_bufsize) {}
ssize_t SerialDevice::write_to_autopilot(const char *buffer, size_t size) const { return -1; }
void IntelligentEnergy24::update(const struct sitl_input &input) {}
}
