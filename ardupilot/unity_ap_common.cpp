// Unity translation unit for cpp2lean: ArduPilot's AP_Common/Location.cpp and the AP_Math sources it
// calls into; the C++ side of the difftest compiles them separately.
#include <AP_Common/Location.cpp>
#include <AP_Math/location.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Common/Bitmask.h>

// Bitmask<N> at the sizes of the vehicle's classes (NUM_SERVO_CHANNELS, MSG_LAST,
// SRV_Channel::k_nr_aux_servo_functions, RC_Channel::AUX_FUNCTION_MAX and twice it): explicit
// instantiations, so that the AST holds the specializations. Nothing else is added.
template class Bitmask<32>;
template class Bitmask<102>;
template class Bitmask<190>;
template class Bitmask<317>;
template class Bitmask<634>;
