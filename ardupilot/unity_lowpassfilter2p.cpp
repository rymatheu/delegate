// Unity translation unit for cpp2lean: ArduPilot's LowPassFilter2p.cpp (first: it defines
// AP_INLINE_VECTOR_OPS before including AP_Math.h) and vector2.cpp (Vector2's operators, which
// vector2.h does not inline). The C++ side of the difftest compiles them separately.
#include <Filter/LowPassFilter2p.cpp>
#include <AP_Math/vector2.cpp>
