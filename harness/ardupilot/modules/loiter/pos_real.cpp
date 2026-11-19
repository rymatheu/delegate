// pos_real.cpp: the real position controller source, for the one function AC_Loiter computes with
// that belongs to the position stage and returns its value within the call.
//
// AC_Loiter::set_pilot_desired_acceleration_rad converts lean angles to an acceleration with
// AC_PosControl::lean_angles_rad_to_accel_NED_mss (AC_Loiter.cpp:180, 198; defined at
// AC_PosControl.cpp:1200-1215). It depends on this tick's pilot sticks, so it cannot be a signal of
// the position stage (which runs later in the tick), and it must not be rewritten here. So the
// real AC_PosControl.cpp is compiled in this unit, unmodified, under another class name: the
// macro below renames the identifier AC_PosControl throughout this translation unit (the .cpp and
// every header it includes), so its definitions become members of AC_PosControl_Real. The class
// AC_PosControl that AC_Loiter.cpp holds a reference to keeps its own name in the other units, and
// its out-of-line methods there are the hand-over stand-ins of stubs_posctl.cpp (the calls this
// stage hands to the position stage). Without the rename the two sets of definitions would clash.
//
// Of AC_PosControl_Real only lean_angles_rad_to_accel_NED_mss is reachable: it reads no member
// (its result depends only on its argument), and it is called on an object in zeroed storage that
// is never constructed. Everything else of AC_PosControl.cpp is unreferenced and removed by the
// linker (-dead_strip); `nm` on the executable lists what is left (adapter.cpp's header).
#define AC_PosControl AC_PosControl_Real
#include <AC_AttitudeControl/AC_PosControl.cpp>
#undef AC_PosControl

#include "cut.h"

alignas(AC_PosControl_Real) static unsigned char pos_real_storage[sizeof(AC_PosControl_Real)];

Vector3f harness_real_lean_angles_rad_to_accel_NED_mss(const Vector3f &att_target_euler_rad)
{
    const AC_PosControl_Real &pc = *reinterpret_cast<const AC_PosControl_Real *>(pos_real_storage);
    return pc.lean_angles_rad_to_accel_NED_mss(att_target_euler_rad);
}
