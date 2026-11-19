import ArduLean.Runtime.Boundary
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_SurfaceDistance`. Sources: `libraries/AP_SurfaceDistance/AP_SurfaceDistance.h`, `libraries/AP_SurfaceDistance/AP_SurfaceDistance.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_SurfaceDistance::enabled_and_healthy : bool () const`, `AP_SurfaceDistance.cpp:194-197`. -/
def AP_SurfaceDistance.enabled_and_healthy (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 8)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldB (this + 9)
    sc'3 := t'2
  return sc'3

/-- C++ `AP_SurfaceDistance::data_stale : bool ()`, `AP_SurfaceDistance.cpp:188-192`. -/
def AP_SurfaceDistance.data_stale (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 60)
  return (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) > (Int32.toUInt32 ((1000 : Int32)))))

/-- `AP_SurfaceDistance.SurfDistParameters.SurfDistParameters` as a pure function of its arguments (it reads and writes no memory). -/
def AP_SurfaceDistance.SurfDistParameters.SurfDistParameters.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 0)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 4)
  return ()

/-- C++ `AP_SurfaceDistance::SurfDistParameters::SurfDistParameters : void () noexcept(false)`, `AP_SurfaceDistance.h:?-?`. -/
def AP_SurfaceDistance.SurfDistParameters.SurfDistParameters (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_SurfaceDistance.SurfDistParameters.SurfDistParameters.pure' this)

/-- C++ `AP_SurfaceDistance::AP_SurfaceDistance : void (Rotation, uint8_t, SurfDistParameters *)`, `AP_SurfaceDistance.h:17-21`. -/
def AP_SurfaceDistance.AP_SurfaceDistance.body (fp : UInt64) (this : UInt64) (rot : UInt8) (i : UInt8) (surf_dist_params : UInt64) : PMem.M Unit := do
  let mut rot := rot
  let mut i := i
  let mut surf_dist_params := surf_dist_params
  PMem.stU64 (this + 0) surf_dist_params
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))
  LowPassFilter'float.LowPassFilter'2 (this + 20) (fp + 0)
  HALSITL.Semaphore.Semaphore (this + 48)
  PMem.stU8 (this + 56) rot
  PMem.stU8 (this + 57) i
  return ()

def AP_SurfaceDistance.AP_SurfaceDistance (this : UInt64) (rot : UInt8) (i : UInt8) (surf_dist_params : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_SurfaceDistance.AP_SurfaceDistance.body fp this rot i surf_dist_params
  PMem.leave fp
  return r

end Vehicle_lib
