import ArduLean.Runtime.CFloat
import ArduLean.Estimator.World_3

/-!
ArduPilot `libraries/AP_Math`, part 3 of 3. Sources: `libraries/AP_Math/AP_Math.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `void fill_nanf(double * f, uint16_t count)`, `AP_Math/AP_Math.cpp:463-483`. -/
def fill_nanf_double_uint16_t (w : World) (f : Array Binary64) (f'o : Nat) (count : UInt16) : World × (Array Binary64) := Id.run do
  let mut w := w
  let mut f := f
  pure ()  -- C++ `static bool created`: a World field (a static local)
  pure ()  -- C++ `static double many_nanfs[2048]`: a World field (a static local)
  if !w.fill_nanf'created then
    for i' in [0:2048] do
      let i : UInt16 := Nat.toUInt16 i'
      w := { w with fill_nanf'created := true }
      w := { w with fill_nanf'many_nanfs := w.fill_nanf'many_nanfs.set! (UInt16.toNat i) (Binary64.ofBits 0x7ff4000000000000) }
  if UInt16.toUInt64 count > (2048 : UInt64) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  for t'1 in [0:((UInt16.toUInt64 count).toNat)] do  -- C++ `memcpy` of k elements
    f := f.set! (f'o + t'1) (w.fill_nanf'many_nanfs[0 + t'1]!)
  return (w, f)

end Estimator_lib
