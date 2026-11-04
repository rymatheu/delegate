import AP_Math.AP_Math
import Contracts.Float32Clip

/-!
# `constrain_float` of the AP_Math port meets the clip contract

`AP_Math.constrain_float` (`AP_Math/AP_Math.lean`, the port of `AP_Math.cpp:282-304`) is the
definition `Contracts.Float32Clip.constrain_float` verbatim (`constrain_float_eq`), so the
theorems of `Contracts.Float32Clip` apply to it.
-/

namespace Contracts.Float32ClipAP

theorem constrain_float_eq : AP_Math.constrain_float = Float32Clip.constrain_float := rfl

/-- `AP_Math.constrain_float` is finite and in `[low, high]` for every input, NaN and infinities
included, for finite `low ≤ high` whose sum does not overflow. -/
theorem constrain_float_spec {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hsum : |lo.toReal + hi.toReal| ≤ Float.Model.UnpackedFloat.maxFinite32)
    (x : Float32) :
    (AP_Math.constrain_float x lo hi).IsFinite ∧ lo.toReal ≤ (AP_Math.constrain_float x lo hi).toReal ∧
      (AP_Math.constrain_float x lo hi).toReal ≤ hi.toReal :=
  Float32Clip.constrain_float_spec hlo hhi hle hsum x

/-- On a finite input, `AP_Math.constrain_float` is the real clamp of its value. -/
theorem constrain_float_toReal {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hx : x.IsFinite) :
    (AP_Math.constrain_float x lo hi).toReal = max lo.toReal (min hi.toReal x.toReal) :=
  Float32Clip.constrain_float_toReal hlo hhi hle hx

end Contracts.Float32ClipAP
