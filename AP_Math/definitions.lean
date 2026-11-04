import AP_Math.ftype

/-!
# `AP_Math/definitions.h`, constants

Mirrors `libraries/AP_Math/definitions.h:8-45` at ArduPilot 802db19de1. ArduPilot compiles with
`-fsingle-precision-constant` (gcc) or `-cl-single-precision-constant` (clang)
(`Tools/ardupilotwaf/boards.py:403`, `:512`, `:521`), so `M_PI` is the `float` literal
`0x40490fdb` and every derived constant is a `float` expression, folded with round-to-nearest; the
Lean definitions are the same `Float32` expressions.

Left out: the GPS/WGS84 doubles, unit conversions and time constants (`:36-130`), unused by the
cascade.
-/

namespace AP_Math

/-- `M_PI` (`definitions.h:11`). -/
def M_PI : Float32 := 3.141592653589793238462643383279502884
/-- `M_PI_2` = `M_PI / 2` (`:16`). -/
def M_PI_2 : Float32 := M_PI / 2
/-- `M_2PI` = `M_PI * 2` (`:20`). -/
def M_2PI : Float32 := M_PI * 2
/-- `CDEG_TO_RAD` (`:31`). -/
def CDEG_TO_RAD : Float32 := M_PI / 18000.0
/-- `RAD_TO_CDEG` (`:32`). -/
def RAD_TO_CDEG : Float32 := 18000.0 / M_PI
/-- `DEG_TO_RAD` (`:33`). -/
def DEG_TO_RAD : Float32 := M_PI / 180.0
/-- `RAD_TO_DEG` (`:34`). -/
def RAD_TO_DEG : Float32 := 180.0 / M_PI
/-- `GRAVITY_MSS` (`:45`). -/
def GRAVITY_MSS : Float32 := 9.80665

end AP_Math
