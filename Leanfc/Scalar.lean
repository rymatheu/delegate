import FloatLib.Floats

/-!
# Scalar

The controller's number type `R` (FloatLib's IEEE binary32) and the few scalar helpers every
module uses. In pyfc this is `numpy.float32` (`F` in every file) plus `np.clip`.
Every operation here is `+ - * /`, negation, `ExecFloat.sqrt`, `min`, `max` or a comparison.
-/

open FloatLib.Floats

/-- The controller scalar: IEEE 754 binary32, round to nearest even. -/
abbrev R := Binary32

namespace R

/-- Binary64 to binary32, round to nearest (setup and logging only, never inside a tick). -/
def ofFloat (x : Float) : R := ExecFloat.Binary.ofFloat x

/-- Binary32 to binary64 (exact). -/
def toFloat (x : R) : Float := ExecFloat.Binary.toFloat x

def sqrt (x : R) : R := ExecFloat.sqrt x

def abs (x : R) : R := if x < 0 then -x else x

/-- `np.clip(x, lo, hi)` = `min (max x lo) hi`. -/
def clamp (lo hi x : R) : R := min (max x lo) hi

end R

/-- Standard gravity, m/s², along +down in NED. -/
def gravity : R := 9.80665
