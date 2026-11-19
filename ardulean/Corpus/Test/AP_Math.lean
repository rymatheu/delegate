import ArduLean.Vehicle
import Corpus.Test.Edge

/-!
# Edge evaluation of the AP_Math candidates (Corpus/PLAN.md, rule 6)

Each candidate statement of `STATEMENTS-tier0.md`, as a `Bool` on concrete inputs, is checked here on the edge inputs
(`Corpus.Edge.inputs`, all pairs or triples) and on a pseudo-random sample of words. `#guard` makes the build fail if a
candidate that is proved in `Corpus/Code/` fails on an input; the findings (`FINDINGS.md`) are checked as `#guard`s
that their witnesses really falsify the naive statement.
-/

open FloatLib.Floats (Binary32 Binary64)
open Vehicle_lib Corpus.Edge

namespace Corpus.Test.AP_Math

def B (w : UInt32) : Binary32 := Binary32.ofBits w
def eps : Binary32 := B 0x34000000
def nan? (x : Binary32) : Bool := Binary32.isNaN x
def fin? (x : Binary32) : Bool := Binary32.isFinite x
def le (a b : Binary32) : Bool := decide (a ≤ b)
def lt (a b : Binary32) : Bool := decide (a < b)
/-- the same bits -/
def same (a b : Binary32) : Bool := Binary32.toBits a == Binary32.toBits b
/-- the same value: both NaN, or `==` (so `-0` and `+0` agree) -/
def sameV (a b : Binary32) : Bool := (nan? a && nan? b) || a == b

-- the code functions as `Bool`/`Binary32` functions
def isZero (x : Binary32) : Bool := Id.run (is_zero.pure' x)
def isPos (x : Binary32) : Bool := Id.run (is_positive'float.pure' x)
def isNeg (x : Binary32) : Bool := Id.run (is_negative'float.pure' x)
def isEq (x y : Binary32) : Bool := Id.run (is_equal'float_float.pure' x y)
def sq (x : Binary32) : Binary32 := Id.run (sq.pure' x)
def norm (x y : Binary32) : Binary32 := Id.run (norm.pure' x y)
def radians (x : Binary32) : Binary32 := Id.run (radians.pure' x)
def degrees (x : Binary32) : Binary32 := Id.run (degrees.pure' x)
def cdToRad (x : Binary32) : Binary32 := Id.run (cd_to_rad.pure' x)
def constrain (a l h : Binary32) : Binary32 := Id.run (constrain_value_line'float.pure' a l h 0)
def safeSqrt (x : Binary32) : Binary32 := Id.run (safe_sqrt'float.pure' x)
def safeAsin (x : Binary32) : Binary32 := Id.run (safe_asin'float.pure' x)
def wrap2PI (x : Binary32) : Binary32 := Id.run (wrap_2PI.pure' x)
def wrapPI (x : Binary32) : Binary32 := Id.run (wrap_PI'float.pure' x)
def expo (x e : Binary32) : Binary32 := Id.run (input_expo.pure' x e)
def invSqrt (o p d : Binary32) : Binary32 := Id.run (inv_sqrt_controller.pure' o p d)
def sqrtAccel (e rc rs p s : Binary32) : Binary32 := Id.run (sqrt_controller_accel.pure' e rc rs p s)

def pi : Binary32 := B 0x40490fdb
def twoPi : Binary32 := B 0x40c90fdb
def wide : List Binary32 := inputs ++ sample 3000

def failsW₁ (p : Binary32 → Bool) : List String := (wide.filter fun x => !p x).map nameOf |>.take 8

/-! ## is_zero, is_positive, is_negative, is_equal -/

#guard fails₁ (fun x => isZero x == (lt (-eps) x && lt x eps)) == []
#guard failsW₁ (fun x => isZero x == (lt (-eps) x && lt x eps)) == []
#guard fails₁ (fun x => isPos x == le eps x) == []
#guard fails₁ (fun x => isNeg x == le x (-eps)) == []
#guard failsW₁ (fun x => isNeg x == le x (-eps)) == []
#guard fails₁ (fun x => !(isZero x && (isPos x || isNeg x))) == []
#guard fails₁ (fun x => !(isPos x && isNeg x)) == []
#guard fails₁ (fun x => (isZero x || isPos x || isNeg x) == !nan? x) == []
#guard fails₁ (fun x => !nan? x || (!isZero x && !isPos x && !isNeg x)) == []
#guard fails₂ (fun a b => isEq a b == isEq b a) == []
#guard fails₂ (fun a b => isEq a b == isZero (a - b)) == []
#guard fails₁ (fun a => isEq a a == fin? a) == []

/-! ## sq, norm -/

#guard fails₁ (fun x => nan? x || le 0 (sq x)) == []
#guard fails₁ (fun x => nan? (sq x) == nan? x) == []
#guard fails₁ (fun x => sameV (sq (-x)) (sq x)) == []
#guard fails₂ (fun a b => nan? a || nan? b || (le 0 (norm a b) && !nan? (norm a b))) == []
#guard fails₂ (fun a b => sameV (norm a b) (norm b a)) == []
#guard fails₂ (fun a b => sameV (norm (-a) b) (norm a b)) == []
-- finding: `|a| ≤ norm a b` fails when `a*a` underflows
-- (witness: a = the smallest subnormal, b = 0: a*a = 0, norm = 0 < a)
#guard !le (Binary32.abs (B 0x00000001)) (norm (B 0x00000001) (B 0)) && same (norm (B 0x00000001) (B 0)) (B 0)

/-! ## radians, degrees, cd_to_rad -/

#guard fails₁ (fun x => sameV (radians (-x)) (-(radians x))) == []
#guard fails₁ (fun x => sameV (degrees (-x)) (-(degrees x))) == []
#guard fails₁ (fun x => sameV (cdToRad (-x)) (-(cdToRad x))) == []
#guard fails₂ (fun x y => !le x y || le (radians x) (radians y)) == []
#guard fails₂ (fun x y => !le x y || le (degrees x) (degrees y)) == []
#guard fails₂ (fun x y => !le x y || le (cdToRad x) (cdToRad y)) == []
#guard fails₁ (fun x => nan? (radians x) == nan? x) == []
#guard fails₁ (fun x => !le 0 x || le 0 (radians x)) == []
-- finding: the sign is not kept strictly: radians (-minsub) = -0
#guard same (radians (B 0x80000001)) (B 0x80000000)

/-! ## constrain_value_line (float) -/

#guard (fails₃ fun a l h => !le l h || nan? a || (le l (constrain a l h) && le (constrain a l h) h)).isEmpty
#guard (fails₃ fun a l h => !le l a || !le a h || same (constrain a l h) a).isEmpty
#guard (fails₃ fun a l h => nan? a || same (constrain a l h) a || same (constrain a l h) l ||
  same (constrain a l h) h).isEmpty
#guard (fails₃ fun a l h => !le l h || nan? a || sameV (constrain (constrain a l h) l h) (constrain a l h)).isEmpty
#guard (fails₃ fun a l h => !le l h || !nan? a || !fin? (l + h) ||
  (le l (constrain a l h) && le (constrain a l h) h)).isEmpty
-- findings: a NaN `amt` with `low + high` overflowing or NaN leaves `[low, high]`
#guard same (constrain (B 0x7fc00000) (B 0x7f7fffff) (B 0x7f7fffff)) (B 0x7f800000)
#guard nan? (constrain (B 0x7fc00000) (B 0xff800000) (B 0x7f800000))

/-! ## safe_sqrt, safe_asin -/

#guard failsW₁ (fun x => !nan? (safeSqrt x)) == []
#guard failsW₁ (fun x => le 0 (safeSqrt x)) == []
#guard failsW₁ (fun x => !le 0 x || same (safeSqrt x) (Binary32.sqrt x)) == []
#guard failsW₁ (fun x => le 0 x || same (safeSqrt x) (B 0)) == []
#guard failsW₁ (fun x => !nan? (safeAsin x)) == []
#guard failsW₁ (fun x => le (B 0xbfc90fdb) (safeAsin x) && le (safeAsin x) (B 0x3fc90fdb)) == []
#guard failsW₁ (fun x => !le (B 0x3f800000) x || same (safeAsin x) (B 0x3fc90fdb)) == []
-- the premise `AsinfRange` on the edge inputs and the sample
#guard failsW₁ (fun v => !(lt (B 0xbf800000) v && lt v (B 0x3f800000)) ||
  (!nan? (Musl.asinf.asinf v) && le (B 0xbfc90fdb) (Musl.asinf.asinf v) &&
    le (Musl.asinf.asinf v) (B 0x3fc90fdb))) == []

/-! ## wrap_2PI, wrap_PI -/

-- the premise `FmodfRange` on the edge inputs and the sample
#guard failsW₁ (fun r => !fin? r || (fin? (Musl.fmodf.fmodf r twoPi) && lt (B 0xc0c90fdb) (Musl.fmodf.fmodf r twoPi) &&
  lt (Musl.fmodf.fmodf r twoPi) twoPi)) == []
#guard failsW₁ (fun x => !fin? x || (fin? (wrap2PI x) && le 0 (wrap2PI x) && le (wrap2PI x) twoPi)) == []
#guard failsW₁ (fun x => !fin? x || (fin? (wrapPI x) && le (-pi) (wrapPI x) && le (wrapPI x) pi)) == []
#guard failsW₁ (fun x => fin? x || nan? (wrap2PI x)) == []
#guard failsW₁ (fun x => !(le 0 x && le x pi) || same (wrapPI x) x) == []
-- findings: `wrap_2PI` reaches `M_2PI` (so `[0, 2π)` is false), is not idempotent, and `wrap_PI` is not the
-- identity on `[-π, 0)`
#guard same (wrap2PI (B 0x80000001)) twoPi
#guard same (wrap2PI (B 0xb4000000)) twoPi
#guard same (wrap2PI (wrap2PI (B 0xb4000000))) (B 0)
#guard !same (wrapPI (B 0xbf7fffff)) (B 0xbf7fffff) && !same (wrapPI (B 0x80000001)) (B 0x80000001)

/-! ## input_expo -/

#guard (fails₂ fun x e => !fin? e || (le (B 0xbf800000) (expo x e) && le (expo x e) (B 0x3f800000))).isEmpty
#guard (fails₂ fun x e => sameV (expo (-x) e) (-(expo x e))).isEmpty
#guard (fails₂ fun x e => !le (B 0x3f733333) e || sameV (expo x e) (constrain x (B 0xbf800000) (B 0x3f800000))).isEmpty
-- finding: not monotone for a large negative `expo`
#guard le (B 0x3f070ba2) (B 0x3f206aa9) && !le (expo (B 0x3f070ba2) (B 0xcbe42a8e)) (expo (B 0x3f206aa9) (B 0xcbe42a8e))
-- finding: `expo = -∞` gives a NaN (`(1 - expo) * 0`)
#guard nan? (expo (B 0) (B 0xff800000))

/-! ## inv_sqrt_controller, sqrt_controller_accel -/

-- finding: with `p < 0` the acceleration does not oppose `rate_state`
#guard same (sqrtAccel (B 0xc0000000) (B 0xc0000000) (B 0xc0000000) (B 0xc0000000) (B 0xc0000000)) (B 0xc0800000)
-- finding: finite inputs, NaN out: `output² / (2 D_max)` is `∞ / ∞` for `output = D_max = FLT_MAX`, `p = 0`
#guard nan? (invSqrt (B 0x7f7fffff) (B 0) (B 0x7f7fffff))
-- finding: with `p < 0` the result is not odd in `output` (`output = ±0`, `p = -1`, `D_max = 1`)
#guard !sameV (invSqrt (B 0x80000000) (B 0xbf800000) (B 0x3f800000)) (-(invSqrt (B 0) (B 0xbf800000) (B 0x3f800000)))

/-! ## constrain_int16 -/

def ci (a l h : Int16) : Int16 := Id.run (constrain_int16.pure' a l h)
#guard (fails16₃ fun a l h => !(l ≤ h) || (l ≤ ci a l h && ci a l h ≤ h)).isEmpty
#guard (fails16₃ fun a l h => !(l ≤ a && a ≤ h) || ci a l h == a).isEmpty
#guard (fails16₃ fun a l h => ci a l h == (if a < l then l else if h < a then h else a)).isEmpty
-- finding: with `low > high` the result is `low` below `low`, else `high`: not idempotent
#guard ci (ci (-32768) (-32767) (-32768)) (-32767) (-32768) != ci (-32768) (-32767) (-32768)

/-! ## Second increment: the closed entries and new findings -/

-- `is_equal_comm`, `is_equal_self` (already above); `sq_nonneg_of_not_isNaN`, `norm_nonneg_of_not_isNaN`
#guard fails₁ (fun x => nan? x || (!nan? (sq x) && le 0 (sq x))) == []
#guard fails₂ (fun a b => nan? a || nan? b || (!nan? (norm a b) && le 0 (norm a b))) == []
-- `radians_odd` etc. as words on numbers; `_isNaN`
#guard fails₁ (fun x => nan? x || same (radians (-x)) (-(radians x))) == []
#guard fails₁ (fun x => nan? x || same (degrees (-x)) (-(degrees x))) == []
#guard fails₁ (fun x => nan? x || same (cdToRad (-x)) (-(cdToRad x))) == []
#guard fails₁ (fun x => nan? (degrees x) == nan? x && nan? (cdToRad x) == nan? x) == []
-- `constrain_float_odd` (bounds `±1`, `±FLT_MAX`)
#guard fails₁ (fun x => nan? x || same (constrain (-x) (B 0xbf800000) (B 0x3f800000))
  (-(constrain x (B 0xbf800000) (B 0x3f800000)))) == []
#guard fails₁ (fun x => nan? x || same (constrain (-x) (B 0xff7fffff) (B 0x7f7fffff))
  (-(constrain x (B 0xff7fffff) (B 0x7f7fffff)))) == []
-- `input_expo_odd` (as words, or both NaN), `input_expo_zero`
#guard (fails₂ fun x e => nan? x || same (expo (-x) e) (-(expo x e)) || (nan? (expo (-x) e) && nan? (expo x e))).isEmpty
#guard fails₁ (fun e => !fin? e || (!nan? (expo (B 0) e) && expo (B 0) e == B 0)) == []
-- `inv_sqrt_controller_odd`: `is_positive p` and `|output| ≥ ε`
#guard (fails₃ fun o p d => !(isPos p && le eps (Binary32.abs o)) || same (invSqrt (-o) p d) (-(invSqrt o p d)) ||
  (nan? (invSqrt (-o) p d) && nan? (invSqrt o p d))).isEmpty
-- finding F14: not odd for `0 < p < ε` (`is_zero p` selects `output² / (2 D_max)`)
#guard lt (B 0) (B 0x00000001) && !sameV (invSqrt (B 0xbf800000) (B 0x00000001) (B 0x3f800000))
  (-(invSqrt (B 0x3f800000) (B 0x00000001) (B 0x3f800000)))
-- finding F15: not odd for `0 < |output| < ε` outside the linear region (`is_positive` is false for both signs):
-- `output = 0.9 ε` (`0x33e66666`), `p = 2`, `D_max = ε`
#guard isPos (B 0x40000000) && !sameV (invSqrt (B 0xb3e66666) (B 0x40000000) eps)
  (-(invSqrt (B 0x33e66666) (B 0x40000000) eps))
-- `sqrt_controller_accel_not_isNaN`, `sqrt_controller_accel_opposes_nonneg` (a reduced grid: the full one takes 40 s)
def accelVals : List Binary32 := [B 0, B 0x80000000, B 0x3f800000, B 0xbf800000, B 0x34000000, B 0xb4000000,
  B 0x7f7fffff, B 0xff7fffff, B 0x00000001]
#guard Id.run do
  let mut ok := true
  for e in [B 0, B 0x7f7fffff] do
    for rc in accelVals do
      for rs in accelVals do
        for p in [B 0, B 0x00000001, B 0x3f800000, B 0x7f7fffff, B 0xbf800000] do
          for s in [B 0, B 0x3f800000, B 0x7f7fffff, B 0x34000000, B 0xbf800000] do
            let r := sqrtAccel e rc rs p s
            if nan? r then ok := false
            if le 0 p && ((le 0 rs && !le r 0) || (le rs 0 && !le 0 r)) then ok := false
  return ok

/-! ## `calc_lowpass_alpha_dt`, `MIN` (callees of `update_all`) -/

def alpha (dt c : Binary32) : Binary32 := ((calc_lowpass_alpha_dt dt c).run (default : PMem.Mem)).1
#guard fails₂ (fun dt c => same (alpha dt c)
  (if isNeg dt || isNeg c then B 0x3f800000 else if isZero c then B 0x3f800000 else if isZero dt then B 0
    else dt / (dt + B 0x3f800000 / (B 0x40c90fdb * c)))) == []

end Corpus.Test.AP_Math
