import Corpus.Test.UpdateAll
import Corpus.Code.Filter.Filter

/-!
# Edge evaluation of `AC_PID::update_all`'s value and fields (fourth increment, the open statement of OPEN.md)

The candidate: for finite `target` and `measurement`, the call returns `(P + D) + I` with `P`, `D` the `PD_max`-limited
`((E·kp)·m)·pd_scale`, `((D'·kd)·m)·pd_scale` (`m` the slew modifier, which the call leaves in `_pid_info.Dmod` at
`+188`), `I` the integrator `update_i` computes from the new error; and it leaves `_target`, `_error`, `_derivative`,
`_target_derivative` at the values below (two cases on the reset flag, the derivative on `is_positive(dt)`), and the
reset flag clear. Checked on the synthetic states of `Test/UpdateAll.lean` (reset flag set and clear, `dt` positive and
zero, `PD_max` active and not).
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge
open Corpus.Test.UpdateAll

namespace Corpus.Test.UpdateAllValue

def isPos (x : Binary32) : Bool := Id.run (Vehicle_lib.is_positive'float.pure' x)
def alpha (dt c : Binary32) : Binary32 := Corpus.Filter.lpAlpha dt c

/-- The expected fields and value, from the state `s` before the call. -/
def expect (s : PMem.Mem) (target meas dt : Binary32) (limit : Bool) (pd isc m : Binary32) :
    Binary32 × Binary32 × Binary32 × Binary32 × Binary32 × Binary32 :=
  let rst := ((PMem.ldBits (pid + 128) 0 1).run s).1 != 0
  let T0 := rd s (pid + 136); let E0 := rd s (pid + 140); let D0 := rd s (pid + 144); let TD0 := rd s (pid + 152)
  let T1 := if rst then target else T0 + alpha dt (rd s (pid + 24)) * (target - T0)
  let E1 := if rst then target - meas else E0 + alpha dt (rd s (pid + 28)) * ((T1 - meas) - E0)
  let D1 := if rst then B 0 else if isPos dt then D0 + alpha dt (rd s (pid + 32)) * ((E1 - E0) / dt - D0) else D0
  let TD1 := if rst then B 0 else if isPos dt then (T1 - T0) / dt else TD0
  let I := rd s (pid + 132); let K := rd s (pid + 4); let M := rd s (pid + 16)
  let I1 :=
    if (!Id.run (Vehicle_lib.is_zero.pure' K) && isPos dt) then
      (if (!limit || (isPos I && Id.run (Vehicle_lib.is_negative'float.pure' E1)) ||
          (Id.run (Vehicle_lib.is_negative'float.pure' I) && isPos E1)) then
        Id.run (Vehicle_lib.constrain_value_line'float.pure' (I + ((E1 * K) * isc) * dt) (-M) M 346)
      else I)
    else B 0
  let P0 := E1 * rd s pid * m * pd
  let Dd := D1 * rd s (pid + 8) * m * pd
  let pdmax := rd s (pid + 20)
  let (P, D) := if isPos pdmax && decide (Binary32.abs (P0 + Dd) > pdmax) then
      (P0 * (pdmax / Binary32.abs (P0 + Dd)), Dd * (pdmax / Binary32.abs (P0 + Dd))) else (P0, Dd)
  (T1, E1, D1, TD1, I1, P + D + I1)

def valCheck (kp ki kimax integ err : Binary32) (flags : UInt8) (pdmax target meas dt : Binary32) (limit : Bool)
    (pd : Binary32) : Bool :=
  let s := pidState kp ki kimax integ err flags pdmax
  let r := (Vehicle_lib.AC_PID.update_all pid target meas dt limit pd (B 0x3f800000)).run s
  let m := rd r.2 (pid + 188)
  let (T1, E1, D1, TD1, I1, ret) := expect s target meas dt limit pd (B 0x3f800000) m
  let rst' := ((PMem.ldBits (pid + 128) 0 1).run r.2).1
  bits r.1 == bits ret && bits (rd r.2 (pid + 136)) == bits T1 && bits (rd r.2 (pid + 140)) == bits E1 &&
    bits (rd r.2 (pid + 144)) == bits D1 && bits (rd r.2 (pid + 152)) == bits TD1 &&
    bits (rd r.2 (pid + 132)) == bits I1 && rst' == 0

def valFails : List String := Id.run do
  let mut out := []
  for ki in [B 0, B 0x3f800000] do
    for integ in [B 0, B 0x3f000000, B 0xbf800000] do
      for err in [B 0x3f800000, B 0xbf800000] do
        for flags in [(0 : UInt8), 1, 2, 3] do
          for pdmax in [B 0x3f000000, B 0, B 0x461c4000] do
            for target in [B 0x3f800000, B 0x42c80000, B 0xc2c80000] do
              for dt in [B 0x3c23d70a, B 0] do
                for limit in [false, true] do
                  for pd in [B 0x3f800000, B 0x40000000] do
                    if !valCheck (B 0x3f800000) ki (B 0x3f800000) integ err flags pdmax target (B 0x3dcccccd) dt
                        limit pd then
                      out := s!"{nameOf ki} {nameOf integ} {nameOf err} {flags} {nameOf pdmax} {nameOf target} {nameOf dt} {limit} {nameOf pd}" :: out
  return out

#guard valFails.isEmpty

end Corpus.Test.UpdateAllValue
