import ArduLean.Vehicle
import Corpus.Test.Edge

/-!
# Edge evaluation of the `AC_PID.update_i` candidates (Corpus/PLAN.md, rule 6)

`update_i` run on concrete states: a fresh memory with an `AC_PID` at `0x20000` (heap) and the stack at `0x30000`,
fields set from the edge values; checked: the stack pointer is restored, `_kimax` is unchanged, and the bound
`-kimax ≤ integrator ≤ kimax` is preserved whenever `kimax` is finite and `≥ 0`. (Not states of the recorded flights.)
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge

namespace Corpus.Test.AC_PID

def B (w : UInt32) : Binary32 := Binary32.ofBits w
def le (a b : Binary32) : Bool := decide (a ≤ b)

def obj : UInt64 := 0x20000

/-- The state with the four fields set. -/
def state (ki kimax integ err : Binary32) : PMem.Mem :=
  let s := PMem.fresh 0x40000 0x30000 0x20000 ByteArray.empty
  let act : PMem.M Unit := do
    PMem.stF32 (obj + 4) ki; PMem.stF32 (obj + 16) kimax; PMem.stF32 (obj + 132) integ; PMem.stF32 (obj + 140) err
  (act.run s).2

def vals : List Binary32 := [B 0, B 0x80000000, B 0x3f800000, B 0xbf800000, B 0x34000000, B 0x7f7fffff,
  B 0xff7fffff, B 0x7f800000, B 0x7fc00000, B 0x3dcccccd, B 0x42c80000]

/-- The checks on one run; `true` when they hold. -/
def check (ki kimax integ err dt isc : Binary32) (limit : Bool) : Bool :=
  let s := state ki kimax integ err
  let s' := ((Vehicle_lib.AC_PID.update_i obj dt limit isc).run s).2
  let rd (st : PMem.Mem) (a : UInt64) : Binary32 := ((PMem.ldF32 a).run st).1
  let M := rd s (obj + 16)
  let I := rd s (obj + 132)
  let I' := rd s' (obj + 132)
  let bound := !(Binary32.isFinite M && le (B 0) M && le (-M) I && le I M) || (le (-M) I' && le I' M)
  -- `update_i_integrator_exact`: one of the three values, the third exactly the clamped update
  let E := rd s (obj + 140)
  let K := rd s (obj + 4)
  let upd := Id.run (Vehicle_lib.constrain_value_line'float.pure' (I + ((E * K) * isc) * dt) (-M) M 346)
  let exact := Binary32.toBits I' == Binary32.toBits I || Binary32.toBits I' == 0 ||
    Binary32.toBits I' == Binary32.toBits upd
  s'.sp == s.sp && Binary32.toBits (rd s' (obj + 16)) == Binary32.toBits M && bound && exact

def fails : List String := Id.run do
  let mut out := []
  for ki in vals do
    for kimax in vals do
      for integ in vals do
        for err in [B 0x3f800000, B 0xbf800000, B 0x7fc00000] do
          for dt in [B 0x3c23d70a, B 0, B 0x7fc00000] do
            for isc in [B 0x3f800000, B 0x7f800000] do
              for limit in [false, true] do
                if !check ki kimax integ err dt isc limit then
                  out := s!"{nameOf ki} {nameOf kimax} {nameOf integ} {nameOf err} {nameOf dt} {nameOf isc} {limit}" :: out
  return out

#guard fails.isEmpty

end Corpus.Test.AC_PID
