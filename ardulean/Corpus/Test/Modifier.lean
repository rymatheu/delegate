import Corpus.Test.UpdateAll
import Corpus.Code.Filter.SlewLimiter

/-!
# Edge evaluation of `SlewLimiter::modifier`'s value (fourth increment)

The candidate `modifier_eq`: on the synthetic states of `Test/UpdateAll.lean` (the `slew_rate_max` reference at
`slMax`, outside the object), the returned value is `Corpus.Filter.modVal dt M msr` with `M` the float at `slMax` and
`msr` the field `+32` as the call leaves it. All four branches occur in the grid (`dt` not positive; `M ≤ 0`;
`msr > M`; `msr ≤ M`), which the second check confirms.
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge
open Corpus.Test.UpdateAll

namespace Corpus.Test.Modifier

def modCheck (mx tau field sample dt : Binary32) (i0 i1 flags : UInt8) : Bool :=
  let s := slState mx tau field i0 i1 flags
  let r := (Vehicle_lib.SlewLimiter.modifier slObj sample dt).run s
  bits r.1 == bits (Corpus.Filter.modVal dt (rd s slMax) (rd r.2 (slObj + 32)))

/-- Which branch of `modVal` a grid point takes (0: `dt` not positive, 1: `M ≤ 0`, 2: `msr > M`, 3: otherwise). -/
def branch (mx tau field sample dt : Binary32) (i0 i1 flags : UInt8) : Nat :=
  let s := slState mx tau field i0 i1 flags
  let r := (Vehicle_lib.SlewLimiter.modifier slObj sample dt).run s
  if !(Id.run (Vehicle_lib.is_positive'float.pure' dt)) then 0
  else if decide (rd s slMax ≤ Int32.toBinary32 0) then 1
  else if decide (rd r.2 (slObj + 32) > rd s slMax) then 2 else 3

def grid : List (Binary32 × Binary32 × Binary32 × Binary32 × Binary32 × UInt8 × UInt8 × UInt8) := Id.run do
  let mut out := []
  for mx in [B 0x3f800000, B 0, B 0xbf800000, B 0x7fc00000, B 0x7f800000, B 0x3dcccccd] do
    for tau in [B 0x40000000, B 0x7fc00000] do
      for field in [B 0, B 0x3f800000, B 0x7fc00000, B 0x41200000] do
        for sample in [B 0x3f800000, B 0xc2c80000, B 0x7f800000] do
          for dt in [B 0x3c23d70a, B 0, B 0x7fc00000] do
            for (i0, i1, flags) in [((0 : UInt8), (1 : UInt8), (0 : UInt8)), (2, 255, 3)] do
              out := (mx, tau, field, sample, dt, i0, i1, flags) :: out
  return out

#guard grid.all fun (mx, tau, field, sample, dt, i0, i1, flags) => modCheck mx tau field sample dt i0 i1 flags
#guard [0, 1, 2, 3].all fun b =>
  grid.any fun (mx, tau, field, sample, dt, i0, i1, flags) => branch mx tau field sample dt i0 i1 flags == b

end Corpus.Test.Modifier
