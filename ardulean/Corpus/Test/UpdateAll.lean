import ArduLean.Vehicle
import Corpus.Test.Edge
import Corpus.Machine.Memory

/-!
# Edge evaluation of the third increment's candidates (Corpus/PLAN.md, rule 6)

Run on synthetic states (a fresh memory, the objects in the heap, the stack at `stackBase`, fields set from edge
values): `LowPassFilter<float>::apply` (Case and Effect), `SlewLimiter::modifier` (Effect, the `!is_positive(dt)`
case, the window indices at `0`, `1`, `2`, `255`), `AC_PID::update_all` (Effect, the integrator bound, the
non-finite case), `update_i`'s condition form, and the bit-field laws. Effect is checked byte by byte on windows around
the object and the stack (the rest of the memory is checked through the size and a sample of addresses), together with
the stack pointer and other fields of the state. (Not states of the recorded flights.)
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge

namespace Corpus.Test.UpdateAll

def B (w : UInt32) : Binary32 := Binary32.ofBits w
def bits (x : Binary32) : UInt32 := Binary32.toBits x
def rd (st : PMem.Mem) (a : UInt64) : Binary32 := ((PMem.ldF32 a).run st).1
def le (a b : Binary32) : Bool := decide (a ≤ b)

def fresh : PMem.Mem := PMem.fresh 0x40000 0x30000 0x20000 ByteArray.empty

/-- Every byte of `[lo, hi)` outside `w` is unchanged, as are the size, the stack pointer, the heap pointer and the
sticky flags. -/
def frameOK (s s' : PMem.Mem) (lo hi : Nat) (w : Nat → Bool) : Bool :=
  s'.m.size == s.m.size && s'.sp == s.sp && s'.hp == s.hp && s'.fuelOut == s.fuelOut && s'.depthOut == s.depthOut &&
    (List.range (hi - lo)).all fun k => w (lo + k) || s'.m.get! (lo + k) == s.m.get! (lo + k)

def inI (a n j : Nat) : Bool := a ≤ j && j < a + n

def vals : List Binary32 := [B 0, B 0x80000000, B 0x3f800000, B 0xbf800000, B 0x34000000, B 0x7f7fffff,
  B 0x7f800000, B 0x7fc00000, B 0x3dcccccd, B 0x42c80000, B 0x00000001]

/-! ## `LowPassFilter<float>::apply` -/

def lpfObj : UInt64 := 0x20100
def lpfSmp : UInt64 := 0x20200
def lpfDt : UInt64 := 0x20204

def lpfState (out cutoff smp dt : Binary32) (flag : UInt8) : PMem.Mem :=
  let act : PMem.M Unit := do
    PMem.stF32 lpfObj out; PMem.stU8 (lpfObj + 4) flag; PMem.stF32 (lpfObj + 8) cutoff
    PMem.stF32 lpfSmp smp; PMem.stF32 lpfDt dt
  (act.run fresh).2

def lpfCheck (out cutoff smp dt : Binary32) (flag : UInt8) : Bool :=
  let s := lpfState out cutoff smp dt flag
  let r := (Vehicle_lib.LowPassFilter'float.apply lpfObj lpfSmp lpfDt).run s
  let α := ((Vehicle_lib.calc_lowpass_alpha_dt dt cutoff).run s).1
  let expect := if flag != 0 then out + (smp - out) * α else smp
  bits r.1 == bits expect &&
    frameOK s r.2 (0x20000) (0x20300) (fun j => inI lpfObj.toNat 5 j) &&
    frameOK s r.2 (0x30000 - 64) (0x30000 + 128) (fun j => inI 0x30000 16 j)

def lpfFails : List String := Id.run do
  let mut out := []
  for o in vals do
    for c in [B 0, B 0x42c80000, B 0x3f800000, B 0x7fc00000, B 0xbf800000] do
      for x in [B 0x3f800000, B 0x7f800000, B 0x7fc00000] do
        for d in [B 0x3c23d70a, B 0, B 0xbf800000] do
          for f in [0, 1, 255] do
            if !lpfCheck o c x d f then out := s!"{nameOf o} {nameOf c} {nameOf x} {nameOf d} {f}" :: out
  return out

#guard lpfFails.isEmpty

/-! ## `SlewLimiter::modifier` -/

def slObj : UInt64 := 0x20400
/-- `slew_rate_max` and `slew_rate_tau` (references): two floats outside the object. -/
def slMax : UInt64 := 0x20500
def slTau : UInt64 := 0x20504

def slState (mx tau field : Binary32) (i0 i1 : UInt8) (flags : UInt8) : PMem.Mem :=
  let act : PMem.M Unit := do
    PMem.stU64 slObj slMax; PMem.stU64 (slObj + 8) slTau
    PMem.stF32 slMax mx; PMem.stF32 slTau tau
    for o in [16, 28, 32, 36, 40, 44] do PMem.stF32 (slObj + o.toUInt64) field
    PMem.stU32 (slObj + 48) 7; PMem.stU32 (slObj + 52) 9
    PMem.stU8 (slObj + 56) i0; PMem.stU8 (slObj + 57) i1
    PMem.stU8 (slObj + 76) flags; PMem.stU8 (slObj + 77) (flags >>> 1)
  (act.run fresh).2

def slCheck (mx tau field sample dt : Binary32) (i0 i1 flags : UInt8) : Bool :=
  let s := slState mx tau field i0 i1 flags
  let r := (Vehicle_lib.SlewLimiter.modifier slObj sample dt).run s
  let notPos := !(Id.run (Vehicle_lib.is_positive'float.pure' dt))
  frameOK s r.2 0x20000 0x20800 (fun j => inI (slObj.toNat + 16) 62 j) &&
    frameOK s r.2 (0x30000 - 64) (0x30000 + 128) (fun j => inI 0x30000 32 j) &&
    (!notPos || bits r.1 == 0x3f800000)

def slFails : List String := Id.run do
  let mut out := []
  for mx in [B 0x3f800000, B 0, B 0xbf800000, B 0x7fc00000, B 0x7f800000] do
    for tau in [B 0x40000000, B 0, B 0x7fc00000] do
      for field in [B 0, B 0x3f800000, B 0x7fc00000, B 0x7f7fffff] do
        for sample in [B 0x3f800000, B 0xc2c80000, B 0x7f800000] do
          for dt in [B 0x3c23d70a, B 0, B 0xbf800000, B 0x7fc00000] do
            for (i0, i1) in [((0 : UInt8), (1 : UInt8)), (1, 2), (2, 255), (255, 0)] do
              for flags in [(0 : UInt8), 1, 2, 3] do
                if !slCheck mx tau field sample dt i0 i1 flags then
                  out := s!"{nameOf mx} {nameOf tau} {nameOf field} {nameOf sample} {nameOf dt} {i0} {i1} {flags}" :: out
  return out

#guard slFails.isEmpty

/-! ## `AC_PID::update_all` -/

def pid : UInt64 := 0x20800
def pidMax : UInt64 := 0x20a00
def pidTau : UInt64 := 0x20a04

def pidState (kp ki kimax integ err : Binary32) (flags : UInt8) (pdmax : Binary32) : PMem.Mem :=
  let act : PMem.M Unit := do
    PMem.stF32 pid kp; PMem.stF32 (pid + 4) ki; PMem.stF32 (pid + 8) (B 0x3c23d70a)
    PMem.stF32 (pid + 16) kimax; PMem.stF32 (pid + 20) pdmax
    PMem.stF32 (pid + 24) (B 0x41a00000); PMem.stF32 (pid + 28) (B 0); PMem.stF32 (pid + 32) (B 0x41a00000)
    PMem.stU64 (pid + 48) pidMax; PMem.stU64 (pid + 56) pidTau
    PMem.stF32 pidMax (B 0x42c80000); PMem.stF32 pidTau (B 0x3f800000)
    PMem.stU8 (pid + 128) flags
    PMem.stF32 (pid + 132) integ; PMem.stF32 (pid + 136) (B 0x3f800000); PMem.stF32 (pid + 140) err
    PMem.stU8 (pid + 148) 1
  (act.run fresh).2

def ibound (st : PMem.Mem) : Bool :=
  let M := rd st (pid + 16)
  let I := rd st (pid + 132)
  Binary32.isFinite M && le (B 0) M && le (-M) I && le I M

def pidCheck (kp ki kimax integ err : Binary32) (flags : UInt8) (pdmax target meas dt : Binary32) (limit : Bool) :
    Bool :=
  let s := pidState kp ki kimax integ err flags pdmax
  let r := (Vehicle_lib.AC_PID.update_all pid target meas dt limit (B 0x3f800000) (B 0x3f800000)).run s
  let nonfinite := !Binary32.isFinite target || !Binary32.isFinite meas
  frameOK s r.2 0x20000 0x20c00 (fun j => inI (pid.toNat + 48) 152 j) &&
    frameOK s r.2 (0x30000 - 64) (0x30000 + 128) (fun j => inI 0x30000 48 j) &&
    (!ibound s || ibound r.2) &&
    (!nonfinite || bits r.1 == 0)

def pidFails : List String := Id.run do
  let mut out := []
  for ki in [B 0, B 0x3f800000, B 0x7fc00000] do
    for kimax in [B 0x3f800000, B 0, B 0x7f800000, B 0x7fc00000] do
      for integ in [B 0, B 0x3f000000, B 0xbf800000, B 0x7fc00000] do
        for err in [B 0x3f800000, B 0xbf800000] do
          for flags in [(0 : UInt8), 1, 2, 3] do
            for target in [B 0x3f800000, B 0x7f800000, B 0x7fc00000, B 0x42c80000] do
              for dt in [B 0x3c23d70a, B 0] do
                for limit in [false, true] do
                  if !pidCheck (B 0x3f800000) ki kimax integ err flags (B 0x3f000000) target (B 0) dt limit then
                    out := s!"{nameOf ki} {nameOf kimax} {nameOf integ} {nameOf err} {flags} {nameOf target} {nameOf dt} {limit}" :: out
  return out

#guard pidFails.isEmpty

/-! ## `update_i`: the condition form (`update_i_integrator_cases`) -/

def updiCheck (ki kimax integ err dt isc : Binary32) (limit : Bool) : Bool :=
  let s := pidState (B 0x3f800000) ki kimax integ err 0 (B 0)
  let s' := ((Vehicle_lib.AC_PID.update_i pid dt limit isc).run s).2
  let I := rd s (pid + 132)
  let E := rd s (pid + 140)
  let K := rd s (pid + 4)
  let M := rd s (pid + 16)
  let expect :=
    if (!Id.run (Vehicle_lib.is_zero.pure' K) && Id.run (Vehicle_lib.is_positive'float.pure' dt)) then
      (if (!limit || (Id.run (Vehicle_lib.is_positive'float.pure' I) && Id.run (Vehicle_lib.is_negative'float.pure' E)) ||
          (Id.run (Vehicle_lib.is_negative'float.pure' I) && Id.run (Vehicle_lib.is_positive'float.pure' E))) then
        Id.run (Vehicle_lib.constrain_value_line'float.pure' (I + ((E * K) * isc) * dt) (-M) M 346)
      else I)
    else B 0
  bits (rd s' (pid + 132)) == bits expect

def updiFails : List String := Id.run do
  let mut out := []
  for ki in vals do
    for integ in vals do
      for err in [B 0x3f800000, B 0xbf800000, B 0, B 0x7fc00000] do
        for dt in [B 0x3c23d70a, B 0, B 0x34000000, B 0x33ffffff] do
          for limit in [false, true] do
            if !updiCheck ki (B 0x3f800000) integ err dt (B 0x3f800000) limit then
              out := s!"{nameOf ki} {nameOf integ} {nameOf err} {nameOf dt} {limit}" :: out
  return out

#guard updiFails.isEmpty

/-! ## Bit-fields: store then load, other bits kept -/

def bitsCheck (b : UInt8) (o o' : Nat) (v : UInt64) : Bool :=
  let s := ((PMem.stU8 0x20f00 b).run fresh).2
  let s' := ((PMem.stBits 0x20f00 o 1 v).run s).2
  let ld (st : PMem.Mem) (k : Nat) : UInt64 := ((PMem.ldBits 0x20f00 k 1).run st).1
  ld s' o == v % 2 && (o == o' || ld s' o' == ld s o') && s'.m.get! 0x20eff == s.m.get! 0x20eff &&
    s'.m.get! 0x20f01 == s.m.get! 0x20f01

#guard (List.range 256).all fun b => (List.range 8).all fun o => (List.range 8).all fun o' =>
  [0, 1, 2, 3].all fun v => bitsCheck b.toUInt8 o o' v

end Corpus.Test.UpdateAll
