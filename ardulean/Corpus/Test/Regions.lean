import ArduLean.Vehicle
import Corpus.Machine.Memory
import Corpus.Test.UpdateAll

/-!
# Regions: the heap after static construction, `alloc`, and the stack depth under the rate PIDs (third increment)

* The vehicle's initial memory (`Vehicle_lib.initMem`) and its C++ static construction (`staticDynamicInit`,
  `staticConstruct`) are evaluated here: the heap pointer after static construction, inside `[heapBase, stackBase)`.
  `AP_Vehicle::setup()` (which runs `Copter::allocate_motors`, where `AC_AttitudeControl_Multi` and `AC_PosControl` are
  allocated) calls the HAL (`PMem.halImpl`, an `@[extern]` constant implemented by the driver Main.lean), so it cannot be
  evaluated by the Lean interpreter; OPEN.md states what remains.
* `PMem.alloc` on synthetic states: the block, the heap pointer's step, the zeroing.
* The stack: the frame sizes of the chain scheduler → rate controller → `AC_PID::update_all` → callees, checked against
  the code by `rfl`, and the high-water mark of `update_all`'s run measured with a sentinel.
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Corpus.Test.Regions

/-! ## Static construction -/

def s0 : PMem.Mem := Vehicle_lib.initMem (ByteArray.mk (Array.replicate 65536 0))
def sStatic : PMem.Mem := ((do Vehicle_lib.staticDynamicInit; Vehicle_lib.staticConstruct : PMem.M Unit).run s0).2

/- After static construction: 3808 bytes of heap used (`hp = 0x20ee0`), inside `[heapBase, stackBase)`; the stack
pointer at `stackBase`; no fuel or depth flag. -/
#guard sStatic.hp == 0x20ee0 && Vehicle_lib.heapBase ≤ sStatic.hp.toNat && sStatic.hp.toNat ≤ Vehicle_lib.stackBase &&
  sStatic.sp.toNat == Vehicle_lib.stackBase && sStatic.m.size == Vehicle_lib.memSize && !sStatic.fuelOut &&
  !sStatic.depthOut

/-! ## `alloc` -/

def allocCheck (hp n : Nat) : Bool :=
  let s := { Corpus.Test.UpdateAll.fresh with hp := hp.toUInt64 }
  let s := ((do for k in [0:n + 32] do PMem.stU8 (hp.toUInt64 + k.toUInt64 - 16) 0xAA : PMem.M Unit).run s).2
  let r := (PMem.alloc n).run s
  r.1 == hp.toUInt64 && r.2.hp.toNat == hp + (n + 15) / 16 * 16 && r.2.sp == s.sp &&
    (List.range n).all (fun k => r.2.m.get! (hp + k) == 0) &&
    (List.range 16).all (fun k => r.2.m.get! (hp - 16 + k) == 0xAA && r.2.m.get! (hp + n + k) == 0xAA)

#guard [1, 15, 16, 17, 104, 776, 984, 1112, 2504, 4096].all fun n => allocCheck 0x20ee0 n

/-! ## The stack under the rate PIDs -/

/-- The frames on the path, as the code makes them (`enter k`, `frameSize k = ⌈k/16⌉·16`). -/
example (this : UInt64) : Vehicle_lib.AP_Vehicle.loop this =
    (do let fp ← PMem.enter 72; let r ← Vehicle_lib.AP_Vehicle.loop.body fp this; PMem.leave fp; return r) := rfl
example (this : UInt64) : Vehicle_lib.AP_Scheduler.loop this =
    (do let fp ← PMem.enter 16; let r ← Vehicle_lib.AP_Scheduler.loop.body fp this; PMem.leave fp; return r) := rfl
example (this : UInt64) : Vehicle_lib.AC_AttitudeControl_Multi.rate_controller_run this =
    (do let fp ← PMem.enter 28
        let r ← Vehicle_lib.AC_AttitudeControl_Multi.rate_controller_run.body fp this; PMem.leave fp; return r) := rfl
example (this g : UInt64) (dt : Binary32) : Vehicle_lib.AC_AttitudeControl_Multi.rate_controller_run_dt this g dt =
    (do let fp ← PMem.enter 12
        let r ← Vehicle_lib.AC_AttitudeControl_Multi.rate_controller_run_dt.body fp this g dt; PMem.leave fp
        return r) := rfl
example (this : UInt64) (a b c : Binary32) (l : Bool) (d e : Binary32) :
    Vehicle_lib.AC_PID.update_all this a b c l d e =
    (do let fp ← PMem.enter 4; let r ← Vehicle_lib.AC_PID.update_all.body fp this a b c l d e; PMem.leave fp
        return r) := rfl
example (this : UInt64) (a b : Binary32) : Vehicle_lib.SlewLimiter.modifier this a b =
    (do let fp ← PMem.enter 12; let r ← Vehicle_lib.SlewLimiter.modifier.body fp this a b; PMem.leave fp
        return r) := rfl
example (this a b : UInt64) : Vehicle_lib.LowPassFilter'float.apply this a b =
    (do let fp ← PMem.enter 4; let r ← Vehicle_lib.LowPassFilter'float.apply.body fp this a b; PMem.leave fp
        return r) := rfl
example (this : UInt64) (a : Binary32) (l : Bool) (b : Binary32) : Vehicle_lib.AC_PID.update_i this a l b =
    (do let fp ← PMem.enter 4; let r ← Vehicle_lib.AC_PID.update_i.body fp this a l b; PMem.leave fp
        return r) := rfl

def frame (k : Nat) : Nat := (k + 15) / 16 * 16

/- The depth from `AP_Vehicle::loop`'s entry: its frame (80), `AP_Scheduler::loop` (16), the task dispatch
(`AP_Scheduler::run`, the functor and the method wrapper, `Copter::run_rate_controller_main`: no frame), the rate
controller (32), `rate_controller_run_dt` (16), `update_all` (16), then `update_i` (16) or `SlewLimiter::modifier` with
`LowPassFilter::apply` (32): 176 bytes to `update_i`, 192 at the deepest point under `update_all`. -/
#guard frame 72 + frame 16 + frame 28 + frame 12 + frame 4 + frame 4 == 176 &&
  frame 72 + frame 16 + frame 28 + frame 12 + frame 4 + frame 12 + frame 4 == 192

/-- The high-water mark of `update_all`'s run on the stack: with the 256 bytes from the stack pointer set to a
sentinel, the bytes `update_all` changes there are all below `sp + 48` (and some at or above `sp + 32`, the
modifier's filter frame). -/
def hwm (s : PMem.Mem) (target dt : Binary32) : Nat :=
  let sp := s.sp
  let s := ((do for k in [0:256] do PMem.stU8 (sp + k.toUInt64) 0xAA : PMem.M Unit).run s).2
  let r := (Vehicle_lib.AC_PID.update_all Corpus.Test.UpdateAll.pid target (Binary32.ofBits 0) dt false
    (Binary32.ofBits 0x3f800000) (Binary32.ofBits 0x3f800000)).run s
  ((List.range 256).filter fun k => r.2.m.get! (sp.toNat + k) != 0xAA).foldl max 0

#guard
  let s := Corpus.Test.UpdateAll.pidState (Binary32.ofBits 0x3f800000) (Binary32.ofBits 0x3f800000)
    (Binary32.ofBits 0x3f800000) (Binary32.ofBits 0) (Binary32.ofBits 0x3f800000) 0 (Binary32.ofBits 0x3f000000)
  let h := hwm s (Binary32.ofBits 0x3f800000) (Binary32.ofBits 0x3c23d70a)
  32 ≤ h && h < 48

end Corpus.Test.Regions
