import Vehicle_lib

/-!
A smoke test of the translation's definitions (README.md "Phase 5: total definitions"): not part of the translated
output and not a theorem of the corpus. Each `example` only shows that a definition unfolds in the kernel (by `rfl`,
`unfold` or `simp only`): a pure leaf, a memory function's definition equation, a function of a formerly recursive
component (the depth's base case and one step), and the structural recursion on the World's text type.

    cd lean && LEAN_NUM_THREADS=1 lake env lean ../tests/UnfoldSmoke.lean     (after `lake build vehicle_replay`)

`set_option profiler true` prints the time of every step of each example (elaboration, tactics, kernel type checking,
linting; a summary at the end).
-/

open FloatLib.Floats (Binary32 Binary64)
open Vehicle_lib

set_option profiler true
set_option profiler.threshold 0

/-- 1. A pure leaf (`safe_sqrt<float>` as a function of its argument, in `Id`): its body, by `rfl`. -/
example (v : Binary32) :
    safe_sqrt'float.pure' v =
      (if decide (v ≥ Int32.toBinary32 (0 : Int32)) = true then Binary32.sqrt v else Int32.toBinary32 (0 : Int32)) := by
  unfold safe_sqrt'float.pure'
  rfl

/-- 2. A memory function's definition equation (the Functor call of `AP_Mission::complete`, per-site dispatch): the
entry passes the component's depth, and one step of the depth-indexed definition is its body, by `rfl`. -/
example (this : UInt64) :
    Functor'void.operator__'at'AP_Mission'_mission_complete_fn this =
      Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec 300 this := rfl

example (n : Nat) (this : UInt64) :
    Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec (n + 1) this =
      (do
        let t1 ← PMem.ldU64 (this + 8)
        let t2 ← PMem.ldU64 this
        fnptr'0'at'AP_Mission'_mission_complete_fn'rec n t1 t2
        return ()) := rfl

/-- 3. Functions of the formerly recursive component of `Copter::set_mode` (75 functions, depth 300) and of
`Copter::set_land_complete` with `AP_Arming_Copter::disarm` (depth 64): with no depth left a function is
`PMem.depthOut` (the sticky flag, the type's default), by `rfl`; with depth `n + 1` it is its body, whose calls inside
the component take `n`, by `rfl` (`Mode::set_mode`, mode.cpp: `return copter.set_mode(mode, reason);`). -/
example (this : UInt64) (b : Bool) : Copter.set_land_complete'rec 0 this b = PMem.depthOut := rfl

example (n : Nat) (this : UInt64) (mode reason : UInt8) :
    Mode.set_mode'rec (n + 1) this mode reason =
      (do
        let t ← Copter.set_mode'rec n (0x86d8 : UInt64) mode reason
        return t) := rfl

/-- 4. Structural recursion on the World's text type (`worldOutputs'ctext` on `Estimator_lib.CText`): the empty text
writes nothing, by `rfl`. -/
example (bp : UInt64) : worldOutputs'ctext bp .none = pure () := rfl
