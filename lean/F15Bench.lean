import CFloat

/-!
F15 (PORT-PLAN.md 4.13): the cost of an element write into an array member of a structure, as the
translator emits it (README.md, "Phase 3: EKF data structures"). A 24 × 24 matrix of `Binary64` (EKF3's
`Matrix24`, flat row-major) is a member of the state; each benchmark writes its 576 elements once per
call, each element from another element (a transpose, so no floating-point operation is timed).

- `before`: `s := { s with P := s.P.set! k v }` (the emitted form without --ekf-arrays): `s.P` is still
  referenced by `s` when `set!` runs, so the array is copied on every write.
- `after`: the array is taken out of the structure first (--ekf-arrays): `let a := s.P; s := { s with
  P := #[] }; s := { s with P := a.set! k v }`; `a` is then the only reference and `set!` is in place.
- `*_field`: the value also reads another member of the state (`if s.a == 7 then s.b else ...`).
- `nested_*`: the same for an array inside a member structure inside an array of structures
  (`s.EKF[m].P[k]`, EKFGSF_yaw's `EKF[mdl_idx].P[i][j]`).

Usage: `lake build f15_bench && .lake/build/bin/f15_bench [calls]`
-/

open FloatLib.Floats (Binary64)

namespace F15Bench

structure Inner where
  P : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0)
  q : Binary64 := Binary64.ofBits 0
deriving Inhabited

structure State where
  a : UInt32 := 0
  P : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0)
  EKF : Array Inner := Array.replicate 5 {}
  inner : Inner := {}
  b : Binary64 := Binary64.ofBits 0
deriving Inhabited

def before (s : State) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      s := { s with P := s.P.set! (i * 24 + j) s.P[j * 24 + i]! }
  return s

def after (s : State) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      let t'1 := s.P[j * 24 + i]!
      let t'2 := s.P
      s := { s with P := #[] }
      s := { s with P := t'2.set! (i * 24 + j) t'1 }
  return s

/-- As `before`, the value also reading another member of `s` (as most translated assignments do). -/
def before_field (s : State) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      s := { s with P := s.P.set! (i * 24 + j) (if s.a == 7 then s.b else s.P[j * 24 + i]!) }
  return s

def after_field (s : State) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      let t'1 := (if s.a == 7 then s.b else s.P[j * 24 + i]!)
      let t'2 := s.P
      s := { s with P := #[] }
      s := { s with P := t'2.set! (i * 24 + j) t'1 }
  return s

/-- An array in a member structure (`s.inner.P[k]`), as emitted. -/
def member_before (s : State) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      s := { s with inner.P := s.inner.P.set! (i * 24 + j) s.inner.P[j * 24 + i]! }
  return s

def nested_before (s : State) (m : Nat) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      s := { s with EKF := s.EKF.set! m ({ s.EKF[m]! with P := s.EKF[m]!.P.set! (i * 24 + j) (s.EKF[m]!.P[j * 24 + i]!) }) }
  return s

def nested_after (s : State) (m : Nat) : State := Id.run do
  let mut s := s
  for i in [0:24] do
    for j in [0:24] do
      let t'1 := s.EKF[m]!.P[j * 24 + i]!
      let t'2 := s.EKF
      s := { s with EKF := #[] }
      let t'3 := t'2[m]!
      let t'2 := t'2.set! m default
      let t'4 := t'3.P
      let t'3 := { t'3 with P := #[] }
      let t'3 := { t'3 with P := t'4.set! (i * 24 + j) t'1 }
      s := { s with EKF := t'2.set! m t'3 }
  return s

def init : State := Id.run do
  let mut s : State := {}
  for k in [0:576] do
    s := { s with P := s.P.set! k (Binary64.ofBits (UInt64.ofNat k)) }
  return s

def sum (a : Array Binary64) : UInt64 := a.foldl (fun x y => x + Binary64.toBits y) 0

def time (name : String) (calls : Nat) (f : State → State) : IO Unit := do
  let mut s := init
  let t0 ← IO.monoNanosNow
  for _ in [0:calls] do
    s := f s
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / (calls * 576).toFloat
  IO.println s!"{name}: {calls} calls x 576 element writes: {ns} ns per write (checksum {sum s.P + sum (s.EKF[2]!).P})"

end F15Bench

def main (args : List String) : IO Unit := do
  let calls := (args.head? >>= String.toNat?).getD 200
  F15Bench.time "before" calls F15Bench.before
  F15Bench.time "after" calls F15Bench.after
  F15Bench.time "before_field" calls F15Bench.before_field
  F15Bench.time "after_field" calls F15Bench.after_field
  F15Bench.time "member_before" calls F15Bench.member_before
  F15Bench.time "nested_before" calls (F15Bench.nested_before · 2)
  F15Bench.time "nested_after" calls (F15Bench.nested_after · 2)
