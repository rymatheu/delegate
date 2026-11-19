import Harness.Module

/-! Clause helpers shared by the PX4 controller modules (px4_att, px4_pos, px4_fmm, px4_land) and
their compositions. Plain functions building contract expressions; no module-specific meaning. -/

namespace Px4.Modules.Px4Common

open Harness Harness.Contract.Lang

/-- `x` is NaN (the only value for which `x = x` fails). -/
def isNaN (x : String) : Expr := ¬. (Expr.var x =. Expr.var x)

/-- `x` is finite or NaN, not ±∞ (PX4 uses NaN for "not set"). -/
def notInf (x : String) : Expr := finite x ∨. isNaN x

/-- `x` is NaN or within [lo, hi]. -/
def nanOr (x : String) (lo hi : Expr) : Expr := isNaN x ∨. (lo ≤. x ∧. x ≤. hi)

/-- `x` is within [lo, hi] (so finite). -/
def within (x : String) (lo hi : Expr) : Expr := lo ≤. x ∧. x ≤. hi

/-- |x| ≤ b. -/
def absLe (x : String) (b : Expr) : Expr := abs x ≤. b

/-- The conjunction of a non-empty list (`tt` for the empty one). -/
def allOf (es : List Expr) : Expr :=
  match es with
  | [] => tt
  | e :: rest => rest.foldl (· ∧. ·) e

/-- The fields `pre_0 … pre_(n-1)` of an array field. -/
def arr (pre : String) (n : Nat) : List String := (List.range n).map fun i => s!"{pre}_{i}"

/-- The squared norm of the array field `pre_0 … pre_(n-1)`, summed in index order. -/
def normSq (pre : String) (n : Nat) : Expr :=
  match arr pre n with
  | [] => 0
  | f :: rest => rest.foldl (fun e g => e + Expr.var g * Expr.var g) (Expr.var f * Expr.var f)

/-- A unit quaternion (or unit vector) within a tolerance on the squared norm. -/
def unitArr (pre : String) (n : Nat) (tol : Expr := 0.001) : Expr :=
  Expr.abs (normSq pre n - 1) ≤. tol

/-- Every component of the array field finite. -/
def finiteArr (pre : String) (n : Nat) : Expr := allOf ((arr pre n).map fun f =>
    Expr.finite (Expr.var f))

/-- binary32 `math::radians(1)` = `(float)M_PI / 180.f`, as PX4 computes it. -/
def degToRad : Expr := 0.0174532924

end Px4.Modules.Px4Common
