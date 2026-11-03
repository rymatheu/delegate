import Flight.Arith

/-!
# `Float` instance of the scalar interface

The executable controller runs over IEEE-754 doubles. This file imports only core Lean and
`Flight.Arith`.
-/

namespace Flight

/-- Double-precision floating point satisfies the controller's scalar interface, using the core `Float` operations. -/
instance instArithFloat : Arith Float where
  toZero := inferInstance
  toOne := inferInstance
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  toLT := inferInstance
  toLE := inferInstance
  toMin := inferInstance
  toMax := inferInstance
  toOfScientific := inferInstance
  natCast := Nat.toFloat
  decLt := fun a b => Float.decLt a b
  decLe := fun a b => Float.decLe a b
  abs := Float.abs
  sqrt := Float.sqrt
  sin := Float.sin
  cos := Float.cos
  atan2 := Float.atan2
  pi := 3.141592653589793

end Flight
