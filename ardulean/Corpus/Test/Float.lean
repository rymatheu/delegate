import Corpus.Test.Edge

/-!
# Edge evaluation of the second increment's float lemmas (Corpus/PLAN.md, rule 6)

`Corpus/Machine/Float.lean`, section "Rounding with overflow, negation, signs": each statement as a `Bool` on all
pairs of edge inputs, before it was proved; and the witness of FINDINGS F13 (`x - y = -(y - x)` as words).
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Edge

namespace Corpus.Test.Float

def B (w : UInt32) : Binary32 := Binary32.ofBits w
def nan? (x : Binary32) : Bool := Binary32.isNaN x
def fin? (x : Binary32) : Bool := Binary32.isFinite x
def le (a b : Binary32) : Bool := decide (a ≤ b)
def lt (a b : Binary32) : Bool := decide (a < b)
def same (a b : Binary32) : Bool := Binary32.toBits a == Binary32.toBits b
/-- finite values `> 0`, as `mul_le_mul_of_pos_right'` takes them -/
def pos : List Binary32 := [B 0x00000001, B 0x34000000, B 0x3c8efa35, B 0x3f800000, B 0x42652ee0, B 0x7f7fffff,
  B 0x40000000]

-- `neg_mul'`, `mul_neg'`: as words, whenever the product is a number
#guard (fails₂ fun x y => nan? x || nan? y || nan? (x * y) || same ((-x) * y) (-(x * y))).isEmpty
#guard (fails₂ fun x y => nan? x || nan? y || nan? (x * y) || same (x * (-y)) (-(x * y))).isEmpty
-- `isNaN_neg_mul`, `isNaN_neg_div`, `neg_div'`
#guard (fails₂ fun x y => nan? ((-x) * y) == nan? (x * y)).isEmpty
#guard (fails₂ fun x y => nan? ((-x) / y) == nan? (x / y)).isEmpty
#guard (fails₂ fun x y => nan? x || nan? y || nan? (x / y) || same ((-x) / y) (-(x / y))).isEmpty
-- `mul_comm'` on numbers
#guard (fails₂ fun x y => nan? x || nan? y || same (x * y) (y * x)).isEmpty
-- `sub_antisymm`: NaN together, and opposite values (`==` identifies `±0`)
#guard (fails₂ fun x y => nan? x || nan? y ||
  (nan? (x - y) == nan? (y - x) && (nan? (x - y) || (x - y) == -(y - x)))).isEmpty
-- finding F13: as words `x - y = -(y - x)` fails exactly at `x = y` (`+0` against `-0`)
#guard same (B 0x3f800000 - B 0x3f800000) (B 0) && same (-(B 0x3f800000 - B 0x3f800000)) (B 0x80000000)
#guard (fails₂ fun x y => nan? x || nan? y || nan? (x - y) || same (x - y) (-(y - x)) || x == y).isEmpty
-- `mul_le_mul_of_pos_right'`: through overflow, `±∞` included
#guard (fails₂ fun x y => !le x y || pos.all fun c => le (x * c) (y * c)).isEmpty
-- sign under overflow: `mul_self_nonneg'`, `add_nonneg'`
#guard (fails₁ fun x => nan? x || (!nan? (x * x) && le (B 0) (x * x))).isEmpty
#guard (fails₂ fun x y => !(le (B 0) x && le (B 0) y) || (!nan? (x + y) && le (B 0) (x + y))).isEmpty
-- `div_nonneg_of_pos`
#guard (fails₂ fun x y => !(fin? x && fin? y && lt (B 0) x && lt (B 0) y) || (!nan? (x / y) && le (B 0) (x / y))).isEmpty
-- `midpoint_mem`
#guard (fails₂ fun l h => !le l h || !fin? (l + h) || (fin? ((l + h) / B 0x40000000) && le l ((l + h) / B 0x40000000) &&
  le ((l + h) / B 0x40000000) h)).isEmpty
-- `isFinite_one_sub`
#guard (fails₁ fun e => !fin? e || fin? (B 0x3f800000 - e)).isEmpty

end Corpus.Test.Float
