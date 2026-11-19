import Harness.Expr
import Harness.Sha256

/-! A contract: an assumption over (params, input) and a guarantee over (params, input, output),
each a list of named clauses. The contract holds on a run when, at every step where the
assumption holds, every guarantee clause holds. -/

namespace Harness

structure Clause where
  name : String
  expr : Expr
  deriving Inhabited

def Clause.text (c : Clause) : String := s!"{c.name}: {c.expr.print}"

structure Contract where
  assume : List Clause
  guarantee : List Clause
  deriving Inhabited

namespace Contract

def assumeText (c : Contract) : String :=
  "\n".intercalate (c.assume.map fun a => s!"  {a.text}")

/-- What a guarantee clause's hash is taken of: the whole assumption and that clause, printed.
Changing the assumption makes the evidence of every clause stale; changing one guarantee clause
makes only that clause's evidence stale. -/
def clauseHashText (c : Contract) (g : Clause) : String :=
  s!"assume\n{c.assumeText}\nguarantee\n  {g.text}\n"

def clauseHash (c : Contract) (g : Clause) : String := Sha256.hashString (c.clauseHashText g)

def text (c : Contract) : String :=
  s!"assume\n{c.assumeText}\nguarantee\n" ++ "\n".intercalate (c.guarantee.map fun g => s!"  {g.text}")

end Contract

end Harness
