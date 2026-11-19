import Corpus

/-!
The audit of the proof corpus (Corpus/PLAN.md, "Tooling"). Not a proof: a report on the theorems of the modules
`Corpus.Code.*`.

    LEAN_NUM_THREADS=1 lake env lean tests/CorpusAudit.lean     (after `lake build Corpus`)

1. Rule 2: every theorem whose name starts with `Corpus.` and lives in a `Corpus.Code.*` module has a constant of
   `Vehicle_lib` or `Estimator_lib` in its statement. The ones that do not are listed (`RULE 2 VIOLATION`).
2. Rule 4: the axioms each theorem depends on; any axiom other than `propext`, `Classical.choice`, `Quot.sound` is
   listed (`RULE 4 VIOLATION`), and the set of axioms used is printed.
3. Coverage (a `Wrapper` is the lemma `f … = pure (f.pure' …)`): per code function (a `f.pure'` counts as `f`), the kinds of lemma proved about it, by the theorem's name
   suffix (Corpus/PLAN.md, "Kinds of low-level proof"); a theorem counts for every code constant in its
   conclusion. Printed as Markdown table rows for `Corpus/LEDGER.md`.
-/

open Lean

namespace CorpusAudit

def isCodeConst (n : Name) : Bool :=
  (`Vehicle_lib).isPrefixOf n || (`Estimator_lib).isPrefixOf n

/-- Lean's auxiliary constants (matchers, equation lemmas, …) are not code functions. -/
def isAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" || s.startsWith "eq_"
  | _ => true

/-- The code function a constant belongs to: `f.pure'` is `f`; `Vehicle_lib.` dropped. -/
def codeFn (n : Name) : String :=
  let s := n.toString
  let s := if s.startsWith "Vehicle_lib." then s.drop "Vehicle_lib.".length else s
  let s := if s.endsWith ".pure'" then s.dropEnd ".pure'".length else s
  s.toString

/-- The conclusion of a statement: its type after the leading `∀`s. -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

/-- A wrapper lemma: the memory-side `f … = pure (f.pure' …)`. -/
def isWrapper (ty : Expr) : Bool :=
  match (conclusion ty).eq? with
  | some (_, _, rhs) => rhs.getAppFn.constName? == some ``Pure.pure
  | none => false

/-- The kind of a theorem from its name's last component (`Wrapper` from its statement). -/
def kind (thm : Name) (ty : Expr) : String :=
  let s := match thm with | .str _ s => s | _ => ""
  let has (p : String) := (s.splitOn p).length > 1
  if isWrapper ty then "Wrapper"
  else if s.endsWith "_val" || has "nodup" || s.endsWith "_table" then "Protocol"
  else if has "preserves" then "Invariant"
  else if s.endsWith "_cases" || has "integrator_of_" then "Case"
  else if has "frame" || has "shape" || s.endsWith "_w32" || has "kimax" || has "integrator" || s.endsWith "_run" ||
      s.endsWith "_agree" || s.endsWith "_triple" || s.endsWith "_call" || s.endsWith "_size" || s.endsWith "_run'" ||
      s.endsWith "_state" then
    "Effect"
  else if s.endsWith "_ext" || has "toReal" || has "toNat" || has "toInt" then "Meaning"
  else if has "mono" || has "idem" || has "not_positive" || has "not_negative" || has "or_positive" || has "odd" ||
      has "comm" then "Order"
  else if has "isNaN" && !(has "_of_isNaN") || has "isFinite" || has "divisor" || s.endsWith "_pre" ||
      s.startsWith "pre_of" || has "bridged" || has "layout" || s.endsWith "_upre" || s.startsWith "upre_of" ||
      has "ne_zero" then
    "Safety"
  else if has "_mem" || has "nonneg" || s.endsWith "_le" then "Range"
  else "Case"

def kinds : List String := ["Wrapper", "Case", "Safety", "Range", "Order", "Meaning", "Effect", "Invariant", "Protocol"]

def okAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def audit : CoreM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      -- (the projections of a proof-side `structure` of hypotheses are Lean's, not corpus theorems)
      if (`Corpus).isPrefixOf n && !isAux n && (env.getProjectionFnInfo? n).isNone then
        if let some idx := env.getModuleIdxFor? n then
          let mod := env.header.moduleNames[idx.toNat]!
          if (`Corpus.Code).isPrefixOf mod then thms := thms.push n
  thms := thms.qsort (·.toString < ·.toString)
  let mut viol2 : Array Name := #[]
  let mut viol4 : Array (Name × Array Name) := #[]
  let mut axiomsUsed : NameSet := {}
  let mut cov : Std.HashMap String (Std.HashMap String Nat) := {}
  for n in thms do
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants.filter isCodeConst
    if used.isEmpty then viol2 := viol2.push n
    let axs ← Lean.collectAxioms n
    for a in axs do axiomsUsed := axiomsUsed.insert a
    let bad := axs.filter (fun a => !okAxioms.contains a)
    if !bad.isEmpty then viol4 := viol4.push (n, bad)
    let k := kind n ci.type
    let fns := ((conclusion ci.type).getUsedConstants.filter isCodeConst).map codeFn
    let fns := if fns.isEmpty then used.map codeFn else fns
    let mut seen : List String := []
    for f in fns do
      if seen.contains f then continue
      seen := f :: seen
      let row := cov.getD f {}
      cov := cov.insert f (row.insert k (row.getD k 0 + 1))
  IO.println s!"theorems in Corpus.Code.*: {thms.size}"
  IO.println s!"rule 2 (statement names a code constant): {thms.size - viol2.size} of {thms.size}; violations: {viol2.toList}"
  IO.println s!"rule 4 (axioms): violations: {viol4.toList}"
  IO.println s!"axioms used: {axiomsUsed.toList}"
  let mut totals : Std.HashMap String Nat := {}
  for n in thms do
    if let some ci := env.find? n then
      totals := totals.insert (kind n ci.type) (totals.getD (kind n ci.type) 0 + 1)
  IO.println s!"theorems by kind: {kinds.map fun k => (k, totals.getD k 0)}"
  -- pure leaves (`Vehicle_lib.f.pure'`): covered when at least two theorems name `f` or `f.pure'` in their conclusion
  let mut nPure := 0
  let mut nCov := 0
  let mut nPureV := 0
  let mut nCovV := 0
  for (n, ci) in env.constants.map₁.toList do
    if (`Vehicle_lib).isPrefixOf n then
      if let .str _ "pure'" := n then
        nPure := nPure + 1
        let unit := (conclusion ci.type).isAppOfArity ``Id 1 && (conclusion ci.type).appArg!.isConstOf ``Unit
        if !unit then nPureV := nPureV + 1
        let c := (cov.getD (codeFn n) {}).fold (fun acc _ v => acc + v) 0
        if c ≥ 2 then
          nCov := nCov + 1
          if !unit then nCovV := nCovV + 1
  IO.println s!"pure leaves covered (at least two theorems): {nCov} of {nPure}; returning a value: {nCovV} of {nPureV}"
  IO.println ""
  IO.println s!"| code function | {" | ".intercalate kinds} |"
  IO.println s!"|---|{"".intercalate (kinds.map fun _ => "---|")}"
  let rows := cov.toList.toArray.qsort (·.1 < ·.1)
  for (f, row) in rows do
    let cells := kinds.map fun k => match row.get? k with | some c => toString c | none => ""
    IO.println s!"| `{f}` | {" | ".intercalate cells} |"

#eval audit

end CorpusAudit
