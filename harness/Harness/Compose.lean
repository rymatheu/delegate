import Harness.System

/-! Composition by name: operators that make ordinary system nodes, so the checks, the runtime,
the campaigns and the ledger apply to their results unchanged.

* `compose name a b` (and `composeAll name [a, b, …]`): the children run in the order given.
  An input of a later child with the name and type of an earlier child's output is wired
  `out` (same tick); an input of an earlier (or the same) child with the name and type of a
  later child's output is wired `prev`, starting at that output field's `init`. Every other
  input becomes an input of the composite under its own name (one input when several children
  have it); parameters are the union by name; every output of every child is an output.
* `rename n map`, `inst n name shared`, `fix n vals`, `hide n outs`: adapters, one-child systems
  that only route values. `compose` absorbs adapters into its own wires, so they add neither a
  level nor a process.

The composite's contract is computed: its assumption is every assumption clause of a child that
mentions only the composite's parameters and inputs; an assumption clause that mentions a wired
signal is an obligation, to be discharged by the siblings (the monitors check it at the child);
its guarantee is every guarantee clause of the children, except one that mentions an input fed
through `prev` (the composite has no field for the previous tick's value; it stays a child
guarantee). Clause names that clash are prefixed with the child's instance name; identical
clauses are kept once. -/

namespace Harness

/-! ### Expressions -/

namespace Expr

/-- Replace every field by an expression. -/
def mapVars (f : String → Expr) : Expr → Expr
  | var n | ref n _ _ => f n
  | lit b => lit b
  | blit b => blit b
  | add a b => add (a.mapVars f) (b.mapVars f)
  | sub a b => sub (a.mapVars f) (b.mapVars f)
  | mul a b => mul (a.mapVars f) (b.mapVars f)
  | div a b => div (a.mapVars f) (b.mapVars f)
  | neg a => neg (a.mapVars f)
  | abs a => abs (a.mapVars f)
  | le a b => le (a.mapVars f) (b.mapVars f)
  | lt a b => lt (a.mapVars f) (b.mapVars f)
  | eq a b => eq (a.mapVars f) (b.mapVars f)
  | and a b => and (a.mapVars f) (b.mapVars f)
  | or a b => or (a.mapVars f) (b.mapVars f)
  | not a => not (a.mapVars f)
  | finite a => finite (a.mapVars f)

end Expr

/-- The constant as an expression of the contract language (integers read as binary32, as the
language reads integer fields). -/
def Word.expr (w : Word) : Expr :=
  if w.type == .bool then .blit (w.bits != 0) else .lit (Expr.wordToF32 w.type w.bits).toBits

/-- The clause with its fields renamed. -/
def Clause.rename (m : String → String) (c : Clause) : Clause :=
  ⟨c.name, c.expr.mapVars fun n => .var (m n)⟩

/-- The clause with some fields replaced by constants. -/
def Clause.subst (vals : List (String × Word)) (c : Clause) : Clause :=
  ⟨c.name, c.expr.mapVars fun n => match vals.lookup n with
    | some w => w.expr
    | none => .var n⟩

/-- The regime with its fields renamed. -/
def Regime.rename (m : String → String) (r : Regime) : Regime :=
  { r with clauses := r.clauses.map (·.rename m),
           hints := r.hints.map fun
             | .increasing f s lo hi => .increasing (m f) s lo hi
             | .walk f lo hi st => .walk (m f) lo hi st
             | .unit fs c sp st => .unit (fs.map m) c sp st }

/-- What two hints on one field both allow: for two clocks, the same start and the common range
of increments; for any other two, the same hint; `none` when there is none. -/
private def hintMeet : Hint → Hint → Option Hint
  | .increasing f s lo hi, .increasing f' s' lo' hi' =>
    let l := max lo lo'
    let h := min hi hi'
    if f == f' && s == s' && l ≤ h then some (.increasing f s l h) else none
  | a, b => if a.text == b.text then some a else none

/-! ### Adapters -/

private def fieldNames (m : Module) : List String :=
  (m.params ++ m.input ++ m.output).toList.map (·.name)

/-- The one-child system that shows `n` with the kept fields renamed by `vis`, the inner fields
in `consts` fed by constants, and the outputs in `hidden` left out. -/
private def adapter (origin note name : String) (n : Node) (vis : String → String)
    (consts : List (String × Word)) (hidden : List String) (contract : Contract)
    (regimes : List Regime) (coverage : List Clause) : Node :=
  let v := n.view
  let kept (s : Schema) := s.filter fun f => (consts.lookup f.name).isNone
  let ren (s : Schema) := s.map fun f => { f with name := vis f.name }
  let feed (mk : String → Source) (s : Schema) : List Wire :=
    s.toList.map fun f => ⟨f.name, match consts.lookup f.name with
      | some w => .const w
      | none => mk (vis f.name)⟩
  let outs := v.output.filter fun f => !hidden.contains f.name
  .system { name, doc := v.doc, params := ren (kept v.params), input := ren (kept v.input),
            output := ren outs,
            children := [{ name := n.name, node := n, params := feed .param v.params,
                           input := feed .input v.input }],
            outputs := outs.toList.map fun f => ⟨vis f.name, .out n.name f.name⟩,
            contract, regimes, coverage, origin, note }

private def renameAs (origin name note : String) (n : Node) (map : List (String × String)) :
    Except String Node := do
  let names := fieldNames n.view
  for (a, _) in map do
    unless names.contains a do throw s!"{origin} of {n.name}: no field '{a}'"
  let vis (f : String) : String := (map.lookup f).getD f
  let v := n.view
  let c : Contract := { assume := v.contract.assume.map (·.rename vis),
                        guarantee := v.contract.guarantee.map (·.rename vis) }
  return adapter origin note name n vis [] [] c (v.regimes.map (·.rename vis))
    (v.coverage.map (·.rename vis))

/-- The node with interface fields renamed (`(old, new)` pairs); the contract, the regimes and
the coverage follow. -/
def rename (n : Node) (map : List (String × String)) : Except String Node :=
  renameAs "rename" n.name
    s!"rename of {n.name}: {", ".intercalate (map.map fun (a, b) => s!"{a} → {b}")}" n map

/-- The node as an instance `name`: every field prefixed `name_`, except those in `shared`. -/
def inst (n : Node) (name : String) (shared : List String := []) : Except String Node := do
  let names := fieldNames n.view
  for f in shared do
    unless names.contains f do throw s!"instance {name} of {n.name}: no field '{f}'"
  let sh := if shared.isEmpty then "" else s!" except {", ".intercalate shared}"
  renameAs "instance" name s!"instance {name} of {n.name}: fields prefixed {name}_{sh}" n
    (names.filter (!shared.contains ·) |>.map fun f => (f, s!"{name}_{f}"))

/-- Clauses with constants substituted: the closed ones that hold are dropped (returned by
name), a closed one that fails is an error. -/
private def substClauses (what : String) (vals : List (String × Word)) (cs : List Clause) :
    Except String (List Clause × List String) := do
  let mut kept : List Clause := []
  let mut dropped : List String := []
  for c in cs do
    let c' := c.subst vals
    if c'.expr.vars.isEmpty then
      if c'.expr.holds #[] then dropped := dropped ++ [c.name]
      else throw s!"{what}: the constants violate clause {c.name}: {c.expr.print}"
    else kept := kept ++ [c']
  return (kept, dropped)

/-- The node with inputs or parameters fed by constants and removed from its interface. Clauses
get the constants substituted; one that becomes closed and true is dropped (the monitors still
check it at the node); hints on fixed fields are dropped. -/
def fix (n : Node) (vals : List (String × Word)) : Except String Node := do
  let v := n.view
  let what := s!"fix of {n.name}"
  for (f, w) in vals do
    match (v.params ++ v.input).find? (·.name == f) with
    | none => throw s!"{what}: '{f}' is not a parameter or input"
    | some fd =>
      unless fd.type == w.type do
        throw s!"{what}: '{f}' is {fd.type.name}, the constant is {w.type.name}"
  let (a, da) ← substClauses what vals v.contract.assume
  let (g, dg) ← substClauses what vals v.contract.guarantee
  let regimes ← v.regimes.mapM fun r => do
    let (cs, _) ← substClauses s!"{what}, regime {r.name}" vals r.clauses
    pure { r with clauses := cs,
                  hints := r.hints.filter fun h => h.fields.all (vals.lookup · |>.isNone) }
  let (cov, _) ← substClauses what vals v.coverage
  let fixedText := ", ".intercalate (vals.map fun (f, w) => s!"{f} = {w.text}")
  let dropped := da ++ dg
  let dtext := if dropped.isEmpty then "" else
    s!"; held by the constants: {", ".intercalate dropped}"
  return adapter "fix" s!"fix of {n.name}: {fixedText}{dtext}" n.name n id vals []
    { assume := a, guarantee := g } regimes cov

/-- The node with outputs removed from its interface. An output a guarantee clause or a coverage
observation mentions cannot be hidden. -/
def hide (n : Node) (outs : List String) : Except String Node := do
  let v := n.view
  for o in outs do
    unless v.output.any (·.name == o) do throw s!"hide of {n.name}: '{o}' is not an output"
  for c in v.contract.guarantee ++ v.coverage do
    for o in outs do
      if c.expr.vars.contains o then
        throw s!"hide of {n.name}: output '{o}' is mentioned by clause {c.name}: {c.expr.print}"
  return adapter "hide" s!"hide of {n.name}: {", ".intercalate outs}" n.name n id [] outs
    v.contract v.regimes v.coverage

/-- The node with one more regime (over its parameters and inputs). A regime only steers
sampling, so this changes neither the code hash nor the contract. -/
def withRegime (n : Node) (r : Regime) : Node :=
  match n with
  | .module m => .module { m with regimes := m.regimes ++ [r] }
  | .system s => .system { s with regimes := s.regimes ++ [r] }

/-- The node with more assumption clauses over its own parameters and inputs: a fact a
composite needs about how it is used (a parameter bound, a restriction of its commands) that no
child guarantees, stated so that it is not silently open. The contract changes (its hash with
it); a clause naming a field the node does not have is an error. -/
def withAssume (n : Node) (cs : List Clause) : Except String Node := do
  let v := n.view
  let names := (v.params ++ v.input).toList.map (·.name)
  for c in cs do
    for x in c.expr.vars do
      unless names.contains x do
        throw s!"withAssume of {n.name}: clause {c.name} names '{x}', not a parameter or input"
  return match n with
  | .module m => .module { m with contract := { m.contract with assume := m.contract.assume ++ cs } }
  | .system s => .system { s with contract := { s.contract with assume := s.contract.assume ++ cs } }

/-- The system with more guarantee clauses over its own interface: what the composite as a
whole is to achieve that no child guarantees (a property of the closed loop, such as the
separation of two vehicles), monitored at every tick like any other clause. In the formal link
such a clause is not derived from the children: it is an `OpenCover` hypothesis ("uncovered").
The contract changes (its hash with it); a clause naming a field the system does not have is an
error; a module is returned as it is. -/
def withGuarantee (n : Node) (cs : List Clause) : Except String Node := do
  let v := n.view
  let names := (v.params ++ v.input ++ v.output).toList.map (·.name)
  for c in cs do
    for x in c.expr.vars do
      unless names.contains x do
        throw s!"withGuarantee of {n.name}: clause {c.name} names '{x}', not a field"
  return match n with
  | .system s => .system { s with contract := { s.contract with
      guarantee := s.contract.guarantee ++ cs } }
  | m => m

/-- The system with its independent children stepped at the same time (`SysOf.concurrent`,
`CSysOf.stepGroups`): children that do not read each other's outputs of the same tick, such as
two vehicles' stacks, each in its own thread. The records, the contract and the code hash are
those of stepping them one after the other. -/
def concurrently (n : Node) : Node :=
  match n with
  | .system s => .system { s with concurrent := true }
  | m => m

/-- The system with its obligations' discharges stated (`Discharge`); a module is returned as
it is. -/
def withDischarges (n : Node) (ds : List Discharge) : Node :=
  match n with
  | .system s => .system { s with discharges := s.discharges ++ ds }
  | m => m

/-- The node with initial values declared on output fields: the word a `prev` wire made by
`compose` from that output holds at the first tick. A declaration only; the code is unchanged. -/
def withInit (n : Node) (vals : List (String × Word)) : Except String Node := do
  let v := n.view
  for (f, w) in vals do
    match v.output.find? (·.name == f) with
    | none => throw s!"withInit of {n.name}: '{f}' is not an output"
    | some fd =>
      unless fd.type == w.type do
        throw s!"withInit of {n.name}: '{f}' is {fd.type.name}, the value is {w.type.name}"
  let set (s : Schema) : Schema := s.map fun f => match vals.lookup f.name with
    | some w => { f with init := w.bits }
    | none => f
  return match n with
  | .module m => .module { m with output := set m.output }
  | .system s => .system { s with output := set s.output }

/-! ### Composition -/

/-- A child of a composite after its adapters are absorbed: its instance name, the node that
becomes the child, its visible interface and contract, the source of every inner parameter and
input in terms of visible fields (`param g`, `input g`, `const w`), and the inner field of every
visible output. -/
private structure Part where
  inst : String
  node : Node
  view : Module
  feedP : List (String × Source)
  feedI : List (String × Source)
  outs : List (String × String)

private instance : Inhabited Part :=
  ⟨{ inst := "", node := default, view := default, feedP := [], feedI := [], outs := [] }⟩

/-- Absorb a chain of adapters. -/
private partial def absorb (n : Node) : Part :=
  let plain : Part :=
    { inst := n.name, node := n, view := n.view,
      feedP := n.view.params.toList.map fun f => (f.name, .param f.name),
      feedI := n.view.input.toList.map fun f => (f.name, .input f.name),
      outs := n.view.output.toList.map fun f => (f.name, f.name) }
  match n with
  | .system s =>
    match s.origin, s.children with
    | "", _ | "compose", _ => plain
    | _, [ch] =>
      let a := absorb ch.node
      let tr (src : Source) : Source := match src with
        | .input h => ((ch.input.find? (·.field == h)).map (·.source)).getD src
        | .param h => ((ch.params.find? (·.field == h)).map (·.source)).getD src
        | other => other
      { inst := s.name, node := a.node, view := s.view,
        feedP := a.feedP.map fun (f, src) => (f, tr src),
        feedI := a.feedI.map fun (f, src) => (f, tr src),
        outs := s.outputs.filterMap fun w => match w.source with
          | .out _ h => (a.outs.lookup h).map (w.field, ·)
          | _ => none }
    | _, _ => plain
  | .module _ => plain

/-- Clause names made unique: a name shared by clauses that differ is prefixed with each one's
instance name; identical clauses are kept once. -/
private def uniqueNames (items : List (String × Bool × Clause)) : List (Bool × Clause) :=
  let key (k : Bool) (c : Clause) := (k, c.text)
  let named := items.map fun (i, k, c) =>
    let clash := items.any fun (_, k', c') => c'.name == c.name && key k' c' != key k c
    (k, if clash then { c with name := s!"{i}_{c.name}" } else c)
  named.foldl (init := []) fun acc (k, c) =>
    if acc.any fun (k', c') => k' == k && c'.text == c.text then acc else acc ++ [(k, c)]

/-- Compose the nodes: they run in the order given (see the file's comment for the rules). The
composite's stack is `stack`, or else the one flight stack its children other than `sim` share
(an error when they are from both: then `stack` is required). -/
def composeAll (name : String) (nodes : List Node) (stack : Option Stack := none) :
    Except String Node := do
  let parts := (nodes.map absorb).toArray
  let instNames := parts.toList.map (·.inst)
  if instNames.eraseDups.length != instNames.length then
    throw s!"compose {name}: instance names must be unique ({", ".intercalate instNames}); \
      use inst to name them"
  -- outputs, by visible name
  let mut outOwner : Array (String × Nat × Field) := #[]
  for (p, i) in parts.toList.zipIdx do
    for f in p.view.output do
      if let some (_, j, _) := outOwner.find? (·.1 == f.name) then
        throw s!"compose {name}: output '{f.name}' of {parts[j]!.inst} and of {p.inst}; \
          rename one first"
      outOwner := outOwner.push (f.name, i, f)
  -- the source of every visible input of every part
  let mut cinputs : Array (Field × String) := #[]
  let mut srcOf : Array (List (String × Source)) := #[]
  let mut prevFed : Array (List String) := #[]
  for (p, i) in parts.toList.zipIdx do
    let mut l : List (String × Source) := []
    let mut pf : List String := []
    for f in p.view.input do
      match outOwner.find? (·.1 == f.name) with
      | some (_, j, o) =>
        unless o.type == f.type do
          throw s!"compose {name}: input '{f.name}' of {p.inst} is {f.type.name}, output \
            '{f.name}' of {parts[j]!.inst} is {o.type.name}"
        let inner := (parts[j]!.outs.lookup f.name).getD f.name
        if j < i then l := l ++ [(f.name, .out parts[j]!.inst inner)]
        else
          l := l ++ [(f.name, .prev parts[j]!.inst inner ⟨o.type, o.init⟩)]
          pf := pf ++ [f.name]
      | none =>
        match cinputs.find? (·.1.name == f.name) with
        | some (g, who) =>
          unless g.type == f.type do
            throw s!"compose {name}: input '{f.name}' is {g.type.name} in {who} and \
              {f.type.name} in {p.inst}"
        | none => cinputs := cinputs.push (f, p.inst)
        l := l ++ [(f.name, .input f.name)]
    srcOf := srcOf.push l
    prevFed := prevFed.push pf
  -- parameters, the union by name
  let mut cparams : Array (Field × String) := #[]
  for p in parts do
    for f in p.view.params do
      match cparams.find? (·.1.name == f.name) with
      | some (g, who) =>
        unless g.type == f.type do
          throw s!"compose {name}: parameter '{f.name}' is {g.type.name} in {who} and \
            {f.type.name} in {p.inst}"
      | none => cparams := cparams.push (f, p.inst)
  for (o, j, _) in outOwner do
    if let some (_, who) := cinputs.find? (·.1.name == o) then
      throw s!"compose {name}: output '{o}' of {parts[j]!.inst} has the name of an input of \
        {who}; rename one first"
    if let some (_, who) := cparams.find? (·.1.name == o) then
      throw s!"compose {name}: output '{o}' of {parts[j]!.inst} has the name of a parameter \
        of {who}; rename one first"
  let cfields := (cparams ++ cinputs).toList.map (·.1.name)
  let within (c : Clause) : Bool := c.expr.vars.all cfields.contains
  -- children and outputs
  let children : List Child := parts.toList.zipIdx.map fun (p, i) =>
    let tr (src : Source) : Source := match src with
      | .input g => ((srcOf[i]!).lookup g).getD src
      | other => other
    { name := p.inst, node := p.node, params := p.feedP.map fun (f, s) => ⟨f, s⟩,
      input := p.feedI.map fun (f, s) => ⟨f, tr s⟩ }
  let outputs : List Wire := outOwner.toList.map fun (o, j, _) =>
    ⟨o, .out parts[j]!.inst ((parts[j]!.outs.lookup o).getD o)⟩
  -- the contract
  let mut items : List (String × Bool × Clause) := []
  let mut childOnly : List String := []
  for (p, i) in parts.toList.zipIdx do
    for c in p.view.contract.assume do
      if within c then items := items ++ [(p.inst, true, c)]
    for c in p.view.contract.guarantee do
      if c.expr.vars.any (prevFed[i]!).contains then
        childOnly := childOnly ++ [s!"{p.inst}.{c.name}"]
      else items := items ++ [(p.inst, false, c)]
  let named := uniqueNames items
  let contract : Contract :=
    { assume := named.filterMap fun (k, c) => if k then some c else none,
      guarantee := named.filterMap fun (k, c) => if k then none else some c }
  -- regimes: by name, the conjunction of the children's clauses over the composite's fields
  let rnames := (parts.toList.flatMap fun p => p.view.regimes.map (·.name)).eraseDups
  let mut regimes : List Regime := []
  for rn in rnames do
    let mut cs : List (String × Bool × Clause) := []
    let mut hints : List Hint := []
    let mut docs : List String := []
    let mut dropped : List String := []
    for p in parts do
      let some r := p.view.regimes.find? (·.name == rn) | continue
      if !r.doc.isEmpty && !docs.contains r.doc then docs := docs ++ [r.doc]
      for c in r.clauses do
        if within c then cs := cs ++ [(p.inst, true, c)]
        else dropped := dropped ++ [s!"{p.inst}.{c.name}"]
      for h in r.hints do
        let fs := h.fields
        if !(fs.all fun f => cinputs.any (·.1.name == f)) then
          dropped := dropped ++ [s!"{p.inst} hint on {", ".intercalate fs}"]
        else match hints.find? (fun h' => h'.fields.any fs.contains) with
          | some h' =>
            -- two hints on one input: their intersection (an error only when it is empty)
            match hintMeet h' h with
            | some m => hints := hints.map fun x => if x.text == h'.text then m else x
            | none =>
              throw s!"compose {name}, regime {rn}: two hints on '{", ".intercalate fs}' with \
                nothing in common: \
                {h'.text}; {h.text}"
          | none => hints := hints ++ [h]
    let dtext := if dropped.isEmpty then "" else
      s!" (dropped, on wired signals: {", ".intercalate dropped})"
    regimes := regimes ++ [{ name := rn, doc := "; ".intercalate docs ++ dtext,
                             clauses := (uniqueNames cs).map (·.2), hints }]
  let coverage := (uniqueNames (parts.toList.zipIdx.flatMap fun (p, i) =>
    p.view.coverage.filterMap fun c =>
      if c.expr.vars.any (prevFed[i]!).contains then none else some (p.inst, false, c))).map (·.2)
  let only := if childOnly.isEmpty then "" else
    s!"; child guarantees on prev-fed inputs, not in the composite's: {", ".intercalate childOnly}"
  return .system {
    name, doc := s!"composite of {", ".intercalate instNames}",
    params := cparams.map (·.1), input := cinputs.map (·.1), output := outOwner.map (·.2.2),
    children, outputs, contract, regimes, coverage, origin := "compose", stack,
    note := s!"composite of {" then ".intercalate instNames}{only}" }

/-- Compose two nodes: `a` runs first, then `b`. -/
def compose (name : String) (a b : Node) : Except String Node := composeAll name [a, b]

/-! ### Obligations -/

/-- An assumption clause of an instance that rests on what its siblings (or constants) feed it,
not on its parent's assumption: the fields it mentions that are wired, with their sources. -/
structure Obligation where
  path : String
  clause : String
  fields : List (String × String)

/-- The obligations of every instance below the node, in preorder. -/
partial def CNode.obligations (n : CNode) (path : String) : Array Obligation :=
  match n with
  | .module _ => #[]
  | .system s =>
    (s.decl.children.zip s.children.toList).toArray.flatMap fun (ch, cc) =>
      let p := s!"{path}/{ch.name}"
      let wired (f : String) : Option String :=
        match (ch.params ++ ch.input).find? (·.field == f) with
        | some ⟨_, src@(.out ..)⟩ | some ⟨_, src@(.prev ..)⟩ | some ⟨_, src@(.const _)⟩ =>
          some src.text
        | _ => none
      let own := cc.node.view.m.contract.assume.toArray.filterMap fun c =>
        let ws := c.expr.vars.filterMap fun f => (wired f).map (f, ·)
        if ws.isEmpty then none else some { path := p, clause := c.name, fields := ws }
      own ++ cc.node.obligations p

end Harness
