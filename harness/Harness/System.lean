import Harness.Module

/-! Systems: harnesses written in Lean that contain modules and other systems
(docs/9-nesting.md).

A node is a module (one C++ executable) or a system: an interface (params, input, output), an
ordered list of children, one source for every parameter and input field of every child, one
source for every output field of the system, and a contract. Sources are `input f`, `param f`,
`out c f`, `prev c f init` and `const v`. This file holds the declaration, the checks made before
anything runs, the resolved (checked) form the runtime steps, and the canonical wiring text that a
system's code hash is taken of. -/

namespace Harness

/-- A constant with its type, as one record word. -/
structure Word where
  type : FieldType
  bits : UInt32
  deriving Inhabited, BEq, Repr

namespace Word
/-- A binary32 constant. -/
def f32 (x : Float32) : Word := ⟨.f32, x.toBits⟩
/-- A Boolean constant. -/
def bool (b : Bool) : Word := ⟨.bool, if b then 1 else 0⟩
/-- An unsigned 32-bit constant. -/
def u32 (n : Nat) : Word := ⟨.u32, UInt32.ofNat n⟩
/-- A signed 32-bit constant (two's complement). -/
def i32 (n : Int) : Word :=
  ⟨.i32, if n < 0 then 0 - UInt32.ofNat n.natAbs else UInt32.ofNat n.toNat⟩
/-- The word as in files, with its type: `0x3f800000: f32`. -/
def text (w : Word) : String := s!"{w.type.wordText w.bits}: {w.type.name}"
end Word

/-- Where a value comes from (docs/9-nesting.md, "A system's declaration"). -/
inductive Source where
  /-- the system's own input field, this tick -/
  | input (f : String)
  /-- the system's own parameter field -/
  | param (f : String)
  /-- output field `f` of child `c`, this tick (only for children that run after `c`) -/
  | out (c f : String)
  /-- output field `f` of child `c` at the previous tick; `init` at the first tick -/
  | prev (c f : String) (init : Word)
  /-- a constant -/
  | const (v : Word)
  deriving Inhabited, Repr

/-- The source as text (the canonical form the code hash is taken of). -/
def Source.text : Source → String
  | input f => s!"input {f}"
  | param f => s!"param {f}"
  | out c f => s!"out {c} {f}"
  | prev c f i => s!"prev {c} {f} init {i.text}"
  | const v => s!"const {v.text}"

/-- A field fed by a source. -/
structure Wire where
  field : String
  source : Source
  deriving Inhabited, Repr

/-- One child of a system: an instance name, the node it instantiates, and one wire for every
parameter and every input field of that node. -/
structure ChildOf (N : Type) where
  name : String
  node : N
  params : List Wire
  input : List Wire

/-- How an obligation of a composite (an assumption clause of an instance that rests on what its
siblings feed it, `CNode.obligations`) is discharged, as the composite's author states it:
`by` lists the guarantee clauses (`PATH.clause`, PATH an instance path below the system, e.g.
`attitude` or `rate_c/roll`) and the composite's own assumption clauses (`assume.clause`) that
together imply it; `kind` is `guarantee` (neighbors' guarantees alone), `assumption` (with an
assumption of the composite on its parameters or inputs), or `hypothesis` (nothing implies it:
the obligation is a stated hypothesis of the composite about its inner signals, checked every
tick by the monitors, not proved); `note` says why. A documentation record: `harness
obligations NAME --status` prints it and checks that every clause it names exists. -/
structure Discharge where
  path : String
  clause : String
  kind : String
  by_ : List String := []
  note : String := ""

/-- A system's declaration over a node type `N` (closed by `Node`). -/
structure SysOf (N : Type) where
  name : String
  doc : String := ""
  params : Schema
  input : Schema
  output : Schema
  /-- in the order they run within a tick -/
  children : List (ChildOf N)
  /-- one wire for every output field of the system -/
  outputs : List Wire
  contract : Contract
  /-- named regimes a campaign can be restricted to, as for a module -/
  regimes : List Regime := []
  /-- Boolean observations a campaign counts, as for a module -/
  coverage : List Clause := []
  /-- how the system was made: "" by hand, "compose", or an adapter ("rename", "instance",
  "fix", "hide"); an adapter has one child, and `compose` absorbs it into its own wires -/
  origin : String := ""
  /-- a line for `tree` saying what an adapter or a composite did -/
  note : String := ""
  /-- the stack the system belongs to (its folder is STACK/harnesses/NAME); `none`: the one
  flight stack its children other than `sim` share (`Stack.ofChildren`) -/
  stack : Option Stack := none
  /-- how the obligations of the children are discharged (documentation, see `Discharge`) -/
  discharges : List Discharge := []
  /-- step children that do not read each other's outputs of the same tick at the same time
  (`Running.step`, `CSysOf.stepGroups`): each in its own thread, the records exactly those of
  stepping them one after the other, so neither the semantics nor the code hash depends on it -/
  concurrent : Bool := false

/-- A node: a module (one executable) or a system (a harness written in Lean). -/
inductive Node where
  | module (m : Module)
  | system (s : SysOf Node)

/-- A system whose children are nodes. -/
abbrev Sys := SysOf Node
/-- A child of a system. -/
abbrev Child := ChildOf Node

instance : Inhabited Node := ⟨.module default⟩

/-- The system's interface and contract as a module-shaped value (no executable), so that the
module checks, the generator and the contract hashes apply to it unchanged. -/
def SysOf.view (s : SysOf N) (stack : Stack := s.stack.getD .sim) : Module :=
  { name := s.name, doc := s.doc, params := s.params, input := s.input, output := s.output,
    contract := s.contract, exe := "", stack, regimes := s.regimes, coverage := s.coverage }

namespace Node
/-- The node's name. -/
def name : Node → String
  | module m => m.name
  | system s => s.name
/-- `module` or `system`. -/
def kind : Node → String
  | module _ => "module"
  | system _ => "system"
/-- The node's stack: a module's own; a system's declared one, or else the one its children
share (`Stack.ofChildren`). -/
partial def stack : Node → Except String Stack
  | module m => pure m.stack
  | system s => match s.stack with
    | some k => pure k
    | none => do
      let kids ← s.children.mapM fun ch => do
        match ch.node.stack with
        | .ok k => pure (ch.name, k)
        | .error e => throw s!"system {s.name}, child {ch.name}: {e}"
      Stack.ofChildren s.name kids
/-- Interface and contract as a module-shaped value (a system's with its stack resolved, `sim`
when it cannot be). -/
def view : Node → Module
  | module m => m
  | system s => s.view ((Node.system s).stack.toOption.getD .sim)
end Node

/-! ### Helpers for writing declarations -/

/-- The schema with every field name prefixed (documentation kept). -/
def Schema.prefixed (pre : String) (s : Schema) : Schema :=
  s.map fun f => { f with name := pre ++ f.name }

namespace Wire
/-- Every field of `s` fed by the system parameter of the same name with prefix `pre`. -/
def paramsPrefixed (pre : String) (s : Schema) : List Wire :=
  s.toList.map fun f => ⟨f.name, .param (pre ++ f.name)⟩
/-- Child fields fed by system inputs: `(child field, system input)` pairs. -/
def inputs (pairs : List (String × String)) : List Wire :=
  pairs.map fun (f, g) => ⟨f, .input g⟩
/-- System output fields fed by outputs of child `c`: `(system output, child field)` pairs. -/
def outsOf (c : String) (pairs : List (String × String)) : List Wire :=
  pairs.map fun (f, g) => ⟨f, .out c g⟩
end Wire

/-! ### The checked form -/

/-- A source resolved to positions. -/
inductive Src where
  | input (i : Nat)
  | param (i : Nat)
  | out (c i : Nat)
  /-- the `k`-th `prev` wire of the system -/
  | prev (k : Nat)
  | const (w : UInt32)
  deriving Inhabited

/-- A `prev` wire's state: which child output it holds, and its value at the first tick. -/
structure PrevWire where
  child : Nat
  field : Nat
  init : UInt32
  deriving Inhabited

/-- A checked child: its node and its sources resolved, in the order of its schemas. -/
structure CChildOf (N : Type) where
  name : String
  node : N
  params : Array Src
  input : Array Src

/-- A checked system. -/
structure CSysOf (N : Type) where
  decl : Sys
  view : Checked
  /-- the declared stack, or the one the children share -/
  stack : Stack
  children : Array (CChildOf N)
  outputs : Array Src
  prevs : Array PrevWire

/-- A checked node: what the runtime, the campaigns and the ledger work on. -/
inductive CNode where
  | module (c : Checked)
  | system (s : CSysOf CNode)

instance : Inhabited CNode := ⟨.module default⟩
instance : Inhabited (CChildOf CNode) :=
  ⟨{ name := "", node := default, params := #[], input := #[] }⟩

/-- A checked system. -/
abbrev CSys := CSysOf CNode

namespace CNode
/-- Interface and contract, resolved. -/
def view : CNode → Checked
  | module c => c
  | system s => s.view
/-- The node's name. -/
def name (n : CNode) : String := n.view.m.name
/-- `module` or `system`. -/
def kind : CNode → String
  | module _ => "module"
  | system _ => "system"
/-- The stack the node belongs to. -/
def stack : CNode → Stack
  | module c => c.m.stack
  | system s => s.stack
/-- The folder that holds the node and its evidence: STACK/modules/NAME for a module,
STACK/harnesses/NAME for a system. -/
def home : CNode → System.FilePath
  | module c => c.m.stack.name / "modules" / c.m.name
  | system s => s.stack.name / "harnesses" / s.view.m.name
end CNode

/-! ### Checks (docs/9-nesting.md, "What is checked before anything runs") -/

private inductive Role where
  | childParam | childInput | sysOutput

private def Role.text : Role → String
  | childParam => "param" | childInput => "input" | sysOutput => "output"

private def Role.article : Role → String
  | childParam => "a param" | childInput => "an input" | sysOutput => "an output"

private def findIdx? (s : Schema) (n : String) : Option (Nat × FieldType) :=
  (s.toList.zipIdx.find? (·.1.name == n)).map fun (f, i) => (i, f.type)

/-- Resolve the wires of one port: every field of `fields` must have exactly one wire, every
wire must name a field, every source must be allowed for the role and have the field's type.
`pos` is the position of the child being wired (the number of children for system outputs). -/
private def resolveWires (s : Sys) (kidOut : Array (String × Schema)) (pos : Nat) (role : Role)
    (here : String) (fields : Schema) (ws : List Wire) (prevs : Array PrevWire) :
    Except String (Array Src × Array PrevWire) := do
  for w in ws do
    if (findIdx? fields w.field).isNone then
      throw s!"{here}: wire to '{w.field}', which is not {role.article} field"
  let mut prevs := prevs
  let mut out : Array Src := #[]
  for f in fields do
    let at_ := s!"{here} '{f.name}'"
    let src ← match ws.filter (·.field == f.name) with
      | [w] => pure w.source
      | [] => throw s!"{at_}: no source"
      | l => throw s!"{at_}: {l.length} sources, expected exactly one"
    let bad (why : String) : Except String Unit := throw s!"{at_} ← {src.text}: {why}"
    let sameType (what : String) (t : FieldType) : Except String Unit :=
      if t == f.type then pure ()
      else bad s!"{what} is {t.name}, the field is {f.type.name}"
    let child (c : String) : Except String Nat :=
      match s.children.findIdx? (·.name == c) with
      | some j => pure j
      | none => throw s!"{at_} ← {src.text}: system {s.name} has no child '{c}'"
    let childField (j : Nat) (c g : String) : Except String (Nat × FieldType) :=
      match findIdx? kidOut[j]!.2 g with
      | some r => pure r
      | none => throw s!"{at_} ← {src.text}: child {c} has no output field '{g}'"
    match src, role with
    | .input g, .childInput | .input g, .sysOutput =>
      let some (i, t) := findIdx? s.input g
        | throw s!"{at_} ← {src.text}: system {s.name} has no input field '{g}'"
      sameType s!"input {g}" t
      out := out.push (.input i)
    | .param g, .childParam | .param g, .childInput =>
      let some (i, t) := findIdx? s.params g
        | throw s!"{at_} ← {src.text}: system {s.name} has no param field '{g}'"
      sameType s!"param {g}" t
      out := out.push (.param i)
    | .out c g, .childInput | .out c g, .sysOutput =>
      let j ← child c
      if j ≥ pos then
        bad s!"child {c} runs at position {j}, this one at {pos}: `out` needs a child that \
          runs earlier (no instantaneous loop; feedback must use prev)"
      let (i, t) ← childField j c g
      sameType s!"output {c}.{g}" t
      out := out.push (.out j i)
    | .prev c g init, .childInput =>
      let j ← child c
      let (i, t) ← childField j c g
      sameType s!"output {c}.{g}" t
      unless init.type == f.type do bad s!"init is {init.type.name}, the field is {f.type.name}"
      out := out.push (.prev prevs.size)
      prevs := prevs.push ⟨j, i, init.bits⟩
    | .const v, .childParam | .const v, .childInput =>
      sameType "the constant" v.type
      out := out.push (.const v.bits)
    | _, _ => bad s!"this kind of source is not allowed for {role.article} field \
      (docs/9-nesting.md)"
  return (out, prevs)

mutual
/-- Check a node: modules as before; systems by the five checks of docs/9-nesting.md, recursively.
Errors name the system, the child and the field. -/
partial def Node.check : Node → Except String CNode
  | .module m => return .module (← m.check)
  | .system s => return .system (← Sys.check s)

/-- Check a system (see `Node.check`). -/
partial def Sys.check (s : Sys) : Except String CSys := do
  -- 5 (and the field-name rules of 1): the contract against the system's own interface
  let view ← s.view.check
  -- 1: instance names
  for ch in s.children do
    unless Module.isIdent ch.name do
      throw s!"system {s.name}: child instance name '{ch.name}' is not an identifier"
  let names := s.children.map (·.name)
  if names.eraseDups.length != names.length then
    throw s!"system {s.name}: child instance names must be unique ({", ".intercalate names})"
  let kids ← s.children.toArray.mapM fun ch =>
    match Node.check ch.node with
    | .ok c => pure c
    | .error e => throw s!"system {s.name}, child {ch.name}: {e}"
  let kidOut := (s.children.toArray.zip kids).map fun (ch, k) => (ch.name, k.view.m.output)
  -- the stack: declared, or the one the children share
  let stack ← match s.stack with
    | some k => pure k
    | none => Stack.ofChildren s.name ((s.children.zip kids.toList).map fun (ch, k) =>
        (ch.name, k.stack))
  let view := { view with m := { view.m with stack } }
  -- 2, 3, 4: completeness, types, no instantaneous loop
  let mut prevs : Array PrevWire := #[]
  let mut cks : Array (CChildOf CNode) := #[]
  for (ch, j) in s.children.zipIdx do
    let k := kids[j]!
    let here := s!"system {s.name}, child {ch.name}"
    let (ps, pv) ← resolveWires s kidOut j .childParam s!"{here}, param" k.view.m.params
      ch.params prevs
    let (is, pv) ← resolveWires s kidOut j .childInput s!"{here}, input" k.view.m.input
      ch.input pv
    prevs := pv
    cks := cks.push { name := ch.name, node := k, params := ps, input := is }
  let (os, pv) ← resolveWires s kidOut s.children.length .sysOutput s!"system {s.name}, output"
    s.output s.outputs prevs
  return { decl := s, view, stack, children := cks, outputs := os, prevs := pv }
end

/-! ### Instances, wiring text, code hash -/

/-- One instance in a node tree: its path (instance names from the outermost node down), its
node, and its depth (0 for the outermost). -/
structure Inst where
  path : String
  node : CNode
  depth : Nat
  deriving Inhabited

/-- Every instance of the tree, the node itself first, in preorder (the order a tick steps
them). -/
partial def CNode.instances (n : CNode) (path : String) (depth : Nat := 0) : Array Inst :=
  match n with
  | .module _ => #[⟨path, n, depth⟩]
  | .system s => s.children.foldl (init := #[⟨path, n, depth⟩]) fun acc ch =>
    acc ++ ch.node.instances s!"{path}/{ch.name}" (depth + 1)

/-- The distinct modules of the tree (by name), in preorder. -/
def CNode.modules (n : CNode) : Array Module :=
  (n.instances n.name).foldl (init := #[]) fun acc i =>
    match i.node with
    | .module c => if acc.any (·.name == c.m.name) then acc else acc.push c.m
    | .system _ => acc

/-- The wires of a port in the order of the port's schema (canonical, whatever the declaration's
order). -/
def wiresInOrder (fields : Schema) (ws : List Wire) : List (String × Source) :=
  fields.toList.filterMap fun f => (ws.find? (·.field == f.name)).map fun w => (f.name, w.source)

/-- The canonical text of a system's wiring with its children's code hashes, in order: what a
system's code hash is the SHA-256 of. -/
def CSysOf.wiringText (s : CSysOf CNode) (childHashes : Array String) : String := Id.run do
  let d := s.decl
  let mut t := s!"system {d.name}\nparams {d.params.text}\ninput {d.input.text}\n"
  t := t ++ s!"output {d.output.text}\n"
  for (ch, j) in d.children.zipIdx do
    let k := s.children[j]!.node
    t := t ++ s!"child {ch.name}: {k.kind} {k.name} code {childHashes[j]!}\n"
    for (f, src) in wiresInOrder k.view.m.params ch.params do
      t := t ++ s!"  param {f} <- {src.text}\n"
    for (f, src) in wiresInOrder k.view.m.input ch.input do
      t := t ++ s!"  input {f} <- {src.text}\n"
  for (f, src) in wiresInOrder d.output d.outputs do
    t := t ++ s!"output {f} <- {src.text}\n"
  return t

/-- The code hash of a node: for a module the hash its executable reports (`modHash`), for a
system the SHA-256 of its wiring text and its children's code hashes. -/
partial def CNode.codeHash (modHash : Module → String) : CNode → String
  | .module c => modHash c.m
  | .system s =>
    Sha256.hashString (s.wiringText (s.children.map fun ch => ch.node.codeHash modHash))

/-- The nesting as indented lines, down to `depth` levels: each child with its instance name,
node name and kind (and what made it, for an adapter or a composite), and its wires. -/
partial def CNode.treeLines (n : CNode) (indent : String := "") (depth : Nat := 1000) :
    List String :=
  match n with
  | .module _ => []
  | .system s =>
    if depth == 0 then [] else
    let d := s.decl
    let made (k : CNode) : String := match k with
      | .system ks => if ks.decl.note.isEmpty then "" else s!"  [{ks.decl.note}]"
      | .module _ => ""
    let kid (ch : Child) (k : CNode) : List String :=
      [s!"{indent}  {ch.name}: {k.name} ({k.kind}, {k.stack.name}){made k}"] ++
      (wiresInOrder k.view.m.params ch.params).map (fun (f, src) =>
        s!"{indent}      param {f} ← {src.text}") ++
      (wiresInOrder k.view.m.input ch.input).map (fun (f, src) =>
        s!"{indent}      input {f} ← {src.text}") ++
      k.treeLines (indent ++ "    ") (depth - 1)
    (if indent.isEmpty && !d.note.isEmpty then [s!"  [{d.note}]"] else []) ++
    (d.children.zip s.children.toList).flatMap (fun (ch, c) => kid ch c.node) ++
    [s!"{indent}  outputs of {d.name}"] ++
    (wiresInOrder d.output d.outputs).map fun (f, src) => s!"{indent}      {f} ← {src.text}"

end Harness
