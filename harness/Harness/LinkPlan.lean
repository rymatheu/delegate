import Harness.LinkCheck
import Harness.Compose

/-! # The link theorem for a system node (docs/10-formal-link.md, "Theorems", 4)

For a checked node, the plan says how each clause the theorem needs is obtained:

* an assumption clause of a child is the composite's own assumption clause read through the
  wires (`own`, proved by `transportOK`), or an obligation: discharged by the range checker
  (`checked`, proved), stated in the discharge table and not checkable (`cited`: a `CitedDis`
  hypothesis), or open (`open_`: an `OpenDis` hypothesis);
* a guarantee clause of the composite is a child's guarantee read through the wires (`copy`,
  proved), or not (`open_`: an `OpenCover` hypothesis).

`goodEv` turns the plan into an `Algebra.Ev` tree for `Good exe n`, and `linkEv` into one for
`Beh exe n ⊨ (nodeStep n).always`, so `Ev.sound` applies. Its leaves are the leaf claims of the
modules, `FloatFacts`, and the assumed and open hypotheses; every inner node is a Lean proof
(the checkers' soundness theorems, `citedDis_loop`, `sound_implements`). The tree is computed by
running the checkers on the checked node (compiled code: the node comes from `Node.check`, which
is `partial`, so the kernel cannot evaluate it); its type is checked by Lean for every node. -/

namespace Harness.Link

open Harness

/-! ## Evidence records -/

/-- A leaf of the link's evidence tree. -/
inductive LinkRec where
  /-- the IEEE facts the checkers use -/
  | floatFacts
  /-- a module's leaf claim: its executable meets its contract (what campaigns test) -/
  | leafClaim (module : String)
  /-- a discharge implication stated in the table, not proved: `CitedDis exe ⟦sys⟧ i k cites` -/
  | assumed (sys : String) (i k : Nat) (inst clause : String) (cites : String) (by_ : List String)
  /-- an obligation nothing discharges: `OpenDis exe ⟦sys⟧ i k` -/
  | openObl (sys : String) (i k : Nat) (inst clause : String) (why : String)
  /-- a guarantee of a system that is not a copy of a child's: `OpenCover exe ⟦sys⟧ k` -/
  | openCover (sys : String) (k : Nat) (clause : String)
  /-- the tree is deeper than the evaluation fuel (does not happen below depth 1000) -/
  | fuel (path : String)
  deriving Repr, Inhabited

abbrev LEv := Algebra.Ev LinkRec

/-- A claim proved in Lean: evidence with no leaves. -/
def proved {P : Prop} (h : P) : LEv P :=
  .derive (.all (n := 0) (Q := fun _ => True) (fun i => i.elim0)) (fun _ => h)

/-- The leaves of an evidence tree, in order. -/
def leaves {P : Prop} : LEv P → List LinkRec
  | .leaf _ r => [r]
  | .derive E _ => leaves E
  | .and E₁ E₂ => leaves E₁ ++ leaves E₂
  | .all (n := n) E => (List.finRange n).flatMap fun i => leaves (E i)
  | .alt E₁ E₂ => leaves E₁ ++ leaves E₂

/-! ## The plan -/

/-- How an assumption clause of a child is obtained. -/
inductive AAcct where
  | own (q : Nat)
  | checked (cs : List Cite) (by_ : List String)
  | cited (cs : List Cite) (by_ : List String)
  | open_ (why : String)
  deriving Repr, Inhabited

/-- How a guarantee clause of a system is obtained. -/
inductive GAcct where
  | copy (i k : Nat)
  | open_
  deriving Repr, Inhabited

/-- Whether a child input of `s` is fed by a `prev` wire from child `j`. -/
def prevFrom (s : CSys) (i j : Nat) : Bool :=
  (s.children[i]!).input.any fun src => match src with
    | .prev m => (s.prevs[m]!).child == j
    | _ => false

/-- A path of instance names below a node, as child indices. -/
def walkPath : CNode → List String → Option (CNode × List Nat)
  | n, [] => some (n, [])
  | .module _, _ :: _ => none
  | .system s, nm :: rest => do
    let j ← s.children.findIdx? (·.name == nm)
    let (m, p) ← walkPath (child s j) rest
    pure (m, j :: p)

/-- A citation of a discharge table (`assume.NAME` or `PATH.NAME`) for an obligation of child
`i`, with the tick at which the wire delivers it: the same tick for a child scheduled before
`i` that feeds it no `prev` wire, the tick before otherwise. -/
def resolveCite (s : CSys) (i : Nat) (txt : String) : Option Cite :=
  match txt.splitOn "." with
  | ["assume", c] => (s.view.assume.findIdx? (·.name == c)).map Cite.assume
  | [ip, c] =>
    match ip.splitOn "/" with
    | j0 :: rest => do
      let j ← s.children.findIdx? (·.name == j0)
      let (node, path) ← walkPath (child s j) rest
      let k ← node.view.guarantee.findIdx? (·.name == c)
      let lag := if j < i && !prevFrom s i j then 0 else 1
      pure (.guar j path k lag)
    | [] => none
  | _ => none

/-- The account of assumption clause `k` of child `i`. -/
def acctOf (s : CSys) (i k : Nat) : AAcct :=
  let e := ((child s i).view.assume[k]!).expr
  let nm := ((child s i).view.assume[k]!).name
  let own := (List.range s.view.assume.size).find? fun q =>
    transportOK s (.kid i 0) e .sys (s.view.assume[q]!).expr
  match own with
  | some q => .own q
  | none =>
    -- a clause on constants (and initial values) alone, such as one `fix` dropped as held by
    -- its constants, needs no citation
    if rangeCheck s i k [] then .checked [] ["the wired constants"] else
    -- implied by the composite's assumption (a hand-written system states combined clauses)
    let all := (List.range s.view.assume.size).map Cite.assume
    if rangeCheck s i k all then .checked all ["the composite's assumption"] else
    let chName := (s.children[i]!).name
    match s.decl.discharges.find? (fun d => d.path == chName && d.clause == nm) with
    | none => .open_ "no discharge stated"
    | some d =>
      if d.kind == "hypothesis" then .open_ s!"stated as a hypothesis: {d.note}"
      else if d.kind == "constant" then
        .open_ "stated as held by its wired constants, but the checker does not prove it from them"
      else
        let cs := d.by_.map (resolveCite s i)
        if cs.any (·.isNone) then .open_ s!"a cited clause does not resolve: {d.by_}"
        else
          let cs := cs.filterMap id
          if !(cs.all (citeOK s i)) then .open_ s!"a citation is not well placed: {d.by_}"
          else if rangeCheck s i k cs then .checked cs d.by_ else .cited cs d.by_

/-- The account of guarantee clause `k` of system `s`. -/
def gacctOf (s : CSys) (k : Nat) : GAcct :=
  let e := (s.view.guarantee[k]!).expr
  let found := (List.range s.children.size).findSome? fun i =>
    ((List.range (child s i).view.guarantee.size).find? fun k' =>
      transportOK s (.kid i 0) ((child s i).view.guarantee[k']!).expr .sys e).map (i, ·)
  match found with
  | some (i, k') => .copy i k'
  | none => .open_

/-- Citations as Lean terms. -/
def citesText (cs : List Cite) : String :=
  "[" ++ ", ".intercalate (cs.map fun
    | .assume q => s!".assume {q}"
    | .guar j p k lag => s!".guar {j} {p} {k} {lag}") ++ "]"

/-! ## Evidence for one clause -/

theorem all_citeOK {s : CSys} {i : Nat} {cs : List Cite} (h : cs.all (citeOK s i) = true) :
    ∀ c, c ∈ cs → citeOK s i c = true := fun c hc => List.all_eq_true.mp h c hc

/-- Evidence that assumption clause `k` of child `i` is discharged (loop form). -/
def discEv (exe : Checked → Trace → Prop) (s : CSys) (path : String) (i k : Nat) :
    LEv (OpenDis exe s i k) :=
  let nm := ((child s i).view.assume[k]!).name
  let p := s!"{path}/{(s.children[i]!).name}"
  let openLeaf (why : String) : LEv (OpenDis exe s i k) := .leaf _ (.openObl path i k p nm why)
  let citedLeaf (cs : List Cite) (by_ : List String) : LEv (OpenDis exe s i k) :=
    if h : cs.all (citeOK s i) = true then
      .derive (.leaf (CitedDis exe s i k cs) (.assumed path i k p nm (citesText cs) by_))
        (fun hc => citedDis_loop hc (all_citeOK h))
    else openLeaf "a citation is not well placed"
  match acctOf s i k with
  | .own q =>
    if h : q < s.view.assume.size ∧
        transportOK s (.kid i 0) ((child s i).view.assume[k]!).expr .sys
          (s.view.assume[q]!).expr = true then
      .derive (.leaf FloatFacts .floatFacts) (fun ff => own_loopDis ff h.1 h.2)
    else openLeaf "transport failed"
  | .checked cs by_ =>
    if h : rangeCheck s i k cs = true ∧ cs.all (citeOK s i) = true then
      .derive (.leaf FloatFacts .floatFacts)
        (fun ff => citedDis_loop (rangeCheck_sound ff h.1) (all_citeOK h.2))
    else citedLeaf cs by_
  | .cited cs by_ => citedLeaf cs by_
  | .open_ why => openLeaf why

/-- Evidence that guarantee clause `k` of the system is covered. -/
def coverEv (exe : Checked → Trace → Prop) (s : CSys) (path : String) (k : Nat) :
    LEv (OpenCover exe s k) :=
  let openLeaf : LEv (OpenCover exe s k) := .leaf _ (.openCover path k (s.view.guarantee[k]!).name)
  match gacctOf s k with
  | .copy i k' =>
    if h : i < s.children.size ∧ k' < (child s i).view.guarantee.size ∧
        transportOK s (.kid i 0) ((child s i).view.guarantee[k']!).expr .sys
          (s.view.guarantee[k]!).expr = true then
      .derive (.leaf FloatFacts .floatFacts) (fun ff => copy_cover ff h.1 h.2.1 h.2.2)
    else openLeaf
  | .open_ => openLeaf

theorem sysOK_of {exe : Checked → Trace → Prop} {s : CSys}
    (hA : ∀ i, i < s.children.size → ∀ k, k < (child s i).view.assume.size → OpenDis exe s i k)
    (hG : ∀ k, k < s.view.guarantee.size → OpenCover exe s k) : SysOK exe s :=
  fun r hb => ⟨fun i hi k hk => hA i hi k hk r hb, fun k hk => hG k hk r hb⟩

/-- Evidence that the system's wiring and contracts are `SysOK`. -/
def sysEv (exe : Checked → Trace → Prop) (s : CSys) (path : String) : LEv (SysOK exe s) :=
  .derive
    (.and
      (.all (n := s.children.size)
        (Q := fun i => ∀ k, k < (child s i).view.assume.size → OpenDis exe s i k)
        fun i => .all (n := (child s i).view.assume.size) (Q := fun k => OpenDis exe s i k)
          fun k => discEv exe s path i k)
      (.all (n := s.view.guarantee.size) (Q := fun k => OpenCover exe s k)
        fun k => coverEv exe s path k))
    (fun h => sysOK_of h.1 h.2)

/-- Evidence that the tree is `Good` (structural on the fuel, which bounds the depth). -/
def goodEv (exe : Checked → Trace → Prop) : Nat → String → (n : CNode) → LEv (Good exe n)
  | 0, path, _ => .leaf _ (.fuel path)
  | _ + 1, _, .module c => .derive (.leaf (LeafClaim exe c) (.leafClaim c.m.name)) Good.module
  | fuel + 1, path, .system s =>
    .derive
      (.and
        (.all (n := s.children.size) (Q := fun i => Good exe (child s i))
          fun i => goodEv exe fuel s!"{path}/{(s.children[i]!).name}" (child s i))
        (sysEv exe s path))
      (fun h => Good.system h.1 h.2)

/-- The link theorem's evidence for a node: `Beh exe n ⊨ (nodeStep n).always`. -/
def linkEv (exe : Checked → Trace → Prop) (n : CNode) :
    LEv (Algebra.Implements (Beh exe n) (nodeStep n).always) :=
  .derive (goodEv exe 1000 n.name n) sound_implements

/-- Under a policy whose accepted records are true, a supported link tree proves the link. -/
theorem linkEv_sound {exe : Checked → Trace → Prop} {n : CNode} {T : LinkRec → Prop}
    (hf : (linkEv exe n).faithful T) (hs : (linkEv exe n).supported T) :
    Algebra.Implements (Beh exe n) (nodeStep n).always :=
  Algebra.Ev.sound (linkEv exe n) hf hs

/-! ## Counting and printing (run natively) -/

/-- What the plan of a tree adds up to. -/
structure Counts where
  /-- module instances, and the distinct modules among them -/
  instances : Nat := 0
  modules : List String := []
  systems : Nat := 0
  /-- child assumption clauses that are the composite's own (transport, proved) -/
  own : Nat := 0
  /-- of those, obligations by `CNode.obligations` (a constant feeds them) -/
  ownObligations : Nat := 0
  /-- composite guarantees copied from a child (transport, proved) -/
  copies : Nat := 0
  /-- discharge implications proved by the range checker: from the table's citations, from the
  wired constants alone, from the composite's assumption -/
  checked : Nat := 0
  checkedConst : Nat := 0
  checkedAssume : Nat := 0
  /-- discharge implications stated in a table, assumed -/
  assumed : Nat := 0
  /-- obligations (in the sense of `CNode.obligations`) with no usable discharge -/
  open_ : Nat := 0
  /-- other child assumptions (on the system's own fields) its assumption does not give -/
  openOther : Nat := 0
  /-- composite guarantees that are not a copy of a child's -/
  openCover : Nat := 0
  deriving Inhabited

def Counts.add (a b : Counts) : Counts :=
  { instances := a.instances + b.instances,
    modules := b.modules.foldl (fun l m => if l.contains m then l else l ++ [m]) a.modules,
    systems := a.systems + b.systems, own := a.own + b.own,
    ownObligations := a.ownObligations + b.ownObligations, copies := a.copies + b.copies,
    checked := a.checked + b.checked, checkedConst := a.checkedConst + b.checkedConst,
    checkedAssume := a.checkedAssume + b.checkedAssume, assumed := a.assumed + b.assumed,
    open_ := a.open_ + b.open_, openOther := a.openOther + b.openOther,
    openCover := a.openCover + b.openCover }

/-- Whether a field of the clause is fed by `out`, `prev` or `const` (an obligation in the sense
of `CNode.obligations`). -/
def isObligation (s : CSys) (i : Nat) (e : Expr) : Bool :=
  let ch := s.children[i]!
  let v := (child s i).view.m
  let rec slots : Expr → List Nat
    | .ref _ k _ => [k]
    | .var _ | .lit _ | .blit _ => []
    | .add a b | .sub a b | .mul a b | .div a b | .le a b | .lt a b | .eq a b | .and a b
    | .or a b => slots a ++ slots b
    | .neg a | .abs a | .not a | .finite a => slots a
  (slots e).any fun k =>
    let src := if k < v.params.size then ch.params[k]?
      else if k < v.params.size + v.input.size then ch.input[k - v.params.size]? else none
    match src with
    | some (.out ..) | some (.prev _) | some (.const _) => true
    | _ => false

/-- One line per clause the theorem needs, and the counts, for one system. -/
def sysLines (s : CSys) (path : String) : List String × Counts := Id.run do
  let mut ls : List String := []
  let mut c : Counts := { systems := 1 }
  for i in List.range s.children.size do
    let ch := s.children[i]!
    let v := (child s i).view
    for k in List.range v.assume.size do
      let cl := v.assume[k]!
      let at_ := s!"{path}/{ch.name}.{cl.name}"
      match acctOf s i k with
      | .own q =>
        c := { c with own := c.own + 1,
                      ownObligations := c.ownObligations + (if isObligation s i cl.expr then 1 else 0) }
        ls := ls ++ [s!"  own      {at_} = assume.{(s.view.assume[q]!).name} through the wires"]
      | .checked _ by_ =>
        c := match by_ with
          | ["the wired constants"] => { c with checkedConst := c.checkedConst + 1 }
          | ["the composite's assumption"] => { c with checkedAssume := c.checkedAssume + 1 }
          | _ => { c with checked := c.checked + 1 }
        ls := ls ++ [s!"  PROVED   {at_} by the range checker from {", ".intercalate by_}"]
      | .cited _ by_ =>
        c := { c with assumed := c.assumed + 1 }
        ls := ls ++ [s!"  STATED   {at_} from {", ".intercalate by_} (CitedDis, a hypothesis)"]
      | .open_ why =>
        if isObligation s i cl.expr then
          c := { c with open_ := c.open_ + 1 }
          ls := ls ++ [s!"  OPEN     {at_}: {why} (OpenDis)"]
        else
          c := { c with openOther := c.openOther + 1 }
          ls := ls ++ [s!"  OPEN     {at_}: on the system's own fields, not implied by its \
            assumption (OpenDis; not an obligation of `obligations`)"]
  for k in List.range s.view.guarantee.size do
    let g := s.view.guarantee[k]!
    match gacctOf s k with
    | .copy i k' =>
      c := { c with copies := c.copies + 1 }
      ls := ls ++ [s!"  copy     {path}.{g.name} = {path}/{(s.children[i]!).name}.\
        {((child s i).view.guarantee[k']!).name}"]
    | .open_ =>
      c := { c with openCover := c.openCover + 1 }
      ls := ls ++ [s!"  OPEN     {path}.{g.name}: not a child's guarantee (OpenCover)"]
  return (ls, c)

/-- The plan of the whole tree (structural on the fuel). -/
def treeLines : Nat → String → CNode → List String × Counts
  | 0, path, _ => ([s!"  (fuel exhausted at {path})"], {})
  | _ + 1, _, .module c => ([], { instances := 1, modules := [c.m.name] })
  | fuel + 1, path, .system s =>
    let (own, c) := sysLines s path
    (List.range s.children.size).foldl (init := ([s!"system {path}"] ++ own, c)) fun (ls, c) i =>
      let (ls', c') := treeLines fuel s!"{path}/{(s.children[i]!).name}" (child s i)
      (ls ++ ls', c.add c')

/-- The account of every assumption clause of every instance below the node, by instance path
and clause name (the paths of `CNode.obligations`), structural on the fuel. -/
def accounts : Nat → String → CNode → List (String × String × AAcct)
  | 0, _, _ => []
  | _ + 1, _, .module _ => []
  | fuel + 1, path, .system s =>
    (List.range s.children.size).flatMap fun i =>
      let p := s!"{path}/{(s.children[i]!).name}"
      ((List.range (child s i).view.assume.size).map fun k =>
        (p, ((child s i).view.assume[k]!).name, acctOf s i k)) ++
      accounts fuel p (child s i)

/-- The status line. -/
def Counts.summary (c : Counts) : String :=
  let m := c.checked + c.checkedConst + c.checkedAssume
  let detail := if c.checkedConst + c.checkedAssume == 0 then "" else
    s!" ({c.checked} from the discharge table, {c.checkedConst} from wired constants, \
      {c.checkedAssume} from the composite's assumption)"
  let other := if c.openOther == 0 then "" else
    s!", {c.openOther} other child assumptions not implied by the system's assumption"
  let cover := if c.openCover == 0 then "" else
    s!", {c.openCover} system guarantees not derived from the children's"
  s!"the link theorem applies (Harness/Link.lean `sound`, evidence `linkEv`) with \
    {c.modules.length} leaf hypotheses ({c.instances} module instances), \
    {m} discharge implications proved by the checker{detail}, {c.assumed} stated \
    (hypotheses), \
    {c.open_} open obligations{other}{cover}; \
    {c.own + c.copies} clauses carried by the wires and proved ({c.own} child assumptions \
    from the composite's, {c.ownObligations} of them obligations on constants; {c.copies} \
    guarantees copied)"

/-- The statement of the link theorem for the node, with its named hypotheses. `⟦p⟧` stands for
the checked instance at path `p` (its `CSys` for a system, its `Checked` for a module), which
only compiled code can compute (`Node.check` is `partial`); the numbers are child and clause
indices; the hypothesis types are the definitions of `Harness/Link.lean`. -/
def statement (n : CNode) : String := Id.run do
  let (_, c) := treeLines 1000 n.name n
  let ev := linkEv (fun _ _ => True) n
  let ls := leaves ev
  let mut hs : List String := []
  let mut seen : List String := []
  for r in ls do
    let h := match r with
      | .floatFacts => "(ff : FloatFacts)"
      | .leafClaim m => s!"(«leaf {m}» : LeafClaim exe ⟦{m}⟧)"
      | .assumed sys i k p cl cs by_ =>
        s!"(«dis {p}.{cl}» : CitedDis exe ⟦{sys}⟧ {i} {k} {cs})  -- from {", ".intercalate by_}"
      | .openObl sys i k p cl _ => s!"(«open {p}.{cl}» : OpenDis exe ⟦{sys}⟧ {i} {k})"
      | .openCover sys k cl => s!"(«cover {sys}.{cl}» : OpenCover exe ⟦{sys}⟧ {k})"
      | .fuel p => s!"(«fuel {p}» : Good exe ⟦{p}⟧)"
    unless seen.contains h do
      seen := seen ++ [h]
      hs := hs ++ [h]
  let header := s!"theorem link_{n.name} (exe : Checked → Trace → Prop)"
  let body := hs.map (s!"    " ++ ·)
  let concl := s!"    : Algebra.Implements (Beh exe ⟦{n.name}⟧) (nodeStep ⟦{n.name}⟧).always := \
    Algebra.Ev.sound (linkEv exe ⟦{n.name}⟧) ‹faithful› ‹supported›"
  return "\n".intercalate ([header] ++ body ++ [concl,
    s!"-- {ls.length} leaves, {hs.length} distinct hypotheses; {c.summary}"])

end Harness.Link
