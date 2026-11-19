import Harness.Runtime
import Harness.Algebra

/-! # The formal link (docs/10-formal-link.md)

The semantics of a system as `Harness/Runtime.lean` steps it, and the theorem that the
children's contracts, as wired, give the system's contract.

* Traces, runs and the wiring relation `Consistent`, stated with the runtime's own `fetch`.
* Behaviors `Beh`: a module's runs are what its executable produces (a variable, `exe`); a
  system's runs are wired runs of its children's behaviors.
* `Deep` and `DSat`: the history form, for a node and every instance below it.
* `link`: one system, by `Algebra.loop`. `sound`: the nested statement, by induction on `Beh`.
* `LoopDis` (an obligation discharged in loop form) and `CitedDis` (discharged by cited clauses,
  each at the tick at which the wire delivers it), with `citedDis_loop`.

Core Lean only. Nothing is assumed about `Float32`: clause truth is `Expr.holds`, the function
the monitors call. -/

namespace Harness.Link

open Harness

/-! ## Records and arrays -/

theorem getElem!_eq {α} [Inhabited α] (a : Array α) {k : Nat} (h : k < a.size) :
    a[k]! = a[k] := getElem!_pos a k h

theorem append_left! {α} [Inhabited α] (a b : Array α) {k : Nat} (h : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_eq _ (by simp; omega), getElem!_eq _ h, Array.getElem_append_left h]

theorem append_right! {α} [Inhabited α] (a b : Array α) {k : Nat} (h : a.size ≤ k) :
    (a ++ b)[k]! = b[k - a.size]! := by
  by_cases hk : k < a.size + b.size
  · rw [getElem!_eq _ (by simp; omega), getElem!_eq _ (by omega), Array.getElem_append_right h]
  · rw [getElem!_neg _ _ (by simp; omega), getElem!_neg _ _ (by omega)]

theorem map! {α β} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {k : Nat}
    (h : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_eq _ (by simp; omega), getElem!_eq _ h, Array.getElem_map]

theorem ofFn! {α} [Inhabited α] {n : Nat} (f : Fin n → α) {k : Nat} (h : k < n) :
    (Array.ofFn f)[k]! = f ⟨k, h⟩ := by
  rw [getElem!_eq _ (by simp; omega), Array.getElem_ofFn]

/-! ## Traces and runs -/

/-- One case of a node: its parameter record (passed once, at `init`), and its input and
output records at every tick. -/
structure Trace where
  params : Record
  input : Nat → Record
  output : Nat → Record

instance : Inhabited Trace := ⟨⟨#[], fun _ => #[], fun _ => #[]⟩⟩

/-- The environment the monitors evaluate the node's clauses on at tick `t`
(`runCampaign`: `params ++ inp ++ out`). -/
def Trace.env (τ : Trace) (t : Nat) : Array UInt32 := τ.params ++ τ.input t ++ τ.output t

/-- A run: the node's trace and one run per child, the records `Running.init` and
`Running.step` report for every instance, as a tree. -/
inductive Run where
  | mk (τ : Trace) (kids : List Run)

instance : Inhabited Run := ⟨.mk default []⟩

def Run.root : Run → Trace
  | .mk τ _ => τ

def Run.kids : Run → List Run
  | .mk _ ks => ks

/-- The run of child `i`. -/
def Run.kid (r : Run) (i : Nat) : Run := r.kids.getD i default

/-- A checked system's child `i`. -/
def child (s : CSys) (i : Nat) : CNode := (s.children[i]!).node

/-- Records of the sizes of the node's schemas. -/
def Sized (c : Checked) (τ : Trace) : Prop :=
  τ.params.size = c.m.params.size ∧
    ∀ t, (τ.input t).size = c.m.input.size ∧ (τ.output t).size = c.m.output.size

/-! ## Clauses -/

/-- Every clause of the list holds on the environment (`Expr.holds`, as the monitors read it). -/
def HoldsAll (cs : Array Clause) (env : Array UInt32) : Prop :=
  ∀ k, k < cs.size → (cs[k]!).expr.holds env = true

/-- The node's assumption at tick `t`. -/
def NA (n : CNode) (r : Run) (t : Nat) : Prop := HoldsAll n.view.assume (r.root.env t)

/-! ## The wiring -/

/-- The outputs at tick `t` of the first `m` children: what `Running.step` has pushed onto
`outs` when it assembles the input of child `m` (and, for `m` = the number of children, the
array the system's outputs and the next `prev` state are read from). -/
def outsUpTo (kids : List Run) (m t : Nat) : Array Record :=
  Array.ofFn (n := m) fun j => (kids.getD j.val default).root.output t

/-- The `prev` state at tick `t`: the initial values at tick 0 (`Running.init`), then the
outputs of the tick before (the end of `Running.step`). -/
def prevAt (s : CSys) (kids : List Run) : Nat → Array UInt32
  | 0 => s.prevs.map (·.init)
  | t + 1 => s.prevs.map fun w => (outsUpTo kids s.children.size t)[w.child]![w.field]!

/-- The run is wired as `Running.init` and `Running.step` wire it. -/
def Consistent (s : CSys) (r : Run) : Prop :=
  r.kids.length = s.children.size ∧
  (∀ i, i < s.children.size →
    (r.kid i).root.params = (s.children[i]!).params.map (fetch #[] r.root.params #[] #[])) ∧
  (∀ i, i < s.children.size → ∀ t,
    (r.kid i).root.input t = (s.children[i]!).input.map
      (fetch (r.root.input t) r.root.params (outsUpTo r.kids i t) (prevAt s r.kids t))) ∧
  (∀ t, r.root.output t = s.outputs.map
      (fetch (r.root.input t) r.root.params (outsUpTo r.kids s.children.size t)
        (prevAt s r.kids t)))

/-! ## Behaviors -/

/-- The runs of a node. `exe c` is the set of traces the executable of module `c` can produce
(never defined here). A system's runs are its children's runs, wired. -/
inductive Beh (exe : Checked → Trace → Prop) : CNode → Run → Prop
  | module {c : Checked} {τ : Trace} : Sized c τ → exe c τ → Beh exe (.module c) (.mk τ [])
  | system {s : CSys} {τ : Trace} {kids : List Run} :
      Sized s.view τ → Consistent s (.mk τ kids) →
      (∀ i, i < s.children.size → Beh exe (child s i) ((Run.mk τ kids).kid i)) →
      Beh exe (.system s) (.mk τ kids)

theorem Beh.sized {exe} {n : CNode} {r : Run} (h : Beh exe n r) : Sized n.view r.root := by
  cases h with
  | module hs _ => exact hs
  | system hs _ _ => exact hs

theorem Beh.consistent {exe} {s : CSys} {r : Run} (h : Beh exe (.system s) r) :
    Consistent s r := by
  cases h with
  | system _ hc _ => exact hc

theorem Beh.kid {exe} {s : CSys} {r : Run} (h : Beh exe (.system s) r) {i : Nat}
    (hi : i < s.children.size) : Beh exe (child s i) (r.kid i) := by
  cases h with
  | system _ _ hk => exact hk i hi

/-! ## The history form -/

/-- At tick `t` the node's assumption and guarantee hold, and so do those of every instance
below it. -/
inductive Deep : CNode → Run → Nat → Prop
  | module {c : Checked} {τ : Trace} {ks : List Run} {t : Nat} :
      HoldsAll c.assume (τ.env t) → HoldsAll c.guarantee (τ.env t) → Deep (.module c) (.mk τ ks) t
  | system {s : CSys} {τ : Trace} {kids : List Run} {t : Nat} :
      HoldsAll s.view.assume (τ.env t) → HoldsAll s.view.guarantee (τ.env t) →
      (∀ i, i < s.children.size → Deep (child s i) ((Run.mk τ kids).kid i) t) →
      Deep (.system s) (.mk τ kids) t

theorem Deep.assume {n : CNode} {r : Run} {t : Nat} (h : Deep n r t) : NA n r t := by
  cases h with
  | module ha _ => exact ha
  | system ha _ _ => exact ha

theorem Deep.guarantee {n : CNode} {r : Run} {t : Nat} (h : Deep n r t) :
    HoldsAll n.view.guarantee (r.root.env t) := by
  cases h with
  | module _ hg => exact hg
  | system _ hg _ => exact hg

theorem Deep.kid {s : CSys} {r : Run} {t : Nat} (h : Deep (.system s) r t) {i : Nat}
    (hi : i < s.children.size) : Deep (child s i) (r.kid i) t := by
  cases h with
  | system _ _ hk => exact hk i hi

/-- The history form of a node: at every tick up to which its assumption has held, it and
every instance below it meet their assumption and guarantee. -/
def DSat (n : CNode) (r : Run) : Prop := ∀ t, (∀ t', t' ≤ t → NA n r t') → Deep n r t

/-- The node's step contract over runs; `DSat` is its reading `Step.always`. -/
def nodeStep (n : CNode) : Algebra.Step Run := ⟨NA n, Deep n⟩

theorem dsat_iff_always (n : CNode) (r : Run) : DSat n r ↔ (nodeStep n).always.G r := Iff.rfl

/-! ## Discharge and cover -/

/-- Assumption clause `k` of child `i` holds at `t`, in loop form: from the system's assumption
up to `t`, the children scheduled before `i` at `t`, and every child at every earlier tick. -/
def LoopDis (s : CSys) (r : Run) (i k : Nat) : Prop :=
  ∀ t, (∀ t', t' ≤ t → NA (.system s) r t') →
    (∀ j, j < s.children.size → j < i → Deep (child s j) (r.kid j) t) →
    (∀ j, j < s.children.size → ∀ t', t' < t → Deep (child s j) (r.kid j) t') →
    ((child s i).view.assume[k]!).expr.holds ((r.kid i).root.env t) = true

/-- Guarantee clause `k` of the system holds at `t`, from the system's assumption up to `t` and
every child at every tick up to `t`. -/
def Cover (s : CSys) (r : Run) (k : Nat) : Prop :=
  ∀ t, (∀ t', t' ≤ t → NA (.system s) r t') →
    (∀ j, j < s.children.size → ∀ t', t' ≤ t → Deep (child s j) (r.kid j) t') →
    (s.view.guarantee[k]!).expr.holds (r.root.env t) = true

/-! ## The link theorem for one system -/

/-- One system: children in their history form, every assumption clause of every child
discharged in loop form, every guarantee clause of the system covered, give the system's
history form. The induction over ticks and schedule positions is `Algebra.loop`, instantiated
with the children's step contracts and the system's assumption as the environment. -/
theorem link (s : CSys) (r : Run)
    (hK : ∀ i, i < s.children.size → DSat (child s i) (r.kid i))
    (hA : ∀ i, i < s.children.size → ∀ k, k < (child s i).view.assume.size → LoopDis s r i k)
    (hG : ∀ k, k < s.view.guarantee.size → Cover s r k) :
    DSat (.system s) r := by
  let n := s.children.size
  let S : Nat → Algebra.Step PUnit := fun i =>
    ⟨fun _ t => NA (child s i) (r.kid i) t, fun _ t => Deep (child s i) (r.kid i) t⟩
  have key := Algebra.loop n (fun i _ => DSat (child s i) (r.kid i)) S
    (fun _ t => NA (.system s) r t)
    (fun i _ _ hb _ => hb)
    (fun _ t he i hi hcur hprev k hk =>
      hA i hi k hk t he (fun j _ hji => hcur j hji) (fun j hj t' ht' => hprev j hj t' ht'))
    PUnit.unit (fun i hi => hK i hi) trivial
  -- key : ∀ t, (∀ t' ≤ t, NA system t') → ∀ i < n, Deep (child i) t
  intro t ht
  have hkids : ∀ t', t' ≤ t → ∀ i, i < n → Deep (child s i) (r.kid i) t' := fun t' ht' =>
    key t' fun t'' ht'' => ht t'' (Nat.le_trans ht'' ht')
  cases r with
  | mk τ kids =>
    exact Deep.system (ht t (Nat.le_refl t))
      (fun k hk => hG k hk t ht fun j hj t' ht' => hkids t' ht' j hj)
      (fun i hi => hkids t (Nat.le_refl t) i hi)

/-! ## Nesting -/

/-- A module's leaf claim: every run of its executable, with schema-sized records, meets the
guarantee at every tick up to which the assumption has held. The campaigns' claim; a
hypothesis here. -/
def LeafClaim (exe : Checked → Trace → Prop) (c : Checked) : Prop :=
  ∀ τ, exe c τ → Sized c τ → ∀ t, (∀ t', t' ≤ t → HoldsAll c.assume (τ.env t')) →
    HoldsAll c.guarantee (τ.env t)

/-- What a system needs of its wiring and contracts, on all its behaviors. -/
def SysOK (exe : Checked → Trace → Prop) (s : CSys) : Prop :=
  ∀ r, Beh exe (.system s) r →
    (∀ i, i < s.children.size → ∀ k, k < (child s i).view.assume.size → LoopDis s r i k) ∧
    (∀ k, k < s.view.guarantee.size → Cover s r k)

/-- Every module of the tree meets its leaf claim and every system of the tree is `SysOK`. -/
inductive Good (exe : Checked → Trace → Prop) : CNode → Prop
  | module {c : Checked} : LeafClaim exe c → Good exe (.module c)
  | system {s : CSys} : (∀ i, i < s.children.size → Good exe (child s i)) → SysOK exe s →
      Good exe (.system s)

/-- The nested statement: every behavior of a good tree is in its history form. A child that
is a system gets its `DSat` from this theorem one level down. -/
theorem sound {exe : Checked → Trace → Prop} {n : CNode} {r : Run} (hb : Beh exe n r)
    (hg : Good exe n) : DSat n r := by
  induction hb with
  | module hs he =>
    cases hg with
    | module hl =>
      intro t ht
      exact Deep.module (ht t (Nat.le_refl t)) (hl _ he hs t ht)
  | @system s τ kids hs hc hk ih =>
    cases hg with
    | system hgk hok =>
      have h := hok _ (Beh.system hs hc hk)
      exact link s _ (fun i hi => ih i hi (hgk i hi)) h.1 h.2

/-- In the algebra's terms: the behaviors of a good tree implement its step contract read over
runs (`Algebra.Implements`, `Step.always`). -/
theorem sound_implements {exe : Checked → Trace → Prop} {n : CNode} (hg : Good exe n) :
    Algebra.Implements (Beh exe n) (nodeStep n).always :=
  fun _ hb _ => sound hb hg

/-- The nested statement spelled out for a system with a system child: if the child's own
children are good and its wiring is `SysOK`, and the parent's other children are good and its
wiring is `SysOK`, every behavior of the parent is in history form, and so is every behavior of
the child inside it. -/
theorem sound_nested {exe : Checked → Trace → Prop} {s : CSys} {j : Nat} {s' : CSys}
    (hj : j < s.children.size) (hs' : child s j = .system s')
    (hgc : ∀ i, i < s'.children.size → Good exe (child s' i)) (hok' : SysOK exe s')
    (hgo : ∀ i, i < s.children.size → i ≠ j → Good exe (child s i)) (hok : SysOK exe s)
    {r : Run} (hb : Beh exe (.system s) r) :
    DSat (.system s) r ∧ DSat (.system s') (r.kid j) := by
  have hgj : Good exe (child s j) := hs' ▸ Good.system hgc hok'
  have hg : Good exe (.system s) := Good.system (fun i hi => by
    by_cases h : i = j
    · subst h; exact hgj
    · exact hgo i hi h) hok
  refine ⟨sound hb hg, ?_⟩
  have := sound (Beh.kid hb hj) hgj
  rw [hs'] at this
  exact this

/-! ## Instances below a node, by path -/

/-- The instance at a path of child indices is well named, with guarantee clause `k`. -/
def validPath : CNode → List Nat → Nat → Bool
  | n, [], k => decide (k < n.view.guarantee.size)
  | .module _, _ :: _, _ => false
  | .system s, j :: p, k => decide (j < s.children.size) && validPath (child s j) p k

/-- Guarantee clause `k` of the instance at the path holds at `t`. -/
def GAt : CNode → Run → List Nat → Nat → Nat → Prop
  | n, r, [], k, t => (n.view.guarantee[k]!).expr.holds (r.root.env t) = true
  | .module _, _, _ :: _, _, _ => False
  | .system s, r, j :: p, k, t => GAt (child s j) (r.kid j) p k t

theorem deep_gat : ∀ (p : List Nat) (n : CNode) (r : Run) (k t : Nat), Deep n r t →
    validPath n p k = true → GAt n r p k t
  | [], n, r, k, t, hd, hv => by
    simp [validPath] at hv
    exact Deep.guarantee hd k hv
  | _ :: _, .module _, _, _, _, _, hv => by simp [validPath] at hv
  | j :: p, .system s, r, k, t, hd, hv => by
    simp [validPath] at hv
    exact deep_gat p (child s j) (r.kid j) k t (Deep.kid hd hv.1) hv.2

/-! ## Cited discharges -/

/-- A cited clause: an assumption clause `q` of the system (`assume.NAME` in a discharge
table), or guarantee clause `k` of the instance at `path` below child `j`, read `lag` ticks
before the obligation (`PATH.NAME`). -/
inductive Cite where
  | assume (q : Nat)
  | guar (j : Nat) (path : List Nat) (k : Nat) (lag : Nat)
  deriving Repr, Inhabited

/-- What the cited clause says at the obligation's tick `t`; a citation read `lag` ticks before
`t` says nothing when `t < lag` (at the first tick a `prev` wire holds its initial value). -/
def avail (s : CSys) (r : Run) (t : Nat) : Cite → Prop
  | .assume q => (s.view.assume[q]!).expr.holds (r.root.env t) = true
  | .guar j p k lag => lag ≤ t → GAt (child s j) (r.kid j) p k (t - lag)

/-- A citation for child `i`'s obligation is well placed: it names an existing clause, and a
same-tick citation names a child scheduled before `i` (the side condition of the loop rule). -/
def citeOK (s : CSys) (i : Nat) : Cite → Bool
  | .assume q => decide (q < s.view.assume.size)
  | .guar j p k lag => decide (j < s.children.size) && validPath (child s j) p k &&
      (lag != 0 || decide (j < i))

/-- The discharge implication of a table entry: on every behavior, at every tick, the cited
clauses (each at its tick) imply assumption clause `k` of child `i`. -/
def CitedDis (exe : Checked → Trace → Prop) (s : CSys) (i k : Nat) (cs : List Cite) : Prop :=
  ∀ r, Beh exe (.system s) r → ∀ t, (∀ c, c ∈ cs → avail s r t c) →
    ((child s i).view.assume[k]!).expr.holds ((r.kid i).root.env t) = true

/-- An open obligation, as a hypothesis: the loop form on every behavior. -/
def OpenDis (exe : Checked → Trace → Prop) (s : CSys) (i k : Nat) : Prop :=
  ∀ r, Beh exe (.system s) r → LoopDis s r i k

/-- A guarantee clause of the system that is not a copy of a child's, as a hypothesis. -/
def OpenCover (exe : Checked → Trace → Prop) (s : CSys) (k : Nat) : Prop :=
  ∀ r, Beh exe (.system s) r → Cover s r k

/-- A cited discharge with well-placed citations is a discharge in loop form. -/
theorem citedDis_loop {exe : Checked → Trace → Prop} {s : CSys} {i k : Nat} {cs : List Cite}
    (h : CitedDis exe s i k cs) (hok : ∀ c, c ∈ cs → citeOK s i c = true) :
    OpenDis exe s i k := by
  intro r hb t hsys hcur hprev
  apply h r hb t
  intro c hc
  have hc' := hok c hc
  cases c with
  | assume q =>
    simp [citeOK] at hc'
    exact hsys t (Nat.le_refl t) q hc'
  | guar j p k' lag =>
    simp [citeOK] at hc'
    obtain ⟨⟨hj, hv⟩, hl⟩ := hc'
    intro hlag
    by_cases h0 : lag = 0
    · subst h0
      have hji : j < i := by simpa using hl
      simpa using deep_gat p _ _ k' t (hcur j hj hji) hv
    · exact deep_gat p _ _ k' (t - lag) (hprev j hj (t - lag) (by omega)) hv

end Harness.Link
