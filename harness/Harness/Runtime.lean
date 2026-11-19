import Harness.Protocol
import Harness.System

/-! Running a node (docs/9-nesting.md, "How a tick runs").

A running module is one process. A running system holds its children, running, and its state:
its parameter record and the value of every `prev` wire. `init`, `step` and `stop` work the same
for both. `init` returns the parameter record of every instance of the subtree, and `step` the
(input, output) pair of every instance, in preorder (the order of `CNode.instances`), so that the
monitors and the case logs see every exchange. Records pass through wires as the same words. -/

namespace Harness

/-- A system's state between ticks. -/
structure SysState where
  params : Record
  /-- one word per `prev` wire -/
  prev : Array UInt32

/-- A running node: one process per module instance. `groups`: the children in tick order, in
groups stepped at the same time (`CSysOf.stepGroups`; one child per group unless the system is
`concurrent`). -/
inductive Running where
  | module (proc : Proc)
  | system (s : CSys) (kids : Array Running) (st : IO.Ref SysState) (groups : Array (Array Nat))

/-- The (input, output) records of every instance at one tick, in preorder. -/
abbrev Exchanges := Array (Record × Record)

/-- The word a source holds (public so that `Harness/Link.lean` states the wiring with it). -/
def fetch (inp params : Record) (outs : Array Record) (prev : Array UInt32) : Src → UInt32
  | .input i => inp[i]!
  | .param i => params[i]!
  | .out c i => outs[c]![i]!
  | .prev k => prev[k]!
  | .const w => w

/-- The children of a system in groups of consecutive children, in tick order: a child joins the
group of the children before it when it reads no output of the same tick (`out` source) of any
child of that group. A group's children read only the system's inputs and parameters, `prev`
values, constants and outputs of children of earlier groups, so stepping them at the same time
gives the records of stepping them one after the other. A system that is not `concurrent` has
one child per group. -/
def CSysOf.stepGroups (s : CSysOf N) (concurrent : Bool := s.decl.concurrent) :
    Array (Array Nat) := Id.run do
  if !concurrent then return (Array.range s.children.size).map fun i => #[i]
  let mut gs : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  for (ch, j) in s.children.zipIdx do
    let readsCur := ch.input.any fun
      | .out c _ => cur.contains c
      | _ => false
    if cur.isEmpty || !readsCur then cur := cur.push j
    else
      gs := gs.push cur
      cur := #[j]
  if !cur.isEmpty then gs := gs.push cur
  return gs

namespace Running

/-- The child processes of the subtree. -/
partial def procs : Running → Array Proc
  | module p => #[p]
  | system _ kids _ _ => kids.flatMap procs

/-- Stop every process of the subtree. -/
partial def stop : Running → IO Unit
  | module p => p.stop
  | system _ kids _ _ => kids.forM stop

/-- `init` with the node's parameter record. Returns every instance's parameter record. -/
partial def init : Running → Record → IO (Array Record)
  | module p, params => do p.init params; return #[params]
  | system s kids st _, params => do
    let mut all := #[params]
    for (ch, k) in s.children.zip kids do
      all := all ++ (← k.init (ch.params.map (fetch #[] params #[] #[])))
    st.set { params, prev := s.prevs.map (·.init) }
    return all

/-- One tick with the node's input record. Returns the node's output record and every instance's
(input, output) records. -/
partial def step : Running → Record → IO (Record × Exchanges)
  | module p, inp => do
    let out ← p.step inp
    return (out, #[(inp, out)])
  | system s kids st groups, inp => do
    let ss ← st.get
    let mut outs : Array Record := Array.mkEmpty kids.size
    let mut ex : Exchanges := #[]
    for g in groups do
      let kid (j : Nat) : IO Running := match kids[j]? with
        | some k => pure k
        | none => throw (IO.userError s!"system {s.decl.name}: no child {j}")
      if g.size == 1 then
        let j := g[0]!
        let (o, e) ← (← kid j).step (s.children[j]!.input.map (fetch inp ss.params outs ss.prev))
        outs := outs.push o
        ex := ex ++ e
      else
        -- every input of the group is assembled from what is known before the group; each child
        -- but the last is stepped as a task (Lean's thread pool), the last on this thread, and all
        -- are awaited before any error is raised
        let inputs := g.map fun j => s.children[j]!.input.map (fetch inp ss.params outs ss.prev)
        let tasks ← (g.zip inputs).pop.mapM fun (j, i) => do
          let k ← kid j
          IO.asTask (k.step i)
        let (jl, il) := (g.zip inputs).back!
        let lastR : Except IO.Error (Record × Exchanges) ← try
            let r ← (← kid jl).step il
            pure (.ok r)
          catch e => pure (.error e)
        let mut res : Array (Record × Exchanges) := #[]
        let mut err : Option IO.Error := none
        for t in tasks do
          match ← IO.wait t with
          | .ok r => res := res.push r
          | .error e => if err.isNone then err := some e
        match lastR with
        | .ok r => res := res.push r
        | .error e => if err.isNone then err := some e
        if let some e := err then throw e
        for (o, e) in res do
          outs := outs.push o
          ex := ex ++ e
    let out := s.outputs.map (fetch inp ss.params outs ss.prev)
    st.set { ss with prev := s.prevs.map fun w => outs[w.child]![w.field]! }
    return (out, #[(inp, out)] ++ ex)

end Running

/-- Start one process per module instance of the tree (each checked against its declaration).
If a start fails, the processes already started are stopped. -/
partial def CNode.start (n : CNode) : IO Running :=
  match n with
  | .module c => return .module (← Proc.start c.m)
  | .system s => do
    let mut kids : Array Running := #[]
    for ch in s.children do
      try kids := kids.push (← ch.node.start)
      catch e =>
        for k in kids do try k.stop catch _ => pure ()
        throw e
    -- HARNESS_SEQUENTIAL=1 steps every child one after the other (to compare the records)
    let seq := (← IO.getEnv "HARNESS_SEQUENTIAL").getD "" == "1"
    return .system s kids (← IO.mkRef { params := #[], prev := #[] })
      (s.stepGroups (s.decl.concurrent && !seq))

/-- The code hash of each module of the tree, from the manifests of the running processes. -/
def Running.moduleHash (r : Running) (m : Module) : String :=
  match r.procs.find? (·.m.name == m.name) with
  | some p => p.manifest.codeHash
  | none => "(not running)"

/-- The code hash of each distinct module of the tree, from a short describe of its executable. -/
def describeHashes (n : CNode) : IO (Module → String) := do
  let mut hs : Array (String × String) := #[]
  for m in n.modules do
    let h ← try pure (← describeModule m).codeHash catch _ => pure "(no executable)"
    hs := hs.push (m.name, h)
  return fun m => ((hs.find? (·.1 == m.name)).map (·.2)).getD "(unknown)"

end Harness
