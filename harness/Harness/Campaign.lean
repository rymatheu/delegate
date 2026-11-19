import Lean.Data.Json
import Harness.Runtime
import Harness.Generate
import Harness.Sha256

/-! Test campaigns and replay, for any node (a module or a system).

A campaign runs `cases` cases; each case draws a parameter record, calls `init`, then draws
`steps` input records and calls `step` with each, so the node's internal state evolves. Every
guarantee clause of the node under test is checked at every step. The campaign records, per
clause, the number of checks, the number of violations, the smallest margin and where it
occurred, and saves two replayable cases per clause: the first counterexample (if any) and the
case with the smallest margin.

For a system the same campaign also monitors every inner instance (docs/9-nesting.md,
"Monitors"): at every step, whether the instance's assumption held (when it does not, the system
did not discharge it: a discharge failure, at the instance's path), and, at the steps where it
held, each of its guarantee clauses. Saved cases of a system log every instance's exchanges. -/

namespace Harness

open Lean (Json)

/-- One inner instance's exchanges over a case: its parameter record and, per step, its input and
output records. -/
structure InstLog where
  path : String
  params : Record
  inputs : Array Record := #[]
  outputs : Array Record := #[]
  deriving Inhabited

/-- A case as run: the node's parameter record and per-step input and output records. -/
structure CaseRecord where
  index : Nat
  params : Record
  inputs : Array Record
  outputs : Array Record
  /-- for a system: every inner instance's exchanges, in preorder -/
  inner : Array InstLog := #[]
  deriving Inhabited

/-- What a campaign saw of one guarantee clause. -/
structure ClauseStat where
  clause : Clause
  /-- the instance whose clause it is; "" for the node under test -/
  path : String := ""
  checked : Nat := 0
  violations : Nat := 0
  minMargin : Option Float := none
  minAt : Option (Nat × Nat) := none
  minCase : Option CaseRecord := none
  cex : Option (CaseRecord × Nat) := none
  deriving Inhabited

/-- Count one check of the clause on `env` at (case `ci`, step `k`); `mk` builds the case so far,
only when it is kept. -/
def ClauseStat.observe (st : ClauseStat) (env : Array UInt32) (ci k : Nat)
    (mk : Unit → CaseRecord) : ClauseStat := Id.run do
  let e := st.clause.expr
  let mut st' := { st with checked := st.checked + 1 }
  unless e.holds env do
    st' := { st' with violations := st'.violations + 1 }
    if st'.cex.isNone then st' := { st' with cex := some (mk (), k) }
  if let some x := e.margin env then
    let better : Bool := match st'.minMargin with
      | some y => x < y
      | none => true
    if better then
      st' := { st' with minMargin := some x, minAt := some (ci, k), minCase := some (mk ()) }
  return st'

/-- Per inner instance: at how many steps its assumption held, in how many cases it failed (a
discharge failure of the system: from that step on the instance's guarantee is not checked for
the rest of the case), the first such step, and how often each assumption clause failed. -/
structure AssumeStat where
  path : String
  steps : Nat := 0
  /-- steps at which the assumption held at that step -/
  held : Nat := 0
  /-- steps at which it had held at every step so far in the case (the guarantee was checked) -/
  heldSoFar : Nat := 0
  /-- cases with a discharge failure -/
  failedCases : Nat := 0
  firstFail : Option (CaseRecord × Nat) := none
  /-- per assumption clause: steps at which it failed, and cases whose first failure it was in -/
  clauseFails : Array (String × Nat × Nat) := #[]
  deriving Inhabited

/-- Seed, size and regime of a campaign. -/
structure CampaignConfig where
  seed : Nat := 1
  cases : Nat := 2000
  steps : Nat := 200
  /-- the regime inputs are generated in, besides the assumption -/
  regime : Option String := none
  /-- a CSV file to write every step's output record to (case, step, then the node's outputs) -/
  logFile : Option String := none

/-- What the outputs did over a campaign: for a Boolean field the number of steps it was true;
for a numeric field the smallest and largest finite values and the number of non-finite ones. -/
structure OutputSeen where
  trues : Nat := 0
  lo : Option Float := none
  hi : Option Float := none
  nonFinite : Nat := 0
  deriving Inhabited

/-- Count one output word. -/
def OutputSeen.add (o : OutputSeen) (t : FieldType) (w : UInt32) : OutputSeen :=
  if t == .bool then { o with trues := o.trues + (if w != 0 then 1 else 0) }
  else
    let x := (Expr.wordToF32 t w).toFloat
    if x.isFinite then
      { o with lo := some (match o.lo with | some y => min x y | none => x),
               hi := some (match o.hi with | some y => max x y | none => x) }
    else { o with nonFinite := o.nonFinite + 1 }

/-- Everything a campaign found. -/
structure CampaignResult where
  seen : Array OutputSeen
  cfg : CampaignConfig
  stats : Array ClauseStat
  stepsRun : Nat
  casesSkipped : Nat
  seconds : Float
  /-- the code hash of the node under test -/
  codeHash : String
  /-- the executable's manifest when the node under test is a module -/
  manifest : Option Manifest
  /-- every instance, the node under test first, and each one's code hash -/
  insts : Array Inst
  instHashes : Array String
  /-- inner clauses, monitored -/
  inner : Array ClauseStat := #[]
  /-- inner assumptions: discharge -/
  assumes : Array AssumeStat := #[]
  /-- the regime, when the campaign ran in one -/
  regime : Option Regime := none
  /-- per coverage observation of the node: steps at which it was true -/
  coverage : Array (Clause × Nat) := #[]

/-- True when steps ran and the campaign found no violation and no discharge failure. -/
def CampaignResult.passed (r : CampaignResult) : Bool :=
  r.stepsRun > 0 && r.stats.all (·.violations == 0) && r.inner.all (·.violations == 0) &&
    r.assumes.all (·.failedCases == 0)

/-! ### Records in files -/

/-- A record as a JSON object, one text word per field. -/
def recordJson (s : Schema) (r : Record) : Json :=
  Json.mkObj ((s.zip r).toList.map fun (f, w) => (f.name, Json.str (f.type.wordText w)))

/-- A record read back from `recordJson`'s form. -/
def recordOfJson (s : Schema) (j : Json) : Except String Record :=
  s.mapM fun f => do
    let t ← j.getObjValAs? String f.name
    match f.type.parseWord? t with
    | some w => pure w
    | none => throw s!"field {f.name}: cannot read '{t}' as {f.type.name}"

/-- A record as the fields that differ from `prev` (all fields when `prev` is empty). -/
def recordDeltaJson (s : Schema) (prev r : Record) : Json := Id.run do
  let mut kvs : List (String × Json) := []
  for i in [0:s.size] do
    let f := s[i]!
    let w := r[i]!
    if prev[i]? != some w then kvs := kvs ++ [(f.name, Json.str (f.type.wordText w))]
  return Json.mkObj kvs

/-- A record read back from `recordDeltaJson`'s form: a missing field keeps `prev`'s word. -/
def recordOfDeltaJson (s : Schema) (prev : Record) (j : Json) : Except String Record := do
  let mut out : Record := #[]
  for i in [0:s.size] do
    let f := s[i]!
    match j.getObjValAs? String f.name with
    | .error _ => match prev[i]? with
      | some w => out := out.push w
      | none => throw s!"field {f.name}: missing in the first input record"
    | .ok t => match f.type.parseWord? t with
      | some w => out := out.push w
      | none => throw s!"field {f.name}: cannot read '{t}' as {f.type.name}"
  return out

/-- Input records in the delta form, decoded in order. -/
def inputsOfDeltaJson (s : Schema) (js : Array Json) : Except String (Array Record) := do
  let mut prev : Record := #[]
  let mut out := #[]
  for j in js do
    prev ← recordOfDeltaJson s prev j
    out := out.push prev
  return out

/-- Input records as indexed deltas, the form of a long case's inputs file: per step a flat array
`[i, "word", i, "word", ...]` of the fields (by index in the schema) that differ from the step
before; every field at the first step. -/
def inputsIndexedJson (s : Schema) (rs : Array Record) : Json := Id.run do
  let mut steps : Array Json := #[]
  for k in [0:rs.size] do
    let r := rs[k]!
    let prev := if k == 0 then #[] else rs[k-1]!
    let mut a : Array Json := #[]
    for i in [0:s.size] do
      let w := r[i]!
      if prev[i]? != some w then
        a := (a.push (Json.num i)).push (Json.str (s[i]!.type.wordText w))
    steps := steps.push (Json.arr a)
  return Json.arr steps

/-- Input records read back from `inputsIndexedJson`'s form. -/
def inputsOfIndexedJson (s : Schema) (js : Array Json) : Except String (Array Record) := do
  let mut prev : Record := #[]
  let mut out := #[]
  for j in js do
    let some a := (j.getArr?).toOption | throw "an inputs step is not an array"
    let mut r : Array (Option UInt32) := prev.map some
    if r.isEmpty then r := Array.replicate s.size none
    for q in [0:a.size / 2] do
      let some i := (a[2*q]!.getNat?).toOption | throw "an inputs index is not a number"
      let some t := (a[2*q+1]!.getStr?).toOption | throw "an inputs word is not a string"
      unless i < s.size do throw s!"inputs index {i} beyond the schema's {s.size} fields"
      match s[i]!.type.parseWord? t with
      | some w => r := r.set! i (some w)
      | none => throw s!"field {s[i]!.name}: cannot read '{t}' as {s[i]!.type.name}"
    let some rec := r.mapM id | throw "a field is missing in the first input record"
    prev := rec
    out := out.push rec
  return out

/-- A long case's inputs file: its parameters and every input record once (indexed deltas),
shared by the case's saved (case, step) files, which name it with its hash and how many of its
records are theirs (`inputs_file`, `inputs_sha256`, `inputs_count`). -/
def caseInputsJson (n : CNode) (codeHash campaign : String) (c : CaseRecord) : Json :=
  let m := n.view.m
  Json.mkObj [(n.kind, Json.str m.name), ("code_hash", Json.str codeHash),
    ("campaign", Json.str campaign), ("kind", Json.str "inputs of a long case"),
    ("case", Json.num c.index), ("steps", Json.num c.inputs.size),
    ("fields", Json.arr (m.input.map (Json.str ·.name))),
    ("params", recordJson m.params c.params),
    ("inputs_indexed", inputsIndexedJson m.input c.inputs)]

/-- The most record words a saved case keeps beyond its parameters and inputs. A longer case keeps
every input (a replay needs them all, from the first step), each as the fields that changed since
the step before (`inputs_delta`), only the outputs of its last steps, and no per-instance logs (so
`replay --child` is not available for it); the file says so. -/
def caseWordBudget : Nat := 20000

/-- Whether a saved case is capped (`caseWordBudget`): its outputs and per-instance logs exceed
the budget. -/
def caseCapped (c : CaseRecord) : Bool :=
  let innerWords := c.inner.foldl (fun a l =>
    a + l.inputs.foldl (· + ·.size) 0 + l.outputs.foldl (· + ·.size) 0) 0
  c.outputs.foldl (· + ·.size) 0 + innerWords > caseWordBudget

/-- A saved case. For a module the file is as it always was; for a system it is keyed `system`
and adds `instances`: every inner instance's path, node, kind, code hash, parameter record and
per-step input and output records. `path` names the instance of an inner clause. -/
def caseJson (n : CNode) (insts : Array Inst) (hashes : Array String)
    (codeHash campaign kind clause : String) (path : Option String) (c : CaseRecord)
    (step : Nat) (inputsRef : Option (String × String) := none) : Json :=
  let m := n.view.m
  let inst (l : InstLog) : Json :=
    match (insts.zip hashes).find? (·.1.path == l.path) with
    | none => Json.null
    | some (i, h) =>
      let im := i.node.view.m
      Json.mkObj [("path", Json.str l.path), ("node", Json.str i.node.name),
        ("kind", Json.str i.node.kind), ("code_hash", Json.str h),
        ("params", recordJson im.params l.params),
        ("inputs", Json.arr (l.inputs.map (recordJson im.input))),
        ("outputs", Json.arr (l.outputs.map (recordJson im.output)))]
  let capped := caseCapped c
  -- a capped case whose inputs are in the case's inputs file keeps the outputs of its last step
  -- only (the step it is evidence for): a long campaign saves one such file per distinct step
  let keep := if capped then
      (if inputsRef.isSome then min c.outputs.size 1
       else min c.outputs.size (max 1 (caseWordBudget / max 1 m.output.size)))
    else c.outputs.size
  let outs := c.outputs.extract (c.outputs.size - keep) c.outputs.size
  Json.mkObj ([
    (n.kind, Json.str m.name), ("code_hash", Json.str codeHash), ("campaign", Json.str campaign),
    ("kind", Json.str kind), ("clause", Json.str clause), ("case", Json.num c.index),
    ("step", Json.num step),
    ("note", Json.str
      "f32 fields are bit patterns; `harness replay` runs this file and prints values"),
    -- with an inputs file, the parameters are there and the outputs are words in schema order
    if inputsRef.isSome then ("params_in", Json.str "inputs_file")
    else ("params", recordJson m.params c.params),
    match inputsRef with
    | some (f, _) => ("inputs_file", Json.str f)
    | none => ("inputs", Json.arr (if capped then
      (c.inputs.zipIdx.map fun (r, k) =>
        recordDeltaJson m.input (if k == 0 then #[] else c.inputs[k-1]!) r)
      else c.inputs.map (recordJson m.input))),
    if inputsRef.isSome then
      ("outputs_words", Json.arr (outs.map fun r =>
        Json.arr ((m.output.zip r).map fun (f, w) => Json.str (f.type.wordText w))))
    else ("outputs", Json.arr (outs.map (recordJson m.output)))] ++
    (match inputsRef with
     | some (_, h) => [("inputs_sha256", Json.str h), ("inputs_count", Json.num c.inputs.size)]
     | none => []) ++
    (if capped then [("inputs_delta", Json.bool (inputsRef.isNone)),
      ("outputs_from_step", Json.num (c.outputs.size - keep)),
      ("capped", Json.str s!"a long case: outputs of the last {keep} steps only, no instance logs \
        (caseWordBudget)")] else []) ++
    (match path with | some p => [("path", Json.str p)] | none => []) ++
    (match n with
     | .system _ => [("instances", Json.arr (if capped then #[] else c.inner.map inst))]
     | .module _ => []))

/-! ### Running -/

private def assumeHolds (c : Checked) (env : Array UInt32) : Bool :=
  c.assume.all (·.expr.holds env)

/-- Draw a parameter record satisfying every assumption conjunct that mentions only parameters. -/
private def genParams (c : Checked) (gens : Array FieldGen) (paramConj : List Expr) :
    GenM (Option Record) := do
  let env0 := Array.replicate c.m.envSize (0 : UInt32)
  for _ in [0:1000] do
    let mut env := env0
    for g in gens do
      env := env.set! g.slot (← FieldGen.draw g env0)
    if paramConj.all (·.holds env) then
      return some (env.extract 0 c.m.params.size)
  return none

/-- What generates a campaign's records: a node's assumption and, optionally, a regime. Shared
by campaigns and equivalence checks, so both draw the same records from the same seed. -/
structure Sampler where
  c : Checked
  /-- the clauses every drawn (params, input) satisfies: the assumption and the regime's -/
  gen : Array Clause
  paramConj : List Expr
  pgens : Array FieldGen
  igens : Array FieldGen
  hints : Array (Nat × Nat × Nat × Nat)
  walks : Array (Nat × Float × Float × Float) := #[]
  units : Array (Array Nat × Array Float × Array Float × Array Float) := #[]
  env0 : Array UInt32
  regime : Option Regime

/-- The sampler of a checked node in a regime (by name). -/
def Sampler.make (c : Checked) (regime : Option String) : Except String Sampler := do
  let m := c.m
  let rg ← match regime with
    | none => pure none
    | some name => match c.regimes.find? (·.regime.name == name) with
      | some r => pure (some r)
      | none => throw s!"{m.name} has no regime {name}; regimes: \
          {", ".intercalate (c.regimes.toList.map (·.regime.name))}"
  let gen := c.assume ++ ((rg.map (·.clauses)).getD #[])
  let conj := gen.toList.flatMap (·.expr.conjuncts)
  return { c, gen
           paramConj := conj.filter fun e => e.vars.all fun n => (m.params.any (·.name == n))
           pgens := (m.params.toList.zipIdx.map fun (f, i) =>
             FieldGen.make m.envSize conj f i).toArray
           igens := (m.input.toList.zipIdx.map fun (f, i) =>
             FieldGen.make m.envSize conj f (m.inputBase + i)).toArray
           hints := (rg.map (·.hints)).getD #[]
           walks := (rg.map (·.walks)).getD #[]
           units := (rg.map (·.units)).getD #[]
           env0 := Array.replicate m.envSize (0 : UInt32)
           regime := rg.map (·.regime) }

/-- The input generation's state within a case: input fields held for the whole case, and the
hinted fields' current values. -/
structure CaseGen where
  held : Array (Option UInt32)
  fixed : Array (Option UInt32)

/-- A parameter record, or none after 1000 attempts. -/
def Sampler.params (s : Sampler) : GenM (Option Record) := genParams s.c s.pgens s.paramConj

/-- Start a case: per input field, held for the whole case or drawn afresh at every step. -/
def Sampler.startCase (s : Sampler) : GenM CaseGen := do
  let held ← s.igens.mapM fun (g : FieldGen) => do
    if ← chance 0.4 then return some (← g.draw s.env0) else return none
  return { held, fixed := Array.replicate s.c.m.input.size none }

/-- The input record of step `k`, satisfying the assumption and regime with `params`; none
after 200 attempts. -/
def Sampler.input (s : Sampler) (params : Record) (cg : CaseGen) (k : Nat) :
    GenM (Option Record × CaseGen) := do
  let mut fixed := cg.fixed
  let mut held := cg.held
  for (i, start, lo, hi) in s.hints do
    if k == 0 then fixed := fixed.set! i (some (UInt32.ofNat start))
    else
      let d ← randBelow (hi - lo + 1)
      fixed := fixed.set! i ((fixed[i]!).map (· + UInt32.ofNat (lo + d)))
  let f32At (i : Nat) : Float := ((fixed[i]!).map fun w => (Float32.ofBits w).toFloat).getD 0
  for (i, lo, hi, st) in s.walks do
    let u ← randUnit
    let x := if k == 0 then lo + u * (hi - lo) else f32At i + (2 * u - 1) * st
    fixed := fixed.set! i (some (max lo (min hi x)).toFloat32.toBits)
  for (is, c, sp, st) in s.units do
    let mut v : Array Float := #[]
    for j in [0:is.size] do
      let u ← randUnit
      v := v.push (if k == 0 then c[j]! + sp[j]! * (2 * u - 1)
        else f32At is[j]! + st[j]! * (2 * u - 1))
    let n := (v.foldl (fun a x => a + x * x) 0).sqrt
    let w := if n > 1e-6 then v.map (· / n) else (List.range is.size).toArray.map
      fun j => if j == 0 then 1.0 else 0.0
    for j in [0:is.size] do
      fixed := fixed.set! is[j]! (some w[j]!.toFloat32.toBits)
  let outZero := Array.replicate s.c.m.output.size (0 : UInt32)
  for attempt in [0:200] do
    let inp ← s.igens.mapIdxM fun i (g : FieldGen) => do
      match fixed[i]!, held[i]! with
      | some w, _ => pure w
      | none, some w => if attempt < 100 then pure w else g.draw s.env0
      | none, none => g.draw s.env0
    if s.gen.all (·.expr.holds (params ++ inp ++ outZero)) then
      if attempt ≥ 100 then
        held := held.mapIdx fun i (h : Option UInt32) => h.map fun _ => inp[i]!
      return (some inp, { held, fixed })
  return (none, { held, fixed })

/-- Run a campaign on a node: inputs from the node's assumption (and the regime's clauses and
hints), its guarantee tested, and for a system every inner instance monitored. A guarantee
clause of an instance is checked at a step only while that instance's assumption has held at
every step so far in the case (`Step.always` in the formal side). -/
def runCampaign (n : CNode) (cfg : CampaignConfig) (log : String → IO Unit) :
    IO CampaignResult := do
  let c := n.view
  let m := c.m
  let smp ← IO.ofExcept (Sampler.make c cfg.regime)
  -- the instances below the node under test, with their slot in the per-tick exchanges
  let insts := n.instances n.name
  let inner := insts.extract 1 insts.size
  let mut rng : Rng := ⟨cfg.seed.toUInt64⟩
  let mut stats : Array ClauseStat := c.guarantee.map fun g => { clause := g }
  let mut istats : Array ClauseStat := inner.flatMap fun i =>
    i.node.view.guarantee.map fun g => { clause := g, path := i.path }
  let mut astats : Array AssumeStat := inner.map fun i =>
    { path := i.path, clauseFails := i.node.view.assume.map fun a => (a.name, 0, 0) }
  let mut cov : Array Nat := c.coverage.map fun _ => 0
  let mut stepsRun := 0
  let mut skipped := 0
  let mut seen : Array OutputSeen := Array.replicate m.output.size {}
  let run ← n.start
  let logH ← match cfg.logFile with
    | some f => some <$> IO.FS.Handle.mk f .write
    | none => pure none
  if let some h := logH then
    h.putStrLn ("case,step," ++ ",".intercalate (m.output.toList.map (·.name)))
  let t0 ← IO.monoNanosNow
  for ci in [0:cfg.cases] do
    let (po, g1) := smp.params.run rng
    rng := g1
    let some params := po | skipped := skipped + 1; continue
    let allParams ← run.init params
    let (cg0, g2) := smp.startCase.run rng
    rng := g2
    let mut cg := cg0
    let mut inputs : Array Record := #[]
    let mut outputs : Array Record := #[]
    let mut logs : Array InstLog :=
      inner.mapIdx fun j i => { path := i.path, params := allParams[j+1]! }
    -- whether each instance's assumption has held at every step so far (root first)
    let mut sofar : Array Bool := Array.replicate insts.size true
    let mut caseOk := true
    for k in [0:cfg.steps] do
      let ((found, cg'), g3) := (smp.input params cg k).run rng
      rng := g3
      cg := cg'
      let some inp := found | caseOk := false; break
      let (out, ex) ← run.step inp
      if let some h := logH then
        h.putStrLn (s!"{ci},{k}," ++ ",".intercalate
          ((m.output.zip out).toList.map fun (f, w) => f.type.showWord w))
      inputs := inputs.push inp
      outputs := outputs.push out
      for j in [0:logs.size] do
        let (ji, jo) := ex[j+1]!
        logs := logs.modify j fun l =>
          { l with inputs := l.inputs.push ji, outputs := l.outputs.push jo }
      stepsRun := stepsRun + 1
      for fi in [0:m.output.size] do
        seen := seen.modify fi (·.add m.output[fi]!.type out[fi]!)
      let mk (_ : Unit) : CaseRecord := ⟨ci, params, inputs, outputs, logs⟩
      let env := params ++ inp ++ out
      for oi in [0:cov.size] do
        if c.coverage[oi]!.expr.holds env then cov := cov.modify oi (· + 1)
      -- the node under test (its assumption holds by generation; checked all the same)
      if sofar[0]! && !assumeHolds c env then sofar := sofar.set! 0 false
      if sofar[0]! then
        for si in [0:stats.size] do
          stats := stats.modify si (·.observe env ci k mk)
      -- monitors of the inner instances
      let mut si := 0
      for j in [0:inner.size] do
        let v := inner[j]!.node.view
        let (ji, jo) := ex[j+1]!
        let jenv := allParams[j+1]! ++ ji ++ jo
        let fails := v.assume.map fun a => !a.expr.holds jenv
        let ok := fails.all (!·)
        let first := sofar[j+1]! && !ok
        if first then sofar := sofar.set! (j+1) false
        let still := sofar[j+1]!
        astats := astats.modify j fun a =>
          { a with steps := a.steps + 1, held := a.held + (if ok then 1 else 0),
                   heldSoFar := a.heldSoFar + (if still then 1 else 0),
                   failedCases := a.failedCases + (if first then 1 else 0),
                   firstFail := if first && a.firstFail.isNone then some (mk (), k)
                     else a.firstFail,
                   clauseFails := a.clauseFails.mapIdx fun ai (nm, st, fc) =>
                     if fails[ai]! then (nm, st + 1, fc + (if first then 1 else 0))
                     else (nm, st, fc) }
        for _ in v.guarantee do
          if still then istats := istats.modify si (·.observe jenv ci k mk)
          si := si + 1
    unless caseOk do skipped := skipped + 1
    if (ci + 1) % 500 == 0 then log s!"  {ci + 1}/{cfg.cases} cases, {stepsRun} steps"
  let t1 ← IO.monoNanosNow
  run.stop
  let hashOf := run.moduleHash
  let manifest := match run with
    | .module p => some p.manifest
    | .system .. => none
  return { seen, cfg, stats, stepsRun, casesSkipped := skipped,
           seconds := (t1 - t0).toFloat / 1e9, codeHash := n.codeHash hashOf, manifest,
           insts, instHashes := insts.map (·.node.codeHash hashOf), inner := istats,
           assumes := astats, regime := smp.regime,
           coverage := c.coverage.zip cov }

/-! ### Replay -/

/-- What a replay found. -/
structure ReplayOutcome where
  steps : Nat
  identical : Bool
  firstMismatch : Option Nat

/-- An inner instance's log read back from a case file: its slot among the instances of the
subtree being replayed, and its records. -/
private structure LoggedInst where
  slot : Nat
  log : InstLog

/-- Run `n` (at `path`) on a logged parameter record and input records, compare its outputs bit
for bit with the logged ones, and the inputs and outputs of every logged inner instance. Prints
every step of the node itself and every inner mismatch. -/
private def replayRun (n : CNode) (path : String) (title fileHash : String) (params : Record)
    (ins outs : Array Record) (inner : Array LoggedInst) : IO ReplayOutcome := do
  let c := n.view
  let m := c.m
  let run ← n.start
  let hash := n.codeHash run.moduleHash
  IO.println title
  IO.println s!"  recorded with code hash {fileHash}"
  let rel := if fileHash == hash then " (same)"
    else if fileHash.length == 64 then " (a DIFFERENT build)" else ""
  let label := match n with
    | .module _ => "executable code hash   "
    | .system _ => "code hash now          "
  IO.println s!"  {label} {hash}{rel}"
  IO.println s!"  params: {params.text m.params}"
  let allParams ← run.init params
  let insts := n.instances path
  let mut innerBad := 0
  for li in inner do
    unless allParams[li.slot]! == li.log.params do
      innerBad := innerBad + 1
      IO.println s!"  {li.log.path}: parameter record ≠ the logged one"
  let mut identical := true
  let mut first : Option Nat := none
  -- a capped case records the outputs of its last steps only: compare those
  let off := ins.size - outs.size
  for k in [0:ins.size] do
    let (out, ex) ← run.step ins[k]!
    let same := k < off || out == outs[k - off]!
    if !same then
      identical := false
      if first.isNone then first := some k
    let env := params ++ ins[k]! ++ out
    let failing := c.guarantee.filter (fun g => !g.expr.holds env) |>.map (·.name)
    let flag := if same then "=" else "≠"
    let fail := if failing.isEmpty then "" else s!"  violates: {", ".intercalate failing.toList}"
    IO.println s!"  step {k}: {ins[k]!.text m.input}"
    IO.println s!"       {flag} {out.text m.output}{fail}"
    if !same then IO.println s!"     recorded {outs[k - off]!.text m.output}"
    for li in inner do
      let im := insts[li.slot]!.node.view.m
      let (ji, jo) := ex[li.slot]!
      let okIn := li.log.inputs[k]? == some ji
      let okOut := li.log.outputs[k]? == some jo
      unless okIn && okOut do
        innerBad := innerBad + 1
        if first.isNone then first := some k
        IO.println s!"    {li.log.path}: {if okIn then "" else "input ≠ logged; "}\
          {if okOut then "" else "output ≠ logged"}"
        IO.println s!"      now    {ji.text im.input} → {jo.text im.output}"
  run.stop
  IO.println (if identical then
      s!"outputs bit-identical to the recorded ones at all {outs.size} recorded steps \
        (of {ins.size})"
    else s!"outputs DIFFER from the recorded ones (first at step {first.getD 0})")
  unless inner.isEmpty do
    IO.println (if innerBad == 0 then
      s!"inner instances ({inner.size}): parameter, input and output records bit-identical to \
        the log at all {ins.size} steps"
      else s!"inner instances: {innerBad} records DIFFER from the log")
  return { steps := ins.size, identical := identical && innerBad == 0, firstMismatch := first }

/-- Run a saved case and compare bit for bit. With `child`, the instance at that path (relative
to the outermost node, or in full) is re-run alone, in a fresh process tree, from its logged
parameter and input records. -/
def replayFile (findNode : String → Option Node) (file : System.FilePath)
    (child : Option String := none) : IO ReplayOutcome := do
  let txt ← IO.FS.readFile file
  let j ← IO.ofExcept (Json.parse txt)
  let name ← match j.getObjValAs? String "module", j.getObjValAs? String "system" with
    | .ok n, _ | _, .ok n => pure n
    | _, _ => throw (IO.userError s!"{file}: neither a module nor a system case")
  let some node := findNode name | throw (IO.userError s!"no module or system named {name}")
  let root ← IO.ofExcept node.check
  let logs := (j.getObjValAs? (Array Json) "instances").toOption.getD #[]
  let logPath (l : Json) : String := (l.getObjValAs? String "path").toOption.getD ""
  -- the logged instances below `path`, read against the instances of the subtree at `path`
  let innerOf (sub : CNode) (path : String) : IO (Array LoggedInst) := do
    let insts := sub.instances path
    let mut out := #[]
    for l in logs do
      let q := logPath l
      if !q.startsWith (path ++ "/") then continue
      let some slot := insts.findIdx? (·.path == q)
        | throw (IO.userError s!"{file}: logged instance {q} is not in {path}")
      let im := insts[slot]!.node.view.m
      let ps ← IO.ofExcept (recordOfJson im.params (← IO.ofExcept (l.getObjVal? "params")))
      let is ← IO.ofExcept ((← IO.ofExcept (l.getObjValAs? (Array Json) "inputs")).mapM
        (recordOfJson im.input))
      let os ← IO.ofExcept ((← IO.ofExcept (l.getObjValAs? (Array Json) "outputs")).mapM
        (recordOfJson im.output))
      out := out.push ⟨slot, { path := q, params := ps, inputs := is, outputs := os }⟩
    return out
  let records (src : Json) (sub : CNode) : IO (Record × Array Record × Array Record) := do
    let sm := sub.view.m
    -- a case whose parameters are in its inputs file (`params_in`)
    let paramsJ ← match src.getObjVal? "params", src.getObjValAs? String "inputs_file" with
      | .ok j, _ => pure j
      | .error _, .ok f => do
        let ij ← IO.ofExcept (Json.parse (← IO.FS.readFile ((file.parent.getD ".") / f)))
        IO.ofExcept (ij.getObjVal? "params")
      | .error e, .error _ => throw (IO.userError s!"{file}: {e}")
    let ps ← IO.ofExcept (recordOfJson sm.params paramsJ)
    let is ← match src.getObjValAs? String "inputs_file" with
      | .ok f =>
        -- a long case's inputs, kept once per case next to this file and bound by its hash
        let p := (file.parent.getD ".") / f
        let h ← Sha256.hashFile p
        let want ← IO.ofExcept (src.getObjValAs? String "inputs_sha256")
        unless h == want do
          throw (IO.userError s!"{p}: sha256 {h}, the case names {want}")
        let ij ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
        let all ← IO.ofExcept (inputsOfIndexedJson sm.input
          (← IO.ofExcept (ij.getObjValAs? (Array Json) "inputs_indexed")))
        let cnt ← IO.ofExcept (src.getObjValAs? Nat "inputs_count")
        unless cnt ≤ all.size do
          throw (IO.userError s!"{p} holds {all.size} input records, the case needs {cnt}")
        pure (all.extract 0 cnt)
      | .error _ => do
        let ijs ← IO.ofExcept (src.getObjValAs? (Array Json) "inputs")
        IO.ofExcept (if (src.getObjValAs? Bool "inputs_delta").toOption.getD false
          then inputsOfDeltaJson sm.input ijs else ijs.mapM (recordOfJson sm.input))
    let os ← match src.getObjValAs? (Array Json) "outputs_words" with
      | .ok rows => IO.ofExcept (rows.mapM fun row => do
          let ws ← row.getArr?
          unless ws.size == sm.output.size do
            throw s!"an output record of {ws.size} words, the schema has {sm.output.size} fields"
          (sm.output.zip ws).mapM fun (f, w) => do
            let t ← w.getStr?
            match f.type.parseWord? t with
            | some x => pure x
            | none => throw s!"field {f.name}: cannot read '{t}' as {f.type.name}")
      | .error _ => IO.ofExcept ((← IO.ofExcept (src.getObjValAs? (Array Json) "outputs")).mapM
          (recordOfJson sm.output))
    return (ps, is, os)
  let hashIn (src : Json) := (src.getObjValAs? String "code_hash").toOption.getD "?"
  match child with
  | none =>
    let (ps, is, os) ← records j root
    replayRun root root.name s!"replay {file}: {root.kind} {root.name}, {is.size} steps"
      (hashIn j) ps is os (← innerOf root root.name)
  | some p =>
    let full := if p.startsWith (root.name ++ "/") then p else s!"{root.name}/{p}"
    let insts := root.instances root.name
    let some inst := insts.find? (·.path == full)
      | throw (IO.userError s!"{root.name} has no instance {full}; instances: \
          {", ".intercalate (insts.toList.drop 1 |>.map (·.path))}")
    let some l := logs.find? (logPath · == full)
      | throw (IO.userError s!"{file} has no log of instance {full}")
    let (ps, is, os) ← records l inst.node
    replayRun inst.node full
      s!"replay {file}, instance {full} alone: {inst.node.kind} {inst.node.name}, {is.size} steps"
      (hashIn l) ps is os (← innerOf inst.node full)

end Harness
