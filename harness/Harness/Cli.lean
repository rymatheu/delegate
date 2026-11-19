import Lean.Data.Json
import Harness.Ledger
import Harness.Compose
import Harness.LinkPlan

/-! The commands of a harness executable, shared by the `harness` command (with its registry of
modules and systems) and by a compiled top-level harness (`Harness.runMain`). Run from the
harness directory (paths are relative to it). -/

namespace Harness.Cli

open Harness
open Lean (Json)

/-- What the commands can name: nodes by name (a composition may fail; its error is shown when
the node is named), and the program's name for usage and recorded commands. -/
structure Env where
  /-- each node behind a function, so that a system is composed only when it is named (a
  registry of constants would compose every system at program start) -/
  nodes : List (String × (Unit → Except String Node))
  /-- what `list` shows of the systems without composing them: their stacks as the registry
  states them (checked against the composed system when it is named) -/
  systems : List (String × Stack) := []
  prog : String := "harness"

/-- The entry of that name, composed. -/
def Env.find (e : Env) (name : String) : Option (Except String Node) :=
  (e.nodes.find? (·.1 == name)).map fun (_, f) => do
    let n ← f ()
    if let some k := (e.systems.find? (·.1 == name)).map (·.2) then
      let k' ← n.stack
      unless k' == k do
        throw s!"the registry lists {name} under {k.name}, its children give {k'.name}"
    return n

/-- The named node, checked. -/
def Env.getNode (e : Env) (name : String) : IO CNode := do
  match e.find name with
  | none => throw (IO.userError s!"no module or system named {name} \
      (known: {", ".intercalate (e.nodes.map (·.1))})")
  | some (.error msg) => throw (IO.userError s!"{name} is not a valid node: {msg}")
  | some (.ok n) => IO.ofExcept n.check

/-- The nodes that are valid, for replay. -/
def Env.findNode (e : Env) (name : String) : Option Node :=
  match e.find name with
  | some (.ok n) => some n
  | _ => none

/-- Pad with spaces to `n` characters. -/
def pad (s : String) (n : Nat) : String := s.pushn ' ' (n - s.length)

/-- A margin for people, `-` when there is none. -/
def fmtMargin : Option Float → String
  | some x => F32.fmt x
  | none => "-"

/-- `harness gen NAME`. -/
def cmdGen (env : Env) (name : String) : IO Unit := do
  let .module c ← env.getNode name
    | throw (IO.userError s!"{name} is a system; `gen` writes the records of a module")
  let dir : System.FilePath := "build" / "gen" / name
  IO.FS.createDirAll dir
  let f := dir / "module_records.h"
  IO.FS.writeFile f c.m.recordsHeader
  IO.println s!"wrote {f}"
  -- the same schemas as JSON, for modules not written in C++ (py/module_protocol.py)
  let sj (s : Schema) := Json.arr (s.map fun x => Json.mkObj
    [("name", Json.str x.name), ("type", Json.str x.type.name), ("doc", Json.str x.doc)])
  let fj := dir / "module_schema.json"
  IO.FS.writeFile fj ((Json.mkObj [("name", Json.str c.m.name), ("params", sj c.m.params),
    ("input", sj c.m.input), ("output", sj c.m.output)]).pretty ++ "\n")
  IO.println s!"wrote {fj}"

/-- `harness describe NAME`. -/
def cmdDescribe (env : Env) (name : String) : IO Unit := do
  let n ← env.getNode name
  match n with
  | .module c =>
    let man ← describeModule c.m
    IO.println s!"module    {man.name}"
    IO.println s!"code hash {man.codeHash}"
    IO.println s!"compiler  {man.compiler}"
    IO.println s!"flags     {man.flags}"
    IO.println s!"params    {man.params.text}"
    IO.println s!"input     {man.input.text}"
    IO.println s!"output    {man.output.text}"
    IO.println "schemas match the Lean declaration"
  | .system s =>
    let mut hs : Array (String × String) := #[]
    for m in n.modules do
      hs := hs.push (m.name, (← describeModule m).codeHash)
    let hashOf (m : Module) := ((hs.find? (·.1 == m.name)).map (·.2)).getD "?"
    IO.println s!"system    {name}"
    IO.println s!"code hash {n.codeHash hashOf}  (its wiring and its children's code hashes)"
    IO.println s!"params    {s.view.m.params.text}"
    IO.println s!"input     {s.view.m.input.text}"
    IO.println s!"output    {s.view.m.output.text}"
    for i in (n.instances name).toList.drop 1 do
      IO.println s!"  {pad i.path 20} {i.node.kind} {i.node.name}, \
        code hash {i.node.codeHash hashOf}"
    IO.println s!"every module executable matches its Lean declaration ({hs.size} executables)"

/-- `harness tree NAME`. -/
def cmdTree (env : Env) (name : String) (depth : Nat := 1000) : IO Unit := do
  let n ← env.getNode name
  let v := n.view.m
  IO.println s!"{name} ({n.kind}, {n.stack.name}): params {v.params.size}, \
    input {v.input.size}, output {v.output.size} fields"
  for l in n.treeLines "" depth do IO.println l

/-- `harness obligations NAME`: every assumption clause of an instance that rests on what its
siblings or constants feed it (to be discharged by the siblings' guarantees; the monitors check
it at the instance). -/
def cmdObligations (env : Env) (name : String) (status : Bool := false) : IO UInt32 := do
  let n ← env.getNode name
  let obs := n.obligations name
  if obs.isEmpty then IO.println s!"{name}: no obligations"
  let insts := n.instances name
  -- the stated discharges of every system of the tree, with the system's path
  let held : Array (String × CNode × Discharge) := insts.foldl (init := #[]) fun acc i =>
    match i.node with
    | .system cs => acc ++ (cs.decl.discharges.toArray.map fun d => (i.path, i.node, d))
    | .module _ => acc
  -- how the link theorem's plan obtains each assumption clause (Harness/LinkPlan.lean)
  let accts := Link.accounts 1000 name n
  let mut provedN := 0
  let mut statedN := 0
  let mut openN := 0
  let mut badN := 0
  for o in obs do
    IO.println s!"{o.path}  {o.clause}"
    for (f, src) in o.fields do IO.println s!"    {f} ← {src}"
    if status then
      let entry := held.find? fun (p, _, d) => s!"{p}/{d.path}" == o.path && d.clause == o.clause
      -- every named clause must exist: PATH.clause a guarantee of that instance, assume.clause
      -- an assumption clause of the system that states the discharge
      if let some (p, holder, d) := entry then
        let missing := d.by_.filter fun b =>
          match b.splitOn "." with
          | ["assume", c] => !(holder.view.assume.any (·.name == c))
          | [ip, c] => match insts.find? (·.path == s!"{p}/{ip}") with
            | some i => !(i.node.view.guarantee.any (·.name == c))
            | none => true
          | _ => true
        unless missing.isEmpty do
          badN := badN + 1
          IO.println s!"    NAMED CLAUSES NOT FOUND: {", ".intercalate missing}"
      let tableLine : String := match entry with
        | some (_, _, d) => s!" [table: {d.kind}{if d.by_.isEmpty then "" else
            s!", {", ".intercalate d.by_}"}]"
        | none => " [table: no entry]"
      let acct : Option Link.AAcct :=
        (accts.find? fun (p, c, _) => p == o.path && c == o.clause).map (·.2.2)
      match acct with
      | some (.own _) =>
        provedN := provedN + 1
        IO.println s!"  PROVED: the composite's own assumption clause, through the wires \
          (transport checker){tableLine}"
      | some (.checked _ by_) =>
        provedN := provedN + 1
        IO.println s!"  PROVED by the range checker from {", ".intercalate by_}{tableLine}"
      | some (.cited _ by_) =>
        statedN := statedN + 1
        IO.println s!"  STATED, not proved: a hypothesis of the link theorem (CitedDis) from \
          {", ".intercalate by_}"
      | some (.open_ why) =>
        openN := openN + 1
        IO.println s!"  OPEN: {why}{tableLine}"
      | none =>
        openN := openN + 1
        IO.println s!"  OPEN: not in the link theorem's plan{tableLine}"
      if let some (_, _, d) := entry then
        unless d.note.isEmpty do IO.println s!"    {d.note}"
  if status then
    IO.println s!"{obs.size} obligations: {provedN} proved (transport or range checker), \
      {statedN} stated (hypotheses of the link theorem), {openN} open\
      {if badN > 0 then s!", {badN} citing clauses that do not exist" else ""}"
  return if badN > 0 then 1 else 0

private def clauseRow (st : ClauseStat) (name : String) (w : Nat) : String :=
  let at_ := match st.minAt with | some (a, b) => s!"({a}, {b})" | none => ""
  s!"{pad name w} {pad (toString st.checked) 9} {pad (toString st.violations) 10}  \
    {fmtMargin st.minMargin} {at_}"

/-- Print what a campaign found. -/
def printResult (n : CNode) (r : CampaignResult) : IO Unit := do
  let m := n.view.m
  IO.println s!"code hash {r.codeHash}"
  let rate := (r.stepsRun.toFloat / r.seconds).round.toUInt64
  IO.println s!"{r.stepsRun} steps in {F32.fmt r.seconds} s ({rate} steps/s through the pipe, \
    contract checks included); {r.casesSkipped} cases skipped"
  if let some rg := r.regime then IO.println s!"regime {rg.name}: {rg.text}"
  if r.stepsRun == 0 then IO.println "EMPTY CAMPAIGN: no step ran (every case was skipped)"
  IO.println "guarantee clauses, checked while the assumption had held so far in the case:"
  let w := r.stats.foldl (fun w st => max w (st.clause.name.length + 1)) 20
  IO.println s!"{pad "clause" w} {pad "checked" 9} {pad "violations" 10}  \
    smallest margin (case, step)"
  for st in r.stats do
    IO.println (clauseRow st st.clause.name w)
    if let some (cr, k) := st.cex then
      IO.println s!"{pad "" w}   first counterexample: case {cr.index}, step {k}"
  unless r.inner.isEmpty && r.assumes.isEmpty do
    IO.println "inner clauses, monitored while the instance's assumption had held so far in \
      the case:"
    let iw := r.inner.foldl (fun w st => max w (st.path.length + st.clause.name.length + 3)) 36
    IO.println s!"{pad "path  clause" iw} {pad "checked" 9} {pad "violations" 10}  \
      smallest margin (case, step)"
    for st in r.inner do
      IO.println (clauseRow st s!"{st.path}  {st.clause.name}" iw)
      if let some (cr, k) := st.cex then
        IO.println s!"{pad "" iw}   first counterexample: case {cr.index}, step {k}"
    IO.println "inner assumptions (to be discharged by the system):"
    for a in r.assumes do
      let ff := match a.firstFail with
        | some (cr, k) => s!"; DISCHARGE FAILURE in {a.failedCases} cases, first at case \
            {cr.index}, step {k}"
        | none => ""
      IO.println s!"  {pad a.path 34} held at {a.held} of {a.steps} steps, had held so far \
        at {a.heldSoFar}{ff}"
      for (nm, st, fc) in a.clauseFails do
        if st > 0 then
          IO.println s!"  {pad "" 34}   {nm} failed at {st} steps, in the first failure of \
            {fc} cases"
  IO.println "outputs seen:"
  for (f, o) in m.output.zip r.seen do
    if f.type == .bool then IO.println s!"  {pad f.name 16} true at {o.trues} steps"
    else IO.println s!"  {pad f.name 16} finite range [{fmtMargin o.lo}, {fmtMargin o.hi}], \
      non-finite at {o.nonFinite} steps"
  unless r.coverage.isEmpty do
    IO.println "coverage (steps at which the observation was true):"
    for (cl, k) in r.coverage do
      IO.println s!"  {pad cl.name 28} {k} of {r.stepsRun} steps   {cl.expr.print}"

/-- `harness test NAME`: exit code 0 when no clause was violated and, for a system, no inner
clause was violated and every inner assumption was discharged. -/
def cmdTest (env : Env) (name : String) (cfg : CampaignConfig) (command : String) :
    IO UInt32 := do
  let n ← env.getNode name
  let rg := match cfg.regime with | some r => s!", regime {r}" | none => ""
  IO.println s!"{name}: campaign seed {cfg.seed}, {cfg.cases} cases x {cfg.steps} steps{rg}"
  IO.println n.view.m.contract.text
  let r ← runCampaign n cfg (fun s => IO.println s)
  printResult n r
  let f ← recordCampaign n r command
  IO.println s!"result: {f}"
  let nrec := r.stats.size + r.inner.size + r.assumes.size
  IO.println s!"ledger: {nrec} records appended to {ledgerPath n}"
  return if r.passed then 0 else 1

/-- One status line (and the evidence files) of a clause. `label` says what kind of evidence
backs it. -/
def printClauseStatus (indent name label : String) (w : Nat) (st : ClauseStatus) : IO Unit := do
  let get (r : Json) (k : String) : String :=
    match r.getObjVal? k with
    | .ok (.str s) => s
    | .ok j => j.compress
    | .error _ => "?"
  let num (r : Json) (k : String) : Nat := (r.getObjValAs? Nat k).toOption.getD 0
  let files (rs : Array Json) := ", ".intercalate (rs.toList.map (get · "result_file"))
  match st with
  | .backed rs =>
    let checks := rs.foldl (fun n r => n + num r "checked") 0
    let margins := rs.filterMap fun r => (r.getObjValAs? Float "smallest_margin").toOption
    let mg := if margins.isEmpty then "" else
      s!", smallest margin {F32.fmt (margins.foldl min margins[0]!)}"
    -- campaigns per regime
    let rgOf (r : Json) : String := (r.getObjValAs? String "regime").toOption.getD "no regime"
    let rgs := (rs.map rgOf).toList.eraseDups
    let per := if rgs == ["no regime"] then "" else
      " (" ++ ", ".intercalate (rgs.map fun g =>
        let sel := rs.filter (rgOf · == g)
        s!"{g}: {sel.size}, {sel.foldl (fun n r => n + num r "checked") 0} checks") ++ ")"
    IO.println s!"{indent}{pad name w} {pad "backed" 9} {label}: {rs.size} campaigns, \
      {checks} checks{mg}{per}"
    for r in rs do IO.println s!"{indent}{pad "" (w + 10)} {get r "result_file"}"
  | .failed rs =>
    IO.println s!"{indent}{pad name w} {pad "failed" 9} counterexample found: {files rs}"
  | .undischarged rs =>
    IO.println s!"{indent}{pad name w} {pad "undischarged" 9} a served session with a discharge \
      failure (checks not backed): {files rs}"
  | .empty rs =>
    IO.println s!"{indent}{pad name w} {pad "empty" 9} only empty campaigns (0 checks): \
      {files rs}"
  | .stale reasons =>
    IO.println s!"{indent}{pad name w} {pad "stale" 9} {"; ".intercalate reasons}"
  | .unbacked =>
    IO.println s!"{indent}{pad name w} {pad "unbacked" 9} no evidence"

/-- Whether a module's sources changed since its executable was built. -/
def printSources (indent : String) (m : Module) (codeHash : String) : IO Unit := do
  match ← recomputeCodeHash m with
  | some (h, changed) =>
    if h == codeHash && changed.isEmpty then
      IO.println s!"{indent}sources: every file the compiler read is unchanged since the build"
    else
      IO.println s!"{indent}sources: CHANGED since the executable was built \
        ({changed.size} files); rebuild with {m.stack.buildCommand m.name}"
      for f in changed do IO.println s!"{indent}  {f}"
  | none => IO.println s!"{indent}sources: no build record (build/modules/NAME/code_inputs.txt)"

/-- `harness status NAME` for a system: own clauses, inner clauses, children, formal link. -/
def systemStatus (n : CNode) (s : CSys) : IO Unit := do
  let name := n.name
  let hashOf ← describeHashes n
  let codeHash := n.codeHash hashOf
  IO.println s!"system {name}"
  IO.println s!"  code hash {codeHash} (its wiring and its children's code hashes)"
  for m in n.modules do
    IO.println s!"  module {m.name}: executable {m.exe}, code hash {hashOf m}"
    printSources "    " m (hashOf m)
  IO.println s!"  own clauses (tested as a unit, or monitored in served sessions):"
  IO.println s!"    {pad "clause" 26} {pad "status" 9} evidence"
  for (g, st) in ← ownStatuses n codeHash do
    printClauseStatus "    " g.name "tested" 26 st
  IO.println s!"  inner clauses (monitored in {name}, as wired and excited here):"
  let insts := (n.instances name).toList.drop 1
  let iw := insts.foldl (fun w i => i.node.view.guarantee.foldl
    (fun w g => max w (i.path.length + g.name.length + 3)) (max w (i.path.length + 15))) 36
  IO.println s!"    {pad "path  clause" iw} {pad "status" 9} evidence"
  let records ← readLedger n
  let obs := n.obligations name
  for i in insts do
    let c := i.node.view.m.contract
    let sc := n.view.m.contract
    let a ← clauseStatus records codeHash (innerHash sc (assumptionHash c)) assumptionClause
      (some i.path)
    printClauseStatus "    " s!"{i.path}  {assumptionClause}" "discharged at every step" iw a
    for o in obs.filter (·.path == i.path) do
      IO.println s!"      obligation {o.clause}: \
        {", ".intercalate (o.fields.map fun (f, src) => s!"{f} ← {src}")}"
    for g in i.node.view.guarantee do
      let st ← clauseStatus records codeHash (innerHash sc (c.clauseHash g)) g.name (some i.path)
        (assumptionHashesNow n)
      printClauseStatus "    " s!"{i.path}  {g.name}" "monitored (assumption held so far)" iw st
  IO.println s!"  children (their own evidence, alone):"
  for ch in s.children do
    let k := ch.node
    let sts ← ownStatuses k (k.codeHash hashOf)
    IO.println s!"    {pad ch.name 12} {k.name} ({k.kind}): {statusSummary (sts.map (·.2))}"
  let (_, lc) := Link.treeLines 1000 name n
  IO.println s!"  formal link: {lc.summary} (command `link {name}`)"

/-- `harness link NAME`: the plan of the link theorem (docs/10-formal-link.md): how each clause
the theorem needs is obtained, the counts, and the statement with its named hypotheses. -/
def cmdLink (env : Env) (name : String) : IO Unit := do
  let n ← env.getNode name
  match n with
  | .module _ => IO.println s!"{name} is a module: its contract is a leaf claim (LeafClaim)"
  | .system _ =>
    let (ls, c) := Link.treeLines 1000 name n
    for l in ls do IO.println l
    IO.println ""
    IO.println (Link.statement n)
    IO.println ""
    IO.println s!"formal link: {c.summary}"

/-- `harness status NAME`. -/
def cmdStatus (env : Env) (name : String) : IO Unit := do
  let n ← env.getNode name
  match n with
  | .system s => systemStatus n s
  | .module c =>
    let m := c.m
    let man? ← try pure (some (← describeModule m)) catch e => do
      IO.println s!"executable: {e}"
      pure none
    let codeHash := (man?.map (·.codeHash)).getD "(no executable)"
    IO.println s!"module {m.name}"
    IO.println s!"  executable {m.exe}: code hash {codeHash}"
    printSources "  " m codeHash
    IO.println s!"  {pad "clause" 20} {pad "status" 9} evidence"
    for (g, st) in ← ownStatuses n codeHash do
      printClauseStatus "  " g.name "tested" 20 st

/-- The options of `harness test`. -/
def parseFlags (args : List String) : Except String CampaignConfig := do
  let rec go (cfg : CampaignConfig) : List String → Except String CampaignConfig
    | [] => pure cfg
    | "--seed" :: v :: rest => do go { cfg with seed := ← num v } rest
    | "--cases" :: v :: rest => do go { cfg with cases := ← num v } rest
    | "--steps" :: v :: rest => do go { cfg with steps := ← num v } rest
    | "--regime" :: v :: rest => go { cfg with regime := some v } rest
    | "--log" :: v :: rest => go { cfg with logFile := some v } rest
    | a :: _ => throw s!"unknown option {a}"
  go {} args
where
  num (v : String) : Except String Nat := match v.toNat? with
    | some n => pure n
    | none => throw s!"not a number: {v}"


/-! ### Equivalence -/

/-- `harness equiv A B`: run `A` and `B` on the same parameter and input records, drawn from
`A`'s assumption (and regime), matching fields by name, and compare the outputs they have in
common bit for bit at every step. Fields only one side has are listed; `B` may not need a
parameter or input `A` lacks. Exit code 1 at the first difference. -/
def cmdEquiv (env : Env) (a b : String) (cfg : CampaignConfig) : IO UInt32 := do
  let na ← env.getNode a
  let nb ← env.getNode b
  let ma := na.view.m
  let mb := nb.view.m
  -- B's field i is A's field (map[i]); fields only one side has
  let corr (what : String) (sa sb : Schema) : IO (Array (Option Nat)) := do
    let onlyA := sa.filter fun f => !sb.any (·.name == f.name)
    let onlyB := sb.filter fun f => !sa.any (·.name == f.name)
    unless onlyA.isEmpty do
      IO.println s!"  {what} only in {a}: {", ".intercalate (onlyA.toList.map (·.name))}"
    unless onlyB.isEmpty do
      IO.println s!"  {what} only in {b}: {", ".intercalate (onlyB.toList.map (·.name))}"
    sb.mapM fun f => do
      match sa.findIdx? (·.name == f.name) with
      | some i =>
        unless sa[i]!.type == f.type do
          throw (IO.userError s!"{what} {f.name}: {sa[i]!.type.name} in {a}, \
            {f.type.name} in {b}")
        pure (some i)
      | none => pure none
  IO.println s!"equiv {a} {b}: seed {cfg.seed}, {cfg.cases} cases x {cfg.steps} steps\
    {match cfg.regime with | some r => s!", regime {r} of {a}" | none => ""}"
  let pm ← corr "params" ma.params mb.params
  let im ← corr "input" ma.input mb.input
  let om ← corr "output" ma.output mb.output
  if pm.any (·.isNone) || im.any (·.isNone) then
    IO.println s!"{b} needs a parameter or input {a} does not have: cannot feed it"
    return 2
  let pairs := (om.toList.zipIdx.filterMap fun (o, j) => o.map (·, j)).toArray
  IO.println s!"  comparing {pairs.size} outputs by name"
  let smp ← IO.ofExcept (Sampler.make na.view cfg.regime)
  let ra ← na.start
  let rb ← nb.start
  let stop : IO Unit := do ra.stop; rb.stop
  let mut rng : Rng := ⟨cfg.seed.toUInt64⟩
  let mut steps := 0
  for ci in [0:cfg.cases] do
    let (po, g1) := smp.params.run rng
    rng := g1
    let some params := po | continue
    let _ ← ra.init params
    let _ ← rb.init (pm.map fun i => params[i.getD 0]!)
    let (cg0, g2) := smp.startCase.run rng
    rng := g2
    let mut cg := cg0
    for k in [0:cfg.steps] do
      let ((found, cg'), g3) := (smp.input params cg k).run rng
      rng := g3
      cg := cg'
      let some inp := found | break
      let (oa, _) ← ra.step inp
      let (ob, _) ← rb.step (im.map fun i => inp[i.getD 0]!)
      steps := steps + 1
      for (i, j) in pairs do
        unless oa[i]! == ob[j]! do
          let f := ma.output[i]!
          IO.println s!"DIFFERENT at case {ci}, step {k}, output {f.name}: \
            {a} {f.type.showWord oa[i]!} ({f.type.wordText oa[i]!}), \
            {b} {f.type.showWord ob[j]!} ({f.type.wordText ob[j]!})"
          stop
          return 1
  stop
  if steps == 0 then
    IO.println "no step ran"
    return 1
  IO.println s!"bit-identical: {pairs.size} outputs at all {steps} steps"
  return 0

/-! ### Run and serve -/

/-- `harness run NAME`: one case (init once, then `steps` ticks) on generated records, with the
monitors; prints the summary and records nothing. -/
def cmdRun (env : Env) (name : String) (cfg : CampaignConfig) : IO UInt32 := do
  let n ← env.getNode name
  IO.println s!"{name}: run, seed {cfg.seed}, {cfg.steps} steps\
    {match cfg.regime with | some r => s!", regime {r}" | none => ""}"
  let r ← runCampaign n { cfg with cases := 1 } (fun _ => pure ())
  printResult n r
  return if r.passed then 0 else 1

private def readExactStdin (h : IO.FS.Stream) (n : Nat) : IO (Option ByteArray) := do
  let mut buf := ByteArray.emptyWithCapacity n
  while buf.size < n do
    let chunk ← h.read (n - buf.size).toUSize
    if chunk.isEmpty then return none
    buf := buf ++ chunk
  return some buf

private def u32Bytes (v : Nat) : ByteArray :=
  Record.encode #[{ name := "n", type := .u32 }] #[UInt32.ofNat v]

private def schemaJsonOf (s : Schema) : Json :=
  Json.arr (s.map fun f => Json.mkObj [("name", Json.str f.name), ("type", Json.str f.type.name)])

/-- `harness serve NAME`: the node as a module, speaking the module protocol of
cpp/module_protocol.h on stdin and stdout (`D`, `I`, `S`, `Q`), so a compiled harness can be a
child of another harness. The manifest's code hash is the node's code hash. The monitors run
inside: every node's assumption (history form) and guarantee clauses at every step; their
verdicts go to build/serve/NAME.log (stdout carries the protocol). At the end of a session with
at least one step, its monitored counts are written to the node's ledger (`recordServeSession`:
evidence/served/ID.json and the session log next to it). -/
def cmdServe (env : Env) (name : String) : IO UInt32 := do
  let n ← env.getNode name
  let run ← n.start
  let codeHash := n.codeHash run.moduleHash
  let m := n.view.m
  let insts := n.instances name
  IO.FS.createDirAll ("build" / "serve")
  let logPath : System.FilePath := "build" / "serve" / s!"{name}.log"
  let lg ← IO.FS.Handle.mk logPath .write
  let say (l : String) : IO Unit := do lg.putStrLn l; lg.flush
  say s!"serve {name}, code hash {codeHash}"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let reply (b : ByteArray) : IO Unit := do stdout.write b; stdout.flush
  let ok := ByteArray.mk #['K'.toNat.toUInt8]
  let mut params : Array Record := #[]
  let mut sofar : Array Bool := #[]
  let mut steps := 0
  let mut cases := 0
  -- per instance: assumption failures (cases); per (instance, clause): violations
  let mut afail : Array Nat := insts.map fun _ => 0
  let mut gviol : Array (Array Nat) := insts.map fun i => i.node.view.guarantee.map fun _ => 0
  -- for the ledger: checks per clause, assumption held per instance, first discharge failure
  let mut gcheck : Array (Array Nat) := insts.map fun i => i.node.view.guarantee.map fun _ => 0
  let mut held : Array Nat := insts.map fun _ => 0
  let mut firstFail : Array (Option (Nat × Nat)) := insts.map fun _ => none
  let mut afailLogged : Array Nat := insts.map fun _ => 0
  -- the session's ledger records (a session with no step records nothing)
  let record (st : ServedStats) : IO Unit := do
    if st.steps == 0 then return
    let f ← recordServeSession n codeHash s!"{env.prog} serve {name}" logPath st
    say s!"ledger: session recorded, {f}"
  let summary (afail : Array Nat) (gviol : Array (Array Nat)) (cases steps : Nat) : IO Unit := do
    say s!"summary: {cases} inits, {steps} steps"
    for (i, j) in insts.toList.zipIdx do
      let v := i.node.view
      let bad := (v.guarantee.zip gviol[j]!).filter (·.2 > 0)
      say s!"  {i.path}: assumption failed in {afail[j]!} cases; guarantee violations: \
        {if bad.isEmpty then "none" else
          ", ".intercalate (bad.toList.map fun (c, k) => s!"{c.name} at {k} steps")}"
  repeat
    let some op ← readExactStdin stdin 1 | break
    match Char.ofNat op[0]!.toNat with
    | 'D' =>
      let man := Json.mkObj [("name", Json.str name), ("code_hash", Json.str codeHash),
        ("flags", Json.str s!"harness system {name} served by {env.prog} serve"),
        ("compiler", Json.str toolVersion), ("params", schemaJsonOf m.params),
        ("input", schemaJsonOf m.input), ("output", schemaJsonOf m.output)]
      let t := man.compress.toUTF8
      reply (ok ++ u32Bytes t.size ++ t)
    | 'I' =>
      let some b ← readExactStdin stdin m.params.bytes | break
      params ← run.init (Record.decode m.params b)
      sofar := insts.map fun _ => true
      cases := cases + 1
      reply ok
    | 'S' =>
      let some b ← readExactStdin stdin m.input.bytes | break
      if params.isEmpty then reply (ByteArray.mk #['E'.toNat.toUInt8]); continue
      let (out, ex) ← run.step (Record.decode m.input b)
      steps := steps + 1
      for (i, j) in insts.toList.zipIdx do
        let v := i.node.view
        let (ji, jo) := ex[j]!
        let env := params[j]! ++ ji ++ jo
        let holdsNow := v.assume.all (·.expr.holds env)
        if holdsNow then held := held.modify j (· + 1)
        -- the failing clauses by name, at the first 50 failing steps of each instance
        if !holdsNow && afailLogged[j]! < 50 then
          afailLogged := afailLogged.modify j (· + 1)
          let bad := v.assume.filter fun c => !c.expr.holds env
          let fields := v.m.params ++ v.m.input ++ v.m.output
          let shown (c : Clause) : String := ", ".intercalate (c.expr.vars.eraseDups.map fun x =>
            match fields.findIdx? (·.name == x) with
            | some k => s!"{x}={fields[k]!.type.showWord env[k]!}"
            | none => x)
          say s!"init {cases}, step {steps}: {i.path}: assumption clause(s) failing: \
            {"; ".intercalate (bad.toList.map fun c => s!"{c.name} ({shown c})")}"
        if sofar[j]! && !holdsNow then
          sofar := sofar.set! j false
          afail := afail.modify j (· + 1)
          if firstFail[j]!.isNone then firstFail := firstFail.set! j (some (cases, steps))
          say s!"init {cases}, step {steps}: {i.path}: assumption failed (discharge failure)"
        if sofar[j]! then
          for (g, gi) in v.guarantee.toList.zipIdx do
            gcheck := gcheck.modify j (·.modify gi (· + 1))
            unless g.expr.holds env do
              if gviol[j]![gi]! == 0 then
                say s!"init {cases}, step {steps}: {i.path}: {g.name} violated"
              gviol := gviol.modify j (·.modify gi (· + 1))
      reply (ok ++ out.encode m.output)
    | 'Q' =>
      summary afail gviol cases steps
      reply ok
      run.stop
      record { inits := cases, steps, held, firstFail, checked := gcheck, violations := gviol }
      return 0
    | _ =>
      reply (ByteArray.mk #['E'.toNat.toUInt8])
      break
  summary afail gviol cases steps
  run.stop
  record { inits := cases, steps, held, firstFail, checked := gcheck, violations := gviol }
  return 0

/-! ### The command line -/

/-- The usage text for a program. -/
def usage (prog : String) (named : Bool) : String :=
  let N := if named then " NAME" else ""
  s!"usage:
  {prog} list [--compose]         the modules and the systems (--compose: compose every system)
  {prog} gen{N}                 write build/gen/NAME/module_records.h (modules only)
  {prog} contract{N}            print the contract and the regimes
  {prog} describe{N}            run the executables' describe, check them against Lean
  {prog} tree{N} [--depth D]    print a system's nesting: children, kinds and wires
  {prog} obligations{N} [--status]
                                   assumptions of instances that rest on their siblings;
                                   --status: how each is discharged, or open
  {prog} test{N} [--seed N] [--cases N] [--steps K] [--regime R]
                                   run a test campaign and record it in the ledger
  {prog} run{N} [--steps K] [--seed N] [--regime R] [--log FILE]
                                   one case with the monitors, nothing recorded
  {prog} replay FILE [--child PATH]
                                   rerun a saved case, or one instance of it alone
  {prog} status{N}              each guarantee clause: backed, stale, failed or unbacked
  {prog} link{N}                the link theorem's plan for a system: what is proved, what
                                   is a hypothesis (docs/10-formal-link.md)
  {prog} equiv A B [--seed N] [--cases N] [--steps K] [--regime R]
                                   same records into A and B, outputs compared bit for bit
  {prog} serve{N}               speak the module protocol on stdin/stdout"

/-- Run one command line against the nodes of `env`. -/
def dispatch (env : Env) (args : List String) : IO UInt32 := do
  try
    match args with
    | "list" :: opt =>
      -- grouped by stack (in the order of `Stack.all`), registry order within a stack; the
      -- systems the registry states a stack for are not composed (their doc is shown, and their
      -- validity checked, by `list --compose` or when they are named)
      let compose := opt == ["--compose"]
      unless opt.isEmpty || compose do throw (IO.userError "usage: list [--compose]")
      let stackOf (e : Except String Node) : Option Stack := (e >>= Node.stack).toOption
      let lazy (nm : String) : Option Stack :=
        if compose then none else (env.systems.find? (·.1 == nm)).map (·.2)
      let entries := env.nodes.map fun (nm, _) =>
        (nm, match lazy nm with | some k => (none, some k) | none => (some (env.find nm).get!, none))
      IO.println s!"{pad "name" 14} {pad "stack" 9} {pad "kind" 7} doc"
      for k in Stack.all do
        for (nm, e, lk) in entries do
          match e, lk with
          | none, some k' =>
            if k' == k then
              IO.println s!"{pad nm 14} {pad k.name 9} {pad "system" 7} (composed when named; \
                list --compose composes every system)"
          | some e, _ =>
            if let (.ok n, some k') := (e, stackOf e) then
              if k' == k then IO.println s!"{pad nm 14} {pad k.name 9} {pad n.kind 7} {n.view.doc}"
          | none, none => pure ()
      for (nm, e, _) in entries do
        match e with
        | some (.ok n) => if (stackOf (.ok n)).isNone then
            IO.println s!"{pad nm 14} {pad "?" 9} INVALID \
              {match n.stack with | .error msg => msg | .ok _ => ""}"
        | some (.error msg) => IO.println s!"{pad nm 14} {pad "?" 9} INVALID {msg}"
        | none => pure ()
      return 0
    | ["gen", n] => cmdGen env n; return 0
    | ["contract", n] =>
      let m := (← env.getNode n).view.m
      IO.println m.contract.text
      for r in m.regimes do IO.println s!"regime {r.name}: {r.text}"
      return 0
    | ["describe", n] => cmdDescribe env n; return 0
    | ["tree", n] => cmdTree env n; return 0
    | ["tree", n, "--depth", d] => cmdTree env n (d.toNat?.getD 1000); return 0
    | ["obligations", n] => cmdObligations env n
    | ["obligations", n, "--status"] => cmdObligations env n true
    | "test" :: n :: rest =>
      let cfg ← IO.ofExcept (parseFlags rest)
      cmdTest env n cfg (" ".intercalate (env.prog :: "test" :: n ::
        ["--seed", toString cfg.seed, "--cases", toString cfg.cases,
         "--steps", toString cfg.steps] ++
        (match cfg.regime with | some r => ["--regime", r] | none => [])))
    | "run" :: n :: rest => cmdRun env n (← IO.ofExcept (parseFlags rest))
    | "equiv" :: a :: b :: rest => cmdEquiv env a b (← IO.ofExcept (parseFlags rest))
    | ["serve", n] => cmdServe env n
    | ["replay", f] =>
      let o ← replayFile env.findNode f
      return if o.identical then 0 else 1
    | ["replay", f, "--child", p] =>
      let o ← replayFile env.findNode f (some p)
      return if o.identical then 0 else 1
    | ["status", n] => cmdStatus env n; return 0
    | ["link", n] => cmdLink env n; return 0
    | _ => IO.eprintln (usage env.prog true); return 2
  catch e =>
    IO.eprintln s!"{env.prog}: {e}"
    return 1

end Harness.Cli

namespace Harness

/-- The command line of a compiled top-level harness: every command of `harness` for the one
root node `top` (the NAME is implicit), e.g. `top tree`, `top test --regime flight`,
`top run --steps 200`, `top serve`. -/
def runMain (top : Except String Node) (args : List String) : IO UInt32 := do
  let name := match top with | .ok n => n.name | .error _ => "top"
  let env : Cli.Env := { nodes := [(name, fun _ => top)], prog := "top" }
  match args with
  | [] => IO.eprintln (Cli.usage "top" false); return 2
  | "replay" :: rest => Cli.dispatch env ("replay" :: rest)
  | "list" :: _ => Cli.dispatch env ["list"]
  | cmd :: rest => Cli.dispatch env (cmd :: name :: rest)

end Harness

namespace Harness

/-- Fail with the composition's or the check's error; for `#harness_check`. -/
def assertValid (n : Except String Node) : IO Unit :=
  match n >>= Node.check with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"harness check failed: {e}")

/-- `#harness_check t`: compose and check `t` when the file is built, so that a wiring mistake
is an error at this line of the build. -/
macro "#harness_check " t:term : command => `(#eval Harness.assertValid $t)

end Harness
