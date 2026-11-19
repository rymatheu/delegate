import Lean.Data.Json
import Harness.Campaign

/-! The evidence ledger. A node's evidence lives in its folder (`CNode.home`), STACK/modules/NAME
for a module, STACK/harnesses/NAME for a system, where STACK is the node's stack (`ardupilot`,
`px4` or `sim`):

  HOME/evidence/ledger.json          one record per contract clause per campaign (appended)
  HOME/evidence/tested/ID.json       a campaign's result file
  HOME/evidence/tested/ID/*.json     its replayable cases

Each ledger record names the clause, the kind of evidence (`tested`), the verdict, the tool, the
exact command, seed and counts, and three hashes: the code hash of the node, the contract hash of
the clause, and the hash of the result file. A clause is backed when a passing record matches all
three hashes as they are now; stale when records exist but none matches; unbacked when there is
no record.

A system's campaign adds `monitored` records, one per inner (path, clause), with a `path` field:
the clause is the inner instance's own, its contract hash is taken from that instance's contract,
and its code hash is the system's (they are facts about the child as wired in this system). The
clause `(assumption)` of an inner path records at how many steps that instance's assumption held;
a step where it did not is a discharge failure of the system. -/

namespace Harness

open Lean (Json)

/-- The tool named in ledger records. -/
def toolVersion : String := s!"harness 0.1.0 (Lean {Lean.versionString})"

/-- The evidence folder of a node. -/
def evidenceDir (n : CNode) : System.FilePath := n.home / "evidence"
/-- The ledger of a node. -/
def ledgerPath (n : CNode) : System.FilePath := evidenceDir n / "ledger.json"

/-- The clause name under which an inner instance's assumption (its discharge) is recorded. -/
def assumptionClause : String := "(assumption)"

/-- The contract hash of an inner instance's assumption as a whole. -/
def assumptionHash (c : Contract) : String :=
  Sha256.hashString s!"assume\n{c.assumeText}\n"

/-- The contract hash of a monitored record: the inner instance's clause hash, under the
assumption of the system it was monitored in. What a child does in a system depends on how the
system's assumption excites it, so a change of that assumption makes the monitored records
stale (the system's code hash covers the wiring only). -/
def innerHash (sys : Contract) (childHash : String) : String :=
  Sha256.hashString s!"system assume\n{sys.assumeText}\ninner clause {childHash}\n"

private def jsonFloat (x : Float) : Json :=
  if x.isNaN || x.isInf then Json.str (F32.fmt x)
  else if x == 0 then Json.num 0
  else
    let (neg, n, k) := F32.sig7 x
    let m : Int := if neg then -(n : Int) else n
    if k ≥ 0 then Json.num ⟨m * 10 ^ k.toNat, 0⟩ else Json.num ⟨m, (-k).toNat⟩

private def utcStamp : IO String := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%SZ"] }
  return out.stdout.trimAscii.toString

/-- The records of a node's ledger (none when it has no ledger yet). -/
def readLedger (n : CNode) : IO (Array Json) := do
  let p := ledgerPath n
  unless ← p.pathExists do return #[]
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
  IO.ofExcept (j.getObjValAs? (Array Json) "records")

/-- The contract of the instance at `path` among the campaign's instances. -/
private def instContract (r : CampaignResult) (path : String) : Contract :=
  ((r.insts.find? (·.path == path)).map (·.node.view.m.contract)).getD default

/-- Write the result file and the case files of a campaign, and append one ledger record per
guarantee clause (and, for a system, per inner clause and per inner assumption). Returns the
result file's path. -/
def recordCampaign (n : CNode) (r : CampaignResult) (command : String) : IO System.FilePath := do
  let m := n.view.m
  let stamp ← utcStamp
  let dir := evidenceDir n / "tested"
  -- two campaigns of one seed in the same second (another regime) get distinct ids
  let base := s!"{stamp}-seed{r.cfg.seed}"
  let mut id := base
  let mut dup := 2
  while ← (dir / s!"{id}.json").pathExists do
    id := s!"{base}-{dup}"
    dup := dup + 1
  let caseDir := dir / id
  IO.FS.createDirAll caseDir
  let shared ← IO.mkRef (#[] : Array ((Nat × Nat) × List (String × Json)))
  -- and its inputs are written once per case (`case{i}-inputs.json`, the longest saved prefix of
  -- the case), named with their hash by each (case, step) file: a long case of a composite with
  -- many free inputs would otherwise carry its whole input history in every such file
  let saved : Array CaseRecord :=
    (r.stats ++ r.inner).foldl (fun a st =>
      a ++ (st.cex.map (·.1)).toList.toArray ++ st.minCase.toList.toArray) #[] ++
    r.assumes.filterMap (·.firstFail.map (·.1))
  let mut longest : Array CaseRecord := #[]
  for cr in saved do
    if caseCapped cr then
      match longest.findIdx? (·.index == cr.index) with
      | some i => if longest[i]!.inputs.size < cr.inputs.size then longest := longest.set! i cr
      | none => longest := longest.push cr
  let mut files0 : Array (Nat × String × String) := #[]
  for cr in longest do
    let fname := s!"case{cr.index}-inputs.json"
    let f := caseDir / fname
    IO.FS.writeFile f ((caseInputsJson n r.codeHash id cr).compress ++ "\n")
    files0 := files0.push (cr.index, fname, ← Sha256.hashFile f)
  let inputFiles := files0
  -- every saved case is written once per (case, step) and shared by the clauses whose evidence it
  -- is: its records (the instance logs included) do not depend on the clause, and many clauses
  -- with their smallest margins at the same steps would each write a copy (modules too, since
  -- 2026-11-19; before, a module's saved case was one file per clause)
  let save (cr : CaseRecord) (k : Nat) : IO (List (String × Json)) := do
    if let some (_, e) := (← shared.get).find? (·.1 == (cr.index, k)) then return e
    let f := caseDir / s!"case{cr.index}-step{k}.json"
    let ref := if caseCapped cr then
        (inputFiles.find? (·.1 == cr.index)).map fun (_, fn, h) => (fn, h) else none
    IO.FS.writeFile f ((caseJson n r.insts r.instHashes r.codeHash id
      "saved case (shared by the clauses whose evidence it is)" "" none cr k ref).pretty ++ "\n")
    let e := [("file", Json.str f.toString), ("sha256", Json.str (← Sha256.hashFile f)),
      ("case", Json.num cr.index), ("step", Json.num k)]
    shared.modify (·.push ((cr.index, k), e))
    return e
  -- a clause never checked is not evidence: an empty campaign
  let verdict (st : ClauseStat) : String :=
    if st.violations != 0 then "failed" else if st.checked == 0 then "empty" else "passed"
  let discharge (a : AssumeStat) : String :=
    if a.failedCases != 0 then "failed" else if a.steps == 0 then "empty" else "passed"
  -- present only for a campaign in a regime, so other records keep their form; the regime's text
  -- is in the result file, a ledger record names it by its hash (a regime of a generated node can
  -- be hundreds of kilobytes, and a campaign writes one record per clause)
  let regimeFields : List (String × Json) := match r.regime with
    | some rg => [("regime", Json.str rg.name), ("regime_text", Json.str rg.text)]
    | none => []
  let regimeRef : List (String × Json) := match r.regime with
    | some rg => [("regime", Json.str rg.name), ("regime_hash", Json.str (Sha256.hashString rg.text))]
    | none => []
  let margin (st : ClauseStat) : Json :=
    match st.minMargin with | some x => jsonFloat x | none => Json.null
  -- one clause of the result file, with its saved cases
  let clauseJson (st : ClauseStat) (hash : String) : IO Json := do
    let g := st.clause
    let path := if st.path.isEmpty then none else some st.path
    let mut files : Array (String × Json) := #[]
    if let some (cr, k) := st.cex then
      files := files.push ("counterexample", Json.mkObj (← save cr k))
    if let some cr := st.minCase then
      let k := (st.minAt.map (·.2)).getD 0
      files := files.push ("smallest_margin_case", Json.mkObj (← save cr k))
    return Json.mkObj ((match path with | some p => [("path", Json.str p)] | none => []) ++ [
      ("clause", Json.str g.name), ("text", Json.str g.expr.print),
      ("contract_hash", Json.str hash),
      ("verdict", Json.str (verdict st)),
      ("checked", Json.num st.checked), ("violations", Json.num st.violations),
      ("smallest_margin", margin st)] ++ files.toList)
  let mut clauses : Array Json := #[]
  for st in r.stats do clauses := clauses.push (← clauseJson st (m.contract.clauseHash st.clause))
  let mut monitored : Array Json := #[]
  let ihash (st : ClauseStat) : String :=
    innerHash m.contract ((instContract r st.path).clauseHash st.clause)
  let ahash (a : AssumeStat) : String :=
    innerHash m.contract (assumptionHash (instContract r a.path))
  for st in r.inner do monitored := monitored.push (← clauseJson st (ihash st))
  let mut assumptions : Array Json := #[]
  for a in r.assumes do
    let mut files : List (String × Json) := []
    if let some (cr, k) := a.firstFail then
      files := [("first_discharge_failure", Json.mkObj (← save cr k))]
    assumptions := assumptions.push (Json.mkObj ([
      ("path", Json.str a.path), ("contract_hash", Json.str
        (ahash a)),
      ("verdict", Json.str (discharge a)),
      ("steps", Json.num a.steps), ("assumption_held", Json.num a.held),
      ("assumption_held_so_far", Json.num a.heldSoFar),
      ("cases_with_discharge_failure", Json.num a.failedCases),
      ("failing_clauses", Json.mkObj (a.clauseFails.toList.filterMap fun (nm, st, fc) =>
        if st == 0 then none else some (nm, Json.mkObj [("steps", Json.num st),
          ("first_failures", Json.num fc)])))] ++ files))
  let build : List (String × Json) := match r.manifest with
    | some man => [("compiler", Json.str man.compiler), ("flags", Json.str man.flags)]
    | none => [("children", Json.arr ((r.insts.zip r.instHashes).toList.drop 1 |>.toArray.map
        fun (i, h) => Json.mkObj [("path", Json.str i.path), ("node", Json.str i.node.name),
          ("kind", Json.str i.node.kind), ("code_hash", Json.str h)]))]
  let sysOnly : List (String × Json) := match n with
    | .system _ => [("monitored", Json.arr monitored), ("assumptions", Json.arr assumptions),
      ("formal_link", Json.str "not built: no Lean proof yet that the children's contracts, \
        as wired, imply this system's contract")]
    | .module _ => []
  let result := Json.mkObj ([
    (n.kind, Json.str m.name), ("kind", Json.str "tested"), ("id", Json.str id),
    ("tool", Json.str toolVersion), ("command", Json.str command),
    ("code_hash", Json.str r.codeHash)] ++ build ++ [
    ("seed", Json.num r.cfg.seed), ("cases", Json.num r.cfg.cases),
    ("steps_per_case", Json.num r.cfg.steps),
    ("steps_run", Json.num r.stepsRun), ("cases_skipped", Json.num r.casesSkipped),
    ("seconds", jsonFloat r.seconds),
    ("assume", Json.arr (m.contract.assume.toArray.map fun a => Json.str a.text)),
    ("outputs_seen", Json.mkObj ((m.output.zip r.seen).toList.map fun (f, o) =>
      (f.name, if f.type == .bool then Json.mkObj [("true_steps", Json.num o.trues)]
        else Json.mkObj [("min_finite", (o.lo.map jsonFloat).getD Json.null),
                         ("max_finite", (o.hi.map jsonFloat).getD Json.null),
                         ("non_finite_steps", Json.num o.nonFinite)]))),
    ("guarantee", Json.arr clauses)] ++ sysOnly ++ regimeFields ++
    (if r.coverage.isEmpty then [] else [("coverage", Json.mkObj (r.coverage.toList.map
      fun (cl, k) => (cl.name, Json.mkObj [("text", Json.str cl.expr.print),
        ("true_steps", Json.num k)])))]))
  let resultFile := dir / s!"{id}.json"
  IO.FS.writeFile resultFile (result.pretty ++ "\n")
  let resultHash ← Sha256.hashFile resultFile
  let common : List (String × Json) := [
    ("tool", Json.str toolVersion), ("command", Json.str command),
    ("seed", Json.num r.cfg.seed), ("cases", Json.num r.cfg.cases),
    ("steps_per_case", Json.num r.cfg.steps)] ++ regimeRef
  let tail : List (String × Json) := [
    ("code_hash", Json.str r.codeHash),
    ("result_file", Json.str resultFile.toString), ("result_hash", Json.str resultHash),
    ("date", Json.str stamp)]
  let record (kind : String) (st : ClauseStat) (hash : String) : Json :=
    Json.mkObj ((if st.path.isEmpty then [] else [("path", Json.str st.path)]) ++ [
      ("clause", Json.str st.clause.name), ("kind", Json.str kind),
      ("verdict", Json.str (verdict st))] ++ common ++ [
      ("checked", Json.num st.checked), ("violations", Json.num st.violations),
      ("smallest_margin", margin st),
      ("contract_hash", Json.str hash)] ++ tail)
  let mut records ← readLedger n
  for st in r.stats do
    records := records.push (record "tested" st (m.contract.clauseHash st.clause))
  for st in r.inner do records := records.push (record "monitored" st (ihash st))
  for a in r.assumes do
    records := records.push (Json.mkObj ([
      ("path", Json.str a.path), ("clause", Json.str assumptionClause),
      ("kind", Json.str "monitored"),
      ("verdict", Json.str (discharge a))] ++ common ++ [
      ("checked", Json.num a.steps), ("violations", Json.num (a.steps - a.held)),
      ("cases_with_discharge_failure", Json.num a.failedCases),
      ("contract_hash", Json.str (ahash a))] ++ tail))
  IO.FS.writeFile (ledgerPath n)
    ((Json.mkObj [(n.kind, Json.str m.name), ("records", Json.arr records)]).pretty ++ "\n")
  return resultFile

/-! ### Served sessions -/

/-- What `harness serve` monitored in one session, per instance (root first): the steps at which
the instance's assumption had held so far and each guarantee clause was checked, its
violations, and the first discharge failure (init, step). -/
structure ServedStats where
  inits : Nat
  steps : Nat
  /-- per instance: steps at which its assumption held -/
  held : Array Nat
  /-- per instance: the first step at which its assumption failed -/
  firstFail : Array (Option (Nat × Nat))
  /-- per instance, per guarantee clause: checks and violations -/
  checked : Array (Array Nat)
  violations : Array (Array Nat)

/-- Write a served session's evidence: the session log copied to HOME/evidence/served/ID.log, a
result file HOME/evidence/served/ID.json, and ledger records of the `monitored` kind for the
node's own clauses and for every inner (path, clause) and inner assumption, as a system campaign
writes them. The served inputs are not drawn from the assumption, so the node's own clauses are
monitored, not tested. Verdicts: `failed` for a clause violated; `undischarged` for every clause
of the node, and every clause of an instance at or below a path whose assumption failed, when
the session had a discharge failure (their checks ran only while the assumptions held, and the
composite's guarantee rests on all of them); `failed` for an inner assumption that failed;
`empty` for no check; else `passed`. Returns the result file. -/
def recordServeSession (n : CNode) (codeHash command : String) (log : System.FilePath)
    (st : ServedStats) : IO System.FilePath := do
  let m := n.view.m
  let insts := n.instances n.name
  let stamp ← utcStamp
  let id := s!"{stamp}-served"
  let dir := evidenceDir n / "served"
  IO.FS.createDirAll dir
  let logCopy := dir / s!"{id}.log"
  if ← log.pathExists then IO.FS.writeFile logCopy (← IO.FS.readFile log)
  let failedPaths := (insts.zip st.firstFail).filterMap fun (i, f) => f.map fun _ => i.path
  let anyDischarge := !failedPaths.isEmpty
  let under (p : String) : Bool := failedPaths.any fun q => p == q || p.startsWith (q ++ "/")
  let verdict (j : Nat) (gi : Nat) : String :=
    let path := insts[j]!.path
    if st.violations[j]![gi]! != 0 then "failed"
    else if (j == 0 && anyDischarge) || (j != 0 && under path) then "undischarged"
    else if st.checked[j]![gi]! == 0 then "empty" else "passed"
  let hashOf (j : Nat) (g : Clause) : String :=
    if j == 0 then m.contract.clauseHash g
    else innerHash m.contract (insts[j]!.node.view.m.contract.clauseHash g)
  let clauseJ (j : Nat) : Array Json :=
    insts[j]!.node.view.guarantee.zipIdx.map fun (g, gi) => Json.mkObj [
      ("clause", Json.str g.name), ("verdict", Json.str (verdict j gi)),
      ("checked", Json.num st.checked[j]![gi]!), ("violations", Json.num st.violations[j]![gi]!)]
  let instJ : Array Json := insts.zipIdx.map fun (i, j) => Json.mkObj ([
    ("path", Json.str i.path), ("node", Json.str i.node.name),
    ("assumption_held", Json.num st.held[j]!),
    ("discharge_failure", match st.firstFail[j]! with
      | some (c, k) => Json.mkObj [("init", Json.num c), ("step", Json.num k)]
      | none => Json.null),
    ("guarantee", Json.arr (clauseJ j))])
  let result := Json.mkObj [
    (n.kind, Json.str m.name), ("kind", Json.str "served"), ("id", Json.str id),
    ("tool", Json.str toolVersion), ("command", Json.str command),
    ("code_hash", Json.str codeHash), ("inits", Json.num st.inits),
    ("steps_run", Json.num st.steps), ("session_log", Json.str logCopy.toString),
    ("discharge_failures", Json.arr (failedPaths.map Json.str)),
    ("instances", Json.arr instJ)]
  let resultFile := dir / s!"{id}.json"
  IO.FS.writeFile resultFile (result.pretty ++ "\n")
  let resultHash ← Sha256.hashFile resultFile
  let tail : List (String × Json) := [
    ("tool", Json.str toolVersion), ("command", Json.str command),
    ("steps_run", Json.num st.steps), ("session_log", Json.str logCopy.toString),
    ("code_hash", Json.str codeHash),
    ("result_file", Json.str resultFile.toString), ("result_hash", Json.str resultHash),
    ("date", Json.str stamp)]
  let mut records ← readLedger n
  for (i, j) in insts.zipIdx do
    let pathF : List (String × Json) := if j == 0 then [] else [("path", Json.str i.path)]
    for (g, gi) in i.node.view.guarantee.zipIdx do
      records := records.push (Json.mkObj (pathF ++ [
        ("clause", Json.str g.name), ("kind", Json.str "monitored"),
        ("verdict", Json.str (verdict j gi)),
        ("checked", Json.num st.checked[j]![gi]!), ("violations", Json.num st.violations[j]![gi]!),
        ("contract_hash", Json.str (hashOf j g))] ++ tail))
    if j != 0 then
      let failed := st.firstFail[j]!.isSome
      records := records.push (Json.mkObj (pathF ++ [
        ("clause", Json.str assumptionClause), ("kind", Json.str "monitored"),
        ("verdict", Json.str (if failed then "failed" else if st.steps == 0 then "empty"
          else "passed")),
        ("checked", Json.num st.steps), ("violations", Json.num (st.steps - st.held[j]!)),
        ("cases_with_discharge_failure", Json.num (if failed then 1 else 0)),
        ("contract_hash", Json.str (innerHash m.contract
          (assumptionHash i.node.view.m.contract)))] ++ tail))
  IO.FS.writeFile (ledgerPath n)
    ((Json.mkObj [(n.kind, Json.str m.name), ("records", Json.arr records)]).pretty ++ "\n")
  return resultFile

/-! ### Status -/

/-- Recompute the code hash from the build's record of the files the compiler read
(build/modules/NAME/code_inputs.txt): `some (hash, changed files)`, or `none` without a build.
The labels' roots ($ARDUPILOT_ROOT, $HARNESS, any other) are in build/modules/NAME/roots.env. -/
def recomputeCodeHash (m : Module) : IO (Option (String × Array String)) := do
  let dir : System.FilePath := "build" / "modules" / m.name
  let inputs := dir / "code_inputs.txt"
  let roots := dir / "roots.env"
  unless (← inputs.pathExists) && (← roots.pathExists) do return none
  -- every line NAME=PATH of roots.env: a label $NAME/rest stands for PATH/rest
  let mut rootList : Array (String × String) := #[]
  for l in (← IO.FS.readFile roots).splitOn "\n" do
    match l.splitOn "=" with
    | k :: v :: rest => rootList := rootList.push (k, "=".intercalate (v :: rest))
    | _ => pure ()
  let mut out := ""
  let mut changed : Array String := #[]
  for l in (← IO.FS.readFile inputs).splitOn "\n" do
    if l.isEmpty then continue
    match l.splitOn "  " with
    | [h, label] =>
      let path := match rootList.find? fun (k, _) => label.startsWith s!"${k}/" with
        | some (k, r) => r ++ "/" ++ (label.drop (k.length + 2)).toString
        | none => label
      let now ← if ← System.FilePath.pathExists path then Sha256.hashFile path else pure "missing"
      if now != h then changed := changed.push label
      out := out ++ s!"{now}  {label}\n"
    | _ => out := out ++ l ++ "\n"
  return some (Sha256.hashString out, changed)

inductive ClauseStatus where
  /-- passing records that match all three hashes -/
  | backed (recs : Array Json)
  /-- a matching record with a violation: the clause is refuted for this code and contract -/
  | failed (recs : Array Json)
  /-- matching records, all with 0 checks (every case skipped, or the clause never reached):
  no evidence -/
  | empty (recs : Array Json)
  /-- matching records from a served session in which an instance's assumption failed (a
  discharge failure): the clause's checks in that session are not backed evidence -/
  | undischarged (recs : Array Json)
  | stale (reasons : List String)
  | unbacked

/-- The current contract hash of each inner instance's assumption record (`innerHash` of its
assumption under the node's), by path: what a served session's discharge failure is compared
with. -/
def assumptionHashesNow (n : CNode) : String → Option String := fun p =>
  ((n.instances n.name).find? (·.path == p)).map fun i =>
    innerHash n.view.m.contract (assumptionHash i.node.view.m.contract)

/-- A clause's status from its ledger records: the records that match the current code hash,
contract hash and result-file hash count; a failing one among them refutes the clause. `path`
selects the records of an inner instance's clause (`none`: the node's own clauses). -/
def clauseStatus (records : Array Json) (codeHash contractHash : String) (name : String)
    (path : Option String := none) (assumeNow : String → Option String := fun _ => none) :
    IO ClauseStatus := do
  let mine := records.filter fun r => (r.getObjValAs? String "clause").toOption == some name &&
    (r.getObjValAs? String "path").toOption == path
  if mine.isEmpty then return .unbacked
  let get (r : Json) (k : String) := (r.getObjValAs? String k).toOption.getD ""
  let mut matching : Array Json := #[]
  let mut newestReasons : List String := []
  for r in mine.reverse do
    let mut reasons : List String := []
    if get r "code_hash" != codeHash then
      reasons := reasons ++
        [s!"code hash {(get r "code_hash").take 12}… in the ledger, {codeHash.take 12}… now"]
    if get r "contract_hash" != contractHash then
      reasons := reasons ++ [s!"contract hash {(get r "contract_hash").take 12}… in the ledger, \
        {contractHash.take 12}… now"]
    let rf : System.FilePath := get r "result_file"
    let rh ← if ← rf.pathExists then Sha256.hashFile rf else pure "missing"
    if rh != get r "result_hash" then
      reasons := reasons ++
        [s!"result file {rf} {if rh == "missing" then "missing" else "changed"}"]
    -- an `undischarged` record of a served session whose discharge failure happened under an
    -- assumption of the failing instance that has changed since (`assumeNow`: the current hash of
    -- an instance's assumption record) says nothing about the clause now
    if get r "verdict" == "undischarged" then
      let fails := records.filter fun q => get q "result_file" == get r "result_file" &&
        get q "clause" == assumptionClause && get q "verdict" == "failed"
      for q in fails do
        let p := get q "path"
        if let some h := assumeNow p then
          if h != get q "contract_hash" then
            reasons := reasons ++ [s!"its discharge failure ({p}) was under an earlier \
              assumption of {p}"]
    if reasons.isEmpty then matching := matching.push r
    else if newestReasons.isEmpty then newestReasons := reasons
  if matching.isEmpty then return .stale newestReasons
  let failing := matching.filter fun r => get r "verdict" == "failed"
  if !failing.isEmpty then return .failed failing
  let undis := matching.filter fun r => get r "verdict" == "undischarged"
  if !undis.isEmpty then return .undischarged undis
  let checks (r : Json) : Nat := (r.getObjValAs? Nat "checked").toOption.getD 0
  let backing := matching.filter fun r => get r "verdict" == "passed" && checks r > 0
  return if backing.isEmpty then .empty matching else .backed backing

/-- One word for a status. -/
def ClauseStatus.tag : ClauseStatus → String
  | .backed _ => "backed" | .failed _ => "failed" | .empty _ => "empty" | .stale _ => "stale"
  | .undischarged _ => "undischarged" | .unbacked => "unbacked"

/-- The status of each of a node's own guarantee clauses, from its own ledger, for the given
code hash. -/
def ownStatuses (n : CNode) (codeHash : String) : IO (Array (Clause × ClauseStatus)) := do
  let records ← readLedger n
  let assumeNow := assumptionHashesNow n
  n.view.guarantee.mapM fun g => do
    return (g, ← clauseStatus records codeHash (n.view.m.contract.clauseHash g) g.name none
      assumeNow)

/-- A one-line count of statuses: `3 clauses: 2 backed, 1 stale`. -/
def statusSummary (sts : Array ClauseStatus) : String :=
  let tags := ["backed", "failed", "undischarged", "empty", "stale", "unbacked"]
  let parts := tags.filterMap fun t =>
    let k := (sts.filter (·.tag == t)).size
    if k == 0 then none else some s!"{k} {t}"
  s!"{sts.size} clauses: {", ".intercalate parts}"

end Harness
