import Plant

/-!
The audit of the plant library (`plant/PLAN.md`, rules 3 and 4, "Measure of progress"). Not a proof: a report on
the theorems of the modules `Plant.*` outside `Plant.Model.*` and `Plant.Lib.*`.

    cd plant && LEAN_NUM_THREADS=1 lake env lean tests/PlantAudit.lean     (after `lake build`)

1. Rule 3: every such theorem has in its statement a constant of `Plant.Model.*` (a definition of the model, not the
   bare carrier types `X`, `Vec3`, `Quat`, `State` or the constants Lean generates for structures) or one of the
   flow and step constants (`flowConsts` below). A theorem that names neither but names a derived definition (a
   definition outside `Plant.Model` whose value reaches a model, flow or step constant, such as `alphaMax`, `wB`,
   `box`, `energy`) is counted separately; one that names none of these is listed as a violation.
2. Rule 4: the axioms each theorem depends on; any axiom other than `propext`, `Classical.choice`, `Quot.sound` is
   listed, and the set of axioms used is printed.
3. Coverage: per model or flow/step constant, the number of theorems of each kind of `PLAN.md` ("Kinds of plant
   property") whose conclusion names it (or, if the conclusion names none, whose hypotheses do). The kind is the one
   `kindOverride` gives, else the one `kindOf` reads off the name. Printed as Markdown table rows for `LEDGER.md`.
   With `verbose := true` every theorem is printed with its module and kind.
-/

open Lean

namespace PlantAudit

def verbose : Bool := false

/-- The carrier types of the model and what Lean generates for them: not model constants for rule 3. -/
def carrierTypes : List Name := [`Plant.X, `Plant.Vec3, `Plant.Quat, `Plant.State, `Plant.PState, `Plant.SampleR]

/-- The flow and step constants (rule 3), defined outside `Plant.Model`. -/
def flowConsts : List Name :=
  [`Plant.vfT, `Plant.flowT, `Plant.traj, `Plant.step, `Plant.eulerStep, `Plant.sfX, `Plant.sampledFlow,
   `Plant.nextR, `Plant.sampleR, `Plant.tickSpecForce, `Plant.IsRun, `Plant.stepN, `Plant.trajN]

def isAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" || s.startsWith "eq_"
  | _ => true

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.moduleNames[idx.toNat]!

/-- A constant Lean generates for a structure: a field projection, the constructor, the recursors and the like, and
the lemmas about the constructor (`mk.inj`, `mk.injEq`, `mk.sizeOf_spec`). -/
def isStructural (env : Environment) (n : Name) : Bool :=
  (env.getProjectionFnInfo? n).isSome || (match env.find? n with | some (.ctorInfo _) => true | _ => false) ||
  match n with
  | .str p s =>
    (isStructure env p && ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ibelow",
      "binductionOn", "ext", "ext_iff", "ctorIdx", "eta", "mk"].contains s) ||
    (match env.find? p with | some (.ctorInfo _) => true | _ => false)
  | _ => false

def isModelConst (env : Environment) (n : Name) : Bool :=
  if flowConsts.contains n then true
  else if carrierTypes.contains n || isStructural env n then false
  else match moduleOf env n with
    | some m => (`Plant.Model).isPrefixOf m && !isAux n &&
        (match env.find? n with | some (.defnInfo _) => true | _ => false)
    | none => false

/-- The definitions of `Plant.*` outside `Plant.Model` whose value names, directly or through other such
definitions, a model, flow or step constant (`alphaMax`, `wB`, `box`, …): the derived quantities. -/
def derivedConsts (env : Environment) : NameSet := Id.run do
  let mut defs : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .defnInfo d := ci then
      if (`Plant).isPrefixOf n && !isAux n && !isModelConst env n then
        if let some m := moduleOf env n then
          if (`Plant).isPrefixOf m then defs := defs.push (n, d.value.getUsedConstants)
  let mut out : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for (n, used) in defs do
      if !out.contains n && used.any (fun c => isModelConst env c || out.contains c) then
        out := out.insert n; changed := true
  return out

partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

def kinds : List String := ["Algebra", "Range", "Regularity", "Invariant", "Existence", "Sensitivity", "Exact", "Step"]

/-- Kinds fixed by hand where the name does not tell. -/
def kindOverride : List (Name × String) :=
  [(`Plant.backwardDiff_sub_specForce, "Step"), (`Plant.downAxis_quatOf, "Algebra"), (`Plant.normSq_quatOf, "Algebra"),
   (`Plant.vf_pI, "Algebra"), (`Plant.vf_vI, "Algebra"), (`Plant.dn_eq_downAxis, "Algebra"),
   (`Plant.vf_v_eq_sf, "Algebra"), (`Plant.run_qnormSq, "Invariant"), (`Plant.step_eq_flowT, "Existence"),
   (`Plant.vfT_eq_vf, "Algebra"), (`Plant.scaledSol_traj, "Existence"), (`Plant.scaledSol_flowT, "Existence"),
   (`Plant.scaledSol_of_hasDerivAt, "Existence"), (`Plant.traj_pv_sharp, "Step"), (`Plant.step_pv_sharp, "Step"),
   (`Plant.traj_pv_first, "Step"), (`Plant.traj_att_taylor, "Step"), (`Plant.vf_traj_sub_v, "Step"),
   (`Plant.q_dot_scaled, "Algebra"), (`Plant.energy_dot_scaled, "Algebra"), (`Plant.v_scaledSol, "Step"),
   (`Plant.p_scaledSol, "Step"), (`Plant.norm_le_box_of_scaledSol, "Step"), (`Plant.energy_scaledSol, "Invariant"),
   (`Plant.two_dot_torque_le, "Range"), (`Plant.alphaMax_eq, "Algebra"), (`Plant.thrust_eq, "Algebra"),
   (`Plant.accel_hover, "Exact"), (`Plant.traj_zero, "Existence")]

def kindOf (n : Name) : String :=
  let s := match n with | .str _ s => s | _ => ""
  let has (p : String) := (s.splitOn p).length > 1
  if has "lipschitz" || has "continuous" || has "Lipschitz" || has "hasDerivAt" || has "_sub_v" || has "_sub_p" ||
      has "_sub_q" || has "_sub_w" || has "differentiable" then "Regularity"
  else if has "hover" || has "exact" || has "closed" || has "level" || has "yawSpin" || has "_eq_" || has "sharp" ||
      has "taylor" || has "first" || has "Free" then "Exact"
  else if has "qnormSq_" && (has "step" || has "traj" || has "scaled" || has "solution" || has "run" || has "const") ||
      has "energy_scaled" || has "energy_dot" || has "q_dot" || has "Invariant" || has "preserves" then "Invariant"
  else if s.endsWith "_spec" || has "unique" || has "flowT" || has "traj_zero" || has "isIntegralCurve" || has "run_" ||
      has "sampledFlow" || has "stepN" || has "trajN" || has "semigroup" || has "iterate" then "Existence"
  else if has "sens" || has "dist_step" || has "input" then "Sensitivity"
  else if has "equivariant" || has "translate" || has "rotate" || has "linear" || has "inverse" || has "mix" ||
      has "_eq" || has "comm" || has "toX" || has "ofX" || has "mul_" || has "image" then "Algebra"
  else if has "step" || has "traj" || has "Euler" || has "euler" || has "remainder" || has "move" || has "gronwall" ||
      has "backwardDiff" || has "Bd_traj" then "Step"
  else "Range"

/-- The kind of every theorem of a module, unless `kindOverride` says otherwise (the modules written for this
library, where the module is the kind). -/
def moduleKind : List (Name × String) :=
  [(`Plant.Field.Actuators, "Algebra"), (`Plant.Flow.Sensitivity, "Sensitivity"), (`Plant.Step.Exact, "Exact"),
   (`Plant.Step.Symmetry, "Algebra"), (`Plant.Step.Period, "Step"), (`Plant.Step.Multi, "Existence")]

def newOverride : List (Name × String) :=
  [(`Plant.clip01_mono, "Range"), (`Plant.force_mono, "Range"), (`Plant.thrust_mono, "Range"),
   (`Plant.accel_mono, "Range"), (`Plant.range_wrench, "Range"), (`Plant.Kin_nonneg, "Range"),
   (`Plant.abs_clip01_sub_le, "Regularity"), (`Plant.abs_clip01_sub_le_norm, "Sensitivity"),
   (`Plant.abs_accel_sub_le, "Sensitivity"), (`Plant.abs_torqueX_div_sub_le, "Sensitivity"),
   (`Plant.abs_torqueY_div_sub_le, "Sensitivity"), (`Plant.abs_torqueZ_div_sub_le, "Sensitivity"),
   (`Plant.norm_vf_sub_input_le, "Sensitivity"), (`Plant.accel_const_eq_grav_iff, "Exact"),
   (`Plant.continuous_step, "Regularity"), (`Plant.continuous_step_uncurry, "Regularity"),
   (`Plant.step_lipschitzOnWith, "Regularity"), (`Plant.torqueFreeXY_const, "Algebra"),
   (`Plant.accel_eq_zero_of_nonpos, "Algebra"), (`Plant.spinState_step, "Invariant"),
   (`Plant.qnormSq_stepN, "Invariant"), (`Plant.stepN_hover, "Exact"), (`Plant.stepN_level_state, "Invariant"),
   (`Plant.stepN_level_vz, "Exact"), (`Plant.stepN_level_pz, "Exact"), (`Plant.stepN_add_posVec, "Algebra"),
   (`Plant.stepN_yawRot, "Algebra"), (`Plant.qnormSq_yawRot, "Invariant")]

def kind (n mod : Name) : String :=
  match kindOverride.lookup n with
  | some k => k
  | none => match newOverride.lookup n with
    | some k => k
    | none => (moduleKind.lookup mod).getD (kindOf n)

def okAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def audit : CoreM Unit := do
  let env ← getEnv
  let mut thms : Array (Name × Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if (`Plant).isPrefixOf n && !isAux n && !isStructural env n then
        if let some mod := moduleOf env n then
          if (`Plant).isPrefixOf mod && !(`Plant.Model).isPrefixOf mod && !(`Plant.Lib).isPrefixOf mod then
            thms := thms.push (n, mod)
  thms := thms.qsort (·.1.toString < ·.1.toString)
  let derived := derivedConsts env
  let mut viol3 : Array Name := #[]
  let mut viaDerived : Array Name := #[]
  let mut viol4 : Array (Name × Array Name) := #[]
  let mut axiomsUsed : NameSet := {}
  let mut cov : Std.HashMap String (Std.HashMap String Nat) := {}
  let mut totals : Std.HashMap String Nat := {}
  for (n, mod) in thms do
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants.filter (isModelConst env)
    if used.isEmpty then
      if ci.type.getUsedConstants.any derived.contains then viaDerived := viaDerived.push n
      else viol3 := viol3.push n
    let axs ← Lean.collectAxioms n
    for a in axs do axiomsUsed := axiomsUsed.insert a
    let bad := axs.filter (fun a => !okAxioms.contains a)
    if !bad.isEmpty then viol4 := viol4.push (n, bad)
    let k := kind n mod
    totals := totals.insert k (totals.getD k 0 + 1)
    if verbose then IO.println s!"{mod} {n} {k}"
    let cs := (conclusion ci.type).getUsedConstants.filter (isModelConst env)
    let cs := if cs.isEmpty then used else cs
    let mut seen : List Name := []
    for c in cs do
      if seen.contains c then continue
      seen := c :: seen
      let f := (c.replacePrefix `Plant .anonymous).toString
      let row := cov.getD f {}
      cov := cov.insert f (row.insert k (row.getD k 0 + 1))
  IO.println s!"theorems outside Plant.Model and Plant.Lib: {thms.size}"
  IO.println s!"rule 3 (statement names a model, flow or step constant): {thms.size - viol3.size - viaDerived.size} of {thms.size} directly, {viaDerived.size} through a derived definition, {viol3.size} violations"
  IO.println s!"  through a derived definition: {viaDerived.toList}"
  IO.println s!"  violations: {viol3.toList}"
  IO.println s!"rule 4 (axioms): violations: {viol4.toList}"
  IO.println s!"axioms used: {axiomsUsed.toList}"
  IO.println s!"theorems by kind: {kinds.map fun k => (k, totals.getD k 0)}"
  IO.println ""
  IO.println s!"| constant | {" | ".intercalate kinds} |"
  IO.println s!"|---|{"".intercalate (kinds.map fun _ => "---|")}"
  let rows := cov.toList.toArray.qsort (·.1 < ·.1)
  for (f, row) in rows do
    let cells := kinds.map fun k => match row.get? k with | some c => toString c | none => ""
    IO.println s!"| `{f}` | {" | ".intercalate cells} |"

#eval audit

end PlantAudit
