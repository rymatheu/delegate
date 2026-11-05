import Lean

/-!
# Frame reasoning on the translated code

The translated functions are `Id.run do` blocks: local mutable state, `if`/`match`, `for` loops,
join points (`have __do_jp := fun … => …`), and calls to other translated functions. A *frame
property* of such a function is a predicate `P` on a state type `σ` that every value of type `σ`
the function builds satisfies: a field that the function never writes (`(f s).fld = s.fld`), or a
bound that every write respects (`ActOK s._actuator`).

`frame_gen σ P using tac` proves `P (f args)` by one pass over the unfolded body of `f`:

* `let x := v; b`: proves `P v` (if `v` has a component of type `σ`), then `b` with `x` and
  `P x` as *variables*: the proof is `(fun x hx => pb) v pv`, so nothing is ever substituted and the
  proof stays linear in the size of the body (no `zeta`-blowup, no case split on conditions);
* `if`/`dite`/`cond`/`match`: every branch (the conditions are never looked at);
* `bind`/`pure`/`Id.run` in `Id`, `forIn` over a range, a list or an array (with `P` as the loop
  invariant on the `σ` components of the loop state), `ForInStep.yield`/`done`, pairs (`Prod`,
  `MProd`) and their projections, calls of join points;
* every other term (a record literal, a call of another function) is a *leaf*: its goal
  `P leaf` is given to `tac`, with the hypotheses `P x` of all the `σ`-variables in scope.

The statement transported along a value of type `τ` is `P` on its `σ` components: `P x` for
`τ = σ`, the conjunction over the components of a product, `P` of the value of a `ForInStep`, and
`∀ args, (P on the σ-args) → (P on the result)` for a join point. Values without a `σ` component
carry no statement.

(`mvcgen` of `Std.Do` does the same job in general, but on these bodies its default mode splits
every join point per path, exponentially many conditions, and its `+jp` mode fails on `else if`
chains in v4.36.0-rc2.)
-/

open Lean Elab Tactic Meta

namespace Contracts.Track.Frame

universe u v w

theorem frame_ite {α : Sort u} {P : α → Prop} {c : Prop} [h : Decidable c] {t e : α}
    (ht : P t) (he : P e) : P (if c then t else e) := by
  cases h <;> assumption

theorem frame_dite {α : Sort u} {P : α → Prop} {c : Prop} [h : Decidable c] {t : c → α}
    {e : ¬c → α} (ht : ∀ hc, P (t hc)) (he : ∀ hc, P (e hc)) : P (dite c t e) := by
  cases h with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

theorem frame_cond {α : Type u} {P : α → Prop} {b : Bool} {t e : α} (ht : P t) (he : P e) :
    P (cond b t e) := by
  cases b <;> assumption

theorem frame_forIn_list {α : Type u} {β : Type v} {P : β → Prop} (xs : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (h0 : P init) (hf : ∀ a b, P b → P (f a b).value) :
    P (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact h0
  | cons a as ih =>
    rw [List.forIn_cons]
    have h1 := hf a init h0
    revert h1
    show P (Id.run (f a init)).value →
      P ((match Id.run (f a init) with
        | ForInStep.done b => (pure b : Id β)
        | ForInStep.yield b => forIn as b f) : Id β)
    cases Id.run (f a init) with
    | done b => exact fun h => h
    | yield b => exact fun h => ih b h

theorem frame_forIn_range {β : Type v} {P : β → Prop} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → Id (ForInStep β)) (h0 : P init) (hf : ∀ a b, P b → P (f a b).value) :
    P (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact frame_forIn_list _ init f h0 hf

theorem frame_forIn_array {α : Type u} {β : Type v} {P : β → Prop} (xs : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) (h0 : P init) (hf : ∀ a b, P b → P (f a b).value) :
    P (forIn xs init f) := by
  rw [← Array.forIn_toList]
  exact frame_forIn_list _ init f h0 hf

/-- The context of the generator: the state type, the predicate, the leaf tactic, and the proofs of
the statements of the variables in scope. -/
structure Ctx where
  /-- The tracked state types and their predicates. -/
  σP : Array (Expr × Expr)
  leaf : Syntax
  hyps : Array (Expr × Expr) := #[]

abbrev M := ReaderT Ctx TacticM

/-- The statement carried by a value `x : τ`, or `none` when `τ` has no `σ` component. -/
partial def mkStmt (τ x : Expr) : M (Option Expr) := do
  let c ← read
  let τ ← whnfD τ
  if τ.isForall then
    return ← forallTelescopeReducing τ fun args R => do
      let r ← mkStmt R (mkAppN x args)
      let some r := r | return none
      let mut body := r
      for a in args.reverse do
        if let some sa ← mkStmt (← inferType a) a then
          body := mkForall `h .default sa body
        body ← mkForallFVars #[a] body
      return some body
  for (σ, P) in c.σP do
    if (← withNewMCtxDepth (isDefEq τ σ)) then return some (P.beta #[x])
  if τ.isAppOfArity ``Prod 2 || τ.isAppOfArity ``MProd 2 then
    let isP := τ.isAppOfArity ``Prod 2
    let fst ← mkAppM (if isP then ``Prod.fst else ``MProd.fst) #[x]
    let snd ← mkAppM (if isP then ``Prod.snd else ``MProd.snd) #[x]
    let a ← mkStmt (τ.getArg! 0) fst
    let b ← mkStmt (τ.getArg! 1) snd
    return match a, b with
      | none, none => none
      | some a, none => some a
      | none, some b => some b
      | some a, some b => some (mkAnd a b)
  if τ.isAppOfArity ``ForInStep 1 then
    return ← mkStmt (τ.getArg! 0) (← mkAppM ``ForInStep.value #[x])
  return none

/-- Run the leaf tactic on the goal `st`. -/
def proveLeaf (st : Expr) : M Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar st
  let rest ← Tactic.run g.mvarId! (evalTactic (← read).leaf)
  unless rest.isEmpty do
    let msgs ← rest.mapM fun g => do return m!"{← g.getType}"
    throwError "frame_gen: the leaf tactic left goals:{indentD (MessageData.joinSep msgs Format.line)}"
  instantiateMVars g

/-- Add the variable `x` (and, when its type carries a statement, a hypothesis for it) to the
context, and run `k` with the variables to abstract. -/
def withTracked {α} (n : Name) (t : Expr) (k : Expr → Array Expr → M α) : M α :=
  withLocalDeclD n t fun x => do
    match ← mkStmt t x with
    | none => k x #[x]
    | some sx =>
      withLocalDeclD (n.appendAfter "_frame") sx fun hx =>
        withReader (fun c => { c with hyps := c.hyps.push (x, hx) }) (k x #[x, hx])

/-- `fun y => P_α y`, the statement of type `α` as a predicate. -/
def stmtLam (α : Expr) : M Expr :=
  withLocalDeclD `y α fun y => do
    let s ← mkStmt α y
    mkLambdaFVars #[y] (s.getD (mkConst ``True))

/-- Whether values of type `α` carry a statement. -/
def carries (α : Expr) : M Bool :=
  withLocalDeclD `y α fun y => do return (← mkStmt α y).isSome

mutual

/-- A proof of the statement of `e`, or `none` when `e` carries none. -/
partial def prove (e : Expr) : M (Option Expr) := do
  let e := e.consumeMData
  let τ ← inferType e
  let some st ← mkStmt τ e | return none
  some <$> proveSt e st

/-- A proof of `st`, the statement of `e`. -/
partial def proveSt (e : Expr) (st : Expr) : M Expr := do
  let e := e.consumeMData.headBeta
  match e with
  | .letE n t v b _ =>
    let pv? ← prove v
    withTracked n t fun x xs => do
      let b' := b.instantiate1 x
      let some pb ← prove b' | throwError "frame_gen: let body carries no statement"
      let f ← mkLambdaFVars xs pb
      match pv? with
      | some pv => return mkApp2 f v pv
      | none =>
        if xs.size == 2 then throwError "frame_gen: let value carries no statement"
        return mkApp f v
  | .fvar fv =>
    if let some (_, h) := (← read).hyps.find? (fun (x, _) => x == .fvar fv) then
      return h
    proveLeaf st
  | .lam .. => proveUnder e
  | .proj ``Prod 0 x => proveProj x true st
  | .proj ``Prod 1 x => proveProj x false st
  | .proj ``MProd 0 x => proveProj x true st
  | .proj ``MProd 1 x => proveProj x false st
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .fvar fv := fn then
      if let some (_, h) := (← read).hyps.find? (fun (x, _) => x == .fvar fv) then
        -- a join point: apply its hypothesis to the arguments and their proofs
        let mut prf := h
        for a in args do
          prf := mkApp prf a
          if let some pa ← prove a then prf := mkApp prf pa
        return prf
    let .const name _ := fn | proveLeaf st
    match name, args.size with
    | ``ite, 5 =>
      let α := args[0]!
      let P' ← stmtLam α
      let pt ← proveSt args[3]! (P'.beta #[args[3]!])
      let pe ← proveSt args[4]! (P'.beta #[args[4]!])
      mkAppOptM ``frame_ite #[α, P', args[1]!, args[2]!, args[3]!, args[4]!, pt, pe]
    | ``dite, 5 =>
      let α := args[0]!
      let P' ← stmtLam α
      let pt ← proveUnder args[3]!
      let pe ← proveUnder args[4]!
      mkAppOptM ``frame_dite #[α, P', args[1]!, args[2]!, args[3]!, args[4]!, pt, pe]
    | ``cond, 4 =>
      let α := args[0]!
      let P' ← stmtLam α
      let pt ← proveSt args[2]! (P'.beta #[args[2]!])
      let pe ← proveSt args[3]! (P'.beta #[args[3]!])
      mkAppOptM ``frame_cond #[α, P', args[1]!, args[2]!, args[3]!, pt, pe]
    | ``Id.run, 2 => proveSt args[1]! st
    | ``Pure.pure, 4 => proveSt args[3]! st
    | ``Bind.bind, 6 =>
      -- in `Id`: `x >>= k` is `k x`
      let x := args[4]!
      let k := args[5]!
      let px? ← prove x
      let pk ← proveUnder k
      match px? with
      | some px => return mkApp2 pk x px
      | none => return mkApp pk x
    | ``ForInStep.yield, 2 => proveSt args[1]! st
    | ``ForInStep.done, 2 => proveSt args[1]! st
    | ``ForIn.forIn, 8 => proveForIn args st
    | ``Prod.mk, 4 => proveMk args[2]! args[3]! st
    | ``MProd.mk, 4 => proveMk args[2]! args[3]! st
    | ``Prod.fst, 3 => proveProj args[2]! true st
    | ``Prod.snd, 3 => proveProj args[2]! false st
    | ``MProd.fst, 3 => proveProj args[2]! true st
    | ``MProd.snd, 3 => proveProj args[2]! false st
    | _, _ =>
      if let some m ← matchMatcherApp? e then
        if m.remaining.isEmpty then
          return ← proveMatch m
      proveLeaf st

/-- For `f = fun xs => body` (eta-expanded if needed): `fun xs hxs => proof of body`. -/
partial def proveUnder (f : Expr) : M Expr := do
  let fT ← whnfD (← inferType f)
  let .forallE n t _ _ := fT | throwError "frame_gen: expected a function: {f}"
  withTracked n t fun x xs => do
    let body := (mkApp f x).headBeta
    let τ ← inferType body
    if (← whnfD τ).isForall then
      let pb ← proveUnder body
      mkLambdaFVars xs pb
    else
      let some pb ← prove body | throwError "frame_gen: the body carries no statement: {body}"
      mkLambdaFVars xs pb

partial def proveMk (a b st : Expr) : M Expr := do
  let pa? ← prove a
  let pb? ← prove b
  match pa?, pb? with
  | some pa, some pb => mkAppM ``And.intro #[pa, pb]
  | some pa, none => return pa
  | none, some pb => return pb
  | none, none => proveLeaf st

partial def proveProj (x : Expr) (isFst : Bool) (st : Expr) : M Expr := do
  let τ ← whnfD (← inferType x)
  let some px ← prove x | proveLeaf st
  let a ← carries (τ.getArg! 0)
  let b ← carries (τ.getArg! 1)
  if a && b then
    return if isFst then mkProj ``And 0 px else mkProj ``And 1 px
  return px

partial def proveForIn (args : Array Expr) (st : Expr) : M Expr := do
  -- `@forIn m ρ α inst β xs init f`
  let ρ ← whnfD args[1]!
  let β := args[4]!
  let xs := args[5]!
  let init := args[6]!
  let f := args[7]!
  let lem ←
    if ρ.isConstOf ``Std.Legacy.Range then pure ``frame_forIn_range
    else if ρ.isAppOfArity ``List 1 then pure ``frame_forIn_list
    else if ρ.isAppOfArity ``Array 1 then pure ``frame_forIn_array
    else return ← proveLeaf st
  let P' ← stmtLam β
  let some p0 ← prove init | proveLeaf st
  let pf ← proveUnder f
  mkAppOptM lem (if lem == ``frame_forIn_range then #[β, P', xs, init, f, p0, pf]
    else #[none, β, P', xs, init, f, p0, pf])

/-- Register, for the variables `xs`, the conjuncts of `h : T` that are their statements. -/
partial def registerFrom (xs : Array Expr) (h T : Expr) (acc : Array (Expr × Expr)) :
    M (Array (Expr × Expr)) := do
  let T ← whnfR T
  if T.isAppOfArity ``And 2 then
    let acc ← registerFrom xs (mkProj ``And 0 h) (T.getArg! 0) acc
    return ← registerFrom xs (mkProj ``And 1 h) (T.getArg! 1) acc
  for x in xs do
    if acc.any (fun (y, _) => y == x) then continue
    if let some sx ← mkStmt (← inferType x) x then
      if ← withNewMCtxDepth (isDefEq sx T) then
        return acc.push (x, h)
  return acc

partial def proveMatch (m : MatcherApp) : M Expr := do
  -- the statements of the discriminants are passed into the alternatives
  let mut dProofs := #[]
  let mut carriesD := #[]
  for d in m.discrs do
    match ← prove d with
    | some p => dProofs := dProofs.push p; carriesD := carriesD.push true
    | none => carriesD := carriesD.push false
  let motive ← lambdaTelescope m.motive fun ds _ => do
    let app := mkAppN (mkConst m.matcherName m.matcherLevels.toList)
      (m.params ++ #[m.motive] ++ ds ++ m.alts)
    let some s ← mkStmt (← inferType app) app | throwError "frame_gen: match carries no statement"
    let mut body := s
    for d in ds.reverse, c in carriesD.reverse do
      if c then
        if let some sd ← mkStmt (← inferType d) d then
          body := mkForall `h .default sd body
    mkLambdaFVars ds body
  let lvls := match m.uElimPos? with
    | some pos => m.matcherLevels.set! pos Level.zero
    | none => m.matcherLevels
  let mHead := mkAppN (mkConst m.matcherName lvls.toList) (m.params ++ #[motive] ++ m.discrs)
  let mut T ← whnfD (← inferType mHead)
  let k := (carriesD.filter id).size
  let mut alts' := #[]
  for info in m.altInfos, alt in m.alts do
    let .forallE _ altT rest _ := T | throwError "frame_gen: unexpected matcher type"
    T ← whnfD rest
    let n := info.numFields + (if info.hasUnitThunk then 1 else 0)
    let p ← forallBoundedTelescope altT (n + k) fun ys _ => do
      let xs := ys.extract 0 n
      let hs := ys.extract n (n + k)
      let mut acc := (← read).hyps
      for h in hs do
        acc ← registerFrom xs h (← inferType h) acc
      withReader (fun c => { c with hyps := acc }) do
        let body := (mkAppN alt xs).headBeta
        let some pb ← prove body | throwError "frame_gen: match alternative carries no statement"
        mkLambdaFVars ys pb
    alts' := alts'.push p
  return mkAppN (mkAppN mHead alts') dProofs

end

/-- The hypotheses `h : P x` in the context for the variables `x : σ`; a variable without one gets
`P x` from the leaf tactic when it can (for an unchanged field: `rfl`). -/
def contextHyps (σP : Array (Expr × Expr)) (tac : Syntax) : TacticM (Array (Expr × Expr)) := do
  let mut hyps := #[]
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    for (σe, Pe) in σP do
      unless ← withNewMCtxDepth (isDefEq ld.type σe) do continue
      let want := Pe.beta #[ld.toExpr]
      let mut found := none
      for ld' in (← getLCtx) do
        if ld'.isImplementationDetail then continue
        if ← withNewMCtxDepth (isDefEq ld'.type want) then
          found := some ld'.toExpr
          break
      match found with
      | some h => hyps := hyps.push (ld.toExpr, h)
      | none =>
        let gm ← mkFreshExprSyntheticOpaqueMVar want
        try
          let rest ← Tactic.run gm.mvarId! (evalTactic tac)
          if rest.isEmpty then hyps := hyps.push (ld.toExpr, ← instantiateMVars gm)
        catch _ => pure ()
      break
  return hyps

def frameGen (σP : Array (Term × Term)) (e : Term) (tac : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let σPe ← σP.mapM fun (σ, P) => do return (← elabTerm σ none, ← elabTerm P none)
    let ee ← elabTerm e none
    let hyps ← contextHyps σPe tac
    let ctx : Ctx := { σP := σPe, leaf := tac, hyps }
    let some st ← (mkStmt (← inferType ee) ee).run ctx
      | throwError "frame_gen: {ee} carries no statement"
    unless ← isDefEq (← g.getType) st do
      throwError "frame_gen: the goal is not the statement{indentExpr st}"
    let some e' ← unfoldDefinition? ee | throwError "frame_gen: cannot unfold {ee}"
    let e' := e'.headBeta
    let prf ← (proveSt e' st).run ctx
    g.assign prf
  replaceMainGoal []

/-- `frame_gen σ P e using tac`: prove the statement of `e = f args` (`P e` when `e : σ`, `P` on
the `σ` components of `e` otherwise; it must be the goal up to unfolding) by unfolding `f` once and
running the frame generator, with `tac` on the leaves. -/
elab "frame_gen " σ:term:max P:term:max e:term:max " using " tac:tacticSeq : tactic =>
  frameGen #[(σ, P)] e tac

/-- `frame_gen2 σ₁ P₁ σ₂ P₂ e using tac`: the same, tracking two state types. -/
elab "frame_gen2 " σ₁:term:max P₁:term:max σ₂:term:max P₂:term:max e:term:max " using "
    tac:tacticSeq : tactic =>
  frameGen #[(σ₁, P₁), (σ₂, P₂)] e tac

end Contracts.Track.Frame
