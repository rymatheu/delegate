# 10. The formal link

**Status (2026-11-18):** built. `Harness/Link.lean` (the semantics and the theorem), `Harness/LinkCheck.lean` (the two checkers and their soundness), `Harness/LinkPlan.lean` (the instance for a system node), `Harness/LinkKernel.lean` (the range checker decided by the kernel on literals from `ap_ctl`). Core Lean 4.35, no Mathlib, no `sorry`, no new axioms (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only). `harness link NAME` prints the plan and the statement; `harness status NAME` reports the counts; `harness obligations NAME --status` says of each obligation whether it is proved, stated or open, from the same plan.

The question: if every child of a system meets its contract and every obligation is discharged, does the system, as the runtime steps it, meet its computed contract? The theorem below answers yes, for the semantics that `Harness/Runtime.lean` and `Harness/Campaign.lean` implement, and the instance for a node lists exactly what is still a hypothesis.

## Definitions (all in `Harness/Link.lean`)

**Values.** A record is the runtime's `Record` (`Array UInt32`). A clause is the runtime's resolved `Clause`; it holds on an environment `env` when `c.expr.holds env = true`, the same `Expr.holds` the monitors call. Lean's `Float32` is opaque to the kernel, so nothing is proved about float arithmetic: the theorem is about clause truth values, and `Expr.holds` is a fixed function of the words. The checkers need a handful of IEEE facts; they are fields of one structure, `FloatFacts`, an explicit hypothesis wherever it is used.

**Trace of a node** (`Trace`): a parameter record, an input record and an output record per tick (`Nat → Record`), for one case (one `init`, then `step` at ticks 0, 1, 2, ...). Its environment at tick `t` is `params ++ input t ++ output t`, exactly the array `runCampaign` evaluates an instance's clauses on.

**Run of a node** (`Run`): a tree of traces with the node's shape: the node's own trace and one run per child. It is what `Running.init` and `Running.step` return per tick (the records of every instance), arranged as a tree instead of the preorder array.

**Wiring** (`Consistent s r`), for a checked system `s : CSys` and a run `r = ⟨τ, kids⟩`, stated with the runtime's own `fetch` (made public for this, see "Changes"):
- one kid per child;
- child `i`'s parameters are `children[i].params.map (fetch #[] τ.params #[] #[])` (what `Running.init` passes);
- child `i`'s input at tick `t` is `children[i].input.map (fetch (τ.input t) τ.params outs prev)`, where `outs` is the array of the outputs at tick `t` of children `0 … i-1` only (what `Running.step` has pushed when it assembles child `i`'s input; an `out` source naming a later child reads `#[]` and so the word 0, as in the runtime) and `prev` is the `prev` state at tick `t`;
- the `prev` state at tick 0 is `s.prevs.map (·.init)` (set by `init`), at tick `t+1` it is `s.prevs.map fun w => outs_t[w.child]![w.field]!` with `outs_t` all children's outputs at tick `t` (set at the end of `step`);
- the system's output at tick `t` is `s.outputs.map (fetch (τ.input t) τ.params outs_t prev)`.

`const`, `param`, `input`, `out` and `prev` sources are all read by `fetch`, so they mean what the runtime makes them mean. Renames, `inst`, `fix` and `hide` need no separate semantics: `compose` absorbs them into the wires (`fix` becomes `const` sources, renames become different source names, `hide` drops output wires), and the checked system the runtime steps is the absorbed one. What adapters change is the *contract* (renamed or constant-substituted clauses); that is handled by the transport checker below.

**Behavior** (`Beh exe n r`), with `exe : Checked → Trace → Prop` the set of traces each module's executable can produce (a variable: the C++ is never modeled). For a module, a run `⟨τ, []⟩` with `exe c τ`; for a system, a run whose wiring is `Consistent` and each of whose kids is a behavior of its child. Both require records of the schema's sizes (`Sized`), which the runtime ensures by decoding every reply with the schema and assembling every record with one source per field.

**History form.** `NA n r t`: the node's assumption holds at tick `t` on its environment. `Deep n r t`: at tick `t` the node's assumption and guarantee hold, and recursively every instance below it has its assumption and its guarantee at `t`. `DSat n r := ∀ t, (∀ s ≤ t, NA n r s) → Deep n r t`. For a module this is the history form the monitors check (guarantee at `t` while the assumption has held at every tick so far); for a system it says more: while the system's assumption has held, no inner instance has a discharge failure or a violated clause. In the algebra, `DSat` is `Step.always` of the step contract `nodeStep n := ⟨NA n, Deep n⟩` over runs.

**Leaf claim** (hypothesis 1): `LeafClaim exe c := ∀ τ, exe c τ → Sized c τ → ∀ t, (∀ s ≤ t, A at s) → G at t`, one per distinct module. This is what campaigns test; it stays a hypothesis.

**Discharged** (hypothesis 2). For child `i`'s assumption clause `a`, the loop form `LoopDis`: on every behavior, at every tick `t` such that the system's assumption has held at all ticks up to `t`, the children before `i` are `Deep` at `t`, and all children are `Deep` at every tick before `t`, the clause `a` holds on child `i`'s environment at `t`. A discharge table entry is a stronger, cited form `CitedDis`: the conjunction of the cited clauses implies `a`, each cited clause read at the tick at which the wire delivers its values: `assume.q` at `t`; a guarantee of instance `j/…` at `t` when every wire from `j` into `i` is `out` and `j < i`, at `t-1` otherwise; at `t = 0` a `t-1` citation is absent, so the implication must hold from the `prev` initial values alone. `CitedDis` with well-placed citations implies `LoopDis` (`citedDis_loop`).

**Covered.** A guarantee clause of the system holds at `t` whenever the system's assumption has held up to `t` and every child is `Deep` at all ticks up to `t` (`Cover`).

## Theorems

1. `link` (one system, any `CSys`): `Consistent s ⟨τ,kids⟩`, `DSat` for every kid, `LoopDis` for every assumption clause of every child, and `Cover` for every guarantee clause of `s` give `DSat (system s) ⟨τ,kids⟩`. Proved by instantiating `Algebra.loop` (the step contracts of the children, environment `NA` of the system), so the induction over ticks and schedule position is the algebra's, not a second copy.
2. `sound` (nesting): if every module in the tree satisfies its leaf claim and every system in the tree satisfies `SysOK` (`LoopDis` and `Cover` on all its behaviors), every behavior of the tree satisfies `DSat`. By induction on `Beh`; a child that is a system gets its `DSat` from this theorem one level down. Corollary `sound_implements`: `Beh exe n ⊨ (nodeStep n).always` in the sense of `Algebra.Implements`.
3. Checker soundness (`Harness/LinkCheck.lean`): the transport checker (a composite clause is a child clause read through the wires, the case of every clause `compose` copies, renames or fixes) gives `LoopDis` for a child clause copied into the composite's assumption and `Cover` for a composite guarantee copied from a child; the range checker gives `CitedDis`. It reads the obligation by its structure: `∧` (both sides), `∨` (either side), a guarded `¬b ∨ body` (the body with `b` assumed true, under which cited clauses `¬b ∨ body'` with the same guard signal give `body'`), a formula of constant Booleans (evaluated), and leaves: atoms identical to a cited one through the wires, or range atoms `lo ≤ x`, `x ≤ hi`, `<`, `|x| ≤ b`, `|x| < b`, `finite x`, implied by cited atoms on the same signal (`x = c` also as a cited fact), or on a constant, with bounds compared as exact integers scaled by 2^149. Both under `FloatFacts` (21 named IEEE facts). A constant is compared exactly when it is an f32 word or a u32 below 2^24 (exact in binary32).
4. Instance (`Harness/LinkPlan.lean`): for a checked node, the plan (which clause is discharged how), the counts, the printed statement with its named hypotheses, and an `Algebra.Ev` tree `linkEv exe n : Ev LinkRec (Beh exe n ⊨ (nodeStep n).always)` whose leaves are the leaf claims, `FloatFacts`, and the assumed (`CitedDis`) and open (`OpenDis`, `OpenCover`) hypotheses; checker results enter as Lean proofs, so `Ev.sound` (`linkEv_sound`) applies. For a child assumption clause the plan tries, in order: the composite's own clause through the wires (transport); the range checker on the wired constants and `prev` initial values alone (the clauses `fix` dropped as held by its constants, and the table's entries of kind `constant`, which are open if this fails); the range checker on the whole composite assumption (hand-written systems state combined clauses); the discharge table's citations (range checker, else assumed); otherwise open.

## Results

`harness link NAME` on every system (2026-11-18, main, after the controller chain's shared discharge table, `ardupilot/harnesses/chain/Discharges.lean`, and the estimator's, supervisor's and mixer's code-fact guarantees; the boundary of what stays open is listed in the round's report). Wires: child assumptions that are the composite's own clause, plus guarantees copied, both proved by transport. Checker: discharges proved by the range checker (from the table's citations / the wired constants / the composite's whole assumption). Stated: table entries no checker proves (`CitedDis` hypotheses). Open: obligations with no usable discharge (`OpenDis`). Uncovered: system guarantees that are not a child's (`OpenCover`).

| System | Leaf hyps (instances) | Wires | Checker | Stated | Open | Uncovered |
|---|---|---|---|---|---|---|
| `rate` (hand-written) | 1 (3) | 18 + 9 | 6 (0/0/6) | 0 | 0 | 9 |
| `rate_c` | 1 (3) | 24 + 12 | 0 | 0 | 0 | 0 |
| `inner_loop` (hand-written) | 2 (4) | 65 + 12 | 7 (0/1/6) | 0 | 1 | 10 |
| `inner_loop_c` | 2 (4) | 73 + 38 | 1 (0/1/0) | 0 | 1 | 0 |
| `closed_inner` | 3 (5) | 68 + 42 | 1 (0/1/0) | 0 | 8 | 0 |
| `est_loop` | 3 (3) | 9 + 21 | 0 | 1 | 5 | 4 |
| `ap_ctl` | 5 (7) | 126 + 75 | 17 (15/2/0) | 5 | 2 | 0 |
| `ap_flight` | 8 (10) | 25 + 82 | 78 (12/66/0) | 2 | 49 | 0 |
| `ap_full` | 9 (11) | 110 + 98 | 23 (19/4/0) | 2 | 46 | 0 |
| `ap_full_ekf` | 9 (11) | 116 + 111 | 31 (28/3/0) | 3 | 42 | 0 |
| `px4_inner` | 2 (2) | 290 + 29 | 2 (2/0/0) | 16 | 0 | 0 |
| `px4_closed_rate` | 6 (6) | 407 + 71 | 2 | 16 | 33 | 0 |
| `px4_est` | 4 (4) | 256 + 67 | 15 | 0 | 36 | 0 |
| `px4_est_flying` | 7 (7) | 545 + 98 | 17 | 16 | 37 | 0 |
| `px4_att_loop` | 9 (9) | 525 + 107 | 25 | 16 | 105 | 0 |
| `px4_pos_loop` | 10 (10) | 594 + 118 | 32 | 16 | 113 | 0 |
| `px4_auto_loop` | 12 (12) | 720 + 130 | 48 | 16 | 173 | 3 |
| `px4_cmd_loop` | 13 (13) | 1039 + 175 | 181 | 16 | 151 | 3 |
| `px4_nav_loop` | 16 (16) | 1099 + 275 | 230 | 16 | 198 | 6 |
| `px4_full` | 16 (16) | 1724 + 325 | 364 | 17 | 154 | 1 |

The PX4 rows (2026-11-18, with the PX4 discharge table `px4/harnesses/px4_chain/Discharges.lean`): the width and slot obligations between generated ports are discharged by the publisher's generated guarantees (`Ports.outWidths`: a field narrower in its C struct than its record field carries a value of the C type; a queued topic's count is at most the slots the glue copies), navigator's mission storage by px4_mavlink's mirror mark, navigator's `window_holds_tick` by the observer `px4_cmd_window`. The checker proves the unsigned ones; the 16 stated per composite are the signed (int8) actuator saturation widths of control_allocator_status (the range checker compares f32 words and u32 below 2^24 only), and in `px4_full` also fmm's one-slot read of vehicle_command (MAVLink publishes up to 8 per tick). Still open: everything that is not a neighbor's range fact (sensor-level physics, the hand-written bridges' outputs, navigator's `command_window`, an assumption on the ground station's traffic). The uncovered guarantees are the truth clauses `px4_auto_loop`, `px4_cmd_loop`, `px4_nav_loop` and `px4_full` add against the simulator.

`ap_full` and `ap_full_ekf` each have one obligation (a constant-fed clause) proved by transport, so `obligations` counts one more proved there (24 and 32).

**`ap_ctl`, before and after** (`harness obligations ap_ctl --status`): before, "24 obligations: 22 discharged, 2 open", where "discharged" meant only that a table entry existed. After: "24 obligations: 17 proved (transport or range checker), 5 stated (hypotheses of the link theorem), 2 open". Of the 8 entries the first checker left stated, the guards and equality atoms prove 3 (`position.tgt_handover_args`, `attitude.pc_throttle_cutoff_range`, `rate_c.yaw_scales_range`), and the new `constant` entry `position.lt_handover_args` (constant false guards) is proved too. Still stated: `rate_c.roll/pitch_scales_range` (bound `1 + atc_thr_g_boost`), `mixer.commands_bounded` (bound `7e15 + kimax`, citations below `rate_c`), `guidance.pc_limits_range` (`limits_follow_guidance` relates signals, an induction over ticks), `position.tgt_bounded` (`wp_leg_spline` must be related to the spline commands).

**Not extended:** citations of a clause below a child (`rate_c/roll.command_magnitude`). The semantics has them (`GAt`, `citedDis_loop`); the checker would need `slotSig` through a nested system's wiring (its `Consistent`, one level down), and the only such citation in `ap_ctl` also has a non-literal bound, so it would prove nothing more today.

## Findings

- The tick of a citation is not in the discharge table; the plan infers it from the wiring as stated above. At the first tick a `prev` citation is absent, so the discharge must hold from the initial value: this is what `ap_ctl`'s `withInit` values supply, and the checker proves those first-tick cases from the literal values (`position.ac_lean_range`, `rate_c.*_signals_bounded`).
- `harness obligations --status` reported `inner_loop_c/mixer.ff_range` OPEN, but the constants `fix` wires (0) discharge it; `fix` itself dropped the substituted clause as held. It is now reported proved, from the constants.
- `CNode.obligations` does not list a child assumption that mentions only fields the parent feeds from its own inputs and parameters, on the presumption that the parent's assumption gives it. Nothing checked that for hand-written systems; the link checks it (the 6 such clauses of the hand-written `rate`, also inside `inner_loop`, follow from `rate`'s assumption by the range checker).
- `obligations --status` counted a table entry of kind `guarantee` or `assumption` as discharged when its clauses existed. It now reports proved, stated or open from the link's plan; an entry of kind `constant` is proved by the checker from the wired constants, or open.
- The runtime's `fetch` of an `out` source naming a later child reads 0, and a child parameter fed by `input` reads 0 (`Running.init` passes `#[]`); `Sys.check` excludes both. The model follows the runtime, and the transport checker accepts only what the check allows.
- Hand-written systems and `est_loop` state guarantees that are not their children's (`rate`'s `command_sum` and others, `est_loop`'s tracking clauses): they are `OpenCover` hypotheses, not derived.

## What the model does not cover

- The executables: `exe` is a variable. The theorem says nothing about whether the C++ meets its contract; campaigns do.
- One case: a trace starts at `init`. Restarts within a run, process crashes and pipe errors are outside.
- The instance is computed, not kernel-reduced: `Node.check`, `absorb` and `CNode.obligations` are `partial` and contract literals are made by `Float32.ofScientific`, so the kernel cannot evaluate a concrete system. The generic theorems and the checkers' soundness are kernel-checked for every system; which plan a concrete system gets is decided by running the checkers (compiled), the same code path that builds the system the runtime steps. A kernel `decide` of the range checker on literal bits copied from `ap_ctl` shows the comparison itself is kernel-decidable.
- `FloatFacts` (IEEE facts about `≤`, `<`, `==`, `abs`, negation, `isFinite` and bit round trips of Lean's `Float32`) are hypotheses, never proved.
- Root records: the root's parameter and input records are assumed schema-sized (the campaign generator's job).
