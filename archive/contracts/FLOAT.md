# The float layer

This is the reference for the float lemmas in `contracts/` (Lean `v4.36.0-rc2`, Mathlib). They are
the TRACK_PLAN.md P1 layer: they let a proof about translated code read a `Float32`/`Float`
expression as a real number, either exactly or within a stated error bound. Everything listed here
is sorry-free and depends only on `propext`, `Classical.choice` and `Quot.sound`.

The semantics come from core Lean's own float model. In v4.36, `Float32.add` and the other
operations are *defined* through `Float32.Model` (`pack (UnpackedFloat.add …)`), and the compiler
overrides them with the C operators. So these lemmas are about Lean's definitions, and no
assumption about the hardware is needed. The C library externs (`sinf`, `fmaxf`, …) and the two
`float`/`double` conversions are opaque. Their facts come from the hypothesis `LibmSpec`
(`Contracts/Mission/Spec.lean`).

## Files

| file | kind | content |
|---|---|---|
| `FloatModel/ToReal.lean` | module | `UnpackedFloat.toReal`, canonical forms, `Float.toReal`, `Float.IsFinite` |
| `FloatModel/Order.lean` | module | comparisons against exact values (binary64) |
| `FloatModel/Add.lean`, `Small.lean`, `DivSqrt.lean`, `Bracket.lean` | module | the rounding analysis, format-generic, with the binary64 statements |
| `FloatModel/Float32.lean` | module | the binary32 instance: `Float32.toReal`, `IsFinite`, error bounds, brackets |
| `FloatModel/Compare.lean` | module | NaN/∞ comparisons, `fabsf`, midpoint, the clamp `cvl`, `MIN`/`MAX` |
| `FloatModel/Err.lean` | module | the error bundle `Near` (`Float32.Near`, `Float.Near`) |
| `FloatModel/Lit.lean` | plain | literal values (`f32_unpack`), `two32`, `two64` |
| `Contracts/Track/FloatLib.lean` | plain | the translator's clamps, `MIN`/`MAX`, `fminf`/`fmaxf`, conversions (`LibmSpec`) |
| `Contracts/Track/Frame.lean` | plain | `frame_gen`: invariants of translated `Id.run do` code (see below) |

The first six files are the port of `delegate-port/FloatModel` to v4.36. That port had three
changes: module headers, `Format.he : 2 ≤ exponentBits`, and `if_pos`/`if_neg` renamed to
`ite_eq_left`/`ite_eq_right`. `Compare`, `Err` and `Lit` are new.

`Lit.lean` is a plain file because evaluating a literal needs the bodies of core's conversions
(`OfScientific`, `Int32.toFloat32`), and those bodies are not exposed to modules. For the same
reason, the module lemmas that need the literal `2` of the midpoint take it as the hypothesis
`Two32` (`Two64`), and `Float32.two32` (`Float.two64`) proves it.

## Notation

`⟦x⟧ = x.toReal`: the exact value (`0` on NaN and `±∞`). `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰`, and
`maxFinite32 = (2 − 2⁻²³)·2¹²⁷` for binary32. For binary64 they are `2⁻⁵³`, `2⁻¹⁰⁷⁵` and
`maxFinite`.

## The error model (`Float32.*`; `Float.*` with the binary64 constants)

| name | statement (finite operands; the exact result at most `maxFinite32` in magnitude) |
|---|---|
| `add_err_all`, `sub_err_all` | the result is finite and `|fl(a∘b) − (⟦a⟧∘⟦b⟧)| ≤ u·|⟦a⟧∘⟦b⟧|` (exact below `2⁻¹²⁶`) |
| `mul_err_all` | `|fl(a·b) − ⟦a⟧⟦b⟧| ≤ u·|⟦a⟧⟦b⟧| + η` |
| `div_err_all` | (`⟦b⟧ ≠ 0`) `|fl(a/b) − ⟦a⟧/⟦b⟧| ≤ u·|⟦a⟧/⟦b⟧| + η` |
| `sqrt_err_all` | (`⟦a⟧ ≥ 0`) `|fl(√a) − √⟦a⟧| ≤ u·√⟦a⟧ + η` |
| `add_error`, `sub_error`, `mul_error` | the same bounds on the normal range, without `η` |
| `add_std_model`, `sub_std_model`, `mul_std_model` | `fl(x) = x(1+δ)` with `|δ| ≤ u` (normal range) |
| `add_error_small`, `sub_error_small` | exact below `2⁻¹²⁶` |
| `mul_error_small` | below `2⁻¹²⁶`: within `η` |
| `add_bracket`, `sub_bracket`, `mul_bracket`, `div_bracket`, `sqrt_bracket` | **monotonicity of rounding**: a finite float `f` with `⟦f⟧ ≤ x` (resp. `≥`) stays `≤` (resp. `≥`) after rounding `x` |
| `exists_double` | `2⟦a⟧` is a float when it does not overflow |
| `abs_toReal_le_maxFinite` | every float's value is at most `maxFinite32` in magnitude |

## Values, finiteness, comparisons (`Compare.lean`)

| name | statement |
|---|---|
| `isNaN_iff`, `trichotomy` | every float is finite, NaN, `+∞` or `−∞` (by its unpacked form) |
| `not_isNaN_of_isFinite`, `isFinite_neg`, `toReal_neg` | |
| `toReal_abs`, `isFinite_abs` | `fabsf` is exact: `⟦|a|⟧ = |⟦a⟧|` |
| `lt_iff_toReal_lt`, `le_iff_toReal_le`, `decide_lt_eq`, `decide_le_eq`, `beq_iff_toReal_eq` | (from `Float32.lean`) on finite floats, the float comparisons are the real ones |
| `not_lt_of_isNaN_left/right`, `not_le_of_isNaN_left/right` | every comparison with a NaN is false |
| `lt_of_unpack_inf_neg`, `lt_of_unpack_inf_pos` | `−∞ <` every finite float `< +∞` |
| `between_of_not_lt_of_not_gt` | a non-NaN `a` with `¬ a < lo` and `¬ hi < a` (finite bounds) is finite with `⟦lo⟧ ≤ ⟦a⟧ ≤ ⟦hi⟧` |
| `add_between`, `mid_between` | `(a + b) / 2` of finite floats (each at most `maxFinite32/2`) is finite and lies between them |
| `ite_lt_min`, `ite_gt_max` | `MIN`/`MAX` as emitted (`if a < b then a else b`) are finite with value `min`/`max` |

### The clamp `constrain_value_line`

`Float32.cvl amt lo hi` is `if amt.isNaN then (lo + hi) / 2 else if amt < lo then lo else if
amt > hi then hi else amt`. Every translated `constrain_value_line_float` is this function by `rfl`
(`FloatLib.*_cvl`, `FloatLib.cvl_eqs`). The same holds for `constrain_value_line_double` and
`Float.cvl`.

| name | statement |
|---|---|
| `cvl_between two` | for finite `lo`, `hi` (at most `maxFinite32/2`) and **every** `amt` (NaN, `±∞` included), the result is finite and between `lo` and `hi`, in either order |
| `cvl_mem two` | the result lies in every interval `[A, B]` that contains `lo` and `hi` |
| `cvl_symm two` | `cvl amt (−k) k` is finite with `|·| ≤ k` (`0 ≤ ⟦k⟧ ≤ maxFinite32/2`): every integrator limit |
| `cvl_of_between` | the identity on finite values in `[lo, hi]` |
| `FloatLib.cvl_toReal` | for finite `amt` and `lo ≤ hi`, `⟦cvl amt lo hi⟧ = max ⟦lo⟧ (min ⟦amt⟧ ⟦hi⟧)` |

## Literals (`Lit.lean`)

`f32_unpack` proves `x.toModel.unpack = u` for a closed literal `x` by evaluation (the kernel checks
it). From that equation, `Float32.toReal_of_unpack` and `isFinite_of_unpack` (and their `_zero`
forms, plus the `Float.` versions) give the value and finiteness.

```lean
theorem unpack_lit_half :
    (0.5 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-24) (by decide) := by f32_unpack
```

The file already has `0.0`, `1.0`, `0.5`, `0.125`, `0.6875`, `Int32.toFloat32 2`,
`Int32.toFloat32 0`, the double `0.0` and `Int32.toFloat 2`, each as `unpack_*`, `toReal_*`
(simp) and `isFinite_*`.

`Float.toFloat32 (c : Float)` and `Float32.toFloat` are opaque externs in core v4.36, so their
values come from `LibmSpec`:

* `FloatLib.toFloat32_exact` for a double literal that is a `float` value;
* `FloatLib.toFloat32_near` for correct rounding;
* `FloatLib.toFloat_near` for exact widening.

`fminf`/`fmaxf` are covered by `FloatLib.fminf_near` and `fmaxf_near`.

## The error bundle (`Err.lean`)

`Float32.Near x r ε` says that `x` is finite and `|⟦x⟧ − r| ≤ ε`. `Float.Near` is the same for
doubles. Each operation propagates it and adds its own rounding. The side condition is a
no-overflow bound stated on the real side.

| name | conclusion |
|---|---|
| `Near.exact`, `Near.of_eq` | `Near x ⟦x⟧ 0`, `Near x r 0` |
| `Near.neg` | `Near (−a) (−r) ε` |
| `Near.add`, `Near.sub` | `Near (a ± b) (ra ± rb) (εa + εb + u(|ra ± rb| + εa + εb))` |
| `Near.mul` | `Near (a·b) (ra·rb) (|ra|εb + |rb|εa + εaεb + u(|ra|+εa)(|rb|+εb) + η)` |
| `Near.div` | (`εb < |rb|`) `Near (a/b) (ra/rb) ((|rb|εa + |ra|εb)/(|rb|(|rb|−εb)) + u(|ra|+εa)/(|rb|−εb) + η)` |
| `Near.sqrt` | (`⟦a⟧ ≥ 0`, `ra ≥ 0`) `Near (√a) (√ra) (√εa + u√(ra+εa) + η)` |
| `Near.weaken` | to any `r'`, `ε'` with `|r − r'| + ε ≤ ε'` |
| `Near.abs_le`, `Near.toReal_le`, `Near.le_toReal`, `Near.eps_nonneg` | reading the bound back |

The usage pattern is bottom-up:

```lean
have h : Float32.Near (a * b + c) (ra * rb + rc) _ :=
  (ha.mul hb (by norm_num)).add hc (by norm_num)
exact h.weaken (by norm_num)      -- against the stated real law and bound
```

## Invariants of translated code: `frame_gen` (`Contracts/Track/Frame.lean`)

`frame_gen σ P (f args) using tac` proves the statement of `P` on every `σ`-value that `f args`
returns. The statement is `P` on the `σ` components of the result: on pairs it is the
conjunction, and on join points it is `∀ args, P args → P result`. `frame_genN [σ₁, …] [P₁, …]`
tracks several state types. The tactic makes one pass over the unfolded body:

* a `let`, or a `have`, becomes a variable with its hypothesis, so there is no `zeta` blowup. A
  value whose statement fails is bound without one, so a later clamp can repair it.
* `if`/`dite`/`cond`/`match`: each branch is proved with the branch condition as a hypothesis.
* `forIn` over ranges, lists and arrays uses `P` as the loop invariant.
* `let (a, b) := e` binds the components of `e`.
* every other term is a *leaf*, given to `tac`. If `tac` fails on a call of a definition, the
  definition is unfolded, up to `frame_gen.inline` levels (default 8).

Leaf tactics must stay at reducible transparency: `with_reducible exact …`, and `field_assumption`,
which finds a hypothesis or a field of one at reducible transparency. A default-transparency
`exact` can start unfolding float arithmetic in the kernel's model. `set_option frame_gen.debug
true` logs the leaves, the inlinings and the `let`s left without a statement.

`frame_gen` exists because `mvcgen` (`Std.Do`) did not work on these bodies. Its default mode
splits every join point per path, which gives exponentially many conditions: hundreds for
`output_armed_stabilizing`, over 5 minutes. Its `+jp` mode fails on `else if` chains in
v4.36.0-rc2 (`rwIfWith` builds an ill-typed `Eq.mpr`, reproduced on a 12-line example).
