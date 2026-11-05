# cpp2lean

A deterministic, syntax-directed translator from a subset of C++ to executable Lean 4 (phases 0, 1
and 2 of the translator plan: free functions over numbers, then classes; phase 3, ArduPilot's control
classes). The output is
a shallow model: ordinary Lean functions over `Float32`, `Float`, the fixed-width integer types,
structures and inductives, written in `do` notation so that they read like the C++; a class becomes a
namespace with a `State` structure and one function per member function that threads the state. The
model is checked against the C++ by differential execution, bit for bit.

```
file.cpp --clang++ (flags below) -Xclang -ast-dump=json -fsyntax-only--> AST JSON
AST JSON --cpp2lean.py (one handler per clang node kind; rejects everything else)--> Name.lean
Name.lean --lake build (lean/)--> Lean executable      file.cpp + driver --clang++--> C++ executable
both executables, same input lines --difftest.py--> bit comparison
```

## Usage

```
python3 cpp2lean.py file.cpp -o OutDir [--namespace Name] [--header FILE]...
    [--boundary Class,Class | --boundary @file]... [--param-class Class=type]...
    [--extern name:LeanName[:N]]... [-I dir]... [--clang-arg ARG]... [--keep-going]
    [--lib-dir DIR]... [--ap-param] [--drop Qual::name]... [--boundary-fn Qual::name]... [--src-root DIR]
    [--use SPEC | --use @file]... [--nest] [--type-name CXX=Lean]... [--output-log]
    [--boundary-call Class::member]... [--boundary-query Class::member]... [--array-params] [--site-inputs]
    [--boundary-live Class]... [--boundary-static Class::member]...
```

| option | meaning |
|---|---|
| `--namespace Name` | Lean namespace of the free functions and module name (default: the file name in CamelCase, `numeric.cpp` -> `Numeric`); must differ from every class name |
| `--header FILE` | also translate the declarations of this header (a class defined in `AC_PID.h`, its member functions in `AC_PID.cpp`); otherwise only the main file is translated |
| `--boundary C,...` | classes that are not translated (the stub boundary): their objects are not state, what is read from them becomes `Inputs` (see "Classes") |
| `--param-class C=type` | a class holding one parameter value (ArduPilot's `AP_Float=float`, `AP_Int8=int8_t`): members of this class form the `Params` structure |
| `--extern name:Lean[:N]` | a function outside the translated files (or only declared in them) and the Lean function to call for it, with only the first N arguments if N is given (e.g. `constrain_value_line:AP_Math.constrain_float:3` drops the line number) |
| `-I dir`, `--clang-arg ARG` | include directories and further clang arguments for the AST (for ArduPilot: the reference build's `-std=gnu++11 -cl-single-precision-constant -D...`, `-include ap_config.h`) |
| `--keep-going` | survey mode: also translate the member functions of a class some of whose data members were rejected, to list every rejection (the output is not usable) |
| `--lib-dir DIR` | files under DIR (ArduPilot's `AP_Math`, `Filter`) are translated only as far as the translated files use them: the functions they call, the classes and template specializations they hold or call (see "ArduPilot") |
| `--ap-param` | ArduPilot's `AP_Param`: members of type `AP_ParamT<T>` (`AP_Float`, `AP_Int8`, ...) are parameters; `var_info` tables, `setup_object_defaults`, `load`, `save` as described in "ArduPilot" |
| `--drop Qual::name` | calls of this function are left out (an effect outside the model: `AP_InternalError::error`); a call whose result is used is rejected |
| `--boundary-fn Qual::name` | a free function whose result is an input (`AP_HAL::millis`): each call without arguments is a field of `Inputs` |
| `--src-root DIR` | source paths in comments and messages relative to DIR (ArduPilot's `libraries/`) |
| `--drop Class::member` | (phase 3) also a data member or member function: not part of the model; see "AP_Motors" |
| `--use SPEC` | a library function, member function or constructor translated as if a translated file called it: `name` (every overload and template specialization), `Class<args>::member`, optionally with parameter types `name(float, Vector3<float>)`; `@file` reads one per line (`ardupilot/AP_Math.use`) |
| `--nest` | the classes are emitted inside the file's namespace too (`AP_Math_lib.Vector3f.State`), so that several translations share one Lean package |
| `--type-name CXX=Lean` | the Lean name of a class template specialization whose typedef is not unique (`Vector2<double>=Vector2p`) |
| `--output-log` | outputs to the boundary are the calls in order, `Outputs := Array Output` with one constructor per boundary function, instead of the last values written |
| `--boundary-call Class::member` | a member function of a translated class that belongs to the boundary (`AP_Motors::rc_write`): not translated; a call is an output (void) or an input (a value) |
| `--boundary-query Class::member` | a non-const member function of a boundary class that does not change the object (a getter not marked `const`: `AC_AttitudeControl::get_bf_feedforward`): its calls are inputs, as those of a const member function |
| `--array-params` | a `const T *` parameter read only by subscript is the array the caller passes (`AP_MotorsMatrix::add_motors`) |
| `--site-inputs` | a const boundary call with non-constant arguments, outside loops, is one input per call site |
| `--boundary-live Class` | (with `--output-log`) a boundary class whose reads are live: each read is a function of the output log so far and of the call's arguments, `Outputs → args → T`, applied at the read, so a read after a call into the object sees the call (AC_WPNav reading AC_PosControl; see "AC_WPNav, the AHRS view, and the two vehicles") |
| `--boundary-static Class::member` | a member function of a boundary class that reads nothing of its object (`AP_AHRS::calc_trig`): translated as a function of its arguments (named `Class_member`), its calls are calls of it |

Writes `OutDir/Name.lean`, `OutDir/Name.signatures.json` (the translated free functions and classes
with their C++ signatures, their state leaves and inputs, the enums, and every floating literal with
the bits clang gives it; read by `difftest.py`), and `OutDir/CppLibm.lean` when the C++ calls
`fmaxf`/`fminf`/`fmax`/`fmin`. Exit status 0 on success; 1 if clang fails; 2 if the file is outside
the subset, after printing one line per rejection, in source order (the file of each rejected
construct, which may be a header):

```
tests/reject_cases.cpp:7:32: rejected: pointer or reference type `const float *`
tests/reject_cases.cpp:18:16: rejected: recursive call (function `factorial` is on a call cycle)
tests/reject_cases.cpp:24:5: rejected: `while` loop whose trip count is not a compile-time constant (...)
```

The first rejected construct of each free function, constant, data member and member function is
reported, so one run lists everything that needs work. Python 3 standard library only; clang is
`clang++` (or `$CXX`).

Other commands:

```
python3 difftest.py [--seed S] [--random N] [--calls N] [example ...]   # differential test, exit 0 iff 0 lines differ
tests/run_tests.sh [--update]                                 # golden, rejection, build and difftest checks
```

Layout:

- `cpp2lean.py` (the translator), `difftest.py` (the differential test: driver generator and harness).
- `examples/`: the demonstration inputs (`numeric`, `mixed`, `boost` for phase 1; `pid` and `shape` for
  phase 2; `motors` for phase 3's boundary outputs; `frame` for the constructs added for AP_Math and
  AP_Motors, with its C++ environment `frame_env.h`; `control` for those added for AC_AttitudeControl
  and AC_PosControl), their configurations `*.json` (namespace, translator options, class-driver
  configuration) and the generated C++ drivers `*_driver.cpp`; `navigate` (with its C++ environment
  `navigate_env.h` and its library directory `navlib/`) for the constructs added for AC_WPNav.
- `tests/`: golden output (`tests/golden/`, `tests/golden/ardupilot/`), rejection inputs with their
  expected messages, and `run_tests.sh`.
- `lean/`: the Lean package (`lakefile.toml`, `lean-toolchain`; core Lean only, no Mathlib). It holds
  the translated modules, `CppLibm.lean`, the generated difftest driver `Main.lean` (executable `demo`),
  `Compose.lean` (copied there by `ardupilot/compose/compose.sh`, executable `compose`), the Lean vehicle
  `Vehicle.lean` and `VehicleMain.lean` (executable `copter_lean`) with the generated
  `VehicleParams.lean`. `difftest.py` keeps the library roots in step with the examples.
- `ardupilot/`: phase 3, the translation of ArduPilot's control classes.
  - `src`: the ArduPilot tree at commit 802db19de1 (a symbolic link; every script reads it through the
    variable `AP`, default `ardupilot/src`, and uses `$AP/libraries`). Nothing in it is modified.
  - `stubs/`: C++ stub headers that the ArduPilot classes compile against in place of the HAL-facing
    parts of the tree (`ap_config.h` and `hwdef.h` for waf's generated headers, `AP_AHRS/AP_AHRS.h` and
    `AP_AHRS/AP_AHRS_View.h` returning a scripted AHRS sample, `AP_Scheduler`, `AP_Logger`,
    `AP_BattMonitor`, `AP_Baro`, `AP_Notify`, `AP_Vehicle`, `GCS_MAVLink`, `SITL`), and
    `oracle_env.cpp`, the out-of-line definitions they link against (singletons, the HAL clock, a HAL
    with a no-op `RCOutput`, `AP_Param` defaults from the real `var_info` tables). They come first on
    the include path, before `libraries/AP_Common/missing` and `libraries/`.
  - `standin/`: a C++-only stand-in for a boundary header that a translated file includes from its own
    directory (`standin/AC_AttitudeControl/AC_AttitudeControl.h`), put in place by clang's
    `-ivfsoverlay` for the C++ side of a difftest only (`cxx_overlay`).
  - `translate_*.sh` with their unity files `unity_*.cpp` and outputs in `out/`, `AP_Math.use`,
    `check_unity.py`, `check_shared.py`, the difftest configurations `*.json`, the C++ environments
    `*_env.cpp`, `ap_motors_driver.h`, `cpp2lean_events.h`, the generated drivers, and
    `motors_coverage.py`.
  - `compose/`: the per-tick composition check (`compose.sh`, `compose_env.cpp`, `Compose.lean`).
  - `ahrs/`: the AHRS view derivation's sources: `extract.py` (copies `AP_AHRS_View::update` and
    `AP_AHRS::calc_trig` out of ArduPilot's files, unmodified, at their line numbers),
    `AP_AHRS_View_decls.h` (the declarations they need) and the two copies.
  - `vehicle/`: the reference vehicle `copter_ref.cpp` with `vehicle_env.cpp`, `build.sh` (both
    vehicles), `gen_params.py` (the Lean vehicle's parameter tables) and `replay.sh` (the replay
    check).
  - `data/`: a recorded flight of 8431 ticks at 400 Hz: `inputs.txt` (the samples, one line per tick
    in the protocol of `sim/PROTOCOL.md`), `trace.txt` (the navigator targets of each tick),
    `oracle-nosincos.txt` (the reference output of the compiled C++ classes on those samples and
    targets: the 22 values per tick, as exact decimals and bit patterns) and
    `oracle-diag-floattrig.txt` (the same with single-precision quaternion trig, a deliberate
    variant used as a sensitivity check).
- `sim/`: the closed-loop flights in gym-pybullet-drones (`README.md`, `PROTOCOL.md` the lock-step
  protocol of the two vehicles, `run_copter.py`, `fly.sh`, `compare_flights.py`, `params/`, `out/`
  the flights, `RESULTS.md`).
- `build/`: driver binaries, inputs and outputs of the last difftest run, the reference vehicle
  (`build/vehicle/`).

## Compilation assumptions

Verbatim from the plan:

> The C++ is compiled with no excess precision (`FLT_EVAL_METHOD == 0`, true on x86-64 and arm64), `-ffp-contract=off`, no `-ffast-math`, `-fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos` (clang fuses sine and cosine of one argument into `__sincos*_stret`, which is not bit-identical to separate calls), and the same C library on both sides. Signed integer arithmetic never overflows (the C++ has no undefined behavior on the executed paths). These are the flags the reference build of the ArduPilot classes uses (`ardupilot/vehicle/build.sh`); the translator's own test harness uses the same ones.

The AST is produced with exactly `clang++ -std=c++17 -O2 -ffp-contract=off -fno-fast-math
-fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -Xclang -ast-dump=json
-fsyntax-only file.cpp`.

**Amendment found by the difftest: `-fno-builtin` for code generation.** With the plan's flags
alone, clang -O2 rewrites libm calls whose arguments are constants. In `examples/mixed.cpp`,
`powf(fabsf(x), 0.5f)` compiles to an `fsqrt` sequence (LLVM's pow(x, 0.5) -> sqrt simplification
needs no fast-math flag), while the Lean side calls libm `powf`; macOS `powf` and the correctly
rounded square root differ by 1 ulp at x = 0xbf88ec2f (C++ `trig_mix` = 0xbfccfb05, Lean
0xbfccfb03; `difftest.py` with the plan's flags only: 1 of 110000 lines differ). The same
simplifier also rewrites `powf(x, 2.0f)` to `fmul`, `powf(x, -1.0f)` to `fdiv`, `powf(2.0f, x)` to
`exp2f(x)` (checked in the assembly). So the C++
driver is compiled with the plan's flags plus `-fno-builtin` (`CODEGEN_EXTRA` in `cpp2lean.py`), and
`lean/lakefile.toml` passes the same flags to the C compiler of Lean (`moreLeancArgs`; Lean already
passes `-ffp-contract=off` itself). The reference build of the ArduPilot classes adds `-fno-builtin`
too (`ardupilot/vehicle/build.sh`); without it, any ArduPilot code that calls `powf`/`pow` with a
constant exponent is exposed to the same rewrite.
`-fno-builtin` does not reach calls written as `__builtin_powf`, which is how libc++'s float
overloads `std::pow(float, float)`, `std::sin(float)`, ... are implemented; see "Known gaps".

Further assumptions specific to the Lean side, all checked on this host (macOS arm64, Apple clang
17, Lean v4.33.0-rc1):

- Both executables run on the same machine with the same floating-point environment (round to
  nearest, no flush to zero) and link the same libm (the system `libSystem`).
- Out-of-range float to integer conversion is undefined in C++; Lean's `Float32.toInt32` etc.
  saturate (NaN gives 0). They agree on every in-range value (truncation toward zero).
- Integer division by zero and `INT_MIN / -1` are undefined in C++; Lean returns 0 / wraps.
- Conversions to a narrower signed type and right shifts of negative values are
  implementation-defined in C++17; clang wraps modulo 2^n and shifts arithmetically, as Lean does.
- Shift counts at or above the width are undefined in C++; Lean reduces them modulo the width.

Assumptions of the class translation (phase 2):

- A data member with no initializer starts at zero (the `State` field default is the zero of its
  type): ArduPilot zero-fills its objects, and the difftest's C++ objects have static storage, which
  C++ zero-initializes before construction. Reading such a member before writing it is otherwise
  undefined behavior.
- A conversion from an integer to an enum only produces enumerator values (`E.ofInt` maps any other
  value to the first enumerator).
- Objects of boundary classes do not change while a translated member function runs (each distinct
  read is one `Inputs` field), and translated code does not write them (non-const calls on them are
  rejected).

## The subset

Accepted in phase 1 (free functions over numbers):

- Declarations at file scope: function definitions (`static`/`inline` allowed; prototypes are
  skipped and calls through them resolve to the definition), `const`/`constexpr` scalars and
  arrays with an initializer (`def name : T := ...`), typedefs and `using` (types are resolved
  through them).
- Types: see the mapping table.
- Expressions: literals with the type clang assigned; variables; every `ImplicitCastExpr` and every
  explicit cast (C-style, `static_cast`, functional) as the named Lean conversion; `+ - * / %`;
  `< > <= >= == !=`; `&& || !` (short circuit, also when the right operand has side effects); `& | ^ ~
  << >>` on integers; `?:` (also with side effects in the branches); `=`, compound assignment,
  pre/post `++`/`--`, also nested inside expressions; calls to translated functions and to the
  `<cmath>` functions of the table; subscript of a constant array.
- Statements: declarations (`let` if never assigned again, `let mut` otherwise; several per
  `DeclStmt`; without initializer if a definite-assignment check proves every read is preceded by an
  assignment, emitted with a placeholder value and a comment), assignment, `if`/`else` (and
  `else if`), `return` anywhere, `break`, `continue`, blocks, empty statements; `for` and `while`
  with a constant trip count (below). Statements after a `return`/`break`/`continue` in the same
  block are unreachable and are not emitted.
- Loops: `for (T i = C0; i op C1; step)` with integer `T`, `op` one of `< <= > >= !=`, `step` one of
  `i++ ++i i-- --i i += C i -= C`, constants `C0 C1 C` (literals, `const`/`constexpr` integer
  variables, `+ - *` of those), and no assignment to `i` in the body: the translator computes the trip
  count N and emits `for i' in [C0:C0+N] do let i : T := Nat.toT i'` (or `[0:N]` with
  `i := C0 + C * i'` for other starts and steps; `for _ in [0:N]` if the body does not read `i`).
  `while (i op C1) { ...; step }` where `i` is declared earlier in the same block with a constant
  initializer, is not assigned between its declaration and the loop, is stepped only by the body's
  last statement, and the body has no `continue`: emitted as `for _ in [0:N] do` around the body,
  which keeps updating `i` as the C++ does.
- Every function body becomes `def f (params) : R := Id.run do ...`; a parameter that the body
  assigns is rebound with `let mut x := x`. A function must return on every path.

Accepted in phase 2 (classes; details under "Classes"):

- Structs and classes with data members, in the translated files, also nested in a class: a plain
  struct (no member functions, no base) is `structure Name`; a class is namespace `Name` with
  `structure Name.State`. Data members: the phase 1 types, nested structs and classes, fixed-size
  arrays (also mutable: element writes are `Array.set!`), enums, `bool` bit-fields of width 1 (as
  `Bool`), members of a `--param-class` type (in `Name.Params`), references to and objects of a
  `--boundary` class (not state). Default member initializers are the structure fields' defaults.
- Enums, scoped or not, also nested in a class: `inductive` with `deriving DecidableEq, Inhabited`,
  `E.toInt` (the enumerator values in the underlying type) and, when the C++ converts an integer to
  the enum, `E.ofInt`.
- `static const`/`constexpr` data members: `def`s in the class's namespace. `static` member
  functions: functions in the class's namespace.
- Member functions, const or not, defined in the class or out of line (in `--header` files and the
  main file); constructors with base and member initializers and a body; empty destructors (skipped).
- Single inheritance: base data members flattened into the derived `State` (base first); the base's
  member functions translated again in the derived class's namespace; a virtual call through `this`
  resolves to the most-derived override, a qualified call `Base::f()` to the base's version.
- Reference parameters: `const T&` by value; `T&` as an extra input and an extra component of the
  result, in parameter order (also for free functions, and `void` functions with reference
  parameters).
- Calls of member functions of the same object, of member objects (their state, parameters and
  inputs nest in the caller's), of local objects (without parameters or inputs), of static member
  functions; construction of local objects; copy assignment of structs.
- Reads from `--boundary` objects: data members, const member functions with constant arguments,
  also through a singleton accessor (`AP::ahrs().get_...()`); `--extern` functions.
- Statements and expressions: `switch` on an enum (`match`) or an integer (`if` chain), with cases
  that end in `break`/`return`/`continue` or share the next case's body, `default` anywhere;
  `do`/`while` with a constant trip count (same rules as `while`); the comma operator (left operand
  for its effects); default arguments (expanded at every call, and kept as Lean default values in
  the signature); overloaded names (suffixed by the parameter types: `scale_float`,
  `scale_float_int32_t`); `NAN`, `INFINITY`, `HUGE_VALF` and the double versions (the builtins
  `__builtin_nanf("")`, `__builtin_inff()`, ... become `Float32.ofBits 0x7fc00000`, `0x7f800000`,
  checked by the literal check); a `for` counter of a narrow type compared after promotion (a
  `uint8_t i < 12`), if the bound is a value of the counter's type.

Rejected with `file:line:col: rejected: <construct>` and exit status 2 (each line below is a
message the translator prints; phase 3 relaxes some of them, see "AP_Math and AP_Motors"): pointers
(`*`, `new`, `delete`, address-of, dereference, arrays used as pointers, array parameters, function
pointers); references other than parameters and boundary
members (reference members to translated classes, local references, functions returning a
reference); `volatile`; `char` types, string and character literals; `long double`; unions;
templates (class, function, member); `extern "C"` blocks and definitions inside namespaces;
mutable or non-constant globals and static data members, static local variables that are not
`const`; `mutable` members, bit-fields other than `bool`, members that hide a base member, anonymous
structs and enums; multiple and virtual inheritance; friends; conversion operators and overloaded
operators (on translated classes; `operator=` of structs is translated); delegating constructors;
destructors with a body; objects of abstract classes; recursion (direct, mutual, through member
functions; reported at the call that closes the cycle); member functions and `void` functions without
an observable effect (they write neither the object nor a reference parameter); variadic functions;
`main`; calls of library functions outside the `<cmath>` table and without `--extern`, of functions
without a definition in the translated files; non-const member functions of boundary objects and
calls on them with arguments that are not constants (outputs to the boundary); methods of a
parameter class other than `get`, `set`, the conversion and unary minus; local objects of classes
with parameters or boundary inputs; `for`, `while` and `do` loops without a constant trip count,
range `for`; `switch` cases that fall through into a non-empty case, `break` inside a case other
than as its last statement, `switch` with only `default`, ordering comparisons of enums; `goto` and
labels; `try`/`throw`; inline assembly; `sizeof`/`alignof`; lambdas; reads of a possibly
uninitialized variable; `if` with an initializer, `if constexpr`; identifiers named `decide`, `pure`,
`true`, `false`, `not`, `and`, `or`, `Id` (and `s`, `p`, `inp` in member functions); expression
statements without a side effect (including discarded results of calls without effects). Every node
kind without a handler is rejected with its kind named.

Lean-specific conventions: C++ identifiers are kept verbatim; identifiers that are Lean keywords are
written `«name»`. The translator's own names contain `'` (`i'` for loop indices, `t'1`, `t'2`, ... for
temporaries), which no C++ identifier contains. Lean block comments nest, so `/-` and `-/` inside
emitted comments (e.g. in a path) are written `/ -` and `- /`. Every `def` carries a doc comment
with the C++ declaration and its file and line range. A function in which a parameter or local is
never read in the Lean (e.g. a `const int N` used only as a loop bound, which the translator folds)
gets `set_option linter.unusedVariables false in`, with a comment naming the bindings. Emitted code
compiles without warnings, contains no `sorry`, `axiom` or `partial def`.

## Mapping, as implemented

Types:

| C++ (after typedefs) | Lean |
|---|---|
| `float` | `Float32` |
| `double` | `Float` |
| `bool` | `Bool` |
| `signed char`/`int8_t`, `short`/`int16_t`, `int`/`int32_t`, `long`, `long long`/`int64_t` | `Int8`, `Int16`, `Int32`, `Int64`, `Int64` |
| `unsigned char`/`uint8_t`, `unsigned short`/`uint16_t`, `unsigned`/`uint32_t`, `unsigned long`, `unsigned long long`/`uint64_t` | `UInt8`, `UInt16`, `UInt32`, `UInt64`, `UInt64` |
| `size_t`, `std::size_t` | `USize` |
| `T[N]` (constant at file scope; local or data member; full initializer list, or `= {}`/a zero filler) | `Array T` of N elements, read with `a[i.toNatClampNeg]!` (signed index) or `a[i.toNat]!` (unsigned), written with `a.set! i v`; a member without initializer is `Array.replicate N 0` |
| plain struct `S` (no member functions, no base) | `structure S` (nested in class `C`: `C.S`) |
| class `C` | `C.State`; with parameters also `C.Params`, with boundary reads `C.Inputs` |
| enum `E` (nested in `C`: `C.E`) | `inductive E`, `E.toInt : E → U` (U the underlying type: the fixed one, else `int`/`unsigned int` as clang chooses), `E.ofInt` |
| member of a `--param-class` type, e.g. `AP_Float` | a field of `C.Params` of the mapped scalar type |
| `bool x : 1` | `Bool` |

Literals: an integer literal is `(v : T)` with clang's value and type. A floating literal is `(text :
T)` with the decimal text of the source (suffix removed; `1.` -> `1.0`, `.5` -> `0.5`), or clang's
value text when the literal is spelled inside a macro (`FLT_EPSILON` -> `(1.1920929e-7 : Float32)`);
hexadecimal literals become `Float32.ofBits 0x...`/`Float.ofBits 0x...`. A `double` literal stays
`Float` and the cast clang inserted is emitted. The translator checks that the emitted decimal,
correctly rounded to the literal's type (Lean 4.33's `OfScientific Float32`/`Float` are correctly
rounded: exact fast path, otherwise the exact model), gives the bits of clang's value, and the
difftest checks every emitted literal in compiled Lean against clang's bits. Negative literals are
`-` applied to a literal, as in clang's AST.

Casts (`ImplicitCastExpr`, `CStyleCastExpr`, `CXXStaticCastExpr`, `CXXFunctionalCastExpr`; for an
explicit cast clang puts the conversion in an inner implicit cast):

| castKind | Lean |
|---|---|
| `LValueToRValue`, `NoOp` | nothing |
| `FloatingCast` float -> double / double -> float | `Float32.toFloat` / `Float.toFloat32` |
| `IntegralToFloating` | `IntN.toFloat32`, `UIntN.toFloat32`, `USize.toFloat32` (to float); `.toFloat` (to double); from `bool`: `if b then 1.0 else 0.0` |
| `FloatingToIntegral` | `Float32.toIntN`, `Float32.toUIntN`, `Float32.toUSize`, and the `Float.` ones |
| `IntegralCast` | same width: `IntN.toUIntN` / `UIntN.toIntN`; wider or narrower: `IntN.toIntM` / `UIntN.toUIntM` (sign extension, zero extension, truncation), followed by the signedness change when both differ; `USize` through `USize.toUInt64` / `UInt64.toUSize`; from `bool`: `if b then 1 else 0` |
| `IntegralToBoolean`, `FloatingToBoolean` | `x != 0` |
| `IntegralCast` from an enum / to an enum, `IntegralToFloating` from an enum | `E.toInt x`, then the integer conversion / the integer conversion, then `E.ofInt` |
| `UserDefinedConversion` (a parameter class's `operator const float &`) | the parameter's value `p.f` |
| `UncheckedDerivedToBase` (on `this` in a member call or member access) | nothing (the state is flattened) |
| anything else (`ArrayToPointerDecay` outside a subscript, pointer casts, `reinterpret_cast`, `const_cast`, ...) | rejected |

Every conversion that exists in core Lean 4.33 directly is used directly. Missing in core:
`Int32.toUInt8`, `UInt8.toInt32` and the other combined sign-and-width changes (composed from
two existing ones as above), `Int32.toNat` (the subscript uses `Int32.toNatClampNeg`).

Operators:

| C++ | Lean |
|---|---|
| `+ - * /` | `+ - * /` (the operand types are equal after clang's conversions) |
| `%` (integers) | `%` (`Int32` `%` is `BitVec.srem`, sign of the dividend, like C++; checked: `-7 % 2 = -1`, `7 % -2 = 1`) |
| `/` (integers) | `/` (`Int32` `/` truncates toward zero like C++; checked: `-7 / 2 = -3`, also `Int8`, `Int64`) |
| `== !=` | `== !=` (`BEq`: for `Float32`/`Float` this is IEEE equality) |
| `< <= > >=` | `< ≤ > ≥`, as a decidable proposition in an `if` or `?:` condition, else `decide (...)` |
| `&& \|\| !` | `&& \|\| !`; with side effects in the right operand: `let mut t := a; if t then (effects; t := b)` |
| `& \| ^ ~ << >>` | `&&& \|\|\| ^^^ ~~~ <<< >>>` (`>>>` on `IntN` is arithmetic; checked); the shift count is converted to the left operand's type |
| unary `-` | `-x`, which is `Float32.neg`/`Float.neg`, C negation (flips the sign bit: `-(0.0 : Float32)` prints `-0.000000`); never `0 - x` |
| `c ? a : b` | `if c then a else b`; with side effects in a branch: a `let mut` temporary assigned in an `if` statement |
| `x = e`, `x op= e`, `++x`, `x++` | `x := e`; `x := conv(conv(x, T->L) op e, R->T)` with clang's `computeLHSType` L and `computeResultType` R; `x := x + 1`; post-increment as a value: `let t := x; x := x + 1`, value `t` |

Do not use `≠` for floats: Lean 4.33 has `instDecidableEqFloat32`, a structural equality on the
model, so `decide ((0.0 : Float32) ≠ -0.0) = true` and `decide (NaN ≠ NaN) = false`, both the
opposite of C++ `!=`. The translator only emits `==`/`!=`.

Side effects are linearized in clang's evaluation order: operands left to right (the order clang
uses on this target; C++17 sequences the right operand of an assignment before the left). When a
later operand has side effects, the values of the earlier operands are first bound to temporaries,
so they are read before the effects happen.

`<cmath>` (the C name, or libc++'s overload of the unsuffixed name for `float`, or the `double`
function):

| C++ | Lean |
|---|---|
| `sinf cosf tanf asinf acosf atanf atan2f sqrtf fabsf expf logf powf floorf ceilf roundf log10f log2f exp2f sinhf coshf tanhf` | `Float32.sin cos tan asin acos atan atan2 sqrt abs exp log pow floor ceil round log10 log2 exp2 sinh cosh tanh` (core externs of the same libm functions) |
| `sin cos tan asin acos atan atan2 sqrt fabs exp log pow floor ceil round log10 log2 exp2 sinh cosh tanh` (double) | the same names under `Float.` |
| `fmaxf fminf fmax fmin` | `CppLibm.fmaxf fminf fmax fmin`: missing in core Lean 4.33 (core has `Min`/`Max` instances, which are `if a ≤ b then a else b` and differ from C on NaN and signed zero); `CppLibm.lean` declares them as `@[extern "fmaxf"] opaque ...`, the mechanism core uses for `Float32.sin` |
| `isnan isinf isfinite` (`std::` or not; libc++ `bool (float)`/`bool (double)`) | `Float32.isNaN isInf isFinite` / `Float.` |
| `abs(float)`, `abs(double)` | `Float32.abs` / `Float.abs` |

## Classes

A class becomes `Params`, `State`, `init` and one function per member function in the class's
namespace, with the C++ names and argument order. For a concrete class `C` (abstract classes are
emitted only through their derived classes):

- `structure C.Params`: the members of a `--param-class` type, of the mapped scalar type, and the
  `Params` of member objects that have them (`_pid_roll : PID.Params`). `structure C.State`: every
  other data member, base classes first, member objects as their own `State` or structure. Both
  `deriving Inhabited`; every field has a default (its member initializer, else zero), so `{}` is
  the zero-filled object. `structure C.Inputs`: one field per distinct read from a boundary object,
  in first-use order, named after the member function or data member read (`_ahrs.cos_yaw()` is
  `cos_yaw`; `_ahrs.yaw` is `yaw`; a call with constant arguments `get(2)` is `get_2`; on a clash
  with another object's read, prefixed by the object), and the `Inputs` of member objects that
  read the boundary (`_pid_roll : PID.Inputs`).
- A member function `f` becomes `def C.f [(p : Params)] [(s : State)] [(o : Outputs)] [(r' : Refs)]
  [(inp : Inputs)] args : R`, taking `p` if it (or a member function it calls) reads or writes a
  parameter, `s` likewise for the state, `o` if it writes boundary outputs, `r'` if it reads a
  `const` reference member (phase 3), `inp` if it reads the boundary; its result is the tuple of
  `Params` (if it writes one), `State` (if it writes the state), `Outputs` (if it writes one), the
  reference parameters in order, and the C++ result (omitted for `void`). A const member function therefore never returns `State`; `update_i (p : Params)
  (s : State) (dt : Float32) (limit : Bool) : State` and `get_i (s : State) : Float32` are AC_PID's
  shapes. In the body `this->x` is `s.x` (`p.x` for a parameter, `inp.x` for a boundary read), a write
  is `s := { s with x := e }` on `let mut s := s` (nested: `{ s with _flags._reset_filter := true }`,
  elements: `{ s with h := s.h.set! i v }`), and a call of another member function threads the
  components: `let (t'1, t'2) := update_all p s inp ...; s := t'1`.
- Constructors: `def C.init args : State` (or `Params × State`), starting from `{}`, then the base
  constructor, the member initializers in declaration order (a member object's constructor is its
  class's `init`; a member initializer that is the default member initializer is the field's
  default), then the body. Overloaded constructors are suffixed (`init_float`); if the class has a
  member function named `init`, the constructors are `construct`. A boundary reference passed to
  the constructor is not a Lean parameter.
- Inheritance: for `Tile : Shape`, namespace `Tile` has every member function of `Shape` translated
  against `Tile.State`, under its own name, except that a base version that `Tile` overrides or
  hides is `Tile.Shape.area` (its doc comment says it is a member of `Shape` translated for `Tile`);
  `Shape`'s constructor is `Tile.Shape.init (s : State) ...`, called by `Tile.init`. A virtual call
  through `this` in any of these resolves to `Tile`'s final overrider, so `Shape::scale_report`'s
  call of `area()` is `Tile.area` in `Tile` and `Shape.area` in `Shape`. Calls through pointers or
  references to a base class, where the target would depend on the dynamic type, cannot occur:
  pointers are rejected and references are only boundary objects. Member objects have their static
  type, so their virtual calls resolve to that type's final overrider.
- The boundary (`--boundary`): a member of a boundary class (usually a reference, ArduPilot's
  `AP_AHRS_View &_ahrs`, `AP_Motors &_motors`) or a free function returning a reference to one (the
  singleton accessors `AP::ahrs()`) is not state. Every data member read, and every call of a const
  member function with constant arguments, on such an object is a field of `C.Inputs`, named as the
  C++ names the read: AC_PosControl's reads `_ahrs.cos_yaw()`, `_ahrs.yaw`, `_ahrs.get_accel_ef()`,
  `AP::ahrs().get_control_gain_scaler_XY()` are the fields `cos_yaw`, `yaw`, `get_accel_ef`,
  `get_control_gain_scaler_XY`, with the names of the stub headers `ardupilot/stubs/AP_AHRS/AP_AHRS_View.h`
  and `AP_AHRS.h`, which are the names of the real headers. The caller fills them (the difftest from
  the line, the composition from the other translations' state). A const member function
  with reference parameters (`bool get_lean_max(float &out) const`) is also an input: each reference
  parameter is an `Inputs` field `get_lean_max_out`, assigned to the argument (a variable, member or
  element), and a non-`void` result is the field `get_lean_max`; its other arguments must be
  constants. Calls with variable arguments of const member functions are rejected.
- Outputs to the boundary (phase 3): a non-const `void` member function called on a boundary object
  (`_motors.set_roll(v)`, `_motors.set_throttle_out(thr, boost, 2.0f)`) writes `structure C.Outputs`:
  one field per parameter (`set_roll`; with several parameters `set_throttle_out_throttle`,
  `set_throttle_out_apply_angle_boost`, ...), assigned in program order, so the record holds the
  last call's arguments (last write wins); member objects that write outputs nest (`_mixer :
  Mixer.Outputs`). A member function that writes outputs takes `(o : Outputs)` after `s` and returns
  `Outputs` after `State`: `def run (s : State) (o : Outputs) (inp : Inputs) ... : State × Outputs`.
  Rejected: non-const boundary calls with a result or with reference parameters, without arguments,
  in a constructor, and through a member object that is not a direct member. The record does not
  say whether or how often a function was called in a step; a consumer that needs that (or that
  combines two classes writing the same boundary function) must read it from the call sequence.
  `examples/motors.cpp` covers each case.
- Free functions called from a class are written with the file's namespace (`Pid.is_positive`).

## ArduPilot (phase 3)

`ardupilot/translate_ac_pid.sh` translates ArduPilot's AC_PID family (`AC_PID`, `AC_P`, `AC_P_1D`,
`AC_PID_Basic`, `AC_PID_2D`, `AC_P_2D`, `AP_PIDInfo`) into `ardupilot/out/AC_PID/AC_PID_lib.lean`
(1829 lines, no rejections), with the dialect flags and defines of the reference build (the waf SITL configuration:
`-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math`, `-DAP_FILTER_ENABLED=0`,
`-D__AP_LINE__=__LINE__`, ..., `-include ap_config.h`) and the stub headers (`-I ardupilot/stubs`). Since clang's JSON dump holds the definitions of one translation unit, the script
translates `ardupilot/unity_ac_pid.cpp`, which `#include`s the six `.cpp` files and the library
sources they call (`Filter/SlewLimiter.cpp`, `Filter/LowPassFilter.cpp`, `AP_Math/AP_Math.cpp`,
`control.cpp`, `vector2.cpp`); `--header` selects the AC_PID files as the translated ones and
`--lib-dir` makes `AP_Math/` and `Filter/` libraries. Constructs added for it:

- `--ap-param`. A member of type `AP_ParamT<T, ...>` (`AP_Float`, `AP_Int8`, ...) is a parameter
  (no `--param-class` needed); `get()`, the conversion and unary minus read it, `set(v)` (and
  `set_and_save`, `set_and_save_ifchanged`, `set_and_notify`) write it, `save()`, `load()`,
  `notify()` are left out (`pure ()` with a comment: parameter storage is outside the model).
  `static const AP_Param::GroupInfo var_info[]` is not translated as data; the translator keeps
  the table, and `AP_Param::setup_object_defaults(this, var_info)` in a constructor becomes, entry by
  entry in table order, the write of each parameter's default: the pointed-to member for
  `AP_GROUPINFO_FLAGS_DEFAULT_POINTER` (`_kp := s.default_kp`), the constant for `AP_GROUPINFO`
  (`_kpdmax := 0`), as `AP_Param::setup_object_defaults` does (`ardupilot/stubs/oracle_env.cpp` holds a verbatim copy); nested groups are skipped, as there.
- Library translation on demand (`--lib-dir`). Functions, classes and class template
  specializations from the library directories are translated when a translated file uses them, and
  only then (rejections inside them are reported as for any other code). Template specializations
  are named by their namespace-scope typedef where there is one (`LowPassFilter<float>` is
  `LowPassFilterFloat`, `Vector2<float>` is `Vector2f`, `Vector2<double>` is `Vector2_double`), and
  function templates by their instantiation (`is_zero<float>` is `is_zero_float`,
  `constrain_value_line<float>` is `constrain_value_line_float`). A member object of a translated
  class (`SlewLimiter _slew_limiter`, `LowPassFilterFloat`) nests like any member object, and its
  non-const member functions thread its state: `let (t'1, t'2) := SlewLimiter.modifier
  s._slew_limiter {...} inp._slew_limiter x dt; s := { s with _slew_limiter := t'1 }`.
- `const` reference members (`SlewLimiter`'s `const float &slew_rate_max`): `structure C.Refs`, one
  field per reference member; the member functions that read them take `(r' : Refs)`, and the owner
  passes the values its constructor bound them to (`{ slew_rate_max := p._slew_rate_max, ... }`). The
  bound value must be a constructor parameter of the class, itself bound by the owner to its own
  member; a reference member to a class that is neither a boundary class nor a number (a
  back-reference such as `AP_Motors &motors` in `Thrust_Linearization`) is rejected with a message
  saying so (`tests/reject_phase3.cpp`).
- Constructors: delegating constructors (`AC_PID(const Defaults &) : AC_PID(defaults.p, ...)`)
  call the target's `init`; overloads are suffixed by parameter types (`init_float11`,
  `init_Defaults`); default arguments are Lean default arguments; `Defaults` is a structure like any
  plain struct (its fields default to 0, as C++ value-initialization).
- Accessors returning references (`AP_Float &kP()`, `const AP_PIDInfo &get_pid_info() const`) are
  value functions (`kP (p : Params) : Float32`); a const and a non-const overload that return the
  same member are one function. A call through the returned reference (`kP().set(x)`) is rejected.
- Operators on translated classes (`Vector2f`, for `AC_PID_2D`, `AC_P_2D`): `operator+` is
  `Vector2f.op_add`, overloads suffixed by operand type (`op_mul_float`, `op_mul_Vector2f`),
  compound assignment `op_add_assign` returns the new left operand; calls on temporaries
  (`(a - b).length()`) pass the temporary's state and discard what it writes.
- `--boundary-fn AP_HAL::millis` (an `Inputs` field `millis`, read where `SlewLimiter::modifier`
  calls it; `AC_PID.Inputs` holds it as `_slew_limiter.millis`) and `--drop AP_InternalError::error`
  (the `INTERNAL_ERROR` macro in `constrain_value_line` and `calc_lowpass_alpha_dt`).
- Smaller: `memset(&x, 0, sizeof(x))` (the zero value of `x`'s type), `T()` value-initialization,
  `*this`, `isgreater`/`isgreaterequal`/`isless`/`islessequal` (as `>`/`≥`/`<`/`≤`, which agree on
  every value including NaN since nothing observes the floating-point exception flags), `auto f() ->
  decltype(...)` return types (`MIN`), and member functions without effect in the model (they write
  neither state, parameters, outputs nor a reference parameter: `load_gains`, `save_gains`, the
  empty `set_notch_sample_rate`), listed as "Not emitted" at the end of the class's namespace.

The differential test `python3 difftest.py ardupilot/AC_PID` (configuration `ardupilot/AC_PID.json`)
runs the translation, compiles the real ArduPilot sources (`AC_PID/*.cpp`, `Filter/SlewLimiter.cpp`,
`Filter/LowPassFilter.cpp`, `AP_Math/AP_Math.cpp`, `control.cpp`, `vector2.cpp`, `vector3.cpp`,
`AP_Param/AP_ParamT.cpp`) with the reference flags (`-O2 -ffp-contract=off -fno-fast-math
-cl-single-precision-constant -fno-builtin ...`, the stubs), and links them with
`ardupilot/ac_pid_env.cpp` (`AP_HAL::millis` returning the driver's `cpp2lean_millis`, and the
`AP_InternalError` and `AP_Param` functions copied from `ardupilot/stubs/oracle_env.cpp`, with
`AP_Param::load` returning false). `AC_PID` is constructed with Copter's roll-rate defaults
(`0.135, 0.135, 0.0036, 0.1, 0.5, 5, 10, 20, 0, 1, 0.002`) and driven through every public member
function: `update_all`, `update_error`, `update_i` (private, listed in `extra_methods`), the getters,
`reset_I`, `reset_filter`, every setter, `set_integrator`, `relax_integrator`,
`set_slew_limit_scale`, `get_pid_info`, with `dt` in [0.001, 0.01], targets, measurements and errors in
[-3, 3], random `limit` flags, `millis` increasing by 0 to 12 ms per call, and the corner values of
every argument. The other five classes are driven the same way. Result (seed 20261104):

```
ardupilot/AC_PID AC_PID: 21048 calls on one object (20000 random, 1048 corner) over 45 member functions, 62 state leaves per line; inputs: _slew_limiter.millis
ardupilot/AC_PID AC_PID: 0 of 21049 lines differ (48 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P: 20040 calls on one object (20000 random, 40 corner) over 3 member functions, 2 state leaves per line; inputs: none
ardupilot/AC_PID AC_P: 0 of 20041 lines differ (6 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P_1D: 20180 calls on one object (20000 random, 180 corner) over 8 member functions, 6 state leaves per line; inputs: none
ardupilot/AC_PID AC_P_1D: 0 of 20181 lines differ (10 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_PID_Basic: 20450 calls on one object (20000 random, 450 corner) over 30 member functions, 33 state leaves per line; inputs: none
ardupilot/AC_PID AC_PID_Basic: 0 of 20451 lines differ (1388 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_PID_2D: 20880 calls on one object (20000 random, 880 corner) over 32 member functions, 51 state leaves per line; inputs: none
ardupilot/AC_PID AC_PID_2D: 0 of 20881 lines differ (2946 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P_2D: 20180 calls on one object (20000 random, 180 corner) over 7 member functions, 6 state leaves per line; inputs: none
ardupilot/AC_PID AC_P_2D: 0 of 20181 lines differ (13 tokens equal only as NaN vs NaN with different bits)
```

The slew limiter is exercised: `Dmod` is not 1 on most `update_all` lines (the random calls of
`set_slew_limit` make `SMAX` positive), and changing `MODIFIER_GAIN` (`SlewLimiter.cpp:30`) from 1.5
to 1.6 on one side makes 20015 of 21039 lines differ. `ardupilot/AC_PID_faithful.json` drives `AC_PID`
with Copter's roll-rate gains and the slew limiter and PD limit left inactive.

### AP_Math and AP_Motors (phase 3, second part)

`ardupilot/translate_ap_math.sh` translates the AP_Math functions and classes the control classes use into
`ardupilot/out/AP_Math/AP_Math_lib.lean` (1656 lines): the functions and members listed in
`ardupilot/AP_Math.use` (scalar helpers of `AP_Math.h`/`AP_Math.cpp`, every `control.cpp` function,
the `location.cpp` distance and bearings, `Vector2`/`Vector3` at `float` and `double`, `Matrix3<float>`
times a vector, `QuaternionT<float>`) and what they call, from `ardupilot/unity_ap_math.cpp`.
Template specializations are named after their typedef, `--type-name` choosing where there are several
(`Vector2<double>` is `Vector2p`, `Vector3<double>` is `Vector3p`, as in `control.h` and the hand
port; `QuaternionT<float>` is `Quaternion`). `ardupilot/translate_ap_motors.sh` translates
`AP_Motors`, `AP_MotorsMulticopter`, `AP_MotorsMatrix` and `Thrust_Linearization` (with
`LowPassFilterFloat`, `DerivativeFilterFloat_Size7` and the AP_Math functions they use) into
`ardupilot/out/AP_Motors/AP_Motors_lib.lean` (2852 lines) from `ardupilot/unity_ap_motors.cpp`. Both
use `--nest`, so that the two translations can live in one Lean package. Both scripts first run
`ardupilot/check_unity.py`, which checks that every translated file preprocesses in the unity file
exactly as in its own translation unit: in a unity file, macros defined by an earlier `.cpp` stay
defined for the later ones, and `SRV_Channel.h` defines `AP_BATTERY_ENABLED`, which no header of
`AP_Motors_Thrust_Linearization.cpp` defines with the stub headers (the battery code is therefore
compiled out of it in its own translation unit);
`unity_ap_motors.cpp` includes that file first.

What clang's AST says about the quaternion half-angle trig: `-cl-single-precision-constant` does
not apply inside templates, so in `QuaternionT<float>::from_axis_angle` and `from_euler` the literal
`0.5` is a `double`, `sinF(0.5*theta)` is `(float)sin(0.5 * (double)theta)` (the `double` `sin`), and
the translation is `Float.toFloat32 (Float.sin ((0.5 : Float) * Float32.toFloat theta))`.

Constructs added for AP_Math (each covered by `examples/frame.cpp` or the ArduPilot goldens, and by
`tests/reject_phase3b.cpp` for its limits):

- `--use` (library functions translated without a translated caller), `--nest`, `--type-name`.
- Overloaded operators on class templates at both instantiations, non-const member operators
  writing their first operand (`op_add_assign`), `*this` as an object and as the target of a
  compound assignment (`*this /= length()`).
- `xy()` (`*(const Vector2<T> *)this`, a layout-prefix view) read as the value `{ x := s.x, y := s.y }`
  (written through since the third part, "AC_AttitudeControl and AC_PosControl");
  `operator[]` with a constant index read as the field (`v[0]` is `s.x`). A non-const call on an
  object returned by reference is rejected (`tests/reject_phase3b.cpp:36`), unless the reference is
  a data member or a view of this object (the third part).
- Variadic templates at their instantiation (`norm<double, double, double>` is `norm_double3`, the
  pack parameters named `v'1`, `v'2`), `std::enable_if` return types (`is_equal`), `constexpr`
  values from the library (`std::is_same<...>::value`, `std::numeric_limits<float>::epsilon()`),
  non-type template arguments printed as characters (`DerivativeFilter<float, '\a'>`).
- `fmodf`/`fmod` (`CppLibm.fmodf`, `@[extern "fmodf"]`), and libc++'s mixed `float`/`double`
  overloads (`std::sin(double)` of a `float`-times-`double` argument), whose arguments are converted
  to `double` as in the AST.

Constructs added for AP_Motors:

- `--drop` of data members and member functions: the singleton pointers and `get_singleton`, the
  function-pointer member `_thrust_compensation_callback` with its setter and its only reader
  `AP_MotorsMatrix::thrust_compensation`, the `char *` frame string `custom_frame_string` and the
  functions that format text into `char *` buffers (`get_frame_string`, `arming_checks`), the
  logging functions. Statements that only touch dropped members (`_singleton = this`, `if
  (_singleton != nullptr) AP_HAL::panic(...)`) are left out with a comment in the Lean; any other
  read of a dropped member is rejected (`tests/reject_phase3b.cpp:83`).
- Owner back-references (`Thrust_Linearization`'s `AP_Motors &motors`, constructed as `thr_lin{*this}`):
  a member function of the nested class that reads the owner's members takes `(own : Owner)`, a
  structure of the members it reads, and the owning class builds it with a generated
  `owner_thr_lin (p : Params) (s : State)`. Reading the owner's members is all the nested class may do
  with the reference; a call through it is rejected (`tests/reject_phase3b.cpp:62`).
- Boundary as an output log (`--output-log`): the calls to the boundary are kept in order,
  `Outputs := Array Output` with an `inductive Output` constructor per boundary function
  (`Output.rc_write (chan : UInt8) (pwm : UInt16)`), and a member function returns the events it
  produced. Assignments to members of boundary objects (`AP_Notify::flags.armed = true`) are events
  too. Boundary objects reached through `extern const AP_HAL::HAL &hal` (`hal.rcout->...`), static
  member functions of boundary classes (`SRV_Channels::set_output_scaled`), local references
  (`AP_BattMonitor &battery = AP::battery()`) and boundary reference parameters are accepted.
- `--boundary-call AP_Motors::rc_write` (and `rc_write_angle`, `rc_set_freq`, `add_motor_num`,
  `motor_mask_to_srv_channel_mask`): members of a translated class whose bodies are HAL calls; not
  translated, a call is an output event or an input.
- `--site-inputs`: a const boundary call with non-constant arguments outside loops
  (`SRV_Channels::get_output_channel_mask(SRV_Channel::k_boost_throttle)`) is an input per call site.
- `--array-params`: `add_motors(const MotorDef *motors, uint8_t num_motors)` reads its pointer only
  by subscript, so it is the `Array MotorDef` the caller passes; `static const MotorDef motors[] =
  {...}` tables are `let motors : Array MotorDef := #[...]`, and `ARRAY_SIZE(motors)` is the
  constant.
- `const char *` members and locals assigned string literals (`_frame_class_string = "QUAD"`) are
  `String`; any other use of a `char *` is rejected.
- Parameters: `AP_Enum<PWMType>` and `AP_Enum16` (enum-typed parameters), comparisons and arithmetic
  between parameters, `set_default` (written when the parameter is not configured: an input
  `<parameter>_configured`), `configured()`, `set_and_default`, through accessors (`kP().set_default(x)`)
  and through members (`thr_lin.lin.expo.set_default(...)`).
- Statements: `for` loops with a counter declared before the loop, loops bounded by an `unsigned`
  argument that the body does not assign (`for (uint8_t i = 0; i < num_motors; i++)`, as
  `for i' in [0:num_motors.toNat]`), counters stepped by a constant (`i += 2`), `switch` cases that
  exit early (`case X: if (c) { ...; break; } ...; break;`), `const auto &` locals bound to members,
  anonymous struct members (`AP_Motors::limit`, as `AP_Motors.AP_Motors_limit.State`), typedef'd
  anonymous enums (`SRV_Channel::Function`), `friend class`.

Differential tests (seed 20261104; `python3 difftest.py ardupilot/AP_Math ardupilot/AP_Motors`):

```
ardupilot/AP_Math free functions: 24490 calls (20000 random, 4490 corner) over 63 functions
ardupilot/AP_Math free functions: 0 of 24491 lines differ (391 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<float>: 21420 calls on one object (20000 random, 1420 corner) over 25 member functions, 2 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector2<float>: 0 of 21421 lines differ (366 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<double>: 21260 calls on one object (20000 random, 1260 corner) over 22 member functions, 2 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector2<double>: 0 of 21261 lines differ (326 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<float>: 22320 calls on one object (20000 random, 2320 corner) over 27 member functions, 3 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector3<float>: 0 of 22321 lines differ (663 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<double>: 21820 calls on one object (20000 random, 1820 corner) over 22 member functions, 3 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector3<double>: 0 of 21821 lines differ (522 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Matrix3<float>: 20240 calls on one object (20000 random, 240 corner) over 1 member functions, 9 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Matrix3<float>: 0 of 20241 lines differ (81 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math QuaternionT<float>: 23040 calls on one object (20000 random, 3040 corner) over 26 member functions, 4 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math QuaternionT<float>: 0 of 23041 lines differ (1084 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (linear): 24710 calls on one object (20000 random, 4710 corner) over 126 member functions, 396 state leaves per line; inputs: micros, have_digital_outputs, get_output_channel_mask_k_boost_throttle, _pwm_min_configured, _pwm_max_configured, motor_mask_to_srv_channel_mask, thr_lin.get_air_density_ratio
ardupilot/AP_Motors AP_MotorsMatrix (linear): 0 of 24711 lines differ (71 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (defaults): 24710 calls on one object (20000 random, 4710 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (defaults): 0 of 24711 lines differ (65 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (frames): 25869 calls on one object (20000 random, 5869 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (frames): 0 of 25870 lines differ (1250 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (spool): 25905 calls on one object (20000 random, 5905 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (spool): 0 of 25906 lines differ (64 tokens equal only as NaN vs NaN with different bits)
```

AP_Math: every translated free function is driven by the free-function harness (random and corner
arguments, angles and unit vectors among them); each class line sets the object from the line
(`state_from_line`) and calls one member function, quaternions being random unit quaternions on 70%
of the lines. AP_Motors (`ardupilot/AP_Motors.json`): an `AP_MotorsMatrix` constructed with 400 Hz,
`init(QUAD, X)`, armed, interlocked, spooled up to THROTTLE_UNLIMITED by 400 calls of `output` and
then driven through every public member function and the `thr_lin` ones; `linear` sets `MOT_THST_EXPO
0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.4444`, `defaults` keeps
every default; both hold the arming state and leave out the calls that change the frame. `frames`
also re-initializes through every frame class and type, and `spool` drives arming, interlock and the
spool request freely. Each output line holds all 396 leaves of `Params` and `State` and the HAL
calls of the call (`rc_write` per motor in order, `set_output_scaled`, `rc_set_freq`, ...). The
undefined behavior of the C++ (motor indices outside the arrays, negative `MOT_PWM_MIN`/`MAX`
converted to `uint16_t`, actuator values outside [0, 1] in `output_to_pwm`) is kept out by `domains`.
As checks that the harness sees a wrong translation: single-precision trig in `from_axis_angle` and
`from_euler` makes 285 of 23041 quaternion lines differ (first at line 53, `q1` 0x3f6ad74d vs
0x3f6ad74c); a change in `sqrt_controller` makes 377 free-function lines differ; yaw headroom
0.001 changed to 0.0011 makes 22308 of 24494 `linear` lines differ; `rc_write` events in reverse order
make 1486 lines differ, the first at line 9. Seeds 7 and 8 give 0 differing lines as well.

### AC_AttitudeControl and AC_PosControl (phase 3, third part)

`ardupilot/translate_ac_attitude.sh` translates `AC_AttitudeControl` and `AC_AttitudeControl_Multi`
(with `AC_PID`, `AC_P`, `SlewLimiter`, `LowPassFilterFloat` and the AP_Math functions and classes they
use) into `ardupilot/out/AC_Attitude/AC_Attitude_lib.lean` (2939 lines) from
`ardupilot/unity_ac_attitude.cpp`; `ardupilot/translate_ac_poscontrol.sh` translates `AC_PosControl`
(with `AC_P_1D`, `AC_P_2D`, `AC_PID_2D`, `AC_PID_Basic`, `AC_PID`) into
`ardupilot/out/AC_PosControl/AC_PosControl_lib.lean` (3558 lines). Both from the unmodified sources,
with the reference flags and the stub headers, `--nest`, no rejection; both scripts check their unity files with
`check_unity.py`. `AC_AttitudeControl` is abstract (its rate PIDs are reached through pure virtual
accessors), so it is translated as the base of `AC_AttitudeControl_Multi`, in that class's namespace.

**The boundary.** The objects these classes hold references to are not nested translated objects:
the motors, the AHRS view and the attitude controller are shared by several classes and by the
vehicle (one `AP_MotorsMatrix` is written by the attitude controller and read by the position
controller and the vehicle's loop), so each class sees them as its boundary, and the caller (the
vehicle's loop: `ardupilot/compose/Compose.lean`, `lean/Vehicle.lean`) connects the translations per
tick.
- AC_AttitudeControl(_Multi): `--boundary AP_AHRS_View,AP_Motors,AP_MotorsMulticopter,AP_Scheduler,AP_HAL::HAL`.
  What it reads (the view's quaternion, yaw, `cos_pitch`, `cos_roll`, gyro; the motors' hover
  throttle, throttle, throttle out, thrust maximum, slew rate and `limit` flags; the scheduler's loop
  time; `AP_HAL::micros64`, `AP_HAL::millis`) is `Inputs` (23 fields); what it writes into the motors
  (`set_roll`, `set_roll_ff`, ..., `set_throttle`, `set_throttle_avg_max`, `set_throttle_filter_cutoff`)
  is `Outputs`, the last argument of each setter. Each setter is called at most once per member
  function, and stores its argument or a function of it, so the caller can write every output back
  through the motors' setters after each call.
- AC_PosControl: `--boundary AP_AHRS_View,AP_AHRS,AP_Motors,AC_AttitudeControl,AP_Scheduler,AP_HAL::HAL`.
  What it reads from the AHRS, the motors, the attitude controller's getters, the scheduler's tick
  counter and the clock is `Inputs` (40 fields); its one call into the attitude controller,
  `set_throttle_out`, is an `Output` event (`--output-log`), which the caller makes on the attitude
  controller in order.

Constructs added (each covered by `examples/control.cpp` or the ArduPilot goldens, and by
`tests/reject_phase3c.cpp` for its limits):

- Accessors returning a reference to a data member, resolved through virtual dispatch: a call without
  arguments, on this object or a member object, of a member function that returns a reference and
  whose final overrider's body is `return m;` is the member `m` itself, so `get_rate_roll_pid().reset_I()`
  (`AC_AttitudeControl.cpp:275`, the pure virtual accessor overridden by `return _pid_rate_roll;`) is a
  call on `_pid_rate_roll`, `get_rate_yaw_pid().kP()` a read of its parameter and
  `get_pid_info().slew_rate` a read of the field. (Fixed with it: a merged const/non-const accessor
  pair is now dispatched too.)
- Writes through a layout-prefix view: `Vector2<T> &xy() { return *(Vector2<T> *)this; }` is a path
  step, read as `({ x := s.p.x, y := s.p.y } : Vector2p.State)` and written field by field
  (`s := { s with p.x := t'1.x, p.y := t'1.y }`, the value bound to a temporary first): assignment
  (`_pos_target_ned_m.xy() = ...`), non-const calls (`_vel_desired_ned_ms.xy().zero()`), operators
  (`xy() *= ...`), reference arguments (`update_pos_vel_accel_xy(_pos_desired_ned_m.xy(), ...)`).
- `static constexpr` members of a class type defined out of line (`VECTORF_111`,
  `AC_AttitudeControl.h:549`, `.cpp:208`); member initializers that bind a temporary to a const
  reference parameter (`_p_angle_roll(AC_ATTITUDE_CONTROL_ANGLE_P)` into `AC_P(const float &)`).
- `AP_NESTEDGROUPINFO` in a `var_info` table (at offset 0) is skipped by `setup_object_defaults`, as
  the other nested groups; before, it ended the table.
- `--boundary-query Class::member`: a non-const getter of a boundary class is an input
  (`AC_AttitudeControl::get_bf_feedforward`, `AP_AHRS_View::get_position_NE_reset_count`).
- A local `const T &` bound to the result of a const call on a boundary object is a copy (the boundary
  does not change while a member function runs); a member of a value (a boundary read or a call's
  result: `_ahrs.get_accel_ef().z`, `pos.topostype().z`) is read from the value.
- Inputs that are data members of a member of the boundary object are named with it:
  `_motors.limit.roll` is `limit_roll` (other inputs keep their names).

Differential tests (seed 20261104; `python3 difftest.py ardupilot/AC_Attitude ardupilot/AC_PosControl`):

```
ardupilot/AC_Attitude AC_AttitudeControl_Multi (defaults): 36690 calls on one object (20000 random, 16690 corner) over 124 member functions, 275 state leaves per line; inputs: get_quat_body_to_ned_q.q1, get_quat_body_to_ned_q.q2, get_quat_body_to_ned_q.q3, get_quat_body_to_ned_q.q4, yaw, get_filtered_loop_time, get_throttle_hover, get_throttle_thrust_max, cos_pitch, cos_roll, get_throttle_slew_rate, get_throttle, get_throttle_out, micros64, limit_roll, limit_pitch, limit_yaw, get_gyro_latest.x, get_gyro_latest.y, get_gyro_latest.z, _pid_rate_roll._slew_limiter.millis, _pid_rate_pitch._slew_limiter.millis, _pid_rate_yaw._slew_limiter.millis; outputs: set_throttle_filter_cutoff, set_throttle, set_throttle_avg_max, set_roll, set_roll_ff, set_pitch, set_pitch_ff, set_yaw, set_yaw_ff
ardupilot/AC_Attitude AC_AttitudeControl_Multi (defaults): 0 of 36691 lines differ (383364 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_Attitude AC_AttitudeControl_Multi (tuned): 36690 calls on one object (20000 random, 16690 corner) over 124 member functions, 275 state leaves per line; inputs: (as above)
ardupilot/AC_Attitude AC_AttitudeControl_Multi (tuned): 0 of 36691 lines differ (383364 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PosControl AC_PosControl (defaults): 40205 calls on one object (20000 random, 20205 corner) over 144 member functions, 237 state leaves per line; inputs: get_relative_position_NED_origin_vec.x, get_relative_position_NED_origin_vec.y, get_relative_position_NED_origin_vec.z, get_relative_position_NED_origin, get_relative_position_D_origin_float_posD, get_relative_position_D_origin_float, get_velocity_NED_vec.x, get_velocity_NED_vec.y, get_velocity_NED_vec.z, get_velocity_NED, get_vert_pos_rate_D_velocity, get_vert_pos_rate_D, get_ang_vel_roll_max_rads, get_ang_vel_pitch_max_rads, get_accel_roll_max_radss, get_accel_pitch_max_radss, get_bf_feedforward, millis, get_att_target_euler_rad.x, get_att_target_euler_rad.y, get_att_target_euler_rad.z, ticks32, yaw, get_althold_lean_angle_max_rad, lean_angle_max_rad, get_position_NE_reset_count, has_good_timing, get_control_gain_scaler_XY, cos_yaw, sin_yaw, get_accel_ef.x, get_accel_ef.y, get_accel_ef.z, get_throttle_in, get_throttle_hover, get_position_D_reset_count, get_control_gain_scaler_Z, limit_throttle_lower, limit_throttle_upper, _pid_accel_d_m._slew_limiter.millis
ardupilot/AC_PosControl AC_PosControl (defaults): 0 of 40206 lines differ (361950 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PosControl AC_PosControl (tuned): 40205 calls on one object (20000 random, 20205 corner) over 144 member functions, 237 state leaves per line; inputs: (as above)
ardupilot/AC_PosControl AC_PosControl (tuned): 0 of 40206 lines differ (361950 tokens equal only as NaN vs NaN with different bits)
```

`ardupilot/AC_Attitude.json`: an `AC_AttitudeControl_Multi` constructed on the AHRS view
stub and a real `AP_MotorsMatrix` (both static, zero-filled), set up with `set_dt_s(0.0025)`,
`relax_attitude_controllers()`, `set_throttle_out(0.4444, true, 2)`, then driven through every public
member function and five protected ones, weighted to the per-tick entry points (`rate_controller_run`,
`input_thrust_vector_heading` with every heading mode, `set_throttle_out`, `input_quaternion`, the
`input_euler_*` variants, `get_throttle_boosted`, `update_althold_lean_angle_max`), with plausible
values on 99.5% of the draws: unit quaternions (98% of the AHRS quaternions, 90% of quaternion
arguments), roll and pitch within ±60 degrees, yaw and headings within ±180, rates within ±5 rad/s,
`dt` in [0.0025, 0.004], the thrust vector a lean acceleration with `z` in [-12, -7]; the rest from
the free-function mixture, and the corner values of every argument and of every input of the member
functions that read inputs (`input_corners: readers`). The motors' getters are made to return the
line's value by writing the motors object (`_throttle_hover.set(v)`, `_throttle_filter.reset(v)`), on
the values they can return (`input_domains`: `get_throttle_hover()` is `constrain_float(_throttle_hover,
0.125, 0.6875)`); what the controller writes into the motors is read back from it (`_roll_in`, ...,
`_throttle_filter.get_cutoff_freq()`), and for `set_throttle_avg_max`, which stores
`constrain_float(x, 0, 1)`, the Lean side prints the AP_Motors translation's setter applied to its
output (`lean_outputs`, `lean_imports`). `defaults` keeps the code defaults, `tuned` sets
`sim/params/copter-cf2x-tuned.txt` (`ATC_INPUT_TC 0.05`, `ATC_ACC_R_MAX`/`ATC_ACC_P_MAX 1800`,
`ATC_ANG_RLL_P`/`ATC_ANG_PIT_P 9`) and SITL's `ATC_RAT_YAW_P 0.3`, `ATC_RAT_YAW_I 0.02` (`copter.parm`).
`ardupilot/AC_PosControl.json`: an `AC_PosControl` on the view stub, a real `AP_MotorsMatrix` and a
stand-in attitude controller (`ardupilot/standin/AC_AttitudeControl/AC_AttitudeControl.h`, with the
signatures of the real header, returning the line's values and recording `set_throttle_out` in the
output log; the real getters compute their values from parameters, `radians(_ang_vel_roll_max_degs)`,
which cannot produce every value). Since `AC_PosControl.h` includes `"AC_AttitudeControl.h"` from its
own directory, the stand-in is put in its place by clang's `-ivfsoverlay` (`cxx_overlay`); only the C++
side of the difftest sees it, the translation reads the real header. Set up with the calls of
`AC_WPNav::wp_and_spline_init_m`, driven through every public member function and fifteen protected
ones, weighted to `NE_update_controller`, `D_update_controller`, `set_pos_vel_accel_NED_m`,
`update_estimates`; positions within ±10 m, velocities within ±5 m/s, accelerations within ±5 m/s²,
the AHRS stub's constant answers (every estimate valid, gain scalers 1, reset counts 0) as constant
inputs, the tick counter and the clock increasing. `tuned` sets `PSC_NE_POS_P 1.5`, `PSC_NE_VEL_P 6`,
`PSC_NE_VEL_D 0.5`. In the random part of the runs, NaN is rare: after a draw outside the ranges,
338 of 20003 attitude lines hold a NaN in some field other than the pitch PID's slew-limiter filter
(which keeps one from line 6040 on: nothing resets that filter), and 10
of 20008 position-controller lines do.

As checks that the harness sees a wrong translation (`CPP2LEAN_MUTATE`, a list of regex
replacements applied to the translation before the build): single-precision trig in
`Quaternion.from_axis_angle` and `from_euler` makes 35138 of 36691 attitude lines differ (first at
line 70, `_attitude_target.q2` 0xbe341abf vs 0xbe341ac0); dividing by the climb instead of the descent
speed limit in `calculate_overspeed_gain` makes 2145 of 40206 position-controller lines differ (first at
line 98). Seed 7 gives 0 differing lines in all four runs as well (`examples/control` with seed 8 too).

**Composition with the AP_Math and AC_PID translations.** Each translation carries its own
translation of the library code it uses. `ardupilot/check_shared.py` compares every declaration two
translations share: the attitude translation's 62 AP_Math declarations (the quaternion functions
among them, `from_axis_angle` with the `double` half-angle trig the AST holds) are identical in code to
`AP_Math_lib`'s, its 52 AC_PID-family declarations to `AC_PID_lib`'s; the position controller's 83 and
100 likewise (`Vector2<double>` is named `Vector2p` here, `Vector2_double` in `AC_PID_lib`; one
declaration's doc comment cites `vector3.cpp:632`, the explicit instantiation the unity includes, for
`vector3.h`).

**The per-tick composition** (`ardupilot/compose/compose.sh [N [HOLD_FROM]]`). `Compose.lean` wires the
three translations (AP_MotorsMatrix from `out/AP_Motors`, AC_AttitudeControl_Multi, AC_PosControl) for
one 400 Hz tick as the reference harness that recorded `ardupilot/data/oracle-nosincos.txt` wires the
compiled classes: scheduler loop time, `set_dt_s` on the three, `rate_controller_run` and
`rate_controller_target_reset`, `output`, the AHRS view, `update_estimates`, on the first tick the calls
of `wp_and_spline_init_m` into AC_PosControl and the rate time constants, the navigator's targets from
the recorded trace (`set_pos_vel_accel_NED_m`), `NE_update_controller`, `D_update_controller` (its
`set_throttle_out` event made on the attitude controller), AutoYaw (LOOK_AT_NEXT_WP, HOLD from
`HOLD_FROM`), and `input_thrust_vector_heading(get_thrust_vector(), heading)`. A class's `Inputs` are
filled from the other objects' translated state by their translated getters
(`AP_MotorsMatrix.get_throttle_hover`, `AC_AttitudeControl_Multi.get_att_target_euler_rad`, ...); the
attitude controller's `Outputs` start from the motors' stored values and are written back through the
AP_Motors translation's setters. The environment, the AHRS view of each recorded sample and the
navigator's targets, comes from `compose_env.cpp`, the AHRS stub compiled with the reference flags; it
is the only C++ in the loop. Construction, parameters (the code defaults, SITL's `ATC_RAT_YAW_P 0.3`,
`ATC_RAT_YAW_I 0.02`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.39`, `MOT_BAT_VOLT_MAX 0`, then
`copter-cf2x.txt` and `copter-course-speed.txt`) and the takeover are those of the reference harness.
The tick's 22 numbers (four actuators, the position, velocity and acceleration targets, the thrust
vector, the attitude target's Euler angles, the body-rate targets) are compared with the recorded
output `ardupilot/data/oracle-nosincos.txt`:

```
$ ardupilot/compose/compose.sh            # 500 ticks
composition: 500 ticks; actuators bit-identical to the oracle on 500 of 500 ticks; all 22 values on 500 of 500 ticks
$ ardupilot/compose/compose.sh 8431       # the whole flight
composition: 8431 ticks; actuators bit-identical to the oracle on 8431 of 8431 ticks; all 22 values on 8431 of 8431 ticks
```

With single-precision trig substituted in the attitude translation (`CPP2LEAN_MUTATE`, applied to
`AC_Attitude_lib.lean`), the 500-tick check still passes on the actuators (they first differ at tick
503) but not on all values (the roll body-rate target differs at tick 496, 0x3de6bd69 vs 0x3de6bd68);
over the flight the actuators differ on 7082 ticks, and the output equals the recorded diagnostic
variant `ardupilot/data/oracle-diag-floattrig.txt` (single-precision `from_axis_angle`) on all 8431
ticks.

## AC_WPNav, the AHRS view, and the two vehicles

### AC_WPNav

`ardupilot/translate_ac_wpnav.sh` translates `AC_WPNav` (`libraries/AC_WPNav/AC_WPNav.{h,cpp}`) with
what it uses, `SCurve`, `SplineCurve`, the shaping functions of `AP_Math/control.cpp` and the rest of
AP_Math, into `ardupilot/out/AC_WPNav/AC_WPNav_lib.lean` (3118 lines, no rejection), from
`ardupilot/unity_ac_wpnav.cpp` (checked by `check_unity.py`), with `--nest` and the flags of the other
translations plus `-DAP_TERRAIN_AVAILABLE=0`. That define is the one configuration change: with the
stub headers `AP_Terrain.h` does not compile (it needs MAVLink's message types, which the stub
`GCS_MAVLink` does not declare); with the terrain database compiled out, AC_WPNav's terrain source is
the rangefinder or none (`AC_WPNav.cpp:186-205`), and `get_terrain_source`, `get_terrain_U_m`,
`get_terrain_D_m` and `convert_origin_to_alt_frame` are translated as they are. `AC_Avoid`,
`AC_WPNav_OA` and `AC_Circle` are not compiled (AC_WPNav.cpp calls none of them). To compile
`AC_WPNav.cpp` unmodified, the AHRS stub declares `get_origin` (`AP_AHRS.h:221`, returning false),
which only `get_wp_destination_loc` calls.

- Boundary: `AP_AHRS_View`, `AP_AHRS`, `AC_PosControl`, `AC_AttitudeControl`, `AP_HAL::HAL`, the clock
  (`--boundary-fn AP_HAL::millis`, and `AP_HAL::micros64`, read only by SCurve's logging). What the
  navigator reads from the attitude controller (`get_ang_vel_roll_max_rads`, ..., `get_input_tc`) and
  the clock are `Inputs`; its calls into the position controller are `Output` events in order
  (`--output-log`: `D_init_controller_stopping_point`, `NE_set_max_speed_accel_m`, ...,
  `set_pos_vel_accel_NED_m`, `NE_update_controller`); its reads of the position controller are live
  (`--boundary-live AC_PosControl`, below), among them `_pos_control.NE_get_pos_p().kP()`
  (`--boundary-query AC_PosControl::NE_get_pos_p --boundary-query AC_P_2D::kP`), one input `NE_get_pos_p_kP`.
- Left out (`--drop`): the Location-based entry points (`set_wp_destination_loc`,
  `set_wp_destination_next_loc`, `get_wp_destination_loc`, `get_oa_wp_destination`,
  `set_spline_destination_loc`, `set_spline_destination_next_loc`, `get_vector_NED_m`), which convert
  through the EKF origin; `convert_parameters` (parameter storage); SCurve's console messages
  (`printf` under SITL) and `debug`; its one-time log record (`AP_Logger::Write` and the static latch
  `SCurve::calculate_path::logged_scve`, `SCurve.cpp:1043-1061`); `AP_InternalError::error`.
- Kept: the NED-meter entry points a vehicle uses (`wp_and_spline_init_m`, `set_wp_destination_NED_m`,
  `set_wp_destination_next_NED_m`, `set_spline_destination_NED_m`, `set_spline_destination_next_NED_m`,
  `set_circle_destination_NED_m`, `update_wpnav`, `advance_wp_target_along_track`,
  `reached_wp_destination`, `is_active`, the stopping points, `set_speed_NE_ms`, the speed and
  acceleration getters, the yaw, roll and pitch accessors) and the `var_info` defaults (`WP_SPD`,
  `WP_ACC`, `WP_RADIUS_M`, `WP_SPD_UP`, `WP_SPD_DN`, `WP_ACC_Z`, `WP_JERK`, `WP_ACC_CNR`, `WP_RFND_USE`,
  `WP_TER_MARGIN`): 65 member functions in the difftest.

**Live reads.** The navigator reads the position controller after calling into it in the same member
function: `wp_and_spline_init_m` calls `NE_set_max_speed_accel_m` and then reads the stopping point,
which depends on the limits just set (`AC_WPNav.cpp:232-253`); `set_wp_destination_NED_m` may
re-initialize and then reads the speed limits; `set_speed_NE_ms` sets them and reads them back. The
translator's premise for boundary reads, that the boundary object does not change while a member
function runs, does not hold there, and inputs read once per call would be wrong in the vehicle. With
`--boundary-live C`, every read of an object of class C is a field of `Inputs` whose type is a function
of the output log so far and of the call's arguments, applied where the C++ reads:

```lean
  get_stopping_point_NE_m_stopping_point_ne_m : Outputs → Vector2p.State := fun _ => {}
  terrain_scaler_D_m : Outputs → Float32 → Float32 → Float32 := fun _ _ _ => (0.0 : Float32)
...
  let t'1 := inp.get_stopping_point_NE_m_stopping_point_ne_m o
```

A member function that reads a live object takes the log `o` (and returns it only if it writes it);
the caller of a top-level call passes `#[]` and the `Inputs` of the object as it was at the call. The
vehicle (`lean/Vehicle.lean`, `wpInputs`) makes each read by replaying the log on the position
controller's translation (`replayPos`) and calling its getter, and makes the calls on it after the
call returns. A local reference bound to a live read (`const Vector3p& psc_pos_offset_ned_m =
_pos_control.get_pos_offset_NED_m();`, `AC_WPNav.cpp:572`) names the member, not a copy: each use
reads it again with the log as it is then (a reference to a live read with arguments is rejected).

**Constructs added** (each covered by `examples/navigate.cpp` or the ArduPilot goldens, and by
`tests/reject_phase3d.cpp` for its limits):

- `--boundary-live` (above); `--boundary-query` accessors that return a reference to a member object of
  a boundary object (`_pos_control.NE_get_pos_p()`), which is then part of the boundary, and a
  parameter of it read through its conversion (`.kP()` as a float).
- Reference arguments bound to a member that the called member function also reaches through `this`
  (`SplineCurve::calc_dt_speed_max(..., _destination_speed_max, ...)`, `SplineCurve.cpp:93`, writes
  `speed_max` and then reads `_destination_speed_max`, `:214-215`; in C++ the two are one object): the
  callee is translated for that call with the parameter replaced by the member,
  `calc_dt_speed_max'_destination_speed_max`. Found by the difftest: before this construct, 49949 of
  50276 AC_WPNav lines differed, the first at `_spline_this_leg._destination_speed_max`.
- One-bit unsigned bit-fields (`uint8_t reached_destination : 1`, `AC_WPNav.h:362-366`): the declared
  type, writes stored modulo 2 (`&&& 1`), `++`/`--` rejected.
- Arrays of anonymous structs (SCurve's `struct {...} segment[23]`), arrays of library value classes
  (SplineCurve's `Vector3p _hermite_solution[4]`), and the default construction of an array member
  whose elements construct to zero (the field's default).
- Loops from an unsigned variable start to an inclusive variable bound (`for (uint8_t i = first;
  i <= last; i++)`, `SCurve.cpp:1186`), and loops bounded by a data member in a const member function
  (`i < num_segs`, `SCurve.cpp:800`, `:1218`).
- `--drop` of a static local (`Function::name`): the statements that only touch it and dropped
  functions are left out; calls of `--boundary-fn` functions in their arguments do not count as effects.
- Views of a variable (`stopping_point_ned_m.xy()`) as the target of a write, of a non-const call and
  of a reference argument (reads of such views keep calling the translated accessor).
- `explicit operator double` and `operator int` of a parameter class (AP_Param.h:1010-1016) convert the
  value (before, `sq(AP_Float)` produced a type error in Lean).
- Struct arguments of boundary outputs passed by const reference (`set_pos_vel_accel_NED_m(const
  Vector3p&, ...)`); the difftest prints them leaf by leaf.
- `signatures.json` lists every class's `var_info` table (`var_info`: the parameter entries with their
  Lean paths, the nested tables), which the vehicle's parameter loader uses.
- Emission order: blocks with equal source keys are ordered by their position in clang's AST, also
  when placed as dependencies (two specializations of `MIN` at `AP_Math.h:300` came out in either order
  from run to run, depending on Python's string hashing); every earlier golden is unchanged by this.

Differential tests (seed 20261104; `python3 difftest.py ardupilot/AC_WPNav`):

```
ardupilot/AC_WPNav AC_WPNav (defaults): 47761 calls on one object (20000 random, 27761 corner) over 65 member functions, 577 state leaves per line; inputs: get_ang_vel_roll_max_rads, ..., crosstrack_error_m
ardupilot/AC_WPNav AC_WPNav (defaults): 0 of 47762 lines differ (36685 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_WPNav AC_WPNav (course): 47761 calls on one object (20000 random, 27761 corner) over 65 member functions, 577 state leaves per line; inputs: (as above)
ardupilot/AC_WPNav AC_WPNav (course): 0 of 47762 lines differ (28214 tokens equal only as NaN vs NaN with different bits)
```

`ardupilot/AC_WPNav.json`: an `AC_WPNav` on the AHRS view stub and C++-only stand-ins for the position
and attitude controllers (`ardupilot/standin/AC_AttitudeControl/AC_PosControl.h` and
`AC_AttitudeControl.h`, put in place of the real headers by `-ivfsoverlay`; the real getters cannot
return arbitrary values). The position controller's stand-in records every call in the output log and
answers each read with the line's value plus 0.125 times the number of calls recorded so far in the
member function (plus 0.5 and 0.25 times the arguments of `terrain_scaler_D_m`); the Lean driver's
live `Inputs` compute the same from the log they are given, so the difftest sees whether a read
follows the right calls. A value a read returns by reference is a member that every recorded call
updates. Set up with `wp_and_spline_init_m`, driven through every public member function and
`calc_scurve_jerk_and_snap`, weighted to `update_wpnav`, the destination setters and the spline and
circle legs; destinations within ±10 m, speeds in [0.5, 10] m/s, `dt` in [0.0025, 0.004] s, the clock
increasing. `defaults` keeps the code defaults; `course` sets `WP_SPD 1`, `WP_ACC 1.5`
(`copter-course-speed.txt`) and weights `update_wpnav` with time steps up to 0.1 s, so that legs are
flown to their end (2502 changes of `reached_destination` in its stream). SCurve's console messages
go to `/dev/null` (`quiet_console`). As checks that the harness sees a wrong translation
(`CPP2LEAN_MUTATE`): reading the stopping point with an empty log instead of the log so far makes
47534 of 47762 `defaults` lines differ (47613 `course`), the first at line 1 (`_origin_ned_m.x`
0xbffbcc18d4f4f714 vs 0xc003e60c6a7a7b8a: six calls, 0.75); the along-track buffer 0.05 changed to
0.06 (`AC_WPNav.cpp:589`) makes 35902 and 38592 lines differ, the first at line 18
(`_track_dt_scalar`). Seed 7 gives 0 differing lines in both runs as well (and in `navigate` and
`ardupilot/AHRS_View`). `check_shared.py`: AC_WPNav_lib shares 77 declarations with AP_Math_lib and 45
with AC_PosControl_lib, all identical in code.

### The AHRS view

`AP_AHRS_View.cpp` and `AP_AHRS_Backend.cpp` do not compile against the stub headers (their headers
reach the EKF, the INS, GPS and MAVLink). `ardupilot/translate_ahrs_view.sh` therefore translates
`ardupilot/unity_ahrs_view.cpp`, which holds exactly the two function bodies, copied unmodified by
`ardupilot/ahrs/extract.py` (it checks the first and last lines and every byte against the source) into
files of the same names at the same line numbers (`AP_AHRS_View::update`, `AP_AHRS_View.cpp:61-83` at
802db19de1, and `AP_AHRS::calc_trig`, `AP_AHRS_Backend.cpp:93-135`), after the declarations they use
(`ardupilot/ahrs/AP_AHRS_View_decls.h`: the real declarations, cited by line, with a constructor that
only binds the AHRS), then the AP_Math sources. The AHRS is the boundary: its rotation matrix and gyro
are inputs; `calc_trig` reads nothing of the AHRS object and is translated as a function of its
arguments (`--boundary-static AP_AHRS::calc_trig`, `AHRS_View_lib.AP_AHRS_calc_trig`). Output:
`ardupilot/out/AHRS_View/AHRS_View_lib.lean` (375 lines), with `QuaternionT<float>::rotation_matrix`
(`--use`) for the vehicle. Constructs added:

- `--boundary-static Class::member` (above).
- Nullable out-pointers: a parameter `T *p` used only in `p != nullptr` / `p == nullptr` and `*p`
  (`Matrix3<T>::to_euler(T *roll, T *pitch, T *yaw)`, `matrix3.cpp:49-60`) is a flag `p'given` and the
  value, returned as for `T &`; an argument `&x` passes `true` and x and receives the result, `nullptr`
  passes `false` and a zero and discards it. Other pointer parameters remain rejected.

```
ardupilot/AHRS_View AP_AHRS_View: 21096 calls on one object (20000 random, 1096 corner) over 1 member functions, 44 state leaves per line (set from the line before each call); inputs: get_rotation_body_to_ned.a.x, ..., get_gyro.z
ardupilot/AHRS_View AP_AHRS_View: 0 of 21097 lines differ (274 tokens equal only as NaN vs NaN with different bits)
```

`ardupilot/AHRS_View.json`: the C++ side compiles the same unity file; the state comes from the line
(`y_angle` and the pitch trim 0 on 60% of the lines, the ROTATION_NONE path, random otherwise); 90% of
the rotation inputs are rotation matrices (`rotation_inputs`), a tenth of those at pitch ±90 degrees,
where `calc_trig` falls back to `to_euler` and `cosf`/`sinf` (1943 lines). Computing that fallback's
cosine in double precision makes 26 lines differ. `check_shared.py`: 22 declarations shared with
AP_Math_lib, identical.

### The two vehicles

Both speak the lock-step protocol of `sim/PROTOCOL.md` (17 numbers in per tick, four actuators out,
`--params`, `--set`, `--exact`, `--trace`, `--print-params`, and `--bits` for the bit patterns), are built
by `ardupilot/vehicle/build.sh`, and run the same harness:

- `copter_ref` (`ardupilot/vehicle/copter_ref.cpp`): ArduPilot's AP_Motors, AC_AttitudeControl,
  AC_PosControl, AC_WPNav, AP_Math, AC_PID, Filter, SCurve and SplineCurve compiled unmodified with the
  stub headers, the defines of the translations and `-O2 -ffp-contract=off -fno-fast-math
  -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin`, linked with
  `ardupilot/stubs/oracle_env.cpp`. The AHRS view is the stub, which derives the angles and their
  trigonometry from the sample as `AP_AHRS_View::update` does.
- `copter_lean` (`lean/Vehicle.lean`, `lean/VehicleMain.lean`): the translations AP_Motors_lib,
  AC_Attitude_lib, AC_PosControl_lib, AC_WPNav_lib and AHRS_View_lib, wired per tick as `Compose.lean`
  wires the first three, with the navigator's live reads and calls (above) and the translated view.

The harness (the same functions, in the same order and with the same names, in both files): input
parsing and exact printing; parameters by ArduPilot name through the classes' own var_info tables
under ArduCopter's prefixes `ATC_`, `PSC`, `MOT_`, `WP_` (C++: `collect_params`; Lean: the tables
`ardupilot/vehicle/gen_params.py` generates from `signatures.json`, `lean/VehicleParams.lean`), with SITL's
run deviations; construction, boot (`init(QUAD, X)`, armed, interlocked, `THROTTLE_UNLIMITED`) and the
takeover on the first sample; the tick in Copter's fast-loop order (scheduler, rate controller, motors
output, AHRS, inertial estimates), entry into Auto on the first tick and `Copter::update_flight_mode`;
and a thin mission harness written from ArduCopter's C++, each function marked with the lines it
mirrors: `ModeAuto::init`, `run`, `wp_start`, `do_nav_wp`, `set_next_wp`, `verify_nav_wp`,
`loiter_start` and `exit_mission` (`mode_auto.cpp`), `AutoYaw` LOOK_AT_NEXT_WP and HOLD (`set_mode`,
`default_mode`, `yaw_rad`, `rate_rads`, `get_heading`, `autoyaw.cpp`), and the parts of
`AP_Mission::start`, `update`, `advance_current_nav_cmd` and `complete` that a list of waypoints uses.
The waypoints are NED destinations of `set_wp_destination_NED_m`, the next one that of
`set_wp_destination_next_NED_m`.

**Replay check** (`ardupilot/vehicle/replay.sh`, in the suite): both vehicles on the recorded flight
`ardupilot/data/inputs.txt` with `copter-cf2x.txt` (whose waypoint list is the recorded flight's
figure-eight mission) and `copter-course-speed.txt`, `--exact --trace --bits`:

```
parameters: 133 lines each, identical
replay: 8431 and 8431 ticks; all 22 values bit-identical between copter_lean and copter_ref on 8431 of 8431 ticks (exact decimals equal on 8431)
relation to oracle-nosincos.txt (navigator targets from the recording): actuators equal on 1 of 8431 ticks, all 22 values on 0; first difference: navigator targets (pos_n 1, vel_n 1, acc_n 1), actuators (m1 2), attitude targets (roll_t 485)
```

The recorded reference output `oracle-nosincos.txt` took its navigator targets from the recording
(the navigator that flew it was not AC_WPNav), while both vehicles run AC_WPNav. The targets differ
from the first tick (both start at the stopping point, the vehicle resting on the ground 1.35 cm above
the origin, but differ in the last bits; AC_WPNav's jerk-limited S-curve then climbs far more slowly), the actuators one tick later
(the motors output the previous tick's targets), the attitude targets from tick 485. The replay is
open loop: the states are the recording's, not those of a vehicle following AC_WPNav, so AC_WPNav's
along-track time scaling (`AC_WPNav.cpp:583-607`, the target waits for a vehicle that does not
follow it) holds the target back: at tick 6618, where the recorded mission ended at the start point,
AC_WPNav's target is at (0.76, -0.74, -1.57) m, on the leg towards the fifth waypoint, and it is still
in that region at the last tick.
With the navigator's targets taken from the recording instead, the same classes reproduce
`oracle-nosincos.txt` exactly (the composition check, above).

**Flights** (`sim/fly.sh`, `sim/README.md`, `sim/RESULTS.md`): hover, the 1 m/s figure-eight course and
the course at ArduPilot's default speed, each flown with both vehicles in gym-pybullet-drones: on every
tick of the three missions (4000, 24000 and 12000) the actuators, the simulator's states and all 22
values are bit-identical between the two vehicles.

## Lean 4.33 API findings

- Present: `Float32` `+ - * /`, `Neg` (`Float32.neg`, C `-a`), `<`/`≤` (decidable), `BEq`
  (`==`, `!=`, IEEE), `Float32.toFloat`, `Float.toFloat32`, `Float32.toBits`/`ofBits`,
  `Float.toBits`/`ofBits`, `isNaN`/`isInf`/`isFinite`, the libm externs of the table, and every
  int/float conversion of the cast table (`Int8..Int64`/`UInt8..UInt64`/`USize` `.toFloat32` and
  `.toFloat`, `Float32/Float.toInt8..toUSize`).
- Missing: `fmaxf`, `fminf`, `fmax`, `fmin` (handled by `CppLibm.lean`); combined sign-and-width
  integer conversions (composed); `Int32.toNat` (`toNatClampNeg`).
- Structures: `{ s with a.b := v }` updates a nested field; `Array.set!`, `Array.replicate` and
  `a[i]!` exist; `deriving Inhabited` and `deriving DecidableEq, Inhabited` (for an inductive of
  enumerators) work without Mathlib.
- With the default `autoImplicit true`, an unknown name in a binder's default value is silently
  bound as an implicit argument instead of reported (found while ordering a default argument that
  names a `static constexpr` member); `lean/lakefile.toml` sets `autoImplicit = false`, and the
  translator orders every constant before its first use.
- NaN bits are not observable: `Float32.toBits` and `Float.toBits` return the canonical NaN
  (0x7fc00000, 0x7ff8000000000000) for every NaN, and `Float32.ofBits` canonicalizes a NaN input,
  consistent with the logical model, which has a single NaN. Checked in compiled code: `(-(0/0)).toBits`
  is 0x7fc00000, `(Float32.ofBits 0x7fc00001).toBits` is 0x7fc00000.
- (Phase 3) No `fmodf`/`fmod` in core: `CppLibm.lean` declares them `@[extern "fmodf"]` /
  `@[extern "fmod"]`, as core declares `Float32.sin`. A `Float32` cannot hold a signaling NaN
  (`ofBits 0x7f800001` is quiet), which matters because libm's `fmaxf`/`fminf` return the other operand
  for a quiet NaN and a NaN for a signaling one; the C++ drivers therefore quiet signaling NaN inputs
  (see "Compilation assumptions"). This changed the NaN-rule counts of the earlier runs, not their
  verdicts.
- (Phase 3) Layout: a structure instance `{ a := x,` continued on a line indented less than its first
  field does not parse in Lean 4.33; generated code and the hand-written harnesses (`Compose.lean`, `Vehicle.lean`)
  keep each instance on one line.
- (Phase 3, third part) No namespace aliases: `abbrev M := AP_Motors_lib.AP_MotorsMatrix` is not a
  declaration Lean accepts (a namespace is not a term), so `Compose.lean` names every function in
  full. No other gap: `UInt64.toFloat32`, `Float.toFloat32`, `Float32.toBits`, `Array.set!` and
  structure updates of nested fields (`{ s with _pos.x := a, _pos.y := b }`, several fields in one
  update) are all present in core Lean 4.33. `List.asString` is deprecated (`String.ofList`).

- (Fourth part) No decimal-to-float parser in core (`String.toFloat?` does not exist): the vehicle
  parses with `OfScientific.ofScientific` at `Float` and `Float32`, which are correctly rounded (the
  `strtod`/`strtof` of the C++ vehicle), and prints exact decimals and `%.6f` from `toBits` with `Nat`
  arithmetic (`toString` of a float prints a short decimal). A structure with function-typed fields
  (the live `Inputs`) derives `Inhabited` and takes `fun _ => ...` defaults without further help.

## Differential test

`difftest.py` translates each example into `lean/`, generates the C++ driver
`examples/<example>_driver.cpp` (it `#include`s the example, so static functions are reachable) and
compiles it with the flags above, generates `lean/Main.lean` and runs `lake build` (a warning fails the
run), then feeds both executables the same input lines.

- Input line: one column per parameter slot (for each type, as many columns as the most parameters
  of that type in one function); floating values as hex bit patterns (read with `memcpy` in C++,
  `ofBits` in Lean), integers in decimal, bools as 0/1. Every function of the example is called on
  every line, its k-th parameter of type T taken from the k-th T column.
- Inputs: 2000 random lines (seed 20261104; per column: 40% uniform in [-2, 2], 20% in [-1000, 1000],
  20% ±10^u with u in [-8, 8], 20% uniformly random finite bit patterns, which include subnormals and
  huge values; integers: 40% in [-10, 10], 30% in [-100000, 100000], 30% the full range), plus corner
  lines: the full product of the corner values over as many leading columns as fit in 20000 lines,
  the other columns cycling through theirs. Float corners: ±0, ±1, 0.5, 0.1, ± the smallest
  subnormal, the largest subnormal, the smallest normal, `FLT_EPSILON`, 2^24, ± the largest finite,
  ±inf, NaN 0x7fc00000, -NaN 0xffc00000, a payload NaN 0x7fc00001, a signaling NaN 0x7f800001
  (doubles: the same set); integer corners: 0, ±1, ±2, 7, 8, 9, 31, 32, the minimum and maximum.
- Output: one line per call, `<input line> <function> <hex> <decimal>` for floating results
  (C: `%08x %.9g` / `%016llx %.17g`; Lean: the hex of `toBits` and `toString`), `<input line>
  <function> <value>` for integers and bools. The comparison is on the hex fields (and the decimal of
  integers); the floating decimals are informational, since the two sides format them differently.
- NaN comparison: bit-exact, except that a NaN matches a NaN. This relaxation is needed because
  Lean cannot print a NaN's sign or payload (see the API findings), so the Lean side always prints
  the canonical NaN, while the C++ side prints what arm64 computed (payloads propagate from NaN
  inputs; negation flips the sign of a NaN). Within the subset a NaN's payload and sign are not
  observable by any operation other than printing its bits (comparisons, `isnan`, arithmetic and
  conversions treat all NaNs alike), so the relaxation hides nothing else. The harness reports how many
  lines match only by this rule, grouped by the two patterns, and fails if Lean ever prints a
  non-canonical NaN.
- Also checked: each floating literal the translator emitted, evaluated in compiled Lean, has the bits
  clang gave it (`demo --literals`).

Classes (`examples/<example>.json`, key `classes`): for each listed class a C++ driver
`examples/<example>_<Class>_driver.cpp` (it includes the example with `private`/`protected` defined
as `public`, so it can print every member) and a Lean loop in `lean/Main.lean` (`demo <Ns>.<Class>`)
drive one object through a sequence of calls; the object (C++, with static storage) and the state
(Lean, from `init`) persist across the input lines.

- Configuration: `ctor` (constructor arguments, C++ spelling; enumerators as `Kind::Circle`),
  `globals` and `boundary_args` (the boundary objects the C++ driver defines and passes to the
  constructor), `inputs` (for each `Inputs` field, by path, the C++ statement that makes the boundary
  object return the line's value, e.g. `ahrs_obj.gain_scaler = %s;`), `input_aliases` (fields that
  are the same C++ object: `_pid_pitch.get_control_gain_scaler` is `_pid_roll.get_control_gain_scaler`,
  since both PIDs read one AHRS), `ranges` (per parameter or input name, the interval of 85% of its
  random values; the other 15% come from the free-function mixture above), `weights` (relative
  frequency of member functions), `calls`. Phase 3 adds: `outputs` (for each flattened `Outputs`
  field, the C++ expression holding what the boundary object received, e.g. `motors_obj.roll_in`;
  printed after the state leaves on both sides), `cxx_include` (the header to include instead of the
  example), `cxx_prelude` (lines before it, e.g. `#include <AP_Math/AP_Math.h>` for a header that
  relies on its includer), `extra_methods` (non-public member functions to drive, e.g. `update_i`),
  `monotonic` (inputs that never decrease, as a clock: each value is the previous plus a random step in
  the interval), `range_prob` (the share of random values taken from `ranges`, default 0.85). Struct
  arguments and results of translated struct type are driven leaf by leaf (`Vector2f`).
- ArduPilot targets (`ardupilot/<name>.json`, run as `difftest.py ardupilot/<name>`): `translate`
  (the script that writes the Lean), `out`, `namespace`, `cxx_flags` (with `$STUBS` and `$L` for
  `ardupilot/stubs` and ArduPilot's `libraries/`), `cxx_sources` (compiled and linked into each class
  driver), `cxx_env` (the environment: stubbed HAL and AP_Param functions), and `classes` as above.
- Phase 3, second part (`ardupilot/AP_Math.json`, `ardupilot/AP_Motors.json`): `free` (the
  free-function harness for translated library functions: one call per line with typed arguments,
  including struct arguments leaf by leaf and reference parameters printed after the call; `ranges`,
  `weights`, `unit_args` for arguments that are unit vectors with a probability), `state_from_line`
  (each line sets the object's leaves before the call, for value classes such as `Vector3f`;
  `unit_state` draws unit quaternions), `cxx_class` (the C++ class to construct, e.g. the driver's
  subclass `DriverMotors` overriding the `--boundary-call` members), `setup` (fixed calls before the
  random ones), `params` (parameter values set after construction, on both sides), `const_inputs`
  (inputs held at one value), `domains` (the argument and parameter domains outside which the C++ has
  undefined behavior), `exclude` (member functions not called at random), `member_methods` (member
  functions of a member object, called through it, with the owner helper when they read the owner),
  `after_call`/`after_call_for` (C++ statements after every call, or after one function, that turn a
  boundary effect without a virtual hook into an event, e.g. `AP_Notify::flags.armed`), `run` (a name,
  for several configurations of one class). With `--output-log`, the output line holds the events of
  the call (`e:rc_write i:0 i:1500 ...`), printed by the C++ boundary stand-ins in
  `ardupilot/cpp2lean_events.h` and by Lean from the returned `Array Output`.
- Phase 3, third part (`ardupilot/AC_Attitude.json`, `ardupilot/AC_PosControl.json`,
  `examples/control.json`): an input of a struct type (`_ahrs.get_quat_body_to_ned(q)`) is driven leaf
  by leaf (`get_quat_body_to_ned_q.q1`, ...); `unit_inputs` (struct inputs whose leaves are a unit
  vector with a probability), `input_domains` (the values a boundary getter can return, e.g. a
  getter that constrains: every value of the input, random or corner, lies in the interval),
  `input_corners: "readers"` (corner values of the inputs only for the member functions that read
  inputs), `enum_leaves` (struct arguments with enum members are driven, the enum by its value),
  ranges by `param.leaf` (`heading.yaw_rate_rads`) and by input path (`get_gyro_latest.x`, else its
  prefix `get_gyro_latest`, else the last component), `lean_outputs` (a Lean expression, `%s` the
  output, printed where the C++ side prints a value the boundary object stored as a function of the
  argument), `lean_imports` (another translation's output directory, whose modules the driver
  imports), `cxx_overlay` (a boundary header a translated file includes from its own directory,
  replaced for the C++ side by a stand-in through clang's `-ivfsoverlay`). The environment variable
  `CPP2LEAN_MUTATE` (a JSON list of `[regex, replacement]`) edits an ArduPilot translation before the
  build, for the sensitivity checks; `ardupilot/compose/compose.sh` reads it too (applied to
  `CPP2LEAN_MUTATE_FILE`, default `AC_Attitude_lib.lean`).
- Input line: a member function (its Lean name), its arguments, then a value for every field of the
  flattened `Inputs` (also on calls that do not read them). The public member functions whose
  parameters and result are scalars or enums are driven, base versions included (`Tile.Shape.area`
  is the C++ call `obj.Shape::area()`). Inputs: `calls` random calls (default 20000, seed as above),
  then for every member function and every parameter and input, one call per corner value of its
  type (enum parameters: every enumerator) with the other arguments random.
- Output line: `<line> <function> <result> <reference parameters after the call> | <every leaf of
  Params and State after the call>` as typed tokens (`f:<hex>`, `d:<hex>`, `b:0/1`, `i:<decimal>`,
  enums by value), and a first line with the state after construction. The lines are compared token
  by token, with the NaN rule for `f:`/`d:` tokens.

## Demo transcript

C++ input, `examples/numeric.cpp`:

```cpp
// cpp2lean demo (phase 1): free functions over numbers. Bodies marked "ArduPilot" follow the
// ArduPilot source at the cited lines (commit 802db19de1); the rest is written for the demo.
#include <cfloat>
#include <cmath>

// ArduPilot AP_Math.cpp:282-304, constrain_value_line<float>: NaN maps to the midpoint.
float constrain_float(float amt, float low, float high)
{
    if (isnan(amt)) {
        return (low + high) / 2;
    }
    if (amt < low) {
        return low;
    }
    if (amt > high) {
        return high;
    }
    return amt;
}

// ArduPilot ftype.h:61-63, is_zero(float).
bool is_zero(float x) { return fabsf(x) < FLT_EPSILON; }

// ArduPilot AP_Math.cpp:72-81, safe_sqrt<double> (isgreaterequal(val, 0) written as val >= 0).
float safe_sqrt(double v)
{
    const float val = static_cast<float>(v);
    if (val >= 0) {
        return sqrtf(val);
    }
    return 0;
}

// ArduPilot AP_Motors_Thrust_Linearization.cpp:119-133, apply_thrust_curve_and_volt_scaling with
// battery_scale = 1: solves thrust = (1-e)*u + e*u^2 for u. The literals are doubles, as there.
float thrust_curve(float thrust, float expo, float lift_max)
{
    float thrust_curve_expo = constrain_float(expo, -1.0, 1.0);
    if (is_zero(thrust_curve_expo)) {
        return lift_max * thrust;
    }
    float throttle_ratio = ((thrust_curve_expo - 1.0) + safe_sqrt((1.0 - thrust_curve_expo) * (1.0 - thrust_curve_expo) + 4.0 * thrust_curve_expo * lift_max * thrust)) / (2.0 * thrust_curve_expo);
    return constrain_float(throttle_ratio, 0.0, 1.0);
}

// Horner evaluation of a fixed polynomial, coefficients from a constant array.
static const float horner_coeffs[5] = {1.0f, -0.5f, 0.25f, -0.125f, 0.0625f};

float horner(float x)
{
    float acc = 0.0f;
    for (int i = 0; i < 5; i++) {
        acc = acc * x + horner_coeffs[4 - i];
    }
    return acc;
}

// Single precision throughout, then the float -> double -> float chain of mixed code.
float half_angle_sin(float theta) { return sinf(0.5f * theta); }
float half_angle_sin_d(float theta) { return (float)sin(0.5 * theta); }

// Early returns, a ternary, and a bounded loop with break and continue.
int clamp_steps(int n, float x)
{
    if (n <= 0) {
        return 0;
    }
    if (isnan(x)) return -1;
    int steps = n > 8 ? 8 : n;
    int count = 0;
    float y = x;
    for (int i = 0; i < 8; ++i) {
        if (i >= steps) break;
        y *= 0.5f;
        if (fabsf(y) < 1.0f) continue;
        count += i;
    }
    return 2 * count + (y > 0 ? 1 : 0);
}
```

`python3 cpp2lean.py examples/numeric.cpp -o lean` writes `lean/Numeric.lean` (identical to
`tests/golden/Numeric.lean`; the module doc comment is omitted here):

```lean
namespace Numeric

/-- C++ `float constrain_float(float amt, float low, float high)`, `examples/numeric.cpp:7-19`. -/
def constrain_float (amt low high : Float32) : Float32 := Id.run do
  if Float32.isNaN amt then
    return (low + high) / Int32.toFloat32 (2 : Int32)
  if amt < low then
    return low
  if amt > high then
    return high
  return amt

/-- C++ `bool is_zero(float x)`, `examples/numeric.cpp:22`. -/
def is_zero (x : Float32) : Bool := Id.run do
  return decide (Float32.abs x < (1.1920929e-7 : Float32))

/-- C++ `float safe_sqrt(double v)`, `examples/numeric.cpp:25-32`. -/
def safe_sqrt (v : Float) : Float32 := Id.run do
  let val : Float32 := Float.toFloat32 v
  if val ≥ Int32.toFloat32 (0 : Int32) then
    return Float32.sqrt val
  return Int32.toFloat32 (0 : Int32)

/-- C++ `float thrust_curve(float thrust, float expo, float lift_max)`, `examples/numeric.cpp:36-44`. -/
def thrust_curve (thrust expo lift_max : Float32) : Float32 := Id.run do
  let thrust_curve_expo : Float32 := constrain_float expo (Float.toFloat32 (-(1.0 : Float))) (Float.toFloat32 (1.0 : Float))
  if is_zero thrust_curve_expo then
    return lift_max * thrust
  let throttle_ratio : Float32 := Float.toFloat32 (((Float32.toFloat thrust_curve_expo - (1.0 : Float)) + Float32.toFloat (safe_sqrt (((1.0 : Float) - Float32.toFloat thrust_curve_expo) * ((1.0 : Float) - Float32.toFloat thrust_curve_expo) + (4.0 : Float) * Float32.toFloat thrust_curve_expo * Float32.toFloat lift_max * Float32.toFloat thrust))) / ((2.0 : Float) * Float32.toFloat thrust_curve_expo))
  return constrain_float throttle_ratio (Float.toFloat32 (0.0 : Float)) (Float.toFloat32 (1.0 : Float))

/-- C++ `const float horner_coeffs[5]`, `examples/numeric.cpp:47`. -/
def horner_coeffs : Array Float32 := #[(1.0 : Float32), -(0.5 : Float32), (0.25 : Float32), -(0.125 : Float32), (0.0625 : Float32)]

/-- C++ `float horner(float x)`, `examples/numeric.cpp:49-56`. -/
def horner (x : Float32) : Float32 := Id.run do
  let mut acc : Float32 := (0.0 : Float32)
  for i' in [0:5] do
    let i : Int32 := Nat.toInt32 i'
    acc := acc * x + horner_coeffs[Int32.toNatClampNeg ((4 : Int32) - i)]!
  return acc

/-- C++ `float half_angle_sin(float theta)`, `examples/numeric.cpp:59`. -/
def half_angle_sin (theta : Float32) : Float32 := Id.run do
  return Float32.sin ((0.5 : Float32) * theta)

/-- C++ `float half_angle_sin_d(float theta)`, `examples/numeric.cpp:60`. -/
def half_angle_sin_d (theta : Float32) : Float32 := Id.run do
  return Float.toFloat32 (Float.sin ((0.5 : Float) * Float32.toFloat theta))

/-- C++ `int clamp_steps(int n, float x)`, `examples/numeric.cpp:63-79`. -/
def clamp_steps (n : Int32) (x : Float32) : Int32 := Id.run do
  if n ≤ (0 : Int32) then
    return (0 : Int32)
  if Float32.isNaN x then
    return -(1 : Int32)
  let steps : Int32 := if n > (8 : Int32) then (8 : Int32) else n
  let mut count : Int32 := (0 : Int32)
  let mut y : Float32 := x
  for i' in [0:8] do
    let i : Int32 := Nat.toInt32 i'
    if i ≥ steps then
      break
    y := y * (0.5 : Float32)
    if Float32.abs y < (1.0 : Float32) then
      continue
    count := count + i
  return (2 : Int32) * count + (if y > Int32.toFloat32 (0 : Int32) then (1 : Int32) else (0 : Int32))

end Numeric
```

`examples/mixed.cpp` (translated to `lean/Mixed.lean`, golden `tests/golden/Mixed.lean`) covers the
rest of the subset: every `<cmath>` mapping in float and double, `isinf`/`isfinite`, `-x` against
`0 - x`, integer widths and every kind of integral conversion, `/` and `%` of negatives, shifts and
bitwise operators, float to integer conversions, `bool` conversions, a variable assigned on both
branches before its first read, a counted `while`, `j++`/`++j` inside expressions, `&&`/`||`/`?:`
with side effects, descending and stepped `for` loops, a `size_t` loop over a constant array, a
`!=` loop with `continue`, and narrow-type promotions.

Phase 2. `examples/pid.cpp` (224 lines) is a PID controller modeled on ArduPilot's `AC_PID`: gains
as `AP_Float` parameters (a stand-in class with ArduPilot's `get`/`set`/conversion interface,
translated with `--param-class AP_Float=float`), filters on the target, error and derivative, an
integrator with anti-windup, a PD sum limit, a nested `pid_flags` struct with `bool` bit-fields, a
`PIDInfo` plain struct member, `reset_I`, `reset_filter`, setters, const getters, results through
reference parameters, and a gain scaler read from an `AHRS` object outside the translation
(`--boundary AHRS`). `RateControl` holds two `PID` members, reads the air density through
`AP::ahrs()`, and calls `ext_sqrt`, a function defined outside the file (`--extern
ext_sqrt:Float32.sqrt`). `examples/shape.cpp` (170 lines) has `Shape` and `Tile : Shape` with a
virtual `area` and an explicit `Shape::area()` call, an `enum class Kind` and a nested unscoped enum
with `switch`es, an array member updated in bounded loops, a reference out-parameter, overloaded
member and free functions, constructors with base and member initializers, default arguments,
`static constexpr` members and a `static` member function, `do`/`while`, the comma operator, `NAN`,
`INFINITY`, `HUGE_VALF`, local structs and arrays, and a struct copy.

From `tests/golden/Pid.lean` (the translation of `examples/pid.cpp`):

```lean
/-- Parameters of C++ `PID` (`examples/pid.cpp:67-196`): its members of a --param-class type. -/
structure Params where
  /-- `AP_Float _kp` of `PID` (`examples/pid.cpp:179`). -/
  _kp : Float32 := (0.0 : Float32)
  /-- `AP_Float _ki` of `PID` (`examples/pid.cpp:180`). -/
  _ki : Float32 := (0.0 : Float32)
  /-- `AP_Float _kd` of `PID` (`examples/pid.cpp:181`). -/
  _kd : Float32 := (0.0 : Float32)
  /-- `AP_Float _kimax` of `PID` (`examples/pid.cpp:182`). -/
  _kimax : Float32 := (0.0 : Float32)
  /-- `AP_Float _kpdmax` of `PID` (`examples/pid.cpp:183`). -/
  _kpdmax : Float32 := (0.0 : Float32)
  /-- `AP_Float _filt_T_hz` of `PID` (`examples/pid.cpp:184`). -/
  _filt_T_hz : Float32 := (0.0 : Float32)
  /-- `AP_Float _filt_E_hz` of `PID` (`examples/pid.cpp:185`). -/
  _filt_E_hz : Float32 := (0.0 : Float32)
  /-- `AP_Float _filt_D_hz` of `PID` (`examples/pid.cpp:186`). -/
  _filt_D_hz : Float32 := (0.0 : Float32)
deriving Inhabited

/-- State of C++ `PID` (`examples/pid.cpp:67-196`): its data members. -/
structure State where
  /-- `struct pid_flags _flags` of `PID` (`examples/pid.cpp:190`). -/
  _flags : PID.pid_flags := {}
  /-- `float _integrator` of `PID` (`examples/pid.cpp:191`). -/
  _integrator : Float32 := (0.0 : Float32)
  /-- `float _target` of `PID` (`examples/pid.cpp:192`). -/
  _target : Float32 := (0.0 : Float32)
  /-- `float _error` of `PID` (`examples/pid.cpp:193`). -/
  _error : Float32 := (0.0 : Float32)
  /-- `float _derivative` of `PID` (`examples/pid.cpp:194`). -/
  _derivative : Float32 := (0.0 : Float32)
  /-- `PIDInfo _info` of `PID` (`examples/pid.cpp:195`). -/
  _info : PIDInfo := {}
deriving Inhabited

/-- Values C++ `PID` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `_ahrs.get_control_gain_scaler()` (first read at `examples/pid.cpp:102`). -/
  get_control_gain_scaler : Float32 := (0.0 : Float32)
deriving Inhabited

/-- C++ `PID::PID(AHRS & ahrs, float initial_p, float initial_i, float initial_d, float initial_imax, float filt_hz)`, `examples/pid.cpp:69-79`. -/
def init (initial_p : Float32) (initial_i : Float32) (initial_d : Float32) (initial_imax : Float32) (filt_hz : Float32) : Params × State := Id.run do
  let mut p : Params := {}
  let mut s : State := {}
  p := { p with _kp := initial_p }
  p := { p with _ki := initial_i }
  p := { p with _kd := initial_d }
  p := { p with _kimax := Float32.abs initial_imax }
  p := { p with _filt_E_hz := filt_hz }
  p := { p with _filt_D_hz := filt_hz * Int32.toFloat32 (2 : Int32) }
  s := { s with _flags._reset_filter := true }
  return (p, s)
```

The C++ of `update_i`:

```cpp
    // AC_PID::update_i (AC_PID.cpp:337-351).
    void update_i(float dt, bool limit)
    {
        if (!is_zero(_ki) && is_positive(dt)) {
            if (!limit || ((is_positive(_integrator) && is_negative(_error)) || (is_negative(_integrator) && is_positive(_error)))) {
                _integrator += (_error * _ki) * dt;
                _integrator = constrain_float(_integrator, -_kimax, _kimax);
            }
        } else {
            _integrator = 0.0f;
        }
    }
```

and its translation (a non-const member function that reads parameters and writes the state):

```lean
/-- C++ `void PID::update_i(float dt, bool limit)`, `examples/pid.cpp:164-174`. -/
def update_i (p : Params) (s : State) (dt : Float32) (limit : Bool) : State := Id.run do
  let mut s := s
  if !(Pid.is_zero p._ki) && Pid.is_positive dt then
    if !limit || ((Pid.is_positive s._integrator && Pid.is_negative s._error) || (Pid.is_negative s._integrator && Pid.is_positive s._error)) then
      s := { s with _integrator := s._integrator + (s._error * p._ki) * dt }
      s := { s with _integrator := Pid.constrain_float s._integrator (-p._kimax) p._kimax }
  else
    s := { s with _integrator := (0.0 : Float32) }
  return s

/-- C++ `void PID::get_terms(float & p_out, float & d_out) const`, `examples/pid.cpp:150`. -/
def get_terms (s : State) (p_out : Float32) (d_out : Float32) : Float32 × Float32 := Id.run do
  let mut p_out := p_out
  let mut d_out := d_out
  p_out := s._info.P
  d_out := s._info.D
  return (p_out, d_out)
```

`RateControl::update`, which calls `update_all` on two member objects:

```cpp
    float update(float target_roll, float rate_roll, float target_pitch, float rate_pitch, float dt)
    {
        const float density = AP::ahrs().get_air_density_ratio();
        const float scale = density > 0.0f ? 1.0f / ext_sqrt(density) : 1.0f;
        _out_roll = _pid_roll.update_all(target_roll, rate_roll, dt, _limit) * scale;
        _out_pitch = _pid_pitch.update_all(target_pitch, rate_pitch, dt, _limit) * scale;
        _limit = fabsf(_out_roll) > 1.0f || fabsf(_out_pitch) > 1.0f;
        return _out_roll + _out_pitch;
    }
    void reset() { _pid_roll.reset_I(); _pid_pitch.reset_filter(); }
    void set_gain(float kp) { _pid_roll.set_kP(kp); _pid_pitch.set_kP(kp * 0.5f); }
    float get_roll_i() const { return _pid_roll.get_i(); }
```

```lean
/-- C++ `float RateControl::update(float target_roll, float rate_roll, float target_pitch, float rate_pitch, float dt)`, `examples/pid.cpp:205-213`. -/
def update (p : Params) (s : State) (inp : Inputs) (target_roll : Float32) (rate_roll : Float32) (target_pitch : Float32) (rate_pitch : Float32) (dt : Float32) : State × Float32 := Id.run do
  let mut s := s
  let density : Float32 := inp.get_air_density_ratio
  let scale : Float32 := if density > (0.0 : Float32) then (1.0 : Float32) / Float32.sqrt density else (1.0 : Float32)
  let (t'1, t'2) := PID.update_all p._pid_roll s._pid_roll inp._pid_roll target_roll rate_roll dt s._limit (1.0 : Float32)
  s := { s with _pid_roll := t'1 }
  s := { s with _out_roll := t'2 * scale }
  let (t'3, t'4) := PID.update_all p._pid_pitch s._pid_pitch inp._pid_pitch target_pitch rate_pitch dt s._limit (1.0 : Float32)
  s := { s with _pid_pitch := t'3 }
  s := { s with _out_pitch := t'4 * scale }
  s := { s with _limit := decide (Float32.abs s._out_roll > (1.0 : Float32)) || decide (Float32.abs s._out_pitch > (1.0 : Float32)) }
  return (s, s._out_roll + s._out_pitch)
```

From `tests/golden/Shapes.lean`, namespace `Tile`: the override, the inherited `scale_report` (whose
`area()` calls resolve to `Tile.area`; the same function in namespace `Shape` calls `Shape.area`),
and the constructor:

```lean
/-- C++ `float Tile::area() const`, `examples/shape.cpp:102`. -/
def area (s : State) : Float32 := Id.run do
  return Shape.area s * (0.5 : Float32) + Int32.toFloat32 s._rotation

/-- C++ `float Shape::scale_report(float f, float & before)`, `examples/shape.cpp:58-63` (a member of `Shape`, translated for `Tile`). -/
def scale_report (s : State) (f : Float32) (before : Float32) : State × Float32 × Float32 := Id.run do
  let mut s := s
  let mut before := before
  before := area s
  s := scale_float s f
  return (s, before, area s)

/-- C++ `Tile::Tile(float size, int rotation)`, `examples/shape.cpp:100`. -/
def init (size : Float32) (rotation : Int32) : State := Id.run do
  let mut s : State := {}
  s := Shape.init s Kind.Square size
  s := { s with _rotation := rotation &&& (3 : Int32) }
  return s
```

`python3 difftest.py` (all of it also run by `tests/run_tests.sh`, which builds `lean/` from clean):

```
literals: 68 floating literals; 0 elaborate in Lean to bits other than clang's
boost: 10000 input lines (2000 random, 8000 corner) x 3 functions; columns: float#0 float#1 float#2 float#3
boost: 0 of 30000 lines differ (2832 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 1888 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 944 lines
mixed: 10000 input lines (2000 random, 8000 corner) x 11 functions; columns: float#0 float#1 double#0 double#1 bool#0 bool#1 int32_t#0 int32_t#1 int64_t#0 uint8_t#0 uint8_t#1
mixed: 0 of 110000 lines differ (8160 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 3040 lines
  NaN rule: C++ 7ff8000000000001, Lean 7ff8000000000000: 2000 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 1920 lines
  NaN rule: C++ ffc00001, Lean 7fc00000: 800 lines
  NaN rule: C++ fff8000000000000, Lean 7ff8000000000000: 400 lines
motors: 2400 input lines (2000 random, 400 corner) x 1 functions; columns: float#0 float#1
motors: 0 of 2400 lines differ (60 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 40 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 20 lines
numeric: 10000 input lines (2000 random, 8000 corner) x 8 functions; columns: float#0 float#1 float#2 double#0 int32_t#0
numeric: 0 of 80000 lines differ (5112 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 3408 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 1704 lines
pid: 10000 input lines (2000 random, 8000 corner) x 5 functions; columns: float#0 float#1 float#2
pid: 0 of 50000 lines differ (1512 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 1008 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 504 lines
shape: 2240 input lines (2000 random, 240 corner) x 2 functions; columns: float#0 int32_t#0
shape: 0 of 4480 lines differ (36 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 24 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 12 lines
control Hold: 20963 calls on one object (20000 random, 963 corner) over 10 member functions, 6 state leaves per line; inputs: target.x, target.y, target.z, armed, trim
control Hold: 0 of 20964 lines differ (2333 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 2324 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 9 tokens
frame Host: 20500 calls on one object (20000 random, 500 corner) over 12 member functions, 27 state leaves per line; inputs: _gain_configured, lin_expo_configured, read_at, channel_mask_2
frame Host: 0 of 20501 lines differ (6 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 4 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 2 tokens
motors Mixer: 20084 calls on one object (20000 random, 84 corner) over 2 member functions, 1 state leaves per line; inputs: get_lean_max_out, get_lean_max; outputs: set_roll, set_pitch
motors Mixer: 0 of 20085 lines differ (9 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 6 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 3 tokens
motors Attitude: 20170 calls on one object (20000 random, 170 corner) over 2 member functions, 3 state leaves per line; inputs: get_saturation_count, get_saturation_margin, _mixer.get_lean_max_out, _mixer.get_lean_max; outputs: set_throttle_out_throttle, set_throttle_out_apply_angle_boost, set_throttle_out_filt_cutoff, _mixer.set_roll, _mixer.set_pitch
motors Attitude: 0 of 20171 lines differ (13 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 8 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 5 tokens
pid PID: 20504 calls on one object (20000 random, 504 corner) over 11 member functions, 22 state leaves per line; inputs: get_control_gain_scaler
pid PID: 0 of 20505 lines differ (845 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 838 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 7 tokens
pid RateControl: 20280 calls on one object (20000 random, 280 corner) over 4 member functions, 47 state leaves per line; inputs: get_air_density_ratio, _pid_roll.get_control_gain_scaler, _pid_pitch.get_control_gain_scaler
pid RateControl: 0 of 20281 lines differ (867 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 858 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 9 tokens
shape Shape: 20124 calls on one object (20000 random, 124 corner) over 7 member functions, 7 state leaves per line; inputs: none
shape Shape: 0 of 20125 lines differ (579 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 568 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 11 tokens
shape Tile: 20180 calls on one object (20000 random, 180 corner) over 13 member functions, 12 state leaves per line; inputs: none
shape Tile: 0 of 20181 lines differ (824 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 803 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 21 tokens
```

All NaN-rule lines and tokens come from the payload and negative NaN inputs of the corner lists and
from `-x` on NaN. With seeds 1 and 2 and 50000 random lines each, 0 of 638000 (mixed) and 0 of 464000
(numeric) lines differ. Rerunning with the plan's flags only (no `-fno-builtin`) gives the one
`powf` line described under "Compilation assumptions". As a check that the harness detects a wrong
translation, emitting `0.0 - x` for float negation makes `negate` differ on the input lines where x is +0
(C++ 0x80000000, Lean 0x00000000). The class drivers also pass with seeds 7 and 8 (the latter with
50000 calls per class). Translating virtual calls without dispatch (the base's version) makes
`shape Tile` differ on 1767 of 20149 lines, first at line 13.

## Tests

`tests/run_tests.sh` checks: each example (`examples/*.cpp`, with the namespace and options of its
`.json`) translates to exactly `tests/golden/<Namespace>.lean` (and `tests/golden/CppLibm.lean`),
twice with identical output, with no `sorry`/`axiom`/`partial def`; `tests/reject_cases.cpp` (a
pointer parameter, a recursive function, an unbounded `while`), `tests/reject_misc.cpp` (a mutable
global, a `for` with an input bound, `goto`, an uninitialized read, `new`, a `void` function without
effect, mutual recursion, a `for` whose body assigns its counter, `sizeof`) and
`tests/reject_classes.cpp` (translated with the options in its first line: a pointer member, a
call with a variable argument on a boundary object, a mutable static member,
multiple inheritance, a `mutable` member, an `unsigned` bit-field, an overloaded operator, a
`switch` fallthrough, a `break` nested in a case, an enum ordering, an unsupported parameter-class
method, a local object with parameters, a delegating constructor, recursion through a member
function, a destructor with a body, a hiding member, a union, a class template, a reference member)
exit with status 2, print exactly `tests/reject_*.expected`, and the reported lines are exactly the
lines marked `// expect-reject`; `tests/reject_phase3.cpp` (a back-reference member, a `memset` with a
nonzero value, a used result of a `--drop` function, a temporary with parameters, a `--boundary-fn`
call with arguments, a reference member bound to a member, and for boundary outputs: a constructor
that writes outputs, a non-const boundary call with a result, one with a reference parameter, one
without arguments, a const `void` boundary call without reference parameters) likewise; if the
ArduPilot tree is present, `ardupilot/translate_ac_pid.sh`, `translate_ap_math.sh`,
`translate_ap_motors.sh`, `translate_ac_attitude.sh` and `translate_ac_poscontrol.sh` reproduce
`tests/golden/ardupilot/{AC_PID_lib,AP_Math_lib,AP_Motors_lib,AC_Attitude_lib,AC_PosControl_lib}.lean`
exactly, and `ardupilot/check_shared.py` finds the library code of the last two identical in code to
`AP_Math_lib`'s and `AC_PID_lib`'s; `tests/reject_phase3b.cpp` (the limits of the AP_Math and AP_Motors
constructs: a pointer view of `this` that is not a layout prefix, `operator[]` with a variable index, a
non-const call on an object returned by reference, a pointer dereference, a call through a
back-reference, a loop bound assigned in the body, a local reference to a mutable member, a read of a
dropped member, a boundary call with a variable argument inside a loop, a non-const boundary call
whose result is used, a `const char *` without a literal) and `tests/reject_phase3c.cpp` (the limits
of the AC_AttitudeControl and AC_PosControl constructs: a non-const boundary getter not named by
`--boundary-query`, a local reference to a data member of a boundary object, a non-const call on an
object returned by an accessor that does not return one member) as above; `lean/` builds from clean
without warnings; `difftest.py` (every example, `frame` and `control` included, and
`ardupilot/AC_PID`, `ardupilot/AP_Math`, `ardupilot/AP_Motors`, `ardupilot/AC_Attitude`,
`ardupilot/AC_PosControl`) reports 0 differing lines; and, if the recorded flight is there
(`ardupilot/data/oracle-nosincos.txt`), `ardupilot/compose/compose.sh 500` finds the composition equal
to it on every value of 500 ticks. Since the third part, line 36 of `tests/reject_phase3b.cpp` is `(a ? xy() : xy()).zero()`
(a non-const call on `xy()` itself is accepted now), and the message for a local reference names the
third accepted case (a boundary read); `examples/control.cpp` and `tests/golden/Control.lean` cover
what is accepted. In `tests/reject_classes.cpp`, the `break` nested in a case (line 74) is
now `if (k == 0) { break; } else { k++; }`: an early case exit `if (c) { ...; break; }` is accepted since
phase 3, the `else` branch keeps it rejected. `--update` rewrites
the golden and expected files.

Since the fourth part (AC_WPNav, the AHRS view, the vehicles) the suite also checks: `examples/navigate.cpp`
against `tests/golden/Navigate.lean` and in the difftest; `tests/reject_phase3d.cpp` (the limits of the
new constructs: an array of objects of a class outside the `--lib-dir` libraries, `++` on a one-bit
bit-field, a loop from a signed variable start, a loop bounded by a member in a non-const member
function, a reference argument that is an element of a member the callee also reaches, the value of a
dropped static local, a constructor that reads a live boundary, a local reference to a live read with
arguments); `ardupilot/translate_ac_wpnav.sh` and `ardupilot/translate_ahrs_view.sh` against
`tests/golden/ardupilot/AC_WPNav_lib.lean` and `AHRS_View_lib.lean`; the library code of AC_WPNav_lib
against AP_Math_lib's and AC_PosControl_lib's and of AHRS_View_lib against AP_Math_lib's
(`check_shared.py --skip Output,Outputs`: each translation's boundary calls are its own); the difftests
`ardupilot/AC_WPNav` and `ardupilot/AHRS_View`; the build of both vehicles without warnings
(`ardupilot/vehicle/build.sh`); and the replay check (`ardupilot/vehicle/replay.sh`): the two vehicles
bit-identical on every value of every tick of the recorded flight and printing the same parameters.
The flights are not part of the suite (`sim/README.md`).

## Phase 3 survey: what the phase 2 translator rejects in ArduPilot

(Written before phase 3. Every row is resolved: AC_PID in "ArduPilot (phase 3)", AP_Motors in
"AP_Math and AP_Motors", by translation or by `--drop`, `--boundary-call` and `--output-log`.)

Run against the ArduPilot tree (commit 802db19de1) with the reference flags (`-std=gnu++11
-cl-single-precision-constant -fsigned-char`, the `-D`s, `-include ap_config.h`, `-I
ardupilot/stubs`), `--param-class AP_Float=float --param-class AP_Int8=int8_t` (plus `AP_Int16`,
`AP_Int32`, and `"AP_ParamT<float, AP_PARAM_FLOAT>=float"` for template arguments),
`--extern` for the scalar AP_Math functions (`is_zero`, `is_positive`, `is_negative`,
`calc_lowpass_alpha_dt`, `constrain_value_line:AP_Math.constrain_float:3`), and `--keep-going`.

`AC_PID/AC_PID.cpp` with `--header AC_PID/AC_PID.h --header AC_PID/AP_PIDInfo.h --boundary
SlewLimiter,AP_Logger,GroupInfo`: 31 member functions translate (`update_i`, `relax_integrator`,
`set_integrator`, `reset_I`, `reset_filter`, the getters, the setters, the filter alphas, ...).
Rejected:

| where | construct | what phase 3 needs |
|---|---|---|
| `AC_PID.cpp:9`, `AC_PID.h:156` | `var_info`, the `AP_Param::GroupInfo` table (a static array of a class) | skip `var_info` (model the table as the `Params` defaults) |
| `AC_PID.cpp:117` | `AP_Param::setup_object_defaults(this, var_info)` in the constructor | the parameter defaults from `var_info` (or a `Defaults` argument of `init`) |
| `AC_PID.h:44` | the delegating constructor `AC_PID(const Defaults &)` | delegating constructors |
| `AC_PID.cpp:274` | `_slew_limiter.modifier(...)`, a non-const call (SlewLimiter as boundary) | translate `SlewLimiter` (its constructor stores references to two `AP_Float` members of the owner, `AC_PID.h:184`), or an output/stub mechanism; this blocks `update_all` and `update_error` |
| `AC_PID.cpp:393`, `:405` | `AP_Float::load()`, `save()` (`load_gains`, `save_gains`) | out of scope (EEPROM) |
| `AC_PID.h:96-107` | accessors returning `AP_Float &` (`kP()`, `kI()`, ...) | a reference to a parameter returned as its value (`kP (p : Params) : Float32`) |
| `AC_PID.h:149` | `get_pid_info()` returning `const AP_PIDInfo &` | return a const reference as a value |
| `AC_PID.h:153` | `set_notch_sample_rate` (empty with `AP_FILTER_ENABLED=0`) | skip functions without effect instead of rejecting |

`AP_Motors/AP_MotorsMatrix.cpp` with `--header` for `AP_MotorsMatrix.h`, `AP_MotorsMulticopter.h`,
`AP_Motors_Class.h`, `AP_Motors_Thrust_Linearization.h`, `--boundary
SRV_Channels,AP_Logger,GroupInfo,LowPassFilterFloat,DerivativeFilterFloat_Size7,AP_BattMonitor`
(58 rejections; the ones in `AP_MotorsMatrix.cpp`, by line):

| line | construct |
|---|---|
| 20 | `extern const AP_HAL::HAL& hal` (a global reference) |
| 63, 976, 1143, 1194, 1245 | `MAV_TYPE_*` enumerators of the MAVLink enum (not in the translated files) |
| 127, 196, 473, 499 | `rc_set_freq`, `motor_mask_to_srv_channel_mask`, `rc_write`: members of `AP_Motors` defined in `AP_Motors_Class.cpp`, not translated (they write `SRV_Channels`: outputs) |
| 151 | `for (i = 0; i < AP_MOTORS_MAX_NUM_MOTORS; i++)` with `i` declared before the loop (the counter must be declared in the `for`) |
| 217, 459 | `thr_lin.get_compensation_gain()`, defined in `AP_Motors_Thrust_Linearization.cpp`, not translated (add the `.cpp`) |
| 527 | `add_motor_num` (in `AP_Motors_Class.cpp`) |
| 562, 569 | `const MotorDef *` / `const MotorDefRaw *` parameters (motor tables passed by pointer) |
| 579, 778, 857 | `_frame_class_string = "QUAD"` and the like (string literals into `const char *` members) |
| 1364 | the `MAX` macro (a template `MAX<float>`): needs `--extern` |
| 1398 | `_thrust_compensation_callback`, a function-pointer member |
| 1439 | `AP_MotorsMatrix *AP_MotorsMatrix::_singleton` (a static pointer) |

and in the headers: pointer members and singletons (`AP_Motors_Class.h:169`, `:472`,
`AP_MotorsMatrix.h:28`, `:175`), `const char *` frame strings (`AP_MotorsMatrix.h:136-159`,
`AP_Motors_Class.h:450`, `:459`), the anonymous `limit` struct (`AP_Motors_Class.h:406`, `:412`),
`AP_Enum<PWMType>` and `AP_UInt16` parameters (`AP_Motors_Class.h:434`, `:442`; more
`--param-class` entries), `MAV_TYPE` (`:334`, `:444`), the function-pointer type
`thrust_compensation_fn_t` (`AP_MotorsMulticopter.h:85`, `:224`), `var_info` tables
(`AP_MotorsMulticopter.h:120`, `AP_Motors_Thrust_Linearization.h:48`), the `friend` declarations
of `Thrust_Linearization` (`:8-10`), its reference member `AP_Motors& motors` back to its owner
(`:63`), the construction of `thr_lin{*this}` (`AP_MotorsMulticopter.h:117`), non-const calls on the
throttle filter (`AP_Motors_Class.h:200-201`, `LowPassFilterFloat` as boundary), and logging
functions without effect (`Log_Write`, `save_params_on_disarm`).

## Known gaps

- (Fourth part) Live reads (`--boundary-live`): a local reference bound to a live read with arguments
  is rejected; in the difftest a live read's value depends on the number of calls made before it and
  on its arguments, not on the calls' arguments (those are checked in the output log).
- Aliasing of reference parameters is handled for calls of member functions of the same object whose
  reference argument is a data member (or a member of one) that the callee reaches through `this`.
  Two reference parameters bound to one object (`f(a, a)`), and a reference argument that is part of a
  member object whose member function is called, are neither detected nor rejected.
- `for (T i = a; i <= n; i++)` with `n` of the counter's own unsigned type is translated as `n + 1`
  iterations: for `n` at the type's maximum the C++ loop does not terminate.
- The AHRS view: only `update` and `calc_trig` are translated; the view starts zero-filled (its
  constructor, which for ROTATION_NONE without trim leaves `y_angle` and the trim at 0, is not), and
  `get_quat_body_to_ned` (`from_rotation_matrix`) is not translated: both vehicles read the
  estimate's quaternion, as the AHRS stub does.
- AC_WPNav: the Location-based entry points are dropped and the terrain database is compiled out; the
  spline and circle legs are translated and difftested, but the vehicles' mission harness uses
  waypoints only (`MAV_CMD_NAV_WAYPOINT` without delay, the EKF origin always known, no RC input, no
  takeoff, land or RTL, `WP_YAW_BEHAVIOR` 0 to 2). The parameter loaders do not convert the pre-4.7
  `WPNAV_*` names.
- The Lean vehicle evaluates each live read by replaying the navigator's calls of the current member
  function on the position controller's translation: about 0.6 ms per tick on the recorded flight
  (the C++ vehicle: about 0.03 ms).
- Phase 2 items of the plan not implemented: none of the listed constructs is missing. Limits:
  the `Inputs` record is one per class (each member function takes it if it reads any field), not one
  per member function; enums are always emitted with `toInt` (the drivers print enum values through
  it), `ofInt` only when the C++ converts to the enum.
- Outputs: only non-const `void` boundary calls with value arguments; one record per class, holding
  the last values (no call count, no order between two classes writing the same boundary function).
  Boundary getters with reference out-parameters are inputs, but an `Option`-like pairing of the
  result flag with the values is not built: they are independent fields.
- Outputs with `--output-log` are one log per call; the per-class "last values" record remains the
  default without it. Inputs with `--site-inputs` are one per call site, not one per call: a site
  executed twice in one member function reads one value.
- AP_Math types are translated from the ArduPilot sources (`--lib-dir`, `--use`), within each
  translation.
  `Matrix3<T>::to_euler(T *roll, T *pitch, T *yaw)` (`matrix3.h:249`, nullable out-pointers) is
  translated since the fourth part (in AHRS_View_lib), not in AP_Math_lib, where only
  `Matrix3<float>::operator*(Vector3)` of `Matrix3` is translated. Writes through `Vector3<T>::xy()` are translated since the third part; a view is the
  last step of a path (a field of the view is the object's field).
- AP_Motors: the constructors and `add_motors`/`add_motors_raw` are translated but driven only through
  `init` and the `setup_*` functions; the battery code is compiled out with the stub headers
  (`AP_BATTERY_ENABLED` is not defined in `AP_Motors_Thrust_Linearization.cpp`'s translation unit), so its translation is that of an empty function; the dropped members
  (`--drop`) are not part of the model.
- `kP().save()` and `kP().load()` (parameter storage) are left out, as `save()` and `load()`.
- Several translations do not share code: each carries its own translation of the library code it
  uses (`AC_Attitude_lib.Quaternion`, `AP_Math_lib.Quaternion`), checked identical by
  `ardupilot/check_shared.py`, and its own types, so a caller that connects two of them converts
  between their structures (`Compose.lean` builds an `AC_Attitude_lib.Vector3f.State` from the
  position controller's thrust vector).
- The value function of an accessor that returns a reference to a member object (`get_rate_roll_pid()`,
  `NE_get_pos_p()`) returns the member's `State` only, not its `Params`; calls through such an accessor
  inside the translation use the member itself.
- The attitude controller's writes into the motors are a "last values" record: correct for a caller
  that writes every field back through the motors' setters after each call (each setter stores its
  argument or a function of it, and is called at most once per member function, which holds for
  AC_AttitudeControl_Multi), but it does not say which setters a call made. `--output-log` would say
  it, but the motors' setters are inline and non-virtual, so the C++ side of the difftest could not
  record the calls without a stand-in for `AP_Motors`.
- The composition check mirrors the reference harness, not ArduCopter: its navigator outputs come from
  the recorded trace and its AHRS view from the stub (the two vehicles of "AC_WPNav, the AHRS view, and
  the two vehicles" run the translated navigator and view instead).
- Parameter fields are named after the C++ members (`_kp`), not after the `var_info` names (`P`);
  the vehicles' parameter loader maps the names through the `var_info` tables in `signatures.json`.
- `copysignf`, `hypotf`, `ldexpf` and the rest of `<cmath>` not listed in the mapping table are
  rejected (`fmodf`/`fmod` were added in phase 3).
- libc++'s float overloads (`std::sin(float)`, `std::pow(float, float)`, ...) are mapped to the
  `Float32` functions because they call the same libm functions, but they call them as
  `__builtin_sinf`, which `-fno-builtin-sinf`/`-fno-builtin` do not cover, so clang may still fuse or
  simplify them on the C++ side. The examples use the suffixed C functions only.
- The `for`/`while` trip-count rules are syntactic: a loop whose bound is constant only after
  further reasoning (e.g. `i < n` with `n` a non-`const` local that is never assigned) is rejected.
- The definite-assignment check is conservative: assignments inside a loop body or the right operand
  of `&&`/`||`/`?:` do not count after it.
- The operand order of linearized side effects is left to right; this matches clang on this target
  for every sequenced case, and the unsequenced cases are undefined behavior in C++.
- No proof that the translation is correct (translation validation is phase 4); the evidence is the
  syntax-directed construction and the differential test.
