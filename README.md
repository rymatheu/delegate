# cpp2lean

A deterministic, syntax-directed translator from a subset of C++ to executable Lean 4 (phases 0, 1
and 2 of the translator plan: free functions over numbers, then classes; phase 3, ArduPilot's control
classes). The output is
a shallow model: ordinary Lean functions over FloatLib's `Binary32` and `Binary64` (C's `float` and
`double`: IEEE 754 binary32 and binary64 in software, every operation with a specification theorem),
the fixed-width integer types, structures and inductives, written in `do` notation so that they read
like the C++; a class becomes a
namespace with a `State` structure and one function per member function that threads the state. The
model is checked against the C++ by differential execution, bit for bit. No floating-point operation
of the Lean side runs on the FPU or in the C library: the functions of `<math.h>` that IEEE 754
defines exactly are FloatLib operations, and the others (`sinf`, `pow`, ...) are the translation, by
the same translator, of musl's C sources, which the C++ side links instead of the platform's libm
("The C library").

```
file.cpp --clang++ (flags below) -Xclang -ast-dump=json -fsyntax-only--> AST JSON
AST JSON --cpp2lean.py (one handler per clang node kind; rejects everything else)--> Name.lean
Name.lean --lake build (lean/, FloatLib)--> Lean executable      file.cpp + driver --clang++--> C++ executable
musl's math sources --clang (C99) AST--> cpp2lean.py --> Musl/*.lean      the same sources --clang--> linked into the C++
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
    [--boundary-static Class::member]... [--world]
    [--pointer-params] [--runtime-loops] [--c-strings] [--byte-objects] [--gotos] [--hal-storage SIZE]
    [--general-loops] [--uninit-reads] [--module-sig FILE]... [--import Module]...
    [--ekf-types] [--ekf-arrays] [--ring-buffers] [--survey]
    [--world-pointers] [--semaphores C,...] [--heap-alloc F] [--front-ends] [--param-ext]
    [--world-class C,...] [--param-name NAME=path] [--reachable] [--indexed-inputs] [--sizeof C=N]
    [--mavlink] [--null-member C::m]...
```

A file ending in `.c` is C: it is parsed with `clang -x c -std=c99` and the C constructs of "The C
library" are accepted (int-valued conditions and comparisons, unions as bit patterns, pointer
parameters, `goto`); the translator is used this way for musl's math sources only.

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
| `--world` | (Phase 1) the mutable file-scope objects of translated classes are the fields of one `World` structure; reference members between them, singleton accessors and virtual calls on them are resolved at translation time ("Phase 1 of the port", "The World") |
| `--pointer-params`, `--runtime-loops` | (Phase 2) pointer parameters into arrays and loops bounded by runtime values ("Phase 2") |
| `--c-strings`, `--byte-objects`, `--gotos`, `--hal-storage SIZE` | (Phase 2b) C strings, varargs and the text runtime, byte-level objects, forward gotos, the HAL storage ("Phase 2b") |
| `--ekf-types`, `--ekf-arrays`, `--ring-buffers`, `--survey` | (Phase 3) EKF3's data forms: typedef'd and derived structs, unions as views and bit fields, mutable statics in the World; multidimensional arrays, whole-object `memset`/`memcpy`, in-place writes; type-erased ring buffers monomorphized; a survey mode reporting every rejected statement ("Phase 3: EKF data structures") |
| `--front-ends`, `--param-ext`, `--world-class`, `--param-name` | (Phase 3) the sensor front ends' constructs and AP_Param's parameter classes as translated objects ("Phase 3: sensor front ends and AP_Param") |
| `--reachable`, `--indexed-inputs`, `--sizeof C=N` | (Phase 3) translation from the `--use` entry points only, boundary reads indexed by an instance argument as input arrays, clang's `sizeof` of a class ("Phase 3: AP_DAL and NavEKF3") |
| `--mavlink`, `--null-member C::m` | (Phase 4) the MAVLink C library's constructs: file-scope state, struct pointers, packed structs and bit-fields, byte views, constant tables; pointer members that are always null, folded ("Phase 4: the MAVLink C library") |
| `--mission` | (Phase 4, with `--mavlink`) AP_Mission's constructs: unions of members of different types as bytes with member views, signed bit-fields, `case a ... b`, value-initialization of classes, a local pointer to one of several members, `memcpy` of an object through `(void *)&x`, float to 8/16-bit integers as the reference target converts ("Phase 4: AP_Mission") |
| `--boundary-static Class::member` | a member function of a boundary class that reads nothing of its object (`AP_AHRS::calc_trig`): translated as a function of its arguments (named `Class_member`), its calls are calls of it |
| `--general-loops` | loops whose trip count the translator does not compute, and a backward `goto` (C), are loops of at most 2^64 iterations (see "The C library") |
| `--uninit-reads` | a read the definite-assignment check cannot prove to follow an assignment is accepted (the variable starts at zero; C reads it only after assigning it) |
| `--module-sig FILE` | (C) the `signatures.json` of another translation: calls of its functions use that translation (musl's `__rem_pio2f`, called by `sinf`, `cosf`, `tanf`) |
| `--import Module` | a Lean module the output imports (the module of an `--extern` function) |

Writes `OutDir/Name.lean` (a dotted namespace `Musl.sinf` is the module `Musl.sinf`, the file
`OutDir/Musl/sinf.lean`), `OutDir/Name.signatures.json` (the translated free functions and classes
with their C++ signatures, their state leaves and inputs, the enums, and every floating literal with
the bits clang gives it; read by `difftest.py`), and `OutDir/CFloat.lean`, a copy of
`support/CFloat.lean` (the C semantics of floating point that the emitted code names: conversions,
bit patterns, classification, the exact functions of `<math.h>`, each a FloatLib operation; see
"Mapping"). A translation that calls a function of the C library imports its module (`import
Musl.sinf`; "The C library"). Exit status 0 on success; 1 if clang fails; 2 if the file is outside
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

- `cpp2lean.py` (the translator), `difftest.py` (the differential test: driver generator and harness),
  `support/CFloat.lean` (copied next to every translation).
- `examples/`: the demonstration inputs (`numeric`, `mixed`, `boost` for phase 1; `pid` and `shape` for
  phase 2; `motors` for phase 3's boundary outputs; `frame` for the constructs added for AP_Math and
  AP_Motors, with its C++ environment `frame_env.h`; `control` for those added for AC_AttitudeControl
  and AC_PosControl), their configurations `*.json` (namespace, translator options, class-driver
  configuration) and the generated C++ drivers `*_driver.cpp`; `navigate` (with its C++ environment
  `navigate_env.h` and its library directory `navlib/`) for the constructs added for AC_WPNav; `libm`,
  one wrapper per function of the C library the translations call.
- `tests/`: golden output (`tests/golden/`, `tests/golden/ardupilot/`), rejection inputs with their
  expected messages, and `run_tests.sh`.
- `lean/`: the Lean package (`lakefile.toml`, `lean-toolchain` Lean v4.35.0, `lake-manifest.json`;
  it requires FloatLib, pinned at commit `acba2057e452f32f4ed4f06bb0adbeda5342ba92`, and Mathlib
  v4.35.0, FloatLib's dependency, last). It holds
  the translated modules, `CFloat.lean`, the C library's translation `Musl.lean` and `Musl/*.lean`
  (library `MuslLib`), the generated difftest driver `Main.lean` (executable `demo`),
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
  - `standin/` (removed in Phase 1 with the per-class controller translations that used it).
  - `translate_*.sh` with their unity files `unity_*.cpp` and outputs in `out/` (since Phase 1 the
    controllers are `translate_copter.sh`, `unity_copter.cpp`, `out/Copter`), `AP_Math.use`,
    `check_unity.py`, `check_shared.py`, the difftest configurations `*.json` (`Copter.json` for the
    World), the C++ environments `*_env.cpp` (`copter_env.cpp`), `ap_motors_driver.h`,
    `cpp2lean_events.h` and the generated drivers.
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
- `libm/`: the C library (see "The C library"): `musl-1.2.5/` (the musl sources used, unmodified, with
  musl's `COPYRIGHT` and `VERSION`), `env/` (the headers that stand in for musl's build environment:
  `math.h`, `endian.h`, `features.h`, `fp_arch.h`, and `musl_prefix.h` for the reference),
  `unity/` (one translation unit per function, `groups.txt`), `translate_libm.sh` (the translation,
  output `libm/out/Musl/`), `build_musl.sh` (the objects for the C++ side, `build/libm/`),
  `musl_files.txt`.
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
driver is compiled with the plan's flags plus `-fno-builtin` (`CODEGEN_EXTRA` in `cpp2lean.py`). The
reference build of the ArduPilot classes adds `-fno-builtin`
too (`ardupilot/vehicle/build.sh`); without it, any ArduPilot code that calls `powf`/`pow` with a
constant exponent is exposed to the same rewrite.
`-fno-builtin` does not reach calls written as `__builtin_powf`, which is how libc++'s float
overloads `std::pow(float, float)`, `std::sin(float)`, ... are implemented; such a call still calls
the C name (`powf`), which the link binds to musl's function ("The C library").

**Amendment: the C library is musl's, on both sides.** The plan's "same C library on both sides"
was the platform's libm (macOS `libSystem`) called by both. Since the Lean side computes with
FloatLib (below) and must not call into the C library, the C++ side (the difftest drivers, both
vehicles' reference, the composition environment) links musl 1.2.5's math sources, compiled with the
reference flags as C99 (`libm/build_musl.sh`), with every C name of `<math.h>` the code calls bound
to them at link time, and the Lean side runs the translation of the same sources. `build.sh` lists
the math functions `copter_ref` still imports from the platform: none.

Further assumptions specific to the Lean side, all checked on this host (macOS arm64, Apple clang
17, Lean v4.35.0, FloatLib at `acba2057`):

- The C++ side runs in the default floating-point environment (round to nearest, no flush to
  zero). The Lean side computes with FloatLib's software operations (round to nearest even), with
  no FPU instruction and no C library call for a floating-point value: the C code that Lean emits
  for the translations moves 32- and 64-bit words.
- Out-of-range float to integer conversion is undefined in C++; CFloat's `Binary32.toInt32` etc.
  saturate (NaN gives 0), as arm64's `fcvtzs`/`fcvtzu` and core Lean's `Float32.toInt32` do. They
  agree on every in-range value (truncation toward zero).
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
  `__builtin_nanf("")`, `__builtin_inff()`, ... become `Binary32.ofBits 0x7fc00000`, `0x7f800000`,
  checked by the literal check); a `for` counter of a narrow type compared after promotion (a
  `uint8_t i < 12`), if the bound is a value of the counter's type.

Rejected with `file:line:col: rejected: <construct>` and exit status 2 (each line below is a
message the translator prints; phase 3 relaxes some of them, see "AP_Math and AP_Motors"): pointers
(`*`, `new`, `delete`, address-of, dereference, arrays used as pointers, array parameters, function
pointers); references other than parameters and boundary
members (reference members to translated classes, local references, functions returning a
reference); `volatile` other than on a local variable or parameter; `char` types, string and character literals; `long double`; unions (in C++; a C union of numbers of one width is a bit pattern, "The C library");
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
| `float` | `Binary32` (FloatLib's `ExecFloat.Binary 8 23`; at run time a `UInt32` bit pattern) |
| `double` | `Binary64` (FloatLib's `ExecFloat.Binary 11 52`; a `UInt64`) |
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

Literals: an integer literal is `(v : T)` with clang's value and type. A floating literal is its bit
pattern with the C++ spelling in a comment, `(Binary32.ofBits 0x34000000 /- 1.1920929e-7 -/)` (since
Phase 1; before, the decimal `(1.1920929e-7 : Binary32)`, which the compiled code rounded at every
evaluation), and so is a conversion of a constant (`(float)2`, a `double` constant converted to
`float`); the translator computes the bits exactly, and registers the decimal (or the conversion as
written) with them: the difftest elaborates each registered text in compiled Lean and checks that it
gives those bits (FloatLib's `OfScientific` rounds the exact rational once, to nearest even). The
rest of this paragraph is the earlier rule for the registered decimal: `(text :
T)` with the decimal text of the source (suffix removed; `1.` -> `1.0`, `.5` -> `0.5`), or clang's
value text when the literal is spelled inside a macro (`FLT_EPSILON` -> `(1.1920929e-7 : Binary32)`);
hexadecimal literals become `Binary32.ofBits 0x...`/`Binary64.ofBits 0x...`. A `double` literal stays
`Binary64` and the cast clang inserted is emitted. The translator checks that the emitted decimal,
correctly rounded to the literal's type (FloatLib's `OfScientific` instance rounds the exact rational
once, to nearest even), gives the bits of clang's value, and the
difftest checks every emitted literal in compiled Lean against clang's bits. Negative literals are
`-` applied to a literal, as in clang's AST.

Casts (`ImplicitCastExpr`, `CStyleCastExpr`, `CXXStaticCastExpr`, `CXXFunctionalCastExpr`; for an
explicit cast clang puts the conversion in an inner implicit cast):

| castKind | Lean |
|---|---|
| `LValueToRValue`, `NoOp` | nothing |
| `FloatingCast` float -> double / double -> float | `Binary32.toBinary64` (exact) / `Binary64.toBinary32` (nearest even): FloatLib's `Model.cast` |
| `IntegralToFloating` | `IntN.toBinary32`, `UIntN.toBinary32`, `USize.toBinary32` (to float); `.toBinary64` (to double): FloatLib's `ofRat`, nearest even; from `bool`: `if b then 1.0 else 0.0` |
| `FloatingToIntegral` | `Binary32.toIntN`, `Binary32.toUIntN`, `Binary32.toUSize`, and the `Binary64.` ones: FloatLib's `toInt?` (toward zero), saturating outside the range |
| `IntegralCast` | same width: `IntN.toUIntN` / `UIntN.toIntN`; wider or narrower: `IntN.toIntM` / `UIntN.toUIntM` (sign extension, zero extension, truncation), followed by the signedness change when both differ; `USize` through `USize.toUInt64` / `UInt64.toUSize`; from `bool`: `if b then 1 else 0` |
| `IntegralToBoolean`, `FloatingToBoolean` | `x != 0` |
| `IntegralCast` from an enum / to an enum, `IntegralToFloating` from an enum | `E.toInt x`, then the integer conversion / the integer conversion, then `E.ofInt` |
| `UserDefinedConversion` (a parameter class's `operator const float &`) | the parameter's value `p.f` |
| `UncheckedDerivedToBase` (on `this` in a member call or member access) | nothing (the state is flattened) |
| anything else (`ArrayToPointerDecay` outside a subscript, pointer casts, `reinterpret_cast`, `const_cast`, ...) | rejected |

Every integer conversion that exists in core Lean directly is used directly. Missing in core:
`Int32.toUInt8`, `UInt8.toInt32` and the other combined sign-and-width changes (composed from
two existing ones as above), `Int32.toNat` (the subscript uses `Int32.toNatClampNeg`). The
floating-point conversions are the functions of `support/CFloat.lean` named above, each one FloatLib
operation (and a clamp for the conversions to integers).

Operators:

| C++ | Lean |
|---|---|
| `+ - * /` | `+ - * /` (the operand types are equal after clang's conversions) |
| `%` (integers) | `%` (`Int32` `%` is `BitVec.srem`, sign of the dividend, like C++; checked: `-7 % 2 = -1`, `7 % -2 = 1`) |
| `/` (integers) | `/` (`Int32` `/` truncates toward zero like C++; checked: `-7 / 2 = -3`, also `Int8`, `Int64`) |
| `== !=` | `== !=` (`BEq`: for `Binary32`/`Binary64` FloatLib's `compareEqual`, IEEE equality) |
| `< <= > >=` | `< ≤ > ≥`, as a decidable proposition in an `if` or `?:` condition, else `decide (...)` (FloatLib's IEEE order: false on NaN) |
| `&& \|\| !` | `&& \|\| !`; with side effects in the right operand: `let mut t := a; if t then (effects; t := b)` |
| `& \| ^ ~ << >>` | `&&& \|\|\| ^^^ ~~~ <<< >>>` (`>>>` on `IntN` is arithmetic; checked); the shift count is converted to the left operand's type |
| unary `-` | `-x`, FloatLib's `Neg` (`Model.neg`), C negation (flips the sign bit, of a zero and of a NaN too); never `0 - x` |
| `c ? a : b` | `if c then a else b`; with side effects in a branch: a `let mut` temporary assigned in an `if` statement |
| `x = e`, `x op= e`, `++x`, `x++` | `x := e`; `x := conv(conv(x, T->L) op e, R->T)` with clang's `computeLHSType` L and `computeResultType` R; `x := x + 1`; post-increment as a value: `let t := x; x := x + 1`, value `t` |

Do not use `≠` for floats: FloatLib's `DecidableEq` on `Binary32`/`Binary64` is structural equality
of the bit pattern, so `decide ((0.0 : Binary32) ≠ -0.0) = true` and `decide (NaN ≠ NaN) = false`,
both the opposite of C++ `!=`. The translator only emits `==`/`!=`.

Side effects are linearized in clang's evaluation order: operands left to right (the order clang
uses on this target; C++17 sequences the right operand of an assignment before the left). When a
later operand has side effects, the values of the earlier operands are first bound to temporaries,
so they are read before the effects happen.

`<cmath>` (the C name, or libc++'s overload of the unsuffixed name for `float`, or the `double`
function). The functions IEEE 754 defines exactly are FloatLib operations (`support/CFloat.lean`),
checked against C's definitions case by case; the others are the translation of musl's sources (the
module `Musl.f` of function `f`; "The C library"):

| C++ | Lean |
|---|---|
| `sqrtf fabsf floorf ceilf truncf roundf` / `sqrt fabs floor ceil trunc round` | `Binary32.sqrt abs floor ceil trunc round` / `Binary64.`: FloatLib's `sqrt` (correctly rounded), `abs` (clears the sign bit, of a NaN too, as C's `fabs`), `roundToIntegral` with `.down`, `.up`, `.towardZero`, `.nearestAway` (C's `round` rounds halfway cases away from zero; every mode keeps the sign of a zero result, `floor(-0.5)` is `-1`, `ceil(-0.5)` is `-0`) |
| `fminf fmaxf` / `fmin fmax` | `Binary32.fmin fmax` / `Binary64.`: FloatLib's IEEE 754-2019 `minimumNumber`/`maximumNumber`: the number if one operand is a NaN (C99 F.10.9.2), `-0` below `+0` (C leaves the order of zeros open; musl orders them so); FloatLib's `min`/`max` instances (`minimum`/`maximum`, which propagate NaN) are not C's |
| `copysignf scalbnf ldexpf` / `copysign scalbn ldexp` | `Binary32.copysign scalbn` / `Binary64.`: FloatLib's `copySign`, `scale` (IEEE scaleB, one rounding) |
| `__builtin_fma` (C, musl's `log` and `pow` on arm64) | `Binary64.fma`: FloatLib's `fma` |
| `sinf cosf tanf asinf acosf atanf atan2f expf logf powf fmodf` | `Musl.sinf.sinf`, ..., `Musl.fmodf.fmodf` |
| `sin cos tan asin acos atan atan2 exp log pow fmod` (double) | `Musl.sin.sin`, ..., `Musl.fmod.fmod` (`fmod` is exact, but FloatLib has only IEEE `remainder`) |
| `isnan isinf isfinite` (`std::` or not; libc++ `bool (float)`/`bool (double)`), C's `__builtin_isnan`, `__builtin_signbit` | `Binary32.isNaN isInf isFinite signbit` / `Binary64.` |
| `abs(float)`, `abs(double)` | `Binary32.abs` / `Binary64.abs` |

The other functions of `<math.h>` (`log10f`, `exp2f`, `sinhf`, `hypotf`, ...) are rejected; translating
one is adding its musl file to `libm/unity/groups.txt` and its name to the table.

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
  (s : State) (dt : Binary32) (limit : Bool) : State` and `get_i (s : State) : Binary32` are AC_PID's
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

**Since Phase 1 of the port** (below, "Phase 1 of the port"): AP_MotorsMatrix, AC_AttitudeControl_Multi,
AC_PosControl and AC_WPNav are no longer four translations with boundaries between them but one World
translation (`ardupilot/translate_copter.sh`, `Copter_lib`), difftested as one (`ardupilot/Copter`).
The sections below describe the constructs added for them, which the translator keeps, and the
per-class translations and difftests of that time (`translate_ap_motors.sh`, `translate_ac_attitude.sh`,
`translate_ac_poscontrol.sh`, `translate_ac_wpnav.sh`, their configurations, C++ environments and
stand-ins), which were removed; the live boundary reads (`--boundary-live`) were removed too.

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
  value functions (`kP (p : Params) : Binary32`); a const and a non-const overload that return the
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
ardupilot/AC_PID AC_PID: 0 of 21049 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P: 20040 calls on one object (20000 random, 40 corner) over 3 member functions, 2 state leaves per line; inputs: none
ardupilot/AC_PID AC_P: 0 of 20041 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P_1D: 20180 calls on one object (20000 random, 180 corner) over 8 member functions, 6 state leaves per line; inputs: none
ardupilot/AC_PID AC_P_1D: 0 of 20181 lines differ (152 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_PID_Basic: 20450 calls on one object (20000 random, 450 corner) over 30 member functions, 33 state leaves per line; inputs: none
ardupilot/AC_PID AC_PID_Basic: 0 of 20451 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_PID_2D: 20880 calls on one object (20000 random, 880 corner) over 32 member functions, 51 state leaves per line; inputs: none
ardupilot/AC_PID AC_PID_2D: 0 of 20881 lines differ (376 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PID AC_P_2D: 20180 calls on one object (20000 random, 180 corner) over 7 member functions, 6 state leaves per line; inputs: none
ardupilot/AC_PID AC_P_2D: 0 of 20181 lines differ (112 tokens equal only as NaN vs NaN with different bits)
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
the translation is `Binary64.toBinary32 (Musl.sin.sin ((0.5 : Binary64) * Binary32.toBinary64 theta))`.

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
- `fmodf`/`fmod` (since the FloatLib port musl's, `Musl.fmodf.fmodf`), and libc++'s mixed `float`/`double`
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
ardupilot/AP_Math free functions: 0 of 24491 lines differ (152 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<float>: 21420 calls on one object (20000 random, 1420 corner) over 25 member functions, 2 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector2<float>: 0 of 21421 lines differ (36 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<double>: 21260 calls on one object (20000 random, 1260 corner) over 22 member functions, 2 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector2<double>: 0 of 21261 lines differ (36 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<float>: 22320 calls on one object (20000 random, 2320 corner) over 27 member functions, 3 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector3<float>: 0 of 22321 lines differ (90 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<double>: 21820 calls on one object (20000 random, 1820 corner) over 22 member functions, 3 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Vector3<double>: 0 of 21821 lines differ (42 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Matrix3<float>: 20240 calls on one object (20000 random, 240 corner) over 1 member functions, 9 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math Matrix3<float>: 0 of 20241 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math QuaternionT<float>: 23040 calls on one object (20000 random, 3040 corner) over 26 member functions, 4 state leaves per line (set from the line before each call); inputs: none
ardupilot/AP_Math QuaternionT<float>: 0 of 23041 lines differ (306 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (linear): 24710 calls on one object (20000 random, 4710 corner) over 126 member functions, 396 state leaves per line; inputs: micros, have_digital_outputs, get_output_channel_mask_k_boost_throttle, _pwm_min_configured, _pwm_max_configured, motor_mask_to_srv_channel_mask, thr_lin.get_air_density_ratio
ardupilot/AP_Motors AP_MotorsMatrix (linear): 0 of 24711 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (defaults): 24710 calls on one object (20000 random, 4710 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (defaults): 0 of 24711 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (frames): 25869 calls on one object (20000 random, 5869 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (frames): 0 of 25870 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Motors AP_MotorsMatrix (spool): 25905 calls on one object (20000 random, 5905 corner) over 126 member functions, 396 state leaves per line; inputs: (as above)
ardupilot/AP_Motors AP_MotorsMatrix (spool): 0 of 25906 lines differ (0 tokens equal only as NaN vs NaN with different bits)
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
ardupilot/AC_Attitude AC_AttitudeControl_Multi (defaults): 0 of 36691 lines differ (115634 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_Attitude AC_AttitudeControl_Multi (tuned): 36690 calls on one object (20000 random, 16690 corner) over 124 member functions, 275 state leaves per line; inputs: (as above)
ardupilot/AC_Attitude AC_AttitudeControl_Multi (tuned): 0 of 36691 lines differ (115634 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PosControl AC_PosControl (defaults): 40205 calls on one object (20000 random, 20205 corner) over 144 member functions, 237 state leaves per line; inputs: get_relative_position_NED_origin_vec.x, get_relative_position_NED_origin_vec.y, get_relative_position_NED_origin_vec.z, get_relative_position_NED_origin, get_relative_position_D_origin_float_posD, get_relative_position_D_origin_float, get_velocity_NED_vec.x, get_velocity_NED_vec.y, get_velocity_NED_vec.z, get_velocity_NED, get_vert_pos_rate_D_velocity, get_vert_pos_rate_D, get_ang_vel_roll_max_rads, get_ang_vel_pitch_max_rads, get_accel_roll_max_radss, get_accel_pitch_max_radss, get_bf_feedforward, millis, get_att_target_euler_rad.x, get_att_target_euler_rad.y, get_att_target_euler_rad.z, ticks32, yaw, get_althold_lean_angle_max_rad, lean_angle_max_rad, get_position_NE_reset_count, has_good_timing, get_control_gain_scaler_XY, cos_yaw, sin_yaw, get_accel_ef.x, get_accel_ef.y, get_accel_ef.z, get_throttle_in, get_throttle_hover, get_position_D_reset_count, get_control_gain_scaler_Z, limit_throttle_lower, limit_throttle_upper, _pid_accel_d_m._slew_limiter.millis
ardupilot/AC_PosControl AC_PosControl (defaults): 0 of 40206 lines differ (124031 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_PosControl AC_PosControl (tuned): 40205 calls on one object (20000 random, 20205 corner) over 144 member functions, 237 state leaves per line; inputs: (as above)
ardupilot/AC_PosControl AC_PosControl (tuned): 0 of 40206 lines differ (124031 tokens equal only as NaN vs NaN with different bits)
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

Before the FloatLib port, with the platform's libm on both sides:

```
$ ardupilot/compose/compose.sh            # 500 ticks
composition: 500 ticks; actuators bit-identical to the oracle on 500 of 500 ticks; all 22 values on 500 of 500 ticks
$ ardupilot/compose/compose.sh 8431       # the whole flight
composition: 8431 ticks; actuators bit-identical to the oracle on 8431 of 8431 ticks; all 22 values on 8431 of 8431 ticks
```

Since the port the composition and its environment run musl's functions ("The C library"), while the
oracle was recorded with the platform's libm, by a harness that is not part of this repository; the
comparison now shows where the two libraries' last bits change the flight:

```
$ ardupilot/compose/compose.sh
composition: 500 ticks; actuators bit-identical to the oracle on 500 of 500 ticks; all 22 values on 495 of 500 ticks
  first difference at tick 491: roll_t oracle 39829d21 Lean 39829d22
$ ardupilot/compose/compose.sh 8431
composition: 8431 ticks; actuators bit-identical to the oracle on 532 of 8431 ticks; all 22 values on 502 of 8431 ticks
  first actuator difference at tick 510
  first difference at tick 491: roll_t oracle 39829d21 Lean 39829d22
```

The suite (`tests/run_tests.sh`) requires the 500 ticks' actuators. The bit-exact check of the
translated classes against the compiled ones on this flight is the replay check of the two vehicles
("The two vehicles"), where both sides run musl's functions.

Before the port, with single-precision trig substituted in the attitude translation (`CPP2LEAN_MUTATE`, applied to
`AC_Attitude_lib.lean`), the 500-tick check still passes on the actuators (they first differ at tick
503) but not on all values (the roll body-rate target differs at tick 496, 0x3de6bd69 vs 0x3de6bd68);
over the flight the actuators differ on 7082 ticks, and the output equals the recorded diagnostic
variant `ardupilot/data/oracle-diag-floattrig.txt` (single-precision `from_axis_angle`) on all 8431
ticks.

## AC_WPNav, the AHRS view, and the two vehicles

(The live reads described in this section, `--boundary-live`, were removed in Phase 1: the navigator and the position controller are objects of one World; see "Phase 1 of the port".)

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
  terrain_scaler_D_m : Outputs → Binary32 → Binary32 → Binary32 := fun _ _ _ => (0.0 : Binary32)
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
ardupilot/AC_WPNav AC_WPNav (defaults): 0 of 47762 lines differ (6739 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_WPNav AC_WPNav (course): 47761 calls on one object (20000 random, 27761 corner) over 65 member functions, 577 state leaves per line; inputs: (as above)
ardupilot/AC_WPNav AC_WPNav (course): 0 of 47762 lines differ (238 tokens equal only as NaN vs NaN with different bits)
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
ardupilot/AHRS_View AP_AHRS_View: 0 of 21097 lines differ (0 tokens equal only as NaN vs NaN with different bits)
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
  `ardupilot/stubs/oracle_env.cpp` and with musl's math functions ("The C library"; the build prints
  the math functions the binary imports from the platform's libm: none). The AHRS view is the stub,
  which derives the angles and their trigonometry from the sample as `AP_AHRS_View::update` does.
- `copter_lean` (`lean/Vehicle.lean`, `lean/VehicleMain.lean`): the World translation `Copter_lib`
  (since Phase 1; before, the four translations AP_Motors_lib, AC_Attitude_lib, AC_PosControl_lib and
  AC_WPNav_lib wired by hand, with the navigator's live reads) and AHRS_View_lib, the harness setting
  the objects' boundary inputs and calling the World;
  every number a `Binary32` or `Binary64`, also in the harness (input parsed with FloatLib's
  `OfScientific`, output printed from the bit patterns).

The harness (the same functions, in the same order and with the same names, in both files): input
parsing (correctly rounded: `strtod`/`strtof`, FloatLib's `OfScientific`) and exact printing; parameters by ArduPilot name through the classes' own var_info tables
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
With the navigator's targets taken from the recording instead, the same classes reproduced
`oracle-nosincos.txt` exactly with the platform's libm (the composition check, above), and with
musl's functions up to the last bits from tick 491 on.

**Flights** (`sim/fly.sh`, `sim/README.md`, `sim/RESULTS.md`): hover, the 1 m/s figure-eight course and
the course at ArduPilot's default speed, each flown with both vehicles in gym-pybullet-drones: on every
tick of the three missions (4000, 7797 and 6325 ticks) the actuators, the simulator's states and all 22
values are bit-identical between the two vehicles. Against the flights flown before the FloatLib port
(both vehicles then called the platform's libm), the musl flights first differ at tick 2817 (hover),
569 (course at 1 m/s) and 561 (default speed), when a trigonometric value differs in the last bit;
over the flights the vehicle's position differs by at most 0.005 µm, 22 µm and 15 µm, the
actuators by at most 6e-8, 5.4e-4 and 3.6e-4, the attitude by at most 0.17 mrad; the tick counts, the
end conditions and the summary numbers of `sim/RESULTS.md` (tracking error, final position, waypoint
times) are the same to the printed precision.

**Speed.** `--bench` (sim/BENCH.md: the ticks alone, inputs parsed beforehand), on the recorded flight
(8431 ticks, this machine, 2026-11-11):

| vehicle | ms per tick |
|---|---|
| `copter_ref` (C++, musl) | 0.0011 |
| `copter_lean` before the port (Lean `Float32`/`Float`, platform libm) | 0.0098 (0.021 to 0.028 under load) |
| `copter_lean` with FloatLib and the temporary libm bridge | 3.14 |
| `copter_lean` with FloatLib and musl's translation | 2.88 |

In lock-step (`ardupilot/data/inputs.txt` one line at a time through a pipe, parsing and printing
included) `copter_lean` takes 3.11 ms per tick on average, median 3.01 ms, 99th percentile 3.38 ms, the
first tick 0.78 s (process start: the module initializers of Mathlib and FloatLib); all but that one
of the 8431 ticks exceed the 2.5 ms period of the 400 Hz loop. A sample profile of the ticks:
FloatLib's comparisons (`<`, `≤`, `==`: `Model.compare` aligns two dyadics with GMP big integers, about
2 µs each) take 50% of the time, the rounding of a rational (a literal such as `(1.1920929e-7 :
Binary32)`, which the compiled code rounds at every evaluation, about 1.2 µs, and the conversions of
integer constants `Int32.toBinary32 (2 : Int32)`, about 0.6 µs) 36%, arithmetic (`+ - * /`, `sqrt`:
FloatLib's word kernels, 7 to 20 ns) 2%, musl's functions 3%, the rest (structures, arrays, the
translated control flow) 11%; by caller, AC_WPNav's update 18% and the replay of its live reads on the
position controller 18% (overlapping). Conversions between float and double (about 0.5 µs) and to
integers (0.8 µs) also go through rationals. Options, none of which changes a result: (1) emit
literals and conversions of integer constants as the bit patterns the translator already checks
(`Binary32.ofBits 0x34000000`), measured 1.91 ms per tick with the same checksum; (2) word-level
comparisons and float/double/integer conversions on the bit patterns (a few ns each instead of µs),
with a proof that they equal FloatLib's specifications, in CFloat or upstream in FloatLib; with (1)
this is estimated at about 0.5 ms per tick (removing the 50% the comparisons take from 1.91 ms); (3) caching the position controller replayed for the
navigator's live reads within a call (the harness re-runs the logged calls for each read).



## Phase 1 of the port: speed, the World, streaming input (2026-11-11)

PORT-PLAN.md section 6, "Phase 1": the translator changes that the rest of ArduCopter needs, in the
order that unblocks the most. What changed in the translator's model is described here; what Phase 1
found wrong in the plan is marked "Phase 1:" in PORT-PLAN.md.

### Speed

`copter_lean --bench` on the recorded flight (`ardupilot/data/inputs.txt`, 8431 ticks,
`copter-cf2x.txt` + `copter-course-speed.txt`; one process per measurement, the ticks alone), each
step on top of the previous one; the checksum (the sum of the actuators' bit patterns) is
`000019b902683da2` at every step, and `ardupilot/vehicle/replay.sh` gives 8431 of 8431 ticks
bit-identical after each:

| step | ms per tick |
|---|---|
| before (FloatLib, musl's translation) | 2.79 to 2.86 |
| floating literals and conversions of constants emitted as checked bit patterns | 1.71 |
| comparisons `<`, `≤`, `==` (and `fmin`, `fmax`, float to double) on the bit patterns, proved equal to FloatLib's (`@[csimp]`) | 0.158 |
| the navigator's live-read replay: the position controller's inputs computed once per replay, an empty log not replayed, the harness's literals as bit patterns | 0.138 |
| the World (below): no replay at all, the controllers call each other | 0.096 |
| the World with AC_Loiter and AC_Circle added (six objects) | 0.095 |

`copter_ref` (C++) takes 0.0011 ms per tick on the same flight. The 400 Hz budget is 2.5 ms.

- **Literals.** A floating literal is emitted as its bit pattern with the C++ spelling in a comment,
  `(Binary32.ofBits 0x34000000 /- 1.1920929e-7 -/)`, instead of `(1.1920929e-7 : Binary32)`, which
  the compiled code rounded from its rational at every evaluation. A conversion of a constant
  (`(float)2`, a `double` literal converted to `float`, one IEEE operation on two constants such as
  `M_PI / 2` converted to `float`) is computed by the translator (exact rational arithmetic, one
  rounding per operation, as C) and emitted the same way; a result that might be `-0` is not folded.
  The checks are kept: every literal and every folded conversion is registered with its decimal or
  its conversion as written (`(1.1920929e-7 : Binary32)`, `Int32.toBinary32 (2 : Int32)`), and the
  difftest evaluates that text in compiled Lean and compares it with the emitted bits ("literals: N
  floating literals; 0 elaborate in Lean to bits other than clang's").
- **Comparisons** (`support/CFloat.lean`). `Binary32.blt`, `ble`, `beq` (and the `Binary64` ones)
  are defined as FloatLib's `compareLess`, `compareLessEqual`, `compareEqual`; the `Decidable (x <
  y)`, `Decidable (x ≤ y)` and `BEq` instances of high priority are definitionally FloatLib's (checked
  by `rfl`), so `x < y` means what it meant. Each has a `@[csimp]` theorem, `@Binary32.blt =
  @Binary32.bltImpl`, whose right side works on the bit pattern: NaN test `0x7f800000 < (b &&&
  0x7fffffff)`, then FloatLib's `adjacencyRank` (the signed-magnitude order) computed in `UInt32` /
  `UInt64`. The proofs use FloatLib's `Model.compare_eq_of_toEReal?` and
  `adjacencyRank_lt_adjacencyRank_iff`/`_eq_iff`; `#print axioms` gives `propext`,
  `Classical.choice`, `Quot.sound` only; no `implemented_by`, `sorry` or `native_decide`.
  `fmin`/`fmax` and `Binary32.toBinary64` (normal numbers and zeros on the bits, the rest through
  FloatLib's cast) have their own `@[csimp]` theorems. `Binary64.toBinary32`, integer to float
  (`ofRat`) and float to integer (`toInt?`) followed in Phase 3 ("Phase 3: conversions on the bit
  patterns, `log2f`" below).

### The World (`--world`, PORT-PLAN.md D1)

With `--world` the file-scope objects of translated classes in the translated files are one Lean
`structure World`, and the per-class wiring of the earlier phases (`Inputs` filled by hand from other
classes, `Outputs` written back through setters, live reads replaying a log) is gone between
translated classes.

- **Fields.** For each object `g` of class `C`: `g : C.State`, `g'p : C.Params` if `C` has
  parameters, `g'inp : C.Inputs` if `C` reads the boundary, `g'o : C.Outputs` if it writes the
  boundary (without `--output-log`). `World.init` constructs the objects in definition order (C++
  static initialization), each with its constructor and constant arguments. An `extern` declaration
  of a World object (a cycle between objects needs one) names the definition below it.
- **References between objects.** A reference member of a translated class (`AC_PosControl&
  _pos_control`) is bound, through the constructor that builds each World object and its base
  constructors, to a constructor argument naming another World object; the translator follows that
  binding and the member becomes that object's path in the World (`w.pos_control`). A class whose
  two objects bind a reference to different objects is rejected; a class with references but no
  World object of its own is translated only as the class of a World object (its base-class methods
  are translated for the derived class, as before).
- **Calls.** A member function that reaches another object takes `(w : World)` after `s` and, if it
  changes the World, returns it after `State` (binder order `p s w o r' inp`, result order
  `Params State World Outputs ...`). A call on another object passes that object's `'p`, state, the
  World if the callee needs it, `'o`, `'inp`, and stores the callee's World first, then the
  object's own parts. A virtual call through a reference to a base class resolves to the object's
  class (the World object's class is known), so `AC_WPNav`'s `const AC_AttitudeControl&` calls
  `AC_AttitudeControl_Multi`'s overriders. A getter that returns a member of another object
  (`get_pos_offset_NED_m()`) is that member's path; a `const T &` local bound to it is an alias of
  that path, so each use reads the World as it is then (AC_WPNav.cpp:572); a parameter of another
  object (`_pos_control.NE_get_pos_p().kP()`) is its `'p` path.
- **The caller's own object.** While a member function of World object `g` runs, `g`'s state is in
  its local `s`, not in the World: a call that reaches `g` through the World (directly or through
  its callees) is rejected ("call ... that reaches `g` (this object) through the World"), and so is
  a constructor that reaches another World object.
- **Singletons.** `static C *_singleton` with `_singleton = this;` in the constructor (AP_RTC.cpp:15-25),
  `static C *get_singleton() { return _singleton; }`, `C &AP::c() { return *C::get_singleton(); }`,
  and a file-static object with an accessor (`static AP_InternalError instance;` and
  `AP::internalerror()`, AP_InternalError.cpp:15, :110): the accessors are not translated; a call of
  one is the path of the class's one World object; `_singleton = this` is no operation; a
  comparison of the pointer with `nullptr` is `false` (it is null) in that object's constructor
  before the assignment and `true` everywhere else, since `World.init` runs the constructors before
  anything else. Rejected: any other assignment to the pointer, a class with zero or several World
  objects, other uses of the pointer value.
- **The boundary** stays as it was: a `--boundary` object's reads are `Inputs` fields and its writes
  `Outputs` (or `Output` events with `--output-log`), now per World object (`g'inp`), set by the
  caller (the vehicle harness from the input line and the AHRS view; the difftest from the line).
  `--boundary-live`, the per-class model's emulation of a translated neighbor (the navigator's reads
  of the position controller as functions of the call log), is removed with its machinery
  (`is_live`, `live_read`, the `olive` component, the difftest's live functions), as are the four
  separate controller translations that needed it.

`ardupilot/unity_copter.cpp` defines the controllers as ArduCopter's `Copter::allocate_motors`
builds them (system.cpp:387-497): `AP_MotorsMatrix motors(400)`, `AC_AttitudeControl_Multi
attitude_control(view, motors)`, `AC_PosControl pos_control(view, motors, attitude_control)`,
`AC_WPNav wp_nav(view, pos_control, attitude_control)`, `AC_Loiter loiter_nav(view, pos_control,
attitude_control)`, `AC_Circle circle_nav(view, pos_control)`, on the AHRS view stub as the
boundary. `ardupilot/translate_copter.sh` translates it into `ardupilot/out/Copter/Copter_lib.lean`
(11,734 lines; the four separate translations of AP_Motors, AC_AttitudeControl, AC_PosControl and
AC_WPNav were 12,503 lines and carried four copies of the library code). Its library code is
identical to AP_Math_lib's and AC_PID_lib's (`check_shared.py`: 141 and 106 shared declarations, 0
differ). The vehicle (`lean/Vehicle.lean`) and the composition check (`ardupilot/compose`) now set
the objects' `'inp` from the line and the view and call the World; they no longer wire objects to
each other.

Differential test: `python3 difftest.py ardupilot/Copter` (`ardupilot/Copter.json`,
`ardupilot/copter_env.cpp`) drives every public member function of the six objects (512 member
functions; the setups, parameter runs, ranges, domains, unit quaternions and monotonic clocks of the
four old per-class configurations), sets every object's boundary inputs from the line (one token
for a value several objects read: the AHRS view's `yaw` is read by four objects), records the
motors' HAL calls in the output log on both sides, and prints every leaf of every object (1524 per
line) after every call:

```
ardupilot/Copter World (defaults): 0 of 46778 lines differ
ardupilot/Copter World (tuned): 0 of 43690 lines differ
ardupilot/Copter World (course): 0 of 21451 lines differ
ardupilot/Copter World (linear): 0 of 21683 lines differ
ardupilot/Copter World (frames): 0 of 22234 lines differ
ardupilot/Copter World (spool): 0 of 21687 lines differ
```

A mutation of the navigator (`0.05f` to `0.06f` at AC_WPNav.cpp:589) makes 37,627 of 45,982 lines of
the defaults run differ; `MAX` to `MIN` in what the attitude controller passes to the motors'
`set_throttle_avg_max` makes 20,505 differ, first on a motors leaf after an attitude-controller
call. Not reproduced from the four old per-class tests: the random values the old stand-ins gave the
cross-class reads (now World state), the old corner counts of the cross-class inputs, and the
bodies of the motors' `--boundary-call` HAL functions (`rc_write`, `rc_set_freq`), which the C++
driver overrides as before. `examples/world.cpp` (with `tests/golden/Worlds.lean`) and
`examples/navigate.cpp` (now two World objects, the planner translated) cover the constructs;
`tests/reject_world.cpp` the limits.

Not done in the World (PORT-PLAN F1-F4 beyond the above): pointer members and pointer variables to
World objects (`Mode *flightmode` and a dispatch over the closed set of modes, `GCS_MAVLINK *`
channels), calls through member pointers and functors (the scheduler's task table), init-time heap
objects (`new` in `allocate_motors`; here the objects are file-scope), arrays of World objects (EKF3
cores, RC channels), objects that are members of a World object reached by an accessor (ArduPilot's
singletons are members of `copter`, so the accessor search must look inside World objects).

### Streaming AST input (PORT-PLAN.md D13)

clang's JSON dump goes to a temporary file. Dumps under 64 MB are read whole as before; larger ones
are streamed in two passes: pass 1 reads the file in 32 MB blocks without building the tree and
records, for every declaration at file scope and inside namespaces and `extern "C"` blocks, its byte
span, its file, the location state clang elides (carried in document order), the declaration ids it
defines and the ids it mentions; the declarations in the translated files, the `--header` files and
the `--lib-dir` libraries, closed under "mentions an id defined in", redeclarations and the
enclosing containers, are then decoded with `json.JSONDecoder.raw_decode` and given the location
state they would have had. `CPP2LEAN_AST=whole|stream` forces a mode. The output is byte-identical
to reading the whole dump on all 26 translations of the suite (examples, rejection tests, the
ArduPilot translations, musl). With ArduPilot's real headers: AC_Loiter + AC_Circle (1.02 GB of JSON)
in 9.4 s and 308 MB resident (930 of 13,116 declarations decoded, 1.5 MB of the MAVLink text);
`AP_NavEKF3_core.cpp` (1.07 GB) in 9.1 s and 546 MB. Limits: a lookup by name of a declaration that
is neither in the translated files nor mentioned by id would not find it (the translator does none);
the reader relies on clang's two-space layout with `id` and `kind` first and `inner` last, and falls
back to the whole read otherwise.


## Phase 2: the value-like leaf libraries


Translated from ArduPilot's unmodified sources (commit 802db19de1), each checked bit for bit against
the C++ compiled with the reference flags by `difftest.py`:

| library | script (output) | Lean lines | what |
|---|---|---|---|
| AP_Math rest | `ardupilot/translate_ap_math.sh` (`out/AP_Math/AP_Math_lib.lean`) | 5046 (was 1668) | `matrix_alg.cpp` (`mat_inverse`, `mat_mul`, `mat_identity` and the static `inverse3x3`, `inverse4x4`, `mat_inverseN`, `mat_LU_decompose`, `mat_pivot`, `mat_forward_sub`, `mat_back_sub`, `matrix_multiply`, at float and double), every function of `crc.cpp`, `location_double.cpp` (`wgsllh2ecef`, `wgsecef2llh`), `div1000.h`, the rest of `matrix3.cpp` and `quaternion.cpp` at float and double (`from_rotation_matrix`, `from_rotation`, `rotate(Rotation)`, `to_euler`, `from_euler312`, `normalize`, `inverse`, ...), `Vector3::rotate`/`rotate_inverse` |
| LowPassFilter2p | `ardupilot/translate_lowpassfilter2p.sh` | 962 | `DigitalBiquadFilter<T>`, `LowPassFilter2p<T>` at int, long, float, Vector2f, Vector3f |
| AC_CommandModel | `ardupilot/translate_ac_commandmodel.sh` | 72 | the class, its three parameters and their `var_info` defaults |
| AP_Declination | `ardupilot/translate_ap_declination.sh` | 273 | `get_mag_field_ef`, `get_declination`, `get_earth_field_ga`, the three 19x37 tables |
| AP_Common | `ardupilot/translate_ap_common.sh` | 1115 | `Location` (without its AHRS, panic and object-representation members, below), `Bitmask<N>` at N = 32, 102, 190, 317, 634 |

The translations follow the reference vehicle's configuration where the stub configuration differs:
`AP_CUSTOMROTATIONS_ENABLED 0` and `AP_TERRAIN_AVAILABLE 0` (reference/cfg/ref.hwdef:67, :84), on both
sides of the difftest. `fedisableexcept`/`feenableexcept` (`inverse4x4` under SITL) only change the
floating-point trap mask, which the model does not have (the default environment, "Compilation
assumptions"): `--drop`, and their value, read only by conditions of empty statements, is left out
with them (below).

**Location.** Left out with `--drop` (a call whose result is used is rejected): the members that read
the AHRS singleton (`AP::ahrs()`: home and EKF origin): the constructors from an EKF offset,
`from_ekf_offset_NED_m`, `get_alt_cm`, the `get_vector_*` templates; `get_alt_frame` and
`linearly_interpolate_alt`, which call `AP_HAL::panic` under SITL (the process aborts; no outcome of
the model stands for that, so they are not translated); `is_zero`, a `memcmp` of the object
representation (the unused bits of the bit-field byte and the padding are not modeled); and the callers
whose results depend on these: `get_alt_m`, `change_alt_frame`, `get_height_above`, `same_alt_as`,
`same_loc_as`, `sanitize`, `get_distance_NED_alt_frame`. With the stub headers `AP_AHRS_ENABLED` is 0
where `Location.cpp` tests it (the stub `AP_AHRS.h` does not include `AP_AHRS_config.h`); every member
that is translated is the same code in either configuration.

### Pointers into arrays (`--pointer-params`, PORT-PLAN F6)

- A parameter `T *p`, `const T *p`, `T p[]` (T a number type or a plain struct) that the body uses by
  `p[i]`, `*p`, steps (`p++`, `*p++`, `p += k`, `p = q` into the same array), comparisons with a pointer
  into the same array, as an argument for a pointer parameter, or to initialize a local pointer, is the
  array the caller passes (`Array T`); if the body writes through it (an element assigned, stepped,
  bound to a `T &`, passed to a pointer parameter the callee writes, the target of `memset`/`memcpy`),
  the array is returned after the result, as for `T &`. A parameter used only as `*p` is the scalar the
  caller passes as `&x` (`hash_fnv_1a`'s `uint64_t *hash`). A `const void *` parameter used only
  through a cast to `const uint8_t *` is an array of bytes (`crc8_dvb_s2_update`). A parameter
  compared with a null pointer is a nullable out-pointer, as before.
- A pointer that moves is an offset `p'o : Nat` into its array; `*p` is `p[p'o]!`, `p[i]` is
  `p[p'o + i]!`, `p++` is `p'o := p'o + 1`. A local pointer initialized with a pointer into an array
  (`const uint8_t *pend = p + length;`) is such an offset into the same array.
- A local pointer whose every value is an array of its own (`new (std::nothrow) T[k]`, or the result
  of a function each of whose returns returns such a local: `matrix_multiply`) is a local array:
  `new T[k]` is k zeros (the C++ elements are indeterminate until written; reading one first is
  undefined); the allocation is assumed to succeed (`new (std::nothrow)` returning a null pointer is not
  modeled); `delete[]` is no operation.
- Arguments: an array, an array member, a pointer parameter or local, `a + k` and `&a[k]` (a slice: the
  elements from k on, written back into `a` after the call if the callee writes them). Two pointer
  arguments into the same array of which one is written are rejected (aliasing).
- `memset(p, 0, k * sizeof(T))`, `memcpy(p, q, k * sizeof(T))` (T the element type, or `sizeof(x[0])`):
  k elements from the pointers' offsets; `memcmp(p, q, k * sizeof(T)) == 0` (or `!= 0`) on integer
  arrays (equal bytes iff equal elements). `memset(this, 0, sizeof(*this))` (Location::zero) makes
  every data member zero.
- Also accepted with the option: a local array without initializer whose every element is assigned
  (constant indices, right sides not reading it) before any other statement uses it (`T inv[16];`,
  checked); a local non-const reference bound to a data member, through data members only, of this
  object or of a local (`T &qw = q1;`, from_rotation_matrix): another name for that member; a byte view
  of an integer variable `((uint8_t *)&x)[j]`, read only: byte j on this little-endian target.
- Rejected (tests/reject_phase2.cpp): pointer differences and any other use of a pointer; aliasing
  pointer arguments; `memset` with a value other than 0; byte counts not of the form `k * sizeof(T)`;
  `memcpy` within one array; `memcmp` used other than compared with 0, or on non-integers; `new` of one
  object; a moved local pointer that holds an array of its own; comparisons of pointers into different
  arrays; local references to elements; writes through a byte view.

### Loops bounded by a runtime value (`--runtime-loops`, PORT-PLAN F8)

- `for (T i = start; i op bound; step)` with step `i++` (op `<`, `<=`) or `i--` (op `>`, `>=`), start and
  bound any values the body does not change (the bound: no effects, no variable the body assigns, a
  data member only in a const member function), and no assignment to i in the body: start and bound
  are evaluated once, before the loop, and the loop runs over `(bound - start).toNat` (+1 for `<=`,
  `>=`) values of the counter. The C++ types must show that the counter reaches the bound without
  wrapping: the comparison's type holds every value of T and of the bound's type (before promotion),
  and every value of the bound's type is at most max(T) + 1 for `<`, max(T) - 1 for `<=`, at least
  min(T) - 1 for `>`, min(T) + 1 for `>=` (a constant bound by its value). Rejected otherwise (or, with
  `--general-loops`, a fuel loop as before).
- `while (k--) body` with k an unsigned local or parameter the body does not assign and no `break`:
  k iterations, each decrementing k first; the failing test decrements once more (k wraps, as in C++).
- `for (; p != q; p++)` (or `<`) with p and q pointers into one array, the body moving neither and
  without `continue`: q's offset minus p's iterations (p past q is undefined in C++).
- These are exact trip counts, not fuel: no execution of the C++ runs more or fewer iterations.

### Other constructs (any options)

Static const data members defined out of line (`const float AP_Declination::SAMPLING_RES = 10;`);
constant tables of two dimensions (`(t[i]!)[j]!`); a static member function called through an object
(`loc2.longitude_scale(x)`); the value of a `--drop` function in a local read only by conditions of
empty statements, which are left out; `--drop Class::name(T1, T2)` for one overload; member templates
of class template specializations that nothing instantiates (Bitmask's constructor from an array);
`operator=` with a body (`op_assign`); a member type named without qualification inside a class
template specialization (`biquad_params`); `__builtin_popcount`, `__builtin_ffs`; `abs`/`labs`/`llabs`
of integers; libc++'s `isnan`/`isinf`/`isfinite` of integers (constants); `copysign(float, double)` and
`atan2(int32_t, int32_t)` (libc++'s overloads: the arguments converted to double); `do { ... } while
(false)`; AP_Common's `ASSERT_STORAGE_SIZE` (a compile-time check: no effect); clang's implicit
`extern "C"` declarations of builtins; an overload whose suffixed name is another function's name gets
a further `_` (`swap_float_` for matrix_alg.cpp's `swap(float &, float &)`, since AP_Math.cpp defines
`swap_float`).

`examples/pointers.cpp` (with `examples/pointers.json`, golden `tests/golden/Pointers.lean`) uses every
construct above through functions of numbers, which the difftest drives.

### Difftest additions

- Free functions with array arguments (`array_elem` in signatures.json): config `array_len` gives each
  array's length (`function.param` or `param` -> a Python expression over the integer arguments, e.g.
  `"mat_inverse_float.x": "dim*dim"`, `"crc_crc8.p": "len"`); an array is its length and its elements on
  the line; a written array is printed after the call as its length (in Lean the array's size, which
  must equal it) and its elements; corner lines put each array's elements at each corner value. Scalar
  pointer parameters are passed as `&a`.
- `leaf_domains`: a data member (by name) -> the values it can hold (`[0, 1]` for one-bit bit-fields),
  for state leaves set from the line and leaves of struct arguments.
- The literal check is split into definitions of 128 literals (AP_Declination has 1924).

### Results (seed 20261104)

```
literals: 2079 floating literals; 0 elaborate in Lean to bits other than clang's
pointers: 0 of 150000 lines differ (200 lines equal only as NaN vs NaN with different bits)
ardupilot/AP_Math free functions: 0 of 25661 lines differ (292 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<float>: 0 of 21421 lines differ (36 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector2<double>: 0 of 21261 lines differ (36 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<float>: 0 of 22539 lines differ (91 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Vector3<double>: 0 of 22159 lines differ (67 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Matrix3<float>: 0 of 24650 lines differ (612 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math QuaternionT<float>: 0 of 25399 lines differ (680 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math Matrix3<double>: 0 of 24650 lines differ (614 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Math QuaternionT<double>: 0 of 25399 lines differ (678 tokens equal only as NaN vs NaN with different bits)
ardupilot/AC_CommandModel AC_CommandModel: 0 of 5021 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/LowPassFilter2p LowPassFilter2p<float>: 0 of 20081 lines differ (33 tokens equal only as NaN vs NaN with different bits)
ardupilot/LowPassFilter2p LowPassFilter2p<Vector2<float>>: 0 of 20121 lines differ (98 tokens equal only as NaN vs NaN with different bits)
ardupilot/LowPassFilter2p LowPassFilter2p<Vector3<float>>: 0 of 20161 lines differ (276 tokens equal only as NaN vs NaN with different bits)
ardupilot/LowPassFilter2p LowPassFilter2p<int>: 0 of 20065 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/LowPassFilter2p LowPassFilter2p<long>: 0 of 20065 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Declination free functions: 0 of 20279 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common free functions: 0 of 20349 lines differ (2 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Location: 0 of 22205 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Bitmask<32>: 0 of 10043 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Bitmask<102>: 0 of 10043 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Bitmask<190>: 0 of 10043 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Bitmask<317>: 0 of 10043 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_Common Bitmask<634>: 0 of 10043 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

Sensitivity (CPP2LEAN_MUTATE): `mat_back_sub`'s loop count one short and crc's cursor stepped by 2 make
1162 of 25661 AP_Math free-function lines differ; one declination table entry one ulp off, 85 of 20279;
`__builtin_ffs` off by one, about 680 of 10043 lines of each Bitmask; `b2 := b1` in
`compute_params`, nearly every LowPassFilter2p line.

Not driven: Bitmask's `operator=`, `operator==`, `operator!=` (their argument holds an array; the C++
driver cannot return a `Bitmask &` by value, its copy constructor is deleted), `DigitalBiquadFilter<T>::
compute_params` on its own (not emitted as a symbol by the C++ build; it runs inside
`set_cutoff_frequency`, whose `_params` the state leaves show), file-static functions (driven through
their callers: `mat_inverse` with dim 3, 4 and others), `Matrix3::to_euler` (nullable pointers).

### Known gaps (phase 2)

- Two reference parameters bound to elements of one array (`swap(pivot[a], pivot[b])`, mat_pivot) are
  written back in order: correct unless the two elements are one (`mat_pivot` calls it only for
  `max_j != i`), as for the earlier aliasing gap.
- `new (std::nothrow)` is assumed to succeed; out-of-bounds pointer arithmetic, `memset`/`memcpy` past
  an array's end and `p != q` loops with p past q are undefined in C++ and not detected.
- A byte view assumes the little-endian target.
- A pointer's element type must be a number or plain struct; `char *` stays the string handling of
  phase 3; `void *` only as bytes read through a cast.

## Phase 2b: text, bytes, StorageManager, AP_InternalError, AP_RTC


Translated from ArduPilot's unmodified sources (commit 802db19de1), with the reference flags and the
stub headers, and checked bit for bit against the C++ by `difftest.py`:

| library | script (output) | Lean lines | what |
|---|---|---|---|
| text formatter | `ardupilot/translate_text.sh` (`out/Text/Text_lib.lean`) | 1330 | `print_vprintf` (print_vprintf.cpp), `ftoa_engine` (ftoa_engine.cpp), `ultoa_invert`, `ulltoa_invert` (utoa_invert.cpp), `AP_HAL::Util::snprintf`, `vsnprintf` and their `BufferPrinter` (Util.cpp), and the 80 test functions of `ardupilot/unity_text.cpp` |
| StorageManager | `ardupilot/translate_storage.sh` (`out/StorageManager/StorageManager_lib.lean`) | 421 | `StorageManager::layout` (15 areas, HAL_STORAGE_SIZE 16384), `StorageAccess`: constructor, `size`, `read_block`, `write_block`, `read_byte`/`uint8`/`uint16`/`uint32`/`float`, the writes, `copy_area`; over the HAL storage (`--hal-storage 16384`) |
| AP_InternalError | `ardupilot/translate_internalerror.sh` (`out/AP_InternalError/AP_InternalError_lib.lean`) | 911 | the class: `error` (with its writes of `hal.util->persistent_data` as output events), `errors_as_string` (through `hal.util->snprintf`, i.e. the formatter above), `errors`, `count`, `last_error_line`, the table `error_bit_descriptions` |
| AP_RTC | `ardupilot/translate_rtc.sh` (`out/AP_RTC/AP_RTC_lib.lean`) | 174 | `get_utc_usec`, `get_source_type`, `clock_ms_to_hms_fields`, `get_system_clock_utc`, `get_local_time`, `get_time_utc`, `_is_leap` (not difftested, below) |

`ardupilot/gen_unity_text.py` writes `ardupilot/unity_text.cpp` (and `unity_text.h`, the `domains` of
`Text.json`): one function per conversion specification found in the format strings of the reference
build's sources (the calls of `snprintf`, `vsnprintf`, `GCS_SEND_TEXT`, `send_text`, `check_failed`,
`printf`, `panic`, ... in the files of `build/reference/ap/build/sitl/compile_commands.json`, the
simulator excluded; 72 specifications, `%p` left out because a pointer's value differs between the two
programs), each formatting random arguments of the conversion's type through `hal.util->snprintf`
into a 40-byte buffer with a random size (0 to 40, so truncation and termination are exercised), and 9
whole formats of the vehicle's messages (`"PreArm: Battery %d low voltage %.2fV"`, `"%s: %u (%5.1f%%)"`,
`"gyro %.3e %E %g %G"`, ...). The buffer, the result and every argument are on each line.

### New options

| option | meaning |
|---|---|
| `--c-strings` | `char` (a byte), `char[N]`, string literals and byte pointers as byte arrays with offsets; the C string functions as `CString.lean`; variadic functions and `va_list`; held pointer members, pointer-returning functions, pointer differences, object pointer parameters (below) |
| `--gotos` | forward `goto`, `continue` in `do` loops and `switch` fallthrough, rewritten with flags on clang's AST before translation |
| `--byte-objects` | object representations: `&x` passed as bytes, read-only byte views, unions of numbers in C++, `memcpy` between objects and bytes, `sizeof` |
| `--hal-storage SIZE` | `hal.storage->read_block/write_block` on the HAL storage's SIZE bytes, threaded through the functions that reach them |

All four need `--pointer-params`; none changes the output of a translation that does not use it (the
earlier translations, the examples and musl's translate to the same bytes as before).

### Memory is bytes (`--c-strings`, `--byte-objects`; PORT-PLAN 4.5, F5)

**Representation.** An object of the model is its value (a number, a structure, an `Array`); its
*object representation* is computed from its type when the code looks at it as bytes. Arrays of bytes
are the only memory that byte pointers point into: a `char[N]`, `unsigned char[N]`, `uint8_t[N]`, a
string literal (with its terminating zero) and an object representation are an `Array UInt8`, and a
byte pointer is such an array and an offset (`Nat`), as for the pointers of phase 2. C's `char` (signed
on the reference target, `-fsigned-char`) is stored as its byte (`UInt8`); as a value it is converted
through `UInt8.toInt8` wherever C converts it (integer promotion, comparisons, arithmetic), so `char`
arrays, `unsigned char` arrays and `uint8_t` arrays are one storage type and a cast between their
pointers (`(char *)buf`, `(uint8_t *)data`) is no conversion.

**Layout** (`byte_size_align`, `record_layout`, `type_leaves`): the record layout rules of the target's
ABI (AAPCS64; x86-64 SysV agrees): each scalar aligned to its size, a struct aligned to its most
aligned member and padded to a multiple of it, members in declaration order, bases first,
`__attribute__((packed))` alignment 1; arrays of elements; enums as their underlying type. A layout is a
list of leaves (byte offset, path of fields and indices, scalar type). The bytes of a value
(`value_to_bytes`) are its leaves, little endian (`CString.ofUInt16/32/64`), a float through
`Binary32.toBits`/`Binary64.toBits`, a `bool` as 0/1, padding bytes zero; the value of bytes
(`value_from_bytes`) reads the leaves back (`CString.toUInt16/32/64`, `Binary32.ofBits`). The layout is
checked against the compiler where the difftest observes it: `sizeof` of a 16-byte struct with padding
and of AP_InternalError (12 bytes) are on the difftest lines, and examples/bytes.cpp hashes every byte of
a struct copied to bytes (padding included, zero-initialized on both sides).

**Operations.**
- `&x` used as a byte pointer (passed to a `void *`, `uint8_t *` or `char *` parameter of a translated
  function, of the C string runtime or of the HAL storage; x a number, enum, plain struct, class without
  virtual functions, or an array of them): a temporary holding x's bytes; if the callee writes through
  the pointer, the bytes are stored back into x afterwards (`StorageAccess::read_uint16`'s
  `read_block(&v, loc, sizeof(v))`).
- A local byte pointer to the bytes of a variable (`uint8_t *valbits = (uint8_t *)&val;`, ftoa_engine):
  a copy of the bytes, read only; the variable must never be assigned in the function (checked).
- `memcpy`, `memset`, `memcmp` on byte arrays, with any `size_t` count (`CString.memcpy` etc.); between an
  object and bytes through `&x` as above (`memcpy(&e, raw, sizeof(e))`).
- A union of numbers of one width in C++ (ftoa_engine's `union { float v; uint32_t u; } x;`): its bit
  pattern, as for musl's C unions.
- `sizeof(T)`, `sizeof(x)`: the layout's size, a constant (also as a loop bound).

**Rejected**: writes through a read-only byte view; a byte view of a variable that is assigned; the
object representation of a class with virtual functions (its vtable pointer), of bit-fields, of members
that are not state of the model (parameters, boundary members); `memcmp` over the representation of a
struct with padding (C leaves those bytes unspecified); byte pointers into arrays of other element types
(`(uint8_t *)floats`); pointer arithmetic across objects.

**Extension for Phase 4 without regenerating Phase 2's output.** A translation keeps its values as
they are: a structure stays a structure (`AP_InternalError.State`), so the earlier translations and their
callers do not change. A byte-level view is created only where code takes `&x` as bytes, and goes
through `value_to_bytes`/`value_from_bytes` of the type's layout. Phase 4 adds (a) `memcpy`/`memcmp` of
packed structs (MAVLink's `mavlink_X_t`, AP_Param's `Param_header` bit-fields: leaves at bit offsets with
mask and shift, in `type_leaves`), (b) unions with members of different types (`Mission_Command::Content`,
`mavlink_message_t`'s `payload64`) as the bytes of their largest member with each member a view, and (c)
the cross-check of each layout against clang's `-fdump-record-layouts`; these are new cases of the same
two functions, and the representation of everything translated so far is unchanged. Unions with members
of different widths are rejected now.

### C strings and the runtime (`--c-strings`; PORT-PLAN 4.8, F7, D10)

- Character literals have clang's value and type; a string literal is its bytes (`(#[105, 110, 102, 0] :
  Array UInt8)`), an initializer of `char a[N]` its bytes and zeros; a table of string literals
  (`static const char *const t[]`) is an `Array (Array UInt8)`, an element a pointer at offset 0.
- Byte pointers are phase 2's pointers into arrays (parameters, moved locals, slices `&a[k]`, `a + k`),
  with `char` elements. A local `const char *` assigned pointers into different arrays (string literals,
  local arrays, `va_arg`, table elements: print_vprintf's `pnt`, `p = "inf"` / `"nan"`, errors_as_string's
  `format`) holds a copy of the array it points into and an offset. The pointee must not change while
  the pointer is used: checked statement by statement in the pointer's block (a statement after the one
  that makes it point into a variable's array must not write that array).
- `CString.lean` (support/, copied next to every translation made with `--c-strings`, `--byte-objects` or
  `--hal-storage`, and imported by it): `strlen`, `strnlen`, `strncpy`, `strcmp`, `strncmp`, `strcasecmp`,
  `strncasecmp`, `memcpy`, `memset`, `memcmp` on (array, offset) pairs with C's results; total where C is
  undefined (a byte outside the array reads 0, a write outside it is dropped). The comparisons return the
  difference of the first differing bytes as `unsigned char`s, which is what the platform's C library
  returns (checked: `difftest.py cstring` drives every function against it, including bytes ≥ 0x80 and
  upper/lower case). The result of `strncpy`/`memcpy`/`memset` (the destination pointer) must be discarded.
- Variadic functions: a definition with `...` takes `(va' : Array CArg)`; a call passes its variadic
  arguments, after the default promotions clang made explicit, as tagged slots (`CArg.ofInt32 x`,
  `CArg.dbl d`, `CArg.ptr a o` for a byte pointer); `va_list` is `VaList` (the slots and the next index),
  `va_start` starts it from `va'`, `va_arg(ap, T)` reads the next slot as T (`int`, `unsigned`, `long`,
  `unsigned long`, `long long`, `unsigned long long`, `double`, `char *`) and moves `ap`, `va_end` is
  nothing, `va_copy` copies. Each slot is 64 bits, sign- or zero-extended, as on arm64 Apple (every
  variadic argument in its own 8-byte stack slot), so a mismatched `va_arg` (undefined in C) reads what
  the target would.
- Pointer-returning functions: a function returning `T *` each of whose `return`s returns one pointer
  parameter (utoa_invert's `return s;` after `*s++ = ...`) returns that pointer's offset (`Nat`); a call
  of it is a pointer into the argument's array. `p - q` for pointers into one array is the difference of
  their offsets (`ptrdiff_t`).
- Held pointer members: a data member `T *const p` (BufferPrinter's `char *const _str`) whose
  constructor binds it to a pointer parameter is the array it points into (`_str : Array UInt8`); an
  object of the class must be a local variable constructed from a pointer variable of the function at
  offset 0 (vsnprintf's `BufferPrinter buf(str, ...)`), and after each write of the object the variable
  is the object's array again (and conversely).
- Object pointer parameters: a parameter `B *p` (B a class; print_vprintf's `AP_HAL::BetterStream *s`)
  is translated for the class D of the object its calls pass (`&buf`, a `BufferPrinter`), as a reference
  parameter of type D, so that a virtual call through it (`s->write(c)`) resolves to D's overrider.
  D must have no derived class in the translation, and every translated call must pass D (one
  translation per function; a function no translated function calls is rejected).
- `--boundary-static` members may call each other through `this` (`snprintf` calls `vsnprintf`).
- `hal.util->snprintf(...)` with `--boundary AP_HAL::Util,AP_HAL::HAL --boundary-static
  AP_HAL::Util::snprintf --boundary-static AP_HAL::Util::vsnprintf` is the translation of Util.cpp's own
  `snprintf`, i.e. ArduPilot's `print_vprintf` (AP_HAL/Util.cpp:46-55): the route D10 asks for.

**Rejected** (tests/reject_phase2b.cpp): writes through a pointer to a literal or another pointer
value; `va_arg` of other types; variadic arguments that are structs or pointers to other than bytes; a
used result of `strncpy`/`memcpy`/`memset`; a `const char *` copy whose array is written while it may
point into it; a pointer member other than `T *const`; an object holding a pointer that is not a
pointer variable at offset 0; a class pointer parameter whose argument is not `&x`, or of a class with
derived classes, or passed objects of two classes.

### Gotos (`--gotos`)

Before translation, a function body with forward `goto`s, `continue` in a `do` loop, or a `switch` case
that falls through into a non-empty case is rewritten on clang's AST (`GotoRewriter`), so that the
translator sees only structured code with the same behavior:
- a case that falls through gets the statements of the cases it falls into appended (copies; a
  fallthrough into statements that declare variables or labels is rejected); `[[fallthrough]]` is nothing;
- `continue` in a `do` loop is a `goto` to a label at the end of the loop's body;
- for each label L with forward gotos, a flag `goto'L` (false at the start of the innermost block, `if`
  or `switch` holding L and its gotos); the statements from the first that holds a goto to the one
  before L's are a one-iteration loop, each `goto L` is `goto'L = true; break;` (and `if (goto'L) break;`
  after each loop or switch between it and that loop); a `break`/`continue` in it for an enclosing loop
  leaves it the same way and is repeated after it; declarations without initializer there are moved
  before it (C++ forbids jumping over an initialization). The statement holding L is entered at L when
  the flag is set: in a block, the statements before L's are skipped (`if (!goto'L)`); in an `if`, the
  branch holding L is taken without evaluating the condition; in a `switch`, the statements from L to the
  case's final `break` run after the switch (`if (goto'L) {...}`) and the switch is skipped; a goto from
  one branch of an `if` into the other evaluates the condition once into `cond'L`.
- Rejected: backward gotos, gotos into a loop body, a label in a `switch` case whose statements from the
  label do not end in `break`, a `break` among them before the last.

print_vprintf's `goto flt_oper` (then-branch into the else-branch), `goto non_string`, `goto ultoa` (from
before the switch and from two cases into a third), `goto tail`, the `continue`s of its flag loop and its
two fallthroughs, and ftoa_engine's `goto roundup` (out of a `do` loop into a later `if`), are all of
these forms. examples/bytes.cpp has each of them on numbers.

### The HAL storage (`--hal-storage SIZE`)

`hal.storage` is the boundary of StorageManager (PORT-PLAN 3.2): its contents are an `Array UInt8` of
SIZE bytes, `hal'storage`, a parameter of every function that reaches it (directly or through a callee)
and returned when written, as a reference parameter. `hal.storage->read_block(dst, src, n)` and
`write_block(dst, src, n)` are `HalStorage.read_block`/`write_block` (CString.lean), the semantics of the
reference vehicle's lock-step HAL (`reference/hal/lockstep.cpp`, `class Storage`): a block that does not
fit is not transferred, else the bytes are copied; the difftest's C++ environment (`ardupilot/storage_env.cpp`)
is a copy of that class. Other members of the storage (`erase`, `healthy`) are rejected. In the
signatures the parameter is marked `hidden`; difftest.py passes a zero-filled storage of its size and
discards the one returned (the C++ keeps it in the HAL object). With the World (PORT-PLAN D1), the storage
becomes a field of `World` without changing the translated functions' bodies.

### What is not translated, and why

- **StorageManager**: translated with `AP_SDCARD_STORAGE_ENABLED=0` on both sides of the difftest; the
  reference build has 1 (SITL: `HAL_MEM_CLASS_1000`, the POSIX file system, 4096 KB program limit). The
  difference is `attach_file`/`flush_file` (a microSD file through AP_Filesystem, a `FileStorage` on the
  heap, `goto fail`, `register_io_process`) and a `file != nullptr` branch in `read_block`/`write_block`
  that is taken only after `attach_file`, which runs only if `BRD_SD_MISSION` or `BRD_SD_FENCE` is
  non-zero (both default 0). The model is the reference while neither is set; the SD-card path waits for
  AP_Filesystem and heap objects (Phase 4). `StorageManager::erase` (`hal.storage->erase()`, `::printf`),
  `last_io_failed` and `storage_failed` (set only by flush_file) are left out (`--drop`).
- **AP_InternalError**: needs singleton support for `static AP_InternalError instance;` and
  `AP::internalerror()` (AP_InternalError.cpp:15, :110), left out (`--drop instance --drop
  AP::internalerror`); `error_to_string` (log2f, not among the translated C library functions) is called
  only under `HAL_DEBUG_BUILD` and is left out. `error()` translates (its writes of
  `hal.util->persistent_data.internal_errors/_count/_last_line` are output events, `--output-log`) but is
  not driven: the C++ harness does not log writes of a boundary object's data members.
- **AP_RTC**: needs singleton support for its constructor (`if (_singleton != nullptr) return;
  _singleton = this;`, AP_RTC.cpp:15-25), `get_singleton`, `_singleton`, `AP::rtc()`; a constructor is what
  the class driver starts from, so AP_RTC is translated (and builds in Lean) but not difftested. Also left
  out: `set_utc_usec` (`WITH_SEMAPHORE(rsem)`, a HAL semaphore object, F11; it also reads
  `hal.util->get_soft_armed()` and calls `hal.util->set_hw_rtc()`), `rsem`, `get_semaphore`; `_timegm` and
  `date_fields_to_clock_s` (C's `struct tm`, which on the reference platform has a `char *tm_zone`
  member), `clock_s_to_date_fields` and `get_date_and_time_utc` (C's `gmtime_r`: musl's `__secs_to_tm` is
  not translated). `AP_RTC_LOGGING_ENABLED` and `AP_MAVLINK_SIGNING_ENABLED` are 0 for its AST (the stub
  headers lack `AP_Logger::Write_RTC` and `GCS_MAVLINK::update_signing_timestamp`, called only in
  set_utc_usec).
- **ExpandingString** (AP_Common): not translated. It grows its buffer on the heap while it prints
  (`ExpandingString::expand`, ExpandingString.cpp:38-60: `mem_realloc(buf, used, newsize+1)`, unless it
  was given an external buffer), and its `printf` formats with `hal.util->vsnprintf` into the heap buffer
  at a moving end; the model has no heap objects (PORT-PLAN 4.10 allocates only at start-up), and the
  sizes it reallocates to depend on the text, so it is not faithful without a heap model. Its users in
  the vehicle are AP_Filesystem's virtual files `@SYS`, `@PARAM` and `@MISSION` (MAVLink FTP) and the
  HAL's thread and UART statistics: a ground station that uses MAVLink FTP reaches them, the scripted
  ground station of the reference harness does not.
- Not driven by the formatter's difftest: `%p`; the `BetterStream::printf` route of `print_vprintf`
  (UARTs, `hal.console->printf`), which needs the UART driver as the stream object.

### Examples and tests

`examples/cstring.cpp` (`--c-strings`; golden `tests/golden/CStringDemo.lean`) drives every function of
the C string runtime against the platform's C library on strings built from numbers (letters of both
cases, digits, bytes 0x80 and 0xff), `char` arithmetic, pointers into literals and tables of literals,
and a variadic function reading `int`, `unsigned`, `long long`, `double` and `char *` arguments.
`examples/bytes.cpp` (`--gotos --byte-objects --c-strings`; golden `tests/golden/Bytes.lean`) has each
goto form above, `continue` in a `do` loop, fallthrough, `&x` written through a `void *`, a byte view of
a float, a float/uint32 union, a struct with padding copied to and from bytes, a pointer-returning
function and a pointer difference, a held `char *const` member and a virtual call through a base-class
pointer parameter. `--hal-storage` has no example of its own: it names ArduPilot's `hal.storage`; the
StorageManager translation (golden `tests/golden/ardupilot/StorageManager_lib.lean`) and its difftest are
its test. `tests/reject_phase2b.cpp` holds the limits (13 rejections).

### Differential test additions

- `difftest.py` copies `CString.lean` into the Lean package when a translation writes it, and keeps it in
  the library roots.
- Free functions with a `hidden` parameter (`--hal-storage`): the Lean driver passes a zero-filled
  storage and discards the returned one; the C++ call has no such argument.
- New configurations: `examples/cstring.json`, `examples/bytes.json`, `ardupilot/Text.json`,
  `ardupilot/StorageManager.json`, `ardupilot/AP_InternalError.json`; C++ environments
  `ardupilot/text_env.cpp` (a HAL whose Util has the pure virtual members defined trivially; Util.cpp's
  own `snprintf`/`vsnprintf` are compiled), `ardupilot/storage_env.cpp` (the lock-step storage).

### Results (seed 20261104)

```
literals: 6 floating literals; 0 elaborate in Lean to bits other than clang's
cstring: 0 of 39040 lines differ (0 lines equal only as NaN vs NaN with different bits)
bytes: 0 of 48800 lines differ (0 lines equal only as NaN vs NaN with different bits)
ardupilot/Text free functions: 43062 calls (40000 random, 3062 corner) over 80 functions
ardupilot/Text free functions: 0 of 43063 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/StorageManager free functions: 6340 calls (6000 random, 340 corner) over 9 functions
ardupilot/StorageManager free functions: 0 of 6341 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AP_InternalError free functions: 10050 calls (10000 random, 50 corner) over 1 functions
ardupilot/AP_InternalError free functions: 0 of 10051 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

Sensitivity (`CPP2LEAN_MUTATE`): `goto'flt_oper := true` set false in print_vprintf, 626 of 43063 text
lines differ; ftoa_engine's `factorTable[16]` off by 100 in 7.8e8, 96 lines; `factorTable[2]` off by
one (numbers near 1e-33 only), 0 lines (the formats with `%e`/`%g`, where such numbers print digits,
are few: a gap of the test, not of the translation); one area offset of the storage layout off by one,
45 of 6341 StorageManager lines.

Domains: `%ld`/`%li`/`%lld` are not driven at INT64_MIN: print_vprintf negates a negative value
(`x = -x`, print_vprintf.cpp:403, :411), which overflows there (undefined; clang -O2 prints `-0`, the
Lean `-9223372036854775808`). StorageManager's `read_byte`/`read_uint16`/`read_uint32`/`read_float` are
driven inside the area: for a read that does not fit, read_block leaves their local `v` (partly)
unwritten and they return an indeterminate value.

### Findings

- ArduPilot's formatter is not C's printf: `%x` prints upper-case digits (utoa_invert.cpp tests
  `#if XTOA_UPPER == 0` with `XTOA_UPPER` 0x0200, so the upper-case branch is always compiled; and
  `16 | XTOA_UPPER` is truncated to the `uint8_t` 16); `%f`/`%e`/`%g` convert the `double` argument to
  `float` (`float value = va_arg(ap, double)`), `%f` prints at most 8 digits of it (`ndigs > 8`,
  print_vprintf.cpp:255) and switches to `%e` above 9999999;
  `%llu` of values above 2^63 prints wrong digits (ulltoa_invert's comment: "64 bits is not actually
  enough, we need 65"; e.g. 17730973266611095357 prints `54331438...`). The translation reproduces each
  bit for bit. So D10's "route the C library's snprintf to the same formatter" would change the bytes
  of those calls (parameter and sensor names, `AP_NavEKF3.cpp:1189`); they need the C library's printf
  translated for their formats, or a check that their formats print the same in both.
- `ardupilot/stubs/oracle_env.cpp` defines `AP_HAL::Util::snprintf` with the C library's `::vsnprintf`, not
  print_vprintf: the AP_Motors difftest's arming-check texts were compared against the wrong formatter.
- PORT-PLAN 4.5 says SITL's mission uses "the whole 32 KB"; on the reference board HAL_STORAGE_SIZE is
  16384 (as 3.2 says), STORAGE_NUM_AREAS 15, and the mission areas are 2422 + 2132 + 5204 bytes.
- StorageManager is not a leaf on SITL: AP_SDCARD_STORAGE_ENABLED is 1 there (above).
- AP_RTC and AP_InternalError are not leaves either: both are singletons (4.3), AP_RTC also needs F11
  (semaphores) and the C library's time functions.

## Phase 3 summary (estimation, 2026-11-11 to 2026-11-12)

PORT-PLAN.md section 6, "Phase 3": the estimator translated from the unmodified ArduPilot sources against the reference
build's headers and flags, and checked against the reference vehicle. The sections below are the stages in order; the
last one ("Phase 3: AP_AHRS in the estimator World, the full estimation replay") is the result.

What is translated, as one World (`ardupilot/translate_estimator.sh` → `Estimator_lib`): the sensor front ends
AP_InertialSensor, AP_Baro, Compass, AP_GPS (with AP_RTC, the filters and AP_Param's parameter classes; the reference's
SITL back-end stand-ins and the HAL scheduler stand-in), AP_DAL, AP_NavEKF (buffers, EKFGSF_yaw, AP_NavEKF_Source),
NavEKF3 with its cores, and AP_AHRS with AP_AHRS_Backend, AP_AHRS_NavEKF3, AP_AHRS_DCM and AP_AHRS_View. Boundary: the
vehicle, the HAL's Util, AP_Notify, GCS text, AP_Mission's home storage, AP_AHRS_SIM, AP_Param's storage.

| translation (golden in `tests/golden/ardupilot/`) | Lean lines | defs | ArduPilot extent lines (functions) | check (as its section reports) |
|---|---|---|---|---|
| `EKF_Buffer_lib`, `EKFGSF_lib`, `EstScheduler_lib` | 1,537, 1,244, 571 | 127, 52, 51 | 255 (42), 865 (54), 205 (46) | difftests `ardupilot/EKF_Buffer`, `ardupilot/EKFGSF`: 0 lines differ |
| `Sensors_lib` (front ends, stand-ins, scheduler) | 8,174 | 482 | 6,245 (459) | difftest `ardupilot/Sensors`: 0 |
| `NavEKF_Source_lib` | 474 | 35 | 226 (26) | difftest `ardupilot/NavEKF_Source`: 0 |
| `EKF3_lib` (AP_DAL, NavEKF3) | 14,652 | 606 | 12,457 (565) | difftest `ardupilot/EKF3` (one and two cores): 0 of 24,001 lines |
| `Estimation_lib` (front ends + AP_DAL + NavEKF3) | 22,525 | 1,060 | 18,411 (978) | difftest `ardupilot/Estimation`: 0 of 8,399 lines (two runs) |
| `AHRS_lib` (AP_AHRS + DCM + view on EKF3) | 19,278 | 829 | 15,740 (750) | difftest `ardupilot/AHRS` (one and two cores, DCM fallback): 0 of 24,001 lines |
| `Estimator_lib` (all of the above as one World) | 27,037 | 1,285 | 21,761 (1,175) | replay of both recorded flights against `copter_ref --est`: 35,122 steps and 8,439,007 values per flight, 0 different |

(Extent lines: the distinct `file:a-b` ranges of the translated functions' doc comments.) Acceptance (PORT-PLAN oracle
(a) and (b)): every per-class and World difftest at 0 differing lines; the estimator replay drives the World with the
recorded sensor lines and the vehicle's calls only, and every AP_AHRS key (`q rpy dcm vel pos loc gyro accef resets
healthy initialised origin ekf fs`), EKF3 key (`primary ncores gbias abias var`, per core `x fs P out imu var gsf`),
front-end key and vehicle-side key (`tkd thgt home cfg comp bgnd`) of every main-loop step is bit-identical to the
reference vehicle's, on the deterministic and the noisy flight. Speed of the estimator per 400 Hz step: 167 µs on
average, p99 1.9 ms, 3 of 36,013 steps over the 2.5 ms budget (C++: 0.69 µs for AHRS + EKF3); FloatLib's `Binary64`
fallback dominates.

## Phase 3: conversions on the bit patterns, `log2f` (2026-11-11)

EKF3 computes in `double` and converts double to float, integers to floating point and floating
point to integers in every step; these conversions went through FloatLib's rational and dyadic
arithmetic (100 ns to 1.4 µs each). `support/CFloat.lean` (section "Conversions between floats and
integers on the bit patterns") now computes them on the bit patterns under the rule of the
comparisons above: a `@[csimp]` theorem `@slow = @fastImpl` with a complete proof against
FloatLib's definition, no `implemented_by`, `sorry` or `native_decide`. `#print axioms` of each of
the five theorems gives `[propext, Classical.choice, Quot.sound]`.

| C conversion | `CFloat.lean` function | theorem | on the bits | left to FloatLib |
|---|---|---|---|---|
| `(int)f`, `(uint8_t)d`, ... (`Binary32.toInt8` .. `Binary64.toUSize`) | `CFloat.truncSat32`, `truncSat64` | `CFloat.truncSat32_eq_truncSat32Impl`, `truncSat64_eq_truncSat64Impl` | every word | nothing |
| `(float)n`, `(double)n` (`Int8.toBinary32` .. `USize.toBinary64`) | `CFloat.ofInt32`, `ofInt64` | `CFloat.ofInt32_eq_ofInt32Impl`, `ofInt64_eq_ofInt64Impl` | `n = 0` and `\|n\| < 2^24` (float) resp. `2^53` (double): exact | larger `\|n\|`, which round (`ofInt32Slow`, `ofInt64Slow`) |
| `(float)d` | `Binary64.toBinary32` | `Binary64.toBinary32_eq_toBinary32Impl` | normal results (biased exponent of `d` in `[897, 1149]`) and `±0` | subnormal and overflowing results, infinities, NaNs (`toBinary32Slow`) |

- **To an integer.** `toIntBits` reads the exponent field: all ones gives `none` (NaN, infinity),
  zero gives 0 (zero, subnormal), otherwise the significand with its leading one shifted by the
  unbiased exponent and signed. `toInt?_eq_toIntBits` proves it is FloatLib's `toInt?` on every
  word: `Model.toDyadic?` is `ieeeToDyadic?`, which decodes the same fields, and
  `roundDyadicToInt .towardZero` of `⟨s, m, e⟩` is `m <<< e` or `m >>> -e`.
- **From an integer.** For `|n| < 2^24` (`2^53`) FloatLib's rounding returns the integer itself
  (`CFloat.Conv.toReal_ofRat_int`: `Model.toReal_roundRatScaled_eq_roundAt`, and Flocq's
  `round_preserves_generic` for a value of the format's grid); `ofIntWord` builds that word from
  `k = ⌊log₂ |n|⌋` (`Nat.log2`): sign, exponent `127 + k` (`1023 + k`), `|n| << (23 - k)` without its
  leading one, in `UInt32` (`UInt64`) arithmetic (`ofIntWord_toNat`); the two words have the same
  nonzero real value, so they are equal (`Model.eq_of_toReal_eq_of_nonzero`). Zero is `+0`, by
  `decide`.
- **Double to float.** `Model.cast` rounds the exact dyadic of the double with `Model.roundDyadic`,
  which FloatLib proves equal to its integer algorithm `Model.roundDyadicGeneral`
  (`roundDyadicGeneral_eq_roundDyadic`); for a normal result that algorithm takes its normal branch
  and keeps `roundShiftRightEven (2^52 + F) 29` (`Binary64.cast_binary32_model`), whose
  quotient/remainder form (`roundShiftRightEven_def`) is what `toBinary32Word` computes on the word:
  the significand shifted right by 29, plus one when the 29 dropped bits exceed half or equal half
  with an odd quotient; the exponent is rebiased by 896 and a carry out of the significand runs into
  the exponent field (`toBinary32Word_toNat`). Zeros keep their sign (two words, `decide`).

Measured with `lean/CFloatBench.lean` (executable `cfloat_bench`, added to `lean/lakefile.toml`;
`lake build cfloat_bench`), 20 × 20,000 conversions per row, inputs prepared outside the timing
(doubles `k/1000` with `|k| ≤ 10^8`, their floats, integers below `2^24` and below `2^51`), checksums
equal before and after:

| conversion | before (ns) | after (ns) |
|---|---|---|
| `Binary32.toInt32` | 104 | 12.2 |
| `Binary64.toInt32` | 364 | 12.9 |
| `Binary64.toInt64` | 367 | 17.2 |
| `Binary64.toUInt16` | 367 | 14.2 |
| `Int32.toBinary32` | 887 | 18.9 |
| `Int32.toBinary64` | 1123 | 18.6 |
| `Int64.toBinary64` | 1314 | 194.3 |
| `UInt32.toBinary32` | 784 | 16.9 |
| `Binary64.toBinary32` | 464 | 8.7 |
| `Binary32.toBinary64` (Phase 1, unchanged) | 9 | 7.8 |

`Int64.toBinary64` stays slower because `Int64.toInt` of a value of magnitude `2^31` or more
allocates a big integer (Lean's small `Int` is 32 bits); the conversion itself is on the bits up to
`2^53`. `cfloat_bench check N` compares every compiled conversion with a copy of FloatLib's
definition (the same bodies under other names, which no `@[csimp]` rewrites): words with random
bits, words with the exponent in the bands where the conversions change behaviour (binary32
`[100, 200]`, binary64 `[1000, 1100]`, double to float `[870, 1160]` and `1023`), and the special
values (zeros, infinities, NaNs with payloads, subnormal and normal limits, `2^31`, `2^63`, `2^64`
and `2^24`/`2^53` boundaries, halfway cases of the rounding); integers around every power of two up
to `2^65` and random magnitudes; float to integer for the ranges of all eight integer types.
`cfloat_bench check` (N = 100,000): 3,200,768 float-to-integer, 202,128 integer-to-float and 300,050
double-to-float conversions compared, 0 differences; `cfloat_bench check 300000`: 9,600,768, 602,128
and 900,050, 0 differences.

Differential tests after the change (0 differing lines each; the NaN-only lines as before):

```
$ python3 difftest.py numeric mixed libm
numeric: 0 of 80000 lines differ (100 lines equal only as NaN vs NaN with different bits)
mixed: 0 of 110000 lines differ (2120 lines equal only as NaN vs NaN with different bits)
libm: 0 of 440000 lines differ (600 lines equal only as NaN vs NaN with different bits)
$ python3 difftest.py --seed 7 --random 50000 libm
libm: 0 of 2552000 lines differ (600 lines equal only as NaN vs NaN with different bits)
$ python3 difftest.py ardupilot/AP_Math
free functions 0 of 25661, Vector2<float> 0 of 21421, Vector2<double> 0 of 21261, Vector3<float> 0 of 22539,
Vector3<double> 0 of 22159, Matrix3<float> 0 of 24650, QuaternionT<float> 0 of 25399,
Matrix3<double> 0 of 24650, QuaternionT<double> 0 of 25399 lines differ
```

`lake build` of `lean/` (every default target rebuilt on the new `CFloat.lean`) completes with no
warning; `tests/golden/CFloat.lean` is the new `support/CFloat.lean`.

**`log2f`, `log2`.** musl 1.2.5's `log2f.c`, `log2f_data.c`, `log2f_data.h`, `log2.c`, `log2_data.c`,
`log2_data.h` added to `libm/musl-1.2.5/src/math` (from the release tarball, SHA-256 as above,
unmodified), to `libm/musl_files.txt`, `libm/env/musl_names.txt`, `libm/env/musl_prefix.h`
(`log2f`, `log2`, `__log2f_data`, `__log2_data`), `libm/env/math.h`; `libm/unity/unity_log2f.c`,
`unity_log2.c` and their lines in `libm/unity/groups.txt` (`log2f: log2f log2f_data __math_divzerof
__math_invalidf`, as `logf`; `log2` as `log`). They translate with no translator change beyond the
mapping (`cpp2lean.py`: `log2` added to `LIBM`, so `log2f(float)`, `log2(float)` and `log2(double)`
call `Musl.log2f.log2f` / `Musl.log2.log2`), into `libm/out/Musl/log2f.lean` and `log2.lean`
(golden copies in `tests/golden/libm/`); `examples/libm.cpp` has wrappers `f_log2f` and `f_log2`
(golden `tests/golden/Libm.lean` updated).

## Phase 4: integer to float for every magnitude, narrow float-to-integer as arm64 (2026-11-12)

`support/CFloat.lean` (section "Conversions between floats and integers on the bit patterns", and
"Integer types to float on the words" at its end), under the rule above (`@[csimp]` theorem with a
complete proof against FloatLib's definition; no `implemented_by`, `sorry`, `native_decide`).

- **Rounding on the words.** `CFloat.ofInt32`/`ofInt64` (FloatLib's `ofRat` of the integer) are now
  computed on the words for every integer below `2^64` in magnitude, the rounding ones included:
  `Binary32.ofMagWord`/`Binary64.ofMagWord` take the sign and the magnitude as a `UInt64`, find
  `k = ⌊log₂ m⌋` by a six-step binary search (`CFloat.Conv.log2w`), shift the magnitude up to 24
  (53) bits when `k < 24` (`53`), else shift it right by `k - 23` (`k - 52`) rounding to nearest
  even (`CFloat.Conv.roundShiftRightEvenW`: quotient, remainder, half, ties to the even quotient),
  and add sign, exponent `127 + k` (`1023 + k`) and the significand without its leading one, so a
  round-up to `2^24` (`2^53`) carries into the exponent field. Proof: `ofRat` and FloatLib's dyadic
  rounding of `⟨n < 0, |n|, 0⟩` both round the real `n` (`Model.toReal_roundRatScaled_eq_roundAt`,
  `Model.toReal_roundDyadic_eq_roundAt`), so their finite nonzero results are equal
  (`CFloat.Conv.ofRat_int_eq_roundDyadicGeneral`); the dyadic rounding is FloatLib's integer
  algorithm `Model.roundDyadicGeneral` (`roundDyadicGeneral_eq_roundDyadic`), evaluated on
  `⟨s, m, 0⟩` in `Binary32.roundDyadicGeneral_int`/`Binary64.roundDyadicGeneral_int`; the word is
  matched in `ofMagWord_toNat` (with `roundShiftRightEvenW_toNat`, `log2w_toNat`). `Int`s of
  magnitude `2^64` or more (only `CFloat.ofInt32`/`ofInt64` called directly on an `Int` can have
  them) still go through `ofRat` (`ofInt32Slow`, `ofInt64Slow`). The earlier exact-only path
  (`ofIntBitsNat`, `ofRat_int_small`, `ofIntWord`, `toReal_ofRat_int`) is replaced.
- **No `Int`.** The eighteen wrappers the translator emits (`Int8.toBinary32` .. `USize.toBinary64`,
  defined as `CFloat.ofInt32 n.toInt` / `n.toNat`) each have a `@[csimp]` theorem
  `@Int64.toBinary64 = @Int64.toBinary64Impl` whose right side takes the magnitude from the integer
  word (`CFloat.absWord`: `if x < 0 then 0 - x.toUInt64 else x.toUInt64`, so `INT64_MIN` gives
  `2^63`; signed 8/16/32-bit sources through `toInt64`, unsigned ones through `toUInt64`) and calls
  `CFloat.ofMag32`/`ofMag64`; `Int64.toInt` of a value of magnitude `2^31` or more (a big-integer
  allocation) is no longer evaluated. The emitted Lean text is unchanged.
- **Narrow conversions.** `(uint8_t)f`, `(int8_t)f`, `(uint16_t)f`, `(int16_t)f` (from `float` and
  `double`) are undefined in C outside the type's range; clang on the reference target (arm64,
  `-O2 -ffp-contract=off -fno-fast-math`, Apple clang 17) emits `fcvtzs w` (truncation toward zero,
  saturation to `int32_t`, NaN: 0) for all four, and a store (`strb`/`strh`) keeps the low bits:
  stored, `(uint8_t)-221.0f` is 35, `(uint8_t)300.0f` 44, `(int8_t)200.0f` -56,
  `(uint16_t)-1.9f` 65535, `(int16_t)40000.0` -25536, `(uint8_t)1e12f` 255, `(uint8_t)-3e9f` 0,
  NaN 0. CFloat saturated to the narrow range instead (0, 255, 127, 0, 32767, 255, 0, 0).
  `Binary32.toInt8` .. `Binary64.toUInt16` are now `toInt32` followed by `Int32.toInt8`/`toInt16`
  (and `Int8.toUInt8`/`Int16.toUInt16`), the target's stored value, on the existing fast path
  (`truncSat32`/`truncSat64`); the 32- and 64-bit conversions (`fcvtzs`/`fcvtzu` with `w`/`x`, which
  saturate to the type) are unchanged. Used directly in a wider expression without a store, clang
  may keep the whole `int32_t` (`int r = (uint8_t)-221.0f;` gives -221, as an in-range value needs no
  truncation); no `UInt8` result reproduces that. The `--mission` special case of the translator
  (`Binary32.toInt32` then the integer conversion) now computes what the wrappers compute.

Measured with `cfloat_bench bench` (20 × 20,000 conversions per row, inputs prepared outside the
timing; checksums equal before and after except `Binary64.toUInt16`, whose inputs include negative
doubles, out of range, which now wrap as on the target):

| conversion | before (ns) | after (ns) |
|---|---|---|
| `Binary32.toInt32` | 12.0 | 12.4 |
| `Binary64.toInt32` | 12.4 | 12.6 |
| `Binary64.toInt64` | 15.9 | 16.3 |
| `Binary64.toUInt16` | 13.8 | 12.9 |
| `Int32.toBinary32` (\|n\| < 2^24, as in Phase 3) | 18.6 | 9.7 |
| `Int32.toBinary64` | 18.1 | 9.5 |
| `Int64.toBinary64` (\|n\| < 2^51, as in Phase 3) | 181.4 | 10.0 |
| `UInt32.toBinary32` | 16.9 | 10.0 |
| `Int32.toBinary32`, 2^24 ≤ \|n\| ≤ 2^31 | 862.9 | 9.8 |
| `UInt32.toBinary32`, 2^24 ≤ n < 2^32 | 827.5 | 9.2 |
| `Int64.toBinary64`, 2^31 ≤ \|n\| ≤ 2^53 | 180.2 | 10.0 |
| `Int64.toBinary64`, 2^53 ≤ \|n\| ≤ 2^63 | 1391.4 | 10.0 |
| `Int64.toBinary32`, \|n\| < 2^24 | 19.4 | 10.2 |
| `Int64.toBinary32`, 2^24 ≤ \|n\| ≤ 2^63 | 1053.1 | 10.2 |
| `UInt64.toBinary64`, n < 2^53 | 65.0 | 9.5 |
| `UInt64.toBinary64`, 2^63 ≤ n < 2^64 | 1407.6 | 9.5 |
| `UInt64.toBinary32`, 2^63 ≤ n < 2^64 | 1430.8 | 9.7 |
| `CFloat.ofInt64` on an `Int`, 2^53 ≤ \|n\| ≤ 2^64 | 1361.6 | 77.6 |
| `Binary64.toBinary32` | 8.7 | 8.9 |
| `Binary32.toBinary64` (Phase 1, unchanged) | 8.4 | 8.1 |

`cfloat_bench check 100000` (now also every wrapper `Int8.toBinary32` .. `USize.toBinary64` on the
integers of `intSamples`, each wrapped into the type, against `Ref.ofInt32`/`Ref.ofInt64` of the
type's value): 

```
float to integer: 3200768 conversions compared
integer to float: 202128 conversions compared
integer types to float: 1819152 conversions compared
double to float: 300050 conversions compared
differences: 0
```

Differential tests (0 differing lines; the NaN-only lines as before):

```
$ python3 difftest.py numeric mixed libm
literals: 33 floating literals; 0 elaborate in Lean to bits other than clang's
numeric: 0 of 80000 lines differ (100 lines equal only as NaN vs NaN with different bits)
mixed: 0 of 110000 lines differ (2120 lines equal only as NaN vs NaN with different bits)
libm: 0 of 440000 lines differ (600 lines equal only as NaN vs NaN with different bits)
$ python3 difftest.py ardupilot/AP_Math
free functions 0 of 25661, Vector2<float> 0 of 21421, Vector2<double> 0 of 21261, Vector3<float> 0 of 22539,
Vector3<double> 0 of 22159, Matrix3<float> 0 of 24650, QuaternionT<float> 0 of 25399,
Matrix3<double> 0 of 24650, QuaternionT<double> 0 of 25399 lines differ
```

`#print axioms` of the twenty `@[csimp]` theorems (`CFloat.ofInt32_eq_ofInt32Impl`,
`ofInt64_eq_ofInt64Impl`, `Int8.toBinary32_eq_toBinary32Impl` .. `USize.toBinary64_eq_toBinary64Impl`)
gives `[propext, Classical.choice, Quot.sound]`. `tests/golden/CFloat.lean` is the new
`support/CFloat.lean`; no generated Lean text changes.

## Phase 3: EKF data structures (2026-11-11)

PORT-PLAN.md section 6, "Phase 3", first part: the data forms of EKF3 (F9, F12, F15 and the type-level
rejections of the calibration run), `EKFGSF_yaw`, and the survey of what remains in the function bodies
of AP_NavEKF3, AP_NavEKF and AP_DAL. Every new construct is behind a new option, so the existing
translations are byte-identical (all goldens of `tests/golden` unchanged).

### Against the real headers and the reference configuration

The estimation code is translated against ArduPilot's real headers as the reference build preprocesses
them, not against `ardupilot/stubs`. `ardupilot/ref_flags.py SOURCE` prints the reference build's flags of
one unit (`build/reference/ap/build/sitl/compile_commands.json`, through `reference/build.py`'s
`flags_of`: waf's command line minus optimization, debug and dependency flags, plus the reference's
code generation flags, `reference/hal` first on the include path, relative paths made absolute; `--ast`
keeps the flags that change the AST, `--json` prints a list). `ardupilot/ekf_common.sh` (sourced by the
translation scripts) takes the flags of one unit for cpp2lean and checks a unity file: each included
source is byte-identical to ArduPilot's checkout (`ardupilot/src`; the translation includes the build
copy `build/reference/ap/libraries`, which differs only in the board header guard of
`reference/patches`), preprocesses alone to the same text with the unity's flags as with its own
unit's flags (EKF_Buffer.cpp, EKFGSF_yaw.cpp and AP_Math are compiled without `APM_BUILD_DIRECTORY`,
AP_NavEKF3 and AP_DAL with it), and preprocesses in the unity as alone (`check_unity.py`).
`EKF_Buffer.h` has no include guard and both `EKF_Buffer.cpp` and `AP_NavEKF3_core.h` include it: the
unity files `#import` it first (clang enters a file once imported by no later `#include`), so it is one
copy, as in each file's own unit. The difftest's C++ side compiles the ArduPilot sources from the build
copy with the reference flags (config `"ref_flags": "<unit>"`, warnings left out; `$REF` names the
build copy) and drives private members with `-fno-access-control` (config `"access_control": false`,
instead of `#define private public`, which ArduPilot's real headers do not survive).
The output's header comment shows the `--clang-arg` paths relative to the cpp2lean directory, also an
absolute `-I` directory that does not exist (the reference build's `modules/lwip/src/include`, a
submodule it does not check out), so the goldens do not depend on where the tree sits.

### New options

| option | meaning |
|---|---|
| `--ring-buffers` | F12: a type-erased container (`void *` storage, a `const uint8_t` element size set by its constructor) used through class template specializations `W<T> : C` whose constructor passes `sizeof(T)` is monomorphized per `W<T>` (below) |
| `--ekf-arrays` | F9, F15: `T a[N][M]` as one flat row-major `Array`, references to arrays, `memset` of whole objects, `memcpy` between objects with the same scalars, uninitialized local arrays, runtime indices into field-index views, local references through elements, member bounds of runtime loops, in-place writes of arrays held by array elements |
| `--ekf-types` | structs named by a typedef, structs with base structs as plain structs, brace-initialized scalar members, the union of an array and a struct (a view), unions of one-bit bit-fields over an integer, mutable static data members as World fields (with `--world`) |
| `--survey` | with `--keep-going`: every rejected statement of a function is reported (the translation goes on with the next statement), not only its first rejection; the output is not usable. `CPP2LEAN_SURVEY_METHODS=<file>` writes the member functions as translated (rejected statements left out), for measurements |

### Ring buffers (`--ring-buffers`, PORT-PLAN F12)

`AP_NavEKF/EKF_Buffer.{h,cpp}` are translated unmodified. For each specialization `W<T>` the
type-erased base `C` (`ekf_ring_buffer`, `ekf_imu_buffer`) is copied with its `void *buffer` as
`buffer : Array T` and a flag `buffer'alloc : Bool` (the pointer is not null); `C`'s member functions are
translated for `W<T>`, as inherited member functions are, and `C` itself is not translated. Recognized,
in `C`'s member functions only:

- accessors: a member function returning `void *` whose body is `return (void*)(((uint8_t*)buffer)+idx*uint32_t(elsize));`
  or a call of such an accessor with its parameter (`ekf_imu_buffer::get`): not translated; a call is
  element `idx` (the index converted to the accessor's parameter type);
- `void *` / `const void *` parameters: the element the caller passes as `&x` (by reference if the body
  copies into it); a wrapper's call `C::recall(&element, t)` passes `element`;
- `buffer = calloc(k, elsize)`: `k` zero elements (each the all-zero value of `T`, as `calloc` gives),
  `buffer'alloc := true` (allocation is assumed to succeed, as `new (std::nothrow)`; `calloc(0, n)` is
  not a null pointer on the reference target, so `init(0)` returns true as in C++); `buffer(nullptr)`
  in the constructor and the zero-filled object: no elements, not allocated; `if (buffer)`,
  `buffer == nullptr`, `!buffer`: the flag; `free(buffer)` only directly before a new `calloc` in the
  same function: no effect;
- `memcpy(element, get_offset(i), elsize)` and `memcpy(get_offset(i), element, elsize)`: an
  assignment; `memset(element, 0, elsize)`: the zero element; `memset(buffer, 0, k*uint32_t(elsize))`:
  the first `k` elements zero; `T *el = (T *)get_offset(i);` with `T` the element type or a base of it:
  `el->f` is the element's member;
- `EKF_IMU_buffer_t::operator[]` (`T *ret = (T *)ekf_imu_buffer::get(index); return *ret;`): as a value
  the element; as an lvalue (`storedOutput[i].quat = q`, AP_NavEKF3_core.cpp:1830) the element itself;
- `while (count > 0)` whose body decrements `count` once, at its top level, without `continue`
  (EKF_Buffer.cpp:55): at most `count` iterations, `for _ in [0:count₀] do if !test then break; ...`
  (exact, not fuel); a `for` loop bounded by a data member the body does not write (`index < _size`).

Rejected (tests/reject_phase3e.cpp): any other use of the storage, of a `void *` parameter or of an
accessor; a `void *`-returning member function of other shape; a `memcpy` with another count.

### Multidimensional arrays and in-place writes (`--ekf-arrays`, F9, F15)

`T a[N][M]` (also through a typedef, `Matrix24`, `ftype R_prev[2][3]`) is an `Array T` of N·M elements
with `a[i][j]` its element `i*M + j` (constant indices folded: `P[3][4]` is `P[76]!`); a row `a[i]` is
only an intermediate of a subscript (used as a value or `memset`: rejected). The leaves the difftest
prints are `a[i][j]` in C++. `memset(&x, 0, sizeof(x))` with `(void *)&x`, an array `a`, `&a[0]`,
`&a[0][0]` (EKF3's `memset(&Pmut[0][0], 0, sizeof(Pmut))`, `ZERO_FARRAY`): x zero. `memcpy(&x, &y,
sizeof(z))` between objects whose scalars in the first sizeof(z) bytes have the same offsets and types
(EKFGSF_yaw.cpp:535 copies the first two rows of a `Matrix3F` into `ftype R_prev[2][3]`): leaf by leaf.
`const_cast<const Matrix24 &>(Pmut)` (EKF3's `P`) is `Pmut`. A reference to an array (`Matrix24 &`,
`auto& nextP = KHP;`, which clang spells `double &[24][24]`) is the array. An uninitialized local array
starts at zero (C++ leaves it indeterminate; reading it before writing is undefined). A runtime index
into a field-index view (`ret[r]` of a `Matrix3F`, EKFGSF_yaw.cpp:623) is a `match` on the index; a local
non-const reference may go through elements whose indices do not change while it is live (variables
never assigned, or the counter of an enclosing counted loop: `Vector3F &row = ret[r];`).

**F15.** Lean's compiler already updates an array held by a structure in place: `{ s with P := s.P.set!
k v }` reuses the projection's reference when `s` is unique (also through nested structures,
`{ s with a.P := ... }`). It copies an array reached through an element of another array
(`s.EKF[m].P[k]`: `s.EKF[m]!` shares the element). For those writes (`EKFGSF_yaw`'s `EKF[mdl_idx].P[i][j]`,
the example's `cells[m].P[i][j]`) the translator takes each array and element out of its holder before
`set!` and puts it back after. Measured with `lean/F15Bench.lean` (`lake build f15_bench`, a 24×24
`Binary64` matrix, 576 element writes per call, 300 calls, each write a copy of another element):

| write | as emitted before | with --ekf-arrays |
|---|---|---|
| `s.P[k]` (member array) | 4.9 ns | 4.8 ns (the same code: no change needed) |
| `s.P[k]`, the value reading another member | 7.9 ns | 8.1 ns |
| `s.inner.P[k]` (array in a member structure) | 5.0 ns | (no change) |
| `s.EKF[m].P[k]` (array in an element of an array) | 639 ns | 10.4 ns |

PORT-PLAN 4.13 is corrected accordingly ("Phase 3:").

### Types of EKF3's data members (`--ekf-types`)

- `typedef struct { uint32_t time_ms; } EKF_obs_element_t;` is the record `EKF_obs_element_t`; a struct
  whose bases are structs without member functions (`struct gps_elements : EKF_obs_element_t`) is a
  plain structure with the bases' fields first, as C++ lays it out.
- `const ftype EKFGSF_gyroNoise{1.0e-1};`: the member's default.
- `union { Vector24 statesArray; struct state_elements stateStruct; };` (AP_NavEKF3_core.h:587): the array
  is the member; the struct is a view of it (`stateStruct.velocity.y` is `statesArray[5]!`,
  `stateStruct.quat` the `QuaternionF` built from elements 0-3, an assignment to it writes them), checked
  when every record is filled: the struct's scalar leaves are exactly the array's elements, in order.
- `union nav_filter_status { struct { bool attitude : 1; ... } flags; uint32_t value; }` and the anonymous
  form (`gpsCheckStatus`, AP_NavEKF3_core.h:1621, `union { struct { bool bad_sAcc : 1; ... }; uint16_t
  value; }`): the union is its integer; bit k (the k-th one-bit field) is read `(v >>> k &&& 1 != 0)`
  and written `(v &&& ~~~(1 <<< k)) ||| (if b then 1 <<< k else 0)` (bit-fields are allocated from the
  least significant bit on the little-endian target); the difftest prints `.value`.
- A mutable static data member of numbers or an array of numbers (`NavEKF_core_common::KHP`,
  `Kfusion`, the scratch space shared by every core) is a World field `Class'member` (with `--world`),
  zero at the start; its definition must not have an initializer.

### EKF_Buffer and EKFGSF_yaw

| translation | script (output) | Lean lines | ArduPilot lines |
|---|---|---|---|
| ring buffers | `ardupilot/translate_ekf_buffer.sh` (`out/EKF_Buffer/EKF_Buffer_lib.lean`) | 1537 (127 defs) | EKF_Buffer.h, .cpp (407), monomorphized at the 10 wrappers EKF3 declares in the reference configuration (`imu_elements`, `output_elements`; `gps`, `mag`, `baro`, `tas`, `of`, `vel_odm`, `wheel_odm`, `yaw` elements), with their 10 element structs (AP_NavEKF3_core.h:592-694) and the base `EKF_obs_element_t` |
| EKFGSF_yaw | `ardupilot/translate_ekfgsf.sh` (`out/EKFGSF/EKFGSF_lib.lean`) | 1244 (52 defs) | EKFGSF_yaw.h, .cpp (813), the AP_Math functions it calls (`check_shared.py` against AP_Math_lib: 33 shared declarations, 0 differ) |

`ardupilot/unity_ekf_buffer.cpp` instantiates each wrapper explicitly (`template class
EKF_obs_buffer_t<NavEKF3_core::gps_elements>;`): every member function, as the core's uses instantiate
those it calls. Differential tests (seed 20261104; `ardupilot/EKF_Buffer.json`, `ardupilot/EKFGSF.json`,
environment `ardupilot/ekf_env.cpp`: `AP_InternalError::error` records nothing, as `--drop` leaves it out):

```
$ python3 difftest.py ardupilot/EKF_Buffer
ardupilot/EKF_Buffer EKF_IMU_buffer_t<NavEKF3_core::imu_elements>: 0 of 3390 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_IMU_buffer_t<NavEKF3_core::output_elements>: 0 of 3410 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::gps_elements>: 0 of 3275 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::mag_elements>: 0 of 3159 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::baro_elements>: 0 of 3079 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::tas_elements>: 0 of 3123 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::of_elements>: 0 of 3479 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>: 0 of 3439 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>: 0 of 3279 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF_Buffer EKF_obs_buffer_t<NavEKF3_core::yaw_elements>: 0 of 3123 lines differ (0 tokens equal only as NaN vs NaN with different bits)
$ python3 difftest.py ardupilot/EKFGSF
ardupilot/EKFGSF EKFGSF_yaw (flight): 0 of 4375 lines differ (6150 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKFGSF EKFGSF_yaw (wild): 0 of 1875 lines differ (118435 tokens equal only as NaN vs NaN with different bits)
$ python3 difftest.py ekfdata pointers
ekfdata World: 0 of 20274 lines differ (1351 tokens equal only as NaN vs NaN with different bits)
pointers: 0 of 150000 lines differ (200 lines equal only as NaN vs NaN with different bits)
```

The buffer runs drive `init` (sizes 1-60, IMU 10-40; size 0 makes the next `push` divide by zero),
`push`/`push_youngest_element` with random elements (times in a 150 ms window), `recall` with times in
the same window (about one call in five finds an element), `get_oldest_element`, `operator[]` (indices
below the size), `reset`, `reset_history`; every state leaf, the `elsize` the model computes
(`sizeof(T)` from the record layout) and `buffer != nullptr` are compared. EKFGSF_yaw runs twice:
`flight` with physically plausible inputs only (delta angles ±0.01 rad and delta velocities about one g
over 11-13 ms, velocities ±10 m/s with accuracies 0.3-2 m/s, gyro biases ±0.02 rad/s), `wild` with 15%
of the random values from the free-function mixture (NaN, infinities, huge values); both end with the
corner calls. `getYawData`'s nullable `uint8_t *n_clips` is driven given and null (difftest config
`"nullable_params"`). Sensitivity: `dt < 100` changed to `dt < 90` in `recall` and `_youngest + 1` to
`+ 2` make 11-19 lines of each observation buffer and about 3200 of 3400 of each IMU buffer differ;
one wrong index in `forceSymmetry` (`P[0][1]` written as `P[1][1]`) makes 3790 of 4375 (flight) and
1719 of 1875 (wild) differ.

### The survey: what the bodies of AP_NavEKF3, AP_NavEKF and AP_DAL still need

`ardupilot/survey_ekf3.sh` runs `cpp2lean --keep-going --survey` with `--ekf-types --ekf-arrays
--ring-buffers --runtime-loops --pointer-params --world --ap-param --c-strings --byte-objects` over
`ardupilot/unity_ekf3_survey.cpp` (every source of the three libraries in the reference build, with
AP_Math and AP_Common's Location; seven files are compiled out entirely and not included) and groups the
rejections (`ardupilot/survey_group.py`). In a survey a class whose reference members name World
objects is translated alone too (to list its member functions' needs). The type-level rejections of the
calibration run are gone except the pointer members `NavEKF3_core *core`, `NavEKF3 *frontend`,
`EKFGSF_yaw *yawEstimator` (the other agent's F1). Every rejected statement counts once per rejected
construct:

| feature | count | examples |
|---|---|---|
| F1 pointer members, pointers to World objects (other agent) | 298 | `AP_DAL/AP_DAL.cpp:84`, `AP_DAL/AP_DAL.cpp:95`, `AP_DAL/AP_DAL.h:80` |
| F1 reference members bound to World objects (`dal`, `public_origin`; other agent) | 99 | `AP_NavEKF/AP_NavEKF_Source.cpp:363`, `AP_NavEKF3/AP_NavEKF3.cpp:783`, `AP_NavEKF3/AP_NavEKF3.cpp:797` |
| F1 calls on classes outside the translation (front ends, AP_AHRS, HAL) | 96 | `AP_DAL/AP_DAL.cpp:18`, `AP_DAL/AP_DAL.cpp:33`, `AP_DAL/AP_DAL.cpp:35` |
| F13 AP_Param (`frontend->_param` values, AP_Enum conversions, var_info) | 19 | `AP_NavEKF/AP_NavEKF_Source.cpp:32`, `AP_NavEKF3/AP_NavEKF3.h:323`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:149` |
| F7 text (GCS send_text, snprintf, vsnprintf, panic, FILE) | 3 | `AP_DAL/AP_DAL.cpp:585`, `AP_Math/AP_Math.cpp:452`, `AP_Math/AP_Math.cpp:475` |
| F8 loops bounded by a data member whose type does not bound it (`i <= stateIndexLim`) | 15 | `AP_DAL/AP_DAL_Baro.cpp:22`, `AP_DAL/AP_DAL_Compass.cpp:10`, `AP_DAL/AP_DAL_Compass.cpp:31` |
| local `const` references to state that the function writes (`const ftype &q0 = stateStruct.quat[0]`) | 12 | `AP_DAL/AP_DAL_GPS.cpp:21`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:967`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:968` |
| F10 static locals and mutable globals | 12 | `AP_Math/AP_Math.cpp:352`, `AP_Math/AP_Math.cpp:353`, `AP_Math/AP_Math.cpp:443` |
| survey configuration: AP_Math templates and functions included as translated files (a lib-dir in a translation) | 28 | `AP_Common/Location.cpp:269`, `AP_Common/Location.cpp:289`, `AP_Common/Location.cpp:307` |
| HAL clock reads (`AP_HAL::micros`, boundary functions) | 2 | `AP_DAL/AP_DAL.cpp:60`, `AP_DAL/AP_DAL.cpp:338` |
| views of the state's struct view (`stateStruct.position.xy() = ...`), calls on returned references | 5 | `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:42`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:130`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:134` |
| definite assignment the checker cannot prove (`ftype SA5_inv; if (...) SA5_inv = ...`) | 5 | `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:931`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:987`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1064` |
| enum ordering comparisons | 4 | `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:572`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:744`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:240` |
| brace initializer lists of objects (`AP_DAL::log_*` records) | 7 | `AP_DAL/AP_DAL.cpp:192`, `AP_DAL/AP_DAL.cpp:203`, `AP_DAL/AP_DAL.cpp:215` |
| other | 3 | `AP_DAL/AP_DAL.cpp:286`, `AP_DAL/AP_DAL.h:149`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:612` |

Other: `AP_DAL/AP_DAL.cpp:286`, `AP_DAL/AP_DAL.h:149`: `AP_DAL::malloc_type`/`free_type`, the heap allocation through which `NavEKF3::InitialiseFilter` allocates the cores (F4); `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:612`: an array used as a pointer.

What the next stage needs, by size: (1) F1 (the other agent): `frontend->` (153 statements read the
front end's parameters through the pointer), `dal.` (91 reads of the DAL through the reference member),
`core[i].` and `if (core)`, `yawEstimator->`; these make up 493 of the 608. (2) The DAL's own state: its
`log_R*` records are now translated (AP_DAL/LogStructure.h), its reads of the front ends
(`AP::ins()`, `AP::baro()`, ...) are boundary or World reads (96). (3) Parameters: `frontend->_param`
values as `AP_Float` reads (F13, 19 constructions of `AP_ParamT`), `AP_Enum` conversions of
`AP_NavEKF_Source`. (4) Smaller: 15 loops bounded by `stateIndexLim` with `<=` (a `uint8_t` member whose
values, constants up to 23, the types do not bound: needs a value range or a fuel bound), 12 `const`
references into the state view in functions that write the state (`const ftype &q0 =
stateStruct.quat[0]`: correct as copies only if nothing writes the quaternion while they are live), 5
writes through `stateStruct.position.xy()` (a layout-prefix view of a member of the array view), 5
definite-assignment cases the checker cannot prove, 4 ordering comparisons of enum values, 7 brace
initializers of DAL log records, static locals and globals (12).

**Location.** With the real headers `AP_AHRS_ENABLED` is 1 inside `Location.cpp` (the stub `AP_AHRS.h`
of Phase 2 made it 0): the constructors from an EKF offset, `from_ekf_offset_NED_m`, the
`get_vector_*` templates and `get_alt_cm`'s `ABOVE_HOME`/`ABOVE_ORIGIN` cases (and so `change_alt_frame`,
`get_height_above`, ...) read `AP::ahrs()` (home, EKF origin) instead of returning false or being
compiled out. Phase 2's Location translation dropped exactly those members, so it is unaffected; the
members EKF3 calls (`offset`, `get_distance_NE_ftype`, `get_distance_NE_postype`, `set_alt_cm`,
`copy_alt_from`, `initialised`) are the same code in both configurations. For the vehicle, the
AHRS-reading members make `Location` depend on the AHRS that owns the EKF (a World cycle, F1).

**CovariancePrediction.** Its 795 lines of generated straight-line code (AP_NavEKF3_core.cpp:1175-1730:
`PS0`..`PS`*n* temporaries and `nextP[i][j] = ...`, `nextP` the World's `NavEKF_core_common'KHP`) now
translate; the function as a whole needs `frontend->` (F1), the pointer parameter `rotVarVecPtr` and the
`<= stateIndexLim` loops. Measured on its emitted lines (`lean/CovPredBench.lean`, copied from the survey
output, the 520 `let PS..` and 297 `nextP` writes, also those inside `if`s, at the top level; not a
translation): Lean's elaborator stops with "maximum recursion depth has been reached" (the `do`
block of 520 statements nests one level per statement); with `set_option maxRecDepth 20000` the
definition elaborates in about 2.8 s (8.4 s for the file against 5.7 s for its imports alone) and
compiled it runs in 783 µs per call (about 2800 `Binary64` operations: 280 ns each, FloatLib's
software arithmetic; no array copies). At EKF3's 83 Hz prediction rate that is 65 ms per second per
core. The translator should either emit `set_option maxRecDepth` for long bodies or split them into
blocks passing the live temporaries.

### Examples and tests

`examples/ekfdata.cpp` (golden `tests/golden/EKFData.lean`, `examples/ekfdata.json`: `--nest --world --ekf-types
--ekf-arrays --ring-buffers --runtime-loops`; `--nest` puts its `World` in namespace `EKFData`, so that the
difftest's `Main.lean` can import it next to `Worlds`, whose `World` is top-level) has each construct above in a small form (a type-erased ring
buffer behind a wrapper, a typedef'd struct and a derived one, 2D member and local arrays, `memset` and
`memcpy` forms, an array of structs holding 2D arrays written in place, a runtime field index with a local
reference, an array/struct union, both bit-union forms, a mutable static array in the World, a count-down
`while`) and is difftested as a World (`python3 difftest.py ekfdata`). `tests/reject_phase3e.cpp` holds
the limits (10 rejections). `tests/run_tests.sh` translates the two ArduPilot translations against their
goldens (`tests/golden/ardupilot/EKF_Buffer_lib.lean`, `EKFGSF_lib.lean`) and runs their difftests when
the reference build is present.

Difftest additions: `$REF` in `cxx_flags`, configs `ref_flags`, `access_control`, `only_own` (drive only
the class's own member functions, not those of a private base), `enum_leaves: "all"` (also struct
arguments by non-const reference with enum leaves), `nullable_params` (a nullable out-pointer is driven
given or null, by a flag token), `cxx_extra` (further flags for an example's drivers); World runs print
the World's static data members (`Class::member` in C++); a `bool` leaf may be a C++ expression
(`buffer != nullptr`).

## Phase 3: World pointers, sensor front ends, HAL delays (2026-11-11)

PORT-PLAN.md section 6, "Phase 3" (estimation), second stage: the World features the estimator needs
(F1 rest, F2, F4, F11, the self-reach cycle, and a narrow F3 for the HAL's timer processes), the
decision on the HAL boundary with delays (PORT-PLAN.md, marked "Phase 3:"), and a survey of what still
blocks the four sensor front ends. Everything below is gated by the new options: every earlier
translation (the examples, the rejection tests, the ArduPilot translations, among them EKF_Buffer and EKFGSF of "Phase 3: EKF data structures", musl) translates to
the same bytes as before.

### New options

| option | meaning |
|---|---|
| `--world-pointers` | (with `--world`) a pointer to a translated class is a tag `WPtr` of the program's objects; calls through it dispatch; `new` and placement new fill heap slots of the World; static singleton pointers of classes without a file-scope object are World fields; `Functor<void>` (AP_HAL::MemberProc) is a tag `WFun`; a call that reaches the caller's own object through the World stores and reloads it; functions defined in a namespace are translated |
| `--semaphores C1,C2,...` | classes whose objects are semaphores (`HALSITL::Semaphore`, `WithSemaphore`, `AP_HAL::Semaphore`): members of them are not state, local objects (`WITH_SEMAPHORE`) are no statement, `take`/`take_nonblocking`/`give` are `true`, `take_blocking` nothing (one thread, PORT-PLAN 4.11) |
| `--heap-alloc F` | a function returning raw memory for `(C *)F(sizeof(C) * k, ...)` (default `malloc`, `calloc`; AP_DAL's `malloc_type` would be named here) |

### The model (`--world-pointers`)

- **Pointers are tags.** `inductive WPtr` has `null`, one constructor per file-scope object of a
  translated class (`WPtr.barometer`) and one per class that `new` creates (`WPtr.heap'SimBaro (i :
  Nat)`, the object with index i among that class's heap objects). A pointer member, local, parameter,
  result, array element (`AP_Baro_Backend *drivers[]`) is a `WPtr`; `nullptr` is `WPtr.null`; `p ==
  q`, `p != nullptr`, `!p`, `if (p)` compare tags; casts between a class and its bases keep the tag.
- **Closed world by class, no points-to analysis.** A pointer of static type `B *` can point only to
  an object of B or of a class derived from it, and the translator knows every such object: the
  file-scope objects and the heap objects of the classes `new` creates anywhere in the program
  (a pre-pass over the AST). So the target set of a pointer is computed from its type. With one
  possible object (`frontend->gain` in an EKF core: the one `NavEKF3`; `core[i]` into the heap slots of
  one class) a member access or call is on that object's path (`w.filter`, `w.heap'Core[(WPtr.index
  core) + i]!`); a null pointer there is undefined behavior in C++ and not modeled. With several
  (`drivers[i]->update()` over two back-end classes), a call is a dispatch function
  `WPtr.call'B'm (ptr : WPtr) (w : World) ... : World × ...` with one `match` arm per possible object,
  which calls the final overrider of that object's class on its field or slot and stores its state
  back; a null pointer changes nothing (undefined in C++). The arms must agree on parameters, reference
  results and result (they do for overriders). Member reads through such a pointer are rejected (only
  calls dispatch).
- **Heap slots (F4).** The World has `heap'C : Array C.State := #[]` per heap class C. `new C(args)` and
  `new (std::nothrow) C(args)` construct the state (the constructor may take and return the World:
  `AP_Baro_SITL`'s registers with its front end and the scheduler) and push it; the value is
  `WPtr.heap'C i`. Allocation never fails (as `new T[k]` in Phase 2); `delete p` leaves the slot (nothing
  refers to it again; the C++ difftest driver keeps the memory so that both sides print the object's
  last state). `(C *)f(sizeof(C) * k)` of a `--heap-alloc` function reserves k zero states and points to
  the first; `new (&p[i]) C(args)` constructs into slot `index p + i` (AP_NavEKF3.cpp:850-860's cores).
  A static `C *_singleton` of a class without a file-scope object is a World field `C'_singleton : WPtr`;
  its `get_singleton()` that allocates on first call (`AP_DAL::get_singleton()`) is translated as
  written, a static function of the World.
- **References to World objects.** A reference member of a heap object (`AP_Baro &_frontend`) is the one
  file-scope object of that class; a reference parameter of such a class (`detect(AP_InertialSensor
  &_imu)`) is another name for that object (not passed), and every argument must denote it
  (`*this`, the object, an alias); `AP::baro()` inside AP_Baro's own member functions is `s`.
- **The self-reach cycle.** While a member function of World object g runs, g's state is in `s`. A call
  whose callee may reach g through the World (a dispatch to a back end that calls `_copy_to_frontend`;
  `hal.scheduler->delay` whose timer processes reach g; a constructor that registers with g) is preceded
  by `w := { w with g := s }` (and g's parameters) and, if the callee may change the World, followed by
  `s := w.g`. The same for a heap object: it receives its own pointer `self'`, and its state goes into
  and comes back from `w.heap'C[index self']!`. A heap object's constructor that may reach the object
  being constructed, and a write through a pointer that may point to the object whose member function
  runs, are rejected.
- **`this` as a value.** In a member function of a World object, `WPtr.<object>`; of a heap object,
  `self'`, which its callers pass (`(WPtr.heap'C i)`; in a constructor the slot it will take).
- **Functors (narrow F3).** `Functor<void>` (`AP_HAL::MemberProc`) is `inductive WFun` with `null` and one
  constructor per `Functor<void>::bind<T, &T::m>` in the program (FUNCTOR_BIND, FUNCTOR_BIND_MEMBER),
  holding the object's pointer. `f()` is `WFun.call f w`: a `match` over the bindings, each calling the
  dispatch function of m over the objects of T; `f == g`, `f = g`, `if (f)` on the tags. Functors with
  arguments or results are rejected; the scheduler's task table (F3 proper) is not done.
- **Functions of the World.** Free functions and static member functions that reach the World take
  `(w : World)` and return it when they change it; functions defined inside a namespace are translated
  (the HAL stand-in's `AP_HAL::micros64()` reads the scheduler stand-in's clock).

`examples/worldptr.cpp` (golden `tests/golden/WorldPtrs.lean`) has each construct on the sensor front
ends' patterns: back ends allocated at init into `Backend *drivers[3]`, one through a static `detect`
that deletes it when its init fails, virtual dispatch over two back-end classes, `nullptr` tests, a back
end calling its front end while the front end's `update()` runs, a singleton allocated on first use,
cores placement-constructed in `malloc`ed memory and called by index, semaphore members and
`WITH_SEMAPHORE`. `examples/worlddelay.cpp` (golden `tests/golden/WorldDelay.lean`) is the delay
mechanism below in miniature. `tests/reject_phase3f.cpp` holds the limits (8 rejections: `this` as a
value in a class without objects, a member read through a pointer to several objects, a call through a
pointer to a class without objects, placement new elsewhere than a heap slot, a raw allocation not of
`sizeof(C) * k`, a semaphore member function with a non-boolean result, a pointer to a class made from a
pointer to something else, a heap object's constructor reaching the object being constructed).

### The HAL boundary with delays (PORT-PLAN.md, "Phase 3:" decision)

Estimator code waits inside init and calibration (`AP_Baro::calibrate`, `AP_InertialSensor`'s gyro
calibration and `wait_for_sample`, `Compass::init`), and in the lock-step HAL a wait consumes input lines
and runs the timer processes, i.e. the sensor stand-ins, which call the front ends. So a delay is code of
the World, not a boundary call. Decided and implemented:

- `reference/hal/est_scheduler.h`, `.cpp`: `EstScheduler`, a class of ArduPilot's `AP_HAL::Scheduler`
  interface with the logic of `reference/hal/lockstep.cpp`'s scheduler (HALSITL's `delay`,
  `delay_microseconds` stepping until the time has passed, `register_timer_process` without duplicates,
  timer processes run in registration order per consumed line, not re-entered), whose input lines are
  data of the object: a ring of 1024 parsed records (`EstRecord`: time, IMU samples, baro, mag, GPS;
  boot init consumes 915 lines inside delays, REFERENCE.md), fed by the harness before the calls that
  consume them. `AP_HAL::micros64`, `millis64`, `micros`, `millis` are defined there on its clock. Left
  out, none of which the estimator observes: delay callbacks (GCS and notify code), IO processes and the
  timer failsafe (AP_Param saving, Copter's failsafe_check), the output line; at the end of the records
  a wait returns (`exhausted()`) instead of ending the process. It is not part of copter_ref (the
  reference keeps lockstep.cpp; `reference/build.py` compiles `HAL_SOURCES` only, so the new file does
  not change it). `ardupilot/translate_est_scheduler.sh` translates it with ArduPilot's real headers and
  the reference configuration (`build/reference/ap`, `-I reference/hal` first) into
  `ardupilot/out/EstScheduler/EstScheduler_lib.lean` (374 lines, golden
  `tests/golden/ardupilot/EstScheduler_lib.lean`; it elaborates without warnings); not difftested on
  its own: the difftest harness does not compile ArduPilot targets against the real headers yet.
- The sensor stand-ins of `reference/hal/sensors.cpp` are to be translated together with ArduPilot
  (they are ArduPilot's back-end classes; translating them keeps their semantics the reference's), the
  HAL's other functions (`get_soft_armed`, `malloc_type`, `in_main_thread`, `persistent_data`) are
  boundary inputs or small stand-ins. Not done: sensors.cpp reads the line from a namespace-scope global
  (`Lockstep::in`, with a two-dimensional `imu[2][8]`), keeps the GPS record in an anonymous namespace,
  uses static locals and `struct timeval`; to translate it, it must read the current record from the
  scheduler (`est_scheduler.current()` in the translation, `Lockstep::in` in copter_ref, behind one
  accessor both builds define) and flatten the samples, and the reference must then be rebuilt and
  replayed (`sim/out/lockstep-flight`, byte for byte). sensors.cpp is unchanged here.

`examples/worlddelay.cpp` runs the mechanism end to end: a scheduler stand-in of the same logic over a
ring of records the harness feeds, a back end allocated at init whose constructor registers a timer
process with `FUNCTOR_BIND_MEMBER` (its own pointer), a front end that calibrates through `delay` as
AP_Baro::calibrate does (wait until healthy in 10 ms steps, then average), during which the timer
process latches samples and calls back into the front end; the clock read through `HAL::millis()`.
66 of the difftest's 194 calibrations succeed (the others time out or run out of records, as intended
corners).

### Difftest additions

- World pointers and functors on the lines: a pointer leaf is `p:<name>` (`WPtr.name`: `null`, the
  object, `heap'C#i`; C++: the address looked up among the file-scope objects and the recorded
  allocations); a functor leaf `p:<binding>@<object>` (C++: its wrapper compared with
  `&Functor<void>::method_wrapper<T, &T::m>`).
- Heap objects: after the World objects' leaves, per heap class `h:<count>` and each object's leaves in
  creation order. The C++ driver records every allocation (global `operator new`, both forms, and
  `malloc` through a macro) in order, never frees (`operator delete` keeps the memory of a deleted back
  end, whose slot the Lean side keeps), and classifies an allocation by its size (the classes of `new`
  must have distinct sizes, checked by `static_assert`; placement memory holds a multiple of its class).
- `CPP2LEAN_MUTATE` applies to examples too.

### Results (seed 20261104)

```
worldptr World: 0 of 20123 lines differ (0 tokens equal only as NaN vs NaN with different bits)
worlddelay World: 0 of 20083 lines differ (0 tokens equal only as NaN vs NaN with different bits)
world World: 0 of 20083 lines differ (14 tokens equal only as NaN vs NaN with different bits)
navigate World: 0 of 20680 lines differ (863 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (defaults): 0 of 46778 lines differ (304741 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (tuned): 0 of 43690 lines differ (255044 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (course): 0 of 21451 lines differ (724 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (linear): 0 of 21683 lines differ (1653 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (frames): 0 of 22234 lines differ (17208 tokens equal only as NaN vs NaN with different bits)
ardupilot/Copter World (spool): 0 of 21687 lines differ (26963 tokens equal only as NaN vs NaN with different bits)
```

Sensitivity (`CPP2LEAN_MUTATE` on the examples): the reload `s := w.barometer` after the calls that
reach the barometer removed (3 places: the self-reach cycle broken), 19,744 of 20,123 worldptr lines
differ; the cores called at the first core's index only, 19,952 of 20,123.

### The sensor front ends: not translated yet (see "Phase 3: sensor front ends and AP_Param" for the next stage)

The four front ends (AP_InertialSensor + Backend, AP_Baro + Backend + atmosphere, Compass + Backend,
AP_GPS + GPS_Backend) with the reference's headers and configuration, all their member functions
(`--keep-going`, one unity, `build/survey/unity_sensors_survey.cpp` in the work clone): 221 rejections
before this stage, 159 with `--world-pointers --semaphores --general-loops` (AP_InertialSensor 70 to 58,
AP_Baro 29 to 17, Compass 58 to 27, AP_GPS 61 to 52); 11 of the 159 are calls through back-end pointers
that disappear when the stand-ins are part of the unity. What remains is not World modeling:

- **AP_Param beyond scalar members** (the largest group, about 60): `AP_Vector3f` parameters (19:
  INS offsets and scales, compass offsets, GPS antenna positions), arrays of parameters (`AP_Int8[3]`,
  `AP_UInt32[3]`), parameters inside arrays of structs (`AP_Baro::sensors[i].ground_pressure`,
  `bus_id`), arrays of parameter classes (`AP_GPS::Params params[3]`), Compass's
  `RestrictIDTypeArray<AP_Int8, 3, Priority>`, and the conversions, `set_default`, `save`,
  `set_and_notify` on them. `--ap-param` handles scalar members of a class only; this needs Params
  structures with arrays and vectors and their `var_info` offsets (`AP_GROUPINFO` into array elements),
  i.e. part of F13.
- Types from headers outside the unity: `AP_GPS_FixType` and its enumerators, `Location` (AP_Common,
  translated in Phase 2: as a `--lib-dir`), `JitterCorrection`, `Compass_PerMotor`, `struct tm`
  (GPS_Backend's time conversion), the MAVLink types of the GPS's message handlers (only reachable
  through GCS: `--drop`).
- Pointers to classes that are compiled-out or not in the estimator (`AP_HAL::UARTDriver *` of the GPS
  ports, `AP_AccelCal *`, `AccelCalibrator *`, `AuxiliaryBus *`, `FastRateBuffer *`, `CompassLearn *`):
  null in this configuration; they need `--boundary` or a stand-in each.
- Function pointers of the external-bus probes (`probe_i2c_dev_probefn_t`, AP_Baro's `_probe_*`): not
  reachable on SITL; `--drop`.
- Smaller constructs: AP_Baro_atmosphere's table of an anonymous struct type; an anonymous enum member
  (AP_Baro's `PROBE_*`); range-for over a member array (`for (auto &sensor : sensors)`, AP_Baro::init);
  local references to members that change (`Vector3f &prime_gyro_vec`, AP_InertialSensor); `AP_Enum`
  locals (AP_GPS); `operator*` of a template not instantiated in the unity; `uint8_t` counters bounded
  by `uint64_t` values.

The stand-ins of `reference/hal/sensors.cpp` need the refactoring above (current record behind an
accessor, flat samples) before they join the unity. Next stage (in order): the AP_Param extension;
`--lib-dir` mode with `--use` entry points for the vehicle's paths (init, `wait_for_sample`, `update`,
`periodic`, `accumulate`, `read`, the getters AP_DAL reads), so that the unreachable code is not
translated; the sensors.cpp refactoring and a reference rebuild/replay; a World difftest of the front ends
through their public functions and the stand-ins' timer processes, then the replay of
`sim/out/lockstep-flight/inputs.txt` against an extended `--est` probe.

## Phase 3: sensor front ends and AP_Param (2026-11-11)

PORT-PLAN.md section 6, "Phase 3" (estimation), third stage: the barometer and compass front ends
(AP_Baro, Compass) translated with the reference's sensor stand-ins, the SITL::SIM stand-in and the HAL
scheduler stand-in as one World, difftested and replayed against the reference vehicle; AP_Param beyond
scalar members (part of F13); the stand-ins refactored to be shared by the reference and the
translation. AP_InertialSensor and AP_GPS are not translated yet: their remaining needs are listed at the
end. Everything new is behind new options (`--front-ends`, `--param-ext`, `--world-class`,
`--param-name`): every earlier translation translates to the same bytes (the goldens of `tests/golden`
and `tests/golden/ardupilot`, the rejection tests and musl unchanged), except EstScheduler's, whose
source changed (below).

### New options

| option | meaning |
|---|---|
| `--front-ends` | the constructs of the front ends (below): classes and functions defined inside named namespaces, pointers to polymorphic library classes as World pointers, `hal.<driver>->m()` on the World's object of the driver's class, singleton accessors returning pointers, reference-returning accessors with arguments as paths, live local references and pointers as aliases, range-for over arrays, anonymous file-scope struct tables, multi-bit bit-field unions, conversion operators and member function templates of library classes, `operator++`/`--`, a `continue` in a loop without a constant trip count, nullable `const T *` parameters, boundary inputs of heap classes, zero-initialized static members as World fields |
| `--param-ext` | (with `--ap-param`) AP_Param's parameter classes (`AP_ParamT`, `AP_ParamV`, `AP_ParamTBase`, `AP_Enum`) are library classes translated from `AP_Param.h` and `AP_ParamT.cpp`; parameters are state; `setup_object_defaults` over member paths with constant indices; storage queries as inputs (below) |
| `--world-class C1,C2` | (with `--front-ends`) library classes whose pointers are World pointers although they are not polymorphic (`SITL::SIM`), or which have no object (`CompassLearn`: always null) |
| `--param-name NAME=object.member[k]...` | (with `--param-ext`) the parameter `AP_Param::set_default_by_name("NAME", v)` sets (the compass stand-in's `COMPASS_SCALE`) |

### AP_Param (`--param-ext`, part of F13)

`--ap-param` (Phase 3 of the translator) made a scalar member of type `AP_ParamT<T>` a field of the class's
`Params` and rejected everything else; the front ends need `AP_Vector3f` parameters (19 in the four front
ends), arrays of parameters (`AP_Int8 _use_old_param[3]`, `AP_UInt32 extra_dev_id[5]`), parameters inside
arrays of structs (`AP_Baro::sensors[i].ground_pressure`, `bus_id`; `Compass::_state._priv_instance[i]`'s
`offset`, `dev_id`, `scale_factor`, ...), arrays of parameter groups (`AP_GPS::Params params[3]`) and
`RestrictIDTypeArray<AP_Int8, 3, Priority>`. With `--param-ext`:

- **Parameters are objects of their class, translated from ArduPilot.** `AP_ParamT<T, PT>`, `AP_ParamV<T,
  PT>`, `AP_ParamTBase` and `AP_Enum<E>` are library classes like any other (`AP_Param` is their base,
  without data members): an `AP_Float` member is a field of type `AP_ParamT_float_4.State` (its `_value`),
  in the object's state, at any depth (arrays, structs, arrays of structs, groups). `get()`, `set()`,
  `set_and_save()`, `set_and_save_ifchanged()` (which does not set an equal value: `-0` stays `+0`),
  `set_and_notify()`, the conversion `operator const T &()` (a member function template for `AP_Float`)
  and `explicit operator int ()` are their translations from `AP_Param.h`/`AP_ParamT.cpp`. clang names
  the specializations by the values of their `ap_var_type` arguments (`AP_ParamT<float, 4>`) and the
  types by the enumerators and typedefs (`AP_ParamT<float, AP_PARAM_FLOAT>`, `AP_ParamTBase<int8_t, 1>`):
  the translator maps one to the other. Parameters written at run time (the barometer's ground pressure
  by `calibrate`, its field elevation, the compass's offsets and device ids, its priority list) are
  ordinary state writes; nothing distinguishes them from constants.
- **Defaults.** `AP_Param::setup_object_defaults(this, var_info)` is translated as AP_Param.cpp:1524-1542
  does it: for each entry of the class's table, in order, the float default converted to the entry's
  type (`AP_PARAM_INT8`/`16`/`32`: a float to `int8_t`/`int16_t`/`int32_t` conversion, stored in the
  member's `_value`, so an `AP_UInt32` gets the bits of the `int32_t`), for `AP_PARAM_VECTOR3F` the default
  in each component; nested groups (`AP_SUBGROUPINFO`, `AP_GROUPINFO` of a group object) are skipped, as there (their own constructors set their defaults: `Compass_PerMotor`, `AP_GPS::Params`,
  `AP_InertialSensor_Params`). The entry's member is the operand of its `sizeof(std::declval<C>().m...)`
  check: a path through data members and constant array indices (`sensors[1].ground_pressure`,
  `_state._priv_instance[2].offset`, `compensation[3]`); a default pointer (`AP_GROUPINFO_FLAGS_DEFAULT_POINTER`)
  is rejected (none in the front ends); parameter overrides from a defaults file do not exist in the model
  (the reference has none).
- **Storage is the boundary.** `save()` and `notify()` have no effect (`--drop`: saving to storage, and the
  GCS notification, are outside the model; `save()` is not a boundary event, since storage contents are
  not part of the estimator's state); `configured()` and `load()` are boundary inputs of the calling object
  (`inp.<param>_configured`, one per parameter and call site's text); `set_default(v)` sets the value unless
  that input says the parameter is stored (its registration of the default with the defaults list is the
  defaults file's: outside); `AP_Param::set_default_by_name("COMPASS_SCALE", 1)` (the compass stand-in, as
  SITL's) is `set_default` of the member `--param-name` names, with "not stored" (the C++ side of the
  difftest stores nothing either; the reference's image does not store the scale factors). `configured()`,
  `load()` and `set_default` are implemented but not reached by the barometer's and compass's paths (AP_GPS
  and AP_InertialSensor call them). AP_Param's
  storage conversions (`convert_parameter_width`, `convert_old_parameters`, AP_GPS's `convert_parameters`)
  were met in AP_GPS only and are not translated. The parameters the vehicle loads from storage at boot
  are the replay's initial state (below).

### The front ends' constructs (`--front-ends`)

- Classes, out-of-line members and functions defined inside a named namespace (`namespace SITL { class SIM
  ... }`, `SIM::SIM()` inside it, `namespace AP { SITL::SIM *sitl() }`) are translated as those at file
  scope. A singleton accessor returning a pointer (`AP::sitl()`, through `SITL::SIM::get_singleton()` of a
  library class) is the tag of the class's World object.
- World pointers to library classes: to a polymorphic class (`AP_Compass_Backend *_backends[]`), or one
  named by `--world-class`. A pointer to a class without objects in the World (`CompassLearn *`, a GPS
  UART) is null: a call through it is not reached (undefined behavior if it were) and is the zero of its
  result with a comment; a pointer the boundary returns to such a class (`find_serial`) is null.
- `hal.scheduler->delay(10)`: `hal` (`extern const AP_HAL::HAL &hal`, `--boundary AP_HAL::HAL`) is the
  boundary, but a pointer member of it to a class the World has one object of is that object
  (`est_scheduler`): delays are calls on the World. Other drivers are boundary reads (`hal.util->
  get_soft_armed()`, `was_watchdog_reset()`, `hal.rcout->read_last_sent(...)`).
- Accessors returning references, with arguments (`RestrictIDTypeArray::operator[](const Priority &)`,
  `Compass::_get_state(Priority)`, the INS parameter wrappers and their `const_cast` const twins): the path
  of the returned member or element, with `this` the call's object and the arguments computed once, before.
  So `_state[i].healthy = ...`, `_priority_did_stored_list[j].set_and_save_ifchanged(0)` and
  `Compass::mag_state &state = _compass._state[Compass::StateIndex(instance)];` are writes and aliases of
  that element.
- Local references and pointers to locations that change while they are live (`const Vector3f &c =
  compensation[i].get();`, `struct detect_state *dstate = &detect_state[instance];` used as `dstate->x`) are
  other names for the location, their indices computed at the declaration (C++'s binding); in a const
  member function a reference to a view of the object's data (`primary_mag_field.xy()`) is a copy.
- `for (auto &sensor : sensors)` over an array member or variable: a counted loop, the variable a name of the
  element (a copy for `auto`).
- `static const struct { float amsl_m; ... } atmospheric_1976_consts[] = {...}` (AP_Baro_atmosphere.cpp): the
  anonymous struct is named after the variable (`atmospheric_1976_consts_t`).
- `union DeviceId { struct DeviceStructure devid_s; uint32_t devid; }` (AP_HAL/Device.h:378): the union is its
  integer; a field of the struct is `w` bits at bit `off`, laid out as the Itanium ABI lays out bit-fields
  (`enum BusType bus_type : 3`, `uint8_t bus : 5`, then whole bytes), read `(v >>> off) &&& mask` and
  converted (an enum through `ofInt`), written by masking (`AP_HAL::Device::make_bus_id`).
- Conversion operators and member function templates of library classes (`template<bool X = true> operator
  const float &()` of `AP_ParamT<float>`): member functions named `op_to_float`; `operator++(int)` and
  `operator--` (`op_inc`, `op_dec`; the unnamed `int` parameter named after its position); the
  `explicit` constructor of a functional cast (`Priority(i)`).
- A `continue` in a `for` loop without a constant trip count (`for (Priority i(0); i<COMPASS_MAX_INSTANCES;
  i++)` with a class counter): the step runs at the top of every iteration but the first.
- A nullable `const T *` parameter with a null default (`drain_accumulated_samples(const Vector3f *scaling =
  NULL)`, `if (scaling)`): a flag and the value, not written back.
- A boundary read of a heap object (the compass back end's `AP::battery().current_amps(current)`): the class's
  inputs are one World field `heap'C'inp`, set by the caller as a World object's inputs.
- A member initialized from another member (`SITL::CompassSim _compass_sim{sitl_instance}`, a scalar
  `uint8_t c{_index}`) is initialized by each constructor; a member of a class whose default constructor
  does not give zero (`Quaternion` in `struct sitl_fdm`) gets that constructor; a static data member
  defined `= 0` (`AP_InertialSensor_SITL::bus_id`) is a World field; a second variable of a name in a
  function gets a fresh name (Lean does not shadow a mutable variable); the out-of-line definition of a
  singleton pointer (`SIM *SIM::_singleton = nullptr;`) is the pointer.
- Library classes' static members and constants of types outside the subset (`AP_GPS::_initialisation_blob`)
  are not registered (a use is rejected); a `const char *` data member is the empty string while null
  (AP_GPS's `initblob_state[i].blob`).

`examples/frontends.cpp` (golden `tests/golden/FrontEnds.lean`, configuration `examples/frontends.json`) has
each construct in a small form, as a World with a HAL boundary, a scheduler object, a namespaced simulator
singleton and back ends created at init; `tests/reject_phase3h.cpp` holds the limits (multi-bit bit-fields
outside a bit union, a reference-returning accessor whose body selects between members, range-for over
something other than an array).

### The stand-ins, shared by the reference and the translation

The stand-ins of `reference/hal/sensors.cpp` read the current input line through accessors that both builds
define (`reference/hal/est_input.h`): `est_input()` (the record of the step being run), `est_step_period_us()`,
`est_imu_rate_hz()` and the GPS latch (`est_gps_pending()`, `est_gps_take()`, lockstep.cpp's latch moved
into the HAL step), defined by the lock-step HAL (`reference/hal/lockstep.cpp`, from the line it parsed)
and by the scheduler stand-in (`reference/hal/est_scheduler.cpp`, from its current record, as code of the
World). The record type `EstRecord` is shared: two-dimensional IMU samples flattened (sample j of IMU i is
element `i * 8 + j`). The anonymous-namespace globals, the static locals and `struct timeval` of the GPS
stand-in are gone (`gps_time_week_ms`: UTC as `start_time_UTC` plus the clock, the same values); the
compass stand-in accumulates a copy of the line's field (the original rotated and corrected the global
line in place, which nothing read afterwards). `sensors.cpp` is split into one file per sensor
(`sensors.cpp` the SITL::SIM stand-in, `sensors_ins.cpp`, `sensors_baro.cpp`, `sensors_compass.cpp`,
`sensors_gps.cpp`; `reference/build.py` compiles them), so that a World takes the stand-ins of its front
ends only. The stand-ins report events (`est_event`: the barometer and compass back ends constructed, the
barometer back end's `update`): the reference's probe prints them per line (`ev=`), the scheduler stand-in
keeps them per consumed line (`_events`), so that a replay knows where the vehicle called the front ends.
`EstScheduler` also gained the GPS latch and the difftest's harness entries (`feed_line`, a line from
scalar arguments; `feed_baro_lines`, n lines with barometer samples, as the barometer's calibration
consumes them), so its golden `tests/golden/ardupilot/EstScheduler_lib.lean` changed (542 lines;
`ardupilot/translate_est_scheduler.sh` passes `--front-ends` for `EstRecord r {};`).

The reference (`python3 reference/build.py` in the work clone, 7 units recompiled) reproduces both recorded
flights byte for byte, and its estimation output keeps every earlier key:

```
build/reference/copter_ref --storage $D/storage_in.bin --est est2.txt < $D/inputs.txt > out.txt; cmp out.txt $D/outputs.txt
lockstep-flight: outputs identical (36,013 lines); est.txt: 36,013 lines, every earlier key identical
lockstep-flight-noisy: outputs identical; est.txt: every earlier key identical
```

`reference/hal/est_probe.cpp` adds, per line, `baro=<instances>[,<healthy>,<pressure>,<temperature>,<altitude>,
<ground pressure>,<last update ms>]` (instance 0), `mag=<count>[,<healthy>,<field x,y,z>,<last update us>,
<offsets x,y,z>,<dev id>]` and `ev=<events>`, and once, at the first line (after `AP_Param::load_all`,
before the front ends' init), `# params name=value ...`: every parameter of AP_Baro and Compass as loaded
(REFERENCE.md, "Estimation output (Phase 3)").

### The translation

`ardupilot/translate_sensors.sh` translates `ardupilot/unity_sensors.cpp` (AP_Baro.cpp, AP_Baro_Backend.cpp,
AP_Baro_atmosphere.cpp, AP_Compass.cpp, AP_Compass_Backend.cpp (its `FILTER_KOEF` renamed for the unity:
`check_unity.py --rename`), Compass_PerMotor.cpp, AP_ParamT.cpp, Location.cpp, AP_Declination, Device.cpp,
DerivativeFilter, LowPassFilter, AP_Math; `reference/hal/sensors.cpp`, `sensors_baro.cpp`,
`sensors_compass.cpp`, `est_scheduler.cpp`; the objects `SITL::SIM sitl`, `AP_Baro barometer`, `Compass
compass`) with the reference build's flags and real headers into `ardupilot/out/Sensors/Sensors_lib.lean`:
4,370 Lean lines, 263 definitions, golden `tests/golden/ardupilot/Sensors_lib.lean`. The front ends and
libraries are `--lib-dir`s, restricted to what `ardupilot/Sensors.use` reaches: the vehicle's calls
(`AP_Baro::init`, `calibrate`, `update`; `Compass::init`, `read`, `set_throttle`, `set_voltage`) and the
getters AP_DAL and AP_AHRS read (`num_instances`, `healthy`, `get_pressure`, `get_altitude`,
`get_ground_pressure`, `get_climb_rate`, `get_EAS2TAS`, ...; `get_count`, `get_field`, `last_update_usec`,
`get_offsets`, `use_for_yaw`, `consistent`, `get_declination`, ...). ArduPilot source lines covered by the
translated functions: AP_Baro 721 (AP_Baro.cpp 481, AP_Baro_atmosphere.cpp 152, the back end and headers
88), AP_Compass 929 (AP_Compass.cpp 560, AP_Compass_Backend.cpp 217, Compass_PerMotor 60, headers 92), the
libraries 913 (AP_Math 527, AP_Declination 153, Filter 118, AP_Param 57, AP_Common 40, AP_HAL 18): 2,563
ArduPilot lines (the source ranges of the translated functions, `/-- C++ ... file:a-b` in the output); the
stand-ins and the scheduler 268.

Boundary and left out: `AP::ahrs()` (`get_origin` for the field elevation, `get_location` for the
declination: inputs; `resetHeightDatum`, `update_orientation`: output events), `hal.util` (armed,
watchdog), `AP::battery()` (current, for `COMPASS_MOTCT 2`), `SRV_Channels::find_channel` and
`hal.rcout` (`Compass_PerMotor`, for `COMPASS_PMOT_EN 1`); dropped (`--drop`, no effect in the model): GCS
text, `DEV_PRINTF`, `AP_HAL::panic`, `AP_BoardConfig::config_error` (both end the run in the vehicle:
they are reached only when no barometer is found or it does not calibrate), `AP_InternalError::error`,
AP_Param's `save`/`notify`; semaphores (`--semaphores`).

### Differential test and replay

`python3 difftest.py ardupilot/Sensors` (`ardupilot/Sensors.json`, environment `ardupilot/sensors_env.cpp`:
the HAL with the scheduler stand-in and a Util, the AHRS, battery and GCS members the front ends call on
objects that are never constructed, AP_Param's `setup_object_defaults` copied verbatim from AP_Param.cpp
with nothing stored, `set_default_by_name` for the three names) drives the World: a setup that feeds 900
lines with a barometer sample every 3rd or 4th, then `barometer.init`, `compass.init`,
`barometer.calibrate` (it consumes about 640 lines; its second loop has no delay and ends only when a
sample arrives, so it runs in the setup only), then 4,000 random calls over the 71 member functions of the
three objects with drivers (lines fed with IMU, barometer, compass and GPS values, `update`, `read`,
`set_throttle`, `set_voltage`, delays, the getters) and the corner values of every argument and input,
printing every leaf of every object (641 per line; the scheduler's ring of 1024 records is left out, config
`skip_leaves`, its records reach the state through `_in` when consumed) and the back ends' leaves:

```
$ python3 difftest.py ardupilot/Sensors
ardupilot/Sensors World (calibrated): 0 of 5479 lines differ (1 tokens equal only as NaN vs NaN with different bits)
ardupilot/Sensors World (wild): 0 of 5479 lines differ (1 tokens equal only as NaN vs NaN with different bits)
$ python3 difftest.py frontends
frontends World: 0 of 20049 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

(`calibrated`: values in their ranges; `wild`: 15% outside them, NaN and infinities among them.) Sensitivity:
the compass voltage filter's `0.9f` changed to the next float makes 3,052 and 3,238 of 3,479 lines differ (a
2,000-call run).

The replay, `ardupilot/sensors_replay.py FLIGHT [--lines N]`, runs the World on a recorded flight
through `lean/SensorsReplay.lean` (executable `sensors_replay`; `lean/SensorsReplayParams.lean`, generated:
the parameters by the probe's names): it sets the parameters the reference loaded at boot (`# params`),
feeds the input lines, steps the scheduler where the vehicle consumed a line outside the front ends, calls
`barometer.init`, `compass.init` and `barometer.calibrate` at the steps whose events show them, then per
main loop `compass.set_throttle`/`set_voltage`/`read` where task 13 ran (with the reference's `comp=` and
`loc=`) and `barometer.update` where its event shows it (with `armed=` and `origin=`), and compares the
World's `baro=`, `mag=` and `ev=` with the reference's after every line (the lines consumed inside
`barometer.calibrate`'s delays are inside that call in the reference and are not compared):

```
$ ardupilot/sensors_replay.py sim/out/lockstep-flight --lines 8000
sensors replay lockstep-flight: 8000 lines (boot init through 7085 main loops): 7320 compared (baro=, mag=, ev=), 680 inside barometer.calibrate not compared; 0 differ
$ ardupilot/sensors_replay.py sim/out/lockstep-flight-noisy --lines 8000
sensors replay lockstep-flight-noisy: 8000 lines (boot init through 7085 main loops): 7320 compared (baro=, mag=, ev=), 680 inside barometer.calibrate not compared; 0 differ
```

The flights' recorded `est.txt` predate the front ends' keys: the script has the reference write the
estimation output again (`copter_ref --storage ... --est build/est/<flight>.txt`, 1 s). The 8,000 lines include the boot init (lines 1-915: the barometer's init at line 4, the compass's at 24,
the calibration from 64 to about 704) and the field elevation from the EKF origin at line 5,794 (14.485 s:
`resetHeightDatum` and the new ground pressure).

### Not done: AP_InertialSensor and AP_GPS (done in "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source")

With these features the survey of the four front ends' reachable paths (all of them in one unity, every
entry point of the vehicle and of AP_DAL; `--keep-going --survey`) goes from the 159 rejections of the
previous stage (every member function) to 35 rejected statements: AP_Baro and Compass 0,
AP_InertialSensor 17, AP_GPS 14 (a first pass: more may follow behind them), the IMU stand-in 4.

- AP_InertialSensor: uninitialized local arrays of `Vector3f` in `_init_gyro` (3; `--ekf-arrays` takes
  arrays of numbers only), `wait_for_sample`'s `goto check_sample` and its label (`--gotos` with the
  World), `gyro_available_mask` (a local the `goto` crosses), the fast-rate UART stream `send_uart_data`
  (8: a local struct, `sizeof`, `crc_xmodem`, writes to the UART; not reached without a UART, so it can be
  dropped or translated as unreached), a member read through the accel calibrator pointer (null in the
  World: only calls through such pointers are translated as unreached).
- The IMU stand-in: its `const uint16_t sample_rates[]` parameter (unused), `bus_id++` on a static member of
  a library class (a World field only when non-library code names it), and the timer functor that these
  leave untranslated.
- AP_GPS: ordering comparisons of `AP_GPS_FixType` values (5), `JitterCorrection` (AP_Math's, not yet a
  library of the unity), the inherited constructor `using AP_GPS_Backend::AP_GPS_Backend` of `AP_GPS_SITL`, a
  `switch` case falling through (`--gotos`), the UBLOX initialisation blob (`const char *` pointing into a
  static `char` array, `sizeof`, `size_t` arithmetic: F7's byte arrays for a member pointer, 4), a `const
  uint8_t *` parameter (RTCM injection), a local reference to `params[i].rate_ms` in a counted loop.

What the AHRS + estimator-replay stage needs: these two front ends (the INS is what EKF3 and AP_AHRS read
every loop: `get_delta_angle`, `get_delta_velocity`, `get_delta_time`, `get_gyro`, `get_accel`; the GPS its
`state`); AP_DAL's `start_frame` reads of the front ends as reads of these World objects (the AP_DAL translation of
"Phase 3: AP_DAL and NavEKF3": `AP::baro()`, `AP::compass()` there become the objects here, so the two translations
merge into one unity, and the DAL's boundary reads of the front ends become calls); the probe's front-end
tokens extended to the INS and the GPS (delta angle and velocity with their dt, the GPS fix); the replay
harness extended to `ins.init`/`update`/`wait_for_sample`/`periodic`, `gps.init`/`update` and then
`ahrs.init`/`update` (the scheduler's task list in `est.txt` gives where they run); and AP_AHRS's own reads
of the vehicle (armed, home, flying, trim, terrain stability: `est.txt`'s `armed=`, `home=`, `flying=`,
`cfg=`, `thgt=`) as the replay's inputs.

## Phase 3: AP_DAL and NavEKF3 (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), fourth stage: AP_DAL (as far as EKF3 needs it), the NavEKF3 front
end and NavEKF3_core with every fusion step the reference configuration reaches, each core's EKFGSF_yaw in its
heap slot, translated from the unmodified sources and difftested bit for bit through AP_DAL-level inputs (one
and two cores). Everything new is gated by options (most of it by `--reachable`), so every earlier translation
is byte-identical (examples, rejection tests, the ArduPilot goldens) and the difftests `ardupilot/EKFGSF`,
`ardupilot/EKF_Buffer`, `worldptr`, `ekfdata` stay at 0 differing lines.

### New options

| option | meaning |
|---|---|
| `--reachable` | the member functions of the translated classes are translated only as far as the `--use` entry points (and the constructors of the World objects) reach them; with it, the features below |
| `--indexed-inputs` | a const call on a boundary object with one non-constant integer argument (`ins.use_accel(i)`, `gps.location(i)`, also with reference parameters it writes: `ins.get_delta_velocity(i, dv, dt)`) reads an input array at that argument (`(inp.use_accel_at.getD i false)`); one array per member function, constant arguments, and reference parameter; an index beyond the array reads the zero value |
| `--sizeof C=N` | `sizeof(C)` is N, the size clang computes on the reference target, for a class whose object representation the model does not hold (`sizeof(NavEKF3_core)`, compared with the free memory in AP_NavEKF3.cpp:842; the translation script asks clang for it) |
| `--boundary-call @file` | (extended) a file of names; with `--reachable` a --boundary-call member function called on another object (`frontend->sources.getPosXYSource(i)`) is an input of the caller, as a call on a boundary object |

### `--ekf-types` with `--world-pointers` (the World statics and the heap singleton)

The clash: `AP_DAL *AP_DAL::_singleton = nullptr;` (a pointer with an initializer) next to `static bool
force_write;` (an `--ekf-types` World static). Now the heap prescan runs before the World's references are
resolved, a static singleton pointer of a class without a file-scope object is the World field `C'_singleton`
whatever its (null) initializer, and the World statics and static locals are not `WPtr` constructors. A
reference bound to the heap singleton (`dal{AP::dal()}` in NavEKF3's constructor; `AP_DAL &_dal` parameters and
members of the cores) is the path `w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!` (the pointer is assigned
only by `get_singleton()` while null, so the object a reference was bound to is the singleton for good); the
constructor that binds it evaluates the accessor (`AP_DAL::get_singleton` allocates the object on first use),
and `World.init` passes the World to a constructor that reaches it. An accessor whose body is `*C::get_singleton()`
(`AP::dal()`) is that call and the object it returns. `examples/ekfdal.cpp` (golden `tests/golden/EKFDal.lean`,
`python3 difftest.py ekfdal`: `ekfdal World: 0 of 20061 lines differ`) has these and the constructs below in
small: the singleton with `= nullptr` and static members, a reference member through an accessor, cores in raw
memory binding `Dal &`, a reference member bound to a member of the front end through `frontend->`, a static local
in a member function, `<=` loops over a member written only with constants, a const reference into the state, an
indexed getter `location(i)`, a log record brace-initialized, a struct member of a class with a constructor.
Sensitivity: one ulp in the front end's origin factor makes 129, `lim = 5` written as `4` 629 of 20061 lines differ.

### What `--reachable` adds for NavEKF3 (the survey's rejections, all reachable ones)

`ardupilot/translate_ekf3.sh --keep-going --survey` lists every rejected statement reachable from the entry
points (`ardupilot/ekf3.use`: InitialiseFilter, UpdateFilter and the 41 other functions AP_AHRS and AP_AHRS_NavEKF3 call
on the front end). Before this stage the full survey had 608 rejections (490 with `--world-pointers`); reachable
ones went 299 → 0:

- **The front end through `frontend->`**: a scalar parameter (`frontend->_gpsHorizVelNoise`, converted, copied
  by value to `sq(...)`, negated) is the front end's `w.EKF3'p` field; a member object of the front end with
  parameters (`frontend->sources`) is called with `w.EKF3'p.sources`; `public_origin(frontend->common_EKF_origin)`
  (a reference member of a heap class bound to a member through a pointer with one possible object) is the path
  `w.EKF3.common_EKF_origin`.
- **Heap objects that read and write the boundary**: `w.heap'C'inp` and `w.heap'C'o` (one record for all objects of
  the class; AP_DAL is a singleton), also for member objects of heap objects (`dal.baro().update_calibration()`:
  `w.heap'AP_DAL'o._baro`); getters returning a member of a heap object (`dal.ins()`) are paths into its slot.
  (The `heap'C'inp` field is the one the front ends' heap classes read with `--front-ends`, "Phase 3: sensor
  front ends and AP_Param": one implementation in the translator, `Unit.heap_inp`; only its doc comment
  differs between the two options.)
- **The front ends** (`--boundary AP_HAL::HAL,AP_HAL::Util,AP_AHRS,AP_Vehicle,AP_InertialSensor,AP_Baro,Compass,AP_GPS,...`
  with `--indexed-inputs`): AP_DAL's `start_frame` and its members' `start_frame`s are translated; each getter they
  call is an input of AP_DAL (AP_InertialSensor 17 fields, AP_Baro 5, AP_GPS 22, Compass 14, AP_AHRS/vehicle/HAL
  18; with the source selection of the front end and the cores, 275 tokens per difftest line). Also: a pointer accessor (`AP::vehicle()->get_time_flying_ms()`), `AP::wheelencoder()`
  tested for null (an input), a boundary enum converted to an integer (`(uint8_t)ahrs.get_vehicle_class()`), a
  call without arguments that writes the boundary (`update_calibration()`: a call count), `available_memory()`
  as `--boundary-query`. The HAL clock (`AP_HAL::micros64`, `micros`) is `--boundary-fn`.
- **AP_NavEKF_Source**: its source selection is read from `_source_set[i].posxy` etc., `AP_Enum` parameters in an
  array of structs, which needs AP_Param inside arrays of structs (`--param-ext`, "Phase 3: sensor front ends and
  AP_Param"; this translation does not use it yet).
  Until then the member functions that read them (`ardupilot/ekf3_sources.boundary`: getPosXYSource,
  getPosZSource, getVelXYSource, getVelZSource, useVelXYSource, useVelZSource, haveVelZSource, getYawSource, usingGPS,
  ext_nav_enabled, gps_yaw_enabled, wheel_encoder_enabled) are `--boundary-call` and their results inputs of the
  front end and the cores (indexed by core); the difftest gives the values of ArduPilot's default source
  parameters, and the C++ driver checks after every call that the real AP_NavEKF_Source returns exactly them.
  The var_info entries into the array of structs are left out of `setup_object_defaults`.
- **Loops**: `ARRAY_SIZE(a)` is a constant; a bound `<=` a data member whose every write in the program is a
  constant (`stateIndexLim`: 9, 12, 15, 21, 23, and the zero of the zero-filled object) has that range, and the
  counter of an enclosing loop has its range (`for (auto c=0; c<=r; c++)`): exact trip counts, no fuel needed;
  a bound member of a member (`_RBRH.num_instances`) is invariant if no write in the body reaches it.
- **References**: `const ftype &q0 = stateStruct.quat[0];` and other const and non-const local references
  whose indices are fixed while they are live (numerals, temporaries, immutable locals, loop counters, the heap
  singleton's index) are aliases of the path (each use reads it as it is then, as C++); a getter with one argument
  whose body is `return member[arg];` (`gps.location(i)`) is that element, its index evaluated once;
  `stateStruct.position.xy()` (a layout-prefix view of the struct view of the state array) is the struct view of
  the same first elements, so `xy() = ...`, `xy() += ...` and `xy().zero()` write them.
- **Static locals** (`static uint64_t lastUnhealthyTime_us = 0;` in NavEKF3::UpdateFilter, fill_nanf's `created`
  and 2048-entry NaN table): World fields `Function'name`, zero at the start (other initializers rejected).
- **Smaller**: enum ordering comparisons on the underlying values; a local named `s` renamed `s'`; brace-initialized
  log records (`struct log_REV3 pkt{ event : ... }`); `memset((void*)this, 0, sizeof(*this))`; `Location() {
  zero(); }` as a zero-constructing default constructor; a struct member of a class type is default-constructed
  with its constructor's value (`Quaternion quat` of `log_REPH`: `q1 = 1`; the ring buffers inside
  `NavEKF3_core::tas`: their `elsize`); `std::numeric_limits<double>::signaling_NaN()` (`__builtin_nans`,
  0x7ff4000000000000); the union's implicit copy assignment (`status = filterStatus`); the nullable out-pointer's
  default argument (`getYawData(yaw, var)`, `n_clips = nullptr`); a static data member read directly; two var_info
  tables in one class (NavEKF3's `var_info`, `var_info2`); AP_Declination's tables (`--lib-dir`).
- **Dropped or text** (`--drop`): `GCS::send_text` (GCS_SEND_TEXT; with `--reachable` a dropped call's arguments must
  be without effects: C math functions and const member functions only), `AP_DAL::snprintf` and the member it
  writes, `NavEKF3_core::prearm_fail_string` (the pre-arm text, read only by `pre_arm_check`, which is not an entry
  point of this stage), `MAV_SEVERITY` locals read only by a dropped call, `AP_BoardConfig::allocation_error` and
  `AP_HAL::panic` (unreachable: allocation never fails in the model, fill_nanf's counts are 576 and 28 < 2048).
- **Lean**: the file sets `maxRecDepth 200000` (CovariancePrediction's 520 `let`s and NavEKF3_core's constructor
  exceed 20000 in the code generator) and turns off the unused-variable linter (AP_DAL's `old` copies for
  `WRITE_REPLAY_BLOCK_IFCHANGED`, which is `(void)old` without logging). A run of consecutive `pure ()` lines in a
  `do` block makes Lean's elaboration exponential (15 of them did not finish in 10 minutes), so the left-out
  var_info entries emit no statement.

### The translation

| translation | script (output) | Lean lines | ArduPilot lines covered |
|---|---|---|---|
| AP_DAL, AP_NavEKF, AP_NavEKF3 (+ AP_Math, Location, AP_Declination as used) | `ardupilot/translate_ekf3.sh` (`ardupilot/out/EKF3/EKF3_lib.lean`, golden `tests/golden/ardupilot/EKF3_lib.lean`) | 14,614 (606 defs) | function extents: AP_NavEKF3 9,591, AP_NavEKF 958 (buffers, source selection, EKFGSF_yaw, core common), AP_DAL 882, AP_Math 722, AP_Declination 173, AP_Common 120 (12,457 in all, 565 functions) |

The unity file `ardupilot/unity_ekf3.cpp` includes the sources unmodified (checked as `ekf_common.sh` does) and
defines `NavEKF3 EKF3;` (in the vehicle the member `EKF3` of `AP_AHRS_NavEKF3` inside `AP_AHRS`). The World:
`EKF3` (state, parameters, inputs), the heap slots `heap'AP_DAL` (with `'inp`, `'o`), `heap'NavEKF3_core` (with
`'inp`), `heap'EKFGSF_yaw`, `heap'AP_DAL_Airspeed` (never allocated: no airspeed sensor), the singleton pointer,
the statics `KHP`, `Kfusion`, `force_write`, `logging_started`, and the static locals. It elaborates in 53 s
(`lake env lean`, one thread). AP_DAL's start_frame is translated against boundary front ends (rather than taking
its log records as inputs): the C++ difftest then runs ArduPilot's own start_frame on stub front ends, so the
records, `_micros`/`_millis`, the filtered gyro and accel and the frame bookkeeping are compared too.

### The difftest (`python3 difftest.py ardupilot/EKF3`)

`ardupilot/EKF3.json` names its own harness, `ardupilot/ekf3_difftest.py`. C++: the ArduPilot sources of the unity
compiled from the reference build's copy with the unit's flags and `-fno-access-control`, `NavEKF3 EKF3;` defined by
the driver, the boundary in `ardupilot/ekf3_env.cpp` (the front ends are zero-filled storage of their real classes:
a getter inline in its header answers through the data member it reads, set from the line; the others are
defined there; `AP_HAL::Util::malloc_type` is recorded zeroed memory; AP_Param's defaults code is
ac_pid_env.cpp's copy of AP_Param.cpp). Lean: `lean/EKF3Main.lean` (generated) sets `w.heap'AP_DAL'inp`,
`w.EKF3'inp`, `w.heap'NavEKF3_core'inp` from the line. Each line is a call `U` (UpdateFilter) or `A` (as
AP_AHRS::update_EKF3: InitialiseFilter until it returns true, then UpdateFilter); after it both print the call's
result, the results of 36 getters AP_AHRS reads (healthy, getPrimaryCoreIndex, getQuaternion, getVelNED, getPosNE,
getPosD, getGyroBias(-1), getAccelBias(-1), getVariances, getFilterStatus, getOriginLLH, getLLH, getHAGL,
getInnovations, ...), the boundary outputs and every leaf of every object: the front end (143), AP_DAL (379), each
core (1,237: the 24 states, P, the output predictor, the buffers' indices, ...), each EKFGSF_yaw (215), the statics
(KHP, Kfusion: 604). The scenario (`ardupilot/ekf3_scenario.py`): 400 Hz steps, the vehicle level at CMAC with yaw
30° for 40 s, armed at 39.5 s, then accelerating north-east and climbing, cruising, decelerating; IMU delta
angles and velocities every step (seeded noise), baro at 50 Hz, compass at 100 Hz, GPS at 5 Hz from 2 s; EKF3
started at 1 s. InitialiseFilter succeeds between 2 and 3 s, the filter aligns tilt and yaw (mag), passes the GPS checks and
sets its origin by 12.5 s, learns the gyro bias and fuses GPS from between 30 and 35 s on (PV_AidingMode absolute).
Two cores: 2 s after take-off IMU0's accelerometer gets a 3 m/s² and its gyro a 0.05 rad/s z bias; core 0's error score rises and the front end
switches the primary lane to core 1 at 44.0 s.

```
$ python3 difftest.py ardupilot/EKF3
ardupilot/EKF3 NavEKF3 (one_core): 0 of 24001 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF3 NavEKF3 (two_cores): 0 of 24001 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

(about 7 minutes with the translation; 2 minutes without, `CPP2LEAN_NO_TRANSLATE=1`.) Sensitivity: one ulp in
`0.5` of CovariancePrediction's `PS7` makes 22,535 (one core) and 22,615 (two cores) of 24,001 lines differ;
the lane-selection delay `1E7` written as `5E7` makes 16,000 and 18,800 differ.

### Speed (`python3 ardupilot/ekf3_difftest.py --bench`)

Time per call measured inside each driver (Lean: `IO.monoNanosNow` around the forced call, lake's default release
build; C++: `steady_clock`, `-O2`), same lines as the difftest, Apple M-series, one thread:

| run | calls | Lean mean | Lean median | Lean p99 | C++ mean | ratio |
|---|---|---|---|---|---|---|
| one core, UpdateFilter, all | 23,199 | 220 µs | 23 µs | 2.9 ms | 0.69 µs | 318 |
| one core, prediction steps (every 4th or 5th: the 12 ms EKF rate) | 4,639 | 1.00 ms | 0.66 ms | 3.5 ms | 2.2 µs | 465 |
| one core, the steps in between | 18,560 | 24 µs | 22 µs | 48 µs | 0.33 µs | 75 |
| one core, prediction steps while fusing GPS (> 35 s) | 2,000 | 0.69 ms | 0.53 ms | 2.6 ms | 2.2 µs | 313 |
| two cores, UpdateFilter, all | 23,199 | 451 µs | 51 µs | 5.9 ms | 1.35 µs | 334 |
| two cores, prediction steps | 4,639 | 2.04 ms | 1.35 ms | 7.1 ms | 4.3 µs | 477 |
| two cores, the steps in between | 18,560 | 53 µs | 49 µs | 98 µs | 0.62 µs | 86 |

One core averages 0.22 ms per 400 Hz step against the 2.5 ms budget (C++: 0.69 µs, REFERENCE.md's AHRS + EKF3
figure is the same order), but single prediction steps reach 3.5 ms. What dominates (macOS `sample` of the
one-core run, the timed calls only): array copying and allocation 86% (`Array.extract`, `Array.append`,
`Array.push`, frees), FloatLib arithmetic 9%. The copies come from `NavEKF_core_common::zero_range(ftype *v, n1,
n2)` (`memset(&v[n1], ...)`), which `zeroStatesVarCov` calls once per row of P (`zero_range(&Pmut[row][0], ...)`):
`--pointer-params` passes a pointer into an array as the slice from it to the end and splices the result back,
two copies of the 576-element P per call; and from a heap object's state passed while still in its slot
(`w.heap'NavEKF3_core[i]!`), so its arrays are shared and copied on their first write in the call. Neither is a
FloatLib cost: passing pointers into arrays as the array and an offset, and taking a heap object out of its
slot for the call (F15's swap-out for heap slots), are the next speed steps. (Done: "Phase 3: AP_AHRS, and speed" below.)

### What is boundary or left out in this stage, and why

- The sensor front ends, AP_AHRS, the vehicle, the HAL: boundary (inputs per call, outputs `set_takeoff_expected`
  and the baro calibration count); their translation is "Phase 3: sensor front ends and AP_Param" (AP_Baro and Compass; AP_InertialSensor and AP_GPS still to do).
- AP_NavEKF_Source's source-set getters: boundary-call (above). AP_NavEKF_Source itself is translated and difftested
  with `--param-ext` in "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source", which says what switching this
  translation to it involves.
- Text: GCS_SEND_TEXT dropped (no boundary event: QGroundControl's EKF messages come with the GCS stage), the
  pre-arm string and `AP_DAL::snprintf` dropped, `NavEKF3::pre_arm_check` not an entry point (needs `--c-strings`
  and the text runtime: D10).
- Compiled out in the reference configuration (not included): logging (HAL_LOGGING_ENABLED 0: the replay records
  are written nowhere, `WriteLogMessage` not reached), optical flow, range beacons, visual odometry, airspeed
  (`AP_DAL_Airspeed` is constructed only if `AP::airspeed()` has sensors: AP_AIRSPEED_ENABLED 0).
- Not driven by the difftest: the mutating entry points (`checkLaneSwitch`, `requestYawReset`, `resetGyroBias`,
  `resetHeightDatum`, `setOriginLLH`) are translated but not called by the harness.

## Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), fifth stage: the sensor World of "Phase 3: sensor front ends and
AP_Param" completed with AP_InertialSensor (with its back-end base, its parameters and the IMU stand-in), AP_GPS (with
its back-end base, its parameter groups, JitterCorrection, AP_RTC and the GPS stand-in) and a stand-in of the GPS's
serial port; the World replayed on the whole of both recorded flights against an extended probe of the reference;
AP_NavEKF_Source translated with `--param-ext` and difftested. Everything new in the translator is behind one option,
`--ins-gps` (with `--front-ends`), so every earlier translation is byte-identical (the examples, the rejection tests,
the ArduPilot goldens, musl) except the two whose sources changed: `Sensors_lib` (the new front ends) and
`EstScheduler_lib` (a new harness entry, `feed_imu_lines`).

### New option and constructs (`--ins-gps`)

- **Reference members bound to elements of a World object's arrays.** `AP_GPS_Backend::state` and `params` are bound by
  the constructor to `_state` and `_params`, for which `AP_GPS::_detect_instance` passes `state[instance]` and
  `params[instance]` (AP_GPS.cpp:730). A pre-pass (`heap_elem_refs`) finds every construction site of the heap class,
  checks that each passes an element of the same array member of the World object whose member function constructs it,
  and makes the reference an index: the heap object's state gets a field `state'i : Nat`, the constructor parameter is
  the index (`_state'i`), the site passes the element's index, and a use of the member is the element of the World
  object's array at that index (`w.gps.state[s.state'i]!`; the self-reach cycle stores and reloads the front end as for
  any call that reaches it).
- **Inheriting constructors** (`using AP_GPS_Backend::AP_GPS_Backend;`, AP_GPS_SITL.h:29): the implicit constructor
  with its `CXXInheritedCtorInitExpr` is a constructor of the class; its body is the base's constructor called with its
  parameters, the class's own members keep their defaults (ArduPilot's `new` zero-fills). A base constructor run for a
  heap object may reach the World (the GPS back end's writes `state.have_speed_accuracy = false`).
- **A pointer the boundary returns to a class the World has one object of** (`AP::serialmanager().find_serial(GPS, i)`,
  an `AP_HAL::UARTDriver *`): that object or null, by an input flag per value of the call's one non-constant argument
  (`find_serial_found_SerialProtocol_GPS_at1 : Array Bool`). The World's object is `est_uart`, below.
- **A call every overrider of which returns `false`** (`drivers[instance]->get_RTCMV3(rtcm_data, rtcm_len)`,
  AP_GPS.cpp:974: only the base's `{ return false; }` is in the closed world): the guarded branch cannot run and is
  not translated (`static_false`); a local used only there (`const uint8_t *rtcm_data;`) is left out with it.
- **A call through a subscript of a pointer to a class without objects** (`_imu._accel_calibrator[instance].get_status()`,
  AP_InertialSensor_Backend.cpp:548, behind `_accel_calibrator != nullptr`): not reached, as `p->m()` of such a pointer.
- **Default construction of array members and locals**: elements whose default constructor zeroes them on zero-filled
  storage (`LowPassFilter2pVector3f _accel_filter[3]`: `memset(&_params, 0, ...)` and `_delay_element_1 = T()`), the
  field's default; elements whose constructor gives another value (`AP_GPS::Params params[3]`, whose constructor runs
  `setup_object_defaults`), that value `Array.replicate n`; an uninitialized local array of a class whose default
  constructor gives zero (`Vector3f last_average[3]` in `_init_gyro`), zeros. Arrays of non-library classes are accepted.
- **Smaller**: a local reference to an element indexed by the counter of an enclosing `for` loop of any kind that its
  body never assigns (`auto &rate_ms = params[i].rate_ms;`, AP_GPS.cpp:341); enum ordering comparisons
  (`status >= AP_GPS_FixType::FIX_2D`) and the renaming of a parameter named `s` (`velocity_to_speed_course(GPS_State
  &s)`), as `--reachable` does; `if (_singleton)` as `_singleton != nullptr`; a pointer parameter nothing reads, or only
  passes on to another such parameter (the IMU stand-in's `const uint16_t sample_rates[]`), is not passed; the
  out-of-line zero definition of a library class's static member (`uint8_t AP_InertialSensor_SITL::bus_id = 0;`) is a
  World field read and written as such; `AP_DAL_Compass &AP_DAL::compass()` of a boundary object as a boundary object;
  the file sets `linter.unusedVariables false` (`(void)fft_enabled;` and the slot index of a dispatch whose overrider
  reads no state).

`examples/insgps.cpp` (golden `tests/golden/InsGps.lean`, configuration `examples/insgps.json`) has each construct in a
small form (`python3 difftest.py insgps`: `insgps World: 0 of 20074 lines differ`; the back end's `0.5f` changed to the next
float: 20,052 differ); `tests/reject_phase3i.cpp` the limits (an element of an array that is not a World object's member, a pointer
from the boundary with two non-constant arguments, an uninitialized local array of a class whose constructor is not zero).

### What is translated, boundary, dropped

`ardupilot/unity_sensors.cpp` now also includes AP_InertialSensor.cpp, AP_InertialSensor_Backend.cpp,
AP_InertialSensor_Params.cpp, AP_GPS.cpp, GPS_Backend.cpp, AP_GPS_Params.cpp, AP_RTC.cpp, JitterCorrection.cpp,
LowPassFilter2p.cpp, AP_HAL/UARTDriver.cpp and the stand-ins `sensors_ins.cpp`, `sensors_gps.cpp`, `est_uart.cpp`, and
defines `AP_InertialSensor ins; AP_GPS gps; AP_RTC rtc; EstUART est_uart;` (the first three are members of `copter` in
the vehicle). `ardupilot/Sensors.use` adds the vehicle's calls (`ins.init(loop rate)` with the gyro calibration,
`wait_for_sample`, `update`, `periodic`; `gps.init`, `gps.update`) and the getters AP_DAL (`AP_DAL_InertialSensor` and
`AP_DAL_GPS::start_frame`) and AP_AHRS read (delta angles and velocities with their dt, accel, gyro, health, use flags,
loop rate and delta time, gyro bias limits, IMU positions, vibration and accel peaks, first usable IMUs; status,
location, velocity, accuracies, lag, hdop/vdop, satellites, time, primary, number of sensors, yaw). The GPS's
`AP::rtc().set_utc_usec` is translated (AP_RTC is a World object; `hal.util->set_hw_rtc` an output event).

- **The GPS port stand-in** (`reference/hal/est_uart.h`, `.cpp`, not part of copter_ref): AP_GPS detects its SITL back
  end only on a port (AP_GPS.cpp:672 returns before the `GPS_TYPE_SITL` case without one); in the reference the port is
  the lock-step HAL's SERIAL3, an unconnected port of lockstep.cpp's UART class. `EstUART` is that class's logic for an
  unconnected port (no bytes in or out; `_begin` keeps the baud rate) as an `AP_HAL::UARTDriver`, translated with
  UARTDriver.cpp; its `read()` returns -1 directly (UARTDriver's chain through `read_locked` gives the same; the read
  monitor `_monitor_read_buffer`, fed only by successful reads, is dropped). Only the detection's baud probe reads it.
- **Boundary**: `AP_SerialManager` (find_serial: the port or null, an input), the HAL (`was_watchdog_reset`,
  `get_soft_armed`, `set_hw_rtc`), `AP_Notify::flags` (output events: `initialising`, `gyro_calibrated`, `gps_status`,
  `gps_num_sats`); AP_Param's `load()` of the gyro and accel ids (an input: found in storage) and `configured()` of
  GPS1_TYPE.
- **Dropped** (`--drop`): `AP_InertialSensor::send_uart_data` (the fast-rate IMU stream, called only with an IMU-out
  UART, never set), `fast_rate_buffer` (a member of a class not compiled in), `OpticalFlow::push_gyro` (the HAL's
  Empty::OpticalFlow, whose `push_gyro` does nothing, in both HALs), `AP_Param::convert_parameter_width` and
  `AP_GPS::convert_parameters` (conversions of parameters stored in old formats: nothing to convert in the reference's
  storage; the difftest's environment converts nothing either), `AP_GPS::send_blob_start`/`send_blob_update` (the
  UBLOX initialisation bytes: GPS types SITL and NONE have none, `remaining` stays 0 as it would; other types need a
  UART with a receiver, outside the World), `AP_GPS_Backend::broadcast_gps_type` (GCS text), the RTCM buffer pointer
  `AP_GPS::rtcm_buffer` (only MAVLink RTCM injection reaches it), the UART read monitor.
- **Not reached, translated as such**: the accel calibrators (`HAL_INS_ACCELCAL_ENABLED 0`: the pointers stay null),
  the RTCM relay between moving-baseline receivers (above), byte detection of serial GPS types (no bytes arrive).
- `AP_InertialSensor::periodic` has no effect in this configuration (the batch sampler is compiled out): not emitted.

`ardupilot/out/Sensors/Sensors_lib.lean`: 8,174 Lean lines (4,370 before), 482 definitions, golden
`tests/golden/ardupilot/Sensors_lib.lean` (regenerated); it elaborates without warnings in about 40 s (`lake env lean`,
one thread). ArduPilot lines covered by the translated functions (the ranges in the `/-- C++ ...` doc comments,
emitted and "not emitted" functions): AP_InertialSensor 1,828, AP_GPS 1,076, AP_Compass 1,051, AP_Baro 721, AP_Math
623, Filter 208, AP_Declination 153, AP_Common 80, AP_RTC 78, AP_Param 62, AP_HAL 41, AP_AccelCal 7: 5,928 (2,685
before by the same count), the stand-ins and HAL stand-ins 436.

### The reference: probe and identity

`reference/hal/est_probe.cpp` prints, per line, `ins=<gyro count>,<accel count>,<first usable gyro>,<first usable
accel>,<calibrating>,<delta time>,<last update us>,<have sample>,<next sample us>,<last sample us>`, per IMU
`imu<i>=<accel x,y,z>,<gyro x,y,z>,<delta angle x,y,z>,<its dt>,<valid>,<delta velocity x,y,z>,<its dt>,<valid>,<accel
healthy>,<gyro healthy>,<gyro cal ok>,<gyro offsets x,y,z>,<accel offsets x,y,z>`, `gps=<sensors>,<primary>` and per
receiver `gps<i>=<status>,<lat>,<lng>,<alt>,<frame>,<velocity x,y,z>,<ground speed>,<ground course>,<hdop>,<vdop>,<sats>,
<hacc ok>,<hacc>,<vacc ok>,<vacc>,<sacc ok>,<sacc>,<week>,<week ms>,<last message ms>,<last fix ms>,<vertical velocity>,
<lag ok>,<lag>`, and `evx=` (the IMU stand-in's construction in `AP_InertialSensor::init`, event 8, shifted: `ev=` keeps
its earlier values); `# params` adds every parameter of AP_InertialSensor and AP_GPS. The reference rebuilt in the work
clone (`python3 reference/build.py`) reproduces both flights' outputs and keeps every earlier key:

```
cmp OUT sim/out/lockstep-flight/outputs.txt                  (silent; and the noisy flight's)
reference/tools/est_compare.py BASE NEW-restricted-to-BASE's-keys
lockstep-flight: steps compared: 36013; values compared: 5685582, equal: 5685582, different: 0; all equal
lockstep-flight-noisy: steps compared: 36013; values compared: 5685582, equal: 5685582, different: 0; all equal
```

(BASE: the main workspace's copter_ref before this stage, `--est`.)

### The replay of the whole flights

`ardupilot/sensors_replay.py` (and `lean/SensorsReplay.lean`) now also drive the boot's `gps.init` (at the compass's
init event: Copter::init_ardupilot calls it right before `compass.init`) and `ins.init(400)` (at the step whose `evx=`
shows the IMU back end constructed; its gyro calibration consumes the lines its delays consume, which are inside that
call in the reference and not compared), and in every step whose `tasks=` is not `-` (the main loop, from the last boot
line on) the scheduler's `wait_for_sample` and then, in execution order, `AP_InertialSensor::update` (task 0) and
`AP_GPS::update` (task 12); `AP_InertialSensor::periodic` (task 30) has no effect. Inputs: the parameters of `# params`;
GPS1_TYPE stored (configured) and the GPS protocol found on SERIAL3 and SERIAL4; the ids stored iff non-zero at boot;
the armed flag of the previous step for the IMU back end and AP_RTC. Every front-end key is compared:

```
$ ardupilot/sensors_replay.py sim/out/lockstep-flight
sensors replay lockstep-flight: 36013 lines (boot init through 35098 main loops): 35122 compared (baro=, mag=, ins=, imu<i>=, gps=, gps<i>=, ev=, evx=: 3792376 values), 891 inside barometer.calibrate and ins.init not compared; 0 differ
$ ardupilot/sensors_replay.py sim/out/lockstep-flight-noisy
sensors replay lockstep-flight-noisy: 36013 lines (boot init through 35098 main loops): 35122 compared (baro=, mag=, ins=, imu<i>=, gps=, gps<i>=, ev=, evx=: 3792376 values), 891 inside barometer.calibrate and ins.init not compared; 0 differ
```

(about 1 s each for the Lean replay of 36,013 lines; the script writes `build/est/<flight>.txt` with the reference if
the flight's `est.txt` predates the `# params` line.)

### The difftest of the extended World (`python3 difftest.py ardupilot/Sensors`)

`ardupilot/Sensors.json` adds the new sources and stand-ins, the inputs (the GPS ports, the ids found in storage; the
watchdog and armed flags aliased to the barometer's: one C++ value), and three runs whose setups feed barometer lines,
init the barometer, compass and GPS (GPS1_TYPE 100, `state_params`), calibrate the barometer, feed 300 lines with three
samples of each IMU (`EstScheduler::feed_imu_lines`, new) and run `ins.init(400)`; `two_imus` sets SIM_IMU_COUNT 2 and
two GPS receivers of type 100. Random calls then drive every public member function of the seven World objects
(random lines always carry an IMU sample; `ins.update` and `wait_for_sample` are called only while at least 16 records
are fed, config `guards`: they wait for samples until they come). New difftest settings: `state_params` (parameters
that are state, set after construction on both sides), input arrays (`indexed_input_lengths`), `unlogged_outputs`
(AP_Notify's flags: the C++ side cannot observe a write to a static struct), `guards`; a null `const char *` leaf prints
as the empty string (the model's value).

```
$ python3 difftest.py ardupilot/Sensors
ardupilot/Sensors World (calibrated): 0 of 7854 lines differ (4843 tokens equal only as NaN vs NaN with different bits)
ardupilot/Sensors World (wild): 0 of 7854 lines differ (538 tokens equal only as NaN vs NaN with different bits)
ardupilot/Sensors World (two_imus): 0 of 7854 lines differ (1428 tokens equal only as NaN vs NaN with different bits)
```

(7,853 calls per run, 4,000 random and 3,853 with corner values, over 177 member functions of the seven World
objects; 1,296 leaves per line plus the heap objects' and the output log; about 380 calls of `ins.update`,
`wait_for_sample` and `gps.update` per run; the GPS is detected on the port stand-in and reaches FIX_3D; the setups leave
about 80 fed IMU lines so that the random lines, among them GPS lines, are consumed.) Sensitivity (`CPP2LEAN_MUTATE`, a
1,500-call run): the `0.98f` of AP_GPS's frame-timing average and of the IMU back end's sample-rate filter each changed to
the next float make 4,737, 4,865 and 4,794 of 5,354 lines differ.

### AP_NavEKF_Source (`ardupilot/translate_navekf_source.sh`)

`ardupilot/unity_navekf_source.cpp` (AP_NavEKF_Source.cpp and AP_ParamT.cpp unmodified, `AP_NavEKF_Source sources;`
as NavEKF3 holds it) translates with `--param-ext` into `ardupilot/out/NavEKF_Source/NavEKF_Source_lib.lean` (474 Lean
lines, 35 definitions; AP_NavEKF 298 and AP_Param 6 lines of translated functions; golden
`tests/golden/ardupilot/NavEKF_Source_lib.lean`): the source sets `_source_set[3]` are `AP_Enum` parameters in an
array of structs, set from `var_info` by the constructor. Entry points (`ardupilot/navekf_source.use`): every public
member function NavEKF3, its cores and AP_AHRS call but `pre_arm_check` (its failure text) and `init` (declared, never
defined). Boundary: AP_DAL (`AP::dal().compass().get_num_enabled()`, an input; the barometer's count is compiled out),
AP_Param's `configured()`; `save()` has no effect. `align_inactive_sources` is empty without visual odometry and
`mark_configured` only saves: not emitted.

```
$ python3 difftest.py ardupilot/NavEKF_Source
ardupilot/NavEKF_Source World (defaults): 0 of 3082 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/NavEKF_Source World (sets): 0 of 3082 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/NavEKF_Source World (options): 0 of 3082 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

(runs: ArduPilot's default sets; the second and third sets on external navigation, optical flow, rangefinder, GSF
yaw, beacon, wheel encoder and GPS-with-compass-fallback yaw with one set per core; GPS yaw and FUSE_ALL_VELOCITIES.
Parameter values are enumerator values: an `AP_Enum` holding another value is the first enumerator in the model.)

**Switching EKF3 to it (done in the combined World, "Phase 3: the estimator World and the EKF3 replay"; `EKF3_lib` keeps
the boundary).** `ardupilot/translate_ekf3.sh` would drop `--boundary-call
@ekf3_sources.boundary` and translate NavEKF3's member `sources` as an object with its parameters. That needs
`--param-ext` (with `--front-ends`), which turns every `AP_Param` member of NavEKF3, NavEKF3_core and AP_DAL into state
of its class (`frontend->_gpsHorizVelNoise` from `w.EKF3'p` to `w.EKF3._gpsHorizVelNoise._value`, NavEKF3's
`setup_object_defaults` from `var_info` and `var_info2` into state), so the whole EKF3 translation, its golden,
`lean/EKF3Main.lean` (generated by `ardupilot/ekf3_difftest.py` from the `'p` parameters) and the C++ side of its
difftest change with it; and `--front-ends` changes other constructs of that translation (pointers to library classes,
reference accessors). The steps: (1) translate_ekf3.sh with `--front-ends --ins-gps --param-ext`, the `.boundary` file
removed; (2) ekf3_difftest.py: set parameters as state leaves (as `state_params` does) and drop the per-core source
inputs, the C++ driver's check that the real AP_NavEKF_Source returns the inputs becomes the comparison of the
`sources` leaves; (3) `difftest.py ardupilot/EKF3` at 0. This is part of the combined estimator stage (below), where
the front ends' translation replaces the boundary anyway.

### What the combined estimator replay needs (done, but AP_AHRS: "Phase 3: the estimator World and the EKF3 replay")

One unity with the sensor World, AP_DAL, NavEKF3 (with AP_NavEKF_Source as above) and AP_AHRS (with AP_AHRS_NavEKF3
holding `EKF3`), in which AP_DAL's `start_frame` reads `AP::ins()`, `AP::gps()`, `AP::baro()`, `AP::compass()` as the
World objects instead of its boundary inputs (the getters are translated here, with the names `--indexed-inputs` reads);
the replay commands of this stage plus `ahrs.init`, `ahrs.update` (fast task 3, after task 0's `ins.update` in the same
step) and the vehicle's inputs `est.txt` records (armed, home, flying, trim, terrain stability, vehicle class); the
probe's `q=`, `c<k>.x=`, ... keys compared with the World's AHRS and EKF3. Translator side: options of the sensor World
and the EKF3 translation together (`--param-ext` for both, `--reachable` for EKF3 with `--use` entry points for both).

## Phase 3: AP_AHRS, and speed (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), sixth stage: (B) the speed of the EKF3 translation, whose
copies of arrays the AP_DAL and NavEKF3 stage measured (86% of the time), and (A) AP_AHRS with its EKF3 backend and the
DCM fallback on top of it. Part B is done: the array copies are gone, one core now takes 0.13 ms per 400 Hz
step on average and 0.57 ms per prediction step (p99 2.0 ms), and what remains is FloatLib's `Binary64`
arithmetic. Part A is not done: the unity file, the entry points, the translation script, static data
members of class type as World objects, and the survey of what the AHRS translation still rejects are in
place; the translator's model of pointers to member objects of a World object (AP_AHRS's backend and
estimates pointers, 62 of the 111 reachable rejections) is the next step, and the difftest harness for it
is not written (below; both done in "Phase 3: AP_AHRS translated"). Everything new is gated by options, so every
earlier translation other than `EKF3_lib.lean` is byte-identical (the examples, the rejection tests, the libm and
ArduPilot goldens).

### New options

| option | meaning |
|---|---|
| `--array-offsets` | (with `--pointer-params`) a pointer into an array is passed as the whole array and an offset (`p'o : Nat`, a parameter after `p`), written back whole after the call; `memset`/`memcpy` through a pointer with an offset write the elements one by one in place |
| `--swap-out` | (with `--world-pointers`) a call that writes the state of a World object (`w.EKF3`) or of a heap object (`w.heap'C[i]!`) takes the state out of the World for the call (its place holds `default`) and stores the call's result back |
| `--member-objects` | (with `--world`) a static data member of a translated class (`static NavEKF3 EKF3;` of AP_AHRS_NavEKF3, defined at AP_AHRS_NavEKF3.cpp:13) is a World object named after the member, constructed in definition order; `EKF3.f()` inside the class and `ekf3.EKF3.f()` through an object are that object |

### Pointers into arrays as the array and an offset (`--array-offsets`)

Before, `--pointer-params` passed `&a[k]` (or `a + k`) as the slice from k to the end (`a.extract k a.size`) and,
if the callee writes through it, spliced the result back (`a.extract 0 k ++ r`): two copies of the array per
call. EKF3's `zeroStatesVarCov` zeroes rows of the covariance matrix with `zero_range(&Pmut[row][0], 0, 23)`
(AP_NavEKF_core_common.h:52), so each call copied the 576-element `Pmut` twice, and `zero_range`'s own
`memset(&v[n1], 0, ...)` built a third array (`extract ++ replicate ++ extract`). With the option every array
pointer parameter `T *p` (array mode) is `(p : Array T) (p'o : Nat)`: `p[i]` is `p[p'o + i]!`, `*p` is
`p[p'o]!`, a pointer that moves starts as `let mut p'o := p'o`; the caller passes its array and the offset
(`NavEKF_core_common.zero_range s.Pmut (UInt8.toNat row * 24) 0 23`) and stores the returned array whole
(`s := { s with Pmut := ... }`), so the array has one reference when the callee writes it and Lean updates it
in place. `memset(p, 0, k * sizeof(T))` and `memcpy(p, q, k * sizeof(T))` with an offset are `for j in
[0:k] do p := p.set! (p'o + j) ...`. The aliasing check (two pointer arguments into one array, one written:
rejected) is unchanged. A parameter used only as `*p` (a scalar) and the C mode are not affected.

### Calls on World and heap objects with the state taken out (`--swap-out`)

A call of a member function of a heap object passed the object's state while it was still in its slot
(`NavEKF3_core.UpdateFilter w.heap'NavEKF3_core[i]! w ...`): the state had two references (the slot and the
argument), so the callee's first write to it copied the structure and each array (P, the buffers, the
output predictor) was copied on its first write in the call. With the option such a call (one that returns
the object's state) is preceded by

```
let t'10 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
```

and the callee gets `t'10`, the only reference; the result is stored back as before. The same for a World
object (`let t := w.monitor; w := { w with monitor := default }`). It is sound because nothing reads that
place while the call runs: a callee that reaches the object through the World does so only after the
self-reach cycle (README "Phase 3: World pointers") has stored the object's state there, and the caller's
own arguments are evaluated before the swap; a call one of whose other arguments names the place is left
as it was (checked on the emitted text). In NavEKF3 the swap applies at 18 call sites: the cores (7:
`UpdateFilter`, `setup_core`, `InitialiseFilterBootstrap` and the mutating entry points' calls), AP_DAL (8:
`start_frame`, `ekf_low_time_remaining`, ...) and the EKFGSF_yaw slots (3).

`examples/fastcalls.cpp` (golden `tests/golden/FastCalls.lean`, `python3 difftest.py fastcalls`:
`fastcalls World: 0 of 20091 lines differ`; sensitivity: the offset left out of `zero_range`'s index makes
19,368 lines differ, the static member object's swap-out given the other `Monitor` 20,090) has both in small: `zero_range` on rows of a 6×6 matrix through
`memset`, a pointer that moves, `memcpy` between pointers into two arrays, a const pointer read by
subscript, cores in raw memory updated by index from a file-scope front end, a file-scope object whose
state another one writes through a reference member, and a static data member of a translated class
(`Monitor Front::tally`, a World object under `--member-objects`; the C++ driver names it `Front::tally`).
`tests/reject_phase3j.cpp` holds the limits (5 rejections: the aliasing check under `--array-offsets`, and
the AP_AHRS patterns not modeled yet: a pointer to a member object, a call through it, a range-based `for`
over a member array of structs of references and its initializer).

### Speed (`python3 ardupilot/ekf3_difftest.py --bench`)

Same measurement as in "Phase 3: AP_DAL and NavEKF3" (time per call inside each driver, the difftest's
lines, Apple M-series, one thread); "before" is the AP_DAL and NavEKF3 stage's translation measured in the same
session (it reproduces that stage's table within 3%):

| run | calls | Lean mean before → after | median | p99 | C++ mean | ratio after |
|---|---|---|---|---|---|---|
| one core, UpdateFilter, all | 23,199 | 218 µs → 132 µs | 22 → 21 µs | 2.88 → 1.61 ms | 0.69 µs | 191 |
| one core, prediction steps | 4,639 | 0.99 ms → 0.57 ms | 0.65 → 0.32 ms | 3.46 → 2.04 ms | 2.2 µs | 263 |
| one core, the steps in between | 18,560 | 24 µs → 23 µs | 21 → 20 µs | 48 → 49 µs | 0.32 µs | 70 |
| one core, prediction steps while fusing GPS (> 35 s) | 2,000 | 0.69 ms → 0.45 ms | 0.54 → 0.28 ms | 2.60 → 2.07 ms | 2.2 µs | 203 |
| two cores, UpdateFilter, all | 23,199 | 444 µs → 272 µs | 50 → 47 µs | 5.84 → 3.27 ms | 1.35 µs | 201 |
| two cores, prediction steps | 4,639 | 2.01 ms → 1.16 ms | 1.34 → 0.68 ms | 6.99 → 4.07 ms | 4.3 µs | 271 |
| two cores, the steps in between | 18,560 | 52 µs → 49 µs | 48 → 45 µs | 98 → 96 µs | 0.62 µs | 80 |

One core is now well inside the 2.5 ms budget of a 400 Hz step on average (0.13 ms) and in its worst steps
(prediction steps p99 2.0 ms); two cores average 0.27 ms but their prediction steps reach 4 ms at p99.
What dominates now (`sample` of the one-core bench driver, 2,528 samples inside `NavEKF3::UpdateFilter`):
array copying is gone (`lean_copy_expand_array` 8 samples, `Array.extract` none); FloatLib's `Binary64`
arithmetic takes 2,129 (84%), and 1,538 of them (61% of the whole) are FloatLib's model fallback
(`Configured.Backend.Internal.Fallback.binary64Add`, `Sub`, `Mul`, which compute on `Nat` with GMP: `mpz`
construction, `lean_cstr_to_nat`, allocation and frees). FloatLib's word kernels decline some inputs and fall back to the model on `Nat`: `addFieldsWord?`
returns `none` when either significand is zero (`FloatLib/Floats/ExecFloat/Backends/Word/Small/Add/Runtime.lean`),
and EKF3's arithmetic is full of zero operands (the zeroed rows and columns of P, zero states and
innovations). The next speed step is therefore in FloatLib (word paths for zero operands and the other
declined cases) or in `support/CFloat.lean` (`@[csimp]` fast paths with proofs, as Phase 1 did for the
comparisons), not in the translator.

### Difftests and goldens

```
$ python3 difftest.py ardupilot/EKF3
ardupilot/EKF3 NavEKF3 (one_core): 0 of 24001 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/EKF3 NavEKF3 (two_cores): 0 of 24001 lines differ (0 tokens equal only as NaN vs NaN with different bits)
$ python3 difftest.py fastcalls
fastcalls World: 0 of 20091 lines differ (2124 tokens equal only as NaN vs NaN with different bits)
```

`ardupilot/translate_ekf3.sh` passes `--array-offsets --swap-out`; `tests/golden/ardupilot/EKF3_lib.lean` is
regenerated (14,652 lines, 606 definitions; the differences: `zero_range` and `fill_nanf` with offsets, the
18 swap-outs, renumbered temporaries). Every other golden is byte-identical (the examples, `CFloat.lean`,
`CString.lean`, libm, the rejection tests, the ArduPilot translations); `pointers`, `worldptr`, `ekfdal`,
`ekfdata`, `ardupilot/EKFGSF`, `ardupilot/AP_Math`, `ardupilot/Copter` translate to the same bytes and their
difftests stay at 0 differing lines.

### AP_AHRS (the groundwork; translated in "Phase 3: AP_AHRS translated" below)

What was in place before the translation:

- `ardupilot/unity_ahrs.cpp`: `unity_ekf3.cpp`'s sources plus `AP_AHRS.cpp`, `AP_AHRS_Backend.cpp`,
  `AP_AHRS_DCM.cpp`, `AP_AHRS_NavEKF3.cpp`, `AP_AHRS_View.cpp`, unmodified (checked as `ekf_common.sh` does),
  and `AP_AHRS ahrs;` (AP_Vehicle.h:419 holds it as a member of the vehicle; here a file-scope object). No
  `NavEKF3 EKF3;` of its own: the front end is the backend's static member, defined by AP_AHRS_NavEKF3.cpp:13,
  a World object `EKF3` under `--member-objects` (so the EKF3 harness's `w.EKF3`, `w.EKF3'p`, `w.EKF3'inp`
  stay valid). One World: `ahrs` (its state holds the DCM and EKF3 backends' state and the three
  `Estimates`), `EKF3`, AP_DAL's heap singleton, the cores, the EKFGSF_yaw slots, the view's heap slot
  (`create_view`, ArduCopter/system.cpp:454).
- `ardupilot/ahrs.use`: the 49 entry points (what ArduCopter, AP_Vehicle, AP_Arming and GCS call on AP_AHRS,
  and what the `--est` probe reads: REFERENCE.md "Estimation output").
- `ardupilot/translate_ahrs.sh` (`ardupilot/out/AHRS/AHRS_lib.lean`): the EKF3 script's options plus
  `--member-objects`, the AHRS headers, `AP_AHRS_SIM` instead of `AP_AHRS` in `--boundary`. It does not
  translate yet (exit 2).

The reachable rejections (`ardupilot/translate_ahrs.sh --keep-going --survey`, with the backends' `update`,
`get_results`, `reset`, `reset_gyro_drift` and the view's `update` added as entry points, since the dispatch
that reaches them is itself rejected): 111.

- **62: pointers to member objects of a World object** (with `const_cast<AP_AHRS*>(this)` of the const
  overloads and the initializer of `backends_and_estimates`). AP_AHRS selects its backends through
  `AP_AHRS_Backend *configured_backend, *active_backend` and `AP_AHRS_Backend::Estimates *configured_estimates,
  *active_estimates, *secondary_estimates`, set from `&dcm`, `&ekf3`, `&sim`, `&dcm_estimates`, ...
  (`backend_for_type`, `estimates_for_type`, AP_AHRS.cpp:245, :859), then calls through them
  (`configured_backend->update()`, `->get_results(*configured_estimates)`) and reads 40 fields through them
  (`active_estimates->roll_rad`, AP_AHRS.cpp:411-490; the inline getters of AP_AHRS.h). The model: a
  `WPtr` constructor per member object of a World object of the pointee class (`WPtr.ahrs'dcm`,
  `WPtr.ahrs'dcm_estimates`); a call or read through a pointer member of the object whose function runs is a
  `match` on the tag over its own members (`s.dcm`, `s.ekf3`, `s.sim`), a write through it (`*configured_estimates
  = {}`) a `match` writing the member, a dereference passed to a reference parameter a temporary read and
  written back by `match`. `AP_AHRS_Backend::get_results(Estimates &)` and the `const AP_AHRS_Backend &`
  parameter of `try_set_common_origin` (an abstract class) are reached the same way.
- **5: range-based `for` over `backends_and_estimates[]`**, a member array of structs of two references
  (`{ dcm, dcm_estimates }, { ekf3, ekf3_estimates }, { sim, sim_estimates }`, AP_AHRS.h:1051-1069): to be
  unrolled over the constant array, each reference the member it is bound to, `&b.backend == configured_backend`
  a comparison of tags.
- **The rest (44)**, each with an existing mechanism or a boundary decision: `HALSITL::Semaphore _rsem`
  (`--semaphores`); `AP_Vector3f _trim` and `set_enable` of `AP_Int8` (`--param-ext`); `AP_Notify::flags`
  writes and `hal.util->persistent_data` (DCM's `backup_attitude`, the watchdog home: boundary outputs and
  inputs); `GCS_SEND_MESSAGE`, `gcs().send_text` with formatted arguments, `AP::logger()` (dropped: GCS and
  logging); `AP_BoardConfig::config_error` (only with `AHRS_EKF_TYPE 1`: dropped as unreachable);
  `AP::sitl()->loop_time_jitter_us` (a SITL parameter: a boundary input) and `hal.opticalflow` (null: a
  boundary input); the DCM loops bounded by `ins.get_accel_count()` and `while (... && counter++ < 20)`
  (`--runtime-loops` with boundary bounds; the latter needs the `counter++` form); `compass.read()` and
  `baro.get_climb_rate()` (non-const boundary calls with results: inputs with a call count);
  `AP_AHRS_Backend::get_EAS2TAS` (a static function reading `AP::baro()`); `memcmp` in `Location::same_loc_as`
  (`--pointer-params`' byte comparison). (Two `switch` fallthroughs at AP_AHRS.cpp:250 and :864 are artifacts
  of the survey: the case's only statement, `return &dcm;`, is the rejected pointer.)

Boundary decisions for the AHRS stage: `AP_AHRS_SIM` stays boundary (PORT-PLAN 2.2): its `update`,
`reset`, `reset_gyro_drift` are inline no-ops (translated), its `get_results` (AP_AHRS_SIM.cpp:107, which reads
the simulator through `AP::sitl()`) fills `sim_estimates`, which AP_AHRS reads only through
`estimates_for_type(EKFType::SIM)` (`AHRS_EKF_TYPE 10`) and, in `try_set_common_origin`, only its
`provides_common_origin` (always false for SIM): with `AHRS_EKF_TYPE 3` it is not observable, so
`get_results` is `--drop`ped (the difftest's C++ side answers `AP::sitl()` with a null pointer, which makes
the real `get_results` leave `sim_estimates` at `{}` too). Text: `GCS_SEND_TEXT` ("AHRS: %s active", "EKF3
primary changed", DCM's watchdog message) dropped, as in EKF3; `pre_arm_check` and its failure strings not
an entry point (D10).

What the difftest needs (not written): `ardupilot/ekf3_difftest.py` driven by `AP_AHRS::update` instead of
`NavEKF3::UpdateFilter`, with `init`, `reset`, `set_vehicle_class` at the start and the setters on their
REFERENCE.md schedule (`set_home` at 14.41 s and at arming, `set_terrain_hgt_stable`, `resetHeightDatum`,
`request_yaw_reset`), the AHRS's and DCM's boundary inputs added to the line (AP_InertialSensor's gyro,
accel, delta time and counts, AP_GPS's status, velocity, ground course, Compass's `read` and field, AP_Baro's
climb rate, the armed flag, the SITL jitter parameter), `ekf3_env.cpp`'s stub front ends extended with the
getters DCM calls, every leaf of `ahrs` (with `dcm`, `ekf3`, the three `Estimates`) and of the view printed,
and a scenario in which EKF3 is unhealthy for a while (a GPS glitch or an IMU fault that makes
`ekf3_estimates.filter_faults` non-zero) so that `_active_EKF_type` falls back to DCM and back.

## Phase 3: the estimator World and the EKF3 replay (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), seventh stage: the sensor World ("Phase 3: sensor front ends and
AP_Param", "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source") and AP_DAL + NavEKF3 ("Phase 3: AP_DAL and
NavEKF3") translated as one World, in which AP_DAL's `start_frame` reads the translated front ends and NavEKF3 uses its
translated AP_NavEKF_Source; the EKF3 replayed on the whole of both recorded flights against the reference's `--est`
trace, bit for bit per step; its speed per 400 Hz step. AP_AHRS, `AP::vehicle()` and the HAL's other drivers stay
boundary: the replay harness makes the calls AP_AHRS makes (below, "What the harness does in place of AP_AHRS").
`Sensors_lib`, `EKF3_lib`, `NavEKF_Source_lib` and every other golden are byte-identical; their difftests are unchanged.

### New option and translator changes

| change | gated by | what |
|---|---|---|
| lazy singleton getters | `--est-world` (new) | `static C *get_singleton() { if (!_singleton) { _singleton = new C(); } return _singleton; }` (AP_InertialSensor.cpp:738-744, reached through `AP::ins()` from AP_DAL) of a class with a file-scope object, whose constructor sets `_singleton = this` before anything runs: an accessor of that object (`AP::ins()` is `w.ins`), and its `new` is not a heap allocation (no `heap'AP_InertialSensor` slot) |
| a World pointer from an indexed boundary call | `--est-world` | with `--indexed-inputs`, `AP::serialmanager().find_serial(GPS, uart_idx)` (one non-constant argument) is the `--ins-gps` pointer read (the port stand-in or null, by an input flag per index), not an indexed input of type pointer |
| reference members bound to the heap singleton | (`--ins-gps` with `--world-pointers`) | `heap_elem_refs` (references bound to elements of a World object's array) leaves out a reference to a heap singleton (`AP_DAL &dal` of the cores, `NavEKF3_core(this, dal)`, AP_NavEKF3.cpp:860), which `--ekf-types --world-pointers` already resolves; it rejected it before |
| dropped calls' arguments | (`--reachable`) | a call of a free function whose body is `return e;` with e without effects and whose parameters are values or const references (`degrees(x)`, AP_ParamT.cpp's `default_as_float(v)`) has no effect: allowed in the arguments of a `--drop`ped call (`DEV_PRINTF(..., degrees(best_diff[k]))`, AP_InertialSensor.cpp:1835; `add_default(this, default_as_float(v))`); rejected before |

Only translations that were rejected before change, so every earlier output is byte-identical (checked: the examples,
the rejection tests, libm, and every ArduPilot golden: AC_PID, AP_Math, Copter, AHRS_View, LowPassFilter2p,
AC_CommandModel, AP_Declination, AP_Common, Text, StorageManager, AP_InternalError, AP_RTC, EKF_Buffer, EKFGSF,
EstScheduler, Sensors, NavEKF_Source, EKF3; each translated twice, deterministic). `CPP2LEAN_DEBUG_TARGETS=1` prints the
possible objects of a pointer where a dereference or a boundary pointer read is rejected (a debugging aid, stderr only).

### The translation (`ardupilot/translate_estimation.sh` → `ardupilot/out/Estimation/Estimation_lib.lean`)

`ardupilot/unity_estimation.cpp` includes the sources of `unity_sensors.cpp` and `unity_ekf3.cpp` once each (all with
the flags of their units in the reference build, which are the same for all of them: `ekf_check_unity` checks each file)
and defines the objects `sitl`, `barometer`, `compass`, `ins`, `gps`, `rtc`, `est_uart` and `EKF3` (the scheduler
stand-in defines `est_scheduler`); AP_DAL is the heap singleton, the cores and the EKFGSF_yaw banks are heap slots as in
`EKF3_lib`. The options are the union of the two scripts' (`--front-ends --ins-gps --gotos --param-ext --ap-param
--ekf-types --ekf-arrays --ring-buffers --pointer-params --array-offsets --runtime-loops --general-loops --swap-out
--uninit-reads --indexed-inputs --output-log --world --world-pointers --reachable`, plus `--est-world`), with one entry
list, `ardupilot/estimation.use` (`Sensors.use`, `ekf3.use`, NavEKF3::setTerrainHgtStable, the per-core getters the
probe reads, the scheduler stand-in's harness entries). The EKF sources are translated files (`--header`), the front
ends and libraries `--lib-dir`s. Changes of the boundary against the two separate translations:

- **The front ends are World objects.** `AP::ins()`, `AP::baro()`, `AP::compass()`, `AP::gps()` in AP_DAL's
  `start_frame`s (and `AP::dal().compass().get_num_enabled()` in AP_NavEKF_Source, `dal.baro().update_calibration()` in
  the cores) are the World's `ins`, `barometer`, `compass`, `gps`: the 58 input fields of AP_DAL's front-end members in
  `EKF3_lib` and 5 of its own (the INS's last update and loop delta, the barometer's EAS2TAS, the clock) are calls of the
  translated getters (`AP_Baro.get_altitude_uint8_t w.barometer i`, `w.gps.state[i]!.location.lat`).
- **The HAL clock** is the scheduler stand-in's (`AP_HAL::micros64` and friends translated, as in `Sensors_lib`), not
  `--boundary-fn` inputs.
- **AP_NavEKF_Source** is NavEKF3's member `sources`, translated with its parameters (`--param-ext`): no
  `--boundary-call @ekf3_sources.boundary`, no per-core source inputs.
- **EKF3's parameters are state** (`--param-ext`): `w.EKF3._gpsHorizVelNoise._value` instead of `w.EKF3'p`, set by
  NavEKF3's constructor from `var_info` and `var_info2` (with the `sources` group's constructor for its own table).
- **What stays boundary**: AP_AHRS (AP_DAL's reads of home, vehicle class, fly forward, takeoff/touchdown expected,
  trim, configured EKF type and the vehicle-to-autopilot rotation; the front ends' `get_origin`, `get_location`;
  `resetHeightDatum`, `update_orientation`, `set_takeoff_expected` as output events), `AP::vehicle()->get_time_flying_ms()`,
  `AP::wheelencoder()` (null), the HAL's Util (armed flag, watchdog, `available_memory`, `set_hw_rtc`), AP_Notify's
  flags, AP_SerialManager, AP_BattMonitor, SRV_Channels; dropped as in the two translations, plus `AP_Param::add_default`
  (the GCS's list of defaults, reached through `_imuMask.set_and_default`, AP_NavEKF3.cpp:823). AP_DAL's inputs: 13
  fields (76 in `EKF3_lib`); NavEKF3's and the cores' source inputs (14) are gone.

| translation | Lean lines | definitions | ArduPilot lines covered (function extents, `/-- C++ ... file:a-b`) |
|---|---|---|---|
| `Estimation_lib` | 22,525 | 1,060 | 16,481 in 867 functions: AP_NavEKF3 9,208, AP_InertialSensor 1,657, AP_Math 1,076, AP_NavEKF 931, AP_GPS 907, AP_Compass 848, AP_Baro 687, AP_DAL 545, Filter 199, AP_Common 146, AP_Declination 103, AP_RTC 72, AP_Param 71, AP_HAL 31; the stand-ins and the scheduler 398 |
| (for comparison, the same count) `EKF3_lib` + `Sensors_lib` | 14,652 + 8,174 | 606 + 482 | 11,487 + 5,591 |

It elaborates without warnings in 48 s (`lake build`, one thread; its C compiles in 100 s) and translates in about
3 minutes. Golden `tests/golden/ardupilot/Estimation_lib.lean` (`tests/run_tests.sh` translates it and compares).

### The parameters (`# params`)

The World holds the parameters of AP_Baro, Compass, AP_InertialSensor, AP_GPS, NavEKF3 and its AP_NavEKF_Source; the
replay must start from the values the reference loaded from `storage_in.bin`. AP_Param's loading from the storage image
(`AP_Param::load_all`) is not translated, so the probe prints them: `reference/hal/est_probe.cpp`'s `# params` line now
also has every parameter of NavEKF3's `var_info` and `var_info2` in table order (68: `EKF3._enable` ...
`EKF3._options`) and of its `sources` group (`EKF3.sources._source_set[i].posxy` ... `.yaw` for the three sets,
`EKF3.sources._options`): 261 parameters, 84 of them EKF3's. No AP_AHRS parameter is held by the World (AHRS_EKF_TYPE,
the trim and the orientation are read through `cfg=` and the AHRS inputs). The reference rebuilt in the work clone
(`python3 reference/build.py`, one unit) reproduces both flights' outputs (`cmp`, with and without `--est`) and every
earlier key of `est.txt` (`reference/tools/est_compare.py sim/out/F/est.txt build/est/F.txt`: 36,013 steps,
8,909,177 values, all equal, both flights); only the `# params` line grew.

### What the harness does in place of AP_AHRS

(Superseded by "Phase 3: AP_AHRS in the estimator World, the full estimation replay": `ardupilot/estimation_replay.py`
and `lean/EstimationReplay.lean` now drive `Estimator_lib`, whose AP_AHRS is translated, and the commands below other
than the sensor replay's are replaced by the vehicle's calls on it. This subsection and the next two record the seventh
stage's harness and its results.)

`ardupilot/estimation_replay.py` and `lean/EstimationReplay.lean` extend the sensor replay (same boot sequence: the
parameters, the input records fed ahead, the scheduler stepped where the vehicle consumed a line, `barometer.init`,
`gps.init`, `compass.init`, `barometer.calibrate`, `ins.init(400)` at their events, then per main loop
`wait_for_sample` and the tasks in `tasks=` order). The AP_AHRS side, exactly:

- **Boot** (`Copter::startup_INS_ground`: `ahrs.init()`, `set_vehicle_class(COPTER)`, `ahrs.reset()`): no call on the
  World. AP_AHRS::init's `update_orientation` sets the board orientation the front ends already have (AHRS_ORIENTATION
  0); its EKF-type checks change nothing with AHRS_EKF_TYPE 3; `AP_AHRS_NavEKF3::reset` returns while not started;
  AP_AHRS_DCM::reset's loop over `ins.wait_for_sample()`/`update()` runs only while the accelerometer's length is
  outside [9, 11] m/s², which it is not (the sensor replay's `ins=` keys would show those updates).
- **`AU`, fast task 3 (`read_AHRS`: `ahrs.update(true)`)**: (1) the values AP_DAL's `start_frame` reads from AP_AHRS and
  the vehicle, from the trace's previous step (each setter runs after task 3: arming in task 28, `set_land_complete` in
  task 8, home in task 7 or 28): armed (`armed=`), home (`home=`), vehicle class, fly forward, configured EKF type and
  trim (`cfg=`), takeoff/touchdown expected (`tkd=`), time flying = `millis() - _last_flying_ms` while `likely_flying`
  (`flying=`: AP_Vehicle::get_time_flying_ms), the vehicle-to-autopilot rotation (the identity: `update_trim_rotation_matrices`
  of a zero trim; a non-zero trim is not modeled), `available_memory` 512 KiB (lockstep.cpp's Util), no wheel encoder;
  (2) AP_AHRS_NavEKF3::update (the configured backend first): while not started, the first call sets `start_time_ms =
  millis()` and once `millis() - start_time_ms > 1000` each call runs `NavEKF3::InitialiseFilter`, until it returns
  true; once started, `NavEKF3::UpdateFilter` (also in the call in which InitialiseFilter succeeded); AP_DAL's
  `start_frame` runs inside both, as NavEKF3 issues it; (3) AP_AHRS_DCM::update (the other backend): its only effect on
  the World is drift_correction_yaw's forced `compass.read()` while it has no initial yaw (AP_AHRS_DCM.cpp:672-683:
  compass used for yaw, a new compass sample, `ins.get_delta_time() <= 0.2`), modeled with DCM's `have_initial_yaw` and
  `_compass_last_update`. AP_AHRS's own bookkeeping (estimates, reset counters, origin, notify flags) touches nothing
  of the World; the SITL loop jitter is 0.
- **`TH`, task 11 (`update_ekf_terrain_height_stable`)**: where `thgt=` changes, AP_AHRS::set_terrain_hgt_stable
  forwards to `NavEKF3::setTerrainHgtStable` (3 → 0 at 2.305 s, 0 → 1 → 0 → 1 in flight).
- **`resetHeightDatum`**: AP_Baro::update's field elevation (14.485 s) calls `AP::ahrs().resetHeightDatum()`, an output
  event of the World; the harness then calls `NavEKF3::resetHeightDatum` (AP_AHRS_NavEKF3.h:71; DCM's and SIM's do
  nothing). In the vehicle it runs before the barometer's own `update_calibration()`, here after it; both set the ground
  pressure from the same pressure, and the EKF3 reads the barometer through AP_DAL's snapshot, so the order is not
  observable.
- AP_AHRS's other calls on the EKF3 (`set_origin`, `request_yaw_reset`, `check_lane_switch`, `set_posvelyaw_source_set`)
  do not occur in the flights (REFERENCE.md "Inputs from the rest of the vehicle"); `set_takeoff_expected` from the EKF3
  would show in `tkd=`, which stays 0 (the harness stops if it does not).

### The replay (`ardupilot/estimation_replay.py FLIGHT`)

Per line the harness prints the probe's EKF3 keys, computed from the World as `est_probe.cpp` computes them (`primary`,
`ncores`; while there are cores `gbias`, `abias`, `var` through the front end's getters, and per core `c<k>.x` the 24
states, `c<k>.fs` the core's `getFilterStatus` and `statesInitialised`, `c<k>.P`/`.out`/`.imu` the FNV-1a digests of P,
the output predictor and the IMU buffer, `c<k>.var`, `c<k>.gsf` with the digest of the EKFGSF_yaw bank) and the front
ends' keys; the script compares every value with the trace.

```
$ ardupilot/estimation_replay.py sim/out/lockstep-flight
estimation replay lockstep-flight: 36013 lines (boot init through 35098 main loops); steps compared: 35122 (891 inside barometer.calibrate and ins.init not compared); values compared: 5875104 (EKF3 keys 2082728), equal: 5875104, different: 0; 0 steps differ
$ ardupilot/estimation_replay.py sim/out/lockstep-flight-noisy
estimation replay lockstep-flight-noisy: 36013 lines (boot init through 35098 main loops); steps compared: 35122 (891 inside barometer.calibrate and ins.init not compared); values compared: 5875104 (EKF3 keys 2082728), equal: 5875104, different: 0; 0 steps differ
```

(about 10 s each; the script writes `build/est/<flight>.txt` with the reference when it is missing or older than
`copter_ref`, and `lean/EstimationReplayParams.lean` from the `# params` line.) The EKF3 starts at line 1,316 (3.29 s:
`InitialiseFilter` 1,003 ms after the first `ahrs.update`), so 34,698 steps have a core. Sensitivity of the harness
(`ESTIMATION_REPLAY_DROP`): without `AU` 34,698 steps differ (from line 1,316); without the `resetHeightDatum`
forwarding 30,220 differ, first `c0.x` and `c0.out` at line 5,794 (14.485 s); without `TH` or without DCM's compass read
none differ: the terrain flag is read only with a range finder, and DCM's read comes in the first main loop, in which
`compass.read` of task 13 runs too (both are kept, as the vehicle makes them).

### The World difftest (`python3 difftest.py ardupilot/Estimation`)

`ardupilot/Estimation.json` is `Sensors.json` with the EKF sources and NavEKF3 added: environment
`ardupilot/estimation_env.cpp` (sensors_env.cpp included, with the HAL's Util answering AP_DAL's `available_memory` and
`malloc_type` through `CPP2LEAN_ENV_UTIL_EXTRA`; AP_AHRS's members AP_DAL reads set in its storage from the line; AP_Vehicle's
`likely_flying`/`_last_flying_ms` from the line's time flying), setups ending with `EKF3.InitialiseFilter` (the cores and
banks allocated), 600 random calls and the corner values over 214 member functions of the 8 objects (NavEKF3's entry points
other than InitialiseFilter and UpdateFilter guarded by `EKF3.core != nullptr`: several index `core[]` without a test),
every leaf printed (2,060 per line plus the heap objects': AP_DAL, the core, the bank; 4,163 tokens per line). New
difftest setting: `cxx_union_params` (`EKF3.getFilterStatus`'s `nav_filter_status` out-parameter is its integer in the model).

```
ardupilot/Estimation World (calibrated): 0 of 8399 lines differ (1 tokens equal only as NaN vs NaN with different bits)
ardupilot/Estimation World (wild): 0 of 8399 lines differ (5480 tokens equal only as NaN vs NaN with different bits)
```

(about 3.5 minutes without the translation.) It is a short test of the combination (the front ends read by AP_DAL's
frames, the cores' setup, the getters, the boundary): the cores are set up but their bootstrap never succeeds on random
lines, so the filter's prediction and fusion are covered by `ardupilot/EKF3`'s difftest and by the replay above.

### Speed (`ardupilot/estimation_replay.py FLIGHT --bench K`)

As `sim/BENCH.md` measures: the harness parses every command first; the parameters and the input records (the HAL's
input, as the protocol's parsing is outside the C++ figure) are set and fed outside the timed region; `IO.monoNanosNow`
around each line's calls (and around its `AU` alone); one process per launch, 6 launches, the first discarded, each
step's median over the launches; lake's release build; Apple M4, one thread. The deterministic flight:

| part | steps | mean µs | median µs | p99 µs | max µs | total |
|---|---|---|---|---|---|---|
| all steps | 36,013 | 136.8 | 56.0 | 1,908 | 7,225 | 4.93 s |
| boot init (lines consumed inside `setup()`'s delays; the calibrations' calls) | 914 | 3.3 | 0.2 | 0.4 | 2,473 | 3 ms |
| main loop | 35,099 | 140.2 | 56.3 | 1,991 | 7,225 | 4.92 s |
| main loop, AP_AHRS::update alone (EKF3 through AP_DAL) | 35,099 | 127.3 | 44.1 | 1,978 | 7,212 | 4.47 s |
| main loop, the rest (front ends, scheduler, stand-ins) | 35,099 | 12.9 | 12.7 | 19.9 | 64 | 0.45 s |

Against the reference (REFERENCE.md): AHRS + EKF3 0.69 µs per step in C++, the Lean EKF3 127 µs (about 185 times; the
C++ figure includes AP_AHRS and DCM, which the Lean does not run yet); the whole reference vehicle 3.4 µs per step. The
real-time budget of the whole vehicle is 2,500 µs per step: the estimator takes 5.6% of it on average and 80% at p99;
2 of 36,013 steps exceed it (7.2 ms at 47.8 s and 3.3 ms at 6.1 s, deterministic over the launches), and the 4,318
steps whose AP_AHRS::update takes over 200 µs (the 12 ms prediction steps, every 4th or 5th) average 0.74 ms. What
dominates (macOS `sample` of a bench launch, the 2,805 samples inside the timed calls): FloatLib 77% (its `Binary64`
model fallback on `Nat`/GMP 53%: `binary64Add`/`Sub`/`Mul` declined by the word kernels, with `mpz` construction,
`lean_cstr_to_nat`, allocation and frees; the word kernels and dispatch 24%), the translated code itself 22%, the harness
1%. As the "AP_AHRS, and speed" stage found, the next step is in FloatLib (word paths for the declined cases, zero
operands first) or `support/CFloat.lean` (`@[csimp]` fast paths with proofs), not in the translator.

### What integrating the translated AP_AHRS needs

(Done: README.md "Phase 3: AP_AHRS in the estimator World, the full estimation replay".) The World is ready for it: AP_AHRS's unity (`ardupilot/unity_ahrs.cpp`) holds NavEKF3 as `AP_AHRS_NavEKF3::EKF3`
(`--member-objects`, the same World field name `EKF3`), so the harness's `AU`/`TH`/resetHeightDatum steps become calls of
the translated `AP_AHRS::update(true)`, `set_terrain_hgt_stable`, and the barometer's `AP::ahrs().resetHeightDatum()`
becomes a call on the World's `ahrs` instead of an output event. Steps: (1) the translator's pointers to member objects
of a World object (AP_AHRS's backend and estimates pointers) and the range-for over `backends_and_estimates`
("Phase 3: AP_AHRS, and speed"); (2) a unity of `unity_estimation.cpp` and `unity_ahrs.cpp`'s AP_AHRS sources, with
`AP_AHRS ahrs;` and without `NavEKF3 EKF3;`, AP_AHRS removed from `--boundary` (AP_DAL's, the barometer's and the
compass's reads of it become calls), and `ahrs.use`'s entry points added; (3) the AHRS's own boundary as inputs: the
vehicle's armed, flying and home state (`armed=`, `flying=`, `home=`, set by the vehicle's setters: `set_home`,
`lock_home`, `set_likely_flying` are AHRS/vehicle calls the harness makes from the trace), `cfg=`'s class via
`set_vehicle_class`, AP_AHRS's parameters in `# params` (AHRS_EKF_TYPE, AHRS_ORIENTATION, the trim, AHRS_GPS_USE, ...);
(4) the harness: `ahrs.init`, `set_vehicle_class`, `ahrs.reset` at boot, `ahrs.update(true)` at task 3, the setters at
their tasks, and the probe's AHRS keys (`q`, `rpy`, `dcm`, `vel`, `pos`, `loc`, `gyro`, `accef`, `resets`, `healthy`,
`initialised`, `origin`, `ekf`, `fs`) compared with the World's AP_AHRS getters, as the EKF3 keys are now. The
harness's AP_AHRS_NavEKF3 start logic and DCM compass-read emulation then go away (they are the translated code).

## Phase 3: AP_AHRS translated (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), seventh stage: AP_AHRS with AP_AHRS_Backend, its EKF3 backend
AP_AHRS_NavEKF3 (whose static member is the NavEKF3 front end `EKF3`), the DCM fallback AP_AHRS_DCM and the view
AP_AHRS_View, translated from the unmodified sources on top of the AP_DAL and NavEKF3 translation into one World
and difftested bit for bit (one and two EKF3 cores, the DCM phase before EKF3 starts, the switch to EKF3, a
switch to SITL's SIM backend and back, an IMU fault that makes AP_AHRS fall back to DCM until NavEKF3 changes
lanes, a GPS glitch, the vehicle's setters). The model of pointers and references to member objects that
"Phase 3: AP_AHRS, and speed" proposed is `--member-pointers`; AP_AHRS's and DCM's other constructs are
`--ahrs-ext`. Both are new options, so every earlier translation is byte-identical (the examples, the rejection
tests, libm, the ArduPilot goldens, among them `EKF3_lib.lean`); the only change outside them is a faster
`find_file` (below).

### New options

| option | meaning |
|---|---|
| `--member-pointers` | (with `--world-pointers`) a member object of a World object whose address is taken, or to which a reference member of an unnamed struct is bound, has a `WPtr` tag `<object>'<member>`; pointers to it, such reference members and reference parameters of the owner's member functions whose address is taken (or whose class is abstract) are the tag; calls, reads and writes through them select the running object's own member |
| `--ahrs-ext` | AP_AHRS's and DCM's other constructs (list below) |

### Pointers to member objects (`--member-pointers`)

AP_AHRS holds its backends and their results as member objects (`dcm`, `ekf3`, `sim`; `dcm_estimates`,
`ekf3_estimates`, `sim_estimates`), selects them through pointer members set from `&member`
(`configured_backend = backend_for_type(type)`, `return &dcm;`, AP_AHRS.cpp:245-266, :859-886), calls virtual
member functions through them (`configured_backend->update()`, `->get_results(*configured_estimates)`), reads
and writes through them (`active_estimates->roll_rad`, `*configured_estimates = {}`, AP_AHRS.cpp:411-490,
:587), passes `*p` to reference parameters, compares addresses (`&backend_and_estimates.backend ==
configured_backend`, `&dest.estimates == &source_estimates`), and iterates over `backends_and_estimates[]`, a
member array of structs of two references bound to the members (AP_AHRS.h:1051-1069). The model:

- **Tags.** `member_tags` finds, before the field defaults are computed, every data member of class or struct
  type (or of a `--boundary` class: `AP_AHRS_SIM sim`) of the class of a World object (the class's only one)
  whose address the program takes or to which a reference member of an unnamed struct is bound (not `&x` passed
  to `memset`/`memcpy`/`memcmp`, which is the object's bytes: NavEKF3's `memset(&yaw_reset_data, ...)`). Each
  gets a `WPtr` constructor `ahrs'dcm`, `ahrs'ekf3_estimates`, ...; `&dcm` is `WPtr.ahrs'dcm`. The pointer
  members stay `WPtr` fields (`configured_backend : WPtr`), so the difftest prints them by name.
- **The objects a pointer may designate** follow from its class (closed world, as for `--world-pointers`): an
  `AP_AHRS_Backend *` the tagged members of a class derived from AP_AHRS_Backend (`dcm`, `ekf3`, `sim`: the
  boundary class's bases are read from its definition), an `Estimates *` the three estimates. Such a pointer
  is used only in the member functions of the object that holds the members (else rejected), whose state is `s`.
- **Reads and writes** through a pointer (or reference) whose objects are all of one class are a path step
  `fm` that selects the member by the tag: `active_estimates->roll_rad` is `((match s.active_estimates with |
  .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) :
  AP_AHRS_Backend.Estimates.State).roll_rad` (the `_` arm: any other tag is undefined behavior in C++, as
  `fi`'s last arm), a write `s := (match tag with | .ahrs'dcm_estimates => { s with dcm_estimates := v } |
  ...)`; such a path is passed to reference parameters (`get_results(*configured_estimates)`) and written back
  as any other. (The type ascription is needed: Lean's `do` elaborator fails, "Failed to assign join point
  RHS", on a `match` term whose type it has to infer after a `match` statement of the same block.)
- **Calls** through a pointer or reference are a `match` statement on the tag, one arm per member object, each
  the call of its class's final overrider on that member's path, translated as a direct call on the member
  (parameters, reference members, inputs, outputs, the self-reach cycle and `--swap-out` as for `dcm.update()`
  written out); a result is a `let mut` variable each arm assigns. An arm for a member of a `--boundary` class
  is its overrider's boundary call (`sim.get_origin(ret)`: inputs), nothing if the overrider is `--drop`
  (`AP_AHRS_SIM::get_results`), or the overrider's or inherited body if it is empty or `return <literal>;`
  (`AP_AHRS_SIM::update() { }`, `AP_AHRS_Backend::set_origin(...) { return false; }`).
- **References as tags.** A reference member of an unnamed struct bound to a member object (`AP_AHRS_Backend
  &backend` of `backends_and_estimates[]`) is a `WPtr` field initialized with the tag; `be.backend.update()`
  is a call through it, `&be.backend` its value. A reference parameter `[const] T &x` of a member function of
  the owner, where T has tagged members and x's address is taken or T is abstract (`try_set_common_origin(const
  AP_AHRS_Backend &source_backend, const Estimates &source_estimates)`, AP_AHRS.cpp:493), is passed as the tag;
  a local reference bound to a tagged object (`auto &backend = be.backend;`) is a `WPtr` local.
- **Range-for** over a member array (`for (auto &be : backends_and_estimates)`) is the `--front-ends` loop
  (`for i in [0:3]`, the element an alias), now also under `--member-pointers`.
- **Also:** `x = {}` for a struct (value-initialization: clang's `CXXConstructExpr` of an implicit constructor or
  an `InitListExpr` of `ImplicitValueInitExpr`s) is `({} : T)`, the structure's field defaults; a const member
  function `return const_cast<C*>(this)->f(args);` (`backend_for_type(type) const`, AP_AHRS.h:1096) is an alias
  of its non-const twin; a member call whose callee reaches the running object through the World now reloads that
  object from the callee's World before storing the member's state into it (in AP_AHRS, `dcm.update()` and
  `ekf3.update()` read `AP::ahrs()`; the reload after the store undid the member's update).

`examples/memberptrs.cpp` (golden `tests/golden/MemberPtrs.lean`) has the constructs in small: two backends of
different classes (one reaching a static member object of the World), their estimates, pointers set from
`&member` in the constructor and by a type selection, calls and reads through them, `*p = {}`, `*p` to a
reference parameter, a reference array of structs iterated with `continue`, a reference parameter compared by
address, a local reference, a const overload through `const_cast`. `python3 difftest.py memberptrs`:
`memberptrs World: 0 of 20091 lines differ` (sensitivity: the roll read through the other estimates' arm makes
19,927 of 20091 lines differ). `tests/reject_phase3k.cpp` holds the limits (6 rejections: a member read through
pointers to members of different classes, a subscript of such a pointer, an argument for a tag parameter that is
not a member object, a reference member bound to something other than a member object, a pointer to member
objects outside the owner's member functions, `memcmp` other than `memcmp(this, &x, sizeof(*this))`).

### AP_AHRS's other constructs (`--ahrs-ext`) and the boundary of this stage

The 44 other reachable rejections of the groundwork survey and those that appeared once the backends' code was
reached (DCM was unreachable while the dispatch was rejected), each by an existing mechanism, a boundary decision,
or a narrow construct of `--ahrs-ext`:

- **Semaphores**: `HAL_Semaphore _rsem`, `WITH_SEMAPHORE` (`--semaphores HALSITL::Semaphore,WithSemaphore,AP_HAL::Semaphore`).
- **Parameters without `--param-ext`** (which would make every parameter of the EKF3 translation state, PORT-PLAN
  4.4): `AP_Vector3f _trim` is a parameter of type Vector3f (its var_info default in each component, as
  `AP_Param::setup_object_defaults` does); `_enable.set_enable(v)` (AP_NavEKF3.h:323, from `AP_AHRS::init`) sets
  the value (AP_ParamT.cpp:33; its parameter-count cache is outside the model); DCM's `AP_Float &_kp_yaw`,
  `_kp`, `gps_gain`, `beta`, `AP_Enum<GPSUse> &_gps_use`, `AP_Int8 &_gps_minsats` (bound by AP_AHRS's `dcm{_kp_yaw,
  ...}`, AP_AHRS.h:1020) are the World object's parameters they are bound to (`w.ahrs'p._kp_yaw`), read and
  written there (`_kp_yaw.set(AP_AHRS_YAW_P_MIN)`, AP_AHRS_DCM.cpp:750); a World object's constructor that reads
  the boundary (AP_AHRS's, which selects its backends) gets the object's inputs as `World.init` has them.
- **Writes to boundary objects are outputs** (the last value): `AP_Notify::flags.gps_fusion`, `gps_glitching`,
  `have_pos_abs` (AP_AHRS.cpp:671); the HAL's persistent data, `pd.home_lat` etc. (AP_AHRS.cpp:1781) and DCM's
  `backup_attitude` (`pd.roll_rad`, AP_AHRS_DCM.cpp:315). A local reference or pointer to a boundary object of a
  type the translation does not hold (`AP_HAL::Util::PersistentData &pd = hal.util->persistent_data;`, `const auto
  *sitl = AP::sitl();`) is another name for it (reads are inputs: the watchdog home and attitude, read only after a
  watchdog reset, an input that is false; `sitl->loop_time_jitter_us`, a parameter of the SITL::SIM boundary
  object, 0 in the reference); `if (hal.opticalflow)` is an input (null: false).
- **Front-end reads are boundary inputs in this stage**, as AP_DAL's: INS (`get_accel`, `get_gyro`,
  `get_delta_angle`, `get_delta_time`, `get_accel_health(i)`, `healthy`, `get_gyro_drift_rate`, `use_accel(i)`,
  `get_delta_velocity(i, ...)`, the counts), GPS (`status`, `ground_speed`, `ground_course`, `num_sats`,
  `velocity`, `location`, `last_fix_time_ms`, `last_message_time_ms`, `get_lag`), compass (`use_for_yaw`,
  `last_update_usec`, `get_field`, `get_declination`), baro (`healthy`, `get_altitude`, `get_EAS2TAS`). New
  forms: a non-const call whose result is used (`compass.read()`, AP_AHRS_DCM.cpp:678; `AP::baro().get_climb_rate()`,
  :1487) is an input and its calls are counted (an output); `compass.calculate_heading(_dcm_matrix)` (a const call
  with a non-constant argument) is one input per call site (`--site-inputs`: the compass is boundary; the combined
  World translates it); a static member function without parameters whose body is `return e;` and which reads the
  boundary (`AP_AHRS_Backend::get_EAS2TAS`, `return AP::baro().get_EAS2TAS();`, AP_AHRS_Backend.cpp:277;
  `get_TAS2EAS`, `return 1.0/get_EAS2TAS();`) is e, translated at each call in the caller (its reads the
  caller's inputs); `random()` (the SITL loop jitter, not called with jitter 0) is `--boundary-fn`. Boundary
  outputs: `ins.update()`, `wait_for_sample()` (DCM's reset), `set_board_orientation`, `set_primary`,
  `hal.scheduler->boost_end()`, `delay_microseconds`, `AP::mission().write_home_to_storage()`.
- **Loops**: DCM's `for (i = 0; i < _ins.get_accel_count(); i++)` (AP_AHRS_DCM.cpp:830, :980): a bound that is a
  const boundary call without arguments is an input, fixed while the member function runs (`--runtime-loops`);
  `while ((initAccVec.length() < 9.0f || ...) && counter++ < 20)` (AP_AHRS_DCM.cpp:384) is `--general-loops`;
  `IGNORE_RETURN(x)`, `do {if (x) {}} while(0)` (AP_Common.h:64), is one iteration (C++ too: the condition's
  `IntegralToBoolean` of 0).
- **Smaller**: local arrays of class type without initializer (`Vector3f error[INS_MAX_INSTANCES];`, zero
  constructors, as `--ins-gps`); `nav_filter_status filt_state {};` (zero, as `--front-ends`); `const Vector3f
  &exported_gyro_bias = get_gyro_drift();` (an accessor of this object, its path; the accessor inlining of
  `--front-ends`, with `this` staying the running object and a World object's parameter read by an inlined
  accessor its `'p` field: `AP::ahrs().get_trim()`); `Location::is_zero`'s `!memcmp(this, &definitely_zero,
  sizeof(*this))` (AP_Common/Location.cpp:15) is the equality of every member (memcmp's nonzero value is 1; equal
  members are equal bytes when the padding bits are zero, which Location's constructors make so; floating members
  rejected); `degrees()`/`radians()` count as without effect in the arguments of a dropped call (DCM's GCS text).
- **Dropped**: `GCS::send_text` and `GCS::send_message` (text and MAVLink: the GCS stage); `AP_BoardConfig::config_error`
  (only with AHRS_EKF_TYPE 1); `AP_AHRS_SIM::get_results` (only observable with AHRS_EKF_TYPE 10: with the C++
  side's `AP::sitl()` state absent the real one fills nothing either; ahrs_env.cpp defines it so). AP_AHRS_SIM stays
  `--boundary` (PORT-PLAN 2.2): its member `sim` has a tag; its overriders' calls are boundary calls (inputs),
  empty bodies (`update`, `reset`, `reset_gyro_drift`) or dropped.

`find_file` (cpp2lean.py) called `os.path.realpath` for every node of the AST once per `--header` (51 headers ×
the AST of the AHRS unity: 135 million `lstat` calls, 3 of the 3.5 minutes of the translation); it now remembers
the real path of each file name: `ardupilot/translate_ahrs.sh` takes about 55 s (the same output).

### The translation

| translation | script (output) | Lean lines | ArduPilot lines covered |
|---|---|---|---|
| AP_AHRS, AP_AHRS_Backend, AP_AHRS_NavEKF3, AP_AHRS_DCM, AP_AHRS_View on AP_DAL, AP_NavEKF, AP_NavEKF3 (+ AP_Math, Location, AP_Declination as used) | `ardupilot/translate_ahrs.sh` (`ardupilot/out/AHRS/AHRS_lib.lean`, golden `tests/golden/ardupilot/AHRS_lib.lean`) | 19,279 (829 defs) | function extents: AP_AHRS 3,005 (AP_AHRS_DCM.cpp 1,249, AP_AHRS.cpp 1,052, AP_AHRS_NavEKF3.cpp 252, AP_AHRS_Backend.cpp 112, AP_AHRS_View.cpp 50, the headers 290), AP_NavEKF3 9,540, AP_NavEKF 962, AP_Math 909, AP_DAL 872, AP_Common 268, AP_Declination 173 (15,740 in all, 750 functions) |

One World: `ahrs` (its state holds the DCM and EKF3 backends' state, the three `Estimates`, the reference array
of tags; its parameters, inputs and outputs, with those of `dcm` and `ekf3` as sub-records), the front end `EKF3`
(the static member, `--member-objects`), the heap slots `heap'AP_DAL` (the singleton), `heap'NavEKF3_core`,
`heap'EKFGSF_yaw`, `heap'AP_DAL_Airspeed` (never allocated) and `heap'AP_AHRS_View` (`create_view`), the statics;
`WPtr` has the six member tags. AP_DAL's reads of `AP::ahrs()` (home, vehicle class, fly forward, takeoff and
touchdown expected, trim, EKF type, the body rotation), inputs of the EKF3 translation, are now the translated
AHRS; NavEKF3's `AP::ahrs().set_takeoff_expected` is its member function. `lake env lean` elaborates
`AHRS_lib.lean` in about 50 s (one thread), with no warnings. 17 calls through member pointers or references are `match`es on the tag (57 arms).

### The difftest (`python3 difftest.py ardupilot/AHRS`)

`ardupilot/AHRS.json` names its harness, `ardupilot/ahrs_difftest.py` (with `ardupilot/ahrs_scenario.py` and the
C++ boundary `ardupilot/ahrs_env.cpp`, `ardupilot/ahrs_env_param.cpp`), built on the EKF3 harness's pieces. C++:
the unmodified sources of the unity (AP_AHRS*.cpp with the EKF3 ones) compiled with the reference build's flags and
`-fno-access-control`, `AP_AHRS ahrs;` defined by the driver; the front ends zero-filled storage of their real
classes answering from the line (each getter from one canonical input; `ahrs_scenario` gives every input of the
same getter the same value: AP_DAL's, DCM's, AP_AHRS's, its EKF3 backend's), the HAL with a scheduler and util that
count the outputs, `AP::sitl()` zero-filled storage (loop jitter from the line), AP_AHRS_SIM's out-of-line
functions answering the line, `AP_Notify::flags`, `AP::mission()`. The inline getter that computes a constant
(`get_gyro_drift_rate`, `radians(0.5f/60)`) is asked of the C++ driver (`--consts`) and given to both sides.
Lean: `lean/AHRSMain.lean` (generated) sets `w.heap'AP_DAL'inp`, `w.EKF3'inp`, `w.heap'NavEKF3_core'inp` and
`w.ahrs'inp` from the line.

Each line is `<ops> <arg> <inputs>`: the vehicle's calls in order, `B` (boot: `create_view(ROTATION_NONE)`,
`init`, `set_vehicle_class(COPTER)`, `reset`, as `Copter::allocate_motors` and `startup_INS_ground`), `U`
(`update(true)`, `Copter::read_AHRS`, every line) and the setters at the run's events: `H` (`set_home` to
`get_location`'s location, `update_home_from_EKF`, at 15 s), `L` `lock_home`, `O` `set_origin`, `D`
`resetHeightDatum`, `T` `set_terrain_hgt_stable`, `K`/`W` `set_takeoff_expected`/`set_touchdown_expected`, `Y`
`request_yaw_reset`, `C` `check_lane_switch`, `E` the parameter AHRS_EKF_TYPE written (10, SITL's SIM backend, at
50 s, back to 3 at 52.5 s; 0 has no effect for Copter, which always uses an EKF). After each line both print the
calls' results, 35 getters (the `--est` probe's `q rpy dcm vel pos loc gyro accef resets healthy initialised origin
ekf fs`, the variances, innovations, home, source set, trim, ...), the outputs, and every leaf of every object:
`ahrs` (587 leaves with the DCM and EKF3 backends, the estimates, the tags; its parameters), `EKF3`, AP_DAL, every
core, every EKFGSF_yaw, the view, the statics. The scenario is `ekf3_scenario.py`'s (level at CMAC, armed at 39.5 s,
accelerating, cruising, decelerating; with two IMUs IMU0 biased from 42 s and NavEKF3 switching to core 1), with
the AHRS's inputs derived from the same samples; the two-core run adds a GPS glitch (60 m north from 45 s to 48 s)
and an IMU fault (one NaN delta velocity of IMU1, the primary's, at 55 s). What the AHRS does: DCM is the active
backend until EKF3 is started and initialised (0 to 2.0 s; `init`, `reset` and the DCM's attitude from the
accelerometers), then EKF3; SIM from 50 s to 52.5 s; in the two-core run, 0.2 s after the IMU fault the primary
core's states are NaN, its filter faults set, AP_AHRS falls back to DCM for 5 steps until NavEKF3 changes lanes,
then EKF3 again.

```
$ python3 difftest.py ardupilot/AHRS
ardupilot/AHRS AP_AHRS (one_core): 0 of 24001 lines differ (0 tokens equal only as NaN vs NaN with different bits)
ardupilot/AHRS AP_AHRS (two_cores): 0 of 24001 lines differ (238614 tokens equal only as NaN vs NaN with different bits)
```

(about 5.5 minutes with the translation and the Lean build of `AHRS_lib`; 2 without, `CPP2LEAN_NO_TRANSLATE=1`. The NaN tokens are the faulty core's
states after the IMU fault: C++ and Lean give NaNs with different sign bits, the existing NaN rule.) Sensitivity
(`CPP2LEAN_MUTATE`, applied to the translation before it is built): DCM's integrator gain `_ki` 0.0087f one ulp up
makes 23,919 of 24,001 lines differ in each run (from the first DCM steps on); the AP_Notify flags read through the other
estimates' arm of the tag 9,315 in each; the DCM fallback inverted (EKF3 active only while its filter faults are set)
23,198 in each (every line from the switch to EKF3 at 2.0 s on).

### Speed (`python3 ardupilot/ahrs_difftest.py --bench`)

Time per `AP_AHRS::update(true)` measured inside each driver (Lean: `IO.monoNanosNow` around the call, its result
forced; C++: `steady_clock`, `-O2`; the setters of a line run before, untimed), the difftest's lines, Apple M-series,
one thread. "EKF3 only" is NavEKF3::UpdateFilter alone in "Phase 3: AP_AHRS, and speed" (after `--array-offsets`,
`--swap-out`), the same scenario:

| run | calls | Lean mean | median | p99 | C++ mean | ratio | EKF3 only: Lean mean, median, p99 |
|---|---|---|---|---|---|---|---|
| one core, all steps | 24,000 | 155 µs | 50 µs | 1.58 ms | 1.45 µs | 107 | 132 µs, 21 µs, 1.61 ms |
| one core, EKF3 prediction steps | 4,680 | 0.58 ms | 0.34 ms | 2.01 ms | 3.4 µs | 172 | 0.57 ms, 0.32 ms, 2.04 ms |
| one core, the steps in between | 19,320 | 51 µs | 48 µs | 75 µs | 0.98 µs | 53 | 23 µs, 20 µs, 49 µs |
| one core, DCM active (before EKF3 starts) | 802 | 25 µs | 29 µs | 49 µs | 0.78 µs | 32 | |
| two cores, all steps | 24,000 | 325 µs | 77 µs | 3.25 ms | 2.2 µs | 148 | 272 µs, 47 µs, 3.27 ms |
| two cores, EKF3 prediction steps | 4,680 | 1.34 ms | 0.69 ms | 11.7 ms | 5.8 µs | 234 | 1.16 ms, 0.68 ms, 4.07 ms |
| two cores, the steps in between | 19,320 | 79 µs | 74 µs | 125 µs | 1.34 µs | 59 | 49 µs, 45 µs, 96 µs |

AP_AHRS with DCM adds about 28 µs per step (one core) to EKF3's cost (its DCM backend updates every step, as in
C++; the AHRS's own selection, copies of the estimates and resets); one core averages 0.16 ms per 400 Hz step
against the 2.5 ms budget, its prediction steps 0.58 ms (p99 2.0 ms). The two-core run's prediction-step p99 (11.7
ms) comes from the faulty core after the IMU fault (55 s): its NaN arithmetic takes FloatLib's model fallback, as
the zero operands did ("Phase 3: AP_AHRS, and speed"); before the fault the two-core figures match EKF3's
(`python3 ardupilot/ahrs_difftest.py --bench`, about one minute without the translation).

### What integrating AP_AHRS into the combined estimator World needs

(Done: README.md "Phase 3: AP_AHRS in the estimator World, the full estimation replay".) - **One unity, one World**: `unity_sensors.cpp`'s front ends, stand-ins and scheduler with `unity_ahrs.cpp`'s AHRS,
  AP_DAL and NavEKF3, `AP_AHRS ahrs;` and the front-end objects at file scope; the options are the union
  (`--front-ends --ins-gps --param-ext` of the sensor World, `--member-pointers --ahrs-ext --member-objects` and
  the EKF3 options). `--param-ext` changes the parameter model of the whole translation (parameters are state):
  `--ahrs-ext`'s parameter pieces (AP_Vector3f as a Params value, `set_enable`, DCM's references to AP_AHRS's
  parameters as `w.ahrs'p.<param>`) are written for the `--ap-param` model and must be redone for it (under
  `--param-ext` the references bind state members, `w.ahrs._kp_yaw`, and `_trim` is already an AP_ParamV object).
- **The getters this stage reads as inputs become calls on World objects**: DCM's and AP_AHRS's reads of
  AP_InertialSensor, AP_GPS, Compass and AP_Baro (the list above), and AP_DAL's, are member functions of the
  sensor World's objects; `compass.read()` and `baro.get_climb_rate()` (non-const: inputs with call counts here)
  are translated calls; `compass.calculate_heading(m)` (a site input here) is Compass's own code;
  `AP::sitl()->loop_time_jitter_us` is the SITL::SIM stand-in's parameter (`--world-class SITL::SIM`); the source
  selection of EKF3 (`--boundary-call @ekf3_sources.boundary`) is the translated AP_NavEKF_Source. The
  self-reach cycle then crosses objects in both directions: AP_Baro's field elevation calls `ahrs.resetHeightDatum`
  and `get_origin` inside `barometer.update()` (REFERENCE.md, 14.485 s), NavEKF3 reads the front ends through
  AP_DAL inside `ahrs.update()`.
- **What stays boundary**: the vehicle (`AP::vehicle()` time flying, the armed flag through `hal.util`), the HAL's
  persistent data and AP_Notify (outputs), GCS text and messages (dropped), `AP::mission()` (an output),
  AP_AHRS_SIM (its `get_results` dropped: AHRS_EKF_TYPE 3).
- **The replay against `copter_ref --est`**: the boot calls in `Copter::init_ardupilot`'s order (`create_view` in
  allocate_motors, then `ahrs.init`, `set_vehicle_class(COPTER)`, `ins.init`, `ahrs.reset`), `ahrs.update(true)`
  as fast task 3 after `AP_InertialSensor::update` in each step, and the setters on REFERENCE.md's schedule
  (`set_home` at 14.41 s and at arming, `set_terrain_hgt_stable`, `resetHeightDatum` from the barometer); the
  keys to compare are the probe's `q rpy dcm vel pos loc gyro accef resets healthy initialised origin ekf fs`
  (this difftest's getters) and the cores' keys, plus the AHRS and DCM leaves, which the probe would have to print
  (it prints the getters only). Speed: AP_AHRS and DCM add about 28 µs per step to EKF3's 132 µs (one core).

## Phase 3: AP_AHRS in the estimator World, the full estimation replay (2026-11-12)

PORT-PLAN.md section 6, "Phase 3" (estimation), eighth stage: the two seventh-stage Worlds merged into one translation,
the estimator World of "Phase 3: the estimator World and the EKF3 replay" (sensor front ends, stand-ins, scheduler
stand-in, AP_DAL, NavEKF3 with AP_NavEKF_Source) and the AP_AHRS of "Phase 3: AP_AHRS translated" (AP_AHRS,
AP_AHRS_Backend, AP_AHRS_NavEKF3, AP_AHRS_DCM, AP_AHRS_View), with the parameters as state (`--param-ext`) throughout;
oracle (b) complete: the replay of both recorded flights drives only translated calls in the vehicle's order and
compares every key of the reference's `--est` trace that the World holds, per step, bit for bit. `Estimation_lib`
(and its World difftest) and `AHRS_lib` (and its difftest) stay as their stages left them; every golden is
byte-identical.

### The translation (`ardupilot/translate_estimator.sh` → `ardupilot/out/Estimator/Estimator_lib.lean`)

`ardupilot/unity_estimator.cpp` is `unity_estimation.cpp` with the five AP_AHRS sources added and `AP_AHRS ahrs;` in
place of `NavEKF3 EKF3;` (the EKF3 front end is AP_AHRS_NavEKF3's static member `EKF3`, `--member-objects`, the same
World field). The options are the union of `translate_estimation.sh`'s and `translate_ahrs.sh`'s (`--member-objects
--member-pointers --ahrs-ext` added); the entry points `ardupilot/estimator.use` are `estimation.use`'s and `ahrs.use`'s
plus `AP_Baro::get_baro_drift_offset` (the probe's `bgnd`). What changes against the two separate translations:

- **AP_AHRS is no longer boundary.** AP_DAL's reads of `AP::ahrs()` (home, vehicle class, fly forward, takeoff and
  touchdown expected, trim, configured EKF type, the body rotation: AP_DAL's inputs go from 13 in `Estimation_lib` to 5),
  AP_Baro's field elevation (`AP::ahrs().get_origin`, `resetHeightDatum`: the output event `resetHeightDatum` and the
  barometer's origin inputs are gone) and Compass's `get_location` are calls on the World's `ahrs`.
- **The front ends are no longer boundary for the AHRS.** DCM's and AP_AHRS's reads of AP_InertialSensor, AP_GPS,
  Compass and AP_Baro (inputs in `AHRS_lib`, with `compass.read()` and `get_climb_rate()` counted calls and
  `calculate_heading` a site input) are the translated member functions of `ins`, `gps`, `compass`, `barometer`;
  `AP::sitl()` is the World's SITL::SIM stand-in; the source selection is the translated AP_NavEKF_Source.
- **AP_AHRS's parameters are state** (`w.ahrs._kp_yaw._value`), set by its constructor from `var_info`; DCM's reference
  members `AP_Float &_kp_yaw` ... `AP_Int8 &_gps_minsats` are those members of `w.ahrs`.
- **What stays boundary**: the vehicle (`AP::vehicle()` time flying), the HAL's Util (armed flag, watchdog, persistent
  data read only after a watchdog reset, `available_memory`), `hal.opticalflow` (null), AP_Notify's flags and the HAL's
  persistent data (outputs), `AP::mission().write_home_to_storage()` (an output), AP_AHRS_SIM (its member a tag, its
  overriders boundary calls, `get_results` dropped: AHRS_EKF_TYPE 3), `random()` (SITL's loop jitter, 0),
  AP::wheelencoder(), AP_BattMonitor (the compass's current), SRV_Channels and RCOutput (per-motor compensation, off),
  GCS (`send_text`, `send_message` dropped), AP_Param's storage and its parameter-count cache (`AP_Param::invalidate_count`,
  reached through `set_enable`, dropped) and, as before, `AP_Param::add_default`. The World's inputs: 15 of AP_AHRS's
  (armed, watchdog and persistent data, the SIM backend's answers, the optical flow, `random`) with AP_AHRS_DCM's 5 as
  a sub-record, 5 of AP_DAL's (time flying, armed, memory, wheel encoder), the front ends' as in `Estimation_lib` less
  the barometer's origin and the compass's location (now the AHRS's).

Translator changes (each gated by the combination of options, so every earlier output is byte-identical):

| change | gated by | what |
|---|---|---|
| AP_Vector3f under `--param-ext` | `--ahrs-ext` without `--param-ext` only | `--ahrs-ext`'s parameter-value model of `AP_Vector3f` (a `Vector3f` in the object's Params) applies only without `--param-ext`; with it `_trim` is its AP_ParamV object, state, as every other parameter |
| reference members of a member object bound to the owner's members | `--member-objects --ahrs-ext --param-ext` | `AP_AHRS_DCM dcm{_kp_yaw, _kp, gps_gain, beta, _gps_use, _gps_minsats};` (AP_AHRS.h:1020): the in-class initializer's constructor binds DCM's `AP_Float &` ... members to data members of the World object `ahrs`, each the path `w.ahrs.<member>` (`member_object_refs`, the form `heap_member_refs` uses); without `--param-ext` they stay `--ahrs-ext`'s references to the owner's Params |
| a member object's constructor with non-const reference parameters | (any; no earlier translation has one) | the constructor returns the referenced objects after its state (`AP_AHRS_DCM(AP_Float &kp_yaw, ...)`): the in-class initializer destructures the result and stores each back (it emitted an ill-typed `s with dcm := AP_AHRS_DCM.init ...`) |
| accessors of another class's object that call its member functions | `--ahrs-ext` | `const Vector3f &mag = compass.get_field();` (AP_AHRS_DCM.cpp:527): `get_field()` returns `_get_state(Priority(i)).field`, whose index `_get_state_id(priority)` is a member call on the compass; the inlining of reference accessors translated that call in DCM's context (a rejection); such an accessor is no longer inlined, and the local reference is the existing live reference to a World object's getter (each use calls `Compass.get_field_void w.compass` on the World as it is then) |

| translation | Lean lines | defs | ArduPilot lines covered (distinct `file:a-b` extents of the translated functions' doc comments) |
|---|---|---|---|
| `Estimator_lib` | 27,037 | 1,285 | 21,761 in 1,175 functions: AP_NavEKF3 9,637, AP_AHRS 3,009, AP_InertialSensor 1,738, AP_Math 1,221, AP_NavEKF 1,084, AP_GPS 1,079, AP_Compass 1,002, AP_DAL 875, AP_Baro 749, AP_Common 305, Filter 209, AP_Declination 173, AP_Param 87, AP_RTC 78, AP_HAL 43, AP_AccelCal 7; the stand-ins and the scheduler 465 |
| (by the same count) `Estimation_lib`, `AHRS_lib` | 22,525, 19,278 | 1,060, 829 | 18,411 in 978 functions, 15,740 in 750 |

It translates in about 70 s, elaborates without warnings in about 60 s (`lake build Estimator_lib`, one thread) and its
C compiles in about 2.5 minutes. Golden `tests/golden/ardupilot/Estimator_lib.lean` (`tests/run_tests.sh` section 3).

### The parameters and the probe

`reference/hal/est_probe.cpp`'s `# params` now also has AP_AHRS's 14 `var_info` entries (16 values: `ahrs.gps_gain` ...
`ahrs._origin_alt`, `_trim` by component): 277 parameters, every one the World holds. Each line ends with a new key
`cin=<throttle>,<voltage>`: the vehicle's arguments of `Compass::set_throttle` and `set_voltage` (task 13,
`motors->get_throttle()` and `battery.voltage()`), which the seventh stage took from `comp=`, the compass's state
after them (`set_voltage` low-passes its argument: the voltage was the filtered value's input, a difference invisible
there because the per-motor compensation is off, and visible now that `comp=` is compared). The reference rebuilt
(`python3 reference/build.py`, one unit) reproduces both flights' `outputs.txt` byte for byte with and without `--est`,
and the regenerated traces have every earlier key equal (`reference/tools/est_compare.py sim/out/F/est.txt
build/est/F.txt --keys-of-a`, the new option that compares only the older trace's keys: 36,013 steps, 8,909,177
values, all equal, both flights). The recorded `sim/out/*/est.txt` are the regenerated traces.

### The replay (`ardupilot/estimation_replay.py FLIGHT`, `lean/EstimationReplay.lean`)

The harness now only sequences translated calls and sets boundary inputs; it computes no estimator value. In the
vehicle's order (ArduCopter/system.cpp, Copter.cpp, commands.cpp, AP_Arming_Copter.cpp):

| command | the vehicle's call | where (from the trace) |
|---|---|---|
| `BI`, `AV` | `barometer.init()`; `ahrs.create_view(ROTATION_NONE)` (allocate_motors) | boot, the step with the barometer's event |
| `GI`, `CI`, `BC` | `gps.init()`, `compass.init()`, `barometer.calibrate()` | boot (as the sensor replay) |
| `AI`, `II`, `AR` | Copter::startup_INS_ground: `ahrs.init()`, `ahrs.set_vehicle_class(COPTER)`, `ins.init(400)`, `ahrs.reset()` | boot, the step with the IMU's event |
| `WS`, `IU` | `ins.wait_for_sample()`, `ins.update()` (fast task 0) | every main loop |
| `AU` | `ahrs.update(true)` (fast task 3, read_AHRS): DCM, EKF3 through AP_DAL and the front ends, the view | every main loop |
| `HE` | Copter::update_home_from_EKF (fast task 7): while `!ahrs.home_is_set()`, set_home_to_current_location: `ahrs.get_location`, `ahrs.get_origin`, `ahrs.set_home` (in flight: the altitude from the origin) | every main loop |
| `TH` | `ahrs.set_terrain_hgt_stable(b)` (task 11; b the vehicle's decision, `thgt=` after the call) | every throttle_loop |
| `GU` | `gps.update()` (task 12) | at its rate |
| `CT`, `CV`, `CR` | `compass.set_throttle`, `set_voltage` (arguments from `cin=`), `compass.read()` (task 13) | at its rate |
| `BU` | `barometer.update()` (task 16), whose field elevation calls the translated `ahrs.resetHeightDatum()` and `get_origin` | at its rate |
| `HA` | AP_Arming_Copter::arm's home handling (task 28): `ahrs.resetHeightDatum()` without a home, else set_home_to_current_location unless locked | the step that arms |

Boundary inputs: the HAL's armed flag (every reader: AP_AHRS, DCM, AP_DAL, the IMU stand-in, AP_RTC; the barometer's at
task 16 from the step's own `armed=`), AP_Vehicle's time flying (`millis() - _last_flying_ms` while `likely_flying`,
from the previous step's `flying=`), 512 KiB free memory, no wheel encoder, no watchdog reset, the GPS port and type,
the stored IMU ids (as the sensor replay), the input records, and the parameters from `# params`. Per line the harness
prints the probe's AP_AHRS keys through the translated getters (`q rpy dcm vel pos loc gyro accef resets healthy
initialised origin ekf fs`, with the probe's initial out-parameters, `Quaternion q;` = (1, 0, 0, 0)), the EKF3 keys,
the front-end keys, and the vehicle-side keys the World holds (`tkd thgt home cfg comp bgnd`: AP_AHRS's takeoff and
touchdown flags, terrain state, home, class, fly forward, configured EKF type, source set and trim; the compass's
throttle and filtered voltage; the barometer's ground pressures and drift offset); the script compares every value.

```
$ ardupilot/estimation_replay.py sim/out/lockstep-flight
estimation replay lockstep-flight: 36013 lines (boot init through 35098 main loops); steps compared: 35122 (891 inside barometer.calibrate and ins.init not compared); values compared: 8439007, equal: 8439007, different: 0; 0 steps differ
  by group: AHRS 1756100 values, 0 different; EKF3 2082728 values, 0 different; front ends 3792376 values, 0 different; vehicle side 807803 values, 0 different
$ ardupilot/estimation_replay.py sim/out/lockstep-flight-noisy
estimation replay lockstep-flight-noisy: 36013 lines (boot init through 35098 main loops); steps compared: 35122 (891 inside barometer.calibrate and ins.init not compared); values compared: 8439007, equal: 8439007, different: 0; 0 steps differ
  by group: AHRS 1756100 values, 0 different; EKF3 2082728 values, 0 different; front ends 3792376 values, 0 different; vehicle side 807803 values, 0 different
```

Per key (values compared, both flights the same; 0 different everywhere): AP_AHRS `q` 175,610, `rpy` 105,366, `dcm`
316,098, `vel` 140,488, `pos` 140,488, `loc` 175,610, `gyro` 105,366, `accef` 105,366, `resets` 140,488, `healthy`
35,122, `initialised` 35,122, `origin` 175,610, `ekf` 35,122, `fs` 70,244; EKF3 `primary` 35,122, `ncores` 35,122, `gbias`
104,094, `abias` 104,094, `var` 346,980, `c<k>.x` 832,752, `c<k>.fs` 69,396, `c<k>.P` 34,698, `c<k>.out` 34,698, `c<k>.imu`
34,698, `c<k>.var` 277,584, `c<k>.gsf` 173,490; front ends `baro` 245,836, `mag` 351,013, `ins` 351,220, `imu0` 877,475,
`gps` 70,244, `gps0` 913,172, `gps1` 913,172, `ev` 35,122, `evx` 35,122; vehicle side `home` 210,732, `cfg` 245,854,
`tkd` 140,488, `thgt` 35,122, `comp` 70,244, `bgnd` 105,363. Every step from line 915 (2.2875 s, the first main loop)
on is compared; the 891 lines consumed inside `barometer.calibrate` and `ins.init` are not (the World consumes them in
the same calls, and the probe's line is written mid-call). DCM is the active backend for the first 802 main loops
(EKF3 starts at line 1,316, 3.29 s, and is used once its filter is initialised), EKF3 from line 1,717 (4.29 s) on; home is set by update_home_from_EKF at 14.41 s and again at arming (41.86 s, unlocked);
the barometer's field elevation resets EKF3's height datum through the AHRS at 14.485 s. About 13 s per flight.

Sensitivity (`ESTIMATION_REPLAY_DROP=C` leaves out the harness's command C; deterministic flight):

| mutation | steps differing | first difference |
|---|---|---|
| without `HE` (no update_home_from_EKF) | 30,249 (AHRS 400,440 values, EKF3 839,050, vehicle side 120,996) | `home` at line 5,765 (14.41 s); at arming the AHRS then resets the height datum (no home): `c<k>.x`, `pos`, `vel` from line 16,742 |
| without `HA` (arming's home update) | 19,272 | `home` at line 16,742 (41.855 s, altitude 58,400 vs 58,401 cm) |
| without `AR` (`ahrs.reset()` at boot) | 802 (AHRS keys only) | `q`, `rpy`, `dcm`, `accef` at line 915: DCM's attitude from the accelerometers is missing until EKF3 takes over |
| without `AI` (`ahrs.init`, `set_vehicle_class`) | 35,099 | `cfg` (class 0 instead of 2) at line 915 |
| without `TH` | 35,092 | `thgt` (3 instead of 0) at line 922 (2.305 s) |
| translation: DCM's `renorm` numerator `1.0f` one ulp up (`lean/Estimator_lib.lean`) | 802 (13,098 AHRS values; EKF3 and the rest equal) | `q`, `rpy`, `dcm`, `accef` at line 915, in the last bit (`dcm` a.x 3f800000 vs 3f800001), through line 1,716: every step DCM is active |
| translation: DCM's integrator gain `_ki` one ulp up | 0 | none: DCM's integrator feeds `_omega_I` only after 5 s of accumulation (AP_AHRS_DCM.cpp:1103-1118), and DCM is the active backend for the first 2.0 s of main loops only; DCM's own state is not among the probe's keys |

The last row is the replay's limit for DCM: once EKF3 is active, DCM's state reaches the probe's keys only through a
fallback (none in these flights); `python3 difftest.py ardupilot/AHRS` compares every DCM leaf, the fallback included.

### Speed (`ardupilot/estimation_replay.py FLIGHT --bench K`)

As `sim/BENCH.md` measures: every command parsed first; the parameters and the input records (the HAL's input) set and
fed outside the timed region; `IO.monoNanosNow` around each line's calls and around its `AU`; one process per launch,
6 launches, the first discarded, each step's median over the launches; lake's release build; Apple M4, one thread. The
deterministic flight:

| part | steps | mean µs | median µs | p99 µs | max µs | total |
|---|---|---|---|---|---|---|
| all steps | 36,013 | 167.3 | 83.5 | 1,926 | 7,352 | 6.03 s |
| boot init (lines consumed inside `setup()`'s delays; the init calls) | 914 | 3.3 | 0.2 | 0.3 | 2,488 | 3 ms |
| main loop | 35,099 | 171.6 | 83.8 | 2,016 | 7,352 | 6.02 s |
| main loop, `ahrs.update(true)` alone (DCM, EKF3 through AP_DAL, the view) | 35,099 | 158.8 | 71.5 | 2,003 | 7,339 | 5.57 s |
| main loop, the rest (front ends, scheduler and sensor stand-ins, setters) | 35,099 | 12.8 | 12.6 | 19.1 | 54 | 0.45 s |

(launch means 166.1 to 169.6 µs.) Against the reference (REFERENCE.md): AHRS + EKF3 0.69 µs per step in C++, the Lean
`ahrs.update` 159 µs (230 times); the whole reference vehicle 3.4 µs per step. AP_AHRS, DCM and the view add about 32
µs per step to the seventh stage's EKF3 alone (127 µs). Against the 2,500 µs budget of a 400 Hz step: 6.7% on average,
81% at p99; 3 of 36,013 steps exceed it (7.4 ms at 47.825 s, 3.3 ms at 6.125 s, 2.5 ms at 47.737 s), and the 4,327
main-loop steps whose `ahrs.update` takes over 200 µs (EKF3's prediction steps) average 775 µs. What dominates (macOS
`sample` of a bench launch, 1 ms interval, the 3,837 samples inside the timed calls): by code, `AP_AHRS::update` 92%
(AP_AHRS_NavEKF3::update, i.e. NavEKF3::UpdateFilter, 72%; AP_AHRS_NavEKF3::get_results 11%; DCM 6%; the view 1%),
the scheduler stand-in's delay with the sensor stand-ins 7%, the harness 0%; by kind, FloatLib 76% (its `Binary64`
model fallback 46%, with `mpz`/`Nat` work and the allocation and freeing under it), allocation, freeing and copies
outside FloatLib 10%, the translated code itself 10%. The lever is still FloatLib's fallback path (README "Phase 3:
the estimator World and the EKF3 replay"), not the translation.

### What the harness still does by hand, and why

- **The vehicle's code** around the AHRS calls: the order of the boot calls, the scheduler's choice of tasks per step
  (`tasks=`, the init events `ev=`/`evx=`), Copter::update_home_from_EKF's and AP_Arming_Copter::arm's tests
  (`home_is_set`, `home_is_locked`, `motors->armed()` as the armed flag) and set_home_to_current_location's
  `copy_alt_from` in flight, the terrain decision (`is_taking_off() || is_landing()`, taken from `thgt=`), the compass
  setters' arguments (`cin=`). ArduCopter is Phase 5; the harness makes its calls with the values it computed.
- **AP_Vehicle and the HAL**: the armed flag, the time flying (`get_time_flying_ms`, an inline function of the
  vehicle's `likely_flying` and `_last_flying_ms`), the memory, the watchdog: boundary inputs.
- **AP_Param's loading** from the storage image: the `# params` dump (`load_all` is not translated).
- **Not called**: `AP_InertialSensor::periodic` (task 30: the batch sampler, compiled in but idle), as the seventh stage.

### Tests

`tests/run_tests.sh` section 3 translates `ardupilot/translate_estimator.sh` against its golden (with the reference
build) and, new, `translate_navekf_source.sh` against `tests/golden/ardupilot/NavEKF_Source_lib.lean` with the difftest
target `ardupilot/NavEKF_Source`; section 7 (new) builds the replay (`lake build estimation_replay`, warnings fail it)
and replays both flights whole (needs `build/reference/copter_ref`; about 15 s per flight after the build). The
translation has no random-call World difftest of its own: its parts have theirs (`ardupilot/Estimation` for the front
ends with AP_DAL and NavEKF3, `ardupilot/AHRS` for AP_AHRS with every DCM leaf), and the replay compares the whole
against the reference vehicle.

## Phase 4 summary (parameters, missions, MAVLink, 2026-11-12)

PORT-PLAN.md section 6, "Phase 4". Four translations, each in its own section below, plus a support change:

| translation (golden in `tests/golden/ardupilot/`) | Lean lines | what | check |
|---|---|---|---|
| `Mavlink_lib` (`ardupilot/translate_mavlink.sh`, `--mavlink`) | 25,248 | the generated MAVLink C of the reference build (fork e03dad40, dialect `all`): CRC, message table, finalize/send, the parser, 48 messages with pack/encode/send/decode and every getter (7,861 extent lines of 51 generated headers) | `python3 difftest.py bitfields ardupilot/Mavlink`: 0 of 32,545 lines; 362 layouts equal to clang's |
| `Mission_lib` (`ardupilot/translate_mission.sh`, `--mission`) | 3,362 | AP_Mission storage, conversions MAVLink <-> `Mission_Command`, jump tracking (1,908 extent lines) | `python3 difftest.py ardupilot/Mission`: 0 of 4,328 lines; `ardupilot/mission_roundtrip.py`: 6 of 6 items and the mission areas equal |
| `AP_Param_lib` (`ardupilot/translate_param.sh`, `--param-memory`) | 4,285 | AP_Param over one byte memory: boot, `load_all`, enumeration, names, lookup, set, `save_sync` (1,825 extent lines) | `copter_ref --param-dump` against `param_dump`: identical dumps (609 parameters on both recorded images, 590 on blank storage); `ardupilot/param_difftest.py --cases 66`: 0 of 43,566 lines |
| `GCS_lib` (`ardupilot/gcs/translate_gcs.sh`, `--param-memory` with `dynamic`) | 13,402 | GCS_MAVLink on the same memory with AP_Param, AP_Mission and the MAVLink helpers: receive path, routing, common handlers, parameter and mission protocols, `update_send` (453 functions) | `ardupilot/gcs/gcs_replay.py`: flight 7,145 of 7,304 frames equal, QGroundControl session 8,903 of 9,707 (below) |

`support/CFloat.lean`: integer-to-float conversions on the bits for every magnitude (`@[csimp]`, proved), and float to
8-/16-bit integers as the reference target computes them ("Phase 4: integer to float for every magnitude").

Acceptance (the brief's items):

1. Per-class difftests at 0 differing lines with mutation checks: MAVLink (five mutations, each detected), AP_Mission (two),
   AP_Param (one: `group_id`'s `63U`); the GCS path has no per-class difftest: the byte replay with a mutation of the
   translated parser's CRC (7,145 to 136 equal frames in the flight, 8,903 to 147 in the QGroundControl session) stands in.
2. Parameter loading: the translated boot sequence to `AP_Param::load_all` gives the reference's dump (index, name, type,
   value bits, count) exactly on `sim/out/lockstep-flight/storage_in.bin`, `sim/out/lockstep-qgc/harness/storage_in.bin` and
   blank storage; `LEAN_NUM_THREADS=1 python3 ardupilot/estimation_replay.py sim/out/lockstep-flight` takes its 277
   parameters from it (277 of 277 equal to the probe's) and compares 8,439,007 values, 0 different (both flights).
3. MAVLink byte replay (`python3 ardupilot/gcs/gcs_replay.py SESSION [EST]`, README "Phase 4: GCS_MAVLink"): frames whose
   content is vehicle-side are taken from the recording where the translated scheduler sends them (their sequence numbers
   checked); the rest is produced by the translation. Flight: 36,013 steps, 35,957 with every frame equal; 7,304 recorded
   frames, 7,145 equal (670 translated, 6,475 boundary), 149 different, 10 missing or extra; first difference at step 3,813
   (EK3_IMU_MASK in the parameter download). QGroundControl session: 55,515 steps, 55,337 equal; 9,707 frames, 8,903 equal
   (16 translated, 8,887 boundary), 802 different; first difference at step 5,765 (the vehicle's HOME_POSITION and
   GPS_GLOBAL_ORIGIN pushes, Phase 5), after which the sequence numbers shift.
4. Mission round trip: through the value translation (`ardupilot/mission_roundtrip.py`): the 6 uploaded items stored by
   the translated AP_Mission, the mission areas (9,758 bytes) equal to the reference's and the 6 downloaded items equal; through
   the translated protocol in the GCS replay: the 18 mission and command frames equal in content, the mission areas 1 byte
   different (the home record, which the vehicle writes through `AP_AHRS::set_home`); the parameter area differs in 20 bytes
   (the AP_Param save queue, with MIS_TOTAL, is not translated).
5. Speed per 400 Hz step: GCS work 7.0 to 7.7 µs (QGroundControl session, flight; one run each, release build) and 18 µs
   with the boot's parameter traffic, against 0.38 µs in C++ (`GCS::update_receive` 0.13 + `update_send` 0.25); `load_all`
   1.1 to 1.8 ms (C++ 2 µs) once at boot; one enumeration of 609 parameters 41 to 47 ms (C++ 130 to 180 µs).

The Phase 5 boundary of this phase: `GCS_MAVLINK_Copter` and `GCS_Copter` (their six forwarding overriders are translated
with `copter` as boundary; the rest is boundary), the content of HEARTBEAT, SYS_STATUS, SYSTEM_TIME, RAW_IMU,
SCALED_PRESSURE, ATTITUDE, LOCAL_POSITION_NED, GLOBAL_POSITION_INT, SERVO_OUTPUT_RAW, MISSION_CURRENT, GPS_GLOBAL_ORIGIN,
NAV_CONTROLLER_OUTPUT, RC_CHANNELS, VFR_HUD, POWER_STATUS, BATTERY_STATUS, AUTOPILOT_VERSION, MEMINFO, AHRS, AHRS2, WIND,
EKF_STATUS_REPORT, VIBRATION, HOME_POSITION, EXTENDED_SYS_STATE, GPS_RAW_INT, AVAILABLE_MODES and the STATUSTEXT texts; the
vehicle's answers to DO_SET_MODE, arming and takeoff; the vehicle's HOME/ORIGIN pushes, `write_home_to_storage`; the
objects `Copter::allocate_motors` creates (their parameters are placed by the harness and loaded by the translated
`load_object_from_eeprom`); parameter values changed by vehicle and estimator code (snapshots from the reference probe);
AP_Mission's execution state machine. Translated and on this side: PARAM_VALUE, COMMAND_ACK (common commands), TIMESYNC,
MISSION_COUNT/ITEM_INT/REQUEST_INT/ACK, AVAILABLE_MODES_MONITOR, the scheduling of every stream.

## Phase 4: the MAVLink C library (2026-11-12)

PORT-PLAN.md section 6, "Phase 4", the MAVLink part (4.7, D14): the generated C of the reference build translated, not
a hand-written codec. The library is ArduPilot's MAVLink fork e03dad40, dialect `all`, as the reference build generates
it (`build/reference/ap/build/sitl/libraries/GCS_MAVLink/include/mavlink/v2.0/`) and `GCS_MAVLink.h` configures it
(`MAVLINK_SEPARATE_HELPERS`, `MAVLINK_USE_CONVENIENCE_FUNCTIONS`, `MAVLINK_SEND_UART_BYTES` = `comm_send_buffer`,
`MAVLINK_GET_CHANNEL_BUFFER/STATUS`, 16 channels, `MAVLINK_ALIGNED_FIELDS` 1, little endian), with the flags of
`GCS_MAVLink.cpp`'s unit (`ardupilot/ref_flags.py`). Every new construct is behind `--mavlink` (and `--null-member`);
every existing translation is byte-identical (sections 1-3 of `tests/run_tests.sh`: every golden unchanged).

### New options

| option | meaning |
|---|---|
| `--mavlink` | the MAVLink C library's constructs (below): `extern "C"` blocks, mutable file-scope variables as state, pointers to structs, an `Option` for a returned `const T *`, packed structs and bit-fields of any width (layouts with bit-fields, bytes in both directions, writes masked), an integer array member used only as bytes, `memcpy`/`memset` of whole structs, static constant tables of a function, uninitialized local arrays; the layouts in the signatures for `ardupilot/check_layouts.py` |
| `--null-member C::m` | (with `--mavlink`) a pointer data member that is always null: not state, and what it decides is folded before translation (below) |

`ardupilot/check_unity.py` has two new arguments for this unity: `--home=FILE`, a translation unit whose headers are
compared without the unity including it (`GCS_MAVLink.cpp`, which needs `GCS.h`), and `--normalize` (the generated
headers include each other as `../common/./mavlink_msg_x.h`). The signatures JSON lists the classes in source order
(before: in the order the contexts were created, which could differ from run to run; the Lean output is unchanged).

### The constructs (`--mavlink`)

- **`extern "C"` blocks** (the dialect headers, `checksum.h`): their declarations are translated as those at file scope.
- **File-scope state.** A mutable file-scope variable of the translated files (`mavlink_system`, and the unity's
  channel buffers, status array and UART queue) is a hidden reference parameter of every function that reaches it
  (directly or through a callee: `--hal-storage`'s mechanism, one parameter per variable), returned when written; its
  initial value (initializer, else zero) is the constant `<name>'init`. An `extern` declaration (`GCS_MAVLink.h`'s
  `extern mavlink_system_t mavlink_system;`) names the definition. In the signatures the parameter is `hidden` (kind
  `global`); the difftest passes `<name>'init`.
- **Accessors of elements.** A function `T *f(p) { return &g[p]; }` (or `return &g;`) of a file-scope variable g
  (`mavlink_get_channel_buffer/status`) is not translated; a call is the element `g[p]` (the index evaluated once, into
  a temporary), an lvalue.
- **Pointers to structs.** A parameter `T *p` / `const T *p` (T a plain struct: `mavlink_message_t *msg`,
  `mavlink_status_t *status`, `const mavlink_param_set_t *param_set`) is the object, by reference (returned if not
  `const`); `p->f`, `*p`, passing `p` on, `p` as a byte pointer (the object's bytes, written back) are paths of it. A
  local `T *q = &x;` / `= f(...)` (an accessor) / `= p`, never reassigned, is another name for the object. A null
  test of such a pointer is constant (`p != NULL` true): the callers pass objects; a call passing a null pointer is
  rejected. `(&msg)->len` is `msg.len`.
- **`const T *` results.** A function returning `const T *` whose returns are the null pointer or `&x` returns
  `Option T` (`mavlink_get_msg_entry`: `none`, `some table[low]`); a local initialized by it is an `Option`, its null
  tests `isNone`/`isSome`, `e->f` reads `(e.getD default).f` (only after a test: a null dereference is undefined).
- **A static constant table of a function** (`static const mavlink_msg_entry_t mavlink_message_crcs[] =
  MAVLINK_MESSAGE_CRCS;`, 400 entries) is a constant of the file, `mavlink_get_msg_entry'mavlink_message_crcs`, built
  once (not per call).
- **Bytes.** An integer array member used only as `(char *)&x.f[0]` (every use in the unit: `_MAV_PAYLOAD(msg)`, `uint64_t
  payload64[33]`) is stored as its 264 bytes, so `_MAV_PAYLOAD(msg)` is (the bytes, offset 0) and `mavlink_ck_a(msg) =
  ...` a byte write. A struct pointer or an array of wider numbers passed as a byte pointer (`mavlink_msg_decode_target(msg,
  param_set, ...)`'s `void *payload`, `mav_array_memcpy(packet.voltages, voltages, ...)`, `memcpy(value,
  &_MAV_PAYLOAD(msg)[ofs], n)` into a `uint16_t *`) is a temporary of its bytes, written back if the callee writes them.
  A `void *` parameter used only by `memcpy`/`memset`/`memcmp` and null tests is bytes; a pointer parameter into an array
  tested for null (`mav_array_memcpy`'s `src == NULL`) is never null (the callers pass arrays). `memcpy(p, q,
  sizeof(T))` between two struct pointers of type T is an assignment; `memset(&x, 0, sizeof(x))` of a struct is its zero
  value (also for `mavlink_status_t`, whose null members' zero is the null pointer). A member array of bytes is written
  and read whole (`CString.write`, `CString.slice`) in an object representation.
- **Layouts with bit-fields** (`mav_record_layout`): the rules of the reference targets (AAPCS64; x86-64 agrees): a
  bit-field of declared type T and width w goes at the next bit, unless the struct is not packed and it would cross a
  boundary of an aligned unit of T (then at the next unit); bits from the least significant; a non-bit-field member at
  the next byte its alignment allows; `__attribute__((packed))` alignment 1. Written to bytes bit by bit (each byte the
  field spans ORed), read back by shift and mask; a write to an unsigned bit-field of w bits stores the value modulo 2^w
  (`uint32_t msgid:24`). A record with members outside the model (a function pointer, an unnamed union, a
  `--null-member`) has no object representation (rejected).
- **The layout cross-check.** The signatures list every record layout the translation computed (`layouts`: size,
  alignment, each member's byte offset and size or bit offset and width); `ardupilot/check_layouts.py SIGNATURES -- FLAGS`
  dumps clang's record layouts (`-Xclang -fdump-record-layouts`) for the unity plus a `sizeof` of each record and
  compares them; `translate_mavlink.sh` runs it and fails on a difference: `check_layouts: 362 records, 2825 members: all
  equal to clang's` (the message structs, packed and not, `mavlink_message_t` with its 24-bit `msgid` at bit 96, the
  table entry, `mavlink_system_t`, ...).
- **Late initialization.** `uint8_t *ck; ... ck = buf + header_len + length;` (mavlink_msg_to_send_buffer): a local
  pointer whose first use in its block is one assignment, assigned nowhere else, is declared there (`merge_late_inits`).
- Also: `for` loops' uninitialized local arrays start at zero (C reads them only after writing); a scalar pointer
  parameter passed on to another (`crc_accumulate(*p++, crcAccum)`) is the scalar; `set_option maxRecDepth 20000`
  (FILE_TRANSFER_PROTOCOL's 254-byte struct).

**Null members** (`--null-member __mavlink_status::signing,__mavlink_status::signing_streams`). Signing is not compiled
out of the library: `MAVLINK_NO_SIGN_PACKET` is not defined, and `mavlink_sign_packet`, `mavlink_signature_check` and
the SHA-256 code are compiled into GCS_MAVLink.cpp; `AP_MAVLINK_SIGNING_ENABLED 0` removes GCS_Signing.cpp, the only code
that sets `status->signing`, so the pointers are always null. `NullFold` (a pass on clang's AST before translation, as
`--gotos`' rewrite) reads them as the null pointer and folds: `p` as a condition false, `!c`, `&&`, `||`, `?:` with a
constant operand (a dropped operand must have no effects), a local initialized with a constant and assigned nowhere
else or only that constant (`sig_ok`), a call `f(..., null, ...)` of a function whose first statement is `if (q ==
NULL) return <literal>;` for that parameter (`mavlink_signature_check`), and `if` with a constant condition, until
nothing changes. What it leaves is translated as usual; a read through the null pointer left in reachable code is
rejected, an assignment to the member is rejected. So `signing` is `false` in the finalizers (no signature,
`signature_len` 0), the signed-frame states of the parser keep their framing (13 signature bytes, then
`MAVLINK_FRAMING_OK` or `BAD_CRC`), and the signing code is not translated.

### The translation (`ardupilot/translate_mavlink.sh` → `ardupilot/out/Mavlink/Mavlink_lib.lean`)

`ardupilot/gen_unity_mavlink.py` writes `ardupilot/unity_mavlink.cpp` (and `unity_mavlink.h`): `GCS_MAVLink.h` and
`mavlink_helpers.h` included as `GCS_MAVLink.cpp` includes them (checked: `check_unity.py` compares GCS_MAVLink.h,
mavlink_helpers.h, protocol.h, mavlink_types.h, checksum.h, all.h and the 48 message headers with GCS_MAVLink.cpp's
own unit), then the stand-ins for what `GCS_MAVLink.cpp` and `GCS_MAVLINK` provide around the library (no protocol
code): the channel buffers and status (`mav_chan_buffer[16]`, `mav_chan_status[16]`, returned by
`mavlink_get_channel_buffer/status` as GCS_MAVLINK's `_channel_buffer`/`_channel_status` of the link on the channel
are), `mavlink_system = {7,1}` (GCS_MAVLink.cpp:83), and `comm_send_buffer` appending to a byte queue (`mav_uart`,
`mav_uart_len`; the reference's writes `mavlink_comm_port[chan]`). `comm_send_lock`/`comm_send_unlock` (the channel
semaphore and the txspace check, GCS_MAVLink.cpp:192-215) are `--drop`ped (one thread; the queue has room). Then the
test functions (below). The headers are a `--lib-dir`: what the tests reach is translated.

Translated (25,248 Lean lines with the test functions; 689 library functions over 7,861 extent lines of 51 generated headers):
the helpers (41 functions, 887 extent lines of mavlink_helpers.h, protocol.h, checksum.h): `crc_accumulate`,
`crc_init`, `crc_calculate`, `crc_accumulate_buffer`, `mavlink_get_msg_entry` with the 400-entry table and its binary
search, `_mav_trim_payload`, `_mav_header_pack` (SYSID32, TARGET32 headers), `mavlink_header_to_send_buffer`,
`mavlink_msg_to_send_buffer`, `_mav_parse_error`, `mavlink_finalize_message_buffer_target`, `_chan_target`, `_chan`,
`_target`, `mavlink_finalize_message`, `_mav_finalize_message_chan_send_target`, `_mav_finalize_message_chan_send`,
`_mavlink_send_uart`, `mavlink_start_checksum`, `mavlink_update_checksum`, `mavlink_frame_char_buffer` (the 354-line
parser), `mavlink_frame_char`, `mavlink_parse_char`, `mavlink_reset_channel_status`, `mavlink_set_proto_version`,
`mavlink_get_proto_version`, `mav_array_memcpy`, `mavlink_msg_target_field`, `mavlink_msg_decode_target`, the
`_MAV_RETURN_*` getters (scalars, `char`/`uint8_t`/`uint16_t`/`float` arrays); and for each of 48 messages (HEARTBEAT,
PARAM_VALUE, PARAM_SET, PARAM_REQUEST_READ, PARAM_REQUEST_LIST, MISSION_COUNT, MISSION_REQUEST_INT, MISSION_REQUEST,
MISSION_ITEM_INT, MISSION_ITEM, MISSION_ACK, MISSION_REQUEST_LIST, MISSION_CURRENT, MISSION_ITEM_REACHED,
MISSION_CLEAR_ALL, MISSION_SET_CURRENT, COMMAND_LONG, COMMAND_INT, COMMAND_ACK, STATUSTEXT, TIMESYNC, SYSTEM_TIME,
REQUEST_DATA_STREAM, AUTOPILOT_VERSION, FILE_TRANSFER_PROTOCOL, ATTITUDE, AHRS2, VFR_HUD, GLOBAL_POSITION_INT, AHRS,
EKF_STATUS_REPORT, VIBRATION, BATTERY_STATUS, WIND, LOCAL_POSITION_NED, RAW_IMU, SCALED_PRESSURE, SYS_STATUS,
POWER_STATUS, MEMINFO, NAV_CONTROLLER_OUTPUT, SERVO_OUTPUT_RAW, RC_CHANNELS, GPS_RAW_INT, EXTENDED_SYS_STATE,
HOME_POSITION, GPS_GLOBAL_ORIGIN, AVAILABLE_MODES) its `_pack`, `_pack_chan`, `_encode`, `_encode_chan`, `_send`,
`_send_struct`, `_decode` and every getter (322). The translation and the Lean elaboration take about 20 s each.

**The send path, for the GCS translation.** `_mav_finalize_message_chan_send_target (chan : mavlink_channel_t) (msgid :
UInt32) (packet : Array UInt8) (min_length length crc_extra : UInt8) (target_sysid : UInt32) (mav_chan_status : Array
__mavlink_status) (mavlink_system : __mavlink_system) (mav_uart : Array UInt8) (mav_uart_len : UInt16) : (Array
__mavlink_status) × (Array UInt8) × UInt16` (and `_mav_finalize_message_chan_send` without the target): the packet is the
bytes of the message struct (`(const char *)&packet`), the channel status array is threaded, `mavlink_system` read,
and the frame goes out through `_mavlink_send_uart` to `comm_send_buffer (chan : mavlink_channel_t) (buf : Array UInt8)
(len : UInt8) (mav_uart : Array UInt8) (mav_uart_len : UInt16) : (Array UInt8) × UInt16`, three calls per frame
(header, payload, checksum). Each `mavlink_msg_X_send` takes the fields and the same four hidden state parameters. The
parser: `mavlink_parse_char (chan c : UInt8) (r_message : __mavlink_message) (r_mavlink_status : __mavlink_status)
(mav_chan_buffer : Array __mavlink_message) (mav_chan_status : Array __mavlink_status) : __mavlink_message ×
__mavlink_status × (Array __mavlink_message) × (Array __mavlink_status) × UInt8`. In the GCS translation the state
becomes GCS_MAVLINK's (`_channel_buffer`, `_channel_status` per link) and `comm_send_buffer` GCS_MAVLink.cpp's own
(the UART a boundary): the accessors and `comm_send_buffer` are the stand-ins to replace; the library's functions do
not change.

### The difftest (`python3 difftest.py ardupilot/Mavlink`)

`ardupilot/Mavlink.json` drives the unity's test functions (config `free.only`, new in difftest.py: a regular
expression of the C++ names driven) on both sides; the C++ side is the unity compiled with the reference flags
(`ardupilot/mavlink_env.cpp`: `comm_send_lock/unlock` as no-ops). Each returns a 64-bit FNV-1a hash of everything it
observed; each test resets the state first (`mav_reset`: the C++ keeps file-scope state between calls).

- `pk_<m>(seed, mode)` (48): random fields (strings with zeros anywhere, NaN with payloads, infinities, -0,
  denormals, extremes; 8-bit and 32-bit system and target ids), `_pack`, `_pack_chan`, `_encode` or `_encode_chan`,
  MAVLink 1 or 2 out (the channel's flag; MAVLink 2 trims trailing zeros; MAVLink 1 drops extensions and rejects
  32-bit ids), then `mavlink_msg_to_send_buffer`: the results, every byte of the frame, every field of the message and
  the status;
- `sd_<m>(seed, mode)` (48): `_send` or `_send_struct` on a channel, with a random sequence number, `mavlink_system`
  (also wider than 8 bits) and protocol version: every byte written to the UART and the channel status;
- `dc_<m>(seed, len, flags)` (48): `_decode` (the zero extension of short payloads, TARGET32's target) and every
  getter on random payload bytes with a random length (short, exact, longer) and incompat flags: every byte of the
  decoded struct, every getter's value and array;
- `ps_stream(seed, nbytes, mode)`: `mavlink_parse_char` or `mavlink_frame_char` on a random stream of up to 700 bytes
  mixing valid frames of 14 messages (MAVLink 1 and 2, 8- and 32-bit ids, TARGET32), flipped bits, truncated frames,
  random incompat flags, unknown message ids (MAVLink 1 and 2), signed frames with a good and a bad CRC, garbage with
  start bytes: after every byte the result, the channel status, the returned status, the parse buffer's and the
  returned message's header; every byte of both messages when a frame ends and every 16 bytes;
- `crc_buf`, `msg_entry` (ids in and out of the table), `chan_ops` (reset, protocol version), `bench_parse`,
  `bench_pack` (the speed runs below, also compared).

### Results (seed 20261104)

```
ardupilot/Mavlink free functions: 32544 calls (30000 random, 2544 corner) over 150 functions
ardupilot/Mavlink free functions: 0 of 32545 lines differ (0 tokens equal only as NaN vs NaN with different bits)
bitfields: 0 of 48000 lines differ (0 lines equal only as NaN vs NaN with different bits)
check_layouts: 362 records, 2825 members: all equal to clang's
```

Sensitivity (`CPP2LEAN_MUTATE`, 2000 calls each, 4544 lines): one rotation of `crc_accumulate` changed (`<< 3` to `<< 2`): 2,625
lines differ; `_mav_trim_payload` trimming to two bytes instead of one: 40 (pk_/sd_ lines of messages whose payload
ends in zeros: the test makes a quarter of the fields zero for this); in one build, the parser's `current_rx_seq`
off by one, `mavlink_msg_decode_target`'s TARGET32 sentinel 255 to 254 and the send path's `current_tx_seq` step 1 to
2: 1,315 lines (`ps_` 238, `dc_` 41, `sd_` 1,036: each where only its mutation reaches); HEARTBEAT's `crc_extra` in `mavlink_get_msg_entry`'s table 50 to 51:
69 lines (the parser's CRC check, `msg_entry`; packing uses the header's constant, not the table); the packed
offset of `target_system` 4 to 5 in the three message structs that have it there: 98 lines (`pk_` 9, `sd_` 2, `ps_` 86).

The translation is deterministic (two runs, different `PYTHONHASHSEED`: the same Lean and signatures). Golden
`tests/golden/ardupilot/Mavlink_lib.lean`; `tests/run_tests.sh` section 3 translates it (with the layout check) and
the difftest target `ardupilot/Mavlink` runs in section 4. `examples/bitfields.cpp` (golden `tests/golden/BitFields.lean`,
`--mavlink`) has AP_Param's `Param_header` (four bit-fields over a `uint32_t`, not packed), a packed struct with a
24-bit field, a byte array and an array of `uint16_t`, and bit-fields that cross the units of their types, each
written and read through `memcpy` with bytes: 0 of 48,000 lines differ, and its three layouts equal clang's
(`check_layouts.py` on its signatures).

### Speed

The unity's `bench_parse` (a stream of 4000 bytes made first, then parsed by `mavlink_parse_char`, or not) and
`bench_pack` (200 ATTITUDE messages with random fields packed by `_pack_chan` and `mavlink_msg_to_send_buffer`, or
not), 100 calls each, through the difftest drivers (the C++ inputs repeated 50 times for resolution), the time per byte
or message the difference of the two runs:

| | C++ (`-O2`) | Lean |
|---|---|---|
| per parsed byte (`mavlink_parse_char`) | 4 ns | 0.23 µs |
| per packed message (ATTITUDE, `_pack_chan` + `mavlink_msg_to_send_buffer`) | 0.06 µs | 3 µs |

Each byte the parser takes passes the channel's 298-byte `mavlink_message_t` (its 264-byte payload array) into
`mavlink_frame_char_buffer` and back; a pointer argument to a slice (`buf + 1`) is a copy (`Array.extract`). A
telemetry downlink of 10 kB/s and the uplink of a ground station cost well under a millisecond of Lean per second.

### Not done, and limits

- Messages: the 48 above; the reduced vehicle sends and decodes more (PORT-PLAN 4.7: 58 sent, 40 decoded; a grep of
  the reference build's units finds 179 names, most compiled out). Each further message is a line of
  `gen_unity_mavlink.py`'s MESSAGES (nothing in the translator is message-specific).
- Not reached by the tests, so not translated yet: `_mavlink_resend_uart`, `mavlink_msg_get_send_buffer_length`,
  `mavlink_msg_get_target_sysid`/`_compid`, `mavlink_get_crc_extra`, `mavlink_min/max_message_length`,
  `mavlink_msg_get_target_system`, the `_pack_status`/`_encode_status`/`_send_buf` variants. The routing
  functions take `const mavlink_msg_entry_t *entry` that the callers pass from `mavlink_get_msg_entry` (an `Option`)
  and test for null: such a parameter needs to be an `Option` parameter (not done: a struct pointer parameter is
  assumed non-null).
- `GCS_MAVLink.cpp` itself is not translated: `mavlink_get_channel_buffer/status` reach `gcs().chan(chan)` (GCS and
  GCS_MAVLINK) and `comm_send_buffer` the UART objects; the unity's stand-ins replace them (above).
- `mavlink_channel_t` has four enumerators; channels 4-15 (cast from integers in GCS) are not representable (PORT-PLAN
  4.7, "Phase 4:"). The tests use channels 0-3.
- Signing: folded away (`--null-member`), as in the reference configuration.
- A struct pointer parameter is assumed non-null (a call passing null is rejected); a byte pointer parameter tested
  for null likewise (`mav_array_memcpy`'s `src == NULL` is false). Seven `mavlink_msg_*_send` calls in the reference tree pass
  `nullptr` or `NULL` for an array (`distance_sensor`'s quaternion in GCS_Common.cpp, AP_OSD's replies): their
  translation needs a null byte pointer (a flag, as the nullable out-pointers have); a call passing null is rejected now.

## Phase 4: AP_Mission (2026-11-12)

PORT-PLAN.md section 6, "Phase 4", the AP_Mission part (4.5): the mission's command storage, the conversions between
`Mission_Command` and MAVLink, and what of the mission does not need the vehicle's mode code, translated from
ArduPilot's AP_Mission.cpp (unmodified, the reference build's flags of its unit) and checked against the C++ bit for bit
and against the reference vehicle on the recorded flight's mission upload and download. Every new construct is behind
`--mission` (with `--mavlink`); every existing translation translates to the same bytes (sections 1-3 of
`tests/run_tests.sh`: every golden unchanged).

### New option (`--mission`)

- **Byte unions.** A union whose members have different types (`AP_Mission::Content`: 34 members in the reference
  configuration, packed structs and `Location`; `PackedContent { PackedLocation location; uint8_t bytes[12]; }`; the
  anonymous `union { Packed_Location_Option_Flags flags; uint8_t options; }` of `PackedLocation`) is a structure holding
  the bytes of its size, `bytes : Array UInt8 := Array.replicate N 0` (N from the members' layouts, rounded to the most
  aligned member: 16 for `Content`, alignment 4). A member is a view of the bytes at offset 0, and a member of a struct
  viewed in them is a view at its offset in clang's record layout (`mav_record_layout`, now also for unions): a path step
  `("ub", (offset, type))` reads a scalar with `CString.toUInt32 ...`/`Binary32.ofBits ...` (`scalar_from_bytes`) or a
  struct with `value_from_bytes`, and a write is `CString.write bytes offset (bytes of the value)`; a bit-field is a step
  `("ubf", (offset, bit, width, type))`, read by shift and mask from the bytes it spans (sign-extended if its type is
  signed: `int32_t alt:24` of `PackedLocation`) and written by read-modify-write of those bytes. A byte-array member
  covering the whole union (`packed_content.bytes`) is the bytes themselves, so it is passed as a byte pointer
  (`_storage.read_block(packed_content.bytes, ...)`) like any byte array. The default construction of a union whose
  members are value-initialized to zero (`Location location{}`: `Location()` is `zero()`, a `memset`) is the zero bytes.
  An anonymous union is named after its line (`PackedLocation.union'804_t`, member `union'804`). Every union of the
  translation is a byte union under `--mission`; one whose members are outside the model (AP_Param's `GroupInfo`
  pointers) fails only where it is used.
- **The layouts are cross-checked.** The signatures list the byte unions' layouts with their members at offset 0 and
  `"union": true`; `ardupilot/check_layouts.py` now writes `sizeof(union X)` for them and reads clang's anonymous union
  members (`union'LINE`). Records without a name (an unnamed struct, a typedef'd anonymous struct) and template
  specializations are not listed under `--mission` (clang's `sizeof` needs a name). `translate_mission.sh`:
  `check_layouts: 405 records, 3004 members: all equal to clang's` (`Mission_Command` 28 bytes, `Content` 16 aligned 4,
  `PackedContent` 12, `PackedLocation`'s 24-bit `alt` at bit 8, every message struct).
- **Signed bit-fields** (`int32_t alt:24`) in a struct's own state: a store keeps the value's low w bits, read back
  sign-extended (`(v <<< 8) >>> 8` on `Int32`).
- **`case lo ... hi:`** (GNU case range, `case 0 ... 1:` at AP_Mission.cpp:1144): one label per value (at most 256).
- **Value-initialization of a class** (`cmd = {};`, `Mission_Command home_cmd = {};`, `PackedContent packed {};`): the
  zero value when every node under the `{}` is an implicit value-initialization or a default construction that gives zero
  (a byte union, a class whose constructor is `zero()`); a designated initializer of a struct with methods
  (`packet = { seq: cmd.index, command: cmd.id, autocontinue: 1, };`, AP_Mission.cpp:1702) its members in order, the
  others zero.
- **A local pointer to one of several members** (`float *selector = nullptr; ... selector = &packet.param3; ... if
  (selector != nullptr && (!isfinite(*selector) || ...))`, AP_Mission.cpp:1078-1127): a `UInt8` saying which (0: null,
  k: the k-th distinct `&x` assigned to it, x a member of a local object); `*selector` is a `match` reading that member
  as it is when read (so a write to it after the assignment is seen, as through the pointer); only `*p` reads and null
  comparisons are accepted.
- **`memcpy` through `(void *)&x`**: between a byte union's bytes and a byte array
  (`memcpy((void *)&cmd.content, packed_content.bytes, 12)`), and between a scalar or struct and bytes
  (`memcpy((void*)&id, (void*)&b[1], 2)`, AP_Mission.cpp:3067) through the object's representation, written back.
- **A float converted to an 8- or 16-bit integer** is what clang emits on the reference target (arm64, checked by
  compiling `uint8_t f(float x) { return x; }` with the reference flags): `fcvtzs w`, the value truncated toward zero
  and saturated to int32 (NaN: 0), then its low bits; `(uint8_t)-221.0f` is 35. CFloat's `Binary32.toUInt8` (and
  `toInt8`, `toUInt16`, `toInt16`, also for `Binary64`) saturate to the narrow type's range instead (255, 0, ...): the
  two agree in range and differ outside it (undefined in C). Under `--mission` the conversion goes through
  `Binary32.toInt32`; the other translations keep CFloat's (a finding: an out-of-range conversion there would differ
  from the reference, PORT-PLAN.md "Phase 4:" in 6.7).
- Also: a static data member of a semaphore class (`static HAL_Semaphore _rsem;`) is no state; a constructor's functor
  parameter that only initializes data members left out by `--drop` (AP_Mission's `_cmd_start_fn`, `_cmd_verify_fn`,
  `_mission_complete_fn`) is not a parameter of the translation; a cast of a float to an enum then to an integer
  (`cmd.p1 = (NAV_VTOL_LAND_OPTIONS)packet.param1;`) is the float converted to the enum's underlying type, then to the
  integer; with `--world`, an object of a class at file scope is a World object, not a `--mavlink` file-scope variable.
- `tests/run_tests.sh`: nothing of `--mission` reaches an existing translation (they do not pass it).

### The translation (`ardupilot/translate_mission.sh` → `ardupilot/out/Mission/Mission_lib.lean`)

`ardupilot/unity_mission.cpp` includes AP_Mission.cpp, StorageManager.cpp, AP_ParamT.cpp, AP_Math's location.cpp and
AP_Math.cpp and AP_Common's Location.cpp unmodified (checked: each preprocesses in the unity as in its own unit with the
unity's flags), and defines the objects as the vehicle has them: `AP_Mission mission{...}` as ModeAuto holds it
(mode.h:619), its callbacks bound to a stand-in (`MissionVehicle`, not translated), and the difftest's harness
`MissionTest tester` (below). Flags: the reference build's for AP_Mission.cpp's unit (`ardupilot/ref_flags.py`) plus
`-DAP_SDCARD_STORAGE_ENABLED=0` on both sides (as for StorageManager in Phase 2b: the reference has 1, whose code is
`init`'s microSD block, run only when BRD_SD_MISSION > 0, default 0, and StorageAccess's `file != nullptr` branches,
taken only after `attach_file`) and `-fno-access-control` (the harness sets MIS_TOTAL and MIS_OPTIONS). Options:
`--world --world-pointers --member-objects --reachable` with the entry points of `ardupilot/mission.use`, `--mavlink
--mission --param-ext --hal-storage 16384`, AP_Mission.h/.cpp as `--header`, StorageManager, AP_Param, AP_Math,
AP_Common and the generated MAVLink headers as `--lib-dir`.

Translated (3,362 Lean lines with the harness, 95 definitions; 1,908 ArduPilot extent lines in 50 functions, 1,665 of
them AP_Mission's in 29 functions): `AP_Mission::init` (`_commands_max` from the storage size, MIS_TOTAL wiped when
above it, `check_eeprom_version` with `clear` and the version write, `init_jump_tracking`, CLEAR_ON_BOOT), `add_cmd`,
`replace_cmd`, `write_cmd_to_storage` (the 15-byte record: 8-bit id, or tag byte 0/1 and a 16-bit id; location
commands packed field by field into `PackedLocation`, the others by `memcpy` of 12 or 10 bytes), `read_cmd_from_storage`
(with `format_conversion`), `write_home_to_storage`, `clear`, `truncate`, `num_commands`, `num_commands_max`,
`get_command_id`, `get_next_nav_cmd` with `get_next_cmd`, `get_jump_times_run`, `increment_jump_times_run`,
`get_index_of_jump_tag` (DO_JUMP and DO_JUMP_TAG followed, at most 64 jumps, the jump counters as state), `is_nav_cmd`,
`stored_in_location`, `cmd_has_location`, `sanity_check_params`, `mavlink_int_to_mission_cmd`, `mission_cmd_to_mavlink_int`,
`convert_MISSION_ITEM_to_MISSION_ITEM_INT`, `convert_MISSION_ITEM_INT_to_MISSION_ITEM`, the constructor (AP_Param's
defaults from `var_info`); StorageAccess's constructor, `read_block`, `write_block`, byte/uint16/uint32 reads and writes;
`check_lat`/`check_lng`, `constrain_value_line`, `is_negative`. The translation and the Lean elaboration take about 20 s
each.

Boundary (`w.mission'inp`, set by the caller): `hal.util->get_soft_armed()` (in `clear`), `AP_HAL::millis()` (the
change time), `AP::ahrs().get_home()` (index 0 is home: `read_cmd_from_storage(0)` and `write_home_to_storage`). Left
out: GCS text (`GCS_SEND_TEXT` in `init` and the jump counter messages), `AP_HAL::panic` (`read_cmd_from_storage` of a
record with tag byte 0 and a location command id, which only the fence and rally ids 5000-5004 and 5100 can be: SITL
panics; the difftest does not write such records), `INTERNAL_ERROR`. Parameters: MIS_TOTAL, MIS_RESTART and
MIS_OPTIONS are AP_Param objects in the mission's state (`--param-ext`: `s._cmd_total._value`), set from `var_info`'s
defaults by the constructor; `set_and_save` sets (`AP_Param::save` dropped, as in Phase 3): connecting the save to the
translated AP_Param is the coordinator's. Rally and fence are compiled out of the reference (`HAL_RALLY_ENABLED 0`,
`AP_FENCE_ENABLED 0`): nothing of them is translated; so are the gripper, scripting (`NAV_SCRIPT_TIME`), the mount
(`DO_SET_ROI_WPNEXT_OFFSET`) and payload place (`AP_MISSION_NAV_PAYLOAD_PLACE_ENABLED 0`): their ids convert to
`MAV_MISSION_UNSUPPORTED` as in the reference.

**The interface for the GCS translation** (namespace `Mission_lib`; the mission is the World object `w.mission :
AP_Mission.State`, its inputs `w.mission'inp : AP_Mission.Inputs` (`get_soft_armed`, `millis`, `get_home :
Location.State`), the mission's StorageAccess the World object `w._storage`, the HAL storage the threaded `hal'storage :
Array UInt8` of 16384 bytes):

```
AP_Mission.init (s : State) (w : World) (inp : Inputs) (hal'storage : Array UInt8) : State × Array UInt8
AP_Mission.add_cmd (s : State) (w : World) (inp : Inputs) (cmd : Mission_Command.State) (hal'storage : Array UInt8) : State × Mission_Command.State × Array UInt8 × Bool
AP_Mission.replace_cmd (s : State) (w : World) (inp : Inputs) (index : UInt16) (cmd : Mission_Command.State) (hal'storage : Array UInt8) : State × Array UInt8 × Bool
AP_Mission.read_cmd_from_storage (s : State) (w : World) (inp : Inputs) (index : UInt16) (cmd : Mission_Command.State) (hal'storage : Array UInt8) : Mission_Command.State × Bool
AP_Mission.write_home_to_storage (s : State) (w : World) (inp : Inputs) (hal'storage : Array UInt8) : State × Array UInt8
AP_Mission.clear (s : State) (inp : Inputs) : State × Bool
AP_Mission.truncate (s : State) (inp : Inputs) (index : UInt16) : State
AP_Mission.num_commands (s : State) : UInt16           AP_Mission.num_commands_max (s : State) : UInt16
AP_Mission.get_next_nav_cmd (s : State) (w : World) (inp : Inputs) (start_index : UInt16) (cmd : Mission_Command.State) (hal'storage : Array UInt8) : State × Mission_Command.State × Bool
AP_Mission.mavlink_int_to_mission_cmd (input_packet : __mavlink_mission_item_int_t) (cmd : Mission_Command.State) : Mission_Command.State × MAV_MISSION_RESULT
AP_Mission.mission_cmd_to_mavlink_int (cmd : Mission_Command.State) (packet : __mavlink_mission_item_int_t) : __mavlink_mission_item_int_t × Bool
AP_Mission.convert_MISSION_ITEM_to_MISSION_ITEM_INT (packet : __mavlink_mission_item_t) (mav_cmd : __mavlink_mission_item_int_t) : __mavlink_mission_item_int_t × MAV_MISSION_RESULT
AP_Mission.convert_MISSION_ITEM_INT_to_MISSION_ITEM (item_int : __mavlink_mission_item_int_t) (item : __mavlink_mission_item_t) : __mavlink_mission_item_t × MAV_MISSION_RESULT
```

(`Mission_Command.State` is `{ index id p1 : UInt16, content : AP_Mission.Content, type_specific_bits : UInt8 }`, the
content its 16 bytes.) A call on the World object passes `w.mission` and `w` and stores the returned state back into
`w.mission` (lean/MissionRoundTrip.lean does this). The MAVLink structs are this translation's own
(`Mission_lib.__mavlink_mission_item_int_t`); Mavlink_lib has the same struct under its namespace: when both
translations are one (the GCS World), they are one type.

### The difftest (`python3 difftest.py ardupilot/Mission`)

A World difftest of the harness object `tester` (`ardupilot/Mission.json`; C++ side: AP_Mission.cpp and the other
sources compiled with the same flags, `ardupilot/mission_env.cpp` with the lock-step storage of reference/hal, the
inputs, a no-op `send_text`, AP_Param's `setup_object_defaults`). difftest.py's World driver now threads the HAL
storage when the member functions have it (`hs`, from zero; before, only the free-function driver passed it, zero-filled
per call). The harness's member functions take seeds and build everything from a xorshift generator (translated like
the rest, so both sides make the same values): floats of every kind (random bits: NaNs with payloads, infinities,
denormals; integers, quarters, values near 255, 65535, 2^31), ints (lat/lng extremes and out of range, random), every
command id the conversions handle and those compiled out, 0, 1 (reserved), unknown 16-bit ids, every frame 0-11 and
random ones:

- `t_boot(seed, total, mode, options)`: the whole storage random, the format version written or not, 40 random commands
  written, MIS_TOTAL (-3 to 450) and MIS_OPTIONS (0-15: CLEAR_ON_BOOT) set, `init()`;
- `t_add(seed, kind)`, `t_replace(seed, index, kind)`: a command converted from a random MISSION_ITEM_INT when that is
  accepted, else random id, p1, content bytes and type bits, or a location command with random fields; `add_cmd`,
  `replace_cmd` (at any index, beyond the end, 0);
- `t_raw(seed, index, tag)`: a random 15-byte record written at a slot (8-bit ids, tag bytes 0 and 1 with 16-bit ids);
- `t_read(index)`, `t_get(index)` (read, then `mission_cmd_to_mavlink_int`, as `get_item`), `t_clear()`,
  `t_truncate(index)`, `t_home()`, `t_next(start)` (`get_next_nav_cmd`, jumps followed);
- `t_conv(seed, kind)`: a random MISSION_ITEM_INT through `mavlink_int_to_mission_cmd` (the result, every byte of the
  command), then back through `mission_cmd_to_mavlink_int` (the result, every byte of the item);
- `t_item(seed, kind)`: MISSION_ITEM_INT to MISSION_ITEM and back to MISSION_ITEM_INT (random floats in x/y), both results
  and every byte.

After every call the harness hashes (FNV-1a) the whole 16 KB storage (`h_storage`) and every command read back
(indices 0 to MIS_TOTAL + 1, at most 400) with `read_cmd_from_storage` and `mission_cmd_to_mavlink_int` (`h_cmds`); the
driver prints the result and every leaf of the harness (the last command's 16 content bytes, the last item's 38) and of
the mission (the three Mission_Command members, the jump counters, the flags, the parameters), 364 per line. The inputs
(armed, millis, home with every flag) are random per line.

```
ardupilot/Mission World (defaults): 4327 calls (3000 random, 1327 corner) over 12 member functions of 1 objects, 364 leaves per line
ardupilot/Mission World (defaults): 0 of 4328 lines differ (0 tokens equal only as NaN vs NaN with different bits)
```

Sensitivity (`CPP2LEAN_MUTATE`, 1000 calls, 2328 lines): the 24-bit `alt` of `PackedLocation` read with the sign
extension one bit short (`>>> 40` to `>>> 41` in `read_cmd_from_storage`): 749 lines differ; the `lng` view of
`Content` written at byte 13 instead of 12 (`mavlink_int_to_mission_cmd`, `read_cmd_from_storage`): 1,603 lines. The
translation is deterministic (two runs, different `PYTHONHASHSEED`: the same Lean and signatures).

Excluded from the random values, as undefined in C or a panic in the reference: a stored DO_ENGINE_CONTROL record whose
`bool` members are bytes other than 0 and 1 (the harness writes 0 or 1 there, `valid_bools`: reading another byte as a
`bool` is undefined, and clang's code converts the byte itself, 245 to 245.0f, where the model's `bool` view of a byte
is `!= 0`); records with tag byte 0 and a fence or rally id (SITL's `AP_HAL::panic`). Found on the way: the harness's
own uninitialized `Mission_Command c;` (hashed when a read fails), fixed with `{}`.

### The mission round trip against the reference (`python3 ardupilot/mission_roundtrip.py`, `lean/MissionRoundTrip.lean`)

The recorded flight `sim/out/lockstep-flight` uploads a 6-item mission (MISSION_COUNT, six MISSION_ITEM_INT) and
downloads it (six MISSION_REQUEST_INT). The Lean program (`lake build mission_roundtrip`) boots the mission from
`storage_in.bin` with the translated `init` (MIS_TOTAL at the value the vehicle reported in the parameter download:
AP_Param's load is not part of this slice), rewrites the home record wherever the reference's home changes (est.txt
`home=`; AP_AHRS::set_home calls `AP::mission().write_home_to_storage()`, AP_AHRS.cpp:1787: the vehicle side, Phase 5),
parses the uplink bytes with the translated `Mavlink_lib.mavlink_parse_char` and decoders, and does what
MissionItemProtocol and MissionItemProtocol_Waypoints do with them (written out in the check, call for call: MISSION_COUNT
`truncate`, MISSION_ITEM_INT `mavlink_int_to_mission_cmd` then `replace_cmd` for a sequence number below the count or
`add_cmd` at it, MISSION_REQUEST_INT `read_cmd_from_storage` + `mission_cmd_to_mavlink_int` with get_item's `mission_type`
and `current`). The script compares each answered item with the payload of the MISSION_ITEM_INT the reference sent
(zero-extended; every byte but `target_system`/`target_component`, which the GCS layer sets from the request), and the
storage with the reference's (`copter_ref --storage storage_in.bin --storage-out F` on the trace up to the last mission
message, and on the whole trace):

```
lean: init: MIS_TOTAL 0, num_commands 0, num_commands_max 650
lean: count 6: truncate, num_commands 1
lean: item_int 0 command 16: mavlink_int_to_mission_cmd 0, replace_cmd true, num_commands 1
lean: item_int 1 command 22: mavlink_int_to_mission_cmd 0, add_cmd true, num_commands 2
... (items 2-5: add_cmd true, num_commands 3-6)
lean: home records written: 2
items: Lean 6, reference downlink 6
  item 0: 36 compared bytes equal (command 16, frame 0, x -353632610, y 1491652299)
  ... (items 1-5: equal; commands 22, 16, 16, 82, 21, frame 3)
storage after the last mission message (input line 16740): mission areas 9758 bytes, 0 differ (the reference changed 69 of them since boot); whole image 20 of 16384 bytes differ (offsets 94-358)
  outside the mission areas: 20 bytes differ, 20 of them where the reference's image differs from the boot image (AP_Param's saves: `set_and_save` of MIS_TOTAL and the vehicle's own, not modelled here)
storage at the end of the flight: mission areas 9758 bytes, 0 differ (the reference changed 69 of them since boot); whole image 20 of 16384 bytes differ (offsets 94-358)
mission round trip: all equal
```

(MIS_TOTAL is 0 at boot and becomes 1 when home is first set, at 14.4 s: the upload's item 0 replaces home, which
`replace_cmd` does not write.) The 20 bytes outside the mission areas are in the first parameter area (offsets 94-358):
AP_Param's saves, which the model leaves out (`save()` dropped; the coordinator connects MIS_TOTAL's save to the
translated AP_Param). `tests/run_tests.sh` section 8 runs the round trip.

### Speed

The difftest's 4,327 harness calls (each one hashing the whole 16 KB storage and reading back up to 400 commands with
their conversion) run in 0.65 s in Lean and 0.17 s in C++ (`-O2`): about 150 µs against 40 µs per call, so a
mission upload or download (a few storage writes or reads and one conversion per item) is far below a millisecond
of Lean per item. The round trip (boot, two home writes, 111 uplink lines through the MAVLink parser, six items
stored and read back) takes 0.05 s of Lean.

### Not done, and the Phase 5 boundary

- **The execution state machine** (`start`, `stop`, `resume`, `start_or_resume`, `reset`, `update`,
  `advance_current_nav_cmd`, `advance_current_do_cmd`, `set_current_cmd`, `restart_current_nav_cmd`, `complete`,
  `start_command`, `verify_command`, the landing-sequence and mission-leg searches, `calc_rewind_pos`,
  `update_exit_position`, `get_next_ground_course_cd`, `contains_item`, `contains_terrain_alt_items`, `jump_to_tag`,
  `set_item`/`get_item`): Phase 5. They call into ModeAuto through the three functors (`_cmd_start_fn`, `_cmd_verify_fn`,
  `_mission_complete_fn`, left out here: `--drop`, and the constructor's functor parameters with them), into the vehicle's
  libraries (`start_command`'s camera, relay, servo, aux-function, sprayer, parachute paths; the reference compiles most
  out), AP_AHRS (`get_location`, `distance_to_landing`), the logger (compiled out) and GCS text. What they need: the
  functors as `WFun`-like tags over the program's FUNCTOR_BINDs with arguments and results (Phase 3's `WFun` covers
  `Functor<void>` only), ModeAuto's objects in the World, AP_AHRS's location as an input. Their storage access is already
  translated (`get_next_cmd`, `read_cmd_from_storage`, the jump tracking).
- **AP_Mission_ChangeDetector**: not translated. It needs an array of `Mission_Command` (a class: it has member
  functions) as a member (`mis_change_detect.cmd[3]`: arrays of class objects are rejected), `Mission_Command::operator!=`
  (`memcmp(this, &b, sizeof(Mission_Command))` over a struct with padding: every Mission_Command of the vehicle comes from
  `{}` value-initialization or whole copies, so its padding is zero, which the model's representation also has; the
  translator rejects `memcmp` over padding), and `AP::mission()` from a member of ModeAuto (the World accessor).
- **AP_Param**: MIS_TOTAL's `set_and_save` sets the value; the save into the parameter area, and the boot value from it
  (`load_all`), belong to the AP_Param translation done in parallel.
- `MissionItemProtocol`, `MissionItemProtocol_Waypoints`, the GCS's routing: the coordinator's (the round trip writes
  out their calls); the DO_JUMP target check of `append_item`/`replace_item` is not emulated (no DO_JUMP in the flight).

## Phase 4: AP_Param (2026-11-12)

PORT-PLAN.md section 6, "Phase 4", the AP_Param part (4.4, D12, D15): ArduPilot's AP_Param translated from its sources —
loading from the storage image, the storage format, the `var_info` walks and enumeration, name building, lookup by
name, set and save — over a faithful model of what AP_Param really manipulates: raw memory. The vehicle's AP_Param boot
sequence on the translated code gives the reference's parameter list bit for bit (every index, name, type and value,
the counts, the storage), and the estimation replay now takes its parameters from the translated `load_all` instead of
the probe's dump. Everything new is behind a new option (`--param-memory`, a separate back end, `cpp2lean_mem.py`):
every earlier translation translates to the same bytes (sections 1-3 of `tests/run_tests.sh`, every golden unchanged).

### New option

| option | meaning |
|---|---|
| `--param-memory CONFIG` | translate the functions CONFIG names (and what they call) as C over one byte memory (below), with the constant data clang evaluated; `-o DIR`, `--namespace NS`. CONFIG (`ardupilot/param/AP_Param.json`): the units of the reference build and the AST filters to read (`-ast-dump-filter`), the units whose record layouts and statics are used, the root table, the entry functions, the HAL boundary (`boundary`: Lean text of each call's result; `hal_translated`: a HAL member the reference HAL inherits from AP_HAL, translated), functions left out (`drop`), and constants clang folds without printing them (`constants`) |

`ardupilot/translate_param.sh` runs it (and `ardupilot/param/gen_param_harness.py`, the harness data below) →
`ardupilot/out/AP_Param/AP_Param_lib.lean` (+ `ParamMemory.lean`, `CFloat.lean`, `AP_Param_lib.addresses.json`,
`estimator_params.json`) and `lean/ParamHarnessData.lean`.

### The model: one byte memory (`support/ParamMemory.lean`, `cpp2lean_mem.py`)

AP_Param's tables hold the address of a top-level object (`&copter.g.format_version`, `&copter.ahrs`), `offsetof`
offsets within groups and the address of a pointer member for pointer groups; its code computes `base + offset`,
casts to `AP_Param *` / `AP_Int8 *` / `AP_Float *`, compares addresses (`(ptrdiff_t)this == base + ofs`, which
finds a parameter's table entry), steps through a `Vector3f` by `sizeof(float)`, and reads storage blocks straight into
objects (`_storage.read_block(ptr, ofs, size)`). The translation keeps all of that, as C's abstract machine:

- **The memory** is one `ByteArray` (`PMem.Mem`, threaded by the state monad `PMem.M`): the constant data (the 45
  `var_info` tables reachable from `Copter::var_info`, their strings, the string literals of the code), the 4 objects
  the tables point into (`copter`, 13,216 bytes; `AP_AHRS_NavEKF3::EKF3`; `GCS::_chan_var_info`;
  `AP_BattMonitor::backend_var_info`), the 19 static members the code uses (AP_Param's `_var_info`, `_num_vars`,
  `_storage`, `sentinel_offset`, `_frame_type_flags`, `default_list`, ..., `StorageManager::layout` and its table,
  `SRV_Channels::_singleton`/`channels`), a heap (`new`: the defaults list of `add_default`) and a stack. 196,608
  bytes. The HAL storage is a second `ByteArray` with lockstep.cpp's semantics (as `--hal-storage`).
- **Addresses.** Every pointer, reference and `ptrdiff_t` is a `UInt64`; `AP_Param *` is the parameter's address, `this`
  of a member function an argument, `const GroupInfo *` / `const Info *` the address of a table entry (the brief's
  (table, index) is `table + 32 * index`). A scalar is read or written by its width, little endian, a float by its bit
  pattern, a bit-field by its bits (`Param_header`'s `key_low:8, type:5, key_high:1, group_element:18`, `ParamToken`'s).
  Struct and array objects, and every scalar local whose address is taken or that is bound to a reference (`ptrdiff_t
  base; get_base(info, base)`), live in the function's stack frame; the other scalar locals are Lean variables.
  `_storage.read_block(&phdr, ...)`, `memcpy`, `strncpy` into a name buffer, `*(uint32_t *)&phdr` are memory
  operations at those addresses. A struct passed by value is a copy in the caller's frame.
- **Layouts and constants from clang.** Record layouts are clang's (`-fdump-record-layouts-complete` of the units,
  bit-fields included); the constant data is clang's evaluation of ArduPilot's initializers, read from the units' LLVM IR
  (`-S -emit-llvm -O0` with the reference flags; `memir.py` serializes each global into its object representation by the
  IR's data layout and records its pointer fields as relocations, resolved to the memory's addresses). The tables'
  initializers are macros over `__builtin_offsetof` of members of non-standard-layout classes, `&copter.g.x` and
  defaults converted to `float`, which only clang's constant evaluator computes exactly: this is the brief's "offsets
  from clang" applied to the whole initializer (a deviation from reading the JSON AST of the initializers, which does not
  carry `offsetof` values). Each table appears in the generated file as its bytes, with its entries listed in a comment
  (`{"P", 8, def_value=0.135, flags=0, idx=0, type=4}`, `{"SERVO", 6840, group_info=SRV_Channels::var_info, ...}`).
- **Functions** are `partial def`s in `PMem.M` (one `mutual` block: the group walks recurse), translated statement by
  statement from clang's JSON AST: C's integer conversions as clang made them explicit (cpp2lean's `conv`), loops as
  `repeat` with the `for` increment at the top of the next iteration (so `continue` runs it), `switch` as an `if` chain
  with fallthrough, `&&`/`||`/`?:` with the right operand's effects only when evaluated. Calls follow the AST's
  declarations, across units by qualified name (template specializations by their arguments' values,
  `AP_ParamTBase<short, 2>::set_default`), constructors with their member initializers.
- **The boundary**: `hal.storage->read_block/write_block` (the HAL storage), `hal.storage->erase()` (AP_HAL::Storage's
  own `erase`, translated: lockstep.cpp does not override it), `hal.scheduler->register_io_process` (no effect: the
  save handler is not registered as a callback), `is_system_initialized`, `get_soft_armed`, `get_custom_defaults_file`
  (null on the reference board), `printf`/`DEV_PRINTF`/`hal.console->printf`, `GCS_SEND_PARAM` (no effect: output),
  `INTERNAL_ERROR`, `AP_HAL::panic` (no effect: `check_var_info`'s FATALs on malformed tables only).
- **Left out** (`drop`): `load_defaults_file_from_filesystem/romfs` (reached only with a defaults file: null on the
  board, D15) and `AP_Param::save`: the save queue (`ObjectBuffer_TS<param_save>`, a heap ring buffer built by a
  static constructor and drained by `save_io_handler` on the IO thread) is not translated; `save_sync`, which the IO
  thread runs for each queued parameter, is. `set_and_save`'s `save()` is therefore no operation: in the boot sequence
  below the reference's queued save is not processed before the dumps either (no IO process runs), so the dumps agree;
  a vehicle translation needs the queue (PORT-PLAN.md 4.4 "Phase 4:").

Translated: 98 functions over 1,825 distinct ArduPilot extent lines (AP_Param.cpp 56 functions / 1,572 lines,
StorageManager.cpp 4 / 121, AP_Param.h 7 / 33, AP_ParamT.cpp 3 / 16, AP_Math.cpp 2 / 39, SRV_Channels.cpp 1 / 19,
AP_HAL/Storage.cpp 1 / 10, AC_CommandModel.cpp 1 / 7, AP_Math.h, AP_Common.h): `setup`, `setup_sketch_defaults`,
`check_var_info` (with `check_group_info`, `duplicate_key`), `setup_object_defaults`, `load_all`, `find_by_header`,
`find_by_header_group`, `scan`, `load`, `is_sentinel`, `get_key`, `set_key`, `type_size`, `get_base`,
`adjust_group_offset`, `group_id`, `get_group_info` (both), `first`, `next`, `next_group`, `next_scalar`,
`find_var_info`, `find_var_info_group`, `find_var_info_token`, `copy_name_info`, `copy_name_token`,
`add_vector3f_suffix`, `find`, `find_group`, `find_by_name`, `find_by_index`, `count_parameters`, `invalidate_count`,
`cast_to_float`, `set_value`, `set_float`, `get_default_value` (both), `check_frame_type`, `set_frame_type_flags`,
`save_sync`, `write_sentinel`, `eeprom_write_check`, `erase_all`, `find_key_by_pointer(_group)`,
`load_object_from_eeprom`, `reload_defaults_file`, `add_default`, `check_default`, `configured`,
`configured_in_storage`, `var_info`, the constructors `AP_Param(const Info *)`, `StorageAccess(StorageType)`,
`AC_CommandModel(float, float, float)`, `SRV_Channels()`, `Vector3<float>(x, y, z)`, the `AP_ParamTBase`/`AP_ParamV`
members `set`, `get`, `set_and_save`, `set_default`, `cast_to_float`, `StorageAccess::size`/`read_block`/`write_block`,
`StorageManager::erase`, `AP_HAL::Storage::erase`, `is_equal<float>`, `constrain_value_line<float>`, `MIN`. 4,285 Lean
lines (most of them the tables' listings); the translation takes about 10 s (cached ASTs and IR: 3 s), its Lean
elaborates in about 20 s. Deterministic (two runs, different `PYTHONHASHSEED`: the same bytes).

### Static construction (`lean/ParamBoot.lean`, `ardupilot/param/gen_param_harness.py`)

The reference's parameter values before `setup()` come from the C++ constructors of `copter`'s members. The Lean side
runs the translated code for the same effects, on blank storage (copter_ref loads the image after static construction,
so `configured()` in a constructor sees nothing), in this order:

1. `StorageAccess AP_Param::_storage(StorageManager::StorageParam)` (translated constructor).
2. ParametersG2's member initializers `mode_rtl_ptr(&copter.mode_rtl)`, `mode_land_ptr(&copter.mode_land)` (the
   pointer cells of its `AP_SUBGROUPPTR` entries; taken from that constructor's preprocessed initializer list,
   Parameters.cpp:1203-1265, as the data `ctorPointers`).
3. `setup_object_defaults(object, table)` for every group of the parameter tree reachable from `Copter::var_info`
   through non-pointer entries and through those two pointers (93 calls, `ctorDefaults`, in tree order): each such
   class's constructor makes this call (`AP_Param::setup_object_defaults(this, var_info)`); plus `gps.params[2]`
   (AP_GPS's `Params params[3]` are all constructed, the table names the first two).
4. `AC_CommandModel(PILOT_Y_RATE_DEFAULT, PILOT_Y_EXPO_DEFAULT, 0.0f)` for `g2.command_model_pilot_y` (translated
   constructor; its table's `AP_GROUPINFO_FLAGS_DEFAULT_POINTER` defaults read the members it sets; arguments evaluated
   by clang).
5. `SRV_Channels()` (translated constructor: it sets the default of channels 17-32's `function` to `k_GPIO` with
   `set_default`, which also registers the default with `add_default`).
6. `copter.param_loader`'s `AP_Param(var_info)` (translated: `_var_info`, `_num_vars`, `_singleton`).

Steps 2-5 were found by the comparison below (each was a difference of the pre-load dump or of the difftest before it
was added); every address comes from clang (`__builtin_offsetof(Copter, ...)` in a generated unit compiled with the
flags of Parameters.cpp and `-fno-access-control`).

Then, as AP_Vehicle::setup: `setup_sketch_defaults()`, `check_var_info()`, AP_Vehicle::load_parameters's format check
(`format_version.load()`, `!= k_format_version` → `StorageManager::erase()`, `erase_all()`,
`format_version.set_and_save(120)`; `format_version.set_default(120)`) and `load_all()`.

### The full-vehicle check (`copter_ref --param-dump`, `param_dump`)

`reference/hal/param_dump.cpp` (new, compiled with `-fno-access-control`; `copter_ref --storage IMAGE --param-dump OUT`)
runs exactly that sequence in the reference after static construction, calling ArduPilot's functions only (the format
check repeated statement by statement, since `AP_Vehicle::load_parameters` goes on past `load_all`), and writes the
parameters as GCS_Param enumerates them (`first`/`next_scalar`, `copy_name_token(token, buf, AP_MAX_NAME_SIZE, true)`):
index, token, name, type, value bits, before loading (after `setup_sketch_defaults`) and after `load_all`, with the
count, `count_parameters()` and the storage digest. `lean/.lake/build/bin/param_dump IMAGE OUT` does the same on the
translation:

| storage image | defaults (before load_all) | after load_all | dumps |
|---|---|---|---|
| `sim/out/lockstep-flight/storage_in.bin` | 590 parameters | 609 parameters | identical |
| `sim/out/lockstep-qgc/harness/storage_in.bin` | 590 | 609 | identical |
| blank (16,384 zero bytes: header written, format check erases and re-saves) | 590 | 590 | identical |

(19 parameters appear after loading: the stored enable parameters show their groups. `_frame_type_flags` is 0 at this
point; `Copter::load_parameters` sets it after the conversions.)

### The per-function differential test (`python3 ardupilot/param_difftest.py`)

Both sides boot on a random storage image, then run the same random command script (`copter_ref ... --param-test
SCRIPT`, `param_dump IMAGE OUT --test SCRIPT`): next_scalar from real, neighbouring and random tokens; find_by_name and
find with real names, other case, prefixes, vector suffixes and random strings; find_by_index; set_float with random
types and values followed by save_sync (force or not) and the storage digest; load; count_parameters after setting
enable parameters; load_all again; and the whole enumeration at the end. Images: the flight's; blank; a valid header
and garbage; the flight's records with a sentinel at a random record boundary (type 0x1f, key 0x1ff, all zeros, all
ones); random bit flips; synthetic images of random records (real keys, types and group elements, and random ones,
random values); a wrong header over valid records. The C++ side is ArduPilot's real AP_Param with every table of the
vehicle (the reference vehicle itself).

```
$ python3 ardupilot/param_difftest.py --cases 66
ardupilot/AP_Param: 66 cases (images by kind: 0:3, 1:6, 2:7, 3:10, 4:13, 5:22, 6:5), 1905 commands; 0 of 43566 lines differ; 0 cases differ
```

Sensitivity: `group_id`'s `63U` (AP_Param.cpp:212) changed to `62U` in the Lean: the flight's dump differs in 2 lines (SERIAL0_BAUD, a nested group's element with index 0: its token's group element becomes 3999 instead of 4063, before and after loading), and `param_difftest.py --cases 22` reports 23 of 14,673 lines differing, in all 22 cases (the final enumeration of each).

### The estimation replay with the translated load_all

`ardupilot/estimation_replay.py FLIGHT` now sends `L <image>` to the harness: `lean/EstimationReplay.lean`'s
`loadParams` runs the boot sequence above on the flight's image (`ParamBoot.loadOnly`) and sets each of the 277
parameter paths of the estimator World (`barometer.sensors[0].ground_pressure`, `EKF3._gpsCheck`, `ahrs._trim.x`, ...)
from the parameter memory at its address (`ParamHarnessData.estParams`, the generated address map
`ardupilot/out/AP_Param/estimator_params.json`: path, object, offset, address, size, kind; offsets and types by clang).
The probe's `# params` is no longer the source; the script compares it with the translated load_all's values
(`param_dump IMAGE --est`). Nothing between `load_all` and the probe's first line changes an estimator parameter: all
277 values are equal (the conversions of `Copter::load_parameters` find no old keys in these images, and the front ends'
init runs after the probe's line); the stored IMU ids the harness passes to `ins.init` are now read from the translated
values too.

```
$ LEAN_NUM_THREADS=1 python3 ardupilot/estimation_replay.py sim/out/lockstep-flight
parameters: 277 from the translated AP_Param::load_all on sim/out/lockstep-flight/storage_in.bin (the probe's `# params`: 277, 277 equal)
estimation replay lockstep-flight: 36013 lines (boot init through 35098 main loops); steps compared: 35122 (891 inside barometer.calibrate and ins.init not compared); values compared: 8439007, equal: 8439007, different: 0; 0 steps differ
$ ... sim/out/lockstep-flight-noisy: the same, values compared: 8439007, different: 0
```

Without the `L` command (`ESTIMATION_REPLAY_DROP=L`: the World's parameters stay its constructors' defaults) 35,122
steps differ (4,070,139 values), from line 1 (`gps0`). `ESTIMATION_REPLAY_PARAMS=probe` restores the `# params` source.

### Speed

Apple M4, one thread (the machine shared with other builds; `param_dump` prints them), flight image:

| | C++ (`copter_ref`, -O2) | Lean |
|---|---|---|
| `load_all` (with the format check; 30-odd stored records, each `find_by_header` walking the tables) | 2 µs | about 1.1 ms |
| one enumeration pass (609 × `next_scalar` + `copy_name_token`) | 130-180 µs | about 40 ms |
| static construction, `setup_sketch_defaults`, `check_var_info` | (not measured) | about 1.2 ms |

The enumeration is the GCS's parameter download (one `next_scalar` and `copy_name_token` per PARAM_VALUE, or a whole
pass for `count_parameters` once): 66 µs per parameter in Lean. The cost is the model, not FloatLib: each memory access
goes through the state monad, each function call allocates and zeroes a frame, bit-fields are read bit by bit.

### The Lean interface (for the GCS translation)

`AP_Param *` is a `UInt64` address; the memory and every static of AP_Param (`_var_info`, `_num_vars`,
`_parameter_count`, `default_list`, ...) live in `PMem.Mem`, the state of `PMem.M`, with the HAL storage (`Mem.st`).
After `ParamBoot.boot`/`loadOnly` (or the same calls) a caller threads that state:

```
AP_Param.first (token ptype default_val : UInt64) : PMem.M UInt64            -- static; out-pointers are addresses (0: null)
AP_Param.next_scalar (token ptype default_val : UInt64) : PMem.M UInt64
AP_Param.copy_name_token (this token buffer : UInt64) (buffer_size : UInt64) (force_scalar : Bool) : PMem.M Unit
AP_Param.cast_to_float (this : UInt64) (type : UInt32) : PMem.M Binary32
AP_Param.find_by_name (name ptype token : UInt64) : PMem.M UInt64
AP_Param.set_float (this : UInt64) (value : Binary32) (var_type : UInt32) : PMem.M Unit
AP_Param.save_sync (this : UInt64) (force_save send_to_gcs : Bool) : PMem.M Unit
AP_Param.count_parameters : PMem.M UInt16
```

Buffers and tokens are memory (a caller allocates them with `PMem.enter`/`leave` or `PMem.alloc`); `ParamToken` is
4 bytes (key bits 0-8, idx 9-12, group_element 13-30, last_disabled 31). A cpp2lean translation of GCS_Param that holds
`AP_Param *` values (`_queued_parameter`) needs the bridge the brief anticipates: its `AP_Param *` as these addresses and
the calls above with the state threaded (as `--hal-storage` threads the storage). Phase 5 can replace the byte memory by
a dispatch from addresses to World paths: `AP_Param_lib.addresses.json` lists every object and table with its address
and size, and `estimator_params.json` maps addresses to the estimator World's paths.

### Tests

`tests/run_tests.sh` section 3b translates AP_Param against its golden (`tests/golden/ardupilot/AP_Param_lib.lean`, and
`tests/golden/ardupilot/ParamHarnessData.lean`), twice (determinism); section 8 (new) builds `param_dump` (no
warnings), compares the dumps on the two images and blank storage with the reference's, and runs the difftest (66
cases). Section 7's replay now loads its parameters through the translation.

### Not done, and limits

- The save queue (`AP_Param::save`, `save_io_handler`, `ObjectBuffer_TS`/`ByteBuffer`) and `flush`: not translated
  (above); `set_and_save` sets without saving. The difftest drives `save_sync` directly.
- `Copter::load_parameters`'s conversions after `load_all` (`convert_class`, `convert_g2_objects`,
  `convert_old_parameters`, `gcs().convert_parameters()`, `set_frame_type_flags(COPTER)`): not in this slice's boot
  sequence (the brief's "up to and including load_all"); `set_frame_type_flags`, `find_old_parameter`'s helpers exist or
  are reachable, the conversion functions are not translated.
- The motors' and controllers' tables behind `GOBJECTVARPTR`/`GOBJECTPTR` (null until `allocate_motors`) are not in the
  image (the frame's `AP_MotorsMatrix::var_info` is reached only through `motors_var_info`, set at run time);
  `load_object_from_eeprom` is translated but not exercised.
- Static construction is reproduced for its effects on parameters only, with the constructor calls listed above;
  other constructor effects on `copter` are not in the memory (nothing AP_Param reads depends on them, as the dumps and
  the difftest show). Defaults files (`AP_PARAM_DEFAULTS_FILE_PARSING`, ROMFS) are left out (D15).
- The `std::is_same<double, float>::value` of `is_equal<float>` is given in the configuration (`constants`): clang's
  JSON marks it a constant without its value.
- The doc locations of a function give its definition's lines; template instances share them.

## Phase 4: GCS_MAVLink (2026-11-12)

PORT-PLAN.md section 6, "Phase 4", the GCS part. What is done: GCS_MAVLink's code, as far as the recorded sessions
reach it without the vehicle, translated from the reference build's units over the byte memory of `--param-memory`
(one translation with AP_Param, AP_Mission, StorageManager, ByteBuffer and the MAVLink C library), compiled in Lean, run
end to end on the flight's uplink. What is not done: the byte replay against the recorded downlink (acceptance C), the
mission round trip through it (D), the reference probe (B), the per-class difftests (F); see "Not done" below.

### Design: the memory back end, not the value World

A first survey with the value World (`cpp2lean.py --world --world-pointers ...` on a unity of GCS_Common, GCS, GCS_Param,
MAVLink_routing, MissionItemProtocol(_Waypoints), GCS_MAVLink.cpp) stops at 23 data-member rejections before any member
function (`build/p4gs/survey.txt` and this stage's `build/gcs/survey1.txt`): `AP_HAL::UARTDriver *` and `const
AP_SerialManager::UARTState *` members, `AP_Param *_queued_parameter`, `ObjectBuffer<pending_param_request/reply>`
statics, `ObjectArray<statustext_t>` as a base class, `MissionItemProtocol *missionitemprotocols[3]`, an array of
`GCS_MAVLINK_InProgress` objects, `protocol_handler_fn_t` (a member function pointer), mutable static structs, `const
ap_message *` stream tables, the abstract `GCS` whose dynamic class is `GCS_Copter`. Each is a feature of the value
model; the memory back end of AP_Param has all of them already (pointers are addresses, objects are bytes at clang's
layouts, statics and tables come from the IR, `new` is the heap), and it makes the AP_Param bridge trivial: GCS_Param's
`AP_Param *` is the same address in the same memory, its calls (`first`, `next_scalar`, `copy_name_token`,
`cast_to_float`, `find_by_name`, `find_by_index`, `set_float`, `save_sync`, `count_parameters`) are calls of the
translated functions in the same `PMem.M`. So GCS is translated by `--param-memory` with a new configuration
(`ardupilot/gcs/GCS.json`); the configuration keys below are new and used only by it (AP_Param's translation is
byte-identical: `tests/run_tests.sh` section 3b passes).

### New configuration keys of `--param-memory` (cpp2lean_mem.py), all inactive without `dynamic`

| key | meaning |
|---|---|
| `dynamic` | `{class: [dynamic classes, most derived first]}`: every object of the class has one known dynamic class (`GCS_MAVLINK` objects are `GCS_MAVLINK_Copter`, `GCS` is `GCS_Copter`, `MissionItemProtocol` is `MissionItemProtocol_Waypoints`: Rally and Fence are compiled out). A member call that is not qualified (`handle_message(msg)`, `chan(i)->update_receive()`) calls the final overrider, found by name and parameter types (by the number of parameters when the declaration is in another dump, the non-const overload first); `GCS_MAVLINK::handle_message(msg)` written with the class name is not virtual (detected from the call's source range). Single inheritance: a base is at offset 0 (checked by the layouts used). With `dynamic` also: `for (x : array)` (clang's desugaring), a `break` nested in a `switch` section (the switch inside a `repeat`; a `continue` there is rejected), `AP_ParamT`'s conversion operators as member functions, `T (&)[N]`, typedefs of records and numbers, enums of a class dumped alone, unnamed records by their place, base-class and reference-member initializers and default member initializers in constructors, arrays of class objects default-constructed, static constant locals (placed from the IR as `f(...)::name`), a `c ? a : b` of two lvalues, `auto ... -> decltype(lvalue)` as a reference, the implicit copy assignment of a struct as a byte copy, overloads by argument count, one `Fn` per definition across dumps, the defining unit of a global declared `extern` elsewhere |
| `boundary` | as before (Lean text of a call's result), and now with `{0}`, `{1}`, ... (the arguments' values or addresses), `{this}` (the object's address) and `{_}` (nothing evaluated); also matched on the final overrider's name and on operators (`std::atomic<unsigned int>::operator=`) |
| `unreached`, `unreached_names` | functions outside the slice that the recorded sessions do not reach: a call records the name (`PMem.unreached`) and gives the type's default; the harness reports any such call |
| `zero_statics` | a static defined outside the units (`hal`, 8 bytes, a null reference: `hal.util->persistent_data.last_mavlink_msgid = ...` writes in the null page) |
| `imports`, `lean_options` | further support modules (`GCSMemory`) and `set_option`s (`maxHeartbeats 4000000`: AP_Mission's conversions) |

Other changes of cpp2lean_mem.py (all configurations): a survey mode (`CPP2LEAN_MEM_SURVEY=1`: every function's first
rejection, the reached functions listed to `CPP2LEAN_MEM_SURVEY_LIST`); the AST cache file of an all-lowercase filter
ends in `~lc` (macOS's case-insensitive file system made `gcs` and `GCS` one cache file). `support/ParamMemory.lean`'s
`Mem` has new fields with defaults (the clock, SERIAL0's queues, the boundary's records); `support/GCSMemory.lean` (new)
is the UART of lockstep.cpp and the boundary's records (`bframe`, `answer`, `unreached`, `statustexts`, `ffs`,
`popcount`, `abs`, `labs`).

### The translation (`ardupilot/gcs/translate_gcs.sh` -> `ardupilot/out/GCS/GCS_lib.lean`)

Entries: AP_Param's (as `ardupilot/param/AP_Param.json`), `GCS::update_receive`, `GCS::update_send`,
`GCS_MAVLINK::GCS_MAVLINK` (the constructor), `GCS_MAVLINK::param_io_timer`. 400 functions, 12,265 Lean lines (the
tables' listings included), 9,236 distinct ArduPilot extent lines: GCS_Common.cpp 66 functions / 2,940 lines,
AP_Param.cpp 58 / 1,606, AP_Mission.cpp 16 / 1,380, mavlink_helpers.h 15 / 601, GCS_Param.cpp 12 / 439,
MissionItemProtocol.cpp 16 / 382, MAVLink_routing.cpp 5 / 277, GCS_MAVLink_Copter.cpp 6 / 178 (the overriders that
forward: `packetReceived`, `handle_message`, `handle_command_int_packet`, `try_send_message`, `params_ready`,
`command_int_only`), RingBuffer.cpp 10 / 149, StorageManager.cpp 8 / 141, MissionItemProtocol_Waypoints.cpp 9 / 94,
GCS_MAVLink.cpp 7 / 90 (`comm_send_buffer`, `comm_get_txspace`, `comm_send_lock/unlock`, the channel accessors), GCS.cpp,
the message headers the code reaches. The receive path (`update_receive` with the parser `mavlink_frame_char_buffer`,
`packetReceived`, `MAVLink_routing::check_and_forward`, `accept_packet`, `handle_message` with heartbeat, request data
stream, command long/int with REQUEST_MESSAGE, SET_MESSAGE_INTERVAL, the COMMAND_ACK, system time, timesync, the
parameter messages, the mission messages), the send side (`update_send`: the deferred messages and buckets, stream
intervals from the SRn_ rates, `do_try_send_message`, `try_send_message`, `queued_param_send`,
`send_parameter_async_replies`, the mission protocol's sends, `comm_send_buffer` into SERIAL0's transmit queue). The
translation takes 25 s (cached ASTs and IR), Lean about 1 min (GCSLib) plus 3 min for the C of an executable. Deterministic
(two runs, different `PYTHONHASHSEED`). Golden `tests/golden/ardupilot/GCS_lib.lean`, `tests/run_tests.sh` section 3c.

### The Phase 5 boundary (GCS.json)

- **Frames whose content is the vehicle's** (`PMem.bframe`: the next recorded frame of that id, written where the
  translated `try_send_message` sends it, its sequence number checked against the channel's and the channel's advanced):
  `send_heartbeat` (0), `send_sys_status` (1), `send_system_time` (2), `send_raw_imu` (27), `send_scaled_pressure`
  (29, 2, 3), `send_attitude` (30), `send_attitude_quaternion`, `send_local_position` (32), `send_global_position_int`
  (33), `send_servo_output_raw` (36), `send_mission_current` (42), `send_gps_global_origin` (49),
  `send_nav_controller_output` (62, also Copter's), `send_rc_channels` (65), `send_rc_channels_raw`, `send_vfr_hud` (74),
  `send_power_status` (125), `send_battery_status` (147), `send_autopilot_version` (148), `send_meminfo` (152),
  `send_ahrs` (163), `GCS_MAVLINK_Copter::send_wind` (168), `send_ahrs2` (178), `AP_AHRS::send_ekf_status_report` (193),
  `send_vibration` (241), `send_home_position` (242), `send_extended_sys_state` (245), `AP_GPS::send_mavlink_gps_raw`
  (24) and the GPS RTK/2, compass calibration, `send_available_mode` (435, the mode count 9), and the ids compiled
  out or not streamed (RPM, fence, rangefinder, distance sensor, optical flow, targets, MCU, highres IMU, airspeed,
  simstate, PID tuning, generator, winch, high latency, ADSB, relay, flight information, gimbal). STATUSTEXT (253):
  `GCS::service_statustext` writes the recorded STATUSTEXT frames of the step (`textQuota`); `send_text` is no
  operation (the queue is the vehicle's).
- **The vehicle's answers** (`PMem.answer`, supplied by the harness): `handle_command_do_set_mode` ("set_mode"),
  `handle_command_component_arm_disarm` ("arm"), `GCS_MAVLINK_Copter::handle_MAV_CMD_NAV_TAKEOFF` ("takeoff").
- **HAL and other libraries**: the clock (`millis`, `micros`, `micros64`, `millis16`), SERIAL0 (`available`, `read`,
  `write`, `txspace`, `bw_in_bytes_per_second` 1,000,000, `flow_control_enabled` false, `is_write_locked` false),
  `in_delay_callback` (`inDelayCb`), `AP_Scheduler::time_available_usec` (`timeAvail`), `get_loop_period_us` 2500,
  `UARTState::get_protocol` 2 (MAVLink2), `AP_SerialManager::get_passthru` false (`GCS::update_passthru` dropped),
  `in_config_error` false, `usb_connected` false, `AP_AHRS::get_home` (`homeAddr`), `AP_RTC::set_utc_usec` no operation,
  semaphores, `fprintf`; signing (null: `mavlink_signature_check`, `accept_unsigned_callback`, `mavlink_sign_packet`).
- **Unreached** (recorded if called; none is called on the flight's uplink): the handlers of messages and commands the
  sessions do not send (SET_MODE, SET_GPS_GLOBAL_ORIGIN, PARAM_VALUE, RADIO_STATUS, GPS injection, STATUSTEXT, LED,
  MANUAL_CONTROL, PLAY_TUNE, DATA96, RC override, DISTANCE_SENSOR, LANDING_TARGET, NAMED_VALUE, CAN, COMMAND_ACK; 25
  commands of `GCS_MAVLINK::handle_command_int_packet` and 13 of Copter's), AP_Mission's execution state machine,
  `do_guided`, `send_banner`.

### The smoke run (`lake build gcs_smoke`; NOT the acceptance replay)

`lean/GCSSmoke.lean`: one channel built by the translated constructor on a zero GCS object in the heap (AP_Param's boot
not run; SYSID_THISMAV set to 1 by hand), the flight's recorded uplink fed line by line into SERIAL0, `GCS::update_receive`
and `GCS::update_send` run once per line; no recorded frames are loaded (so every boundary frame is logged "no recorded
frame").

```
$ lean/.lake/build/bin/gcs_smoke sim/out/lockstep-flight/{inputs.txt,outputs.txt,storage_in.bin}
gcs_smoke: 36013 lines in 0.44 s (12.3 us per line)
frames written by the translation: 36036; recorded downlink frames: 7304 (+76 non-MAVLink bytes)
unreached functions called: []
```

It runs without a failure, and shows a difference to find first: the translation's own frames (TIMESYNC on every line; the
channel is not initialised as `GCS_MAVLINK::init` would, the cause of the rate not checked) have an
11-byte header, one byte more than the reference's (`fd 0b 00 00 00 <seq> <sysid> <compid> 6f 00 00` against `fd <len>
00 00 <seq> <sysid> <compid> <id>`): a byte between the compat flags and the sequence number. Not located (the value
translation `Mavlink_lib` of the same helpers is difftested at 0 lines, so the cause is in the memory back end's
translation of `_mav_finalize_message_chan_send_target`/`mavlink_header_to_send_buffer`, or in the image's
`mavlink_system`).

### Not done (and what it needs)

- **The byte replay (C), the mission round trip (D), the probe (B)**: the harness must (1) build the vehicle's GCS state
  as the reference does: static construction (the `ObjectBuffer` statics `param_replies`/`param_requests` and
  `GCS_MAVLINK_InProgress`, `GCS::GCS`, `copter._gcs` at its address in `copter` rather than a heap object, so that
  AP_Param's boot (`ParamBoot`, regenerated for this image's addresses) loads SYSID_THISMAV, SRn_ and MIS_TOTAL into it),
  `GCS::setup_console`/`setup_uarts` (`create_gcs_mavlink_backend`) and `GCS_MAVLINK::init` (with
  `AP_SerialManager` as a boundary), `MissionItemProtocol_Waypoints` at the first `update_send`; (2) run task 28/29 at the
  steps the reference's scheduler runs them and the delay callbacks during boot (`est.txt`'s `tasks=`/`dcb=`), and
  `param_io_timer` per consumed line (the IO process); (3) load the recorded frames per id (`Mem.frames`) and the
  answers (from the recorded COMMAND_ACKs or a probe); (4) compare each step's transmit bytes with `down=`. The probe
  additions (B: per step `timeAvail`, `inDelayCb`, home) are not made; `reference/` is unchanged.
- The header difference above.
- Difftests (F) of the parser/routing/handler path and the param protocol: not written (the value translation's
  difftests cover the MAVLink library; AP_Param's `param_difftest.py` covers AP_Param's functions).
- Speed (E): the smoke run's 12 µs per line (receive and send with a mostly idle channel) is the only figure; the C++
  `GCS::update_send` 0.25 µs and `update_receive` 0.13 µs per step (REFERENCE.md).

### Second stage (2026-11-12): the header bug, the boot, the byte replay

- **The 11-byte header** of the smoke run was a bug of the memory back end: `buf[ofs++] = x` with `ofs` a register
  read the variable after the increment (`old` was the variable's name, not a snapshot). Fixed under `dynamic` (a
  `let` of the old value). AP_Param's translation has postfix increments only as statements (its golden is unchanged;
  with the fix forced on, `CPP2LEAN_MEM_POSTFIX_FIX=1`, its text differs only by the snapshots).
- **More of `dynamic`**: default member initializers of member objects (`_timesync_request.interval_ms = 10000`, records
  found by name or place, `recnodes`), non-const static locals (`AP_Vehicle::scheduler_delay_callback`'s
  `last_1hz/last_50hz/last_5s`, placed from the IR), `delete` (nothing), `std::atomic<uint32_t>{v}`, inherited
  constructors (`inherited_ctors`: `GCS_MAVLINK_Copter` uses `GCS_MAVLINK`'s), overloads by argument count in boundary
  keys (`write/1`), Lean keywords as parameter names (`instance`). Entries added: `GCS::init`, `GCS::setup_console`,
  `GCS::setup_uarts`, `GCS::send_message`, `AP_Vehicle::scheduler_delay_callback` (translated: the boot's delay
  callbacks), the `ObjectBuffer` constructors. 418 functions, 12,640 Lean lines. New boundary: AP_SerialManager
  (`find_serial`/`find_protocol_instance`: SERIAL0 for instance 0; `get_device_id` 65542, MAV1_DEVID as the reference
  reports it; `baudrate`, options), the UART's `begin`/flow control/single-byte `write`, `hal.scheduler->delay` inside
  translated code (`delayMark`: GCS_MAVLINK::init's SiK reset), `AP_Notify::update`, `GCS::convert_parameters` (no old
  keys in these images), `config_error`, `calloc`, `GCS_MAVLINK_Copter::params_ready` true (`copter.ap.initialised_params`,
  set by init_ardupilot before any request of the sessions), `send_banner` (its texts are recorded STATUSTEXT frames).
- **The boot** (`lean/GCSReplay.lean`, `lean/GCSHarnessData.lean` from `PARAM_HARNESS_TARGET=gcs
  ardupilot/param/gen_param_harness.py`): AP_Param's static construction on this image's addresses, `GCS::_singleton =
  &copter._gcs` (clang's offset), the two `ObjectBuffer` statics, the format check and `load_all` (MAV_SYSID, SRn_,
  MIS_TOTAL from the image), `GCS::init`, `setup_console` (the channel: constructor, `load_object_from_eeprom` of its
  MAV1_ parameters, `GCS_MAVLINK::init`, which writes the SiK reset `30 20` three times between four delays, as the
  reference's output lines 1-3 show), `setup_uarts`.
- **The byte replay** (`python3 ardupilot/gcs/gcs_replay.py SESSION [EST]`, `lake build gcs_replay`): per input line the
  uplink into SERIAL0, the IO process (`param_io_timer`, once registered), the delay callbacks `dcb` of `est.txt` during
  boot (the translated `scheduler_delay_callback`), tasks 28/29 when `tasks=` lists them, the IO process after the loop.
  Boundary frames: the content messages above (by message id, sequence checked and advanced), and the vehicle's own
  frames in one queue by place (PARAM_VALUE with index 65535 from AP_Param's change notifications, STATUSTEXT): before the
  GCS work when the recorded step starts with them, else after it. The vehicle's answers from the recorded COMMAND_ACKs.
  The qgc session has no `est.txt`: `copter_ref --est` made one (outputs identical to the recording).

```
$ python3 ardupilot/gcs/gcs_replay.py sim/out/lockstep-flight
gcs_replay: boot 3.8 ms; 36013 steps, GCS work 0.28 s (7.7 us per step)
gcs replay sim/out/lockstep-flight: 36013 steps, 35212 steps whose frames are all equal
recorded frames 7304 (247159 bytes; + 76 console bytes not compared): equal 312 (translated 0, boundary 312), different 368, missing or extra 10899
first difference: step 421, frame 1: the reference starts the parameter download (PARAM_VALUE FORMAT_VERSION, index 0)
storage at the end: mission areas 9758 bytes, 69 differ (the reference changed 69: the upload was not stored)
$ python3 ardupilot/gcs/gcs_replay.py sim/out/lockstep-qgc/harness build/gcs/qgc/est.txt
gcs_replay: boot 3.6 ms; 55515 steps, GCS work 0.39 s (7.0 us per step)
gcs replay sim/out/lockstep-qgc/harness: 55515 steps, 52621 steps whose frames are all equal
recorded frames 9707 (329885 bytes): equal 398 (translated 15, boundary 383), different 2096, missing or extra 12439
  HEARTBEAT 140 boundary-equal; COMMAND_ACK 21: 15 translated-equal, 6 different; AUTOPILOT_VERSION 1 boundary-equal; STATUSTEXT 5 of 6
first difference: step 3616: the translation sends HOME_POSITION and EXTENDED_SYS_STATE, the reference nothing
```

Where it stands. Everything up to the first differences is equal, sequence numbers included: the boot (the SiK bytes,
the boot heartbeats of the translated delay callbacks, the vehicle's notifications and texts), and in the qgc session
the first 15 COMMAND_ACKs (SET_MESSAGE_INTERVAL, REQUEST_MESSAGE) produced by the translation. The two first
differences, both found, not fixed:
1. **A boundary function that may send nothing.** `send_home_position` returns without a frame while home is not set
   (`AP::ahrs().home_is_set()`), `send_extended_sys_state` likewise; `bframe` always sends. Next step: the frames file
   carries each frame's step, and `bframe` sends the next frame of its id only when it was recorded in the current step
   (the scheduler's decision to try is still checked; the vehicle's decision to send is the recording's).
2. **The parameter download starts late and carries another count.** The translation sends its first PARAM_VALUE at
   step 2133 instead of 421 (not yet located: `queued_param_send`'s bandwidth and timing inputs during the delay
   callbacks are the suspects), with `param_count` 621 against 781: the reference's count includes the parameters of
   objects allocated at run time (motors, attitude, position and waypoint controllers behind GOBJECTPTR/GOBJECTVARPTR,
   `allocate_motors`), which this memory does not have (Phase 5).
- **Mission round trip (D)**: not reached. The flight's upload is not stored (mission areas: all 69 bytes the reference
  wrote differ), because the replay diverges before it (step 421); the mission protocol itself is translated.
- **Difftest (F) with mutation**: not written in this stage.
- **Speed (E)**: 7.0-7.7 µs of GCS work per 400 Hz step on the recorded sessions (Lean, one process, release build, one
  run each, not the BENCH.md protocol), against the C++ `update_receive` 0.13 + `update_send` 0.25 µs per step.

### Third stage (2026-11-12): per-step boundary frames, the boot state, the run-time parameter objects

- **Per-step boundary frames**: each recorded frame carries its step; `bframe` sends the next frame of its id only when
  it was recorded in the current step (the vehicle side's decision to send is the recording's, the scheduler's attempt
  the translation's), skipping and logging frames the translation never asked for; only SERIAL0's channel takes them.
- **The late parameter download, located and fixed**: a channel dump (reference: `CPP2LEAN_GCS_DUMP=FROM,TO
  copter_ref --est ...`, a diagnosis-only addition to the private `reference/hal/est_probe.cpp`, stderr only, outputs and
  `est.txt` byte-identical; Lean: `GCS_REPLAY_DUMP=FROM,TO`; `build/gcs/dumpdiff.py` names the differing fields by clang's
  layout) showed `deferred_message[1]` (MSG_NEXT_PARAM, interval 100) uninitialised in the translation: clang's JSON puts
  the explicit elements of an initializer list with an array filler inside `array_filler` (no `inner`), so the default
  member initializer `deferred_message[3] = { { MSG_HEARTBEAT, }, { MSG_NEXT_PARAM, }, }` initialised nothing. Fixed
  (under `dynamic`). Also: the statics' default member initializers (`last_radio_status.txbuf = 100`: clang's IR has
  `zeroinitializer` and a global constructor) are a generated `staticDynamicInit` the harness runs; the CXXDefaultInitExpr's
  own rewritten initializer is used. With these the flight's download starts at step 421, as the reference's.
- **The run-time parameter objects** (`Copter::allocate_motors`): `extra_tables` places `AC_AttitudeControl_Multi::var_info`
  and `AP_MotorsMulticopter::var_info` (reached only through `motors_var_info`/`attitude_control_var_info`);
  `gen_param_harness.py` (GCS target) writes `runtimeObjects` (pointer member, clang's sizeof, table, var_info pointer
  member, the object's groups); the harness allocates each in the heap, sets the pointer (and var_info pointer), runs the
  translated `setup_object_defaults` on each group and `load_object_from_eeprom`. The constructors' own defaults
  (AC_PID's constructor arguments read through `AP_GROUPINFO_FLAGS_DEFAULT_POINTER`, as AC_CommandModel for the static
  objects) are not done: those parameters read 0.
- **SERIAL1 and SERIAL2 are MAVLink ports** in the reference (SERIALn_PROTOCOL 2 by default): the reference creates
  three channels (MAV2_, MAV3_ parameters); `findSerial` now gives three UARTs, only SERIAL0 connected (as lockstep.cpp).

Further in the third stage (each found by the channel dump or the parameter comparison, fixed under `dynamic`):

- `AP_Vehicle::setup`'s `setup_sketch_defaults` and `check_var_info` were missing from the harness's boot (the
  top-level scalars' defaults: RTL_CONE_SLOPE, FS_THR_ENABLE, ... read 0); `Copter::load_parameters`'s
  `set_frame_type_flags(AP_PARAM_FRAME_COPTER)` (ARMING_RUDDER) added.
- The controllers' constructors are translated (entries `AC_AttitudeControl_Multi`, `AC_PosControl`, `AC_WPNav`,
  `AC_Loiter`, `AC_Circle`, `AP_BattMonitor_Analog`; with AC_PID/AC_P/SlewLimiter/LowPassFilter): a delegating
  constructor (`AC_PID(const Defaults &)`), and a one-argument `const X &` constructor is a copy only when X is the
  class itself (before, `AC_PID{Defaults{...}}` was copied as 240 bytes from the 44-byte Defaults).
- SERIAL1 and SERIAL2: their MAV2_/MAV3_ channels exist (`findSerial`), not connected; `get_device_id` per port.
- `GCS::convert_parameters` is translated (it was a no-op boundary: the images have old SR0_ keys, and the conversion
  sets the stream rates of MAV1_); `AP_Param::flush` a no-op (the save queue is not modelled).
- ModeAuto's AP_Mission: its constructor (callbacks left out: `skip_members`), the static `AP_Mission::_storage`'s
  constructor, `AP_Mission::init` (`AP::boardConfig()` null: no microSD mission).
- A reference member (`MissionItemProtocol_Waypoints::mission`) is read through its cell (before: the cell's address
  was used as the object: `num_commands_max` 0, MAV_MISSION_NO_SPACE).
- Vehicle parameter changes: `CPP2LEAN_PARAM_SNAPSHOT=STEP,...` (est_probe.cpp, diagnosis output on stderr; outputs and
  `est.txt` byte-identical, checked) prints every parameter after those steps; the harness sets, through the translated
  `AP_Param::find`/`set_float`, the values non-GCS code changed (compass calibration, gyro offsets, BRD_SAFETY_MASK,
  BARO1_DEVID, SERVOn_FUNCTION, RCn_DZ, ...), at the first parameter request, at the end of boot and every 400 steps;
  MAVn_/MAV_ parameters are excluded (the GCS's own).

Results (`python3 ardupilot/gcs/gcs_replay.py SESSION [EST]`, final state of this stage):

```
flight: 36013 steps, 35957 with all frames equal; recorded 7304 frames (247159 bytes): equal 7145 (translated 670,
        boundary 6475), different 149, missing or extra 10; equal bytes 241685
        parameter download by index: 781 of 781 present, param_count 781; 780 equal (name, value, type, count)
        first difference: step 3813, EK3_IMU_MASK's value (1 recorded, 3 here: set by the vehicle after the snapshot that
        the harness applies, not located; the frames after it differ in sequence number only where noted below)
        mission upload and download: all 18 mission/command frames equal in content (sequence numbers and checksums
        excluded: they differ after the earlier differences); storage at the end: mission areas 1 of 9758 bytes differ
        (offset 1544, the home record: AP_AHRS::set_home's write_home_to_storage is the vehicle's, not replayed);
        20 bytes of the parameter area differ (AP_Param's save queue, MIS_TOTAL's save, not modelled)
qgc:    55515 steps, 55337 with all frames equal; recorded 9707 frames (329885 bytes): equal 8903 (translated 16,
        boundary 8887), different 802, missing or extra 2
        HEARTBEAT 140/140, HOME_POSITION 112/113, MISSION_CURRENT 234/234, STATUSTEXT 5/6, AUTOPILOT_VERSION 1/1 boundary
        equal; COMMAND_ACK 15/21 translated equal; parameter download by index 779 of 781 equal
        first difference: step 5765: GPS_GLOBAL_ORIGIN and HOME_POSITION, pushed by the vehicle when the EKF origin and
        home are set (GCS_SEND_MESSAGE in vehicle code, Phase 5), not sent here; the later frames differ in sequence
```

Sensitivity (a mutation of the translated parser's checksum in `lean/GCS_lib.lean`, `crc_accumulate`'s `<<< 4` to
`<<< 3`, rebuilt, both replays, then restored): every uplink frame fails its checksum, nothing is handled: flight
136 frames equal (was 7145), the parameter download 0 of 781; qgc 147 equal (was 8903), COMMAND_ACK 0 of 21 (was 15),
first difference step 3216 (the first COMMAND_ACKs) instead of 5765.

Speed: the GCS work per 400 Hz step was 18 µs (flight) before the parameter snapshots were applied inside the steps;
with them in the measured steps 99-122 µs (the snapshot application is harness work). C++: `update_receive` 0.13 +
`update_send` 0.25 µs per step.

## Phase 5d summary (the QGroundControl session, the scenario suite, pre-arm checks, speed, the live launch path, 2026-11-13)

PORT-PLAN.md section 6, "Phase 5", the Phase 5d brief: (1) the recorded QGroundControl session on the whole translated
vehicle, (2) a scenario suite recorded with the reference and checked on the translation, replayed and closed loop, (3)
real pre-arm checks and estimator answers, (4) the speed margin, (5) a launch path for a live QGroundControl session with
the translated vehicle. Work split: the orchestrator did items 1, 2, 4 and 5 in the main workspace; one agent did item 3
in an APFS clone (`build/p5d_pre`, section "Phase 5d: pre-arm checks in the World" below), merged and regenerated in the
main workspace (the regenerated Estimator_lib, Vehicle_lib and VehicleBridge are byte-identical to the clone's).

Results (main workspace, release build after the last change; every command below re-run after the final rebuild):

```
$ LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-qgc/harness --est build/gcs/qgc/est.txt
PWM identical on 55515 of 55515 lines; down bytes identical on 55515; both on 55515; boot (init, 915 lines) both identical on 915
tasks identical on 55515 of 55515 steps (tick identical on 55515)
tasks by scheduler tick: 54600 ticks compared, 54600 identical; first difference: None
storage at the end: 16384 bytes, 0 differ from the reference's
$ LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight
PWM identical on 36013 of 36013 lines; down bytes identical on 36013; both on 36013; boot (init, 915 lines) both identical on 915
tasks identical on 36013 of 36013 steps (tick identical on 36013); tasks by scheduler tick: 35098 of 35098 identical
storage at the end: 16384 bytes, 0 differ from the reference's
$ python3 sim/scenarios.py --live
loiter: ok   replay: PWM 28413 of 28413, down 28413, tasks 28413 of 28413, storage 0 bytes differ
loiter: ok   closed loop: inputs.txt identical (28413 lines); outputs.txt identical (28413 lines); end: script finished
brake: ok   replay: PWM 28413 of 28413, down 28413, tasks 28413 of 28413, storage 0 bytes differ
brake: ok   closed loop: inputs.txt identical (28413 lines); outputs.txt identical (28413 lines); end: script finished
rtl: ok   replay: PWM 32013 of 32013, down 32013, tasks 32013 of 32013, storage 0 bytes differ
rtl: ok   closed loop: inputs.txt identical (32013 lines); outputs.txt identical (32013 lines); end: script finished
guided: ok   replay: PWM 28413 of 28413, down 28413, tasks 28413 of 28413, storage 0 bytes differ
guided: ok   closed loop: inputs.txt identical (28413 lines); outputs.txt identical (28413 lines); end: script finished
battery: ok   replay: PWM 26813 of 26813, down 26813, tasks 26813 of 26813, storage 0 bytes differ
battery: ok   closed loop: inputs.txt identical (26813 lines); outputs.txt identical (26813 lines); end: script finished
prearm: ok   replay: PWM 26413 of 26413, down 26413, tasks 26413 of 26413, storage 0 bytes differ
prearm: ok   closed loop: inputs.txt identical (26413 lines); outputs.txt identical (26413 lines); end: script finished
$ LEAN_NUM_THREADS=1 python3 ardupilot/onestate_replay.py sim/out/lockstep-flight
estimation replay lockstep-flight: ... values compared: 8439007, equal: 8439007, different: 0; 0 steps differ
```

The recorded flight flown closed loop again (`fly_reference.py --script flight --bin sim/lean_vehicle.py`): inputs.txt and
outputs.txt `cmp`-identical to `sim/out/lockstep-flight` (36,013 lines each).

### Item 1: the QGroundControl session

`vehicle_replay.py` takes the session's estimation trace with `--est` (the session's `copter_ref --est` file is
`build/gcs/qgc/est.txt`). On the first replay PWM, tasks and storage were already identical on all 55,515 lines and the
downlink differed on 11 lines, two causes, both fixed:

- **AUTOPILOT_VERSION's `uid2`** (line 3,226; the payload 44 bytes instead of 77): the HAL member
  `AP_HAL::Util::get_system_id_unformatted(uint8_t buf[], uint8_t &len)` was not implemented by the Lean HAL (`hal?` in
  the log), and the translator passed `len`'s value instead of its address. Fixed: lockstep.cpp's implementation added to
  the HAL (`lean/VehicleReplay.lean`, hand-written HAL), and cpp2lean_mem.py passes a HAL call's reference argument by
  address (the callee's declared parameter type when the declaration is indexed, else clang's value category: a scalar
  argument that stays an lvalue is bound to a reference; `.hal_calls.txt` lists them: `get_system_id_unformatted/1`,
  `get_system_load/0,1`).
- **AVAILABLE_MODES' `mode_name`** (10 lines): `GCS_MAVLINK_Copter::send_available_mode` passes a mode name of 4 to 17
  bytes to `mavlink_msg_available_modes_send`, which copies 50 bytes: a read past the end of a string literal (C undefined
  behavior), which in the compiled reference reads the linker's neighbors in `__TEXT,__cstring` (`"Auto RTL\0Auto\0FORMAT_VERSION\0..."`).
  Fixed by configuration (Vehicle.json `string_pool`, cpp2lean_mem.py `macho_section`): the reference binary's merged
  `__cstring` section (30,457 bytes) is placed whole as constant data of the memory image and every literal of the code
  that is a whole string of it takes its address there; literals the section does not have are placed as before. This is
  a compilation assumption taken from the reference build, like clang's record layouts: the linker's layout of the string
  literals (listed below as a deviation).

### Item 2: the scenario suite (`sim/scenarios.py`; sim/README.md "The scenario suite")

Six sessions, recorded with `copter_ref` by new scripts of `fly_reference.py` (harness code: `SCENARIOS`, and in
`lockstep_gcs.py` `command_int` and the scenario inputs `rc`, `rc_off`, `bat` for the sensor layer; the flight script's
lines are unchanged): loiter (LOITER with sticks, LAND), brake (GUIDED toward a point, BRAKE, ALT_HOLD with sticks, LAND),
rtl (RTL from 12 m), guided (DO_REPOSITION, CONDITION_YAW, DO_CHANGE_SPEED, a velocity target, NAV_LAND), battery (the
battery reading dropped to 10.2 V: battery failsafe, LAND), prearm (arming refused with its texts, an arming in STABILIZE
and the auto-disarm, the radio failsafe in flight, LAND). The battery voltage and a silent receiver are inputs of the
protocol line, so no injection mechanism was needed. Each is 66-80 s simulated, not 60: EKF3 uses GPS at 41.8 s on every
session from this storage image, and the vehicle cannot arm in a position mode before that.

What the suite reached that the mission flight did not, and what was done:
- `GCS_MAVLINK_Copter::handle_message_set_position_target_local_ned`, `..._global_int` and `handle_message_set_attitude_target`
  were boundary no-ops of Vehicle.json (brake, rtl and guided diverged at line 20,014, one PWM count: the GUIDED target was
  never set). Now translated; their namespace-scope `constexpr` masks (GCS_MAVLink_Copter.cpp:868-888, folded by clang) are
  configuration constants with their values from MAVLink's common.h.
- `handle_command_int_do_reposition`, `handle_MAV_CMD_CONDITION_YAW`, `handle_MAV_CMD_DO_CHANGE_SPEED` were `unreached`
  (guided). Now translated, with the command handlers a ground station commonly sends: `handle_set_mode`,
  `handle_command_get_home_position`, `handle_command_request_autopilot_capabilities`, `handle_command_pause_continue`,
  `handle_command_do_set_roi`, `handle_command_do_set_roi_location`, `handle_command_do_set_mission_current`,
  `handle_command_run_prearm_checks` (not all exercised by the suite).
- `AP_AHRS::pre_arm_check` (prearm: the reference's `Arm: AHRS: not using configured AHRS type` at line 1,214): item 3.
- loiter and battery were identical from the start (LOITER, LAND, the battery failsafe and its texts, the land detector).

Mutation check (code only rtl reaches): in an APFS copy of `lean/`, `ModeRTL::hold_at_return_point_run`'s
`hold_elapsed_ms >= RTL_LOIT_TIME` changed to `>= RTL_LOIT_TIME + 500`, `lake build vehicle_replay` there, then
`python3 sim/scenarios.py --only rtl,loiter --exe <copy>/lean/.lake/build/bin/vehicle_replay`:
`rtl: DIFF replay: PWM 27965 of 32013, down 31945, tasks 32013 of 32013, storage 0 bytes differ; first PWM difference (26999, '67497500', ...)`;
`loiter: ok` (unchanged). The copy was deleted afterwards.

The suite is not added to `tests/run_tests.sh`: the tests delete `lean/.lake/build`, and building `vehicle_replay` again
takes about 13 minutes, over the 5 minutes allowed; `python3 sim/scenarios.py` is the one command (about 2 minutes for the
six replays, 6 more with `--live`).

### Item 3: pre-arm checks and estimator answers

See "Phase 5d: pre-arm checks in the World" below: `AP_AHRS::pre_arm_check` (with the EKF3's pre-arm text),
`AP_Baro::arming_checks`, `AP_GPS::pre_arm_checks`, `AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz` translated
through a `char *` text sink of the value translator (`CText`); `get_filter_status_for_configured_backend` adapted (the
union's word); `active_backend_configured_to_use_gps`, `body_to_earth2D_p`, `broadcast_first_configuration_failure_reason`,
`get_output_banner`, `AP_RTC::get_time_utc` added to the World. Still answered by default: `Compass::configured` (it
formats with the C library's `snprintf`, D10), `Compass::per_motor_calibration_update/end` (rejected),
`AP_InertialSensor::periodic` (no effect in the World's model), `set_imu_out_uart` (not reached in this configuration).
`AP_Notify::update` stays a stub: its effects are the notify devices' `update` and the reset of `AP_Notify::events`, which
only the devices read; no PWM, downlink or storage output depends on it here (source reading, not shown by translation).

### Item 4: speed (D16)

Profile of the recorded flight's replay (`VEHICLE_REPLAY_STEPS=FILE`, new: per main-loop step the lines consumed and its
time; `build/p5d/prof/stepprof.py`; `EST_BENCH_DUMP=FILE` for `estimation_replay.py --bench`, new: the World alone per
step; `sample` of the replay for 12 s):
- The slowest 1 percent of steps fall on three lines of every 80 (lines 6, 11 and 51 modulo 80: 5 Hz and 10 Hz, the
  EKF3's measurement fusions), mostly in flight. On those lines the World alone (the estimation replay of the same
  flight) takes 1.85 ms on average (EKF3 fusion through AP_AHRS::update); the whole vehicle's step there is 1.3 ms more,
  against 0.53 ms more on an average step. 231 of the 351 slowest steps run only the 400 Hz tasks; the scheduler's slower
  tasks are not the cause.
- Whole run (`sample`, 9,646 samples of the main thread): AP_AHRS::update (estimator) 25 %, the memory side 65 %
  (translated vehicle code, its records' allocation and freeing: `lean_dec_ref_cold` 13 %), FloatLib's software floats
  about 7 % (of which the Binary64 add and multiply fall back to a path that parses a big natural number constant with GMP
  on every call, `__gmpz_set_str` 1.7 %); the HAL harness 5 %: `readLine` copied the array of all input lines' times on
  every line (`sn 8 ((← gn 8).push t)`: the state still held the array), which grows to 36,013 entries.
- Fixed: the HAL's slot arrays are changed in place (`modN`, `Array.modify`; hand-written HAL). Replays identical. Mean
  per step on the same (loaded) machine 703 -> 628 µs, p99 2,789 -> 2,624 µs.
- Not reached: p99 under 2.0 ms live. The remaining cost of the slowest steps is the EKF3's fusion in the World (FloatLib
  Binary64 and Binary32 in software) plus the memory side's records; a fast path for FloatLib's Binary64 fallback
  (`@[csimp]` with a complete proof) is the next candidate, not attempted in this phase.
- Measurements: the machine was not quiet during this phase (a user's game at 70-90 % of one core from about 09:35 and
  under memory pressure), so the absolute figures are higher than Phase 5c's (0.58 ms mean, 2.38 ms p99 in a quiet run).
  Final figures (one run each after the final build, the machine quiet again): the recorded flight's replay mean 0.60 ms, p99 2.43 ms, max 35.2 ms per step (5c: 0.58, 2.38, 34.9); the QGroundControl session's replay 0.46, 1.69, 33.9 ms; the closed-loop flight through the pipe (`lean_vehicle.py`) mean 0.63 ms, p99 2.49 ms, max 43.4 ms, 3.2 times real time (5c: 0.67, 2.49, 44); the six scenario replays mean 0.49-0.53 ms, p99 2.32-2.39 ms.

### Item 5: a live QGroundControl session with the translated vehicle

`sim/run_qgc_reference.py --vehicle lean` runs `fly_reference.py --udp --bin sim/lean_vehicle.py` (sim/README.md, "A live
QGroundControl session with the translated vehicle"); `--gcs scripted` uses the new `sim/udp_gcs_check.py` (pymavlink on
QGroundControl's UDP port) instead of QGroundControl. Tested only that way (QGroundControl was not started):

```
$ build/reference/venv/bin/python sim/run_qgc_reference.py --vehicle lean --gcs scripted --seconds 8 --out build/p5d/udp_lean
scripted GCS on udp 127.0.0.1:14550 for 6.5 s: vehicle at ('127.0.0.1', 61732)
heartbeats received: 7 (first after 0.34 s); last: custom_mode 0, system_status 3, base_mode 81
PARAM_REQUEST_LIST sent at 0.34 s; PARAM_VALUE received: 310 (vehicle's count 781); first: FORMAT_VERSION=120, ...
STATUSTEXT: ['ArduCopter V4.8.0-dev (802db19d)', 'cpp2lean-lockstep', 'Frame: QUAD/X', 'EKF3 IMU0 initialised', ...]
```

The session's recording (`build/p5d/udp_lean/harness`, 4,280 lines) replayed through `copter_ref` gives outputs
`cmp`-identical to the translated vehicle's. The command for a session with QGroundControl by hand:
`build/reference/venv/bin/python sim/run_qgc_reference.py --vehicle lean --seconds 120 --out sim/out/lockstep-qgc-lean`.

### What was translated or changed (Phase 5d)

| where | change |
|---|---|
| cpp2lean_mem.py | `string_pool` / `macho_section` (the reference binary's `__cstring` section as the literals' layout); a HAL call's reference arguments by address; (item 3) `%ctext`, `%textsink` drain forms |
| cpp2lean.py | (item 3) `CText`, `--text-results`, `char` member buffers, `AP_DAL::snprintf`, the `text_sink` output |
| ardupilot/vehicle/Vehicle.json | `string_pool`; the three SET_POSITION_TARGET/SET_ATTITUDE_TARGET handlers no longer boundary; 11 command handlers no longer `unreached`; 12 constants (the `MAVLINK_SET_POS_TYPE_MASK_*`); (item 3) `world_outputs` forms |
| ardupilot/estimator.use, ardupilot/translate_estimator.sh, ardupilot/vehicle/gen_bridge.py | (item 3) see below |
| lean/VehicleReplay.lean (HAL, hand-written) | `get_system_id_unformatted`, `power_status_flags`; `modN` (slot arrays in place); `VEHICLE_REPLAY_STEPS` |
| sim/fly_reference.py, sim/lockstep_gcs.py, sim/scenarios.py (new), sim/udp_gcs_check.py (new), sim/run_qgc_reference.py, ardupilot/vehicle/vehicle_replay.py (`--est`), ardupilot/estimation_replay.py (`EST_BENCH_DUMP`) | harnesses |
| tests/golden/ardupilot/Estimator_lib.lean | updated on purpose (item 3's World translation) |

Translation sizes: Vehicle_lib 2,418 functions translated and 5 stubs, 60,617 Lean lines (59,670 after 5c); Estimator_lib
29,278 lines (28,630); VehicleBridge 1,931 lines (1,882). The full regeneration (`build/p5d/regen.sh`: the two
translations, the parameter harness, the bridge, the copies, `lake build vehicle_replay onestate_replay estimation_replay`)
took 29 minutes.

### Still boundary, recorded, hand-written or deviating

- Recorded frames: none (as 5c).
- Answered by default: `Compass::configured` (true), `Compass::per_motor_calibration_update/end`,
  `AP_InertialSensor::periodic`, `set_imu_out_uart` (item 3). The five passing checks of 5c are now translated except
  `Compass::configured`.
- Stubs, called at run time (Phase 5: correction: the Phase 5c summary said they were not called; the replay's
  `# unreached=` line lists them on every session): `AP_Param::convert_g2_objects`, `convert_toplevel_objects` (no old
  parameters in these images: the reference makes no change there), `AP_Notify::update` (50 Hz). Not called:
  `AP_BoardConfig::allocation_error`, `throw_error`.
- Hand-written: the HAL (`lean/VehicleReplay.lean`, now with `get_system_id_unformatted`, `power_status_flags`, `modN`),
  the memory runtime (`support/*.lean`), the bridge's accessors, `sitl`, `create_view`, `get_earth_field_ga`, `handle_msg`,
  the World's scheduler stand-in, the harnesses (listed in the table).
- Deviations: the C string literals at the reference binary's linker layout (`string_pool`, above); a World call that runs
  out of lines is repeated, `AP_AHRS::update`/`reset` are not (as 5c); the INS stored-id flags from est.txt's header (as
  5c); a `char *` sink reproduces the last formatted text only (bytes after its NUL may differ from C; no reader in these
  paths looks past it).
- Workspace note: `build/param-memory-cache`'s AST and IR entries name sources under the deleted clones `build/p5b`,
  `build/p5c` and `build/p5s2`; after their deletion the vehicle translation silently lost 91 functions. Those three
  directories now hold only links to the main workspace's `build/reference` and `reference/` (and a README.txt); do not
  delete them, or rebuild the cache.

## Phase 5d: pre-arm checks in the World (item 3: the `char *` text sink, 2026-11-13)

The estimator functions with a `char *buf, <int> len` failure message, which the bridge answered by hand (`true`, the
text not written), are translated in the World; `AP_AHRS::get_filter_status_for_configured_backend` is adapted.

- **The text value** (cpp2lean.py `--text-buffers`): a `char` buffer is a `CText` (an inductive of the World's prelude):
  `none` (never written: a zero-filled buffer's empty string, or a caller's buffer left as it was), `fmt size fmt args`
  (the last `snprintf(buf, size, fmt, args...)` into it, arguments tagged as for `--text-log`), `text size src args` (the
  same with the text of the buffer `src` as the format), `null` (a null `const char *`). Before (Phase 5c) the value was
  the tuple `(size, fmt, args)`; `Output.send_text_snprintf` now carries the `CText`.
- **Writes**: `hal.util->snprintf` and (new) `dal.snprintf` (AP_DAL::snprintf is `hal.util->vsnprintf`, as
  AP_HAL::Util::snprintf), into a local buffer, a `char *` parameter or (new) a `char buf[N]` data member
  (NavEKF3_core::prearm_fail_string; the `--drop`s of AP_DAL::snprintf and of the member are gone); a buffer passed on to a
  callee's `char *` parameter is passed and returned (Phase 5c).
- **Reads**: `--text-results NavEKF3_core::prearm_failure_reason`: a `const char *` member function returning a text
  member or `nullptr` returns a `CText` (`CText.null`); the local it initializes is a `CText`, compared with `nullptr`
  by `CText.isNull`; `dal.snprintf(failure_msg, failure_msg_len, failure)` (AP_NavEKF3.cpp:1202) is
  `CText.text len failure #[]`: the format is the formatted text of the member, not a guess about it. Reading a `char *`
  parameter's incoming text (as a format or a sent text) is rejected: the caller's bytes are not in the World.
- **The sink**: the bridge's adapter of a World function with a `char *` parameter passes `CText.none`, and after the call
  pushes `Output.text_sink buf text` (a constructor the World declares for its `char *` parameters); the vehicle's drain
  (Vehicle.json `world_outputs`, `%textsink`) formats the text into the caller's buffer with the translated
  AP_HAL::Util::snprintf (`worldOutputs'ctext`: C truncation at the call's size; a `text` format formatted first into a
  zero-filled buffer of the drain's frame; `none` writes nothing; `null` is recorded as unreached), then the caller goes on
  (the drain runs right after every bridge call). `%ctext` does the same for `send_text_snprintf`.
- **Translated** (estimator.use): `AP_AHRS::pre_arm_check` (with `attitudes_consistent`, `set_failure_inconsistent_message`,
  AP_AHRS_NavEKF3/NavEKF3/NavEKF3_core/AP_NavEKF_Source `pre_arm_check`, `prearm_failure_reason`, the EKF3's
  `prearm_fail_string` writes), `AP_Baro::arming_checks`, `AP_GPS::pre_arm_checks`,
  `AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz`, `AP_AHRS::active_backend_configured_to_use_gps`,
  `AP_AHRS::body_to_earth2D_p`, `AP_GPS::broadcast_first_configuration_failure_reason`,
  `AP_InertialSensor::get_output_banner`, `AP_RTC::get_time_utc`.
- **gen_bridge.py**: `nav_filter_status &` (a union of the bit-field struct `flags` and `uint32_t value`, which the World
  holds as its word): the memory's `value` leaf (offset 0, the whole record) loaded and stored back; `size_t` to the World's
  `USize`.
- **Still answered by default** (`not_in_world`): `Compass::configured` (it formats with the C library's `snprintf`, not
  ArduPilot's formatter: D10, the C library's formatter is not translated), `Compass::per_motor_calibration_update/end`
  (rejected: Compass_PerMotor.cpp:148 uses the back-reference `compass` other than reading a value),
  `AP_InertialSensor::periodic` (the World's translation finds it has no effect in the model: not emitted, so the
  default `()` is its effect), `AP_InertialSensor::set_imu_out_uart` (a UART pointer from the memory to a World object;
  reached only for a serial port with protocol 46, not configured).

Results (clone build/p5d_pre, one run each): `python3 sim/scenarios.py` all six scenarios ok (prearm: PWM, down, tasks
26413 of 26413, storage 0 bytes differ; the reference's `Arm: AHRS: not using configured AHRS type` at line 1214 is now
the World's text); `vehicle_replay.py sim/out/lockstep-flight` PWM, down bytes, tasks identical on 36013 of 36013, storage
0 differ; `onestate_replay.py` estimation values different: 0. AP_Notify::update (a stub on the memory side): its effects
are the devices' `update` and the reset of `AP_Notify::events`, which only the notify devices read (grep of ArduCopter
and libraries); no output of the replays (PWM, downlink, storage) depends on it in this SITL configuration (not
translated, not proven by translation).

## Phase 5c summary (downlink identity, World waits interleaved, the closed loop, 2026-11-13)

PORT-PLAN.md section 6, "Phase 5", the Phase 5c brief: (1) the downlink identical with no frame taken from the recording
(text formatting D10, the 64 content senders, the boot interleaving), (2) the translated whole vehicle flown live in the
gym-pybullet-drones lock-step loop that recorded `sim/out/lockstep-flight`. Work split: three agents in APFS clones
(`build/p5c_fmt`: varargs, the formatter, STATUSTEXT; `build/p5c_snd`: the content senders; `build/p5c_w2`: the GPS
probing text and the swap-out miss), merged by the orchestrator, who did the World-wait interleaving, the live loop and
the last fixes; everything was regenerated in the main workspace from the merged sources.

Results (main workspace, release build, one run each, no Lean build running):

```
$ LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight
# step_us mean=577.979195 p99=2381.083000 max=34929.833000 n=35098   (build/vehicle_replay/tasks.txt)
PWM identical on 36013 of 36013 lines; down bytes identical on 36013; both on 36013; boot (init, 915 lines) both identical on 915
first PWM difference: None
first down difference: None
tasks identical on 36013 of 36013 steps (tick identical on 36013)
tasks by scheduler tick: 35098 ticks compared, 35098 identical; first difference: None
storage at the end: 16384 bytes, 0 differ from the reference's
$ LEAN_NUM_THREADS=1 python3 ardupilot/onestate_replay.py sim/out/lockstep-flight
gcs replay sim/out/lockstep-flight: 36013 steps, 35443 steps whose frames are all equal
recorded frames 7304 (247159 bytes; + 76 console bytes not compared): equal 70 (translated 44, boundary 26), different 5885, missing or extra 1367; equal bytes 2575
parameter download by index: recorded 781 indices (count [781]), translation 781 (count [781]); equal (name, value, type, count) 781
storage at the end: mission areas 9758 bytes, 0 differ (...); outside them 0 bytes differ
estimation replay lockstep-flight: ... values compared: 8439007, equal: 8439007, different: 0; 0 steps differ
$ export LEAN_VEHICLE_OUT=$PWD/build/p5c_live_flight2/lean
$ build/reference/venv/bin/python sim/fly_reference.py --script flight --bin sim/lean_vehicle.py --storage build/reference/storage-cf2x.bin --out build/p5c_live_flight2
end: script finished
steps: 36013 (90.03 s simulated), wall 28.55 s (3.2x real time), simulator 3.72 s
vehicle exit code 0
events: 1.00 heartbeat; 17.73 parameters downloaded: 781 in 16.73 s; 41.81 EKF3 using GPS; 41.83 mission uploaded: 6 items; 41.85 mission downloaded: 6 items; 41.85 mode GUIDED; 42.03 armed; 48.88 reached 4.5 m in GUIDED; 48.88 mode AUTO; 88.03 disarmed
inputs.txt  recorded 36013, live 36013, equal 36013, first difference: none
outputs.txt recorded 36013, live 36013, equal 36013, first difference: none
```

Every downlink byte of the recorded flight now comes from translated code: no recorded frame is loaded (the content
senders, STATUSTEXT and the estimator's senders were the recorded ones in 5b), the boot is identical on all 915 lines
(878 in 5b), and the whole downlink on all 36,013 lines (35,771 in 5b). The vehicle per 400 Hz step: mean 0.58 ms, p99
2.38 ms, max 35 ms (the max is a step of the boot calibrations; 5b: 0.50, 2.29, 34 ms); runs with a Lean build on the same
machine measured p99 2.45-2.49 ms. The estimation replay stays at 0 of 8,439,007 different.

Translation sizes after the merge: Vehicle_lib 2,366 functions reached (5 stubs, none called on the flight), 59,670 Lean
lines (51,038 in 5a, 52,088 before 5c); Estimator_lib 28,630 Lean lines (27,991 before 5c); VehicleBridge 171 adapters (151
generated, 10 by hand, 14 not in the World), 1,882 lines. The full regeneration (`ardupilot/translate_estimator.sh`,
`ardupilot/vehicle/translate_vehicle.sh`, `PARAM_HARNESS_TARGET=vehicle python3 ardupilot/param/gen_param_harness.py
sim/out/lockstep-flight/est.txt`, `python3 support/gen_param_memory_v.py --memory --bridge`, `python3
ardupilot/vehicle/gen_bridge.py`, the copies into `lean/`, `cd lean && LEAN_NUM_THREADS=1 lake build vehicle_replay
onestate_replay estimation_replay`) takes about 25 minutes.

Mutation check (item 1's formatter): in an APFS copy of `lean/` (`build/p5c_mut/lean`), the decimal digit base of the
translated `ultoa_invert` (utoa_invert.cpp, `'0' + digit`) changed from 48 to 49, `lake build vehicle_replay` there, then
`LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight --exe
build/p5c_mut/lean/.lake/build/bin/vehicle_replay --out-dir build/p5c_mut/out --compare-with build/vehicle_replay/outputs.txt`:
`down bytes identical on 35998` (36,013 unmutated), boot 914 of 915, PWM, tasks and storage unchanged, `15 of 36013
output lines differ; first at line 704` (the STATUSTEXT "Barometer 1 calibration complete" becomes "Barometer 2 ...": every
`%u`/`%d` digit of a text is one higher). The two agents' clones had each also run one (the same digit base; `vx*100` to
`vx*101` in `GCS_MAVLINK::send_global_position_int`: 52 lines' down bytes differ).

Tests: `LEAN_NUM_THREADS=1 bash tests/run_tests.sh` once after the last change: 174 ok, 0 FAIL, "all tests passed". Goldens
updated on purpose: `tests/golden/ardupilot/Estimator_lib.lean` (the World's text, console, buffer-text, MAVLink-send and
lock-step-mark events, the added getters and senders, `--member-reach`'s two lines, `EST_MARKS` in the scheduler stand-in),
and `EstScheduler_lib.lean`, `Estimation_lib.lean`, `Sensors_lib.lean` (only the line numbers of
`reference/hal/est_scheduler.cpp` in their doc comments: their translations do not define `EST_MARKS`, so their code is
unchanged). GCS_lib and AP_Param_lib translate byte-identically (the new keys are off without Vehicle.json).

### Item 1a: text formatting (D10) and STATUSTEXT from the translation

- **C varargs in the memory back end** (cpp2lean_mem.py key `varargs`, Vehicle.json only): Apple arm64's model. A variadic
  definition gets a hidden last parameter `va'`; the caller writes each extra argument after clang's default promotions into
  its own 8-byte slot of a block in its frame (`va_block`: integers sign- or zero-extended, `double` as its bits, pointers
  as addresses; a record argument is rejected); `va_start(ap, x)` stores `va'` into `ap`; `va_arg(ap, T)` reads T at `ap`
  and stores `ap + 8`; `va_copy` copies, `va_end` nothing. Before, extra arguments were dropped (`AP_Arming::check_failed`'s
  `va_list` was an uninitialized local); now they are evaluated (e.g. `AP_Arming::compass_checks` calls
  `Compass::get_first_usable`).
- **ArduPilot's formatter translated**: `AP_HAL::Util::snprintf`, `vsnprintf` (Util.cpp:18-71, with `BufferPrinter`),
  `print_vprintf` (print_vprintf.cpp:74-540, 724 Lean lines), `ftoa_engine` (174), `ultoa_invert`/`ulltoa_invert` (65 each);
  `hal.util->snprintf/vsnprintf` are `hal_translated` (no longer HAL hooks; `this` 0: neither reads Util state); the gotos
  of print_vprintf and ftoa_engine go through cpp2lean.py's GotoRewriter (`goto_rewrite`, also turning
  `AP_Mission::distance_to_mission_leg` from a stub into code); `s->write(c)` dispatches to `BufferPrinter::write`
  (`hal_dispatch`).
- **The C library's `snprintf` (musl)**: not translated, because no translated function reaches it (a call would be
  rejected and listed in the survey; the survey lists none). The only C-library formatting call reached is `vprintf` in
  `AP_BoardConfig::throw_error`, a stub never called at run time. `hal.util->vsnprintf` stays ArduPilot's own formatter, a
  distinct function, as D10 requires.
- **The World's texts**: `cpp2lean.py --text-log` makes `GCS::send_text(sev, fmt, ...)` in World code an
  `Output.send_text sev fmt args` event (38 sites: EKF3, AP_Baro, AP_GPS, AP_AHRS; arguments tagged: a 64-bit slot or a
  string) and `hal.console->printf(fmt, ...)` (DEV_PRINTF: "Init Gyro", "*", "\n" of `AP_InertialSensor::_init_gyro`) an
  `Output.console_printf` event; `--text-buffers` makes `AP_GPS_Backend::_detection_message`'s `char buffer[51]` filled by
  `hal.util->snprintf` and sent with `"%s"` an `Output.send_text_snprintf` event. The bridge's drain lays the format and the
  slots out in a frame of the drain and calls the translated `GCS::send_text` (formatted by the translated `print_vprintf`),
  formats a buffer text with the translated `AP_HAL::Util::snprintf` (C truncation at the buffer's length) first, and
  passes console texts to the HAL's console `printf` (as the vehicle's own console texts).
- **STATUSTEXT**: `GCS::send_text`, `GCS_MAVLINK::send_text`, `GCS::service_statustext`, `send_banner` (both) translated;
  the recorded STATUSTEXT path is gone from the replay (`textQuota`, `tq`).

### Item 1b: the content senders

- All 64 senders of GCS.json's `PMem.bframe` list are translated and enabled (38 reached on the memory side; 23 never called
  in this configuration: their call sites are compiled out or Copter's override is the translated one). The estimator
  classes' own senders (`AP_AHRS::send_ekf_status_report`, `AP_GPS::send_mavlink_gps_raw`/`gps2_raw`, before hand-written
  adapters writing recorded frames) are translated in the World: `cpp2lean.py --output-fn` makes their
  `mavlink_msg_*_send` calls `Output` events, replayed by the drain as calls of the translated MAVLink library on the link's
  channel (`link.get_chan()` a World input set from the translated `GCS_MAVLINK::get_chan`).
- Getters added to the World (`ardupilot/estimator.use`): AP_AHRS `airspeed_vector_TAS`, `get_error_rp`, `get_error_yaw`
  (with AP_AHRS_DCM's), `get_pos_vel_uncertainty` (NavEKF3/NavEKF3_core `getPosVelUncertainty`),
  `get_relative_position_NED_origin_float`, `get_secondary_estimates`, `get_wind`, `get_yaw_deg`, `groundspeed`;
  `AP_Baro::all_healthy`, `AP_GPS::get_undulation` (both), `AP_InertialSensor::get_temperature`, `AP_RTC::get_utc_usec`;
  the field `AP_AHRS::yaw_sensor` through `bridge_field_reads`. The RTC: the World's `set_utc_usec` (from AP_GPS) and the
  new `get_utc_usec` give SYSTEM_TIME's `time_unix_usec`.
- **Truncated payloads**, two causes: (1) clang's `-fdump-record-layouts` prints MAVPACKED message structs at their
  unpacked layout (`__mavlink_gps_global_origin_t`: `time_usec` at 16, sizeof 24; compiled: 12, 20): Vehicle.json
  `packed_records` (`^__mavlink_\w+_t$`) lays them out packed (`repack_layout`); (2) getters missing from the World
  answered 0 and MAVLink 2's translated `_mav_trim_payload` trimmed the zeros (it agrees with the C library): fixed by the
  getters.
- `bridge_pointer_results`: a `const T *` into the World (`AP_AHRS::get_secondary_estimates`) is copied at clang's layout
  into a temporary of the caller's frame.

### Item 1c: the World's waits interleaved with the vehicle

Before (Phase 5a/5b), the World was fed 1,000 lines ahead and a wait inside World code (`ins.init`'s gyro calibration,
`barometer.calibrate`, `wait_for_sample`) consumed its lines in the World; the memory side caught up afterwards, at the next
HAL call or at the end of `setup()` (each line's output, uplink, IO processes and one delay callback). That order is not the
reference's (lockstep.cpp runs the vehicle's part of each line inside the wait), and it needs the input lines ahead, which a
closed loop does not have. Now the World is never fed ahead and its waits are interleaved:

- `reference/hal/est_scheduler.cpp` (the World's scheduler stand-in, hand-written HAL; under `EST_MARKS`, which only
  `ardupilot/translate_estimator.sh` defines, so the other translations of the file are unchanged in code) marks the
  lock-step points as events of the translation (`est_mark`, `cpp2lean.py --output-fn`): kind 0 a line consumed, kind 1 its
  timer processes run, kind 2 a `delay` iteration with its remaining time (lockstep.cpp's delay-callback rule), kind 3 the
  records ran out. Out of records, `step()` goes on with synthetic lines (the last samples, one step period apart), so that a
  call whose result is discarded ends.
- The adapters of the World functions that may wait (`gen_bridge.py may_wait`: the Lean call graph to `EstScheduler.step`;
  `AP_Baro::calibrate`, `AP_InertialSensor::init`, `update`, `wait_for_sample`, `Compass::init`) call the World on a copy
  of the state; when the call ran out of lines, the state is set back to before the call, the driver runs the call's events
  up to that point (the reference's, at their lines: saves, notifications, texts, MAVLink sends, and at each kind-1 point the
  vehicle's timer processes, failsafe and IO processes, at each kind-2 point the delay callback), emits the output line, reads
  and feeds the next input line (`cpp2lean::world_retry`), and the call is repeated. The events done are dropped from the
  call that completes. `AP_AHRS::update`/`reset` reach a wait only through the DCM's gyro re-initialization: not repeated, a
  wait there is reported in the replay's log (none on the recorded flight).
- The HAL's own waits (`delay`, `delay_microseconds` outside the World) read the next line and step the World once; the
  step's events run the vehicle's part.
- The same code runs on a recorded session (lines from a file) and live (lines from standard input, `LINES` = `-`): the
  replay is the closed loop's behavior on the recorded inputs.

- **The swap-out miss**: `cpp2lean.py --member-reach`: a call on a member object (`ekf3.resetHeightDatum()` through the
  member-pointer match) adds the callee's reached World objects to the caller's, so `AP_Baro::update_field_elevation` writes
  its state into the World before `AP::ahrs().resetHeightDatum()` and reads it back after (2 lines in the World's Lean): the
  extra BARO1_GND_PRESS PARAM_VALUE at line 5,794 is gone.
- **Parameters that read 0**: AP_CANManager's `CANIface_Params`/`CANDriver_Params` array elements were constructed member by
  member (their inline user-provided constructors, `setup_object_defaults`, were never found by name): Vehicle.json
  `ctor_from_class` takes a default constructor from the class's declaration (CAN_D1_PROTOCOL/CAN_D2_PROTOCOL 1). AP_RTC's
  parameters (BRD_RTC_TYPES, BRD_RTC_TZ_MIN) have their home in the World now (`gen_param_harness.py`: the object
  `BoardConfig.rtc`, two paths the probe does not list), as the other estimator objects'.
- **SERIAL3's baud rate**: `AP_SerialManager::UARTState::baudrate` is translated (GCS.json answered 115200); the HAL's
  `UARTDriver::begin` on SERIAL3 (the GPS's port) sets the World's port stand-in (`EstUART`), the same unconnected port
  AP_GPS reads its first probe baud from ("GPS 1: probing for SITL at 230400 baud").
- `AP_AHRS::pre_arm_check` stays one of the bridge's passing checks (not attempted: the `char *` sink).

### Item 2: the closed loop

`sim/lean_vehicle.py` (harness) is a vehicle binary for `sim/fly_reference.py` (`--bin`): it starts
`lean/.lake/build/bin/vehicle_replay` with LINES `-` (live mode: input lines from standard input, output lines written and
flushed when the next line is needed, as lockstep.cpp's `emit_output` before `getline`), converts each protocol line to the
driver's tokens exactly as `vehicle_replay.py` does, and passes the output lines back. The simulator, the sensor layer and
the scripted ground station are fly_reference.py's, unchanged; the same storage image as the recorded flight.

The closed-loop flight (the second: the first, before the last fixes of item 1c, completed the same mission with all
36,013 input lines equal and 36,009 output lines equal, the four differences being the downlink lines item 1c then fixed:
the GPS probing baud at line 922 and three PARAM_VALUE defaults at lines 2,973, 3,053 and 3,093) is the recorded flight:
the simulator is deterministic, so with identical outputs every input line is identical too. The ground station's script
ran to its end (arm, takeoff to 4.5 m in GUIDED, AUTO through waypoint, spline waypoint and land, disarm at 88.03 s), at
3.2 times real time (the translated vehicle 0.65 ms per step through the pipe, mean; lockstep timing p99 2.48 ms).

### What was translated or changed (Phase 5c)

| where | change |
|---|---|
| cpp2lean_mem.py | `varargs` (C varargs on the byte memory, Apple arm64's model: a hidden `va'` parameter, one 8-byte slot per argument after the default promotions, `va_start`/`va_arg`/`va_copy`/`va_end`); `goto_rewrite` (cpp2lean.py's GotoRewriter on bodies with a `goto`: print_vprintf, ftoa_engine, AP_Mission::distance_to_mission_leg); `hal_dispatch` (`BetterStream::write` -> `BufferPrinter`); `hal_translated` (`AP_HAL::Util::snprintf`/`vsnprintf` translated, not HAL); `packed_records`/`repack_layout` (MAVPACKED message structs at their packed layout: clang's layout dump shows them unpacked); `bridge_pointer_results` (a `const T *` into the World copied to a temporary); `world_outputs` forms `%text` (a World text: format and tagged arguments laid out in a drain frame), `%snprintf` (a World text formatted into a buffer by the translated `AP_HAL::Util::snprintf`), `&{k}` (a record argument), `%hal` (an event for the harness), `%console` (a World console text to the HAL's console) |
| cpp2lean.py | `--text-log` (`GCS::send_text` and `hal.console->printf` in World code are `Output` events with their format and tagged arguments), `--text-buffers` (a `char buf[N]` filled by `hal.util->snprintf` and sent with `"%s"`), `--enum-as-int`, `--output-fn` (free functions whose calls are `Output` events: the estimator classes' MAVLink sends, the scheduler's lock-step marks), `--member-reach` (a call on a member object adds the callee's reached World objects: the swap-out miss of `AP_Baro::update_field_elevation`); Lean string escapes `\xHH`/`\uHHHH` (`\u{..}` is not Lean syntax) |
| reference/hal/est_scheduler.{h,cpp} (hand-written HAL stand-in, translated) | under `EST_MARKS` (translate_estimator.sh only): `est_mark` lock-step points; synthetic lines when the records run out, and waits that go on over them |
| ardupilot/translate_estimator.sh, ardupilot/estimator.use | the options above; `GCS::send_text` and `AP_GPS_Backend::broadcast_gps_type` no longer dropped; 16 getters and the three estimator senders added |
| ardupilot/vehicle/Vehicle.json | the 64 `bframe` entries, `send_text` (2), `service_statustext`, `send_banner` (2) and the va builtins removed from `boundary`; the keys above; `AP_HAL::UARTDriver::begin` a HAL call |
| ardupilot/vehicle/gen_bridge.py | the estimator senders generated (no longer hand-written recorded frames); `may_wait`/`wait_body` (the retried World calls) |
| lean/VehicleReplay.lean (HAL, hand-written) | no feed-ahead, no catch-up; `readLine` (lockstep.cpp's step, first half), the `est_mark` handlers (second half, delay callback), `cpp2lean::world_events`/`world_next`, live mode (`LINES` = `-`), `get_system_id`, SERIAL3's `begin` into the World's GPS port |
| lean/EstimationReplay.lean, lean/OneStateReplay.lean, ardupilot/vehicle/vehicle_replay.py (harnesses) | the new World signatures; no recorded frame passed |
| sim/lean_vehicle.py (new harness) | the translated vehicle as fly_reference.py's vehicle binary |

### Still boundary, recorded, hand-written or deviating

- Recorded frames: none. `vehicle_replay.py` passes no frames file (`-`); Vehicle_lib has no `PMem.bframe` or
  `PMem.statustexts` call.
- Passing checks (bridge): `AP_Baro::arming_checks`, `AP_GPS::pre_arm_checks`,
  `AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz`, `Compass::configured`, `AP_AHRS::pre_arm_check`. Not in the World
  (defaults): `AP_AHRS::active_backend_configured_to_use_gps`, `get_filter_status_for_configured_backend`,
  `AP_GPS::broadcast_first_configuration_failure_reason`, `AP_InertialSensor::get_output_banner`, `periodic`,
  `set_imu_out_uart`, `AP_RTC::get_time_utc`, `Compass::per_motor_calibration_*`.
- Stubs: `AP_Param::convert_g2_objects`, `convert_toplevel_objects`, `AP_Notify::update`, `AP_BoardConfig::allocation_error`,
  `throw_error` (none called on the flight).
- Hand-written: the HAL (`lean/VehicleReplay.lean`: lockstep.cpp's drivers, the console `cformat`, `get_system_id`, the
  lock-step handlers, live IO), the memory runtime (`support/*.lean`), the bridge's hand-written adapters (accessors, `sitl`,
  `create_view`, `get_earth_field_ga`, `handle_msg`), the World's scheduler stand-in (`reference/hal/est_scheduler.cpp`,
  translated), the harnesses (`vehicle_replay.py`, `sim/lean_vehicle.py`, `OneStateReplay.lean`, `EstimationReplay.lean`).
- Deviations: a World call that runs out of lines is repeated; between attempts the call's events run against the World as
  the attempt left it (after synthetic lines), and vehicle-side writes to the World during that work are lost (none on this
  flight); `AP_AHRS::update`/`reset` are not repeated (a wait there is logged; none on the flight). The INS stored-id flags
  are still read from est.txt's header (`vehicle_replay.py`; `sim/lean_vehicle.py` takes them as `LEAN_VEHICLE_INS`, default
  `1,1`, this storage image's).
- The one-state replay (`onestate_replay.py`) has no vehicle loop: with the senders translated its frames carry the
  one-state memory's content (no servo, RC, battery or mode state), so its GCS frame counts fell (equal 70 of 7,304 frames, 7,071 in 5b; 35,443 of 36,013 steps with all frames equal, 35,941 in 5b; the parameter download 781 of 781 and the storage 0 bytes differ as before; the QGroundControl session's,
`python3 ardupilot/onestate_replay.py sim/out/lockstep-qgc/harness build/gcs/qgc/est.txt`: 53,468 of 55,515 steps, 66 of
9,707 frames equal (55,336 and 8,903 in 5b), download 781 of 781, storage 0 differ, estimation 0 of 13,138,989 different,
first difference step 1,213, a HEARTBEAT whose content is the vehicle's). The one-state replay's GCS comparison needs the
vehicle's state to be meaningful again; the whole-vehicle replay is now the downlink's acceptance.; its
  comparison is unchanged and its estimation part is 0 different.

## Phase 5b summary (the vehicle, the recorded flight end to end, 2026-11-13)

PORT-PLAN.md section 6, "Phase 5", the Phase 5b brief: (1) the whole-vehicle replay identical, (2) the AP_Param save
queue and the home/origin pushes, (3) the downlink content, (4) speed. Result: the recorded flight's PWM and the
scheduler's tasks are identical on every line, the storage image at the end is identical, and the vehicle runs inside the
400 Hz budget (mean 0.50 ms, p99 2.29 ms); the downlink is not yet identical (item 3: the content messages are still recorded frames and the
texts are not formatted).

Acceptance (main workspace, release build, one run each):

```
$ LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight
vehicle_replay: 36013 lines, 35099 loops, 17.705993 s; step mean 500.833508 us p99 2289.584000 us max 33879.042000 us
PWM identical on 36013 of 36013 lines; down bytes identical on 35771; both on 35771; boot (init, 915 lines) both identical on 878
first PWM difference: None
tasks identical on 36013 of 36013 steps (tick identical on 36013)
tasks by scheduler tick: 35098 ticks compared, 35098 identical; first difference: None
storage at the end: 16384 bytes, 0 differ from the reference's
$ LEAN_NUM_THREADS=1 python3 ardupilot/onestate_replay.py sim/out/lockstep-flight
gcs replay sim/out/lockstep-flight: 36013 steps, 35941 steps whose frames are all equal   (5a: 35958; see below)
recorded frames 7304: equal 7071 (translated 610, boundary 6461), different 217, missing or extra 35
  GPS_GLOBAL_ORIGIN 2 of 2, HOME_POSITION 2 of 2 equal (boundary frames, now pushed by the translated AP_AHRS events)
parameter download by index: 781 of 781 equal
storage at the end: mission areas 9758 bytes, 0 differ; outside them 0 bytes differ
first difference: step 65 (BARO_ALT_OFFSET's PARAM_VALUE, now translated: the World's barometer calibration spans
lines 64-704 inside one estimator command of this replay, so its saves are written after it; the reference writes them at
lines 65 and 705)
estimation: values compared: 8439007, equal: 8439007, different: 0
```

`LEAN_NUM_THREADS=1 bash tests/run_tests.sh` after the last change: 174 ok, 0 FAIL, "all tests passed" (one golden
updated on purpose: `tests/golden/ardupilot/Estimator_lib.lean`, the World's save, notify and send events and the
`ap_message` enumeration). `LEAN_NUM_THREADS=1 bash ardupilot/vehicle/replay.sh`: 8431 of 8431 ticks bit-identical.

### Item 1: the boot gap and the spool-up (root causes)

- **Boot gap (4 lines).** `AP_GPS::init` (AP_GPS.cpp:322) calls `convert_parameters`, whose
  `AP_Param::convert_old_parameters_scaled` ends in `flush()` (AP_Param.cpp:2114, 1323-1335): `delay(10)` while the save
  queue holds a parameter. The queue held ESC_CALIBRATION, saved just before by `Copter::esc_calibration_startup_check`.
  Two configuration gaps hid it: Vehicle.json dropped `AP_Param::save` and answered `AP_Param::flush` with a no-op, and the
  World's translation drops `AP_GPS::convert_parameters` (`--drop`), so nothing ran it. Fixed: `save`, `flush` and the
  queue (`ObjectBuffer_TS<param_save>`) are translated; a new kind of bridge input (`pre_*`, Vehicle.json
  `bridge_inputs`) runs the memory's translation of `AP_GPS::convert_parameters` on the call's object before the World's
  `AP_GPS::init`.
- **No spool-up: four translator bugs** (cpp2lean_mem.py, all under the `vehicle` configuration), found with a
  layout-aware state comparison of `copter` and its heap objects against the reference at a given line (diagnosis tools:
  `build/p5b_diag/refdump.py` (lldb on `build/reference/copter_ref`), `VEHICLE_REPLAY_MEMDUMP=L1,L2,...`,
  `build/p5b_diag/statediff.py`):
  1. static locals of the same name in one function (`static const MotorDef motors[]` in each case of
     `AP_MotorsMatrix::setup_quad_matrix`, AP_MotorsMatrix.cpp:584ff) were all the first one: wrong motor factors. Now
     placed by clang's discriminated symbol (`..._0`, `..._1`; their demangled names are equal).
  2. `attitude_control_var_info = AC_AttitudeControl_Multi::var_info` (Copter::allocate_motors) resolved to
     `AP_MotorsMulticopter::var_info` (the `static_refs` key names the function and the member only): the ATC_
     parameters were never loaded from storage. Now the class qualifier is read from the expression's source range.
  3. enumeration constants whose declaration came from another unit's dump were found by name alone, which collides:
     `AP_Arming::Method::MAVLINK` was 3, the mode numbers wrong (AUTO 16, LAND 1, ...); 142 sites changed. Now by
     (qualified enumeration, name).
  4. a virtual function defined out of its class (`Mode::do_user_takeoff_start_m`, takeoff.cpp:11, declared `virtual`
     at mode.h:306, overridden by ModeGuided) was called directly: the definition's AST node has no `virtual`. Now the
     in-class declaration decides (the takeoff start, `requires_position`, `run`, `exit`, ... are dispatched).
  After 4, `AP_Arming_Copter::mandatory_position_checks` reaches `AP_AHRS::pre_arm_check`, which the World's
  translation rejects (`char *failure_msg`): it is now one of the bridge's passing checks (listed below). And the
  attitude controller read `_ahrs.yaw` of AP_AHRS_View directly, at the view's stand-in address (0): estimator data
  members read by translated code now go through generated adapters (Vehicle.json `bridge_field_reads`).
- **Mutation check** (`land_trigger_sec` of `Copter::update_land_detector`, LAND_DETECTOR_TRIGGER_SEC, 1 -> 2 s, in a
  copy of Vehicle_lib.lean built in `build/p5w`): PWM identical on 35,414 of 36,013 lines (36,013 unmutated), first difference at
  line 34,688 (the landing: `1029,1029,1000,1006` recorded, `1030,1030,1000,1007` mutated); tasks and storage unchanged.
  Command: `LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight --exe
  build/p5w/lean/.lake/build/bin/vehicle_replay --out-dir build/p5b_diag/mut` (the mutated copy built before the HAL
  clock change of item 3, so its down bytes are not comparable).

### Item 2: the save queue, home and origin

- AP_Param's `save`, `flush`, `save_io_handler` and the `ObjectBuffer_TS` ring are translated (the IO process registered
  by `AP_Param::setup` runs at lockstep.cpp's points); `GCS::send_parameter_value` is translated (it was a no-op), so
  `save_sync`'s and `notify`'s PARAM_VALUE notifications are the translation's.
- The World's side (cpp2lean.py `--param-save-log`, with `--output-log`): `AP_Param::save` (also inside `set_and_save`
  and `set_and_save_ifchanged`) and `AP_Param::notify` (also inside `set_and_notify`) on a World parameter are
  `Output.AP_Param_save path force` / `Output.AP_Param_notify path` events, the path the parameter's C++ member path from
  its World object built at run time (`ins._gyro_offset_old_param[1]`); a method of a class with more than one object
  receives its object's path as a parameter `sp`. `--drop GCS::send_message` is gone: `GCS_SEND_MESSAGE(MSG_HOME)` and
  `(MSG_ORIGIN)` in AP_AHRS are `Output.send_message` events. Estimator_lib: 27,666 lines before, 27,991 after;
  estimation replay 0 of 8,439,007 different.
- The bridge replays them (cpp2lean_mem.py, Vehicle.json `world_outputs`): after every bridge call the generated
  `worldOutputs'drain` calls, per event, the translated `AP_Param::save`/`notify` on the parameter's address in this
  image (`PMem.Bridge.addrOfPath`, generated from `estimator_params.json`), `GCS::send_message`, and
  `AP_Mission::write_home_to_storage` (the event that already existed).
- Result: the storage image at the end equal to the reference's (0 bytes differ, in and outside the mission areas), in the
  whole-vehicle and the one-state replay; HOME_POSITION and GPS_GLOBAL_ORIGIN sent at the reference's steps (equal in both
  one-state replays; in the flight's, step 5,765 is no longer the first difference; in the QGroundControl session's the
  first difference is still at step 5,765, now a later frame of it: see below).

### Item 3: the downlink (not met)

Down bytes identical on 35,771 of 36,013 lines (35,264 at the start of 5b). Still recorded: the content messages
(`PMem.bframe`, 64 senders, GCS.json's list) and STATUSTEXT (the vehicle's and the World's texts are not formatted: D10
not done; `GCS::send_text` is still a no-op). What still differs:
- 23 STATUSTEXT frames (texts not formatted), and the sequence numbers of the frames after them (146 lines of the
  parameter download differ in their sequence number only);
- the World's boot saves (barometer calibration, the IMU's gyro calibration) are written at the first IO process after the
  World's delay returns, all at line 25, instead of at lines 65, 705 and 916 (the catch-up deviation of Phase 5a);
- a 1 Hz stream bucket sent at other lines than the reference's until line 6,653 (13 lines; boot timing, not located);
- TIMESYNC, MISSION_* and COMMAND_ACK frames that differ in their sequence number only.

**Content senders: tried, kept recorded.** Translating all 64 senders of GCS.json's list (in the clone `build/p5x`; it
needed three more translator fixes, listed in the table below) keeps PWM, tasks and storage identical. Per message
(payloads compared in order, `build/p5b_diag/msgcmp.py`): SCALED_PRESSURE, ATTITUDE, SERVO_OUTPUT_RAW, MISSION_CURRENT,
NAV_CONTROLLER_OUTPUT, RC_CHANNELS, POWER_STATUS, BATTERY_STATUS, MEMINFO, VIBRATION and POSITION_TARGET_GLOBAL_INT
give the reference's payloads wherever the reference sends them at the same line (the other 14 of each fall on the
boot-time bucket above, which the recorded frame misses too). HEARTBEAT matches on 90 of 94: at line 402 it reports
MAV_STATE_STANDBY instead of BOOT, a side effect of the boot catch-up. SYS_STATUS (the sensor health flags),
SYSTEM_TIME (no RTC time, since `AP_RTC::get_utc_usec` is not in the World), GPS_RAW_INT, RAW_IMU, VFR_HUD, AHRS, AHRS2,
LOCAL_POSITION_NED, WIND, EKF_STATUS_REPORT, GPS_GLOBAL_ORIGIN and HOME_POSITION differ or are not sent: estimator
getters are missing from the World and payloads are truncated. In the main configuration the eleven equal senders
were also translated and measured (one build). The result was down bytes identical on 35,464 lines instead of 35,771.
A translated frame carries the channel's own sequence number, which is off after the unformatted STATUSTEXT frames,
while a recorded frame carries the reference's. The one-state replay had no vehicle to fill those messages' content
(servo outputs, RC, battery), so its frames equal fell to 1,705. The senders are therefore kept recorded until
STATUSTEXT is formatted (Vehicle.json `_content_senders_doc`). Still recorded: all 64 senders and STATUSTEXT.

### Item 4: speed (D16)

Profile (`sample` on the replay, 15 s of the main loop): 37 % of the time in `PMem.enter` (zeroing each stack frame byte
by byte through the bridged store), 33 % in `memcpyRaw` (byte by byte), 3 % in `Bridge.find`. Fixed in the memory runtime
(`support/ParamMemory.lean`, hand-written runtime, not vehicle logic): `memcpy` copies one block when both ranges lie inside
the memory and do not overlap, `memset` of zero copies a block of zeros, `enter`/`alloc` zero through `memset`; every other
case keeps the byte loop. The bytes written are the loop's (the replays above are identical). Whole vehicle per 400 Hz
step: mean 2.13 ms, p99 4.44 ms before; mean 0.60 ms, p99 2.48 ms, max 37 ms after (one run). A second profile (10 s)
then showed `lean_dec_ref_cold` 13 % (freeing small objects), `PMem.Bridge.find` 10 % (a binary search over the 277
bridged fields for every byte access in the bridged range), `ldWord` 2 %; `find` is now one read of a slot table
computed once (`support/gen_param_memory_v.py`). Final, one run, no other build running: mean 0.50 ms, p99 2.29 ms, max 34 ms per step (the max is a step of the boot catch-up). Runs while a Lean
build ran on the same machine measured p99 up to 2.52 ms: the margin is small and load-dependent.

### Translator and configuration changes (Phase 5b)

| where | change |
|---|---|
| cpp2lean_mem.py | discriminated static locals; qualifier of static members from the source; enum constants by qualified enumeration; virtual by the in-class declaration; `pre_*` bridge inputs on the call's object; `bridge_field_reads` adapters; `world_outputs` drain after bridge calls; for the content senders: a call written `Class::f()` whose qualifier has `f`'s length is not virtual (read from the source: `GCS_MAVLINK::vfr_hud_alt()` in GCS_MAVLINK_Copter's override recursed forever), an unqualified enumeration in a member's result type is its class's (`SubMode ModeGuided::submode()`), `errors` escaped as a Lean name. The vehicle translation of the main configuration is byte-identical with and without these three |
| cpp2lean.py | `--param-save-log` (World save and notify events with the parameter's path), `ap_message` enum header (subagent W, merged) |
| ardupilot/translate_estimator.sh | `--param-save-log`; no `--drop AP_Param::save`, `--drop AP_Param::notify`, `--drop GCS::send_message` |
| ardupilot/vehicle/Vehicle.json | `AP_Param::save`/`flush`, `GCS::send_parameter_value` translated; `bridge_inputs` `AP_GPS::init`; `world_outputs`; `bridge_field_reads`; entries `AP_Param::notify`, `AP_Param::save`, `AP_Mission::write_home_to_storage` |
| ardupilot/vehicle/gen_bridge.py | `pre_*` actions; field adapters; `AP_AHRS::pre_arm_check` a passing check |
| support/gen_param_memory_v.py | `PMem.Bridge.addrOfPath`; `PMem.Bridge.find` by a slot table computed once (the binary search's answer, one array read) |
| support/ParamMemory.lean | block `memcpy`/`memset`, `enter`/`alloc` through `memset` |
| lean/VehicleReplay.lean (harness) | the line's time as the HAL clock during the catch-up of World delays; the storage at the end; `VEHICLE_REPLAY_MEMDUMP` |
| lean/OneStateReplay.lean, ardupilot/onestate_replay.py (harness) | the save queue constructed, `save_io_handler` as IO process, the World's events drained after the line's IO; `AP_GPS::init` with `convert_parameters`; PARAM_VALUE notifications of World parameters no longer taken from the recording |
| lean/EstimationReplay.lean (harness) | outputs threaded through `AP_Baro.init/update/calibrate`, `Compass.init`, `resetHeightDatum` |

### Still boundary, recorded, hand-written or deviating

- Recorded: the 64 content senders (`bframe`), STATUSTEXT (`GCS::service_statustext` writes the recorded frames;
  `send_text` no-op), `AP_AHRS::send_ekf_status_report`, `AP_GPS::send_mavlink_gps_raw`/`gps2_raw`.
- Passing checks (the bridge answers true; the reference arms with checks and shows no PreArm text on this flight):
  `AP_Baro::arming_checks`, `AP_GPS::pre_arm_checks`, `AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz`,
  `Compass::configured`, and new in 5b `AP_AHRS::pre_arm_check`.
- Not in the World (default answers): `AP_AHRS::active_backend_configured_to_use_gps` (false), `AP_AHRS::
  get_filter_status_for_configured_backend` (false: the GPS-glitch arming check is skipped), `AP_RTC::get_time_utc`,
  `AP_InertialSensor::periodic`, `set_imu_out_uart`, `AP_GPS::broadcast_first_configuration_failure_reason`,
  `Compass::per_motor_calibration_*`.
- `AP_Param::convert_parameter_width` of GPSn_GNSS_MODE (AP_GPS::init) is not run (no old-width value in these images;
  the reference makes no save there).
- Hand-written: the HAL (lean/VehicleReplay.lean: lockstep.cpp's drivers, the console `printf` formatter `cformat` for
  `BetterStream::printf`), the memory runtime (support/*.lean), the bridge's hand-written adapters (gen_bridge.py HAND).
- Found, not fixed: in the World, `AP_Baro::update_field_elevation` calls `AP::ahrs().resetHeightDatum()`, which reaches
  `AP_Baro::update_calibration` through AP_DAL and sets `_last_notify_ms`; the caller's state is not reloaded after the
  call (cpp2lean.py `--swap-out` does not see the path through AP_DAL), so the second `update_calibration` notifies
  BARO1_GND_PRESS again (one extra PARAM_VALUE at line 5,794). The estimator's values are not affected (the estimation
  replay compares them: 0 different).
- The QGroundControl session's one-state replay (`python3 ardupilot/onestate_replay.py sim/out/lockstep-qgc/harness
  build/gcs/qgc/est.txt`): 55,336 of 55,515 steps with all frames equal, 8,903 of 9,707 frames
  equal, parameter download 781 of 781 (780 before 5b), storage 0 bytes differ in and outside the mission areas (MIS_TOTAL
  was the one difference), estimation 0 of 13,138,989 different; first difference step 5,765 frame 2: the translation's
  PARAM_VALUE of MIS_TOTAL (saved by the translated `write_home_to_storage`) written in the step of the event; the
  reference writes it one line later, as the whole-vehicle replay of the flight does (line 5,766, the same payload there): this
  replay's IO points (after the step's GCS work) are not the vehicle's
- Deviations: the World's delays (ins.init, barometer calibration) consume their lines in the World and the memory side
  catches up after the call (now with each line's own time as the HAL clock); the World's events of such a call are
  replayed after it. A `--max-lines` below the end of boot (915) does not terminate (the replay waits in setup).

## Phase 5a summary (the vehicle, first half, 2026-11-12)

PORT-PLAN.md section 6, "Phase 5", slices 1 and 2 of the brief; slice 3 (home/origin pushes, the AP_Param save queue) not
started. The three sections after this one have the details.

**State-model decision and its measurement.** Two back ends stay, joined in one state: the estimator (AP_AHRS with its
back ends, NavEKF3, AP_DAL, the sensor front ends and stand-ins) stays in the value World `Estimator_lib` (verified
bit-identical, 167 µs per step); everything else (AP_Param, GCS, AP_Mission, the vehicle, the controllers) is on the byte
memory of `cpp2lean_mem.py`, whose state `PMem.Mem` (generated variant `support/ParamMemoryV.lean`) holds the World as a
field. Measurement (`build/p5a/lean/MemBench.lean`, a scratch bench, not a test): the straight-line part of EKF3's
CovariancePrediction as both back ends emit it (60 products, 70 loads of P, 60 stores, `lean/CovPredBench.lean`'s text),
same checksum: value World 35.3-36.3 µs per call, byte memory 54.4-56.7 µs (three runs of 20,000 calls): 1.55 times for
the loads and stores alone, before the memory back end's per-call frames, records returned through memory and parameter
reads through calls, which EKF3 is full of. Moving the estimator would therefore make its 167 µs at least ~260 µs (p99
1.9 ms to about 2.9 ms, over the 2.5 ms budget) and require regenerating and re-verifying 21,761 extent lines; so (a). The
controllers were regenerated anyway (on the memory back end, from the reference units): `Copter_lib` was translated
against stub headers with the AHRS as a stub and cannot be wired into the real vehicle; it stays as the controller
replay's translation.

| piece | translation | ArduPilot extent lines | Lean lines |
|---|---|---|---|
| the vehicle on the byte memory: AP_Vehicle, AP_Scheduler (task tables, functors), Copter (init_ardupilot, allocate_motors, load_parameters, tasks, modes, arming, land detector, ...), RC_Channel(s), SRV_Channel(s), AP_Motors, the controllers, AP_Arming, AP_BattMonitor, AP_Mission (with its execution), GCS, AP_Param, static construction | `ardupilot/vehicle/translate_vehicle.sh` → `ardupilot/out/Vehicle/Vehicle_lib.lean` (2,082 functions reached, 2,076 translated, 6 stubs) | about 35,700 distinct lines in 174 files | 51,038 |
| the bridge: 277 estimator parameters by address (`VehicleBridgeMap.lean`), 124 adapters for the 122 estimator functions the vehicle calls (103 generated by `ardupilot/vehicle/gen_bridge.py` from signatures and clang layouts, 11 by hand: accessors returning addresses, `sitl`, three recorded MAVLink sends, `handle_msg`; 10 functions not in the World give defaults) | `VehicleBridge.lean`, `VehicleBridgeMap.lean` | (marshalling, not ArduPilot code) | generated |
| Estimator_lib with 44 more entry points (64 methods; earlier definitions textually identical, 51 diff lines are moves) | `ardupilot/translate_estimator.sh` | +~600 | 1,351 defs (from 1,285) |

Acceptance (main workspace, after the merge, 2026-11-12):

1. Slice 1 (met for the estimator's parameters; see the regression note below):
   - `LEAN_NUM_THREADS=1 bash ardupilot/vehicle/replay.sh`: 8431 of 8431 ticks bit-identical (controller replay untouched).
   - `LEAN_NUM_THREADS=1 python3 ardupilot/onestate_replay.py sim/out/lockstep-flight`: `values compared: 8439007, equal:
     8439007, different: 0`, with `load_all` writing the 277 estimator parameters directly into the World (no copy, no
     `# params`); `estimation_replay.py` on the new Estimator_lib also 0 of 8,439,007.
   - EK3_IMU_MASK: explained (`NavEKF3::InitialiseFilter`, AP_NavEKF3.cpp:823, `_imuMask.set_and_default(_imuMask & mask)`
     with one IMU: 3 → 1, in the World; the GCS memory had its own copy) and gone in the one-state GCS replay (S1's run:
     35,958 of 36,013 steps, 7,148 of 7,304 frames, download 781 of 781; new first difference step 5,765, the vehicle's
     GPS_GLOBAL_ORIGIN/HOME_POSITION pushes, slice 3). The probe snapshots of COMPASS_OFS_*, COMPASS_EXTERNAL,
     COMPASS_PRIO1_ID, COMPASS_SCALE*, BARO1_DEVID, INS_GYROFFS_* and EK3_IMU_MASK are no longer applied.
2. Slice 2 (met in part): `LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight` (the
   translated static construction, `setup()`, `loop()` as `HAL_Lockstep::run`; the harness supplies input lines and
   collects output lines only): `tasks by scheduler tick: 35098 ticks compared, 35098 identical`; `PWM identical on 18871
   of 36013 lines; down bytes identical on 35264`; boot 886 of 915 lines identical. Not identical: setup() ends at line
   910 instead of 914 (four lines that the reference consumes in a `delay` with three callbacks between
   `register_timer_failsafe`, system.cpp:86, and Compass::init's back end, not located further), so every later line is
   four lines early; after arming (accepted at the reference's step) the motors stay at 1000 (not located). Mutation:
   AP_Scheduler::run's fast-task priority limit 3 → 255 in a copy of Vehicle_lib: 0 of 35,098 ticks identical.
3. Speed of the whole vehicle per 400 Hz step (one run, main workspace): mean 2.31 ms, p99 5.18 ms, max 41 ms (the agent's
   run: 2.08 / 4.47 / 41 ms), against the 2.5 ms budget (mean inside, p99 not) and the C++ reference's 3.4 µs (about 600
   to 700 times). The one-state estimator + GCS replay: mean 272 µs, p99 2.07 ms.

Still boundary or recorded, and why: the content messages of GCS (`bframe`, Phase 5b), STATUSTEXT counts, `GCS::send_
parameter_value` (no-op), `snprintf`/`vsnprintf` (D10), `AP_Notify::update` (NotifyDevice without body), `AP_Param::save`
(the save queue: slice 3), four estimator pre-arm checks not in the World (true), `AP_Param::convert_g2_objects`/`convert_
toplevel_objects` (stubs; the images have no old keys), `AP_Mission::distance_to_mission_leg` (goto), the INS stored-id
flags (from est.txt's header). Delays inside World code (ins.init, baro calibrate) consume lines in the World; the memory
side catches up afterwards with one delay callback per line (a deviation from the reference's interleaving).

Regression found at the merge, fixed: slice 2 translated three answers slice 1 took from the boundary (`AP_Scheduler::time_available_usec`/`get_loop_period_us`, `GCS_MAVLINK_Copter::params_ready`) and moved the HAL clock to the World's `EstScheduler._clock_us`; `lean/OneStateReplay.lean` (which runs without the vehicle's static construction) now sets the scheduler singleton, `_loop_period_us`, the task time and `copter.ap.initialised_params` and gives each GCS step its own clock. After the fix, in main: `gcs replay sim/out/lockstep-flight: 36013 steps, 35958 steps whose frames are all equal`; `equal 7148 (translated 671, boundary 6477), different 148, missing or extra 8`; parameter download 781 of 781 equal; first difference step 5765; estimation 0 of 8,439,007 different.

## Phase 5: the vehicle skeleton (slice 2 groundwork, translator side, 2026-11-12)

PORT-PLAN.md "Phase 5: the vehicle", 4.1, 4.2, 4.10. The vehicle (everything except the estimator) on the byte-memory
back end, as GCS_MAVLink in Phase 4: `ardupilot/vehicle/translate_vehicle.sh` runs `cpp2lean.py --param-memory
ardupilot/vehicle/Vehicle.json` -> `ardupilot/out/Vehicle/Vehicle_lib.lean` (+ `VehicleMemory.lean`, the address map,
`Vehicle_lib.survey.txt`, `Vehicle_lib.hal_calls.txt`, `Vehicle_lib.dumps.txt`) and `ardupilot/vehicle/bridge_calls.txt`.
`Vehicle.json` is GCS.json (AP_Param, GCS_MAVLink, AP_Mission: same keys, entries and boundary) plus the vehicle: entries
`AP_Vehicle::setup` and `AP_Vehicle::loop` (what the HAL main calls; Copter's overriders by dispatch), the key `vehicle`,
and these changes to GCS.json's lists, because the vehicle now translates what they stood for: the three vehicle answers
(`handle_command_do_set_mode`, `handle_command_component_arm_disarm`, `handle_MAV_CMD_NAV_TAKEOFF`) left the boundary;
AP_Mission's execution state machine, `Copter::set_mode`, `ModeAuto::do_guided` and the other ModeAuto entries left
`unreached`; AP_Mission's callbacks left `skip_members` (they are bound with FUNCTOR_BIND_MEMBER and called).

### New in cpp2lean_mem.py, all under the configuration key `vehicle` (AP_Param.json and GCS.json translate byte-identically)

| feature | how |
|---|---|
| definitions found on demand | a function without a body in the dumps so far: the unit whose object defines it (an index of `nm` over `build/reference/obj`, mangled and demangled names, cached as `vehicle_symbols.json`), else the caller's unit (where an inline or template function it uses has its body), dumped with the class's name (a member) or the function's name as `-ast-dump-filter`; likewise the record layouts (`rec_layout`: the current unit's, then a defining unit's), enums and typedefs of unseen types (`ftype`, `NAV_TAKEOFF_FLAGS`, `RC_Channel::AUX_FUNC`), constructors, the statics' defining units (also file statics and static locals); `Vehicle_lib.dumps.txt` lists the 214 dumps added. Template instances are told apart by their mangled names; a call's instance is the one of exactly the callee's type (dumping the caller's unit if needed); overloads are chosen by the arguments' types; a template's pattern is never a candidate |
| records by value (c) | a function returning a record takes the result's address `sret` after `this`; the caller passes a temporary of its frame, whose address is the expression's value; `return e` initializes `*sret` (constructors, init lists, copies); the implicit copy and move constructors are byte copies; `c ? r1 : r2` of records; the operators are ordinary member or free calls |
| <cmath> (d) | cpp2lean's table (`CMATH`): the exact functions as FloatLib operations, the others as musl's translation `Musl.f.f` (imported per function used), libc++'s mixed overloads through double; `isgreater` family; `isnan` of an integer false |
| function pointers (a) | a function designator is the function's address (a fixed address per function, outside the memory); a call through a pointer (`_method(_obj, args...)` of `Functor`) is a call of `fnptr'N`, the dispatcher of the pointer's function type over every function whose address is taken with that type: in translated code (`Functor::bind<T, method>`'s `method_wrapper<T, method>`: FUNCTOR_BIND_MEMBER, AP_Mission's callbacks) and in the statics' constant data (the task tables `Copter::scheduler_tasks`, `AP_Vehicle::scheduler_tasks`: clang's IR relocations to `method_wrapper` instances, resolved to those addresses; their definitions dumped and translated, to a fixpoint); `(t->*method)(args...)` with a constant member pointer is a call of that member function (virtual if it is virtual) |
| virtual calls (b) | by address, the simpler faithful choice (no vptrs: the objects are constructed by the harness's static construction, not by translated constructors): `by_address` `{"Mode": ["copter", "Copter"]}`: a virtual call through `Mode *`/`Mode &` (also an unqualified virtual call inside a Mode member) is a call of `vcall'Mode'f'N`, whose arms compare the object's address with each member object of `copter` whose class derives from Mode (clang's layout of Copter) and call the final overrider of that object's class; the classes with one dynamic class in this vehicle stay on `dynamic` (AP_Vehicle -> Copter, RC_Channel(s) -> the Copter ones, AP_Motors -> AP_MotorsMatrix, AC_AttitudeControl -> _Multi, AP_Arming -> AP_Arming_Copter, AP_BattMonitor_Backend -> _Analog), now only for virtual functions and with the final overrider along the base chain; a polymorphic class's `(primary base)` in clang's layout dump is a base |
| the estimator bridge | every member function of `bridge_classes` (AP_AHRS and back ends, AP_AHRS_View, NavEKF2/3, AP_NavEKF_Source, EKFGSF_yaw, AP_DAL*, AP_InertialSensor*, AP_Baro*, Compass, AP_Compass*, AP_GPS*, AP_RTC, AP_Declination) and the accessors `bridge_functions` (`AP::ahrs`, `AP::ins`, ..., `AP::sitl`) is a call of `PMem.bridge "name"` (`support/VehicleMemory.lean`: recorded) with the type's default (a zeroed temporary for a record); `bridge_calls.txt` lists each with its declaration's signature and call sites, and the estimator data members accessed directly |
| HAL | a HAL member outside the configured boundary is `PMem.halCall "name"` with the default (listed in `Vehicle_lib.hal_calls.txt`, 40 members: RCOutput, RCInput, Util, AnalogIn, ...); `AP_HAL::Scheduler::delay` stays GCS.json's boundary |
| stubs | a function the back end rejects is emitted as a stub (its signature, `PMem.unreached "rejected ..."`, the default) and listed with the rejection in `Vehicle_lib.survey.txt`, so that the translation elaborates |
| smaller | `new T[n]`, `&=`/`|=` on bool, NoOp casts as lvalues, attributes on variables, char-valued template arguments, packs in template arguments (`Functor<void>`), `static constexpr float` members, `typename __promote<...>::type`, `void (*const)(...)`, unnamed enums, static members through an object whose declaration is in no dump |

### Survey (functions reached from the entries; first rejection of each)

| run | reached | rejected |
|---|---|---|
| on-demand definitions only (first run) | 578 | 34 |
| final | 1,848 (1,844 translated) | 4 |

Remaining rejections: `AP_Param::convert_g2_objects`, `convert_toplevel_objects` (arrays of conversion records passed by
value), `Copter::allocate_motors` (`AP_MotorsMatrix::var_info` named without its class in clang's JSON: the static is not
found), `AP_Mission::distance_to_mission_leg` (`goto`). Static `ekf_check_state` (ekf_check.cpp's file static) is not found
(zero bytes). Lean: 45,584 lines; ArduPilot extent about 32,700 distinct lines in 178 files (GCS_Common.cpp 3,312,
AP_Mission.cpp 2,580, AP_Param.cpp 1,828, AP_Arming.cpp 1,353, RC_Channel.cpp 1,256, SCurve.cpp 1,016, AC_PosControl.cpp
952, mode.cpp 865, ...). 22 virtual-call dispatchers over the 9 modes, 4 function-pointer dispatchers (`void (void *)`: 30
targets, the two task tables and the bound callbacks). The bridge: 122 estimator functions, 193 call sites.
Translation about 45 s (cached ASTs). The generated Lean elaborates: `cd lean && LEAN_NUM_THREADS=1 lake build VehicleMemLib`
(new target, roots `VehicleMemory`, `Vehicle_lib`; copies of the generated files in `lean/`), 3.5 min, no errors, no `sorry`.

Not done: the harness (static construction of `copter`'s members, the task loop against `tasks=`), the bridge itself,
AP_Param's save queue, the estimator's own objects; constructors are not translated as such for the vehicle's objects.

## Phase 5: the estimator bridge (slice 1: one state, 2026-11-12)

Two back ends stay: the estimator (AP_AHRS and back ends, NavEKF3/AP_DAL, the front ends, the stand-ins) in the value
World `Estimator_lib`; everything else on the byte memory. The one state is the memory state with the World inside it;
a parameter has one home (the estimator's 277 in the World, every other in the memory).

- **Memory with the World inside** (`support/gen_param_memory_v.py --memory`, generated from the text of
  `support/ParamMemory.lean`, which is unchanged): `support/ParamMemoryV.lean` (`Mem.w : Estimator_lib.World`,
  `Mem.eo : Estimator_lib.Outputs`; `rd`/`wr`, `ldU16/32`, `stU16/32` test one range `[Bridge.lo, Bridge.hi)` first and
  read/write the World field's bits there, a whole-field access is one getter/setter; `memcpy`, `memset`, `strncpy`,
  `halRead` assemble each bridged field and set it once), `GCSMemoryV.lean`, `VehicleMemoryV.lean` (imports only).
  The field map `VehicleBridgeMap.lean` (`--bridge`): the 277 fields of THIS image (`gen_param_harness.py` with
  `PARAM_HARNESS_TARGET=vehicle`: clang's offsets over `Vehicle_lib.addresses.json` -> `ardupilot/out/Vehicle/estimator_params.json`),
  each with its World path (the estimator's signatures), getters/setters on the bits.
- **cpp2lean_mem.py keys** (Vehicle.json only; AP_Param.json and GCS.json translate byte-identically): `memory_module`
  (imported and copied instead of ParamMemory), `bridge_module` (imported, generated: every estimator call becomes
  `VehicleBridge.<f>'<arity> [this] [sret] args... [inputs]`, the arguments in the translator's convention, the
  signatures with clang's record layouts written to `Vehicle_lib.bridge.json`), `bridge_inputs` (a translated vehicle
  function passed as an action to an adapter: `AP_Vehicle::get_time_flying_ms` for `AP_AHRS::update`).
- **Adapters** (`ardupilot/vehicle/gen_bridge.py` -> `VehicleBridge.lean`): 124 adapters for the 122 functions (193
  call sites, all through adapters): 103 generated (memory <-> World marshalling by layout, enums by value, the World
  taken out of the state for the call and stored back, out-parameters and record results written to memory, the HAL
  armed flag `Mem.armed` set in every reader), 11 by hand (the accessors: object addresses; `sitl`: null; the MAVLink
  senders `send_ekf_status_report`, `send_mavlink_gps_raw`/`gps2_raw`: the recorded frame as GCS.json; `handle_msg`:
  unreached), 10 not in the World (recorded, default: AP_Baro::arming_checks, AP_Declination::get_earth_field_ga,
  AP_GPS::broadcast_first_configuration_failure_reason, AP_GPS::pre_arm_checks, AP_InertialSensor::periodic,
  pre_arm_check_gyro_backend_rate_hz, set_imu_out_uart, Compass::configured, per_motor_calibration_update/end).
- **Estimator_lib**: `ardupilot/estimator.use` gained 44 entries (64 methods added; every earlier definition textually
  identical, some moved by the dependency order); golden updated.
- **The combined replay** (`ardupilot/onestate_replay.py SESSION [EST]`, `lean/OneStateReplay.lean`,
  `lake build onestate_replay`): estimation_replay.py's commands (through the adapters) and gcs_replay.py's steps in one
  process over one state; AP_Param's `load_all` writes the estimator's parameters into the World; snapshots are never
  applied to a bridged parameter. Flight: estimation 8,439,007 values, 0 different; GCS 7,148 of 7,304 frames equal,
  parameter download 781 of 781, first difference step 5,765 (GPS_GLOBAL_ORIGIN/HOME_POSITION pushes, vehicle code).
  QGroundControl session: estimation 13,138,989 values, 0 different; 8,903 of 9,707 frames, download 780 of 781
  (MIS_TOTAL), first difference step 5,765.

## Phase 5: the whole-vehicle replay (slice 2, 2026-11-12)

The translated vehicle runs as `HAL_Lockstep::run` runs the reference: the translated static construction, `setup()`,
then `loop()` and the IO processes, repeatedly; the translated scheduler decides what runs. The harness
(`lean/VehicleReplay.lean`) is the HAL (lockstep.cpp's drivers) and the boundary: it supplies the input lines where the
vehicle waits and collects one output line per consumed line.

```
ardupilot/vehicle/translate_vehicle.sh                    # cpp2lean --param-memory ardupilot/vehicle/Vehicle.json
PARAM_HARNESS_TARGET=vehicle python3 ardupilot/param/gen_param_harness.py sim/out/lockstep-flight/est.txt
python3 support/gen_param_memory_v.py --memory --bridge   # ParamMemoryV (HAL state fields), VehicleBridgeMap
python3 ardupilot/vehicle/gen_bridge.py                   # VehicleBridge.lean
cp ardupilot/out/Vehicle/Vehicle_lib.lean support/*V.lean lean/
cd lean && LEAN_NUM_THREADS=1 lake build vehicle_replay   # Vehicle_lib 4.5 min + its C 7 min
python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight [--max-lines N]
```

### Static construction (translator key `static_construction`)

`Vehicle_lib.staticConstruct` is C++'s dynamic initialization of the statics the translation uses, translated from
each static's declaration (`Copter copter;`, `AP_Param::_storage(...)`, `AP_Mission::_storage`, the `ObjectBuffer`
statics `GCS_MAVLINK::param_requests/replies`, `AP_Param::save_queue`, `AP_Vehicle::scheduler_tasks[]` (its
FUNCTOR_BIND table), `dummy_rcchannel`, `NaNf`, ...), in C++'s order: the units in the order of copter_ref's
initializer list (`__init_offsets`, read once into `ardupilot/vehicle/init_order.json`), within a unit the order in
which its `_GLOBAL__sub_I_<unit>` calls the `__cxx_global_var_init` functions (clang's IR; the initialized global is the
one stored to or constructed). It replaces GCSReplay's `staticInit`/`ctorDefaults`/`runtimeObjects` (OneStateReplay
still uses them). New under the key:

- member objects' default constructors are translated (before: skipped, the harness ran `setup_object_defaults`):
  a user-provided constructor is called, an implicit one is its bases' and members' construction and the default member
  initializers (`construct_default`; `this` inside a default member initializer is the object being constructed, e.g.
  ModeAuto's `mission{FUNCTOR_BIND_MEMBER(&ModeAuto::start_command, ...)}`; unnamed records by their place);
- estimator classes (AP_AHRS, AP_InertialSensor, AP_Baro, Compass, AP_GPS, ...) are skipped: the World constructs them
  (`World.init`);
- FUNCTOR_BIND_MEMBER / SCHED_TASK_CLASS / SCHED_TASK (`Functor::bind<T, method>`): the object and a fixed address of the
  bound member function (`bound_methods`); the dispatchers of the functors' pointer types call that member on the bound
  object (arms added where the parameter and result types match);
- `using Base::Base` (`inherited_ctors`: GCS::StatusTextQueue -> ObjectArray), template classes with `::` in their
  arguments, `class`/`noexcept` spelling in constructor types, reference members in aggregates (`AC_AttitudeControl::
  pre_arm_checks`' `{name, AC_P &}` tables), arrays of unknown bound, C globals (`copter`, `hal`) in the IR.
- `static_refs`: `AP_MotorsMatrix::var_info` in `Copter::allocate_motors` is AP_MotorsMulticopter's static (clang's JSON
  names it without its class): allocate_motors is translated now (was a stub).

### The HAL boundary (translator key `hal_hook`)

Every HAL member outside the configuration's boundary is `PMem.hal "<AP_HAL::Class::member>" this #[args]` (arguments
as 64-bit words, floats as bits, records by address; the result converted back). `support/VehicleMemory.lean` declares it
as an `@[extern "cpp2lean_vehicle_hal"] opaque`; the replay driver defines it (`@[export]`): the forward declaration
lets the HAL call the translated vehicle back (IO processes, delay callback, failsafe) and HAL changes rebuild only the
driver. `hal` is a zeroed object of the HAL's size (224 bytes): driver pointers are null; `hal.util->persistent_data`
lives in the null page. The clock is the World's (`EstScheduler._clock_us`, 1 before the first line, as SITL's).
The driver implements lockstep.cpp:

- `delay`, `delay_microseconds`, `delay_microseconds_boost`: consume lines until the time has passed (Scheduler::delay's
  rule for the delay callback; `_min_delay_cb_ms` is 0 until a callback is registered, so every iteration counts as
  lockstep.cpp counts `dcb`); consuming line k writes output line k-1 (`t pwm=16 [down=]`), appends `up` to SERIAL0,
  takes the RC frame and the battery, steps the World (its clock, GPS latch, the sensor stand-ins' timer processes; the
  World is fed 1,000 lines ahead), runs the vehicle's timer processes, the timer failsafe (`failsafe_check_static`) and
  the IO processes (registered functors: `param_io_timer`, `AP_Param::save_io_handler`, called through the dispatcher);
- RCInput (`new_input` once per frame, `num_channels`, `read`), RCOutput (SITL's write with the safety state and
  BRD_SAFETY_MASK read from `AP_BoardConfig::_singleton`, cork/push, read/read_last_sent, force_safety_on/off), AnalogIn
  (pins 12-15 from the line's battery as lockstep.cpp's AnalogSource), Util (`set_soft_armed` -> `Mem.armed`, which the
  bridge forwards to the World; safety state; RTC), the console `printf` (SERIAL0, %s %u %d %x %c), UART options.
- Delays inside World code (`ins.init`, `barometer.calibrate`, `compass.init`, `gps.init`): the World consumes the lines
  (EstScheduler); the memory side catches up at the next HAL call / end of setup / end of loop: per line its output
  line, uplink, RC, battery, failsafe, IO processes and one delay callback. Deviation: that work follows the World call
  instead of interleaving with it, and the last line of each World `delay()` gets a callback the reference does not run
  (the reference's `dcb=0` lines 64, 68, ...).
- `AP::sitl()` is a zeroed SITL object at 0x800 (SIM_LOOP_DELAY 0; null made `AP_Scheduler::loop` delay 1000 us).

Boundary still from the recording or stubbed: the Phase 4 content frames (`PMem.bframe`: heartbeat, SYS_STATUS, ...: not
loaded by this driver yet), STATUSTEXT (`send_text`), `GCS::send_parameter_value` (PARAM_VALUE notifications),
`AP_Notify::update` (stub: rejected, NotifyDevice), the estimator's own pre-arm checks not in the World
(`AP_Baro::arming_checks`, `AP_GPS::pre_arm_checks`, `AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz`,
`Compass::configured`: pass), `snprintf` (formatting, D10), `AP_Param::save` (dropped: no save queue).

### Results (`python3 ardupilot/vehicle/vehicle_replay.py sim/out/lockstep-flight`, 2026-11-12, release build, one run)

Translation: 2,082 functions reached (2,076 translated, 6 stubs: `AP_Param::convert_g2_objects`,
`convert_toplevel_objects` (conversion tables by value; the images have no old keys), `AP_Mission::distance_to_mission_leg`
(goto), `AP_Notify::update` (NotifyDevice's virtual `update` has no body in the dumps; the LEDs and buzzer reach no
output), `AP_BoardConfig::allocation_error`/`throw_error` (varargs; never called)); `Copter::allocate_motors` is
translated. ArduPilot extent about 35,700 distinct lines in 174 files; Vehicle_lib.lean 51,038 lines; `staticConstruct`
17 statics (2 not constructed: `Mode::auto_yaw`, `GCS_MAVLINK::routing`: initializers in no dump, zero-initialized
objects). Translation 45-90 s; Lean: Vehicle_lib 4.5 min, its C 7 min (LEAN_NUM_THREADS=1).

```
vehicle_replay: 36013 lines, 35103 loops, 72.9 s; step mean 2075.5 us p99 4451.6 us max 40324.4 us
output lines: ours 36013, recorded 36013
PWM identical on 18871 of 36013 lines; down bytes identical on 35264; both on 18349; boot (init, 915 lines) both identical on 886
first PWM difference: (912, '2280000', '0,...,0', '2280000', '1000,1000,1000,1000,0,...')
first down difference: (21, '52500', 'fd19...ESC_CALIBRATION...', '')
tasks identical on 26839 of 36013 steps (tick identical on 910)
first tasks difference: (911, ...: ref tick=0 tasks=-, ours tick=1 tasks=0,...,10,28,29,30)
tasks by scheduler tick: 35098 ticks compared, 35098 identical; first difference: None
```

- **Boot**: lines 1-20 identical in structure (SiK reset `0 ` x3, the console banner "Init ArduCopter V4.8.0-dev
  (802db19d) ... Free RAM: 524288" from the translated `printf`, AP_BoardConfig's eight `delay(1)`, the esc-calibration
  wait `delay(20)` until the first RC frame, the delay-callback counts `dcb` of every line); the reference then consumes
  four more lines (21-24: a `delay()` of 10 ms shape, three callbacks) between `register_timer_failsafe`
  (ArduCopter/system.cpp:86) and Compass::init's back-end construction (`ev=4` at line 24), which this run does not (the
  World's `gps.init`/`compass.init` consume none there); not located further (both are World code, golden). So `setup()`
  ends at line 910 instead of 914 and every later step runs four lines early: the per-line comparisons are offset by
  four lines from line 911 on.
- **Scheduler**: by scheduler tick the translated AP_Scheduler runs exactly the reference's tasks on all 35,098 main-loop
  ticks (`tasks=`); one loop per line as in the reference (35,103 loops for 35,103 lines after boot).
- **PWM**: identical on 18,871 lines (boot zeros, the disarmed minimum 1000 on motors 1-4 four lines early). The arm
  command (COMMAND_ACK of 400 at line 16,742) answers MAV_RESULT_FAILED: `AP_Arming::serial_protocol_checks` sees an RC
  input serial port, because GCS.json's boundary `find_protocol_instance`/`find_serial` answered every protocol with the
  MAVLink ports. Fixed (`PMem.findSerialProto`: MAVLink protocols only; `AP::serialmanager()`, a fixed 0x30 before,
  is the translated accessor; the estimator's own pre-arm checks not in the World pass): in the final run the arm
  command and NAV_TAKEOFF are ACCEPTED at the reference's lines (16,742 and 16,814), but the motors stay at 1000 after
  arming (the reference spools up to 1487 by line 18,200): not located (the spool state / AP_Motors armed flag path
  after `AP_Arming_Copter::arm` is the next place to look). The counts above are unchanged by this fix.
- **Down bytes**: identical on 35,264 lines (mostly lines without bytes); the content frames (Phase 4's boundary frames)
  are sent only in the step they were recorded in, which the four-line offset misses; PARAM_VALUE notifications
  (`GCS::send_parameter_value`, still a boundary no-op) and STATUSTEXT are missing.
- **Speed** (whole vehicle per 400 Hz step, main loop, wall time between consumed lines, in-process): mean 2.08 ms, p99
  4.45 ms, max 40 ms, against the 2.5 ms budget (mean inside, p99 not) and the C++ reference's 3.4 us mean (about 610
  times). The estimator part alone was 0.13-0.5 ms (Phase 3).
- **Mutation** (`AP_Scheduler::run`'s `MAX_FAST_TASK_PRIORITIES` 3 -> 255 in a copy of Vehicle_lib.lean, built in
  `build/mut/lean`, same driver, then deleted): tasks by tick 0 of 35,098 identical (35,098 unmutated), tasks per line
  910 of 36,013 (26,839), 2 output lines differ from the unmutated run (disarmed: PWM unchanged).

Not done: the motors after arming, the four boot lines, `GCS::send_parameter_value` and
STATUSTEXT texts (formatting, D10), the estimator keys per step (`--est`'s outputs: the World is the one EstimationReplay
checks, but this driver does not print `ahrsKeys`/`ekfKeys`), the qgc session.

## The C library

The translations call `sinf`, `cosf`, `tanf`, `asinf`, `acosf`, `atanf`, `atan2f`, `expf`, `powf`,
`fmodf`, `sin`, `cos`, `atan2` and `fmod` (AP_Math, AC_AttitudeControl, AC_PosControl, AC_WPNav, the
AHRS view), and the examples also `logf`, `log2f`, `tan`, `asin`, `acos`, `atan`, `exp`, `log`, `log2` and `pow`. IEEE
754 does not define these exactly, so no FloatLib operation computes what a C library computes, and
two C libraries differ in the last bits. Both sides therefore run musl's algorithms: the C++ side
links musl's C sources, the Lean side runs their translation by cpp2lean.

**Source.** musl 1.2.5 (`https://musl.libc.org/releases/musl-1.2.5.tar.gz`, SHA-256
`a9a118bbe84d8764da0ea0d28b3ab3fae8477fc7e4085d90102b8596fc7c75e4`), MIT license
(`libm/musl-1.2.5/COPYRIGHT`; the trigonometric files carry Sun's notice, "Permission to use, copy,
modify, and distribute this software is freely granted, provided that this notice is preserved", the
exp/log/pow family Arm's MIT SPDX line). `libm/musl-1.2.5/` holds the 72 files used (68 until Phase 3 added `log2f` and `log2`), unmodified, at
their paths in the release: the generic C versions of `src/math` (not the `src/math/aarch64`
versions, which are inline assembly), `src/internal/libm.h`, `COPYRIGHT`, `VERSION`
(`libm/musl_files.txt` lists them). Besides the 22 functions above, the C++ side also takes musl's
`sqrtf`, `sqrt`, `fabsf`, `fabs`, `fminf`, `fmin`, `fmaxf`, `fmax`, `floorf`, `floor`, `ceilf`, `ceil`,
`truncf`, `trunc`, `roundf`, `round`, `copysignf`, `copysign`, `scalbnf` and `scalbn`, so that it
calls no function of the platform's libm; the Lean side computes these with FloatLib's operations
(table in "Mapping"), and the difftest compares the two.

**Environment.** musl's sources expect musl's build: `libm/env/` stands in for it with `math.h` (the
declarations and constants the files use, `float_t`/`double_t` of `FLT_EVAL_METHOD == 0`, `isnan` and
`signbit` as clang's builtins instead of musl's union-based macros, which compute the same predicate),
`endian.h`, `features.h` (`hidden`) and `fp_arch.h` (empty: the generic `fp_barrier`, as
`arch/generic`).

**The C++ side** (`libm/build_musl.sh`): each file compiled as its own translation unit, as musl's
build does, with `clang -x c -std=c99 -O2 -ffp-contract=off -fno-fast-math -fno-builtin` and every
external name prefixed `cpp2lean_musl_` (`libm/env/musl_prefix.h`), into `build/libm/`; the linker
options `-Wl,-alias,_cpp2lean_musl_sinf,_sinf` (one per C name) bind every call of a C name in the
reference (also libc++'s `std::sin(float)`, which calls `sinf` through `__builtin_sinf`) to musl's
function. The difftest drivers, `copter_ref` and the composition environment link them;
`ardupilot/vehicle/build.sh` prints the math functions `copter_ref` imports from the platform:
none. On arm64 clang defines `__FP_FAST_FMA`, so musl's `log` and `pow` take their `__builtin_fma`
paths: one `fmadd` instruction on the C++ side, FloatLib's `fma` in Lean.

**The Lean side** (`libm/translate_libm.sh`): one translation unit per function f,
`libm/unity/unity_f.c`, which includes f.c and the files of the helpers it calls
(`libm/unity/groups.txt`; `ardupilot/check_unity.py` checks that each preprocesses as in its own
unit); output `libm/out/Musl/f.lean`, module and namespace `Musl.f`, function `Musl.f.f`, and
`libm/out/Musl.lean`, which imports them all. `__rem_pio2f` and `__rem_pio2` (the argument
reductions of the float and double trigonometric functions, with `__rem_pio2_large`) are modules of
their own, which `sinf`, `cosf`, `tanf`, `sin`, `cos` and `tan` call through `--module-sig` (the
static constant `pio4` of `__tan.c` and of `__rem_pio2.c` cannot share one unit). A data table
(`__exp2f_data`) is translated into each function that reads it. The translator options are
`--lib-dir` for `src/internal` and `src/math` (`libm.h`'s inline functions and the data headers,
translated as far as used), `--nest`, `--general-loops`, `--uninit-reads`, and `--drop fp_force_evalf`,
`fp_force_eval`, `fp_force_evall` (`FORCE_EVAL`, whose only effect is on the floating-point exception
flags, which nothing observes). 26 modules, 3549 lines (24 and 3309 before `log2f`, `log2`). A translation that calls `sinf` imports
`Musl.sinf` and calls `Musl.sinf.sinf`.

C constructs accepted for these sources (only in a `.c` file; `volatile` locals and the two options
also in C++):

- C's int-valued conditions and operators: a condition of type int (or float) is true when nonzero
  (`if (sign)` is `if sign != 0`); a comparison, `&&`, `||` and `!` have type int: their truth value
  where one is needed (`if ix < 0x39800000`), else `if c then 1 else 0` (`return 2 * ix - 1 >= ...`).
- Unions whose members are numbers of one width (`union {float f; uint32_t i;} u = {x};`): the
  variable holds the bit pattern (`let mut u : UInt32 := Binary32.toBits x`), a member is a view
  (`u.f` is `Binary32.ofBits u`, `u.i &= 0x7fffffff` is `u := u &&& ...`). The compound literals of
  `libm.h`'s `asuint`, `asfloat`, `asuint64`, `asdouble` (`((union{float _f; uint32_t _i;}){f})._i`) are
  the conversions themselves (`Binary32.toBits f`).
- Pointer parameters of a number type used only as `*p` (`__rem_pio2f(float x, double *y)`), or only
  as `p[i]` and as an argument for such a parameter (`__rem_pio2_large(double *x, double *y, ...)`):
  the value or the array the caller passes, returned after the result if the body writes through it,
  as for `T &`; the caller passes `&x` for `x` or a local array (or its own such parameter), and
  writes the returned value back.
- `do { ... } while (0)` (the statement macros `GET_FLOAT_WORD`, `FORCE_EVAL`): a loop of one
  iteration. An `if` whose condition is an integer constant expression (`if (sizeof(x) ==
  sizeof(float))` in `FORCE_EVAL`; `sizeof` of a number type): only the selected branch.
- `--general-loops`: a `for`, `while` or `do` loop whose trip count the translator does not compute
  (`for (k=1; iq[jk-k]==0; k++);`, `__rem_pio2_large.c:354`): `for _ in [0:2^64] do` with the C test
  where C tests it and `break` when it is false. The C loop must end within 2^64 iterations (no
  execution reaches that bound; C++ may assume that a loop without side effects terminates). A
  `continue` in a `for` or `do` body is rejected (it would skip the step or the test).
- `goto` (with `--general-loops`): backward, to a label whose statements (the label's and those after
  it in its block) all end in `return` (`goto recompute`, `__rem_pio2_large.c:363`): those statements
  are the body of such a loop, the goto `continue`; forward (`goto medium`, `__rem_pio2.c:61`): the
  statements of the label, which end in `return`, are translated at the goto. A label whose
  statements declare variables, contain other gotos or may fall through is rejected.
- `volatile` local variables and parameters (`fp_barrierf`): no other code can reach them (no
  pointers, no mutable globals), so their accesses are ordinary reads and writes.
- Uninitialized local arrays (`double tx[3];`): zeros, with the comment that C writes every element
  before reading it (reading an indeterminate value is undefined). `--uninit-reads`: a read that the
  definite-assignment check cannot prove (`__tan.c:99` reads `sign`, assigned under the same `if
  (big)`) is accepted, the variable starting at zero.
- C structs, also anonymous ones nested in a struct (`struct {double invc, logc;} tab[16]`), as plain
  structures; constant tables of a struct type with designated initializers (`.tab = {...}`, clang
  lists them in field order); an `extern` declaration of a constant (`exp2f_data.h`) refers to its
  definition; an element of an array member of a constant (`__exp2f_data.tab[i]`).
- `__builtin_expect(c, v)` (`predict_false`) is c; `__builtin_isnan`, `__builtin_signbit` are
  `Binary32.isNaN`, `signbit`; `__builtin_fma` is `Binary64.fma`.
- A prototype in a header outside the translated files (`libm.h`'s `hidden float __sindf(double)`)
  resolves to the definition in them.

Differential test of every function on its own (`examples/libm.cpp`, one wrapper per function, 20
of them IEEE-exact and FloatLib's on the Lean side, 24 musl's (with `log2f`, `log2` since Phase 3); seed 20261104):

```
libm: 10000 input lines (2000 random, 8000 corner) x 44 functions; columns: float#0 float#1 double#0 double#1 int32_t#0
libm: 0 of 440000 lines differ (600 lines equal only as NaN vs NaN with different bits)
$ python3 difftest.py --seed 7 --random 50000 libm
libm: 58000 input lines (50000 random, 8000 corner) x 44 functions; columns: float#0 float#1 double#0 double#1 int32_t#0
libm: 0 of 2552000 lines differ (600 lines equal only as NaN vs NaN with different bits)
```

The corner values include the largest finite numbers, which take `__rem_pio2_large` (the
large-argument reduction of `sin` and `cos`), and the random 20% of bit patterns are mostly huge or
tiny. Found by this test: Lean's prefix `-` takes `>>>` into its operand (`-1U >> 9` in `fmodf.c`
became `-(1 >>> 9)`, 0, and 2203 lines differed); the translator now parenthesizes `(-a) >>> b`.

## Lean and FloatLib API findings

Since the FloatLib port (Lean v4.35.0, FloatLib `acba2057`, Mathlib v4.35.0):

- `Binary32`/`Binary64` (`FloatLib.Floats`, `open FloatLib.Floats (Binary32 Binary64)` in every
  emitted file) have `+ - * /` (FloatLib's certified word kernels), `Neg` (`Model.neg`, flips the sign
  bit), `<`/`≤` (decidable, IEEE: false on NaN), `BEq` (`compareEqual`, IEEE), `OfScientific`
  (the exact rational rounded once), `Inhabited` (+0), a structural `DecidableEq` (bit patterns: not
  C's `==`), and `ToString` (the shortest decimal). Missing, and written in `support/CFloat.lean` from
  FloatLib's operations: the conversions between the two formats (`Model.cast`), from and to the
  integer types (`ofRat`, `toInt?`), and the named C functions; FloatLib's `ofFloat`/`toFloat` go
  through Lean's `Float` and are not used.
- FloatLib's `min`/`max` instances are IEEE `minimum`/`maximum` (NaN propagates), not C's `fmin`/`fmax`
  (`minimumNumber`/`maximumNumber`). FloatLib has IEEE `remainder` but no `fmod`, which is therefore
  musl's (translated).
- NaN bits are observable: `ofBits32`/`toBits32` keep every pattern, signaling NaNs included, and
  operations propagate an operand's payload (quieted), as IEEE 754-2019 §6.2.3 recommends; which
  operand, and how a payload converts between the formats, differ from arm64 (the difftest's NaN rule).
- Dot notation does not reach CFloat's functions (`x.toBinary64`): `Binary32` unfolds to a `Subtype`,
  so the emitted code and the harnesses apply them by name (`Binary32.toBinary64 x`).
- Importing FloatLib imports Mathlib, whose style linters then run on every file (`dupNamespace` on
  `Musl.sinf.sinf`, `nameCheck` on `__rem_pio2f`); `lean/lakefile.toml` turns those two off
  (`weak.linter.*`). `lake build` loads Mathlib's and FloatLib's `.olean` files for each module
  (about 4 s per module); FloatLib itself builds in about 6 minutes, Mathlib's cache is fetched
  (`lake exe cache get`). A bare `lake update` moves the Mathlib pin: the manifest is pinned by hand.
- Lean's prefix `-` parses its operand at precedence 75, which takes in `<<<` and `>>>`: `-a >>> b` is
  `-(a >>> b)` (found by the libm difftest); the translator parenthesizes `(-a) >>> b`.
- Closed terms: the Lean compiler does not hoist a FloatLib literal's rounding out of the function
  that uses it (the rational is a closed constant, its rounding `roundRat` runs at every call), so
- (Phase 1) `@[csimp]` replaces a monomorphic constant by another in compiled code wherever it
  appears, including inside an instance's code; FloatLib's comparison instances are generic over the
  format, so CFloat defines monomorphic `Binary32.blt` etc. (definitionally FloatLib's) and instances
  of high priority that use them, and attaches the `@[csimp]` theorems to those. FloatLib's
  `adjacencyRank` theorems give the IEEE order on non-NaN words as an integer order on the bits.
  `(1.1920929e-7 : Binary32)` costs a rational rounding per evaluation (see "Speed").

From the earlier ports (Lean 4.33, still true):

- Missing in core: combined sign-and-width integer conversions (composed); `Int32.toNat`
  (`toNatClampNeg`).
- Structures: `{ s with a.b := v }` updates a nested field; `Array.set!`, `Array.replicate` and
  `a[i]!` exist; `deriving Inhabited` and `deriving DecidableEq, Inhabited` (for an inductive of
  enumerators) work.
- With the default `autoImplicit true`, an unknown name in a binder's default value is silently
  bound as an implicit argument instead of reported (found while ordering a default argument that
  names a `static constexpr` member); `lean/lakefile.toml` sets `autoImplicit = false`, and the
  translator orders every constant before its first use.
- (Phase 3) Layout: a structure instance `{ a := x,` continued on a line indented less than its first
  field does not parse; generated code and the hand-written harnesses (`Compose.lean`, `Vehicle.lean`)
  keep each instance on one line.
- (Phase 3, third part) No namespace aliases: `abbrev M := AP_Motors_lib.AP_MotorsMatrix` is not a
  declaration Lean accepts (a namespace is not a term), so `Compose.lean` names every function in
  full. `List.asString` is deprecated (`String.ofList`).
- (Fourth part) No decimal-to-float parser in core: the vehicle parses with `OfScientific.ofScientific`
  at `Binary64` and `Binary32` (FloatLib's: the exact decimal rounded once, as `strtod`/`strtof`), and
  prints exact decimals and `%.6f` from the bit patterns with `Nat` arithmetic. A structure with
  function-typed fields (the live `Inputs`) derives `Inhabited` and takes `fun _ => ...` defaults
  without further help.

## Differential test

`difftest.py` translates each example into `lean/`, generates the C++ driver
`examples/<example>_driver.cpp` (it `#include`s the example, so static functions are reachable) and
compiles it with the flags above, linked with musl's math functions (`libm/build_musl.sh`), generates
`lean/Main.lean` and runs `lake build` (a warning fails the run), then feeds both executables the same
input lines. It first translates the C library (`libm/translate_libm.sh`) into `lean/Musl/`.

- Input line: one column per parameter slot (for each type, as many columns as the most parameters
  of that type in one function); floating values as hex bit patterns (read with `memcpy` in C++,
  `Binary32.ofBits` in Lean; both sides read a signaling NaN with its quiet bit set, since C leaves
  signaling NaNs to the implementation), integers in decimal, bools as 0/1. Every function of the example is called on
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
  (C: `%08x %.9g` / `%016llx %.17g`; Lean: the hex of `Binary32.toBits` and FloatLib's `toString`), `<input line>
  <function> <value>` for integers and bools. The comparison is on the hex fields (and the decimal of
  integers); the floating decimals are informational, since the two sides format them differently.
- NaN comparison: bit-exact, except that a NaN matches a NaN. FloatLib keeps a NaN's sign and payload,
  but which operand's payload an operation returns, and how a payload converts between float and
  double, IEEE 754 and C leave open, and FloatLib's choice (the IEEE 754-2019 §6.2.3 recommendation:
  an operand's payload, quieted; across formats the payload as an integer if it fits) differs from
  arm64's (the first NaN operand, or the default NaN; across formats the payload's high bits).
  Within the subset a NaN's payload and sign are not observable by any operation other than
  printing its bits or reading them through a union (comparisons, `isnan`, arithmetic and conversions
  treat all NaNs alike; musl's functions read a NaN's bits only to classify it), so the
  relaxation hides nothing else. The harness reports how many lines match only by this rule, grouped
  by the two patterns.
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
`tests/golden/Numeric.lean`; the imports and the module doc comment are omitted here):

```lean
open FloatLib.Floats (Binary32 Binary64)

namespace Numeric

/-- C++ `float constrain_float(float amt, float low, float high)`, `examples/numeric.cpp:7-19`. -/
def constrain_float (amt low high : Binary32) : Binary32 := Id.run do
  if Binary32.isNaN amt then
    return (low + high) / Int32.toBinary32 (2 : Int32)
  if amt < low then
    return low
  if amt > high then
    return high
  return amt

/-- C++ `bool is_zero(float x)`, `examples/numeric.cpp:22`. -/
def is_zero (x : Binary32) : Bool := Id.run do
  return decide (Binary32.abs x < (1.1920929e-7 : Binary32))

/-- C++ `float safe_sqrt(double v)`, `examples/numeric.cpp:25-32`. -/
def safe_sqrt (v : Binary64) : Binary32 := Id.run do
  let val : Binary32 := Binary64.toBinary32 v
  if val ≥ Int32.toBinary32 (0 : Int32) then
    return Binary32.sqrt val
  return Int32.toBinary32 (0 : Int32)

/-- C++ `float thrust_curve(float thrust, float expo, float lift_max)`, `examples/numeric.cpp:36-44`. -/
def thrust_curve (thrust expo lift_max : Binary32) : Binary32 := Id.run do
  let thrust_curve_expo : Binary32 := constrain_float expo (Binary64.toBinary32 (-(1.0 : Binary64))) (Binary64.toBinary32 (1.0 : Binary64))
  if is_zero thrust_curve_expo then
    return lift_max * thrust
  let throttle_ratio : Binary32 := Binary64.toBinary32 (((Binary32.toBinary64 thrust_curve_expo - (1.0 : Binary64)) + Binary32.toBinary64 (safe_sqrt (((1.0 : Binary64) - Binary32.toBinary64 thrust_curve_expo) * ((1.0 : Binary64) - Binary32.toBinary64 thrust_curve_expo) + (4.0 : Binary64) * Binary32.toBinary64 thrust_curve_expo * Binary32.toBinary64 lift_max * Binary32.toBinary64 thrust))) / ((2.0 : Binary64) * Binary32.toBinary64 thrust_curve_expo))
  return constrain_float throttle_ratio (Binary64.toBinary32 (0.0 : Binary64)) (Binary64.toBinary32 (1.0 : Binary64))

/-- C++ `const float horner_coeffs[5]`, `examples/numeric.cpp:47`. -/
def horner_coeffs : Array Binary32 := #[(1.0 : Binary32), -(0.5 : Binary32), (0.25 : Binary32), -(0.125 : Binary32), (0.0625 : Binary32)]

/-- C++ `float horner(float x)`, `examples/numeric.cpp:49-56`. -/
def horner (x : Binary32) : Binary32 := Id.run do
  let mut acc : Binary32 := (0.0 : Binary32)
  for i' in [0:5] do
    let i : Int32 := Nat.toInt32 i'
    acc := acc * x + horner_coeffs[Int32.toNatClampNeg ((4 : Int32) - i)]!
  return acc

/-- C++ `float half_angle_sin(float theta)`, `examples/numeric.cpp:59`. -/
def half_angle_sin (theta : Binary32) : Binary32 := Id.run do
  return Musl.sinf.sinf ((0.5 : Binary32) * theta)

/-- C++ `float half_angle_sin_d(float theta)`, `examples/numeric.cpp:60`. -/
def half_angle_sin_d (theta : Binary32) : Binary32 := Id.run do
  return Binary64.toBinary32 (Musl.sin.sin ((0.5 : Binary64) * Binary32.toBinary64 theta))

/-- C++ `int clamp_steps(int n, float x)`, `examples/numeric.cpp:63-79`. -/
def clamp_steps (n : Int32) (x : Binary32) : Int32 := Id.run do
  if n ≤ (0 : Int32) then
    return (0 : Int32)
  if Binary32.isNaN x then
    return -(1 : Int32)
  let steps : Int32 := if n > (8 : Int32) then (8 : Int32) else n
  let mut count : Int32 := (0 : Int32)
  let mut y : Binary32 := x
  for i' in [0:8] do
    let i : Int32 := Nat.toInt32 i'
    if i ≥ steps then
      break
    y := y * (0.5 : Binary32)
    if Binary32.abs y < (1.0 : Binary32) then
      continue
    count := count + i
  return (2 : Int32) * count + (if y > Int32.toBinary32 (0 : Int32) then (1 : Int32) else (0 : Int32))

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
ext_sqrt:Binary32.sqrt`). `examples/shape.cpp` (170 lines) has `Shape` and `Tile : Shape` with a
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
  _kp : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _ki` of `PID` (`examples/pid.cpp:180`). -/
  _ki : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _kd` of `PID` (`examples/pid.cpp:181`). -/
  _kd : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _kimax` of `PID` (`examples/pid.cpp:182`). -/
  _kimax : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _kpdmax` of `PID` (`examples/pid.cpp:183`). -/
  _kpdmax : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _filt_T_hz` of `PID` (`examples/pid.cpp:184`). -/
  _filt_T_hz : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _filt_E_hz` of `PID` (`examples/pid.cpp:185`). -/
  _filt_E_hz : Binary32 := (0.0 : Binary32)
  /-- `AP_Float _filt_D_hz` of `PID` (`examples/pid.cpp:186`). -/
  _filt_D_hz : Binary32 := (0.0 : Binary32)
deriving Inhabited

/-- State of C++ `PID` (`examples/pid.cpp:67-196`): its data members. -/
structure State where
  /-- `struct pid_flags _flags` of `PID` (`examples/pid.cpp:190`). -/
  _flags : PID.pid_flags := {}
  /-- `float _integrator` of `PID` (`examples/pid.cpp:191`). -/
  _integrator : Binary32 := (0.0 : Binary32)
  /-- `float _target` of `PID` (`examples/pid.cpp:192`). -/
  _target : Binary32 := (0.0 : Binary32)
  /-- `float _error` of `PID` (`examples/pid.cpp:193`). -/
  _error : Binary32 := (0.0 : Binary32)
  /-- `float _derivative` of `PID` (`examples/pid.cpp:194`). -/
  _derivative : Binary32 := (0.0 : Binary32)
  /-- `PIDInfo _info` of `PID` (`examples/pid.cpp:195`). -/
  _info : PIDInfo := {}
deriving Inhabited

/-- Values C++ `PID` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `_ahrs.get_control_gain_scaler()` (first read at `examples/pid.cpp:102`). -/
  get_control_gain_scaler : Binary32 := (0.0 : Binary32)
deriving Inhabited

/-- C++ `PID::PID(AHRS & ahrs, float initial_p, float initial_i, float initial_d, float initial_imax, float filt_hz)`, `examples/pid.cpp:69-79`. -/
def init (initial_p : Binary32) (initial_i : Binary32) (initial_d : Binary32) (initial_imax : Binary32) (filt_hz : Binary32) : Params × State := Id.run do
  let mut p : Params := {}
  let mut s : State := {}
  p := { p with _kp := initial_p }
  p := { p with _ki := initial_i }
  p := { p with _kd := initial_d }
  p := { p with _kimax := Binary32.abs initial_imax }
  p := { p with _filt_E_hz := filt_hz }
  p := { p with _filt_D_hz := filt_hz * Int32.toBinary32 (2 : Int32) }
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
def update_i (p : Params) (s : State) (dt : Binary32) (limit : Bool) : State := Id.run do
  let mut s := s
  if !(Pid.is_zero p._ki) && Pid.is_positive dt then
    if !limit || ((Pid.is_positive s._integrator && Pid.is_negative s._error) || (Pid.is_negative s._integrator && Pid.is_positive s._error)) then
      s := { s with _integrator := s._integrator + (s._error * p._ki) * dt }
      s := { s with _integrator := Pid.constrain_float s._integrator (-p._kimax) p._kimax }
  else
    s := { s with _integrator := (0.0 : Binary32) }
  return s

/-- C++ `void PID::get_terms(float & p_out, float & d_out) const`, `examples/pid.cpp:150`. -/
def get_terms (s : State) (p_out : Binary32) (d_out : Binary32) : Binary32 × Binary32 := Id.run do
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
def update (p : Params) (s : State) (inp : Inputs) (target_roll : Binary32) (rate_roll : Binary32) (target_pitch : Binary32) (rate_pitch : Binary32) (dt : Binary32) : State × Binary32 := Id.run do
  let mut s := s
  let density : Binary32 := inp.get_air_density_ratio
  let scale : Binary32 := if density > (0.0 : Binary32) then (1.0 : Binary32) / Binary32.sqrt density else (1.0 : Binary32)
  let (t'1, t'2) := PID.update_all p._pid_roll s._pid_roll inp._pid_roll target_roll rate_roll dt s._limit (1.0 : Binary32)
  s := { s with _pid_roll := t'1 }
  s := { s with _out_roll := t'2 * scale }
  let (t'3, t'4) := PID.update_all p._pid_pitch s._pid_pitch inp._pid_pitch target_pitch rate_pitch dt s._limit (1.0 : Binary32)
  s := { s with _pid_pitch := t'3 }
  s := { s with _out_pitch := t'4 * scale }
  s := { s with _limit := decide (Binary32.abs s._out_roll > (1.0 : Binary32)) || decide (Binary32.abs s._out_pitch > (1.0 : Binary32)) }
  return (s, s._out_roll + s._out_pitch)
```

From `tests/golden/Shapes.lean`, namespace `Tile`: the override, the inherited `scale_report` (whose
`area()` calls resolve to `Tile.area`; the same function in namespace `Shape` calls `Shape.area`),
and the constructor:

```lean
/-- C++ `float Tile::area() const`, `examples/shape.cpp:102`. -/
def area (s : State) : Binary32 := Id.run do
  return Shape.area s * (0.5 : Binary32) + Int32.toBinary32 s._rotation

/-- C++ `float Shape::scale_report(float f, float & before)`, `examples/shape.cpp:58-63` (a member of `Shape`, translated for `Tile`). -/
def scale_report (s : State) (f : Binary32) (before : Binary32) : State × Binary32 × Binary32 := Id.run do
  let mut s := s
  let mut before := before
  before := area s
  s := scale_float s f
  return (s, before, area s)

/-- C++ `Tile::Tile(float size, int rotation)`, `examples/shape.cpp:100`. -/
def init (size : Binary32) (rotation : Int32) : State := Id.run do
  let mut s : State := {}
  s := Shape.init s Kind.Square size
  s := { s with _rotation := rotation &&& (3 : Int32) }
  return s
```

`python3 difftest.py` (all of it also run by `tests/run_tests.sh`, which builds `lean/` from clean):

```
literals: 272 floating literals; 0 elaborate in Lean to bits other than clang's
boost: 10000 input lines (2000 random, 8000 corner) x 3 functions; columns: float#0 float#1 float#2 float#3
boost: 0 of 30000 lines differ (0 lines equal only as NaN vs NaN with different bits)
mixed: 10000 input lines (2000 random, 8000 corner) x 11 functions; columns: float#0 float#1 double#0 double#1 bool#0 bool#1 int32_t#0 int32_t#1 int64_t#0 uint8_t#0 uint8_t#1
mixed: 0 of 110000 lines differ (2120 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean ffc00001: 800 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 440 lines
  NaN rule: C++ 7fc00000, Lean ffc00000: 400 lines
  NaN rule: C++ 7ff8000000000001, Lean 7ff8000000000000: 400 lines
  NaN rule: C++ 7fc00001, Lean 7fc00000: 80 lines
motors: 2400 input lines (2000 random, 400 corner) x 1 functions; columns: float#0 float#1
motors: 0 of 2400 lines differ (0 lines equal only as NaN vs NaN with different bits)
numeric: 10000 input lines (2000 random, 8000 corner) x 8 functions; columns: float#0 float#1 float#2 double#0 int32_t#0
numeric: 0 of 80000 lines differ (100 lines equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00000, Lean 7fc00001: 20 lines
  NaN rule: C++ 7fc00001, Lean 7fc00000: 20 lines
  NaN rule: C++ 7fc00001, Lean ffc00000: 20 lines
  NaN rule: C++ ffc00000, Lean 7fc00001: 20 lines
  NaN rule: C++ 7fc00000, Lean ffc00000: 10 lines
  NaN rule: C++ ffc00000, Lean 7fc00000: 10 lines
pid: 10000 input lines (2000 random, 8000 corner) x 5 functions; columns: float#0 float#1 float#2
pid: 0 of 50000 lines differ (0 lines equal only as NaN vs NaN with different bits)
shape: 2240 input lines (2000 random, 240 corner) x 2 functions; columns: float#0 int32_t#0
shape: 0 of 4480 lines differ (0 lines equal only as NaN vs NaN with different bits)
control Hold: 20963 calls on one object (20000 random, 963 corner) over 10 member functions, 6 state leaves per line; inputs: target.x, target.y, target.z, armed, trim
control Hold: 0 of 20964 lines differ (1895 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 1893 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 2 tokens
frame Host: 20500 calls on one object (20000 random, 500 corner) over 12 member functions, 27 state leaves per line; inputs: _gain_configured, lin_expo_configured, read_at, channel_mask_2
frame Host: 0 of 20501 lines differ (0 tokens equal only as NaN vs NaN with different bits)
motors Mixer: 20084 calls on one object (20000 random, 84 corner) over 2 member functions, 1 state leaves per line; inputs: get_lean_max_out, get_lean_max; outputs: set_roll, set_pitch
motors Mixer: 0 of 20085 lines differ (0 tokens equal only as NaN vs NaN with different bits)
motors Attitude: 20170 calls on one object (20000 random, 170 corner) over 2 member functions, 3 state leaves per line; inputs: get_saturation_count, get_saturation_margin, _mixer.get_lean_max_out, _mixer.get_lean_max; outputs: set_throttle_out_throttle, set_throttle_out_apply_angle_boost, set_throttle_out_filt_cutoff, _mixer.set_roll, _mixer.set_pitch
motors Attitude: 0 of 20171 lines differ (0 tokens equal only as NaN vs NaN with different bits)
navigate Navigator: 21809 calls on one object (20000 random, 1809 corner) over 9 member functions, 33 state leaves per line; inputs: stopping_point_out.x, stopping_point_out.y, speed_limit, scaler, now_ms, estimate.x, estimate.y, estimate.z, gain_kP
navigate Navigator: 0 of 21810 lines differ (1757 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7ff8000020000000, Lean 7ff8000000000001: 1755 tokens
  NaN rule: C++ 7ff8000020000000, Lean 7ff8000000000000: 1 tokens
  NaN rule: C++ 7ff8000020000000, Lean fff8000000000000: 1 tokens
pid PID: 20504 calls on one object (20000 random, 504 corner) over 11 member functions, 22 state leaves per line; inputs: get_control_gain_scaler
pid PID: 0 of 20505 lines differ (838 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 832 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 6 tokens
pid RateControl: 20280 calls on one object (20000 random, 280 corner) over 4 member functions, 47 state leaves per line; inputs: get_air_density_ratio, _pid_roll.get_control_gain_scaler, _pid_pitch.get_control_gain_scaler
pid RateControl: 0 of 20281 lines differ (861 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 854 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 7 tokens
shape Shape: 20124 calls on one object (20000 random, 124 corner) over 7 member functions, 7 state leaves per line; inputs: none
shape Shape: 0 of 20125 lines differ (579 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 568 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 11 tokens
shape Tile: 20180 calls on one object (20000 random, 180 corner) over 13 member functions, 12 state leaves per line; inputs: none
shape Tile: 0 of 20181 lines differ (809 tokens equal only as NaN vs NaN with different bits)
  NaN rule: C++ 7fc00001, Lean 7fc00000: 789 tokens
  NaN rule: C++ ffc00000, Lean 7fc00000: 20 tokens
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
`.json`) translates to exactly `tests/golden/<Namespace>.lean` (and `tests/golden/CFloat.lean`),
twice with identical output, with no `sorry`/`axiom`/`partial def`; the C library
(`libm/translate_libm.sh`, which checks its unity files) translates to exactly
`tests/golden/libm/Musl.lean` and `tests/golden/libm/Musl/*.lean`; `tests/reject_c.c` (the limits of
the C constructs: a union of members of different widths, a `continue` in a `for` loop without a
constant trip count, a `goto` to a label whose statements may fall through, a backward `goto` from
inside a loop, a pointer parameter used both as `*p` and `p[i]`) as below; `tests/reject_cases.cpp` (a
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

Since Phase 1 of the port the suite translates `ardupilot/translate_copter.sh` (the World of the six
controllers) against `tests/golden/ardupilot/Copter_lib.lean` in place of the four per-class
translations, checks its library code against AP_Math_lib's and AC_PID_lib's (`check_shared.py
--skip Output,Outputs,World`), runs the difftest target `ardupilot/Copter` in place of
`ardupilot/AP_Motors`, `AC_Attitude`, `AC_PosControl`, `AC_WPNav`, the examples `world` and the
migrated `navigate` (World drivers), and `tests/reject_world.cpp` (a reference to the result of a
call with arguments on a World object, a call that reaches the caller's object through the World, a
constructor that reaches another World object, a singleton pointer assigned something other than
`this`, two objects of a class whose references differ). `tests/reject_phase3d.cpp` lost its two
`--boundary-live` cases. The Phase 2 and 2b libraries, examples (`pointers`, `cstring`, `bytes`) and
reject files (`reject_phase2.cpp`, `reject_phase2b.cpp`) are part of the suite as described in their
sections.

Since Phase 3 of the port (World pointers, README "Phase 3: World pointers, sensor front ends, HAL delays")
the suite also translates and difftests the examples `worldptr` and `worlddelay` (goldens
`tests/golden/WorldPtrs.lean`, `WorldDelay.lean`), checks `tests/reject_phase3f.cpp` (8 rejections), and
translates `ardupilot/translate_est_scheduler.sh` (the HAL scheduler stand-in with the real headers; it
needs `build/reference/ap` from `reference/prepare.sh`, and is skipped without it, as EKF_Buffer and EKFGSF are)
against `tests/golden/ardupilot/EstScheduler_lib.lean`.
Since "Phase 3: AP_AHRS translated" the suite also translates and difftests the example `memberptrs` (golden
`tests/golden/MemberPtrs.lean`), checks `tests/reject_phase3k.cpp` (6 rejections), translates
`ardupilot/translate_ahrs.sh` against `tests/golden/ardupilot/AHRS_lib.lean` (with the reference build, as EKF3)
and runs the difftest target `ardupilot/AHRS` (its own harness, `ardupilot/ahrs_difftest.py`).
Since "Phase 3: the estimator World and the EKF3 replay" and "Phase 3: AP_AHRS in the estimator World, the full
estimation replay" the suite also translates `ardupilot/translate_estimation.sh`, `translate_navekf_source.sh` and
`translate_estimator.sh` against `tests/golden/ardupilot/Estimation_lib.lean`, `NavEKF_Source_lib.lean` and
`Estimator_lib.lean` (with the reference build), runs the difftest targets `ardupilot/Estimation` and
`ardupilot/NavEKF_Source`, and (section 7) builds the estimation replay without warnings and replays both recorded
flights whole against the reference vehicle's `--est` trace (needs `build/reference/copter_ref`; 0 different values).

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
| `AC_PID.h:96-107` | accessors returning `AP_Float &` (`kP()`, `kI()`, ...) | a reference to a parameter returned as its value (`kP (p : Params) : Binary32`) |
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

- (Fourth part, removed in Phase 1) Live reads (`--boundary-live`): replaced by the World.
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
- The Lean vehicle needed 2.88 ms per tick with FloatLib (over the 2.5 ms of the 400 Hz period); since Phase 1 it needs about 0.1 ms ("Phase 1 of the port", "Speed"). Float-to-double rounding and integer/float conversions of variables still go through FloatLib's rational arithmetic.
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
- `hypotf`, `log10f`, `exp2f`, `sinhf` and the rest of `<cmath>` not listed in the mapping table are
  rejected; the functions of the table are the ones the translations and examples call.
- libc++'s float overloads (`std::sin(float)`, `std::pow(float, float)`, ...) are mapped to the musl
  functions of the C name, which they call as `__builtin_sinf`; the link binds that call to musl's
  `sinf` too, but `-fno-builtin-sinf`/`-fno-builtin` do not cover it, so clang may still fuse or
  simplify such a call on the C++ side (constant arguments). The examples use the suffixed C
  functions only.
- The C library: `--general-loops` assumes that every loop it translates ends within 2^64 iterations
  (C++ may assume that a loop without side effects terminates; no execution reaches the bound), and
  `--uninit-reads` that C reads a variable only after assigning it (else C's behavior is undefined);
  both are used for musl's sources only. musl's `FORCE_EVAL` and `fp_barrier`, which only affect the
  floating-point exception flags and the compiler's code motion, are left out or are the identity:
  nothing observes the flags. Which NaN payload and sign a function returns is not compared (the NaN
  rule).
- The composition check (`ardupilot/compose/compose.sh`) compares with `oracle-nosincos.txt`, which
  was recorded with the platform's libm; with musl's functions its values differ from tick 491 on in
  the last bits (see "AC_AttitudeControl and AC_PosControl"). The harness that recorded it is not part
  of this repository, so it cannot be re-recorded with musl; the replay check compares the two
  vehicles, which both run musl's functions, on the same flight.
- The `for`/`while` trip-count rules are syntactic: a loop whose bound is constant only after
  further reasoning (e.g. `i < n` with `n` a non-`const` local that is never assigned) is rejected.
- The definite-assignment check is conservative: assignments inside a loop body or the right operand
  of `&&`/`||`/`?:` do not count after it.
- The operand order of linearized side effects is left to right; this matches clang on this target
  for every sequenced case, and the unsequenced cases are undefined behavior in C++.
- No proof that the translation is correct (translation validation is phase 4); the evidence is the
  syntax-directed construction and the differential test.
