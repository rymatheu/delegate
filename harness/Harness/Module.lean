import Harness.Contract

/-! A module declaration, its validation, and the C++ record definitions generated from it. The
Lean declaration is the single source of a module's schemas: the adapter includes the generated
header, and the executable reports the schemas back on `describe`. -/

namespace Harness

/-- A per-field generation hint of a regime, for what the clause language cannot say. -/
inductive Hint where
  /-- an integer input field that is `start` at the first step of a case and grows at every
  later step by a value drawn uniformly in [`lo`, `hi`] (a clock) -/
  | increasing (field : String) (start lo hi : Nat)
  /-- a binary32 input field that starts uniformly in [`lo`, `hi`] and moves at every later step
  by a value drawn uniformly in [-`step`, `step`], kept within [`lo`, `hi`] (a slowly varying
  signal) -/
  | walk (field : String) (lo hi step : Float)
  /-- binary32 input fields that form a unit vector (a quaternion, a direction): at the first
  step `center + spread ⊙ u` with `u` uniform in [-1, 1]ⁿ, normalized; at every later step the
  previous vector plus `step ⊙ u`, normalized (a slowly turning attitude). The lists have one
  entry per field. -/
  | unit (fields : List String) (center spread step : List Float)
  deriving Inhabited, Repr

/-- The hint as text. -/
def Hint.text : Hint → String
  | .increasing f s lo hi => s!"{f} starts at {s} and increases by {lo} to {hi} at every step"
  | .walk f lo hi st => s!"{f} starts in [{lo}, {hi}] and moves by at most {st} at every step, \
      within [{lo}, {hi}]"
  | .unit fs c sp st => s!"({", ".intercalate fs}) is a unit vector, starting near {c} \
      (spread {sp}) and moving by at most {st} per component at every step"

/-- The input fields a hint sets. -/
def Hint.fields : Hint → List String
  | .increasing f .. | .walk f .. => [f]
  | .unit fs .. => fs

/-- A named regime: extra clauses over (params, input), and hints, that narrow what a campaign
generates. A regime only steers sampling: the contract and its clause hashes are unchanged, so
a campaign under a regime is evidence for the same clauses. -/
structure Regime where
  name : String
  doc : String := ""
  clauses : List Clause
  hints : List Hint := []
  deriving Inhabited

/-- The regime as one line of text (what the result file and the ledger record). -/
def Regime.text (r : Regime) : String :=
  "; ".intercalate (r.clauses.map (·.text) ++ r.hints.map (·.text))

/-- The flight stack a node belongs to, and so the folder at the project root that holds it:
`ardupilot/`, `px4/`, or `sim/` (the simulator, shared by both stacks). -/
inductive Stack where
  | ardupilot
  | px4
  | sim
  deriving Inhabited, BEq, Repr

namespace Stack
/-- The stack's name, which is also its folder at the project root. -/
def name : Stack → String
  | ardupilot => "ardupilot"
  | px4 => "px4"
  | sim => "sim"
/-- Every stack, in the order `harness list` groups by. -/
def all : List Stack := [ardupilot, px4, sim]
/-- The command that builds a module of this stack, as `harness` suggests it. -/
def buildCommand (k : Stack) (name : String) : String :=
  match k with
  | ardupilot => s!"ardupilot/build.sh {name}"
  | px4 => s!"px4/build.sh {name}"
  | sim => s!"sim/modules/{name}/build.sh"
/-- The stack of a composed system from the stacks of its children: the one flight stack
(`ardupilot` or `px4`) the children other than `sim` share, `sim` when every child is `sim`.
Children from both flight stacks are an error: the system has to name its stack. -/
def ofChildren (sys : String) (kids : List (String × Stack)) : Except String Stack := do
  if kids.isEmpty then
    throw s!"system {sys}: no children to take a stack from; declare `stack := some ...`"
  let flight := kids.filter (·.2 != sim)
  match (flight.map (·.2)).eraseDups with
  | [] => pure sim
  | [k] => pure k
  | _ => throw s!"system {sys}: children from more than one flight stack \
      ({", ".intercalate (flight.map fun (c, k) => s!"{c}: {k.name}")}); \
      declare `stack := some ...` (or pass the stack to composeAll)"
end Stack

structure Module where
  name : String
  doc : String := ""
  params : Schema
  input : Schema
  output : Schema
  contract : Contract
  /-- the executable, relative to the harness directory -/
  exe : System.FilePath
  /-- the stack the module belongs to: its folder is STACK/modules/NAME -/
  stack : Stack
  /-- named regimes a campaign can be restricted to (`harness test NAME --regime R`) -/
  regimes : List Regime := []
  /-- Boolean observations over (params, input, output) a campaign counts the steps of; they
  measure what was exercised and are not part of the contract -/
  coverage : List Clause := []
  deriving Inhabited

/-- A checked regime: clauses resolved like the assumption, hints resolved to input fields
`(input index, start, lo, hi)`. -/
structure CRegime where
  regime : Regime
  clauses : Array Clause
  hints : Array (Nat × Nat × Nat × Nat)
  /-- `walk` hints: (input index, lo, hi, step) -/
  walks : Array (Nat × Float × Float × Float) := #[]
  /-- `unit` hints: (input indices, center, spread, step) -/
  units : Array (Array Nat × Array Float × Array Float × Array Float) := #[]
  deriving Inhabited

/-- A validated module: clause expressions resolved to slots in the environment
`params ++ input ++ output`. -/
structure Checked where
  m : Module
  assume : Array Clause
  guarantee : Array Clause
  regimes : Array CRegime := #[]
  coverage : Array Clause := #[]
  deriving Inhabited

namespace Module

def inputBase (m : Module) : Nat := m.params.size
def outputBase (m : Module) : Nat := m.params.size + m.input.size
def envSize (m : Module) : Nat := m.params.size + m.input.size + m.output.size

/-- A field or instance name: a letter or `_`, then letters, digits and `_`. -/
def isIdent (s : String) : Bool :=
  !s.isEmpty && (s.front.isAlpha || s.front == '_') && s.all (fun c => c.isAlphanum || c == '_')

/-- Fields with their slots: `(name, slot, type)`. -/
def slots (m : Module) : List (String × Nat × FieldType) :=
  let tag (base : Nat) (s : Schema) : List (String × Nat × FieldType) :=
    (s.toList.zipIdx).map fun (f, i) => (f.name, base + i, f.type)
  tag 0 m.params ++ tag m.inputBase m.input ++ tag m.outputBase m.output

def check (m : Module) : Except String Checked := do
  let all := m.params ++ m.input ++ m.output
  for f in all do
    unless isIdent f.name do throw s!"{m.name}: field name '{f.name}' is not an identifier"
  let names := all.toList.map (·.name)
  if names.eraseDups.length != names.length then
    throw s!"{m.name}: field names must be unique across params, input and output"
  let cnames := (m.contract.assume ++ m.contract.guarantee).map (·.name)
  if cnames.eraseDups.length != cnames.length then
    throw s!"{m.name}: clause names must be unique"
  let sl := m.slots
  let lookAll (n : String) := (sl.find? (·.1 == n)).map (·.2)
  let lookAssume (n : String) := (sl.find? fun (k, i, _) => k == n && i < m.outputBase).map (·.2)
  let res (look : String → Option (Nat × FieldType)) (c : Clause) : Except String Clause := do
    let e ← match c.expr.resolve look with
      | .ok e => pure e
      | .error msg => throw s!"{m.name}, clause {c.name}: {msg}"
    match e.typeOf with
    | .ok .bool => pure ⟨c.name, e⟩
    | .ok .num => throw s!"{m.name}, clause {c.name}: is a number, expected a Boolean"
    | .error msg => throw s!"{m.name}, clause {c.name}: {msg}"
  let a ← m.contract.assume.mapM (res lookAssume)
  let g ← m.contract.guarantee.mapM (res lookAll)
  let rnames := m.regimes.map (·.name)
  if rnames.eraseDups.length != rnames.length then
    throw s!"{m.name}: regime names must be unique"
  let regimes ← m.regimes.mapM fun r => do
    unless isIdent r.name do throw s!"{m.name}: regime name '{r.name}' is not an identifier"
    let cs ← r.clauses.mapM (res lookAssume)
    let idx (f : String) (float : Bool) : Except String Nat := do
      let some i := m.input.findIdx? (·.name == f)
        | throw s!"{m.name}, regime {r.name}: hint on '{f}', which is not an input field"
      let t := m.input[i]!.type
      if float then
        unless t == .f32 do throw s!"{m.name}, regime {r.name}: hint on '{f}', which is not f32"
      else unless t == .u32 || t == .i32 do
        throw s!"{m.name}, regime {r.name}: hint on '{f}', which is not an integer field"
      pure i
    let mut hs : Array (Nat × Nat × Nat × Nat) := #[]
    let mut walks : Array (Nat × Float × Float × Float) := #[]
    let mut units : Array (Array Nat × Array Float × Array Float × Array Float) := #[]
    for h in r.hints do
      match h with
      | .increasing f start lo hi =>
        let i ← idx f false
        unless lo ≤ hi do throw s!"{m.name}, regime {r.name}: hint on '{f}': lo > hi"
        hs := hs.push (i, start, lo, hi)
      | .walk f lo hi st =>
        let i ← idx f true
        unless lo ≤ hi && 0 ≤ st do
          throw s!"{m.name}, regime {r.name}: hint on '{f}': needs lo ≤ hi and 0 ≤ step"
        walks := walks.push (i, lo, hi, st)
      | .unit fs c sp st =>
        let is ← fs.mapM (idx · true)
        unless !fs.isEmpty && c.length == fs.length && sp.length == fs.length &&
            st.length == fs.length do
          throw s!"{m.name}, regime {r.name}: unit hint on {fs}: one center, spread and step \
            per field"
        units := units.push (is.toArray, c.toArray, sp.toArray, st.toArray)
    pure ({ regime := r, clauses := cs.toArray, hints := hs, walks, units } : CRegime)
  let cov ← m.coverage.mapM (res lookAll)
  return { m, assume := a.toArray, guarantee := g.toArray, regimes := regimes.toArray,
           coverage := cov.toArray }

/-! ### C++ record definitions -/

private def schemaJson (s : Schema) : String :=
  "[" ++ ",".intercalate (s.toList.map fun f =>
    s!"\{\\\"name\\\":\\\"{f.name}\\\",\\\"type\\\":\\\"{f.type.name}\\\"}") ++ "]"

private def structDef (tname : String) (s : Schema) : String :=
  let fields := s.toList.map fun f =>
    let doc := if f.doc.isEmpty then "" else s!"  // {f.doc}"
    s!"    {f.type.cType} {f.name};{doc}"
  s!"struct {tname} \{\n" ++ "\n".intercalate fields ++ (if s.isEmpty then "" else "\n") ++ "};\n"

private def unpackDef (fname tname : String) (s : Schema) : String := Id.run do
  let mut lines : Array String := #[]
  let mut off := 0
  for f in s do
    let line := match f.type with
      | .f32 => s!"    r.{f.name} = harness_float_of_bits(harness_get_u32(b + {off}));"
      | .u32 => s!"    r.{f.name} = harness_get_u32(b + {off});"
      | .i32 => s!"    r.{f.name} = int32_t(harness_get_u32(b + {off}));"
      | .bool => s!"    r.{f.name} = b[{off}] != 0;"
    lines := lines.push line
    off := off + f.type.bytes
  return s!"static inline void {fname}(const uint8_t *b, {tname} &r)\n\{\n" ++
    "\n".intercalate lines.toList ++ (if s.isEmpty then "    (void)b; (void)r;" else "") ++ "\n}\n"

private def packDef (fname tname : String) (s : Schema) : String := Id.run do
  let mut lines : Array String := #[]
  let mut off := 0
  for f in s do
    let line := match f.type with
      | .f32 => s!"    harness_put_u32(b + {off}, harness_bits_of_float(r.{f.name}));"
      | .u32 => s!"    harness_put_u32(b + {off}, r.{f.name});"
      | .i32 => s!"    harness_put_u32(b + {off}, uint32_t(r.{f.name}));"
      | .bool => s!"    b[{off}] = r.{f.name} ? 1 : 0;"
    lines := lines.push line
    off := off + f.type.bytes
  return s!"static inline void {fname}(const {tname} &r, uint8_t *b)\n\{\n" ++
    "\n".intercalate lines.toList ++ (if s.isEmpty then "    (void)b; (void)r;" else "") ++ "\n}\n"

/-- The header `harness gen NAME` writes: build/gen/NAME/module_records.h. -/
def recordsHeader (m : Module) : String :=
  s!"// module_records.h for module {m.name}
// Generated by `harness gen {m.name}` from the module's Lean declaration. Do not edit.
#pragma once

#include <stdint.h>
#include <string.h>

#define HARNESS_MODULE_NAME \"{m.name}\"
#define HARNESS_PARAMS_BYTES {m.params.bytes}u
#define HARNESS_INPUT_BYTES {m.input.bytes}u
#define HARNESS_OUTPUT_BYTES {m.output.bytes}u
#define HARNESS_SCHEMA_JSON \"\\\"params\\\":{schemaJson m.params},\\\"input\\\":{schemaJson m.input},\\\"output\\\":{schemaJson m.output}\"

{structDef "Params" m.params}
{structDef "Input" m.input}
{structDef "Output" m.output}
// records on the wire: little-endian words, floats as bit patterns, bool as one byte
static inline uint32_t harness_get_u32(const uint8_t *b)
\{
    return uint32_t(b[0]) | (uint32_t(b[1]) << 8) | (uint32_t(b[2]) << 16) | (uint32_t(b[3]) << 24);
}
static inline void harness_put_u32(uint8_t *b, uint32_t v)
\{
    b[0] = uint8_t(v); b[1] = uint8_t(v >> 8); b[2] = uint8_t(v >> 16); b[3] = uint8_t(v >> 24);
}
static inline float harness_float_of_bits(uint32_t w)
\{
    float f;
    memcpy(&f, &w, 4);
    return f;
}
static inline uint32_t harness_bits_of_float(float f)
\{
    uint32_t w;
    memcpy(&w, &f, 4);
    return w;
}

{unpackDef "harness_unpack_params" "Params" m.params}
{unpackDef "harness_unpack_input" "Input" m.input}
{packDef "harness_pack_output" "Output" m.output}"

end Module

end Harness
