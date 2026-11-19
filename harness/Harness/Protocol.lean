import Lean.Data.Json
import Harness.Module

/-! The protocol client: the module executable as a child process on two pipes.

request             reply
`D`                 `K`, u32 length, manifest (JSON: name, code hash, flags, compiler, schemas)
`I` params-record   `K`
`S` input-record    `K` output-record
`Q`                 `K`, then the process exits

On start the client asks for the manifest and refuses to run an executable whose name or schemas
differ from the Lean declaration. -/

namespace Harness

open Lean (Json)

structure Manifest where
  name : String
  codeHash : String
  flags : String
  compiler : String
  params : Schema
  input : Schema
  output : Schema
  deriving Inhabited

private def schemaOfJson (j : Json) : Except String Schema := do
  let arr ← j.getArr?
  arr.mapM fun f => do
    let n ← f.getObjValAs? String "name"
    let t ← f.getObjValAs? String "type"
    match FieldType.ofName? t with
    | some ty => pure { name := n, type := ty }
    | none => throw s!"unknown field type '{t}'"

def Manifest.ofJson (j : Json) : Except String Manifest := do
  return {
    name := ← j.getObjValAs? String "name"
    codeHash := ← j.getObjValAs? String "code_hash"
    flags := ← j.getObjValAs? String "flags"
    compiler := ← j.getObjValAs? String "compiler"
    params := ← schemaOfJson (← j.getObjVal? "params")
    input := ← schemaOfJson (← j.getObjVal? "input")
    output := ← schemaOfJson (← j.getObjVal? "output") }

abbrev pipes : IO.Process.StdioConfig := { stdin := .piped, stdout := .piped, stderr := .inherit }

structure Proc where
  m : Module
  child : IO.Process.Child pipes
  manifest : Manifest

private def readExact (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.emptyWithCapacity n
  while buf.size < n do
    let chunk ← h.read (n - buf.size).toUSize
    if chunk.isEmpty then throw (IO.userError "module executable closed its output")
    buf := buf ++ chunk
  return buf

private def expectOk (h : IO.FS.Handle) (what : String) : IO Unit := do
  let b ← readExact h 1
  if b[0]! != 'K'.toNat.toUInt8 then
    throw (IO.userError s!"module executable refused {what}")

private def request (child : IO.Process.Child pipes) (bytes : ByteArray) : IO Unit := do
  child.stdin.write bytes
  child.stdin.flush

private def describeChild (child : IO.Process.Child pipes) : IO Manifest := do
  request child (ByteArray.mk #['D'.toNat.toUInt8])
  expectOk child.stdout "describe"
  let lenB ← readExact child.stdout 4
  let len := (Record.decode #[{ name := "n", type := .u32 }] lenB)[0]!.toNat
  let txt ← readExact child.stdout len
  let s := String.fromUTF8! txt
  match Json.parse s >>= Manifest.ofJson with
  | .ok m => pure m
  | .error e => throw (IO.userError s!"bad manifest: {e}\n{s}")

namespace Proc

/-- Start the module's executable and check its manifest against the declaration. -/
def start (m : Module) : IO Proc := do
  unless ← m.exe.pathExists do
    throw (IO.userError s!"{m.exe} not found; build it with {m.stack.buildCommand m.name}")
  let child ← IO.Process.spawn { cmd := m.exe.toString, stdin := .piped, stdout := .piped, stderr := .inherit }
  let man ← describeChild child
  let mut bad : Array String := #[]
  if man.name != m.name then bad := bad.push s!"name: executable '{man.name}', declaration '{m.name}'"
  for (k, a, b) in [("params", man.params, m.params), ("input", man.input, m.input),
                    ("output", man.output, m.output)] do
    unless a.same b do
      bad := bad.push s!"{k}: executable ({a.text}), declaration ({b.text})"
  unless bad.isEmpty do
    child.kill
    throw (IO.userError (s!"{m.exe} does not match the declaration of {m.name}; rebuild it " ++
      s!"({m.stack.buildCommand m.name}):\n  " ++ "\n  ".intercalate bad.toList))
  return { m, child, manifest := man }

def init (p : Proc) (params : Record) : IO Unit := do
  request p.child ((ByteArray.mk #['I'.toNat.toUInt8]) ++ params.encode p.m.params)
  expectOk p.child.stdout "init"

def step (p : Proc) (input : Record) : IO Record := do
  request p.child ((ByteArray.mk #['S'.toNat.toUInt8]) ++ input.encode p.m.input)
  expectOk p.child.stdout "step (no init?)"
  let b ← readExact p.child.stdout p.m.output.bytes
  return Record.decode p.m.output b

def stop (p : Proc) : IO Unit := do
  request p.child (ByteArray.mk #['Q'.toNat.toUInt8])
  expectOk p.child.stdout "quit"
  let _ ← p.child.wait

end Proc

/-- The manifest of a module executable (start, describe, stop). -/
def describeModule (m : Module) : IO Manifest := do
  let p ← Proc.start m
  p.stop
  return p.manifest

end Harness
