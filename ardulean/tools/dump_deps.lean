/-
The constant-level dependencies of one module, for tools/split_modules.py.

    lake env lean --run tools/dump_deps.lean OUT.tsv MODULE [CLIENT ...]

writes one line per constant `c` declared in MODULE:

    c <TAB> line of c's declaration (or -) <TAB> constants of MODULE that c uses <TAB> other modules of this project
      that c uses <TAB> the constants of those modules that c uses

and, for each CLIENT module, one line `@client CLIENT <TAB> constants of MODULE that CLIENT's constants use`.
"Uses" is `ConstantInfo.getUsedConstants` (type and value). Modules of the toolchain and of the dependencies
(Init, Std, Lean, Lake, Mathlib, FloatLib, Batteries, ...) are left out.
-/
import Lean
open Lean

def external : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `FloatLib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
   `ImportGraph, `LeanSearchClient]

def run (out : System.FilePath) (mod : Name) (clients : List Name) : CoreM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | throwError "module {mod} is not imported"
  let h ← IO.FS.Handle.mk out .write
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let some ci := env.find? n | continue
    let line ← match ← findDeclarationRanges? n with
      | some r => pure (toString r.range.pos.line)
      | none => pure "-"
    let mut same : Array String := #[]
    let mut other : Array Name := #[]
    let mut otherC : Array String := #[]
    for u in ci.getUsedConstantsAsSet do
      match env.getModuleIdxFor? u with
      | some j =>
        if j == idx then same := same.push (toString u)
        else
          let m := env.header.moduleNames[j.toNat]!
          if !(external.contains m.getRoot) then
            if !other.contains m then other := other.push m
            otherC := otherC.push (toString u)
      | none => pure ()
    let sameS := same.qsort (· < ·)
    let otherS := (other.map toString).qsort (· < ·)
    let otherCS := otherC.qsort (· < ·)
    h.putStrLn s!"{n}\t{line}\t{" ".intercalate sameS.toList}\t{" ".intercalate otherS.toList}\t{" ".intercalate otherCS.toList}"
  for c in clients do
    let some ci := env.getModuleIdx? c | throwError "client {c} is not imported"
    let mut used : Array String := #[]
    for n in env.header.moduleData[ci.toNat]!.constNames do
      let some info := env.find? n | continue
      for u in info.getUsedConstantsAsSet do
        if env.getModuleIdxFor? u == some idx && !used.contains (toString u) then used := used.push (toString u)
    h.putStrLn s!"@client {c}\t{" ".intercalate (used.qsort (· < ·)).toList}"

unsafe def main (args : List String) : IO UInt32 := do
  let out :: mod :: clients := args | IO.eprintln "usage: dump_deps OUT.tsv MODULE [CLIENT ...]"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := (mod :: clients).map fun s => s.toName
  let env ← importModules (mods.map fun m => { module := m }).toArray {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<dump_deps>", fileMap := default }
  let st : Core.State := { env }
  discard <| (run out mod.toName (clients.map String.toName)).toIO ctx st
  return 0
