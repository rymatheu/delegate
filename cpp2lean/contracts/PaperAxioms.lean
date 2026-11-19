import Contracts.Track.Reach.LegHold
import Contracts.Track.Reach.Leg3Hold
import Contracts.Track.Reach.Safe
import Contracts.Track.Reach.Safe3
import Contracts.Track.Reach.Hover

/-! The theorems of the paper (`docs/PROOFS.md`): their axioms, and how many theorems of this package
each one rests on. Run from `contracts/` after the build: `lake env lean PaperAxioms.lean`.
Acceptable axioms: `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). -/

#print axioms Contracts.Track.Reach.Leg.waypoint_reach_h
#print axioms Contracts.Track.Reach.Leg3.waypoint_reach
#print axioms Contracts.Track.Reach.Safe.tracking_safe_h
#print axioms Contracts.Track.Reach.Safe.tracking_safe
#print axioms Contracts.Track.Reach.Hover.hover_stable

open Lean Elab Command in
/-- The named theorems of this package (modules `Contracts.*`, `FloatModel.*`; auxiliary declarations
such as `_proof_` and equation lemmas not counted) that the named constants use, transitively, the
constants themselves included; in total and by directory. -/
elab "#count_package_theorems " ids:ident* : command => do
  let env ← getEnv
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let ours (m : Name) : Bool := (`Contracts).isPrefixOf m || (`FloatModel).isPrefixOf m
  let mut seen : NameSet := {}
  let mut todo : Array Name := ids.map (·.getId)
  let mut byDir : Std.HashMap String Nat := {}
  let mut thms := 0
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if ci matches .thmInfo _ then
      if let some m := modOf n then
        if ours m && !n.isInternalDetail then
          thms := thms + 1
          let d := m.getPrefix.toString
          byDir := byDir.insert d (byDir.getD d 0 + 1)
    for c in ci.getUsedConstantsAsSet do
      if !seen.contains c then todo := todo.push c
  let dirs := byDir.toArray.qsort (fun a b => a.1 < b.1)
  let parts := dirs.toList.map fun (d, k) => s!"{d} {k}"
  logInfo m!"{thms} theorems of this package ({", ".intercalate parts})"

#count_package_theorems Contracts.Track.Reach.Leg.waypoint_reach_h
#count_package_theorems Contracts.Track.Reach.Leg3.waypoint_reach
#count_package_theorems Contracts.Track.Reach.Safe.tracking_safe_h Contracts.Track.Reach.Safe.tracking_safe
#count_package_theorems Contracts.Track.Reach.Hover.hover_stable
#count_package_theorems Contracts.Track.Reach.Leg.waypoint_reach_h Contracts.Track.Reach.Leg3.waypoint_reach Contracts.Track.Reach.Safe.tracking_safe_h Contracts.Track.Reach.Safe.tracking_safe Contracts.Track.Reach.Hover.hover_stable
