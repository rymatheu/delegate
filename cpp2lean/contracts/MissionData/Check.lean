import Vehicle
import MissionData.Course
import MissionData.Params

/-!
# `mission_world_check`

`mission_world_check ROOT` (ROOT: the `cpp2lean` directory) checks the embedded course texts of
`MissionData.Course` against the files under ROOT and constructs the world from `courseLines` with
the translated harness (`Vehicle.construct`). It prints one line per file (`same` or `DIFFERENT`), then
the parameters of the constructed world as `copter_lean --print-params` prints them, and
evaluates `missionParamsOk (boot w)` (`MissionData/Params.lean`), the parameter equalities of
`MissionWorld`; the exit code is `0` only if all three texts are the same and that check is `true`. Its parameter
lines must equal the output of
`copter_lean36 --print-params --params sim/params/copter-cf2x.txt --params sim/params/copter-course-speed.txt --params sim/params/copter-cf2x-tuned.txt`.
-/

open Vehicle MissionData

def main (args : List String) : IO UInt32 := do
  let root := args.headD "."
  let mut ok := true
  for (f, t) in courseFiles.zip courseTexts do
    let disk ← IO.FS.readFile (root ++ "/" ++ f)
    let same := disk == t
    ok := ok && same
    IO.eprintln s!"{f}: {if same then "same" else "DIFFERENT"}"
  match construct courseLines with
  | .error e =>
    IO.eprintln s!"construct: {e}"
    return 2
  | .ok w =>
    for l in paramLines w do
      IO.println l
    -- the trusted step of `MissionWorld`: the parameter equalities, evaluated on the booted world
    let pOk := missionParamsOk (boot w)
    IO.eprintln s!"missionParamsOk (boot w): {pOk}"
    return (if ok && pOk then 0 else 1)
