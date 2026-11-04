import Copter

/-!
# Mode schedule of a recorded Copter run (oracle harness input; not part of the port)

Replays the input lines through the Lean port's `Copter.loop` (by Lean's interpreter) and prints
each tick (1-based) at which the Auto submode, the AutoYaw mode or the active mission item changes.
The C++ oracle does not run the navigator (AC_WPNav / SimplePath), so it needs the tick at which the
mission completes and `ModeAuto::loiter_start` switches AutoYaw to HOLD (`--hold-from`).

Run from the package root:
  lake env lean --run oracle/probe/ModeSchedule.lean INPUTS PARAMS_FILE...

`toMicros`, `parseInput?` and `applyLines` are copies of the same functions of
`Copter/Main.lean` (that module also defines `main`, so it cannot be imported here).
-/
namespace ProbeCli
open AP_Math Copter Copter.Text
def toMicros (d : Decimal) : Option Nat :=
  if d.neg then none
  else
    let e := d.e + 6
    if 0 ≤ e then some (d.m * 10 ^ e.toNat)
    else
      let q := 10 ^ e.natAbs
      some ((2 * d.m + q) / (2 * q))

/-- Parse one simulator line, or fail if it does not hold exactly 17 numbers with `dt > 0`. -/
def parseInput? (line : String) : Option AHRS.Sample := do
  let xs ← (words line).mapM parseDecimal?
  match xs with
  | [x, y, z, vx, vy, vz, ax, ay, az, q1, q2, q3, q4, gp, gq, gr, dt] =>
    let dt_us ← toMicros dt
    if dt_us == 0 then none
    let f := Decimal.toFloat32
    pure { pos := ⟨x.toFloat, y.toFloat, z.toFloat⟩, vel := ⟨f vx, f vy, f vz⟩,
           accel_ef := ⟨f ax, f ay, f az⟩, quat := ⟨f q1, f q2, f q3, f q4⟩,
           gyro := ⟨f gp, f gq, f gr⟩, dt_us }
  | _ => none

/-- Apply override lines in order (see the module docstring). -/
def applyLines (base : Parameters) (lines : List String) : Except String Parameters := do
  let mut q := base
  let mut wps : Array Vector3p := #[]
  let mut cleared := false
  for line in lines do
    let body := String.ofList ((line.toList.takeWhile (· != '#')).map fun c => if c == ',' then ' ' else c)
    match words body with
    | [] => continue
    | ["mission.clear"] =>
      wps := #[]
      cleared := true
    | "waypoint" :: rest =>
      match rest.mapM parseDecimal? with
      | some [n, e, dd] => wps := wps.push ⟨n.toFloat, e.toFloat, dd.toFloat⟩
      | _ => throw s!"waypoint needs N E D: {line}"
    | [name, v] =>
      let some d := parseDecimal? v | throw s!"bad number in parameter line: {line}"
      let some q' := setParam q name d | throw s!"unknown parameter or value out of range: {line}"
      q := q'
    | _ => throw s!"expected NAME VALUE: {line}"
  if wps.isEmpty && !cleared then pure q else pure { q with mission := wps.toList }

end ProbeCli
open Copter ProbeCli

def modeStr : Copter.SubMode → String
  | .STARTING => "STARTING" | .WP => "WP" | .LOITER => "LOITER"
def yawStr : Copter.AutoYawMode → String
  | .HOLD => "HOLD" | .LOOK_AT_NEXT_WP => "LOOK_AT_NEXT_WP" | .LOOK_AHEAD => "LOOK_AHEAD"

def main (args : List String) : IO UInt32 := do
  let mut fileLines : List String := []
  let some inputs := args.head? | IO.eprintln "usage: ModeSchedule INPUTS PARAMS_FILE..."; return 2
  for f in args.tail do
    let txt ← IO.FS.readFile f
    fileLines := fileLines ++ txt.splitOn "\n"
  let .ok p := applyLines defaults fileLines | return 2
  let txt ← IO.FS.readFile inputs
  let mut st := State.init p
  let mut started := false
  let mut n : Nat := 0
  let mut prev := ""
  for line in txt.splitOn "\n" do
    if (Copter.Text.words line).isEmpty then continue
    let some smp := parseInput? line | return 3
    if !started then
      st := takeover p st smp
      started := true
    let some st' := loop p st smp | return 4
    st := st'
    n := n + 1
    let navidx := match st.mode_auto.mission.nav_cmd with | none => 0 | some c => c.index
    let cur := s!"{modeStr st.mode_auto._mode} {yawStr st.auto_yaw._mode} nav_cmd {navidx}"
    if cur != prev then
      IO.println s!"tick {n}: {cur}"
      prev := cur
  IO.println s!"ticks {n}"
  return 0
