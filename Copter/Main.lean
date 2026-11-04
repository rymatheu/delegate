import Copter

/-!
# The `copter` executable

Runs `Copter.loop` (one ArduCopter 400 Hz tick in Auto, `Copter/Loop.lean`) in lock-step with an
external simulator over standard streams, with the conventions of `Flight/Main.lean`. The protocol
is fixed; `Copter/PROTOCOL.md` has the same text.

## Input: one line per tick, 17 whitespace-separated numbers

  `x y z  vx vy vz  ax ay az  q1 q2 q3 q4  p q r  dt`

- `x y z`: NED position from the EKF origin, m (read as `double`, ArduPilot's `postype_t` in SITL);
- `vx vy vz`: NED velocity, m/s;
- `ax ay az`: the earth-frame specific force in NED, m/s², as `AP_AHRS::get_accel_ef()` returns it:
  at rest it is `0 0 -9.80665`; the controller adds `GRAVITY_MSS` to `az`
  (`AC_PosControl::get_estimated_accel_D_mss`);
- `q1 q2 q3 q4`: the body-to-NED attitude quaternion in ArduPilot's convention
  (`AP_AHRS::get_quat_body_to_ned`), `q1` the scalar part;
- `p q r`: body rates (`get_gyro_latest`), rad/s, body frame forward-right-down;
- `dt`: the period of this tick, s; it is rounded to whole microseconds (the scheduler's clock) and
  must be positive. The default rate is 400 Hz, `dt = 0.0025`.

All but `x y z` and `dt` are read as `float`, each decimal rounded once to the nearest `float`.

## Output: one line per input line

  `m1 m2 m3 m4`

the actuator values in [0, 1] (`AP_MotorsMulticopter::_actuator`, after the thrust curve, spin
range and slew, before the PWM conversion) for ArduPilot motor slots 0..3 of the quad X frame
(`AP_MotorsMatrix::setup_quad_matrix`, `MOTOR_FRAME_TYPE_X`, `AP_MotorsMatrix.cpp:581-588`). The
angle is the motor arm's direction from the nose, in degrees, positive clockwise seen from above;
the spin direction is the propeller's, seen from above:

| slot | output (`SERVOn`) | angle | position   | spin | yaw factor |
|------|-------------------|-------|------------|------|------------|
| 0    | 1                 | +45   | front right| CCW  | +1         |
| 1    | 2                 | -135  | rear left  | CCW  | +1         |
| 2    | 3                 | -45   | front left | CW   | -1         |
| 3    | 4                 | +135  | rear right | CW   | -1         |

With `--trace` each line continues with, in this order (18 numbers): the navigator target as
`AC_PosControl` holds it after the tick, position (3, NED m: `get_pos_desired_NED_m`), velocity
(3: `get_vel_desired_NED_ms`) and acceleration (3: `_accel_desired_ned_mss`); the thrust vector
(3: `get_thrust_vector()`, `(a_N, a_E, -GRAVITY_MSS)`); the attitude target Euler angles (3, rad:
`get_att_target_euler_rad()`, roll pitch yaw); and the body-rate targets (3, rad/s:
`rate_bf_targets()`, the `_ang_vel_body_rads` that the next tick's rate controller will consume).
The position target equals what `AC_WPNav` sent unless a position controller moved it by its
error clamp.

A line that does not parse is reported on standard error and answered with zeros (4, or 22 with
`--trace`); the state is not advanced. Blank lines are ignored.

## Options

- `--params FILE`: parameter overrides, one per line, `NAME VALUE` with ArduPilot parameter names
  (`ATC_RAT_RLL_P 0.15`; a comma may separate name and value; `#` starts a comment; the pre-4.7
  `WPNAV_*` names are converted, see `Copter.Parameters`). A line `waypoint N E D` appends a mission
  item (NED m from the EKF origin); if the lines give any waypoint, those replace the built-in
  mission, and `mission.clear` drops the waypoints collected so far. Repeatable; read in order.
- `--set "NAME VALUE"`: one more override line, after the files; repeatable.
- `--exact`: print every number as the exact decimal expansion of its binary value (bit-for-bit
  comparable); otherwise `float`s print with six decimals.
- `--print-params`: print the effective parameters (exact values) and the mission, then exit.
- `--trace`: append the trace columns above.
- `--selftest`: run 100 ticks of hover at a fixed sample (level, at rest, 10 m above the origin,
  mission one waypoint at that point) and print the actuators.

The built-in mission is `waypoint 0 0 -5`, `waypoint 10 0 -5`, `waypoint 10 10 -5`. The vehicle is
assumed armed and flying; with the first sample the harness sets the initial condition
(`Copter.takeover`: attitude target at the sample's attitude and, with `run.start_hover 1`, the
default, a steady hover at `MOT_THST_HOVER`), and it enters Auto on the first tick (see
`Copter/Loop.lean`). An empty mission is refused, as `ModeAuto::init` refuses it.
-/

namespace Copter.Cli

open AP_Math Copter.Text

/-- Round an exact non-negative decimal number of seconds to whole microseconds (half up). -/
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

/-- The four actuator values. -/
def formatMotors (a : Vector ftype 4) (exact : Bool) : String :=
  " ".intercalate (a.toList.map (fmt32 exact))

/-- The trace columns (see the module docstring). -/
def formatTrace (s : State) (exact : Bool) : String :=
  let f := fmt32 exact
  let d := fmt64 exact
  let v3 := fun (v : Vector3f) => s!"{f v.x} {f v.y} {f v.z}"
  let psc := s.pos_control
  let pos := AC_PosControl.get_pos_desired_NED_m psc
  let att := s.attitude_control.toState
  s!"{d pos.x} {d pos.y} {d pos.z} {v3 (AC_PosControl.get_vel_desired_NED_ms psc)} {v3 psc._accel_desired_ned_mss} {v3 (AC_PosControl.get_thrust_vector psc)} {v3 (AC_AttitudeControl.get_att_target_euler_rad att)} {v3 (AC_AttitudeControl.rate_bf_targets att)}"

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

/-- Serve the loop over standard input and output until end of input. -/
def runStdio (p : Parameters) (exact trace : Bool) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st := State.init p
  let mut started := false
  let mut lineNo : Nat := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    lineNo := lineNo + 1
    if (words line).isEmpty then continue
    match parseInput? line with
    | some smp =>
      if !started then
        st := takeover p st smp
        started := true
      match loop p st smp with
      | some st' =>
        st := st'
        if trace then stdout.putStrLn (formatMotors st.actuators exact ++ " " ++ formatTrace st exact)
        else stdout.putStrLn (formatMotors st.actuators exact)
      | none =>
        IO.eprintln "copter: ModeAuto::init failed (empty mission)"
        return 1
    | none =>
      IO.eprintln s!"copter: line {lineNo}: expected 17 numbers (x y z vx vy vz ax ay az q1 q2 q3 q4 p q r dt) with dt > 0"
      stdout.putStrLn (" ".intercalate (List.replicate (if trace then 22 else 4) "0"))
    stdout.flush
  return 0

/-- 100 ticks of hover at a fixed sample; prints the actuators every 10 ticks and checks that the
four are equal. -/
def runSelfTest (p : Parameters) (exact : Bool) : IO UInt32 := do
  let p := { p with mission := [⟨0, 0, -10⟩] }
  let smp : AHRS.Sample :=
    { pos := ⟨0, 0, -10⟩, vel := {}, accel_ef := ⟨0, 0, -GRAVITY_MSS⟩, quat := {}, gyro := {},
      dt_us := 2500 }
  IO.println s!"selftest: 100 ticks of 2500 us; level, at rest at NED (0, 0, -10) m; mission: one waypoint at that point; MOT_THST_HOVER {fmt32 exact p.mot.MOT_THST_HOVER}"
  let mut st := takeover p (State.init p) smp
  let mut allEqual := true
  let mut prev : Vector ftype 4 := #v[0, 0, 0, 0]
  for i in [1:101] do
    match loop p st smp with
    | none => IO.eprintln "copter: ModeAuto::init failed"; return 1
    | some st' =>
      prev := st.actuators
      st := st'
      let a := st.actuators
      let eq := a[0].toBits == a[1].toBits && a[1].toBits == a[2].toBits && a[2].toBits == a[3].toBits
      allEqual := allEqual && eq
      if i % 10 == 0 || i ≤ 3 then
        IO.println s!"tick {i}: {formatMotors a exact}  throttle_in {fmt32 exact st.motors._throttle_in} throttle_filter {fmt32 exact st.motors._throttle_filter_value}"
  let a := st.actuators
  IO.println s!"final actuators (exact): {formatMotors a true}"
  IO.println s!"change over the last tick: {fmt32 true (a[0] - prev[0])}"
  IO.println s!"four actuators bitwise equal on every tick: {allEqual}"
  return (if allEqual then 0 else 1)

/-- Command-line options. -/
structure Options where
  selftest : Bool := false
  exact : Bool := false
  printParams : Bool := false
  trace : Bool := false
  paramsFiles : Array String := #[]
  sets : Array String := #[]

/-- Parse the command line. -/
def parseArgs : List String → Options → Except String Options
  | [], o => pure o
  | "--selftest" :: rest, o => parseArgs rest { o with selftest := true }
  | "--exact" :: rest, o => parseArgs rest { o with exact := true }
  | "--print-params" :: rest, o => parseArgs rest { o with printParams := true }
  | "--trace" :: rest, o => parseArgs rest { o with trace := true }
  | "--params" :: f :: rest, o => parseArgs rest { o with paramsFiles := o.paramsFiles.push f }
  | "--set" :: l :: rest, o => parseArgs rest { o with sets := o.sets.push l }
  | a :: _, _ => throw s!"unknown or incomplete option {a}; options: --selftest --exact --print-params --trace --params <file> --set \"<NAME> <VALUE>\""

/-- Parse options, load parameters, and dispatch. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => IO.eprintln s!"copter: {e}"; return 2
  | .ok o =>
    let mut fileLines : List String := []
    for f in o.paramsFiles do
      let txt ← IO.FS.readFile f
      fileLines := fileLines ++ txt.splitOn "\n"
    match applyLines defaults (fileLines ++ o.sets.toList) with
    | .error e => IO.eprintln s!"copter: {e}"; return 2
    | .ok params =>
      if o.printParams then
        for l in showParams params do IO.println l
        return 0
      else if o.selftest then runSelfTest params o.exact
      else if params.mission.isEmpty then
        IO.eprintln "copter: empty mission (ModeAuto::init would refuse Auto)"
        return 2
      else runStdio params o.exact o.trace

end Copter.Cli

/-- Entry point; see the module docstring. -/
def main (args : List String) : IO UInt32 := Copter.Cli.main args
