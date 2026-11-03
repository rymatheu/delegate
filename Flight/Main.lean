import Flight.Controller
import Flight.FloatInstance
import Flight.TestPlant

/-!
# Executable entry point

`flight` runs the controller over `Float` against an external simulator through standard streams:
each input line holds 13 whitespace-separated numbers

  `x y z  vx vy vz  roll pitch yaw  p q r  dt`

(NED meters, meters per second, radians, radians per second, seconds), and each output line holds
the four motor commands `m1 m2 m3 m4` in `[0, 1]`. Controller state is kept across lines. A line
that does not parse is reported on standard error and answered with all motors at zero, so the
simulator stays in lock-step; blank lines are ignored.

`flight --selftest` instead closes the loop for 2000 ticks of 10 ms against the crude plant of
`Flight.TestPlant` and prints a short trace and the final position.

Options (all optional, in any order):
* `--params <file>` reads parameter overrides from a text file, one per line: a dotted key naming a
  field of `Controller.Params` followed by its value(s), e.g. `rate.roll.kp 0.05`; `#` starts a
  comment. A line `waypoint N E D yaw` appends a mission item; if the lines give any waypoint,
  those replace the built-in mission, and a line `mission.clear` drops the waypoints collected so
  far (and replaces the built-in mission even if no waypoint follows). Keys are listed in
  `Flight.Cli.applyKey`. The option may be repeated; files are read in order.
* `--set "<key> <value>..."` applies one more override line after the file; repeatable.
* `--exact` prints each motor command as the exact decimal expansion of its binary64 value
  (binary fractions have finite decimal expansions), so two runs can be compared bit for bit;
  without it commands are printed by `Float.toString` (six decimals).
* `--print-params` prints the effective parameters in the file format and exits.
* `--trace` appends to each output line the navigator's output and memory for logging: position
  setpoint (3), velocity feed-forward (3), acceleration feed-forward (3), heading setpoint and
  index, in the same number format.
  The first four numbers are the motor commands, unchanged.

The overrides only choose values for the existing parameter records; the control modules are not
changed by this file.
-/

namespace Flight

namespace Cli

/-- The built-in mission: climb to 5 m, fly 10 m north, then 10 m east while turning to face east. -/
def defaultMission : List (Waypoint Float) :=
  [⟨⟨0, 0, -5⟩, 0⟩, ⟨⟨10, 0, -5⟩, 0⟩, ⟨⟨10, 10, -5⟩, 1.5707963267948966⟩]

/-- Controller parameters used by the executable unless overridden: library defaults with the built-in mission. -/
def defaultParams : Controller.Params Float := { nav := { waypoints := defaultMission } }

/-- Split a line into its whitespace-separated words. -/
def words (line : String) : List String :=
  let step := fun (acc : List String × List Char) (c : Char) =>
    if c.isWhitespace then
      (if acc.2.isEmpty then acc.1 else String.ofList acc.2.reverse :: acc.1, [])
    else (acc.1, c :: acc.2)
  let (ws, cur) := line.toList.foldl step ([], [])
  (if cur.isEmpty then ws else String.ofList cur.reverse :: ws).reverse

/-- Read a non-empty string of decimal digits as a natural number. -/
def digits? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldl (fun acc c => acc.bind fun n =>
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- Read an optional sign, returning whether it was a minus and the remaining characters. -/
def sign (cs : List Char) : Bool × List Char :=
  match cs with
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | _ => (false, cs)

/-- Parse a decimal number such as `-12`, `0.5`, `.25` or `1.5e-3`. -/
def parseFloat? (s : String) : Option Float := do
  let (neg, body) := sign s.toList
  let (mant, expPart) := body.span (fun c => c != 'e' && c != 'E')
  let (intPart, fracPart) := mant.span (· != '.')
  let fracDigits := fracPart.drop 1
  if intPart.isEmpty && fracDigits.isEmpty then none
  let m ← digits? (intPart ++ fracDigits)
  let e : Int ← match expPart with
    | [] => pure 0
    | _ :: rest =>
      let (eneg, edigits) := sign rest
      let n ← digits? edigits
      pure (if eneg then -(n : Int) else n)
  let decExp := e - fracDigits.length
  let mag := if decExp < 0 then Float.ofScientific m true decExp.natAbs
    else Float.ofScientific m false decExp.toNat
  pure (if neg then -mag else mag)

/-- Parse one simulator line into a controller input, or fail if it does not hold exactly 13 numbers. -/
def parseInput? (line : String) : Option (SimInput Float) := do
  let xs ← (words line).mapM parseFloat?
  match xs with
  | [x, y, z, vx, vy, vz, φ, θ, ψ, p, q, r, dt] =>
    pure ⟨⟨x, y, z⟩, ⟨vx, vy, vz⟩, ⟨φ, θ, ψ⟩, ⟨p, q, r⟩, dt⟩
  | _ => none

/-- The exact decimal expansion of a finite binary64 value (`nan`, `inf`, `-inf` otherwise); trailing fractional zeros are dropped. -/
def exactDecimal (x : Float) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else
    let bits : Nat := x.toBits.toNat
    let neg := bits / 2 ^ 63 == 1
    let expField : Nat := (bits / 2 ^ 52) % 2048
    let frac : Nat := bits % 2 ^ 52
    -- value = m * 2^e
    let (m, e) : Nat × Int :=
      if expField == 0 then (frac, -1074) else (frac + 2 ^ 52, Int.ofNat expField - 1075)
    let body :=
      if 0 ≤ e then toString (m * 2 ^ e.toNat)
      else
        let k := e.natAbs
        -- m / 2^k = m * 5^k / 10^k
        let ds := (toString (m * 5 ^ k)).toList
        let ds := List.replicate (k + 1 - ds.length) '0' ++ ds
        let intPart := ds.take (ds.length - k)
        let fracPart := ((ds.drop (ds.length - k)).reverse.dropWhile (· == '0')).reverse
        if fracPart.isEmpty then String.ofList intPart
        else String.ofList intPart ++ "." ++ String.ofList fracPart
    if neg && m != 0 then "-" ++ body else body

/-- Format four motor commands as one output line, exactly if `exact` is set. -/
def formatMotors (m : Motors Float) (exact : Bool := false) : String :=
  let f := fun (x : Float) => if exact then exactDecimal x else toString x
  s!"{f m.m1} {f m.m2} {f m.m3} {f m.m4}"

/-- Set one field of a PID gain record by name. -/
def setPid (g : PidGains Float) (field : String) (v : Float) : Option (PidGains Float) :=
  match field with
  | "kp" => some { g with kp := v }
  | "ki" => some { g with ki := v }
  | "kd" => some { g with kd := v }
  | "iMax" => some { g with iMax := v }
  | _ => none

/-- Apply one override `key values` to the parameters; `none` if the key is unknown or the arity is wrong. -/
def applyKey (p : Controller.Params Float) (key : String) (vs : List Float) :
    Option (Controller.Params Float) :=
  match key.splitOn ".", vs with
  | ["nav", "acceptRadius"], [v] => some { p with nav := { p.nav with acceptRadius := v } }
  | ["nav", "wpSpeed"], [v] => some { p with nav := { p.nav with wpSpeed := v } }
  | ["nav", "wpAccel"], [v] => some { p with nav := { p.nav with wpAccel := v } }
  | ["nav", "cornerRadius"], [v] => some { p with nav := { p.nav with cornerRadius := v } }
  | ["nav", "yawAlongPath"], [v] =>
    if v == 0 then some { p with nav := { p.nav with yawAlongPath := false } }
    else if v == 1 then some { p with nav := { p.nav with yawAlongPath := true } } else none
  | ["pos", "posGainXY"], [v] => some { p with pos := { p.pos with posGainXY := v } }
  | ["pos", "posGainZ"], [v] => some { p with pos := { p.pos with posGainZ := v } }
  | ["pos", "maxSpeedXY"], [v] => some { p with pos := { p.pos with maxSpeedXY := v } }
  | ["pos", "maxSpeedZ"], [v] => some { p with pos := { p.pos with maxSpeedZ := v } }
  | ["pos", "maxAccelXY"], [v] => some { p with pos := { p.pos with maxAccelXY := v } }
  | ["pos", "maxAccelZ"], [v] => some { p with pos := { p.pos with maxAccelZ := v } }
  | ["pos", "velXY", f], [v] => (setPid p.pos.velXY f v).map fun g => { p with pos := { p.pos with velXY := g } }
  | ["pos", "velZ", f], [v] => (setPid p.pos.velZ f v).map fun g => { p with pos := { p.pos with velZ := g } }
  | ["target", "gravity"], [v] => some { p with target := { p.target with gravity := v } }
  | ["target", "hoverThrottle"], [v] => some { p with target := { p.target with hoverThrottle := v } }
  | ["target", "maxLean"], [v] => some { p with target := { p.target with maxLean := v } }
  | ["att", "rollGain"], [v] => some { p with att := { p.att with rollGain := v } }
  | ["att", "pitchGain"], [v] => some { p with att := { p.att with pitchGain := v } }
  | ["att", "yawGain"], [v] => some { p with att := { p.att with yawGain := v } }
  | ["att", "maxRollPitchRate"], [v] => some { p with att := { p.att with maxRollPitchRate := v } }
  | ["att", "maxYawRate"], [v] => some { p with att := { p.att with maxYawRate := v } }
  | ["rate", "roll", f], [v] => (setPid p.rate.roll f v).map fun g => { p with rate := { p.rate with roll := g } }
  | ["rate", "pitch", f], [v] => (setPid p.rate.pitch f v).map fun g => { p with rate := { p.rate with pitch := g } }
  | ["rate", "yaw", f], [v] => (setPid p.rate.yaw f v).map fun g => { p with rate := { p.rate with yaw := g } }
  | ["mixer", "f1"], [r, q, y] => some { p with mixer := { p.mixer with f1 := ⟨r, q, y⟩ } }
  | ["mixer", "f2"], [r, q, y] => some { p with mixer := { p.mixer with f2 := ⟨r, q, y⟩ } }
  | ["mixer", "f3"], [r, q, y] => some { p with mixer := { p.mixer with f3 := ⟨r, q, y⟩ } }
  | ["mixer", "f4"], [r, q, y] => some { p with mixer := { p.mixer with f4 := ⟨r, q, y⟩ } }
  | _, _ => none

/-- Apply override lines in order; `waypoint` lines are collected and, if any (or after `mission.clear`), replace the mission. -/
def applyLines (base : Controller.Params Float) (lines : List String) :
    Except String (Controller.Params Float) := do
  let mut p := base
  let mut wps : Array (Waypoint Float) := #[]
  let mut cleared := false
  for line in lines do
    let ws := words (String.ofList (line.toList.takeWhile (· != '#')))
    match ws with
    | [] => continue
    | key :: rest =>
      let some vs := rest.mapM parseFloat? | throw s!"bad number in parameter line: {line}"
      if key == "mission.clear" then
        wps := #[]
        cleared := true
      else if key == "waypoint" then
        match vs with
        | [n, e, d, yaw] => wps := wps.push ⟨⟨n, e, d⟩, yaw⟩
        | _ => throw s!"waypoint needs N E D yaw: {line}"
      else
        let some p' := applyKey p key vs | throw s!"unknown key or wrong number of values: {line}"
        p := p'
  if wps.isEmpty && !cleared then pure p else pure { p with nav := { p.nav with waypoints := wps.toList } }

/-- Print the effective parameters in the override-file format. -/
def showParams (p : Controller.Params Float) : List String :=
  let pid := fun (k : String) (g : PidGains Float) =>
    [s!"{k}.kp {g.kp}", s!"{k}.ki {g.ki}", s!"{k}.kd {g.kd}", s!"{k}.iMax {g.iMax}"]
  let mf := fun (k : String) (f : MotorFactors Float) => s!"{k} {f.roll} {f.pitch} {f.yaw}"
  p.nav.waypoints.map (fun w => s!"waypoint {w.pos.x} {w.pos.y} {w.pos.z} {w.yaw}") ++
  [s!"nav.acceptRadius {p.nav.acceptRadius}", s!"nav.wpSpeed {p.nav.wpSpeed}",
   s!"nav.wpAccel {p.nav.wpAccel}", s!"nav.cornerRadius {p.nav.cornerRadius}",
   s!"nav.yawAlongPath {if p.nav.yawAlongPath then 1 else 0}",
   s!"pos.posGainXY {p.pos.posGainXY}", s!"pos.posGainZ {p.pos.posGainZ}",
   s!"pos.maxSpeedXY {p.pos.maxSpeedXY}", s!"pos.maxSpeedZ {p.pos.maxSpeedZ}"] ++
  pid "pos.velXY" p.pos.velXY ++ pid "pos.velZ" p.pos.velZ ++
  [s!"pos.maxAccelXY {p.pos.maxAccelXY}", s!"pos.maxAccelZ {p.pos.maxAccelZ}",
   s!"target.gravity {p.target.gravity}", s!"target.hoverThrottle {p.target.hoverThrottle}",
   s!"target.maxLean {p.target.maxLean}",
   s!"att.rollGain {p.att.rollGain}", s!"att.pitchGain {p.att.pitchGain}",
   s!"att.yawGain {p.att.yawGain}", s!"att.maxRollPitchRate {p.att.maxRollPitchRate}",
   s!"att.maxYawRate {p.att.maxYawRate}"] ++
  pid "rate.roll" p.rate.roll ++ pid "rate.pitch" p.rate.pitch ++ pid "rate.yaw" p.rate.yaw ++
  [mf "mixer.f1" p.mixer.f1, mf "mixer.f2" p.mixer.f2, mf "mixer.f3" p.mixer.f3,
   mf "mixer.f4" p.mixer.f4]

/-- The navigator's output and memory, appended to an output line by `--trace`. -/
def formatNav (n : NavOutput Float) (index : Nat) (exact : Bool) : String :=
  let f := fun (x : Float) => if exact then exactDecimal x else toString x
  s!"{f n.posSp.x} {f n.posSp.y} {f n.posSp.z} {f n.velSp.x} {f n.velSp.y} {f n.velSp.z} {f n.accSp.x} {f n.accSp.y} {f n.accSp.z} {f n.yawSp} {index}"

/-- Serve the controller over standard input and output until end of input. -/
def runStdio (params : Controller.Params Float) (exact : Bool) (trace : Bool := false) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st : Controller.State Float := Controller.State.init
  let mut lineNo : Nat := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    lineNo := lineNo + 1
    if (words line).isEmpty then continue
    match parseInput? line with
    | some inp =>
      let (st', tr) := Controller.stepTrace params st inp
      st := st'
      if trace then
        stdout.putStrLn (formatMotors tr.motors exact ++ " " ++ formatNav tr.nav st'.nav.index exact)
      else stdout.putStrLn (formatMotors tr.motors exact)
    | none =>
      IO.eprintln s!"flight: line {lineNo}: expected 13 numbers (pos, vel, roll pitch yaw, p q r, dt)"
      stdout.putStrLn (if trace then "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" else "0 0 0 0")
    stdout.flush

/-- Format a vector to three decimals per component, for the self-test trace. -/
def fmtVec (v : Vec3 Float) : String :=
  let r := fun (x : Float) => toString ((x * 1000).round / 1000)
  s!"({r v.x}, {r v.y}, {r v.z})"

/-- Close the loop against the built-in plant for 2000 ticks and print a trace and the final position. -/
def runSelfTest (params : Controller.Params Float) : IO Unit := do
  let plant : TestPlant.Params := {}
  let dt : Float := 0.01
  let mut ps := TestPlant.State.init
  let mut cs : Controller.State Float := Controller.State.init
  IO.println s!"selftest: 2000 ticks of {dt} s against the built-in plant; mission (NED) {params.nav.waypoints.map (fun w => fmtVec w.pos)}"
  for i in [0:2000] do
    let (cs', tr) := Controller.stepTrace params cs (ps.measure dt)
    cs := cs'
    ps := TestPlant.step plant ps tr.motors dt
    if (i + 1) % 200 == 0 then
      IO.println s!"t={(i + 1).toFloat * dt} wp={cs.nav.index} pos={fmtVec ps.pos} vel={fmtVec ps.vel} yaw={(ps.att.yaw * 1000).round / 1000} thrust={(tr.target.thrust * 1000).round / 1000}"
  let goal := (params.nav.waypoints.getLast?.map (·.pos)).getD Vec3.zero
  IO.println s!"final position {fmtVec ps.pos}, distance to final waypoint {(Vec3.norm (goal - ps.pos) * 1000).round / 1000} m"

/-- Command-line options. -/
structure Options where
  /-- Run the built-in closed loop instead of serving standard streams. -/
  selftest : Bool := false
  /-- Print motor commands exactly. -/
  exact : Bool := false
  /-- Print the effective parameters and exit. -/
  printParams : Bool := false
  /-- Append the navigator's output to every output line. -/
  trace : Bool := false
  /-- Parameter files, read in order. -/
  paramsFiles : Array String := #[]
  /-- Extra override lines from `--set`, in order. -/
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
  | a :: _, _ => throw s!"unknown or incomplete option {a}; options: --selftest --exact --print-params --trace --params <file> --set \"<key> <values>\""

/-- Parse options, load parameters, and dispatch. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => IO.eprintln s!"flight: {e}"; return 2
  | .ok o =>
    let mut fileLines : List String := []
    for f in o.paramsFiles do
      let txt ← IO.FS.readFile f
      fileLines := fileLines ++ txt.splitOn "\n"
    match applyLines defaultParams (fileLines ++ o.sets.toList) with
    | .error e => IO.eprintln s!"flight: {e}"; return 2
    | .ok params =>
      if o.printParams then
        for l in showParams params do IO.println l
      else if o.selftest then runSelfTest params
      else runStdio params o.exact o.trace
      return 0

end Cli

end Flight

/-- Entry point: `--selftest` runs the built-in closed loop, otherwise serve the controller over standard streams; see the module docstring for the other options. -/
def main (args : List String) : IO UInt32 := Flight.Cli.main args
