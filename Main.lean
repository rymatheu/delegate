import Shell.Tools

/-!
# Main (`leanfc`: the flight controller's IO shell)

The only IO of the flight controller: standard input and output in lock step with the simulator
(`sim/run_leanfc.py`), one 400 Hz tick per line, the parameter files, and, with `--mav`, one UDP
socket to the ground station (`Shell/Link.lean`). Each tick is the pure `Autopilot.step` (services
→ vehicle layer → controller) or, without a ground station, the pure `Autopilot.run` (vehicle layer
→ controller).

Input, one line per tick, 16 whitespace-separated decimals:
`gx gy gz  ax ay az  fix  hc hs  pn pe pd  vn ve vd  vfix` — gyro (rad/s, body), accelerometer
specific force (m/s², body), fix presence (1 or 0; with 0 the heading and the position fix are
`none`), heading (cos ψ, sin ψ), position fix (NED m), velocity fix (NED m/s), velocity-fix
presence (1 or 0) — optionally followed by a 17th, position-fix presence (1 or 0, default 1; with
0 the position fix is `none` while the heading stays, for GPS dropouts). Each decimal is rounded
once, directly to binary32 (FloatLib's `OfScientific`, round to nearest even).

Output, one line per input line: `m1 m2 m3 m4`; with `--trace` also p̂ (3), v̂ (3), q̂ (4) of the
active estimator, the navigator target pSp (3) and the leg index; with `--trace-ekf` also the
diagonal of P (15) and the gyro and accelerometer bias estimates (3 + 3) (for the fixed
estimator: zeros for P, the attitude filter's gyro bias and the nav filter's world-frame
acceleration bias); with `--trace`, then, the heading setpoint (cos ψ, sin ψ) (2), after the
`--trace-ekf` fields so that every earlier field keeps its position; with `--trace-vehicle`, last,
the mode number, armed (0/1), landed state (1..4) and current mission item. Numbers print with 9
significant digits, which round-trips binary32; `--bits` appends ` |` and the 8-digit hex words
of the binary32 numbers. A line that does not parse is reported on standard error and answered
with zeros; the state does not advance. Blank lines are ignored. Standard output is flushed after
every line.

Start:

- default (the batch start, today's behavior): the vehicle is in the air at the file's start
  point, armed, in AUTO, flying the file's mission; `--calibrate N` takes the first N lines as
  at-rest gyro samples (then prints `calibrated`). The output is that of the controller alone.
- `--ground`: on the ground, disarmed, in STABILIZE (ArduCopter's boot mode); the gyros are
  calibrated from the first second of lines and the estimator starts at the first fixes
  (`Copter.Fly`). The onboard mission is the one the files state, with their `TAKEOFF` and `LAND`
  lines around the waypoints (`Leanfc/ParamFile.lean`, `Setup.mission`), so that AUTO from the
  ground (QGroundControl's Start Mission) needs no upload; an upload replaces it.

`--mav` opens the MAVLink link (`--host` 127.0.0.1, `--port` 14550: the ground station;
`--bind-host` 127.0.0.1, `--bind` 0: our socket; `--sysid N`, default the compatibility parameter
MAV_SYSID; `--origin LAT LON ALT`, default the files' `ORIGIN` line, else Pikes Peak summit;
`--log FILE`, every frame received and sent). Without it (`--no-mav`, the default) no socket is
opened and the run is deterministic.

Other modes: `--params FILE` (required except with `--check` and `--codec`; may be repeated,
later files override earlier ones), `--print-params`, `--ekf-only` (the EKF alone, its state as hex
words per tick, for `sim/ekf_parity.py`: a `const` line, an `init` line, then q (4), ω̂ (3), p (3),
v (3), bg (3), ba (3), P row-major (225)), `--check` (the checks of `Leanfc/Checks.lean` on the
shipped files in the working directory, and the parameter table's coverage), `--codec`, `--bench`,
`--selftest` (`Shell/Tools.lean`). A file that does not load is reported on standard error with
its line and the program exits with status 2.
-/

open Mavlink

/-- Read and load the files; the error message on failure. -/
def loadFiles (paths : List String) : IO (Except String Params) := do
  let mut texts : List (String × String) := []
  for f in paths do
    try texts := texts ++ [(f, ← IO.FS.readFile f)]
    catch e => return .error s!"{f}: cannot read: {e}"
  return ParamFile.load texts

def runChecks : IO UInt32 := do
  let load (f : List String) : IO (Option Params) := do
    match ← loadFiles f with
    | .ok P => return some P
    | .error e => IO.eprintln e; return none
  let some cf2x ← load ["params/cf2x.params"] | return 2
  let some x500 ← load ["params/x500.params"] | return 2
  let some x500m ← load ["params/x500.params", "params/mocap.params"] | return 2
  let some cf2xS ← load ["params/cf2x.params", "params/cf2x-spline.params"] | return 2
  let some x500S ← load ["params/x500.params", "params/x500-spline.params"] | return 2
  let some x500X ← load ["params/x500.params", "sim/missions/x500-mixed.params"] | return 2
  let rs := Checks.runChecks cf2x x500 x500m
    [("cf2x waypoint square", cf2x), ("cf2x spline square", cf2xS), ("x500 waypoint square", x500),
     ("x500 spline square", x500S), ("x500 mixed mission", x500X)]
  -- the parameter service covers every parameter of the files, once
  let files := Mavlink.ParamTable.entries.map (·.file)
  let names := Mavlink.ParamTable.entries.map (·.name)
  let covered := ParamFile.names.all (fun k => files.contains k) && files.size == ParamFile.names.length &&
    names.all (fun n => n.length ≤ 16 && (names.filter (· == n)).size == 1)
  let rs := rs ++ [(s!"MAVLink parameter table: every one of the {ParamFile.names.length} file parameters served once, names unique and at most 16 characters", covered)]
  for (name, ok) in rs do
    IO.println s!"{if ok then "PASS" else "FAIL"}  {name}"
  return if rs.all (·.2) then 0 else 1

/-- The lock-step loop over a state `σ`: the first `nCal` lines are calibration samples (`cal`,
then `calibrated` and the optional `afterCal` line), then one `tick` per line of 16 or 17 numbers;
`zeros` answers a line that does not parse. -/
def loop {σ : Type} (nCal : Nat) (st0 : σ) (cal : Array Vec3 → σ → σ) (afterCal : σ → Option String)
    (tick : σ → Sensors → IO (σ × String)) (zeros : String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st := st0
  let mut samples : Array Vec3 := #[]
  let mut calibrated : Bool := nCal == 0
  if calibrated then
    if let some l := afterCal st then stdout.putStrLn l; stdout.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break                     -- end of input
    if line.all Char.isWhitespace then continue    -- blank line
    match parseLine line with
    | none =>
      IO.eprintln s!"unparsable line: {chomp line}"
      if calibrated then stdout.putStrLn zeros; stdout.flush
    | some a =>
      if !calibrated then
        if a.size < 3 then IO.eprintln s!"calibration line needs a gyro sample: {chomp line}"
        else
          samples := samples.push (v3 a 0)
          if samples.size = nCal then
            st := cal samples st
            calibrated := true
            stdout.putStrLn "calibrated"
            if let some l := afterCal st then stdout.putStrLn l
            stdout.flush
      else if a.size != 16 && a.size != 17 then
        IO.eprintln s!"expected 16 or 17 numbers, got {a.size}: {chomp line}"
        stdout.putStrLn zeros; stdout.flush
      else
        let (st', out) ← tick st (sensorsOf a)
        st := st'
        stdout.putStrLn out; stdout.flush

def main (args : List String) : IO UInt32 := do
  if args.contains "--codec" then
    codecLoop (← IO.getStdin) (← IO.getStdout) {}
    return 0
  if args.contains "--bench" then return (← bench args)
  if args.contains "--selftest" then return (← selftest args)
  if args.contains "--check" then return (← runChecks)
  let nCal := argNat args "--calibrate" 0
  let trace := args.contains "--trace"
  let traceEkf := args.contains "--trace-ekf"
  let traceVeh := args.contains "--trace-vehicle"
  let bits := args.contains "--bits"
  let files := argAll args "--params"
  if files.isEmpty then
    IO.eprintln "--params FILE is required (see params/*.params)"; return 2
  let P ← match ← loadFiles files with
    | .ok P => pure P
    | .error e => IO.eprintln s!"parameter file: {e}"; return 2
  if args.contains "--print-params" then
    for l in paramLines P do IO.println l
    return 0
  if args.contains "--ekf-only" then
    IO.println (ekfConstLine P.ekf)
    loop nCal (EKF.init P.ekf P.start Quat.identity) (EKF.calibrate P.ekf)
      (fun e => some ("init " ++ ekfStateLine e))
      (fun e s =>
        let (e, _) := EKF.step P.ekf e s.gyro s.accel s.heading s.position s.velocity
        pure (e, ekfStateLine e))
      "unparsable"
    return 0
  -- the flight controller: vehicle layer + controller, with or without the services
  let su ← match ← setup args with
    | .ok su => pure su
    | .error e => IO.eprintln e; return 2
  let ground := args.contains "--ground"
  let mission := su.mission ground
  let veh := if ground then Copter.initGround P mission else Copter.initAir P mission
  let a0 : Autopilot :=
    { cfg := su.cfg, gcs := su.gcs (su.missionHome ground veh.home) mission, veh, origin := su.origin }
  let cal (smp : Array Vec3) (a : Autopilot) : Autopilot :=
    { a with veh := { a.veh with ctl := Controller.calibrate P smp a.veh.ctl } }
  let line (a : Autopilot) (m : Motors) : String :=
    outputLine trace traceEkf bits a.veh.ctl m (if traceVeh then vehicleFields a.veh else "")
  let zeros := zerosLine trace traceEkf
  if args.contains "--mav" && !args.contains "--no-mav" then
    let host := (argOne args "--host").getD "127.0.0.1"
    let port := ((argOne args "--port").bind String.toNat?).getD 14550
    let bindHost := (argOne args "--bind-host").getD "127.0.0.1"
    let bindPort := ((argOne args "--bind").bind String.toNat?).getD 0
    let link ← match ← Link.open_ host port bindHost bindPort (argOne args "--log") su.cfg.sysid su.cfg.compid with
      | .ok (l, p) => IO.eprintln s!"leanfc: MAVLink system {su.cfg.sysid}, {bindHost}:{p} -> {host}:{port}"; pure l
      | .error e => IO.eprintln e; return 2
    let dt := R.toFloat P.dt
    loop nCal a0 cal (fun _ => none)
      (fun a s => do
        let tSec := a.veh.tick.toFloat * dt
        let inc ← link.take tSec
        let (a, m, out) := a.step s inc
        link.send tSec out
        pure (a, line a m))
      zeros
    link.close
    (← IO.getStdout).flush
    -- the receiver thread is blocked in `recv`; the runtime would wait for it at exit
    IO.Process.exit 0
  else
    loop nCal a0 cal (fun _ => none) (fun a s => let (a, m) := a.run s; pure (a, line a m)) zeros
  return 0
