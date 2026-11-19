import Vehicle

/-!
# `copter_lean`: the lock-step protocol (sim/PROTOCOL.md) over `Vehicle`

`copter_lean [--params FILE]... [--set "NAME VALUE"]... [--exact] [--trace] [--bits] [--print-params]`

One input line per tick (17 numbers), one output line per input line (4 actuators, with `--trace`
the 18 trace numbers), flushed after every line; as `ardupilot/vehicle/copter_ref.cpp` `main`.
-/

open Vehicle

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (exact trace bits : Bool) (w : Option World) (w0 : World) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  if line.trimAscii.isEmpty then
    loop h out exact trace bits w w0
    return
  match parseSample line.trimAscii.toString with
  | none =>
    IO.eprintln s!"copter_lean: bad input line: {line.trimAscii}"
    out.putStrLn (if trace then "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" else "0 0 0 0")
    out.flush
    loop h out exact trace bits w w0
  | some smp =>
    let wa := match w with
      | some x => x
      | none => takeover w0 smp
    let (w1, act) := tick wa smp
    let mut vals : Array Float := act.map Float32.toFloat
    let mut hex : Array String := act.map h32
    if trace then
      let (tv, th) := traceValues w1
      vals := vals ++ tv
      hex := hex ++ th
    let text := " ".intercalate (vals.toList.map fun x => if exact then exactDecimal x else sixDecimals x)
    let text := if bits then text ++ " |" ++ String.join (hex.toList.map (" " ++ ·)) else text
    out.putStrLn text
    out.flush
    loop h out exact trace bits (some w1) w0

def readLines (path : String) : IO (List String) := do
  let t ← IO.FS.readFile path
  return t.splitOn "\n"

/-- sim/BENCH.md: all of standard input, parsed, before anything is timed. -/
partial def readSamples (h : IO.FS.Stream) (acc : Array Sample) : IO (Array Sample) := do
  let line ← h.getLine
  if line.isEmpty then return acc
  let t := line.trimAscii.toString
  if t.isEmpty then return (← readSamples h acc)
  match parseSample t with
  | none => throw (IO.userError s!"copter_lean: bad input line: {t}")
  | some smp => readSamples h (acc.push smp)

/-- The ticks alone, with no parsing and no printing: elapsed nanoseconds, tick count, and a checksum
of the actuator bits (the sum of their 32-bit patterns), as `copter_ref --bench` prints them. -/
def bench (w0 : World) (samples : Array Sample) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut w : Option World := none
  let mut checksum : UInt64 := 0
  for smp in samples do
    let wa := match w with
      | some x => x
      | none => takeover w0 smp
    let (w1, act) := tick wa smp
    for a in act do
      checksum := checksum + a.toBits.toUInt64
    w := some w1
  let t1 ← IO.monoNanosNow
  IO.println s!"{t1 - t0} {samples.size} {hex 16 checksum.toNat}"

def main (args : List String) : IO UInt32 := do
  let mut lines : List String := []
  let mut printParams := false
  let mut exact := false
  let mut trace := false
  let mut bits := false
  let mut doBench := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--params" :: f :: r =>
      lines := lines ++ (← readLines f)
      rest := r
    | "--set" :: s :: r =>
      lines := lines ++ [s]
      rest := r
    | "--print-params" :: r => printParams := true; rest := r
    | "--exact" :: r => exact := true; rest := r
    | "--trace" :: r => trace := true; rest := r
    | "--bits" :: r => bits := true; rest := r
    | "--bench" :: r => doBench := true; rest := r
    | _ =>
      IO.eprintln "usage: copter_lean [--params FILE]... [--set \"NAME VALUE\"]... [--exact] [--trace] [--bits] [--print-params] [--bench]"
      return 2
  match construct lines with
  | .error e =>
    IO.eprintln s!"copter_lean: {e}"
    return 2
  | .ok w =>
    if printParams then
      for l in paramLines w do
        IO.println l
      return 0
    if w.h.WP_YAW_BEHAVIOR < 0 || w.h.WP_YAW_BEHAVIOR > 2 then
      IO.eprintln "copter_lean: only WP_YAW_BEHAVIOR 0, 1 or 2 is mirrored"
      return 2
    if w.mission.isEmpty then
      IO.eprintln "copter_lean: empty mission"
      return 2
    if doBench then
      let samples ← readSamples (← IO.getStdin) #[]
      bench (boot w) samples
      return 0
    loop (← IO.getStdin) (← IO.getStdout) exact trace bits none (boot w)
    return 0
