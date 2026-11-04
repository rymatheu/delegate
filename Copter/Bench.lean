import Copter

/-!
# The `bench` executable: execution time of one `Copter.loop` tick

Measures the port's control tick without parsing or printing, for the comparison with the C++
oracle's `--bench` mode (`oracle/bench.py`, `oracle/BENCH.md`). Not ArduPilot code.

    lake exe bench INPUTS [--params FILE]... [--set "NAME VALUE"]... [--warmup W] [--passes P]

Protocol (the same as `oracle/main.cpp --bench`):
1. read every line of `INPUTS` (the 17-number lines of `Copter/PROTOCOL.md`) and parse them into an
   array of `AHRS.Sample`s, apply the parameter overrides, build `State.init` and apply `takeover`
   with the first sample; none of this is timed;
2. `W` warm-up passes (default 3), then `P` passes (default 20) timed with `IO.monoNanosNow` around
   the whole loop over the ticks, then `P` passes timed per tick (a distribution), then `P` passes
   timed per segment (see below). Each pass starts from the same taken-over state and threads the
   state through `Copter.loop`; the outputs are discarded except the checksum, the XOR of the bit
   patterns of the four actuators over all ticks of a pass, printed so that the work cannot be
   dropped (equal for every pass, and to the oracle's on the same inputs);
3. print, as `key value` lines: the mean total, the per-tick mean and its standard deviation over
   the passes (whole-loop passes), the per-tick median, p99, max and min (per-tick passes), the
   timer overhead, the segment means, the time spent reading and parsing the input file (for
   context; not part of any tick), the checksum.

Segment passes: the tick split as `Copter.loop` is composed (`Copter/Loop.lean`), the part up to
`read_inertia` and the switch into Auto, then `update_flight_mode` (`ModeAuto.run`: mission
bookkeeping, navigator, position and attitude controllers); in between, untimed by the other two,
the navigator alone is evaluated on the same state as a side computation whose result is discarded
(`ModeAuto.mission_update` unless the mission is about to start, then
`AC_WPNav.advance_wp_target_along_track`, the `SimplePath` navigator, which ends with
`set_pos_vel_accel_NED_m`). That estimates the per-tick cost of the part of the port that the
oracle does not run (it reads the navigator's targets from the port's trace). The side computation
shares the state with the real tick, so it copies the records it updates; it is an upper estimate.

`Copter.Main` defines `main` and cannot be imported, so the input parser and the override reader
are copied from it below (`Copter.Cli.toMicros`, `parseInput?`, `applyLines`), unchanged.
-/

namespace Copter.Bench

open AP_Math Copter.Text

/-- Copy of `Copter.Cli.toMicros` (`Copter/Main.lean`). -/
def toMicros (d : Decimal) : Option Nat :=
  if d.neg then none
  else
    let e := d.e + 6
    if 0 ≤ e then some (d.m * 10 ^ e.toNat)
    else
      let q := 10 ^ e.natAbs
      some ((2 * d.m + q) / (2 * q))

/-- Copy of `Copter.Cli.parseInput?` (`Copter/Main.lean`). -/
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

/-- Copy of `Copter.Cli.applyLines` (`Copter/Main.lean`). -/
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

/-- XOR of the bit patterns of the four actuators. -/
@[inline] def actBits (a : Vector ftype 4) : UInt32 :=
  a[0].toBits ^^^ a[1].toBits ^^^ a[2].toBits ^^^ a[3].toBits

/-- `Copter.loop` up to `update_flight_mode` (the same composition, `Copter/Loop.lean`). -/
def tickPrefix (p : Parameters) (s : State) (smp : AHRS.Sample) : Option State := do
  let s := scheduler_loop s smp.dt_us
  let s := ins_update s smp
  let s := run_rate_controller_main p s
  let s := motors_output_main p s
  let s := read_AHRS s smp
  let s := read_inertia s
  if s.in_auto then pure s else enter_auto p s

/-- The navigator alone on the state `update_flight_mode` receives (side computation, see the
header); returns a few bits of its result. -/
def navSide (p : Parameters) (s : State) : UInt32 :=
  let s := if s.mode_auto.waiting_to_start then s else ModeAuto.mission_update p s
  let (wp, psc, _) := AC_WPNav.advance_wp_target_along_track p.wpnav p.psc s.wp_nav s.pos_control
    (AC_PosControl.get_dt_s s.pos_control)
  wp._track_dt_scalar.toBits ^^^ (AC_PosControl.get_vel_desired_NED_ms psc).x.toBits

/-- A pass timed around the whole loop: (ns, checksum). -/
def passTotal (p : Parameters) (s0 : State) (smps : Array AHRS.Sample) : IO (Nat × UInt32) := do
  let mut st := s0
  let mut ck : UInt32 := 0
  let t0 ← IO.monoNanosNow
  for smp in smps do
    match loop p st smp with
    | some s' =>
      st := s'
      ck := ck ^^^ actBits s'.actuators
    | none => throw (IO.userError "ModeAuto::init failed (empty mission)")
  let t1 ← IO.monoNanosNow
  return (t1 - t0, ck)

/-- A pass timed per tick: (per-tick ns, checksum). -/
def passPerTick (p : Parameters) (s0 : State) (smps : Array AHRS.Sample) : IO (Array Nat × UInt32) := do
  let mut st := s0
  let mut ck : UInt32 := 0
  let mut ts : Array Nat := Array.mkEmpty smps.size
  for smp in smps do
    let a ← IO.monoNanosNow
    match loop p st smp with
    | some s' =>
      let b ← IO.monoNanosNow
      ts := ts.push (b - a)
      st := s'
      ck := ck ^^^ actBits s'.actuators
    | none => throw (IO.userError "ModeAuto::init failed (empty mission)")
  return (ts, ck)

/-- A pass timed per segment: (sum of prefix ns, sum of navigator-side ns, sum of
`update_flight_mode` ns, checksum, navigator bits). -/
def passSegments (p : Parameters) (s0 : State) (smps : Array AHRS.Sample) :
    IO (Nat × Nat × Nat × UInt32 × UInt32) := do
  let mut st := s0
  let mut ck : UInt32 := 0
  let mut nk : UInt32 := 0
  let mut tPre := 0
  let mut tNav := 0
  let mut tMode := 0
  for smp in smps do
    let a ← IO.monoNanosNow
    match tickPrefix p st smp with
    | some s1 =>
      let b ← IO.monoNanosNow
      let x := navSide p s1
      -- the comparison makes `x` needed before the next clock read
      if x == 0x7fc00001 then IO.eprint ""
      let c ← IO.monoNanosNow
      let s2 := update_flight_mode p s1
      let ab := actBits s2.actuators
      if ab == 0x7fc00001 then IO.eprint ""
      let d ← IO.monoNanosNow
      tPre := tPre + (b - a)
      tNav := tNav + (c - b)
      tMode := tMode + (d - c)
      st := s2
      ck := ck ^^^ ab
      nk := nk ^^^ x
    | none => throw (IO.userError "ModeAuto::init failed (empty mission)")
  return (tPre, tNav, tMode, ck, nk)

/-- Mean and sample standard deviation. -/
def meanSd (xs : Array Float) : Float × Float :=
  let n := xs.size.toFloat
  let m := xs.foldl (· + ·) 0 / n
  let v := xs.foldl (fun acc x => acc + (x - m) * (x - m)) 0 / (n - 1)
  (m, if xs.size > 1 then v.sqrt else 0)

/-- Command-line options. -/
structure Options where
  inputs : Option String := none
  paramsFiles : Array String := #[]
  sets : Array String := #[]
  warmup : Nat := 3
  passes : Nat := 20

/-- Parse the command line. -/
def parseArgs : List String → Options → Except String Options
  | [], o => pure o
  | "--params" :: f :: rest, o => parseArgs rest { o with paramsFiles := o.paramsFiles.push f }
  | "--set" :: l :: rest, o => parseArgs rest { o with sets := o.sets.push l }
  | "--warmup" :: n :: rest, o => match n.toNat? with
    | some k => parseArgs rest { o with warmup := k }
    | none => throw s!"--warmup needs a number: {n}"
  | "--passes" :: n :: rest, o => match n.toNat? with
    | some k => if k == 0 then throw "--passes must be positive" else parseArgs rest { o with passes := k }
    | none => throw s!"--passes needs a number: {n}"
  | a :: rest, o =>
    if o.inputs.isNone && !a.startsWith "--" then parseArgs rest { o with inputs := some a }
    else throw s!"unknown or incomplete option {a}; usage: bench INPUTS [--params FILE]... [--set \"NAME VALUE\"]... [--warmup W] [--passes P]"

/-- Run the protocol of the header. -/
def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"bench: {e}"; return 2
  let some inputs := o.inputs | IO.eprintln "bench: no INPUTS file"; return 2
  let mut fileLines : List String := []
  for f in o.paramsFiles do
    let txt ← IO.FS.readFile f
    fileLines := fileLines ++ txt.splitOn "\n"
  let p ← match applyLines defaults (fileLines ++ o.sets.toList) with
    | .ok p => pure p
    | .error e => IO.eprintln s!"bench: {e}"; return 2
  if p.mission.isEmpty then
    IO.eprintln "bench: empty mission"; return 2
  -- parse every input line first
  let tp0 ← IO.monoNanosNow
  let txt ← IO.FS.readFile inputs
  let mut smps : Array AHRS.Sample := #[]
  let mut lineNo := 0
  for line in txt.splitOn "\n" do
    lineNo := lineNo + 1
    if (words line).isEmpty then continue
    match parseInput? line with
    | some smp => smps := smps.push smp
    | none => IO.eprintln s!"bench: {inputs}:{lineNo}: not a 17-number sample line"; return 2
  let tp1 ← IO.monoNanosNow
  let some smp0 := smps[0]? | IO.eprintln "bench: no samples"; return 2
  let s0 := takeover p (State.init p) smp0
  let n := smps.size
  let mut ck0 : Option UInt32 := none
  let mut same := true
  for _ in [0:o.warmup] do
    let (_, c) ← passTotal p s0 smps
    if ck0.isNone then ck0 := some c
    same := same && ck0 == some c
  let mut totals : Array Nat := #[]
  for _ in [0:o.passes] do
    let (t, c) ← passTotal p s0 smps
    if ck0.isNone then ck0 := some c
    same := same && ck0 == some c
    totals := totals.push t
  let mut all : Array Nat := Array.mkEmpty (n * o.passes)
  let mut timedMeans : Array Float := #[]
  for _ in [0:o.passes] do
    let (ts, c) ← passPerTick p s0 smps
    same := same && ck0 == some c
    all := all ++ ts
    timedMeans := timedMeans.push ((ts.foldl (· + ·) 0).toFloat / n.toFloat)
  let mut pre : Array Float := #[]
  let mut nav : Array Float := #[]
  let mut mode : Array Float := #[]
  let mut nk0 : Option UInt32 := none
  for _ in [0:o.passes] do
    let (a, b, c, k, nk) ← passSegments p s0 smps
    same := same && ck0 == some k
    if nk0.isNone then nk0 := some nk
    same := same && nk0 == some nk
    pre := pre.push (a.toFloat / n.toFloat)
    nav := nav.push (b.toFloat / n.toFloat)
    mode := mode.push (c.toFloat / n.toFloat)
  -- timer overhead: two consecutive reads
  let mut ovh : Array Nat := Array.mkEmpty 100000
  for _ in [0:100000] do
    let a ← IO.monoNanosNow
    let b ← IO.monoNanosNow
    ovh := ovh.push (b - a)
  let ovhS := ovh.qsort (· < ·)
  let allS := all.qsort (· < ·)
  let pct := fun (q : Float) => allS[min (allS.size - 1) (q * (allS.size - 1).toFloat).floor.toUInt64.toNat]!
  let (m, sd) := meanSd (totals.map fun t => t.toFloat / n.toFloat)
  let (tm, tsd) := meanSd timedMeans
  let (pm, psd) := meanSd pre
  let (nm, nsd) := meanSd nav
  let (mm, msd) := meanSd mode
  let hex := fun (u : UInt32) => String.ofList ((Nat.toDigits 16 u.toNat).leftpad 8 '0')
  IO.println "program lean-port"
  IO.println s!"ticks {n}"
  IO.println s!"warmup {o.warmup}"
  IO.println s!"passes {o.passes}"
  IO.println s!"total_ns_mean {(totals.foldl (· + ·) 0).toFloat / o.passes.toFloat}"
  IO.println s!"per_tick_mean_ns {m}"
  IO.println s!"per_tick_sd_over_passes_ns {sd}"
  let pms := (totals.map fun t => t.toFloat / n.toFloat).qsort (· < ·)
  IO.println s!"per_tick_mean_pass_median_ns {pms[pms.size / 2]!}"
  IO.println s!"per_tick_mean_pass_min_ns {pms[0]!}"
  IO.println s!"timed_per_tick_mean_ns {tm}"
  IO.println s!"timed_per_tick_sd_over_passes_ns {tsd}"
  IO.println s!"per_tick_median_ns {pct 0.5}"
  IO.println s!"per_tick_p99_ns {pct 0.99}"
  IO.println s!"per_tick_max_ns {allS.back!}"
  IO.println s!"per_tick_min_ns {allS[0]!}"
  IO.println s!"timer_overhead_median_ns {ovhS[ovhS.size / 2]!}"
  IO.println s!"segment_prefix_mean_ns {pm}"
  IO.println s!"segment_prefix_sd_ns {psd}"
  IO.println s!"segment_navigator_side_mean_ns {nm}"
  IO.println s!"segment_navigator_side_sd_ns {nsd}"
  IO.println s!"segment_flight_mode_mean_ns {mm}"
  IO.println s!"segment_flight_mode_sd_ns {msd}"
  IO.println s!"parse_ns {tp1 - tp0}"
  IO.println s!"checksum {hex (ck0.getD 0)}"
  IO.println s!"checksum_same_every_pass {same}"
  return (if same then 0 else 1)

end Copter.Bench

/-- Entry point; see the module docstring. -/
def main (args : List String) : IO UInt32 := Copter.Bench.main args
