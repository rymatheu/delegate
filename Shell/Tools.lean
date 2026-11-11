import Shell.Link
import Shell.Text

/-!
# Shell.Tools (test drivers of the MAVLink layer: IO only)

- `codecLoop` (`leanfc --codec`): the codec test driver of `sim/mavlink/test_codec.py`, hex lines
  on standard input: `P hex` feeds the bytes to a fresh parser, `S hex` to the persistent one, and
  prints each frame found as `F version seq sysid compid msgid words...` then
  `END rejected signed`; `E msgid seq sysid compid words...` encodes and prints `H hex`
  (MAVLink 2).
- `bench` (`leanfc --bench`): parser throughput and the cost of `Gcs.step` per tick at
  QGroundControl's stream rates, against the real vehicle layer on the ground.
- `selftest` (`leanfc --selftest`): the certified angles against binary64 `atan2`/`asin`, the
  geodesy round trip and the mission ↔ waypoint-list round trip.

`Setup` is the services' and the vehicle's start configuration shared with `Main.lean`.
-/

open Mavlink

def ofHex (s : String) : ByteArray :=
  let v (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  let cs := s.toList.filter (!·.isWhitespace)
  let rec go : List Char → Array UInt8 → Array UInt8
    | a :: b :: rest, acc => go rest (acc.push (v a * 16 + v b).toUInt8)
    | _, acc => acc
  ByteArray.mk (go cs #[])

/-! ## Codec test driver -/

def frameLine (f : Frame) : String :=
  let ver := match f.version with | .v1 => 1 | .v2 => 2
  let words := match f.msg? with
    | some m => " ".intercalate (m.toWords.toList.map toString)
    | none => "?"
  s!"F {ver} {f.seq} {f.sysid} {f.compid} {f.msgid} {words}"

partial def codecLoop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (persistent : ParserState) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let toks := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match toks with
  | ["P", hex] =>
    let (s, fs) := Parser.feedBytes {} (ofHex hex)
    for f in fs do stdout.putStrLn (frameLine f)
    stdout.putStrLn s!"END {s.stats.rejected} {s.stats.signed}"
    stdout.flush
    codecLoop stdin stdout persistent
  | ["S", hex] =>
    let (s, fs) := Parser.feedBytes persistent (ofHex hex)
    for f in fs do stdout.putStrLn (frameLine f)
    stdout.putStrLn s!"END {s.stats.rejected} {s.stats.signed}"
    stdout.flush
    codecLoop stdin stdout s
  | "E" :: msgid :: seq :: sys :: comp :: words =>
    let ws := (words.filterMap String.toInt?).toArray
    match Msg.ofWords msgid.toNat!.toUInt32 ws with
    | some m =>
      let f := Frame.ofMsg seq.toNat!.toUInt8 sys.toNat!.toUInt8 comp.toNat!.toUInt8 m
      stdout.putStrLn s!"H {toHex f.serialize}"
    | none => stdout.putStrLn "H ?"
    stdout.flush
    codecLoop stdin stdout persistent
  | _ =>
    stdout.putStrLn "?"
    stdout.flush
    codecLoop stdin stdout persistent

/-! ## Setup -/

/-- The default origin when neither the parameter files (`ORIGIN`) nor `--origin` give one:
Pikes Peak summit, Colorado (38.8405° N, 105.0442° W, 4302 m AMSL). -/
def defaultOrigin : Int × Int × Int := (388405000, -1050442000, 4302000)

/-- The services' state and configuration and the vehicle on the ground, from the parameter files. -/
structure Setup where
  store : ParamTable.Store
  cfg : GcsConfig
  origin : Origin

def setup (args : List String) : IO (Except String Setup) := do
  let files := argAll args "--params"
  if files.isEmpty then return .error "--params FILE is required (see params/*.params)"
  let mut texts : List (String × String) := []
  for f in files do
    try texts := texts ++ [(f, ← IO.FS.readFile f)]
    catch e => return .error s!"{f}: cannot read: {e}"
  match ParamTable.Store.load texts with
  | .error e => return .error s!"parameter file: {e}"
  | .ok store =>
    let (lat, lon, alt) ← match argsAfter args "--origin" 3 with
      | some [a, b, c] =>
        match Decimal.parseScaled a 7, Decimal.parseScaled b 7, Decimal.parseScaled c 3 with
        | some a, some b, some c => pure (a, b, c)
        | _, _, _ => return .error "--origin LAT LON ALT: three decimal numbers (at most 7, 7 and 3 decimals)"
      | _ => pure (store.origin.getD defaultOrigin)
    let sysidParam := match ParamTable.Store.indexOf "MAV_SYSID" with
      | some i => match store.get i with | some (_, _, v) => (Format.roundR v).toNat | none => 1
      | none => 1
    let sysid := (argOne args "--sysid" |>.bind String.toNat?).getD sysidParam
    return .ok { store, cfg := { sysid := sysid.toUInt8 }, origin := makeOrigin lat lon alt }

/-- The services at start: the stored mission is the parameter file's waypoints (home = `home`). -/
def Setup.gcs (su : Setup) (home : Vec3) : GcsState :=
  let cmds := Mission.ofWaypoints su.store.params.waypoints
  Gcs.init su.store (cmds.map (Mission.storedOf su.origin home))

/-- Sensor readings of a vehicle at rest, level, nose north, at `p` (bench input). -/
def restSensors (p : Vec3) : Sensors :=
  { gyro := Vec3.zero, accel := ⟨0, 0, -gravity⟩, heading := some (1, 0), position := some p,
    velocity := some Vec3.zero }

/-! ## Bench -/

def bench (args : List String) : IO UInt32 := do
  let .ok su ← setup args | IO.eprintln "setup failed"; return 2
  let P := su.store.params
  let mission := Mission.ofWaypoints P.waypoints
  let rest := restSensors ⟨P.start.x, P.start.y, 0⟩
  let v0 := (List.range 1200).foldl (fun v _ => (Copter.step v #[] none rest).1) (Copter.initGround P mission)
  let gcs0 := su.gcs v0.home
  -- parser throughput: a stream of telemetry frames
  let t := Copter.telemetry v0 su.origin
  let msgs := Out.all.map (Gcs.telemetryMsg su.cfg gcs0 t)
  let one := msgs.foldl (fun b m => b ++ (Frame.ofMsg 0 1 1 m).serialize) ByteArray.empty
  let reps := 200
  let stream := (List.range reps).foldl (fun b _ => b ++ one) ByteArray.empty
  let t0 ← IO.monoNanosNow
  let (_, fs) := Parser.feedBytes {} stream
  let t1 ← IO.monoNanosNow
  let dt := (t1 - t0).toFloat / 1e9
  IO.println s!"parser: {fs.size} frames, {stream.size} bytes in {dt} s: {fs.size.toFloat / dt} frames/s, {stream.size.toFloat / dt / 1e6} MB/s"
  -- Gcs.step per tick with QGroundControl's ArduPilot stream rates
  let reqs : List (Nat × Nat) := [(1, 2), (2, 2), (3, 2), (6, 3), (10, 10), (11, 10), (12, 3)]
  let mut g := gcs0
  let mut v := v0
  for (id, hz) in reqs do
    let rds : RequestDataStream :=
      { target_system := 1, target_component := 1, req_stream_id := id.toUInt8,
        req_message_rate := hz.toUInt16, start_stop := 1 }
    let inc : Incoming := { sysid := 255, compid := 190, msg := .requestDataStream rds }
    let (g', _, cmds) := Gcs.step su.cfg g (Copter.telemetry v su.origin) (some inc)
    g := g'; v := (Copter.step v cmds g'.gcsSeen rest).1
  let n := 4000
  let mut sent := 0
  let mut total := 0
  let mut worst := 0
  for _ in [0:n] do
    let t := Copter.telemetry v su.origin
    let t0 ← IO.monoNanosNow
    let (g', out, cmds) := Gcs.step su.cfg g t none
    sent := sent + out.size
    let t1 ← IO.monoNanosNow
    total := total + (t1 - t0); worst := max worst (t1 - t0)
    g := g'; v := (Copter.step v cmds g'.gcsSeen rest).1
  IO.println s!"Gcs.step: {n} ticks (10 s at 400 Hz), {sent} messages, mean {total.toFloat / n.toFloat / 1000} us, worst {worst.toFloat / 1000} us per tick (QGC's ArduPilot stream rates)"
  -- the vehicle layer with the controller, on the ground
  let t0 ← IO.monoNanosNow
  let v1 := (List.range n).foldl (fun v _ => (Copter.step v #[] none rest).1) v
  let t1 ← IO.monoNanosNow
  IO.println s!"Copter.step (vehicle layer + EKF + controller, on the ground): mean {(t1 - t0).toFloat / n.toFloat / 1000} us per tick ({v1.tick})"
  -- the costliest part: one ATTITUDE (three certified angle enclosures)
  let t0 ← IO.monoNanosNow
  let mut k := 0
  for i in [0:200] do
    let q := Copter.levelQuat (Format.ofRat ((i : ℚ) / 200 - 1/2), Format.ofRat (1 - ((i : ℚ) / 400)))
    let (r, _, _) := Format.euler q
    if r == 0 then k := k + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"Format.euler: {(t1 - t0).toFloat / 200 / 1000} us per quaternion ({k})"
  return 0

/-! ## Self test of the formatter and the mission conversion -/

/-- `--selftest`: certified angles against `Float.atan2`/`Float.asin` (the bound of `Format`), the
enclosure width test, the geodesy round trip and the mission ↔ waypoint round trip. -/
def selftest (args : List String) : IO UInt32 := do
  let .ok su ← setup args | IO.eprintln "setup failed"; return 2
  let mut ok := true
  -- quaternions from a deterministic sweep of roll, pitch, yaw (Float only to build the inputs)
  let mut worst : Float := 0
  let mut allWidth := true
  let mut n := 0
  for i in [0:9] do
    for j in [0:9] do
      for k in [0:9] do
        let r := (i.toFloat - 4) * 0.78
        let p := (j.toFloat - 4) * 0.39
        let y := (k.toFloat - 4) * 0.785
        let (cr, sr, cp, sp, cy, sy) := (Float.cos (r/2), Float.sin (r/2), Float.cos (p/2), Float.sin (p/2), Float.cos (y/2), Float.sin (y/2))
        let q : Quat := ⟨R.ofFloat (cr*cp*cy + sr*sp*sy), R.ofFloat (sr*cp*cy - cr*sp*sy),
                         R.ofFloat (cr*sp*cy + sr*cp*sy), R.ofFloat (cr*cp*sy - sr*sp*cy)⟩
        let (er, ep, ey) := Format.euler q
        -- reference: the same formulas in binary64 from the binary32 components
        let (w, x, yy, z) := (R.toFloat q.w, R.toFloat q.x, R.toFloat q.y, R.toFloat q.z)
        let rr := Float.atan2 (2*(w*x + yy*z)) (1 - 2*(x*x + yy*yy))
        let rp := Float.asin (max (-1) (min 1 (2*(w*yy - x*z))))
        let ry := Float.atan2 (2*(w*z + x*yy)) (1 - 2*(yy*yy + z*z))
        let d := max (Float.abs (R.toFloat er - rr)) (max (Float.abs (R.toFloat ep - rp)) (Float.abs (R.toFloat ey - ry)))
        worst := max worst d
        allWidth := allWidth && Format.widthOk q
        n := n + 1
  let okAng := worst < 3e-7 && allWidth
  ok := ok && okAng
  IO.println s!"{if okAng then "PASS" else "FAIL"}  angles: {n} quaternions, every enclosure narrower than 2^-30: {allWidth}, largest difference from binary64 atan2/asin {worst * 1e9} nrad (bound 2^-31 + 2^-23 rad = 120 nrad, plus the reference's own rounding)"
  -- geodesy round trip: NED → lat/lon → NED within the rounding of 1e-7 degree (1.1 cm)
  let o := su.origin
  let home : Vec3 := ⟨su.store.params.start.x, su.store.params.start.y, 0⟩
  let mut geoWorst : Float := 0
  for i in [0:41] do
    let p : Vec3 := ⟨R.ofFloat ((i.toFloat - 20) * 37.3), R.ofFloat ((i.toFloat - 20) * -51.1), 0⟩
    let (lat, lon) := Format.toLatLon o p
    let (nn, ee) := Format.toNE o lat lon
    geoWorst := max geoWorst (max (Float.abs (R.toFloat nn - R.toFloat p.x)) (Float.abs (R.toFloat ee - R.toFloat p.y)))
  let okGeo := geoWorst < 0.012
  ok := ok && okGeo
  IO.println s!"{if okGeo then "PASS" else "FAIL"}  geodesy: NED -> lat/lon -> NED over +-1 km, largest difference {geoWorst} m (1e-7 deg rounding: 0.011 m)"
  -- mission: the file's waypoints → stored items → local commands → waypoint list
  let wps := su.store.params.waypoints
  let cmds := Mission.ofWaypoints wps
  let items := cmds.map (Mission.storedOf o home)
  let back := items.filterMap fun it => match Mission.toCmd o home it with | .ok c => some c | .error _ => none
  let legs := Mission.toWaypoints home home back
  let mut misWorst : Float := 0
  let mut kinds := true
  for (l, w) in legs.zip wps do
    misWorst := max misWorst (Float.abs (R.toFloat l.pos.x - R.toFloat w.pos.x) + Float.abs (R.toFloat l.pos.y - R.toFloat w.pos.y)
      + Float.abs (R.toFloat l.pos.z - R.toFloat w.pos.z))
    kinds := kinds && l.kind == w.kind
  let okMis := legs.size == wps.size && misWorst < 0.03 && kinds
  ok := ok && okMis
  IO.println s!"{if okMis then "PASS" else "FAIL"}  mission: {wps.size} file waypoints -> MISSION_ITEM_INT -> local -> waypoint list, largest difference {misWorst} m, leg kinds kept: {kinds}"
  return if ok then 0 else 1

