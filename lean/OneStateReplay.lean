import VehicleHarnessData
import EstimatorProbe

/-!
`onestate_replay FRAMES ANSWERS STORAGE OUT SNAPSHOT < COMMANDS` (README.md "Phase 5: the estimator bridge"): the replay of
a recorded session over ONE state, the memory of the vehicle translation (`Vehicle_lib`, on `ParamMemoryV`) with the
estimator World inside it. A harness, not a translation: it sequences translated calls and feeds the boundary.

* `B`: the GCS boot of lean/GCSReplay.lean on Vehicle_lib's image (static construction, AP_Param's format check and
  `load_all`, GCS init, the run-time parameter objects). AP_Param writes the estimator's parameters straight into the
  World (their addresses are bridged fields): no copying of parameters, no probe `# params`.
* the estimator commands of lean/EstimationReplay.lean (ardupilot/estimation_replay.py), each made through the
  vehicle's bridge adapters (`VehicleBridge`) where the vehicle makes that call (`ahrs.update(true)`, `ins.update()`,
  ...), on `(← get).w`; the World boundary inputs that are not vehicle state yet (the GPS's serial port, the stored IMU
  ids, the input records, the scheduler stand-in's lines) set as there; the armed flag in the memory state (`Mem.armed`,
  read by every adapter); AP_Vehicle's time flying from the translated `AP_Vehicle::get_time_flying_ms`, its
  `likely_flying` driven through the translated `set_likely_flying` from the trace's `flying=`.
* `G ...`: one step of the GCS byte replay (lean/GCSReplay.lean): uplink, IO process, delay callbacks, tasks 28/29.
  The reference's parameter snapshots (`CPP2LEAN_PARAM_SNAPSHOT`) are applied only to parameters whose home is the
  memory; a parameter whose address is a bridged field (the estimator's) is never set from a snapshot.
* `E k t`: the probe's estimator keys from the World (stdout), as EstimationReplay.
-/

open Vehicle_lib VehicleHarnessData EstimatorProbe
open FloatLib.Floats (Binary32 Binary64)

namespace OneStateReplay

def ahrsA : UInt64 := VehicleHarnessData.obj'ahrs
/-- `copter.scheduler` (clang's offset in Copter) -/
def schedA : UInt64 := addr'copter + 208

/-- The answers GCS.json's boundary gave and slice 2 translates (`AP_Scheduler::time_available_usec`: the old
`timeAvail` 0xffff, as `_task_time_allowed` from the current time; `GCS_MAVLINK_Copter::params_ready`:
`copter.ap.initialised_params`, set by init_ardupilot before any request of the sessions) -/
def vehicleAnswers : PMem.M Unit := do
  PMem.stU32 (schedA + 112) 0xffff
  PMem.stU32 (schedA + 116) (← PMem.clock).toUInt32
  PMem.stB ((addr'copter + 9448) + 22) true
def insA : UInt64 := VehicleHarnessData.obj'ins
def gpsA : UInt64 := VehicleHarnessData.obj'gps
def baroA : UInt64 := VehicleHarnessData.obj'barometer
def compassA : UInt64 := VehicleHarnessData.obj'compass

def staticInit : PMem.M Unit := do
  StorageAccess.StorageAccess addr'AP_Param___storage 0
  for (c, v) in ctorPointers do
    PMem.stU64 c v
  for (o, t) in ctorDefaults do
    AP_Param.setup_object_defaults o t
  StorageAccess.StorageAccess addr'AP_Mission___storage 3
  let zf ← PMem.alloc 48
  AP_Mission.AP_Mission missionObj zf (zf + 16) (zf + 32)
  for (o, a, b, c) in ctorCommandModels do
    AC_CommandModel.AC_CommandModel o (Binary32.ofBits a) (Binary32.ofBits b) (Binary32.ofBits c)
  SRV_Channels.SRV_Channels servoChannels
  AP_Param.AP_Param paramLoader addr'Copter__var_info
  PMem.stU64 addr'GCS___singleton gcsObj
  ObjectBuffer'GCS_MAVLINK_pending_param_request.ObjectBuffer addr'GCS_MAVLINK__param_requests 20
  ObjectBuffer'GCS_MAVLINK_pending_param_reply.ObjectBuffer addr'GCS_MAVLINK__param_replies 5
  -- (Phase 5b) AP_Param's save queue (`ObjectBuffer_TS<param_save> AP_Param::save_queue{30}`, AP_Param.cpp): the
  -- vehicle's and the World's saves are queued there and written by `save_io_handler` (the IO process below)
  ObjectBuffer_TS'AP_Param_param_save.ObjectBuffer_TS addr'AP_Param__save_queue 30
  staticDynamicInit
  -- (slice 2: these are translated now, no longer GCS.json boundary answers) the vehicle state they read, which this
  -- replay does not construct: AP_Scheduler's singleton (`AP::scheduler()`), its loop period (2500 us)
  PMem.stU64 addr'AP_Scheduler___singleton schedA
  PMem.stU16 (schedA + 64) 2500

def formatCheckAndLoad : PMem.M Bool := do
  let fp ← PMem.enter 16
  let ok ← AP_Param.load formatVersion
  let v ← PMem.ldI16 formatVersion
  if !ok || v != formatVersionExpected then
    StorageManager.erase
    AP_Param.erase_all
    PMem.stI16 fp formatVersionExpected
    AP_ParamTBase'short_2.set_and_save formatVersion fp
  PMem.stI16 (fp + 8) formatVersionExpected
  AP_ParamTBase'short_2.set_default formatVersion (fp + 8)
  let r ← AP_Param.load_all
  PMem.leave fp
  return r

def boot : PMem.M Bool := do
  AP_Param.setup_sketch_defaults
  AP_Param.check_var_info
  let r ← formatCheckAndLoad
  AP_Param.set_frame_type_flags 1
  AP_Mission.init missionObj
  GCS.init gcsObj
  GCS.setup_console gcsObj
  GCS.setup_uarts gcsObj
  let (cell, size, tab, vcell, mon, st, prm) := battBackend
  let a ← PMem.alloc size
  PMem.stU64 cell a
  PMem.stU64 vcell tab
  AP_BattMonitor_Analog.AP_BattMonitor_Analog a mon st prm
  AP_Param.load_object_from_eeprom a tab
  let view ← PMem.alloc 1024
  let mut addrs : Array UInt64 := #[]
  for k in [0:runtimeObjects.size] do
    let (cell, size, tab, vcell, groups) := runtimeObjects[k]!
    let a ← PMem.alloc size
    addrs := addrs.push a
    PMem.stU64 cell a
    if vcell != 0 then PMem.stU64 vcell tab
    match k with
    | 1 => AC_AttitudeControl_Multi.AC_AttitudeControl_Multi a view addrs[0]!
    | 2 => AC_PosControl.AC_PosControl a view addrs[0]! addrs[1]!
    | 3 => AC_WPNav.AC_WPNav a view addrs[2]! addrs[1]!
    | 4 => AC_Loiter.AC_Loiter a view addrs[2]! addrs[1]!
    | 5 => AC_Circle.AC_Circle a view addrs[2]!
    | _ =>
      for (off, t) in groups do
        AP_Param.setup_object_defaults (a + off) t
    AP_Param.load_object_from_eeprom a tab
  return r

def hexBytes (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for k in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (digit cs[2 * k]! * 16 + digit cs[2 * k + 1]!))
  return out

def toHex (b : ByteArray) : String := Id.run do
  let d := "0123456789abcdef".toList.toArray
  let mut s := ""
  for x in b.toList do
    s := s.push d[(x / 16).toNat]! |>.push d[(x % 16).toNat]!
  return s

/-- The parameters non-GCS code changed (GCSReplay.applySnap), but only those whose home is the memory: a parameter
whose address is a bridged field lives in the World and is never set from a snapshot (its differing names are
returned separately). -/
def applySnap (snap : Array String) (step : Nat) : PMem.M (Array String × Array String) := do
  let mut applied : Array String := #[]
  let mut bridged : Array String := #[]
  for l in snap do
    match l.splitOn " " with
    | ["paramsnap", st, nm, _, bits] =>
      if st.toNat! == step then
        let a ← PMem.alloc 32
        for i in [0:nm.length] do
          PMem.stU8 (a + i.toUInt64) (nm.toList[i]!).toNat.toUInt8
        let tp ← PMem.alloc 8
        let vp ← AP_Param.find a tp 0
        if vp != 0 then
          let t ← PMem.ldU32 tp
          let cur ← AP_Param.cast_to_float vp t
          let wbits : UInt32 := (hexBytes bits).toList.foldl (fun acc b => acc * 256 + b.toUInt32) 0
          if Binary32.toBits cur != wbits then
            if (PMem.Bridge.find vp).isSome then
              bridged := bridged.push s!"{nm}:{st}"
            else
              AP_Param.set_float vp (Binary32.ofBits wbits) t
              applied := applied.push nm
    | _ => pure ()
  return (applied, bridged)

def ioProcess (c : UInt64) : PMem.M Unit := do
  -- (Phase 5b) the IO processes in the reference's order of registration: AP_Param::save_io_handler (registered by
  -- AP_Param::setup at boot), then GCS_MAVLINK::param_io_timer (once a channel registered it)
  AP_Param.save_io_handler 0
  if (← PMem.ldU8 addr'GCS_MAVLINK__param_timer_registered) != 0 then
    GCS_MAVLINK.param_io_timer c

def withW (f : Estimator_lib.World → Estimator_lib.World) : PMem.M Unit := do
  let w ← modifyGet fun m => (m.w, { m with w := Estimator_lib.World.init })
  modify fun m => { m with w := f w }

/-- Copter::set_home_to_current_location(_inflight) and set_home (ArduCopter/commands.cpp:22-78) as EstimationReplay
makes them, through the bridge: `get_location`, `get_origin` into Location temporaries of the memory (clang's layout:
the frame bits at byte 0, alt at 4), `set_home`, `lock_home`. -/
def setHomeToCurrent (lock inflight : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let lok ← VehicleBridge.AP_AHRS.get_location'1 ahrsA fp
  let ook ← VehicleBridge.AP_AHRS.get_origin'1 ahrsA (fp + 16)
  if lok && !(inflight && !ook) && ook then
    if inflight then
      -- Location::copy_alt_from: alt and the frame flags (relative_alt bit 0, terrain_alt bit 2, origin_alt bit 3)
      PMem.stI32 (fp + 4) (← PMem.ldI32 (fp + 20))
      for b in [0, 2, 3] do
        PMem.stBits fp b 1 (← PMem.ldBits (fp + 16) b 1)
    let ok ← VehicleBridge.AP_AHRS.set_home'1 ahrsA fp
    if ok && lock then VehicleBridge.AP_AHRS.lock_home'0 ahrsA
  PMem.leave fp

def nat (s : String) : Nat := s.toNat?.getD 0

/-- One estimator command (EstimationReplay.run1's), on the one state. -/
def est (t : Array String) : PMem.M (Option String) := do
  match t[0]! with
  | "F" => withW fun w => { w with est_scheduler := (Estimator_lib.EstScheduler.feed w.est_scheduler (record t)).1 }
  | "S" =>
    let k := nat t[1]!
    withW fun w => Id.run do
      let mut w := w
      for _ in [0:k] do
        if w.est_scheduler._lines.toNat ≥ k || w.est_scheduler._exhausted then break
        -- (Phase 5c) the scheduler's lock-step points (`est_mark` events) are not used here
        let (s, w', _) := Estimator_lib.EstScheduler.delay_microseconds w.est_scheduler w #[] 1
        w := { w' with est_scheduler := s }
      return w
  | "A" => modify fun m => { m with armed := t[1]! == "1" }
  | "BI" => VehicleBridge.AP_Baro.init'0 baroA
  | "AV" =>
    -- Copter::allocate_motors's `ahrs.create_view(ROTATION_NONE)` (allocate_motors is a stub in Vehicle_lib)
    withW fun w => let (s, w', _) := Estimator_lib.AP_AHRS.create_view w.ahrs w Estimator_lib.Rotation.ROTATION_NONE; { w' with ahrs := s }
  | "CI" => VehicleBridge.Compass.init'0 compassA
  | "BC" => VehicleBridge.AP_Baro.calibrate'1 baroA true
  | "BU" =>
    -- the barometer reads the step's own armed flag (task 16): the HAL flag for this call
    let a0 := (← get).armed
    modify fun m => { m with armed := t[1]! == "1" }
    VehicleBridge.AP_Baro.update'0 baroA
    modify fun m => { m with armed := a0 }
  | "GI" =>
    withW fun w => { w with gps'inp := { w.gps'inp with params_0_type_configured := true, find_serial_found_SerialProtocol_GPS_at1 := #[true, true] } }
    -- AP_GPS::init with its `convert_parameters` on the memory (the adapter's pre_convert_parameters action, as the
    -- vehicle's call site passes it)
    VehicleBridge.AP_GPS.init'0 gpsA (AP_GPS.convert_parameters gpsA)
  | "AI" =>
    VehicleBridge.AP_AHRS.init'0 ahrsA
    VehicleBridge.AP_AHRS.set_vehicle_class'1 ahrsA 2
  | "II" =>
    withW fun w => { w with ins'inp := { w.ins'inp with gyro_id__gyro_count_loaded := t[2]! == "1", accel_id__accel_count_loaded := t[3]! == "1", was_watchdog_reset := false } }
    VehicleBridge.AP_InertialSensor.init'1 insA (UInt16.ofNat (nat t[1]!))
  | "AR" => VehicleBridge.AP_AHRS.reset'0 ahrsA
  | "WS" => VehicleBridge.AP_InertialSensor.wait_for_sample'0 insA
  | "IU" => VehicleBridge.AP_InertialSensor.update'0 insA
  | "GU" => VehicleBridge.AP_GPS.update'0 gpsA
  | "CT" => VehicleBridge.Compass.set_throttle'1 compassA (f32 t[1]!)
  | "CV" => VehicleBridge.Compass.set_voltage'1 compassA (f32 t[1]!)
  | "CR" => discard <| VehicleBridge.Compass.read'0 compassA
  | "AU" =>
    -- AP_Vehicle's likely_flying from the trace (the vehicle's decision, slice 2) through the translated setter, the
    -- HAL clock at the World's (the scheduler stand-in's) time; then `ahrs.update(true)` with the translated
    -- AP_Vehicle::get_time_flying_ms as its time-flying input
    let flying := t[1]! == "1"
    let last := (nat t[2]!).toUInt64
    let lf ← PMem.ldB (addr'copter + 6761)
    if flying && !lf then
      modify fun m => { m with clockUs := last * 1000 }
      AP_Vehicle.set_likely_flying addr'copter true
    else if !flying && lf then
      AP_Vehicle.set_likely_flying addr'copter false
    let ms := Estimator_lib.millis (← get).w
    modify fun m => { m with clockUs := ms.toUInt64 * 1000 }
    VehicleBridge.AP_AHRS.update'1 ahrsA true (AP_Vehicle.get_time_flying_ms addr'copter)
  | "HE" =>
    if !(← VehicleBridge.AP_AHRS.home_is_set'0 ahrsA) then
      setHomeToCurrent false (t[1]! == "1")
  | "HA" =>
    if !(← VehicleBridge.AP_AHRS.home_is_set'0 ahrsA) then
      VehicleBridge.AP_AHRS.resetHeightDatum'0 ahrsA
    else if !(← VehicleBridge.AP_AHRS.home_is_locked'0 ahrsA) then
      setHomeToCurrent false false
  | "TH" => VehicleBridge.AP_AHRS.set_terrain_hgt_stable'1 ahrsA (t[1]! == "1")
  | "E" =>
    let w := (← get).w
    return some (t[1]! ++ " t=" ++ t[2]! ++ " " ++ toString w.est_scheduler._lines.toNat ++ ahrsKeys w ++ ekfKeys w ++ frontEnds w ++ vehicleKeys w)
  | _ => pure ()
  return none

/-- The vehicle translation's HAL hook (`PMem.hal`, README.md "Phase 5: the whole-vehicle replay"): this replay drives
the estimator and the GCS by commands, not the vehicle's HAL; a HAL call answers 0 (as `PMem.halCall` did). -/
@[export cpp2lean_vehicle_hal]
def halImplDef (name : String) (this : UInt64) (args : Array UInt64) (s : PMem.Mem) : UInt64 × PMem.Mem :=
  -- (Phase 5c) the World's lock-step points and the World retry (`cpp2lean::*`, VehicleReplay's) are not used here: the
  -- World is fed ahead by the commands
  if name.startsWith "cpp2lean::" then (0, s) else
  (0, { s with log := s.log.push ("hal " ++ name) })

end OneStateReplay

open OneStateReplay in
def main (args : List String) : IO UInt32 := do
  match args with
  | [framesP, answersP, stP, outP, snapP] =>
    let st ← IO.FS.readBinFile stP
    let frameLines ← IO.FS.lines framesP
    let answerLines ← IO.FS.lines answersP
    let mut frames : Array (UInt32 × Array ByteArray) := #[]
    for l in frameLines do
      match l.splitOn " " with
      | [i, h] =>
        let id := i.toNat!.toUInt32
        match frames.findIdx? (·.1 == id) with
        | some j => frames := frames.modify j fun (a, fs) => (a, fs.push (hexBytes h))
        | none => frames := frames.push (id, #[hexBytes h])
      | _ => pure ()
    let mut answers : Array (String × Array UInt64) := #[]
    for l in answerLines do
      match l.splitOn " " with
      | [k, v] =>
        match answers.findIdx? (·.1 == k) with
        | some j => answers := answers.modify j fun (a, vs) => (a, vs.push v.toNat!.toUInt64)
        | none => answers := answers.push (k, #[v.toNat!.toUInt64])
      | _ => pure ()
    let blank := ByteArray.mk (Array.replicate st.size 0)
    let ((), m0) := staticInit.run (initMem blank)
    let mut m : PMem.Mem := { m0 with st := st, frames := frames, framePos := frames.map (fun _ => 0), answers := answers,
                                       answerPos := answers.map (fun _ => 0) }
    let snap ← IO.FS.lines snapP
    let snapSteps := (snap.filterMap fun l => match l.splitOn " " with
      | ["paramsnap", st, _, _, _] => some st.toNat! | _ => none).toList.eraseDups
    let h ← IO.FS.Handle.mk outP .write
    let out ← IO.getStdout
    let hin ← IO.getStdin
    let mut chan0 : UInt64 := 0
    let mut applied : Array String := #[]
    let mut bridged : Array String := #[]
    let mut tGcs : Nat := 0
    let mut tEst : Nat := 0
    let mut tStep : Array Nat := #[]
    let mut cur : Nat := 0
    let mut nsteps : Nat := 0
    repeat
      let line ← hin.getLine
      if line.isEmpty then break
      let t := (((line.trimAscii.toString).splitOn " ").filter (· ≠ "")).toArray
      if t.size == 0 then continue
      if t[0]! == "B" then
        let t0 ← IO.monoNanosNow
        let (ok, m1) := (do vehicleAnswers; boot : PMem.M Bool).run m
        m := m1
        chan0 := ((PMem.ldU64 (gcsObj + offChan)).run m).1
        m := { m with seqAddr := chan0 + offTxSeq, chan0 := chan0 }
        let ((a0, b0), m2) := (applySnap snap (snapSteps.head?.getD 0)).run m
        m := m2
        applied := applied ++ a0
        bridged := bridged ++ b0
        let bootTx := m.tx
        m := { m with tx := ByteArray.empty }
        let t1 ← IO.monoNanosNow
        h.putStrLn s!"# boot load_all={ok} channel=0x{(Nat.toDigits 16 chan0.toNat).asString} tx={toHex bootTx} marks={m.delayMarks.toList} ms={(t1 - t0).toFloat / 1e6}"
      else if t[0]! == "G" then
        match t.toList.drop 1 with
        | [k, tt, dcb, r28, s29, tq, up, _, pre, post] =>
          m := { m with clockUs := tt.toNat!.toUInt64, rx := m.rx.extract m.rxPos m.rx.size ++ hexBytes (if up == "-" then "" else up),
                        rxPos := 0, textQuota := tq.toNat!, bfAt := #[], inDelayCb := dcb.toNat! > 0, curStep := k.toNat! }
          let a ← IO.monoNanosNow
          let stepBody : PMem.M (Array String × Array String) := do
            vehicleAnswers
            for _ in [0:pre.toNat!] do PMem.bframe 0 (0x1000000 : UInt32)
            let mut ap : Array String := #[]
            let mut br : Array String := #[]
            for st in snapSteps.drop 1 do
              if st + 1 == k.toNat! then
                let (x, y) ← applySnap snap st
                ap := ap ++ x
                br := br ++ y
            ioProcess chan0
            -- (Phase 5b) the World's output events of the line's estimator commands (AP_Param saves and notifications,
            -- GCS_SEND_MESSAGE, the mission's home record), replayed on the memory as the vehicle's call sites do after
            -- each bridge call: after the IO processes of the line's start (a save is written by the next IO process)
            worldOutputs'drain
            for _ in [0:dcb.toNat!] do
              AP_Vehicle.scheduler_delay_callback
            if r28 == "1" then GCS.update_receive gcsObj
            if s29 == "1" then GCS.update_send gcsObj
            if r28 == "1" || s29 == "1" then ioProcess chan0
            for _ in [0:post.toNat!] do PMem.bframe 0 (0x1000000 : UInt32)
            return (ap, br)
          let step : PMem.M (Array String × Array String) := do
            -- (slice 2) the HAL clock is the World's (`PMem.clock`); the GCS work of the step reads the step's time, as
            -- `clockUs` gave it before (during boot the World's clock runs ahead inside its own delays): set for the
            -- step, the World's own value restored after it
            let wc := (← get).w.est_scheduler._clock_us
            modify fun m => { m with w := { m.w with est_scheduler := { m.w.est_scheduler with _clock_us := tt.toNat!.toUInt64 } } }
            let r ← stepBody
            modify fun m => { m with w := { m.w with est_scheduler := { m.w.est_scheduler with _clock_us := wc } } }
            return r
          let ((ap, br), m2) := step.run m
          let b ← IO.monoNanosNow
          tGcs := tGcs + (b - a)
          cur := cur + (b - a)
          applied := applied ++ ap
          bridged := bridged ++ br
          m := m2
          let txs := if m.tx.size == 0 then "-" else toHex m.tx
          h.putStrLn s!"{k} {txs} {String.intercalate "," (m.bfAt.toList.map toString)}"
          m := { m with tx := ByteArray.empty }
          tStep := tStep.push cur
          cur := 0
          nsteps := nsteps + 1
        | _ => pure ()
      else
        let a ← IO.monoNanosNow
        let (r, m2) := (est t).run m
        m := m2
        if t[0]! == "E" && (m.w.est_scheduler._lines.toNat == 123456789) then IO.eprintln "?"
        let b ← IO.monoNanosNow
        if t[0]! != "E" && t[0]! != "F" then
          tEst := tEst + (b - a)
          cur := cur + (b - a)
        if let some s := r then out.putStrLn s
    IO.FS.writeBinFile (outP ++ ".storage") m.st
    h.putStrLn s!"# vehicle parameter values applied ({applied.toList.eraseDups.length}): {applied.toList.eraseDups}"
    h.putStrLn s!"# bridged parameters whose snapshot differs (not applied: their home is the World) ({bridged.size}): {bridged.toList}"
    h.putStrLn s!"# unreached={m.unreached.toList.eraseDups} log={m.log.size}"
    let bl := (m.log.filter (·.startsWith "bridge ")).toList.eraseDups
    h.putStrLn s!"# bridge calls not adapted: {bl}"
    for l in m.log.toList.take 40 do
      h.putStrLn s!"# log {l}"
    h.putStrLn s!"# step ns {String.intercalate "," (tStep.toList.map toString)}"
    IO.eprintln s!"onestate_replay: {nsteps} steps; GCS work {tGcs.toFloat / 1e9} s ({tGcs.toFloat / 1e3 / nsteps.toFloat} us per step), estimator calls {tEst.toFloat / 1e9} s"
    return 0
  | _ => IO.eprintln "usage: onestate_replay FRAMES ANSWERS STORAGE OUT SNAPSHOT < COMMANDS"; return 2
