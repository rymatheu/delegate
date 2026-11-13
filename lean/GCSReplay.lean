import GCSHarnessData

/-!
`gcs_replay SCHEDULE FRAMES ANSWERS STORAGE OUT` (README.md, "Phase 4: GCS_MAVLink"): the translated GCS on a recorded
session, step by step, as the reference vehicle runs it. Prepared by `ardupilot/gcs/gcs_replay.py` from the session's
`inputs.txt`, `outputs.txt` and `est.txt` (one SCHEDULE line per input line: time, the delay callbacks run during the
step, whether tasks 28 `GCS::update_receive` and 29 `GCS::update_send` ran, the recorded STATUSTEXT frames of the step,
the uplink bytes, home); FRAMES: the recorded frames by message id (the boundary frames' bytes); ANSWERS: the vehicle's
answers. Every call below is a translated ArduPilot function; this file sequences them, feeds the boundary and writes
each step's transmit bytes (with the offsets of the boundary frames) for the comparison.

Boot, as the reference: static construction (AP_Param's, as `ParamBoot`, on this image's addresses; `GCS::GCS`'s
`_singleton = this` for `copter._gcs`; the `ObjectBuffer` statics `GCS_MAVLINK::param_requests(20)` and
`param_replies(5)`), `AP_Vehicle::load_parameters`'s format check and `load_all`, `GCS::init`, `GCS::setup_console`
(`create_gcs_mavlink_backend`: the channel, `load_object_from_eeprom` of its SRn_/MAVn_ parameters,
`GCS_MAVLINK::init` with its SiK reset bytes), `GCS::setup_uarts`. Then per step: the uplink appended to SERIAL0's
receive queue; the IO process (`param_io_timer`, once registered) at the line's consumption; during boot the delay
callbacks (`AP_Vehicle::scheduler_delay_callback`, translated), in the main loop tasks 28 and 29; the IO process after
the loop.
-/

open GCS_lib GCSHarnessData
open FloatLib.Floats (Binary32)

namespace GCSReplay

/-- diagnosis: the value of RTL_CONE_SLOPE (`AP_Param::find`) into the log -/
def probe (tag : String) : PMem.M Unit := do
  let nm ← PMem.alloc 32
  let s := "RTL_CONE_SLOPE"
  for i in [0:s.length] do
    PMem.stU8 (nm + i.toUInt64) (s.toList[i]!).toNat.toUInt8
  let ty ← PMem.alloc 8
  let vp ← AP_Param.find nm ty 0
  let v ← if vp == 0 then pure 0 else PMem.ldU32 vp
  let w ← PMem.ldU32 40980
  modify fun st => { st with log := st.log.push s!"probe {tag}: RTL_CONE_SLOPE at {vp} bits {v}; at 40980: {w}" }

def staticInit (dbg : Bool := false) : PMem.M Unit := do
  StorageAccess.StorageAccess addr'AP_Param___storage 0
  for (c, v) in ctorPointers do
    PMem.stU64 c v
  for (o, t) in ctorDefaults do
    AP_Param.setup_object_defaults o t
  if dbg then probe "after ctorDefaults"
  -- ModeAuto's AP_Mission (mode.h:619): its constructor, the callbacks into ModeAuto left out (skip_members)
  -- AP_Mission.cpp:55 `StorageAccess AP_Mission::_storage(StorageManager::StorageMission)` (a static's constructor)
  StorageAccess.StorageAccess addr'AP_Mission___storage 3
  let zf ← PMem.alloc 48
  AP_Mission.AP_Mission missionObj zf (zf + 16) (zf + 32)
  for (o, a, b, c) in ctorCommandModels do
    AC_CommandModel.AC_CommandModel o (Binary32.ofBits a) (Binary32.ofBits b) (Binary32.ofBits c)
  SRV_Channels.SRV_Channels servoChannels
  AP_Param.AP_Param paramLoader addr'Copter__var_info
  -- GCS::GCS (GCS.h:1147): `_singleton = this` (its setup_object_defaults is in ctorDefaults)
  PMem.stU64 addr'GCS___singleton gcsObj
  ObjectBuffer'GCS_MAVLINK_pending_param_request.ObjectBuffer addr'GCS_MAVLINK__param_requests 20
  ObjectBuffer'GCS_MAVLINK_pending_param_reply.ObjectBuffer addr'GCS_MAVLINK__param_replies 5
  -- the statics' default member initializers (GCS_MAVLINK::last_radio_status.txbuf = 100), generated
  staticDynamicInit

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

/-- The parameters non-GCS code changed (the reference's values after step `step`, `CPP2LEAN_PARAM_SNAPSHOT`:
calibrations, the vehicle's set_default and set_and_save): set where ours differ, through the translated
AP_Param::find and set_float (boundary inputs); the names set. -/
def applySnap (snap : Array String) (step : Nat) : PMem.M (Array String) := do
  let mut applied : Array String := #[]
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
            AP_Param.set_float vp (Binary32.ofBits wbits) t
            applied := applied.push nm
    | _ => pure ()
  return applied

def ioProcess (c : UInt64) : PMem.M Unit := do
  if (← PMem.ldU8 addr'GCS_MAVLINK__param_timer_registered) != 0 then
    GCS_MAVLINK.param_io_timer c

end GCSReplay

open GCSReplay in
def main (args : List String) : IO UInt32 := do
  match args with
  | [schedP, framesP, answersP, stP, outP, snapP] =>
    let st ← IO.FS.readBinFile stP
    let sched ← IO.FS.lines schedP
    let frameLines ← IO.FS.lines framesP
    let answerLines ← IO.FS.lines answersP
    -- recorded frames by id
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
    let dbgNames := (← IO.getEnv "GCS_REPLAY_NAMES").isSome
    let blank := ByteArray.mk (Array.replicate st.size 0)
    let ((), m0) := (staticInit dbgNames).run (initMem blank)
    let fpos : Array Nat := frames.map (fun _ => 0)
    let apos : Array Nat := answers.map (fun _ => 0)
    let m0 : PMem.Mem := { m0 with st := st, frames := frames, framePos := fpos, answers := answers, answerPos := apos }
    let homeAddr := (PMem.alloc sizeLocation).run m0
    let m0 := { homeAddr.2 with homeAddr := homeAddr.1 }
    let noRt := (← IO.getEnv "GCS_REPLAY_NO_RUNTIME").isSome
    let t0 ← IO.monoNanosNow
    let (ok, m1) := (do
        -- AP_Vehicle::setup (as ParamBoot): setup_sketch_defaults (the top-level scalars' defaults), check_var_info
        AP_Param.setup_sketch_defaults
        AP_Param.check_var_info
        let r ← formatCheckAndLoad
        -- Copter::load_parameters (Parameters.cpp:1383, after load_all): `AP_Param::set_frame_type_flags(AP_PARAM_FRAME_COPTER)`
        AP_Param.set_frame_type_flags 1
        if dbgNames then
          probe "after load_all"
        -- ModeAuto's AP_Mission (static construction: its constructor, the callbacks into ModeAuto left out) and
        -- init_ardupilot's `mode_auto.mission.init()`
        AP_Mission.init missionObj
        GCS.init gcsObj
        if dbgNames then
          probe "after GCS.init"
        GCS.setup_console gcsObj
        GCS.setup_uarts gcsObj
        if dbgNames then
          probe "after setup"
        -- Copter::allocate_motors (Phase 5's code; its parameter effect here): each object in the heap, its pointer
        -- (and var_info pointer) member set, its constructors' setup_object_defaults, AP_Param::load_object_from_eeprom
        -- motors: AP_MotorsMatrix's constructor is not translated: its groups' setup_object_defaults; the
        -- controllers: their translated constructors (the AC_PID members' constructor arguments are the defaults their
        -- tables point to); the AHRS view a placeholder object (the constructors keep the reference only)
        -- AP_BattMonitor::init (Phase 5's call): the analog backend of instance 0, its translated constructor
        if !noRt then
          let (cell, size, tab, vcell, mon, st, prm) := battBackend
          let a ← PMem.alloc size
          PMem.stU64 cell a
          PMem.stU64 vcell tab
          AP_BattMonitor_Analog.AP_BattMonitor_Analog a mon st prm
          AP_Param.load_object_from_eeprom a tab
        let view ← PMem.alloc 1024
        let mut addrs : Array UInt64 := #[]
        for k in [0:(if noRt then 0 else runtimeObjects.size)] do
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
        return r : PMem.M Bool).run m0
    let mut m := m1
    let chan0 ← pure ((PMem.ldU64 (gcsObj + offChan)).run m).1
    m := { m with seqAddr := chan0 + offTxSeq, chan0 := chan0 }
    -- the parameters non-GCS code changed by the first parameter request (the reference's values at that step,
    -- `CPP2LEAN_PARAM_SNAPSHOT`; calibrations, the vehicle's set_default and set_and_save): set where ours differ,
    -- through the translated AP_Param::find and set_float (boundary inputs)
    let snap ← IO.FS.lines snapP
    let snapSteps := (snap.filterMap fun l => match l.splitOn " " with
      | ["paramsnap", st, _, _, _] => some st.toNat! | _ => none).toList.eraseDups
    let firstSnap := snapSteps.head?.getD 0
    let (applied0, m2) := (applySnap snap firstSnap).run m
    m := m2
    let mut applied := applied0
    let bootTx := m.tx
    let bootMarks := m.delayMarks
    m := { m with tx := ByteArray.empty }
    let t1 ← IO.monoNanosNow
    let h ← IO.FS.Handle.mk outP .write
    h.putStrLn s!"# vehicle parameter values applied ({applied.size}): {applied.toList}"
    h.putStrLn s!"# boot load_all={ok} channel=0x{(Nat.toDigits 16 chan0.toNat).asString} tx={toHex bootTx} marks={bootMarks.toList}"
    let mut tStep : Nat := 0
    for line in sched do
      match line.splitOn " " with
      | [k, t, dcb, r28, s29, tq, up, home, pre, post] =>
        let tus := t.toNat!.toUInt64
        let hb := hexBytes home
        m := { m with clockUs := tus, rx := m.rx.extract m.rxPos m.rx.size ++ hexBytes (if up == "-" then "" else up),
                      rxPos := 0, textQuota := tq.toNat!, bfAt := #[], inDelayCb := dcb.toNat! > 0, curStep := k.toNat! }
        let a ← IO.monoNanosNow
        let step : PMem.M Unit := do
          if hb.size == 16 then
            for i in [0:16] do
              PMem.stU8 ((← get).homeAddr + i.toUInt64) (hb.get! i)
          -- the vehicle's parameter change notifications (boundary frames: before the GCS work when the
          -- recorded step starts with them, else after it)
          for _ in [0:pre.toNat!] do PMem.bframe 0 (0x1000000 : UInt32) -- the next vehicle frame (by its place)
          for st in snapSteps.drop 1 do
            if st + 1 == k.toNat! then
              discard <| applySnap snap st
          ioProcess chan0
          for _ in [0:dcb.toNat!] do
            AP_Vehicle.scheduler_delay_callback
          if r28 == "1" then GCS.update_receive gcsObj
          if s29 == "1" then GCS.update_send gcsObj
          if r28 == "1" || s29 == "1" then ioProcess chan0
          for _ in [0:post.toNat!] do PMem.bframe 0 (0x1000000 : UInt32)
        let ((), m2) := step.run m
        if let some r := (← IO.getEnv "GCS_REPLAY_DUMP") then
          -- diagnosis: the bytes of channel 0 after the step (as reference/hal/est_probe.cpp's CPP2LEAN_GCS_DUMP)
          match r.splitOn "," with
          | [a, b] =>
            if a.toNat! ≤ k.toNat! && k.toNat! ≤ b.toNat! then
              let (bs, _) := (do
                  let mut out := ByteArray.empty
                  for i in [0:sizeChannel] do
                    out := out.push (← PMem.ldU8 (chan0 + i.toUInt64))
                  return out : PMem.M ByteArray).run m2
              IO.eprintln s!"gcsdump {k} {toHex bs}"
          | _ => pure ()
        let b ← IO.monoNanosNow
        tStep := tStep + (b - a)
        m := m2
        let txs := if m.tx.size == 0 then "-" else toHex m.tx
        let bfs := String.intercalate "," (m.bfAt.toList.map toString)
        h.putStrLn s!"{k} {txs} {bfs}"
        m := { m with tx := ByteArray.empty }
      | _ => pure ()
    IO.FS.writeBinFile (outP ++ ".storage") m.st
    h.putStrLn s!"# unreached={m.unreached.toList.eraseDups} log={m.log.size}"
    for l in m.log.toList.take 40 do
      h.putStrLn s!"# log {l}"
    IO.eprintln s!"gcs_replay: boot {(t1 - t0).toFloat / 1e6} ms; {sched.size} steps, GCS work {tStep.toFloat / 1e9} s ({tStep.toFloat / 1e3 / sched.size.toFloat} us per step)"
    return 0
  | _ => IO.eprintln "usage: gcs_replay SCHEDULE FRAMES ANSWERS STORAGE OUT SNAPSHOT"; return 2
