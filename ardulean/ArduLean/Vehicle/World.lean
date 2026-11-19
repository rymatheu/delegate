import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_3

/-!
`World`: generated items without a C++ function of their own.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- (Phase 5c) a World text event's format and variadic arguments in memory (a frame: the block of 8-byte
slots, the format's bytes and NUL, the string arguments' bytes and NULs): (frame, format, block). -/
def worldOutputs'textBlock (fmt : String) (args : Array (Sum UInt64 String)) : PMem.M (UInt64 × UInt64 × UInt64) := do
  let fb := fmt.toUTF8
  let ss := args.foldl (fun n a => match a with | .inr s => n + s.toUTF8.size + 1 | .inl _ => n) 0
  let fp ← PMem.enter (8 * args.size + fb.size + 1 + ss)
  let mut p := fp + (8 * args.size).toUInt64
  let f := p
  for i in [0:fb.size] do
    PMem.stU8 (p + i.toUInt64) (fb.get! i)
  PMem.stU8 (p + fb.size.toUInt64) 0
  p := p + (fb.size + 1).toUInt64
  for k in [0:args.size] do
    match args[k]! with
    | .inl w => PMem.stU64 (fp + (8 * k).toUInt64) w
    | .inr s =>
      let b := s.toUTF8
      for i in [0:b.size] do
        PMem.stU8 (p + i.toUInt64) (b.get! i)
      PMem.stU8 (p + b.size.toUInt64) 0
      PMem.stU64 (fp + (8 * k).toUInt64) p
      p := p + (b.size + 1).toUInt64
  return (fp, f, fp)

/-- (Phase 5d) the bytes a buffer holding a World text needs: the size of its last write (at least 1, a
zero-filled byte: the empty string) -/
def worldOutputs'ctextSize (t : Estimator_lib.CText) : UInt64 :=
  match t with
  | .fmt n _ _ => max n 1
  | .text n _ _ => max n 1
  | _ => 1

/-- (Phase 5d) a World text (`Estimator_lib.CText`, cpp2lean.py --text-buffers) written into the buffer at `bp`
with the translated AP_HAL::Util::snprintf, as the C++ wrote it (a format that is a text formatted first). -/
def worldOutputs'ctext (bp : UInt64) (t : Estimator_lib.CText) : PMem.M Unit := do
  match t with
  | .none => pure ()
  | .null => PMem.unreached "cpp2lean::ctext_null"
  | .fmt n g a =>
    let u ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)  -- hal.util
    let (ip, f, iv) ← worldOutputs'textBlock g a
    discard <| AP_HAL.Util.snprintf u bp n f iv
    PMem.leave ip
  | .text n src a =>
    let sb ← PMem.enter (worldOutputs'ctextSize src).toNat
    worldOutputs'ctext sb src
    let u ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)  -- hal.util
    let (ip, _, iv) ← worldOutputs'textBlock "" a
    discard <| AP_HAL.Util.snprintf u bp n sb iv
    PMem.leave ip
    PMem.leave sb
termination_by structural t

def worldOutputs'drain : PMem.M Unit := do
  let os ← modifyGet fun m => (m.eo, { m with eo := #[] })
  for o in os do
    match o with
    | .AP_Param_notify x0 =>
      AP_Param.notify (PMem.Bridge.addrOfPath x0)
    | .AP_Param_save x0 x1 =>
      AP_Param.save (PMem.Bridge.addrOfPath x0) (x1)
    | .console_printf x0 x1 =>
      let (fpc, fc, vac) ← worldOutputs'textBlock x0 x1
      let mut av : Array UInt64 := #[fc]
      for k in [0:x1.size] do
        av := av.push (← PMem.ldU64 (vac + (8 * k).toUInt64))
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" 0 av
      PMem.leave fpc
    | .est_mark x0 x1 =>
      discard <| PMem.hal "cpp2lean::est_mark" 0 #[(x0).toUInt64, (x1).toUInt64]
    | .mavlink_msg_ekf_status_report_send_struct x0 x1 =>
      let a1 ← PMem.enter 26
      PMem.stF32 (a1 + 0) x1.velocity_variance
      PMem.stF32 (a1 + 4) x1.pos_horiz_variance
      PMem.stF32 (a1 + 8) x1.pos_vert_variance
      PMem.stF32 (a1 + 12) x1.compass_variance
      PMem.stF32 (a1 + 16) x1.terrain_alt_variance
      PMem.stU16 (a1 + 20) x1.flags
      PMem.stF32 (a1 + 22) x1.airspeed_variance
      mavlink_msg_ekf_status_report_send_struct (Estimator_lib.mavlink_channel_t.toInt x0) a1
      PMem.leave a1
    | .mavlink_msg_gps2_raw_send x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 =>
      mavlink_msg_gps2_raw_send (Estimator_lib.mavlink_channel_t.toInt x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) (x15) (x16) (x17) (x18)
    | .mavlink_msg_gps_raw_int_send x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =>
      mavlink_msg_gps_raw_int_send (Estimator_lib.mavlink_channel_t.toInt x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) (x15) (x16)
    | .send_message x0 =>
      let a0 ← gcs
      GCS.send_message a0 (Estimator_lib.ap_message.toInt x0)
    | .send_text x0 x1 x2 =>
      let a0 ← gcs
      let (fp2, f2, va2) ← worldOutputs'textBlock x1 x2
      GCS.send_text a0 (x0) f2 va2
      PMem.leave fp2
    | .send_text_snprintf x0 x1 x2 =>
      let a0 ← gcs
      let bp2 ← PMem.enter (worldOutputs'ctextSize x2).toNat
      worldOutputs'ctext bp2 x2
      let (fp2, f2, va2) ← worldOutputs'textBlock x1 #[Sum.inl bp2]
      GCS.send_text a0 (x0) f2 va2
      PMem.leave fp2
      PMem.leave bp2
    | .text_sink x0 x1 =>
      worldOutputs'ctext x0 x1
    | .write_home_to_storage =>
      let a0 ← AP.mission
      AP_Mission.write_home_to_storage a0
    | _ => pure ()

end Vehicle_lib
