import ArduLean.Runtime.Boundary
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2

/-!
ArduPilot `libraries/AP_Mission`, part 3 of 3. Sources: `libraries/AP_Mission/AP_Mission.cpp`, `libraries/AP_Mission/AP_Mission_ChangeDetector.cpp`, `libraries/AP_Mission/AP_Mission_Commands.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Mission::increment_jump_times_run : void (Mission_Command &, bool)`, `AP_Mission.cpp:2486-2517`. -/
def AP_Mission.increment_jump_times_run.body (fp : UInt64) (this : UInt64) (cmd : UInt64) (send_gcs_msg : Bool) : PMem.M Unit := do
  let mut send_gcs_msg := send_gcs_msg
  let t'1 ← PMem.ldU16 (cmd + 2)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) != (UInt32.toInt32 ((177 : UInt32)))) then
    return ()
  for i'2 in [0:100] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
    let t'4 ← PMem.ldU16 cmd
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (UInt32.toInt32 (UInt16.toUInt32 (t'4)))) then
      let t'5 := (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2)
      let t'6 ← PMem.ldI16 t'5
      let t'7 := (t'6 + 1)
      PMem.stI16 t'5 t'7
      if send_gcs_msg then
        let t'8 ← PMem.ldI16 ((cmd + 8) + 2)
        if ((Int16.toInt32 (t'8)) == (-(1 : Int32))) then
          let t'9 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
          PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'9))))))
          let t'10 ← PMem.ldI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2)
          PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 ((Int16.toInt32 (t'10)))))
          let t'11 ← gcs
          GCS.send_text t'11 (6 : UInt32) (0x1743f : UInt64) /- "Mission: %u Jump %i/unlimited" -/ (fp + 0)
        else
          let t'12 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
          PMem.stU64 (fp + 16) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'12))))))
          let t'13 ← PMem.ldI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2)
          PMem.stU64 (fp + 24) (Int64.toUInt64 (Int32.toInt64 ((Int16.toInt32 (t'13)))))
          let t'14 ← PMem.ldI16 ((cmd + 8) + 2)
          PMem.stU64 (fp + 32) (Int64.toUInt64 (Int32.toInt64 ((Int16.toInt32 (t'14)))))
          let t'15 ← gcs
          GCS.send_text t'15 (6 : UInt32) (0x1745d : UInt64) /- "Mission: %u Jump %i/%i" -/ (fp + 16)
      return ()
    else
      let t'16 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'16))) == (65535 : Int32)) then
        let t'17 ← PMem.ldU16 cmd
        PMem.stU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) t'17
        let t'18 := Int32.toInt16 ((1 : Int32))
        PMem.stI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2) t'18
        return ()
  return ()

def AP_Mission.increment_jump_times_run (this : UInt64) (cmd : UInt64) (send_gcs_msg : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 40
  let r ← AP_Mission.increment_jump_times_run.body fp this cmd send_gcs_msg
  PMem.leave fp
  return r

/-- C++ `AP_Mission::get_next_cmd : bool (uint16_t, Mission_Command &, bool, bool)`, `AP_Mission.cpp:2292-2374`. -/
def AP_Mission.get_next_cmd.body (fp : UInt64) (this : UInt64) (start_index : UInt16) (cmd : UInt64) (increment_jump_num_times_if_found : Bool) (send_gcs_msg : Bool) : PMem.M Bool := do
  let mut start_index := start_index
  let mut increment_jump_num_times_if_found := increment_jump_num_times_if_found
  let mut send_gcs_msg := send_gcs_msg
  let mut cmd_index : UInt16 := start_index
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let mut jump_index : UInt16 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  let mut max_loops : UInt8 := Int8.toUInt8 (Int32.toInt8 ((64 : Int32)))
  for _ in PMem.loopFuel do
    let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'2 ← PMem.ldI16 t'1
    if !((decide ((UInt16.toUInt32 (cmd_index)) < (Int32.toUInt32 (Int16.toInt32 (t'2)))))) then break
    let t'3 ← AP_Mission.read_cmd_from_storage this cmd_index (fp + 0)
    if !t'3 then
      return false
    let t'4 ← PMem.ldU16 ((fp + 0) + 2)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'4))) == (UInt32.toInt32 ((601 : UInt32)))) then
      let t'5 ← PMem.ldU16 ((fp + 0) + 8)
      let t'6 ← AP_Mission.get_index_of_jump_tag this t'5
      PMem.stU16 ((fp + 0) + 8) t'6
      let t'7 := UInt32.toUInt16 ((177 : UInt32))
      PMem.stU16 ((fp + 0) + 2) t'7
    let t'8 ← PMem.ldU16 ((fp + 0) + 2)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) == (UInt32.toInt32 ((177 : UInt32)))) then
      let t'9 := max_loops
      let t'10 := (t'9 - 1)
      max_loops := t'10
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'9))) == (0 : Int32)) then
        return false
      let t'11 ← PMem.ldU16 ((fp + 0) + 8)
      let t'12 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
      let t'13 ← PMem.ldI16 t'12
      let mut sc'15 := (decide ((UInt16.toUInt32 (t'11)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'13)))))
      if !sc'15 then
        let t'14 ← PMem.ldU16 ((fp + 0) + 8)
        sc'15 := ((UInt32.toInt32 (UInt16.toUInt32 (t'14))) == (0 : Int32))
      if sc'15 then
        return false
      if ((!increment_jump_num_times_if_found) && ((UInt32.toInt32 (UInt16.toUInt32 (jump_index))) == (UInt32.toInt32 (UInt16.toUInt32 (cmd_index))))) then
        return false
      if ((UInt32.toInt32 (UInt16.toUInt32 (jump_index))) == (65535 : Int32)) then
        jump_index := cmd_index
      let t'16 ← PMem.ldI16 (((fp + 0) + 8) + 2)
      let mut sc'19 := ((Int16.toInt32 (t'16)) == (-(1 : Int32)))
      if !sc'19 then
        let t'17 ← AP_Mission.get_jump_times_run this (fp + 0)
        let t'18 ← PMem.ldI16 (((fp + 0) + 8) + 2)
        sc'19 := (decide ((Int16.toInt32 (t'17)) < (Int16.toInt32 (t'18))))
      if sc'19 then
        let mut sc'21 := increment_jump_num_times_if_found
        if sc'21 then
          let t'20 ← PMem.ldB ((this + 4) + 8)
          sc'21 := !t'20
        if sc'21 then
          AP_Mission.increment_jump_times_run this (fp + 0) send_gcs_msg
        let t'22 ← PMem.ldU16 ((fp + 0) + 8)
        cmd_index := t'22
      else
        let mut sc'24 := increment_jump_num_times_if_found
        if sc'24 then
          let t'23 ← AP_Mission.option_is_set this (8 : Int32)
          sc'24 := !t'23
        if sc'24 then
          for i'25 in [0:100] do
            let i : UInt8 := UInt8.ofNat i'25
            let t'26 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
            if ((UInt32.toInt32 (UInt16.toUInt32 (t'26))) == (UInt32.toInt32 (UInt16.toUInt32 (cmd_index)))) then
              let t'27 := Int32.toInt16 ((0 : Int32))
              PMem.stI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2) t'27
              break
        let t'28 := cmd_index
        let t'29 := (t'28 + 1)
        cmd_index := t'29
    else
      discard <| PMem.memcpy cmd (fp + 0) 28
      discard <| pure (cmd)
      return true
  return false

def AP_Mission.get_next_cmd (this : UInt64) (start_index : UInt16) (cmd : UInt64) (increment_jump_num_times_if_found : Bool) (send_gcs_msg : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.get_next_cmd.body fp this start_index cmd increment_jump_num_times_if_found send_gcs_msg
  PMem.leave fp
  return r

/-- C++ `AP_Mission::distance_to_mission_leg : bool (uint16_t, uint16_t &, float &, uint16_t &, const Location &)`, `AP_Mission.cpp:2797-2877`. -/
def AP_Mission.distance_to_mission_leg.body (fp : UInt64) (this : UInt64) (start_index : UInt16) (search_remaining : UInt64) (rejoin_distance : UInt64) (rejoin_index : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let mut start_index := start_index
  let mut goto_reset_do_jump_tracking : Bool := false
  Location.Location (fp + 0)
  AP_Mission.Mission_Command.Mission_Command (fp + 16)
  let t'1 := Int32.toBinary32 ((-(1 : Int32)))
  PMem.stF32 rejoin_distance t'1
  let t'2 := Int16.toUInt16 (Int32.toInt16 ((-(1 : Int32))))
  PMem.stU16 rejoin_index t'2
  let mut ret : Bool := false
  for i'3 in [0:100] do
    let i : UInt8 := UInt8.ofNat i'3
    discard <| PMem.memcpy ((fp + 48) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) 4
    discard <| pure (((fp + 48) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64))
  let mut index : UInt16 := start_index
  for _ in [0:1] do
    let mut first'4 := true
    for _ in PMem.loopFuel do
      if !first'4 then
        let t'5 ← PMem.ldU16 search_remaining
        let t'6 := (t'5 - 1)
        PMem.stU16 search_remaining t'6
        pure ()
      first'4 := false
      let t'7 ← PMem.ldU16 search_remaining
      if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) > (0 : Int32)))) then break
      let mut cmd_index : UInt16 := index
      let mut first'8 := true
      for _ in PMem.loopFuel do
        if !first'8 then
          let t'9 := cmd_index
          let t'10 := (t'9 + 1)
          cmd_index := t'10
          pure ()
        first'8 := false
        let t'11 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
        let t'12 ← PMem.ldI16 t'11
        if !((decide ((UInt16.toUInt32 (cmd_index)) ≤ (Int32.toUInt32 (Int16.toInt32 (t'12)))))) then break
        let t'13 ← AP_Mission.get_next_cmd this cmd_index (fp + 16) true false
        if t'13 then
          break
        else
          goto_reset_do_jump_tracking := true
          break
      if goto_reset_do_jump_tracking then
        break
      let t'14 ← PMem.ldU16 (fp + 16)
      let t'15 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'14))) + (1 : Int32))))
      index := t'15
      let t'16 ← PMem.ldU16 ((fp + 16) + 2)
      let t'17 ← AP_Mission.stored_in_location t'16
      let mut sc'19 := t'17
      if sc'19 then
        let t'18 ← Location.initialised ((fp + 16) + 8)
        sc'19 := t'18
      if sc'19 then
        let t'20 ← PMem.ldI32 ((fp + 0) + 8)
        let mut sc'22 := (t'20 == (0 : Int32))
        if sc'22 then
          let t'21 ← PMem.ldI32 ((fp + 0) + 12)
          sc'22 := (t'21 == (0 : Int32))
        if sc'22 then
          discard <| PMem.memcpy (fp + 0) ((fp + 16) + 8) 16
          discard <| pure ((fp + 0))
          Location.get_distance_NED_alt_frame (fp + 0) (fp + 448) current_loc
          let t'23 := (fp + 448)
          let t'24 ← Vector3'float.length t'23
          PMem.stF32 rejoin_distance t'24
          let t'25 ← PMem.ldU16 (fp + 16)
          PMem.stU16 rejoin_index t'25
          ret := true
        else
          Location.get_distance_NED_alt_frame (fp + 0) (fp + 480) ((fp + 16) + 8)
          let t'26 := (fp + 480)
          Vector3'float.Vector3'3 (fp + 464) t'26
          let t'27 ← Vector3'float.is_zero (fp + 464)
          if !t'27 then
            Location.get_distance_NED_alt_frame (fp + 0) (fp + 512) current_loc
            let t'28 := (fp + 512)
            Vector3'float.Vector3'3 (fp + 496) t'28
            Vector3'float.projected (fp + 496) (fp + 544) (fp + 464)
            let t'29 := (fp + 544)
            Vector3'float.Vector3'3 (fp + 528) t'29
            let t'30 ← PMem.ldF32 (fp + 528)
            PMem.stI32 (fp + 556) (0 : Int32)
            let t'31 ← MIN'int_float (fp + 556) (fp + 464)
            PMem.stI32 (fp + 560) (0 : Int32)
            let t'32 ← MAX'int_float (fp + 560) (fp + 464)
            let t'33 ← constrain_value_line'float t'30 t'31 t'32 (Int32.toUInt32 ((2845 : Int32)))
            PMem.stF32 (fp + 528) t'33
            let t'34 ← PMem.ldF32 ((fp + 528) + 4)
            PMem.stI32 (fp + 564) (0 : Int32)
            let t'35 ← MIN'int_float (fp + 564) ((fp + 464) + 4)
            PMem.stI32 (fp + 568) (0 : Int32)
            let t'36 ← MAX'int_float (fp + 568) ((fp + 464) + 4)
            let t'37 ← constrain_value_line'float t'34 t'35 t'36 (Int32.toUInt32 ((2846 : Int32)))
            PMem.stF32 ((fp + 528) + 4) t'37
            let t'38 ← PMem.ldF32 ((fp + 528) + 8)
            PMem.stI32 (fp + 572) (0 : Int32)
            let t'39 ← MIN'int_float (fp + 572) ((fp + 464) + 8)
            PMem.stI32 (fp + 576) (0 : Int32)
            let t'40 ← MAX'int_float (fp + 576) ((fp + 464) + 8)
            let t'41 ← constrain_value_line'float t'38 t'39 t'40 (Int32.toUInt32 ((2847 : Int32)))
            PMem.stF32 ((fp + 528) + 8) t'41
            Vector3'float.operator_'2 (fp + 528) (fp + 584) (fp + 496)
            let t'42 := (fp + 584)
            let t'43 ← Vector3'float.length t'42
            let mut disttemp : Binary32 := t'43
            discard <| PMem.memcpy (fp + 0) ((fp + 16) + 8) 16
            discard <| pure ((fp + 0))
            let t'44 ← PMem.ldF32 rejoin_distance
            let mut sc'47 := (decide (disttemp < t'44))
            if !sc'47 then
              let t'45 ← PMem.ldF32 rejoin_distance
              let t'46 ← is_negative'float t'45
              sc'47 := t'46
            if sc'47 then
              PMem.stF32 rejoin_distance disttemp
              let t'48 ← PMem.ldU16 (fp + 16)
              PMem.stU16 rejoin_index t'48
            ret := true
      let t'49 ← PMem.ldU16 ((fp + 16) + 2)
      let t'50 ← AP_Mission.is_landing_type_cmd this t'49
      let mut sc'52 := t'50
      if !sc'52 then
        let t'51 ← PMem.ldU16 ((fp + 16) + 2)
        sc'52 := ((UInt32.toInt32 (UInt16.toUInt32 (t'51))) == (UInt32.toInt32 ((189 : UInt32))))
      if sc'52 then
        goto_reset_do_jump_tracking := true
        break
    if goto_reset_do_jump_tracking then
      break
    if goto_reset_do_jump_tracking then
      break
    ret := false
  for i'2'53 in [0:100] do
    let i'2 : UInt8 := UInt8.ofNat i'2'53
    discard <| PMem.memcpy ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) ((fp + 48) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) 4
    discard <| pure (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64))
  return ret

def AP_Mission.distance_to_mission_leg (this : UInt64) (start_index : UInt16) (search_remaining : UInt64) (rejoin_distance : UInt64) (rejoin_index : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 596
  let r ← AP_Mission.distance_to_mission_leg.body fp this start_index search_remaining rejoin_distance rejoin_index current_loc
  PMem.leave fp
  return r

/-- C++ `AP_Mission::command_do_set_repeat_dist : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:160-165`. -/
def AP_Mission.command_do_set_repeat_dist.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (cmd + 4)
  PMem.stU16 (this + 86) t'1
  let t'2 ← PMem.ldU16 (this + 86)
  PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'2))))))
  let t'3 ← gcs
  GCS.send_text t'3 (6 : UInt32) (0x1737d : UInt64) /- "Resume repeat dist set to %u m" -/ (fp + 0)
  return true

def AP_Mission.command_do_set_repeat_dist (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Mission.command_do_set_repeat_dist.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::get_next_nav_cmd : bool (uint16_t, Mission_Command &)`, `AP_Mission.cpp:563-580`. -/
def AP_Mission.get_next_nav_cmd (this : UInt64) (start_index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let mut start_index := start_index
  let mut cmd_index : UInt16 := start_index
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := cmd_index
      let t'3 := (t'2 + 1)
      cmd_index := t'3
      pure ()
    first'1 := false
    let t'4 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'5 ← PMem.ldI16 t'4
    if !((decide ((UInt16.toUInt32 (cmd_index)) < (Int32.toUInt32 (Int16.toInt32 (t'5)))))) then break
    let t'6 ← AP_Mission.get_next_cmd this cmd_index cmd false true
    if !t'6 then
      return false
    let t'7 ← AP_Mission.is_nav_cmd cmd
    if t'7 then
      return true
  return false

/-- C++ `AP_Mission::get_landing_sequence_start : uint16_t (const Location &)`, `AP_Mission.cpp:2536-2566`. -/
def AP_Mission.get_landing_sequence_start.body (fp : UInt64) (this : UInt64) (current_loc : UInt64) : PMem.M UInt16 := do
  let mut landing_start_index : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut min_distance : Binary32 := Int32.toBinary32 ((-(1 : Int32)))
  let t'1 ← AP_Mission.num_commands this
  let mut count : UInt16 := t'1
  for i'2 in [1:count.toNat] do
    let i : UInt16 := UInt16.ofNat i'2
    let t'3 ← AP_Mission.get_command_id this i
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) != (UInt32.toInt32 (UInt16.toUInt32 ((UInt32.toUInt16 ((189 : UInt32))))))) then
      continue
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'4 ← AP_Mission.read_cmd_from_storage this i (fp + 0)
    if !t'4 then
      continue
    let t'5 ← PMem.ldU16 ((fp + 0) + 2)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (UInt32.toInt32 ((189 : UInt32)))) then
      let t'6 ← Location.initialised ((fp + 0) + 8)
      let mut sc'8 := !t'6
      if sc'8 then
        let t'7 ← AP_Mission.get_next_nav_cmd this i (fp + 0)
        sc'8 := !t'7
      if sc'8 then
        continue
      Location.get_distance_NED_alt_frame ((fp + 0) + 8) (fp + 32) current_loc
      let t'9 := (fp + 32)
      let t'10 ← Vector3'float.length t'9
      let mut tmp_distance : Binary32 := t'10
      if ((decide (min_distance < (Int32.toBinary32 ((0 : Int32))))) || (decide (tmp_distance < min_distance))) then
        min_distance := tmp_distance
        landing_start_index := i
  return landing_start_index

def AP_Mission.get_landing_sequence_start (this : UInt64) (current_loc : UInt64) : PMem.M UInt16 := do
  let fp ← PMem.enter 44
  let r ← AP_Mission.get_landing_sequence_start.body fp this current_loc
  PMem.leave fp
  return r

/-- C++ `AP_Mission::is_takeoff_next : bool (uint16_t)`, `AP_Mission.cpp:194-219`. -/
def AP_Mission.is_takeoff_next.body (fp : UInt64) (this : UInt64) (cmd_index : UInt16) : PMem.M Bool := do
  let mut cmd_index := cmd_index
  discard <| PMem.memset ((fp + 0) + 0) 0 2
  discard <| PMem.memset ((fp + 0) + 2) 0 2
  discard <| PMem.memset ((fp + 0) + 4) 0 2
  AP_Mission.Content.Content ((fp + 0) + 8)
  discard <| PMem.memset ((fp + 0) + 24) 0 1
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      let t'4 := cmd_index
      let t'5 := (t'4 + 1)
      cmd_index := t'5
      pure ()
    first'1 := false
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (16 : Int32)))) then break
    let t'6 ← AP_Mission.get_next_nav_cmd this cmd_index (fp + 0)
    if !t'6 then
      return false
    let t'7 ← PMem.ldU16 ((fp + 0) + 2)
    let sw'8 := UInt32.toInt32 (UInt16.toUInt32 (t'7))
    if sw'8 == (84 : Int32) || sw'8 == (22 : Int32) || sw'8 == (24 : Int32) then
      return true
    else if sw'8 == (218 : Int32) || sw'8 == (93 : Int32) then
      continue
      return false
    else
      return false
  return false

def AP_Mission.is_takeoff_next (this : UInt64) (cmd_index : UInt16) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.is_takeoff_next.body fp this cmd_index
  PMem.leave fp
  return r

/-- C++ `AP_Mission::starts_with_takeoff_cmd : bool ()`, `AP_Mission.cpp:222-229`. -/
def AP_Mission.starts_with_takeoff_cmd (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 84)
  let t'2 ← PMem.ldI8 t'1
  let mut c'3 : Int32 := default
  if t'2 != (0 : Int8) then
    c'3 := (65535 : Int32)
  else
    let t'4 ← PMem.ldU16 (this + 88)
    c'3 := UInt32.toInt32 (UInt16.toUInt32 (t'4))
  let mut cmd_index : UInt16 := Int16.toUInt16 (Int32.toInt16 (c'3))
  if ((UInt32.toInt32 (UInt16.toUInt32 (cmd_index))) == (65535 : Int32)) then
    let t'5 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
    cmd_index := t'5
  let t'6 ← AP_Mission.is_takeoff_next this cmd_index
  return t'6

/-- C++ `AP_Mission_ChangeDetector::check_for_mission_change : bool ()`, `AP_Mission_ChangeDetector.cpp:9-57`. -/
def AP_Mission_ChangeDetector.check_for_mission_change.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP.mission
  let mission : UInt64 := t'1
  let t'2 ← AP_Mission.last_change_time_ms mission
  let mut change_time_ms : UInt32 := t'2
  let t'3 ← PMem.ldU32 this
  let mut update_time_changed : Bool := (change_time_ms != t'3)
  let t'4 ← AP_Mission.get_current_nav_index mission
  let mut curr_cmd_idx : UInt16 := t'4
  let t'5 ← PMem.ldU16 (this + 4)
  let mut curr_cmd_idx_changed : Bool := ((UInt32.toInt32 (UInt16.toUInt32 (curr_cmd_idx))) != (UInt32.toInt32 (UInt16.toUInt32 (t'5))))
  if ((!update_time_changed) && (!curr_cmd_idx_changed)) then
    return false
  let mut cmds_changed : Bool := false
  let mut num_cmds : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut cmd_idx : UInt16 := curr_cmd_idx
  AP_Mission.Mission_Command.Mission_Command ((fp + 0) + 0)
  AP_Mission.Mission_Command.Mission_Command ((fp + 0) + 28)
  AP_Mission.Mission_Command.Mission_Command ((fp + 0) + 56)
  for _ in PMem.loopFuel do
    let mut sc'7 := (decide ((UInt8.toUInt64 (num_cmds)) < ((84 : UInt64) / (28 : UInt64))))
    if sc'7 then
      let t'6 ← AP_Mission.get_next_nav_cmd mission cmd_idx ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (num_cmds))) * 28).toUInt64)
      sc'7 := t'6
    if !(sc'7) then break
    let t'8 := num_cmds
    let t'9 := (t'8 + 1)
    num_cmds := t'9
    let t'10 ← PMem.ldU8 (this + 6)
    let mut sc'12 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) > (UInt32.toInt32 (UInt8.toUInt32 (t'10)))))
    if !sc'12 then
      let t'11 ← AP_Mission.Mission_Command.operator__ ((fp + 0) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64) ((this + 8) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64)
      sc'12 := t'11
    if sc'12 then
      cmds_changed := true
      discard <| PMem.memcpy ((this + 8) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64) ((fp + 0) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64) 28
      discard <| pure (((this + 8) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64))
    let t'13 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) - (1 : Int32)))) * 28).toUInt64)
    let t'14 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'13))) + (1 : Int32))))
    cmd_idx := t'14
  let t'15 ← PMem.ldU8 (this + 6)
  if ((UInt32.toInt32 (UInt8.toUInt32 (num_cmds))) != (UInt32.toInt32 (UInt8.toUInt32 (t'15)))) then
    cmds_changed := true
  PMem.stU32 this change_time_ms
  PMem.stU16 (this + 4) curr_cmd_idx
  PMem.stU8 (this + 6) num_cmds
  return (cmds_changed && (!curr_cmd_idx_changed))

def AP_Mission_ChangeDetector.check_for_mission_change (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 84
  let r ← AP_Mission_ChangeDetector.check_for_mission_change.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::init : void ()`, `AP_Mission.cpp:64-105`. -/
def AP_Mission.init.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP.boardConfig
  let mut bc : UInt64 := t'1
  if (bc != (0 : UInt64)) then
    let t'2 ← AP_BoardConfig.get_sdcard_mission_kb
    let mut size_kb : UInt16 := t'2
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (size_kb))) > (0 : Int32))) then
      PMem.unreached "StorageAccess::attach_file"
      let t'3 := !(default : Bool)
      PMem.stB (this + 606) t'3
      let t'4 ← PMem.ldB (this + 606)
      if t'4 then
        PMem.stI16 (fp + 0) (Int32.toInt16 ((0 : Int32)))
        AP_ParamTBase'short_2.set (this + 80) (fp + 0)
  let t'5 ← StorageAccess.size (0xbf28 : UInt64) /- &AP_Mission::_storage -/
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) ≥ ((15 : Int32) + (4 : Int32)))) then
    let t'6 ← StorageAccess.size (0xbf28 : UInt64) /- &AP_Mission::_storage -/
    let t'7 := UInt32.toUInt16 ((((UInt16.toUInt32 (t'6)) - (4 : UInt32)) / (Int32.toUInt32 ((15 : Int32)))))
    PMem.stU16 (this + 604) t'7
  let t'8 ← AP_ParamTBase'short_2.get (this + 80)
  let t'9 ← PMem.ldI16 t'8
  let t'10 ← PMem.ldU16 (this + 604)
  if (decide ((Int16.toInt32 (t'9)) > (UInt32.toInt32 (UInt16.toUInt32 (t'10))))) then
    PMem.stI16 (fp + 2) (Int32.toInt16 ((0 : Int32)))
    AP_ParamTBase'short_2.set (this + 80) (fp + 2)
  AP_Mission.check_eeprom_version this
  AP_Mission.init_jump_tracking this
  let t'11 ← AP_Mission.option_is_set this (1 : Int32)
  if t'11 then
    let t'12 ← gcs
    GCS.send_text t'12 (6 : UInt32) (0x173be : UInt64) /- "Clearing Mission" -/ (fp + 8)
    let t'13 ← AP_Mission.clear this
    discard <| pure (t'13)
  let t'14 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 596) t'14
  return ()

def AP_Mission.init (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AP_Mission.init.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::continue_after_land_check_for_takeoff : bool ()`, `AP_Mission.cpp:237-246`. -/
def AP_Mission.continue_after_land_check_for_takeoff (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Mission.continue_after_land this
  if !t'1 then
    return false
  let t'2 ← PMem.ldU16 (this + 88)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (65535 : Int32)) then
    return false
  let t'3 ← PMem.ldU16 (this + 88)
  let t'4 ← AP_Mission.is_takeoff_next this (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'3))) + (1 : Int32)))))
  return t'4

/-- C++ `AP_Mission::get_next_do_cmd : bool (uint16_t, Mission_Command &)`, `AP_Mission.cpp:2380-2401`. -/
def AP_Mission.get_next_do_cmd.body (fp : UInt64) (this : UInt64) (start_index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let mut start_index := start_index
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  if (decide ((UInt16.toUInt32 (start_index)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'2))))) then
    return false
  let t'3 ← AP_Mission.get_next_cmd this start_index (fp + 0) false true
  if !t'3 then
    return false
  else
    let t'4 ← AP_Mission.is_nav_cmd (fp + 0)
    if t'4 then
      return false
    else
      discard <| PMem.memcpy cmd (fp + 0) 28
      discard <| pure (cmd)
      return true

def AP_Mission.get_next_do_cmd (this : UInt64) (start_index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.get_next_do_cmd.body fp this start_index cmd
  PMem.leave fp
  return r

end Vehicle_lib
