import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# GCS_MAVLink: `GCS.h`, `GCS_MAVLink.{h,cpp}`, `GCS_Common.cpp`, `protocol.h`, `MissionItemProtocol*.h`, and ArduCopter's `GCS_MAVLink_Copter.{h,cpp}`

The MAVLink side's pure leaves: tables over command and message ids, the channel test (a signed comparison, FINDINGS
F19), the saturated target field, the location-parameter conversion, the capability words, member accessors and
constant answers.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.GCS_MAVLink

/-! ## Parameter types and channels (`GCS_MAVLink.{h,cpp}`) -/

theorem GCS_MAVLINK.mav_param_type_eq (t : UInt32) :
    Vehicle_lib.GCS_MAVLINK.mav_param_type t = pure (Vehicle_lib.GCS_MAVLINK.mav_param_type.pure' t) := rfl

/-- Protocol: `AP_PARAM_INT8` (1) is `MAV_PARAM_TYPE_INT8` (2), `AP_PARAM_INT16` (2) is `INT16` (4), `AP_PARAM_INT32`
(3) is `INT32` (6), anything else `REAL32` (9) (`GCS_MAVLink.cpp:119-132`). -/
theorem GCS_MAVLINK.mav_param_type_table (t : UInt32) :
    Id.run (Vehicle_lib.GCS_MAVLINK.mav_param_type.pure' t) =
      if t = 1 then 2 else if t = 2 then 4 else if t = 3 then 6 else 9 := by
  have inj : ∀ a b : UInt32, (a.toInt32 == b.toInt32) = (a == b) := fun a b => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← Int32.toBitVec_inj, UInt32.toBitVec_toInt32,
      UInt32.toBitVec_toInt32, UInt32.toBitVec_inj]
  unfold Vehicle_lib.GCS_MAVLINK.mav_param_type.pure'
  simp only [Id.run, inj, beq_iff_eq]
  split_ifs <;> rfl

/-- Range: one of the four MAVLink types. -/
theorem GCS_MAVLINK.mav_param_type_mem (t : UInt32) :
    Id.run (Vehicle_lib.GCS_MAVLINK.mav_param_type.pure' t) ∈ ([2, 4, 6, 9] : List UInt32) := by
  rw [GCS_MAVLINK.mav_param_type_table]; split_ifs <;> simp

theorem valid_channel_eq (chan : UInt32) :
    Vehicle_lib.valid_channel chan = pure (Vehicle_lib.valid_channel.pure' chan) := rfl

/-- Protocol: `valid_channel` compares the channel as a signed `int` against 16 (`GCS_MAVLink.h:62-65`): every value
below 16, and every value from `2^31` on (negative as an `int`), passes (FINDINGS F19). -/
theorem valid_channel_table (chan : UInt32) :
    Id.run (Vehicle_lib.valid_channel.pure' chan) = true ↔ chan.toNat < 16 ∨ 2 ^ 31 ≤ chan.toNat := by
  unfold Vehicle_lib.valid_channel.pure'
  simp only [Id.run, decide_eq_true_eq]
  exact Corpus.Int.lt_u32 chan 16 (by decide)

/-- Case: the channels `0 … 15` are valid. -/
theorem valid_channel_of_lt {chan : UInt32} (h : chan.toNat < 16) :
    Id.run (Vehicle_lib.valid_channel.pure' chan) = true :=
  (valid_channel_table chan).2 (Or.inl h)

/-! ## `protocol.h` -/

theorem mavlink_msg_target_field_eq (t : UInt32) :
    Vehicle_lib.mavlink_msg_target_field t = pure (Vehicle_lib.mavlink_msg_target_field.pure' t) := rfl

/-- Meaning: the target system saturated to `255` (`protocol.h:52-55`). -/
theorem mavlink_msg_target_field_toNat (t : UInt32) :
    (Id.run (Vehicle_lib.mavlink_msg_target_field.pure' t)).toNat = min t.toNat 255 := by
  have key : ∀ u : UInt8, Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 u))) = u := by decide +kernel
  unfold Vehicle_lib.mavlink_msg_target_field.pure'
  simp only [Id.run]
  split
  · next h =>
    have : 255 < t.toNat := by
      simp only [decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt] at h; exact h
    show (Int8.toUInt8 (Int32.toInt8 255)).toNat = _
    rw [show (Int8.toUInt8 (Int32.toInt8 255)).toNat = 255 from rfl]; omega
  · next h =>
    have : t.toNat ≤ 255 := by
      simp only [decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, Bool.not_eq_true, decide_eq_false_iff_not,
        Nat.not_lt] at h; exact h
    show (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (UInt32.toUInt8 t))))).toNat = _
    rw [key, UInt32.toNat_toUInt8]; omega

/-- Range: at most `255`. -/
theorem mavlink_msg_target_field_le (t : UInt32) :
    (Id.run (Vehicle_lib.mavlink_msg_target_field.pure' t)).toNat ≤ 255 := by
  rw [mavlink_msg_target_field_toNat]; omega

/-! ## Commands (`GCS_Common.cpp`, `GCS_MAVLink_Copter.cpp`) -/

theorem GCS_MAVLINK.command_long_stores_location_eq (c : UInt32) :
    Vehicle_lib.GCS_MAVLINK.command_long_stores_location c =
      pure (Vehicle_lib.GCS_MAVLINK.command_long_stores_location.pure' c) := rfl

/-- Protocol: the `COMMAND_LONG`s whose parameters 5–7 are a location (`GCS_Common.cpp:5241-5257`). -/
theorem GCS_MAVLINK.command_long_stores_location_table (c : UInt32) :
    Id.run (Vehicle_lib.GCS_MAVLINK.command_long_stores_location.pure' c) = true ↔
      c.toNat ∈ [179, 201, 195, 192, 43003, 611] := by
  unfold Vehicle_lib.GCS_MAVLINK.command_long_stores_location.pure'; table_tac32

theorem GCS_MAVLINK_Copter.command_int_only_eq (this : UInt64) (c : UInt32) :
    Vehicle_lib.GCS_MAVLINK_Copter.command_int_only this c =
      pure (Vehicle_lib.GCS_MAVLINK_Copter.command_int_only.pure' this c) := rfl

/-- Protocol: only `NAV_VTOL_TAKEOFF` (84) must come as `COMMAND_INT` (`GCS_MAVLink_Copter.cpp:602-610`). -/
theorem GCS_MAVLINK_Copter.command_int_only_table (this : UInt64) (c : UInt32) :
    Id.run (Vehicle_lib.GCS_MAVLINK_Copter.command_int_only.pure' this c) = true ↔ c.toNat ∈ [84] := by
  unfold Vehicle_lib.GCS_MAVLINK_Copter.command_int_only.pure'; table_tac32

theorem GCS_MAVLINK.should_send_message_in_delay_callback_eq (this : UInt64) (id : UInt8) :
    Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback this id =
      pure (Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback.pure' this id) := rfl

/-- Protocol: the messages sent from the delay callback (`GCS_Common.cpp:1233-1251`), by `ap_message` id. -/
theorem GCS_MAVLINK.should_send_message_in_delay_callback_table (this : UInt64) (id : UInt8) :
    Id.run (Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback.pure' this id) = true ↔
      id.toNat ∈ [31, 0, 73] := by
  unfold Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback.pure'; table_tac

theorem GCS_MAVLINK.capabilities_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK.capabilities this = pure (Vehicle_lib.GCS_MAVLINK.capabilities.pure' this) := rfl

/-- Protocol: the capability bits (`GCS_Common.cpp:7587-7624`): `MISSION_FLOAT` (2), `COMMAND_INT`... as the code
folds them, `12290`. -/
theorem GCS_MAVLINK.capabilities_val (this : UInt64) :
    Id.run (Vehicle_lib.GCS_MAVLINK.capabilities.pure' this) = 12290 := rfl

theorem GCS_MAVLINK_Copter.capabilities_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK_Copter.capabilities this =
      pure (Vehicle_lib.GCS_MAVLINK_Copter.capabilities.pure' this) := rfl

/-- Protocol: the copter's capability bits, the common ones included (`GCS_MAVLink_Copter.cpp:1230-1243`), `14799`. -/
theorem GCS_MAVLINK_Copter.capabilities_val (this : UInt64) :
    Id.run (Vehicle_lib.GCS_MAVLINK_Copter.capabilities.pure' this) = 14799 := by
  unfold Vehicle_lib.GCS_MAVLINK_Copter.capabilities.pure' Vehicle_lib.GCS_MAVLINK.capabilities.pure'
  decide

theorem convert_COMMAND_LONG_loc_param_eq (p : Binary32) (st : Bool) :
    Vehicle_lib.convert_COMMAND_LONG_loc_param p st = pure (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p st) :=
  rfl

/-- Case: a NaN parameter converts to `0` (`GCS_Common.cpp:5335-5346`). -/
theorem convert_COMMAND_LONG_loc_param_of_isNaN {p : Binary32} (st : Bool) (h : Binary32.isNaN p = true) :
    Id.run (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p st) = 0 := by
  unfold Vehicle_lib.convert_COMMAND_LONG_loc_param.pure'; simp only [Id.run, h, ite_true]; rfl

/-- Case: a location parameter is scaled by `1e7` (the word `0x4b189680`) and truncated. -/
theorem convert_COMMAND_LONG_loc_param_of_stores {p : Binary32} (h : Binary32.isNaN p = false) :
    Id.run (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p true) =
      Binary32.toInt32 (p * Binary32.ofBits 0x4b189680) := by
  have e : Binary64.toBinary32 (Binary64.ofBits 0x416312d000000000) = Binary32.ofBits 0x4b189680 := by decide +kernel
  unfold Vehicle_lib.convert_COMMAND_LONG_loc_param.pure'; simp only [Id.run, h, e]; rfl

/-- Case: any other parameter is truncated. -/
theorem convert_COMMAND_LONG_loc_param_of_not_stores {p : Binary32} (h : Binary32.isNaN p = false) :
    Id.run (Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' p false) = Binary32.toInt32 p := by
  unfold Vehicle_lib.convert_COMMAND_LONG_loc_param.pure'; simp only [Id.run, h]; rfl

/-! ## Accessors and constant answers (`GCS.h`, `MissionItemProtocol*.h`, `GCS_MAVLink_Copter.h`, `GCS_Common.cpp`) -/

/-- C++ `GCS_MAVLINK::channel_status : mavlink_status_t *()`, `GCS.h:190-?`. -/
theorem GCS_MAVLINK.channel_status_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK.channel_status this = pure (Vehicle_lib.GCS_MAVLINK.channel_status.pure' this) := rfl

/-- Case: the member's address `this + 408`. -/
theorem GCS_MAVLINK.channel_status_pure_eq (this : UInt64) : Id.run (Vehicle_lib.GCS_MAVLINK.channel_status.pure' this) = this + 408 := rfl

/-- Meaning: the address `this + 408` as a number, when it does not wrap. -/
theorem GCS_MAVLINK.channel_status_toNat {this : UInt64} (h : this.toNat + 408 < 2 ^ 64) :
    (Id.run (Vehicle_lib.GCS_MAVLINK.channel_status.pure' this)).toNat = this.toNat + 408 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `GCS_MAVLINK::channel_buffer : mavlink_message_t *()`, `GCS.h:189-?`. -/
theorem GCS_MAVLINK.channel_buffer_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK.channel_buffer this = pure (Vehicle_lib.GCS_MAVLINK.channel_buffer.pure' this) := rfl

/-- Case: the member's address `this + 104`. -/
theorem GCS_MAVLINK.channel_buffer_pure_eq (this : UInt64) : Id.run (Vehicle_lib.GCS_MAVLINK.channel_buffer.pure' this) = this + 104 := rfl

/-- Meaning: the address `this + 104` as a number, when it does not wrap. -/
theorem GCS_MAVLINK.channel_buffer_toNat {this : UInt64} (h : this.toNat + 104 < 2 ^ 64) :
    (Id.run (Vehicle_lib.GCS_MAVLINK.channel_buffer.pure' this)).toNat = this.toNat + 104 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `GCS::statustext_queue : StatusTextQueue &()`, `sitl.h:1189-1191`. -/
theorem GCS.statustext_queue_eq (this : UInt64) :
    Vehicle_lib.GCS.statustext_queue this = pure (Vehicle_lib.GCS.statustext_queue.pure' this) := rfl

/-- Case: the member's address `this + 440`. -/
theorem GCS.statustext_queue_pure_eq (this : UInt64) : Id.run (Vehicle_lib.GCS.statustext_queue.pure' this) = this + 440 := rfl

/-- Meaning: the address `this + 440` as a number, when it does not wrap. -/
theorem GCS.statustext_queue_toNat {this : UInt64} (h : this.toNat + 440 < 2 ^ 64) :
    (Id.run (Vehicle_lib.GCS.statustext_queue.pure' this)).toNat = this.toNat + 440 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `MissionItemProtocol_Waypoints::mission_type : MAV_MISSION_TYPE () const`, `MissionItemProtocol_Waypoints.h:12-14`. -/
theorem MissionItemProtocol_Waypoints.mission_type_eq (this : UInt64) :
    Vehicle_lib.MissionItemProtocol_Waypoints.mission_type this = pure (Vehicle_lib.MissionItemProtocol_Waypoints.mission_type.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem MissionItemProtocol_Waypoints.mission_type_val (this : UInt64) : Id.run (Vehicle_lib.MissionItemProtocol_Waypoints.mission_type.pure' this) = 0 := rfl

/-- C++ `MissionItemProtocol::allocate_update_resources : MAV_MISSION_RESULT ()`, `AP_Common.h:115-117`. -/
theorem MissionItemProtocol.allocate_update_resources_eq (this : UInt64) :
    Vehicle_lib.MissionItemProtocol.allocate_update_resources this = pure (Vehicle_lib.MissionItemProtocol.allocate_update_resources.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem MissionItemProtocol.allocate_update_resources_val (this : UInt64) : Id.run (Vehicle_lib.MissionItemProtocol.allocate_update_resources.pure' this) = 0 := rfl

/-- C++ `MissionItemProtocol_Waypoints::next_item_ap_message_id : ap_message () const`, `MissionItemProtocol_Waypoints.h:37-39`. -/
theorem MissionItemProtocol_Waypoints.next_item_ap_message_id_eq (this : UInt64) :
    Vehicle_lib.MissionItemProtocol_Waypoints.next_item_ap_message_id this = pure (Vehicle_lib.MissionItemProtocol_Waypoints.next_item_ap_message_id.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem MissionItemProtocol_Waypoints.next_item_ap_message_id_val (this : UInt64) : Id.run (Vehicle_lib.MissionItemProtocol_Waypoints.next_item_ap_message_id.pure' this) = 28 := rfl

/-- C++ `MissionItemProtocol::allocate_receive_resources : MAV_MISSION_RESULT (const uint16_t)`, `MissionItemProtocol.h:112-114`. -/
theorem MissionItemProtocol.allocate_receive_resources_eq (this : UInt64) (count : UInt16) :
    Vehicle_lib.MissionItemProtocol.allocate_receive_resources this count = pure (Vehicle_lib.MissionItemProtocol.allocate_receive_resources.pure' this count) := rfl

/-- Protocol: the constant answer. -/
theorem MissionItemProtocol.allocate_receive_resources_val (this : UInt64) (count : UInt16) : Id.run (Vehicle_lib.MissionItemProtocol.allocate_receive_resources.pure' this count) = 0 := rfl

/-- C++ `GCS::min_status_for_gps_healthy : AP_GPS_FixType () const`, `AP_Common.h:1365-1368`. -/
theorem GCS.min_status_for_gps_healthy_eq (this : UInt64) :
    Vehicle_lib.GCS.min_status_for_gps_healthy this = pure (Vehicle_lib.GCS.min_status_for_gps_healthy.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem GCS.min_status_for_gps_healthy_val (this : UInt64) : Id.run (Vehicle_lib.GCS.min_status_for_gps_healthy.pure' this) = 1 := rfl

/-- C++ `GCS_MAVLINK_Copter::vtol_state : MAV_VTOL_STATE () const`, `GCS_MAVLink_Copter.h:50-?`. -/
theorem GCS_MAVLINK_Copter.vtol_state_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK_Copter.vtol_state this = pure (Vehicle_lib.GCS_MAVLINK_Copter.vtol_state.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem GCS_MAVLINK_Copter.vtol_state_val (this : UInt64) : Id.run (Vehicle_lib.GCS_MAVLINK_Copter.vtol_state.pure' this) = 3 := rfl

/-- C++ `camera_command_result_param2 : uint8_t (const __mavlink_command_long_t &, MAV_RESULT)`, `GCS_Common.cpp:5262-5271`. -/
theorem camera_command_result_param2'mavlink_command_long_t_eq (packet : UInt64) (result : UInt32) :
    Vehicle_lib.camera_command_result_param2'mavlink_command_long_t packet result = pure (Vehicle_lib.camera_command_result_param2'mavlink_command_long_t.pure' packet result) := rfl

/-- Protocol: the constant answer. -/
theorem camera_command_result_param2'mavlink_command_long_t_val (packet : UInt64) (result : UInt32) : Id.run (Vehicle_lib.camera_command_result_param2'mavlink_command_long_t.pure' packet result) = 0 := rfl

/-- C++ `camera_command_result_param2 : uint8_t (const __mavlink_command_int_t &, MAV_RESULT)`, `GCS_Common.cpp:5262-5271`. -/
theorem camera_command_result_param2'mavlink_command_int_t_eq (packet : UInt64) (result : UInt32) :
    Vehicle_lib.camera_command_result_param2'mavlink_command_int_t packet result = pure (Vehicle_lib.camera_command_result_param2'mavlink_command_int_t.pure' packet result) := rfl

/-- Protocol: the constant answer. -/
theorem camera_command_result_param2'mavlink_command_int_t_val (packet : UInt64) (result : UInt32) : Id.run (Vehicle_lib.camera_command_result_param2'mavlink_command_int_t.pure' packet result) = 0 := rfl

/-- C++ `GCS_MAVLINK::persist_streamrates : bool () const`, `functor.h:544-?`. -/
theorem GCS_MAVLINK.persist_streamrates_eq (this : UInt64) :
    Vehicle_lib.GCS_MAVLINK.persist_streamrates this = pure (Vehicle_lib.GCS_MAVLINK.persist_streamrates.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem GCS_MAVLINK.persist_streamrates_val (this : UInt64) : Id.run (Vehicle_lib.GCS_MAVLINK.persist_streamrates.pure' this) = false := rfl

/-- C++ `GCS_Copter::min_loop_time_remaining_for_message_send_us : uint16_t () const`, `GCS.h:38-40`. -/
theorem GCS_Copter.min_loop_time_remaining_for_message_send_us_eq (this : UInt64) :
    Vehicle_lib.GCS_Copter.min_loop_time_remaining_for_message_send_us this = pure (Vehicle_lib.GCS_Copter.min_loop_time_remaining_for_message_send_us.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem GCS_Copter.min_loop_time_remaining_for_message_send_us_val (this : UInt64) : Id.run (Vehicle_lib.GCS_Copter.min_loop_time_remaining_for_message_send_us.pure' this) = 250 := rfl

end Corpus.GCS_MAVLink
