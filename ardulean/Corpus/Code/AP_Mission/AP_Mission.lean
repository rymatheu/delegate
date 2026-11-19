import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AP_Mission: `AP_Mission.{h,cpp}`, `AP_Mission_Commands.cpp`

The command tables as membership statements over the MAVLink command id (`table_tac`, `Machine/Int.lean`), the
member accessor, and the `start_command_*` handlers this build compiles out (constant `false`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AP_Mission

/-! ## The command tables (`AP_Mission.cpp`) -/

theorem AP_Mission.stored_in_location_eq (id : UInt16) :
    Vehicle_lib.AP_Mission.stored_in_location id = pure (Vehicle_lib.AP_Mission.stored_in_location.pure' id) := rfl

/-- Protocol: the commands whose parameters are stored as a location (`AP_Mission.cpp:908-941`), by MAVLink id. -/
theorem AP_Mission.stored_in_location_table (id : UInt16) :
    Id.run (Vehicle_lib.AP_Mission.stored_in_location.pure' id) = true ↔
      id.toNat ∈ [16, 17, 18, 19, 21, 22, 30, 31, 82, 92, 179, 188, 189, 191, 195, 201, 84, 85, 94, 5001, 5002, 5003, 5004, 5000, 5100, 36] := by
  unfold Vehicle_lib.AP_Mission.stored_in_location.pure'; table_tac

theorem AP_Mission.cmd_has_location_eq (id : UInt16) :
    Vehicle_lib.AP_Mission.cmd_has_location id = pure (Vehicle_lib.AP_Mission.cmd_has_location.pure' id) := rfl

/-- Case: `cmd_has_location` is `stored_in_location` (`AP_Mission.cpp:3100-3103`). -/
theorem AP_Mission.cmd_has_location_pure_eq (id : UInt16) :
    Id.run (Vehicle_lib.AP_Mission.cmd_has_location.pure' id) =
      Id.run (Vehicle_lib.AP_Mission.stored_in_location.pure' id) := rfl

/-- Protocol: the same table. -/
theorem AP_Mission.cmd_has_location_table (id : UInt16) :
    Id.run (Vehicle_lib.AP_Mission.cmd_has_location.pure' id) = true ↔
      id.toNat ∈ [16, 17, 18, 19, 21, 22, 30, 31, 82, 92, 179, 188, 189, 191, 195, 201, 84, 85, 94, 5001, 5002, 5003, 5004, 5000, 5100, 36] := by
  rw [AP_Mission.cmd_has_location_pure_eq]; exact AP_Mission.stored_in_location_table id

theorem AP_Mission.is_landing_type_cmd_eq (this : UInt64) (id : UInt16) :
    Vehicle_lib.AP_Mission.is_landing_type_cmd this id =
      pure (Vehicle_lib.AP_Mission.is_landing_type_cmd.pure' this id) := rfl

/-- Protocol: the landing commands (`AP_Mission.cpp:2880-2890`): `NAV_LAND` (21), `NAV_VTOL_LAND` (85),
`DO_PARACHUTE` (208). -/
theorem AP_Mission.is_landing_type_cmd_table (this : UInt64) (id : UInt16) :
    Id.run (Vehicle_lib.AP_Mission.is_landing_type_cmd.pure' this id) = true ↔ id.toNat ∈ [21, 85, 208] := by
  unfold Vehicle_lib.AP_Mission.is_landing_type_cmd.pure'; table_tac

theorem AP_Mission.is_takeoff_type_cmd_eq (this : UInt64) (id : UInt16) :
    Vehicle_lib.AP_Mission.is_takeoff_type_cmd this id =
      pure (Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure' this id) := rfl

/-- Protocol: the takeoff commands (`AP_Mission.cpp:2893-2902`): `NAV_TAKEOFF` (22), `NAV_VTOL_TAKEOFF` (84). -/
theorem AP_Mission.is_takeoff_type_cmd_table (this : UInt64) (id : UInt16) :
    Id.run (Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure' this id) = true ↔ id.toNat ∈ [22, 84] := by
  unfold Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure'; table_tac

/-- Protocol: a takeoff command is stored as a location; a landing command other than `DO_PARACHUTE` too. -/
theorem AP_Mission.stored_in_location_of_takeoff (this : UInt64) (id : UInt16)
    (h : Id.run (Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure' this id) = true) :
    Id.run (Vehicle_lib.AP_Mission.stored_in_location.pure' id) = true := by
  rw [AP_Mission.is_takeoff_type_cmd_table] at h
  rw [AP_Mission.stored_in_location_table]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  omega

/-! ## Accessors and constant answers (`AP_Mission.h`, `AP_Mission_Commands.cpp`) -/

/-- C++ `AP_Mission::start_command_parachute : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:131-158`. -/
theorem AP_Mission.start_command_parachute_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_parachute this cmd = pure (Vehicle_lib.AP_Mission.start_command_parachute.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_parachute_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_parachute.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::start_command_do_scripting : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:187-201`. -/
theorem AP_Mission.start_command_do_scripting_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_do_scripting this cmd = pure (Vehicle_lib.AP_Mission.start_command_do_scripting.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_do_scripting_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_do_scripting.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::start_command_do_sprayer : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:167-185`. -/
theorem AP_Mission.start_command_do_sprayer_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_do_sprayer this cmd = pure (Vehicle_lib.AP_Mission.start_command_do_sprayer.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_do_sprayer_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_do_sprayer.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::start_command_do_gimbal_manager_pitchyaw : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:203-244`. -/
theorem AP_Mission.start_command_do_gimbal_manager_pitchyaw_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_do_gimbal_manager_pitchyaw this cmd = pure (Vehicle_lib.AP_Mission.start_command_do_gimbal_manager_pitchyaw.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_do_gimbal_manager_pitchyaw_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_do_gimbal_manager_pitchyaw.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::start_command_do_set_roi : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:246-263`. -/
theorem AP_Mission.start_command_do_set_roi_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_do_set_roi this cmd = pure (Vehicle_lib.AP_Mission.start_command_do_set_roi.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_do_set_roi_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_do_set_roi.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::start_command_do_set_roi_wpnext_offset : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:294-316`. -/
theorem AP_Mission.start_command_do_set_roi_wpnext_offset_eq (this : UInt64) (cmd : UInt64) :
    Vehicle_lib.AP_Mission.start_command_do_set_roi_wpnext_offset this cmd = pure (Vehicle_lib.AP_Mission.start_command_do_set_roi_wpnext_offset.pure' this cmd) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Mission.start_command_do_set_roi_wpnext_offset_val (this : UInt64) (cmd : UInt64) : Id.run (Vehicle_lib.AP_Mission.start_command_do_set_roi_wpnext_offset.pure' this cmd) = false := rfl

/-- C++ `AP_Mission::get_current_nav_cmd : const Mission_Command &() const`, `AP_Common.h:597-600`. -/
theorem AP_Mission.get_current_nav_cmd_eq (this : UInt64) :
    Vehicle_lib.AP_Mission.get_current_nav_cmd this = pure (Vehicle_lib.AP_Mission.get_current_nav_cmd.pure' this) := rfl

/-- Case: the member's address `this + 88`. -/
theorem AP_Mission.get_current_nav_cmd_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_Mission.get_current_nav_cmd.pure' this) = this + 88 := rfl

/-- Meaning: the address `this + 88` as a number, when it does not wrap. -/
theorem AP_Mission.get_current_nav_cmd_toNat {this : UInt64} (h : this.toNat + 88 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AP_Mission.get_current_nav_cmd.pure' this)).toNat = this.toNat + 88 :=
  Corpus.Int.toNat_add_of_lt h

end Corpus.AP_Mission
