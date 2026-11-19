import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AC_AttitudeControl: the accessors of `AC_AttitudeControl.h`, `AC_AttitudeControl_Multi.h`, `AC_PosControl.h`

Each accessor returns the address of a member (`this + k`, the offsets of clang's layout); the roll trim is `0` in this
build.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AC_AttitudeControl

/-- C++ `AC_AttitudeControl::get_roll_trim_rad : float ()`: `cd_to_rad(get_roll_trim_cd())`, `0` in this build. -/
theorem AC_AttitudeControl.get_roll_trim_rad_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad this =
      pure (Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' this) := rfl

/-- Case: the trim converted by `cd_to_rad`. -/
theorem AC_AttitudeControl.get_roll_trim_rad_pure_eq (this : UInt64) :
    Id.run (Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' this) =
      Id.run (Vehicle_lib.cd_to_rad.pure' (Id.run (Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure' this))) := rfl

/-- Protocol: `0`. -/
theorem AC_AttitudeControl.get_roll_trim_rad_val (this : UInt64) :
    Id.run (Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' this) = Binary32.ofBits 0x00000000 := by
  unfold Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure'
  decide +kernel

/-- C++ `AC_AttitudeControl::get_att_target_euler_rad : const Vector3f &() const`, `<scratch space>:331-?`. -/
theorem AC_AttitudeControl.get_att_target_euler_rad_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_att_target_euler_rad this = pure (Vehicle_lib.AC_AttitudeControl.get_att_target_euler_rad.pure' this) := rfl

/-- Case: the member's address `this + 116`. -/
theorem AC_AttitudeControl.get_att_target_euler_rad_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_att_target_euler_rad.pure' this) = this + 116 := rfl

/-- Meaning: the address `this + 116` as a number, when it does not wrap. -/
theorem AC_AttitudeControl.get_att_target_euler_rad_toNat {this : UInt64} (h : this.toNat + 116 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl.get_att_target_euler_rad.pure' this)).toNat = this.toNat + 116 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_vel_desired_NED_ms : const Vector3f &() const`, `AP_Common.h:397-?`. -/
theorem AC_PosControl.get_vel_desired_NED_ms_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_vel_desired_NED_ms this = pure (Vehicle_lib.AC_PosControl.get_vel_desired_NED_ms.pure' this) := rfl

/-- Case: the member's address `this + 788`. -/
theorem AC_PosControl.get_vel_desired_NED_ms_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_vel_desired_NED_ms.pure' this) = this + 788 := rfl

/-- Meaning: the address `this + 788` as a number, when it does not wrap. -/
theorem AC_PosControl.get_vel_desired_NED_ms_toNat {this : UInt64} (h : this.toNat + 788 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_vel_desired_NED_ms.pure' this)).toNat = this.toNat + 788 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::NE_get_pos_p : AC_P_2D &()`, `AP_Common.h:552-?`. -/
theorem AC_PosControl.NE_get_pos_p_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.NE_get_pos_p this = pure (Vehicle_lib.AC_PosControl.NE_get_pos_p.pure' this) := rfl

/-- Case: the member's address `this + 36`. -/
theorem AC_PosControl.NE_get_pos_p_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.NE_get_pos_p.pure' this) = this + 36 := rfl

/-- Meaning: the address `this + 36` as a number, when it does not wrap. -/
theorem AC_PosControl.NE_get_pos_p_toNat {this : UInt64} (h : this.toNat + 36 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.NE_get_pos_p.pure' this)).toNat = this.toNat + 36 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::D_get_pos_p : AC_P_1D &()`, `AP_Common.h:555-?`. -/
theorem AC_PosControl.D_get_pos_p_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.D_get_pos_p this = pure (Vehicle_lib.AC_PosControl.D_get_pos_p.pure' this) := rfl

/-- Case: the member's address `this + 60`. -/
theorem AC_PosControl.D_get_pos_p_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.D_get_pos_p.pure' this) = this + 60 := rfl

/-- Meaning: the address `this + 60` as a number, when it does not wrap. -/
theorem AC_PosControl.D_get_pos_p_toNat {this : UInt64} (h : this.toNat + 60 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.D_get_pos_p.pure' this)).toNat = this.toNat + 60 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::D_get_vel_pid : AC_PID_Basic &()`, `AP_Common.h:561-?`. -/
theorem AC_PosControl.D_get_vel_pid_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.D_get_vel_pid this = pure (Vehicle_lib.AC_PosControl.D_get_vel_pid.pure' this) := rfl

/-- Case: the member's address `this + 264`. -/
theorem AC_PosControl.D_get_vel_pid_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.D_get_vel_pid.pure' this) = this + 264 := rfl

/-- Meaning: the address `this + 264` as a number, when it does not wrap. -/
theorem AC_PosControl.D_get_vel_pid_toNat {this : UInt64} (h : this.toNat + 264 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.D_get_vel_pid.pure' this)).toNat = this.toNat + 264 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_AttitudeControl::get_angle_pitch_p : AC_P &()`, `AC_AttitudeControl.h:81-?`. -/
theorem AC_AttitudeControl.get_angle_pitch_p_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_angle_pitch_p this = pure (Vehicle_lib.AC_AttitudeControl.get_angle_pitch_p.pure' this) := rfl

/-- Case: the member's address `this + 48`. -/
theorem AC_AttitudeControl.get_angle_pitch_p_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_pitch_p.pure' this) = this + 48 := rfl

/-- Meaning: the address `this + 48` as a number, when it does not wrap. -/
theorem AC_AttitudeControl.get_angle_pitch_p_toNat {this : UInt64} (h : this.toNat + 48 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_pitch_p.pure' this)).toNat = this.toNat + 48 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_AttitudeControl::get_angle_roll_p : AC_P &()`, `AC_AttitudeControl.h:80-?`. -/
theorem AC_AttitudeControl.get_angle_roll_p_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_angle_roll_p this = pure (Vehicle_lib.AC_AttitudeControl.get_angle_roll_p.pure' this) := rfl

/-- Case: the member's address `this + 40`. -/
theorem AC_AttitudeControl.get_angle_roll_p_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_roll_p.pure' this) = this + 40 := rfl

/-- Meaning: the address `this + 40` as a number, when it does not wrap. -/
theorem AC_AttitudeControl.get_angle_roll_p_toNat {this : UInt64} (h : this.toNat + 40 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_roll_p.pure' this)).toNat = this.toNat + 40 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_AttitudeControl::get_angle_yaw_p : AC_P &()`, `AC_AttitudeControl.h:82-?`. -/
theorem AC_AttitudeControl.get_angle_yaw_p_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_angle_yaw_p this = pure (Vehicle_lib.AC_AttitudeControl.get_angle_yaw_p.pure' this) := rfl

/-- Case: the member's address `this + 56`. -/
theorem AC_AttitudeControl.get_angle_yaw_p_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_yaw_p.pure' this) = this + 56 := rfl

/-- Meaning: the address `this + 56` as a number, when it does not wrap. -/
theorem AC_AttitudeControl.get_angle_yaw_p_toNat {this : UInt64} (h : this.toNat + 56 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl.get_angle_yaw_p.pure' this)).toNat = this.toNat + 56 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_pos_offset_NED_m : const Vector3p &() const`, `AP_Common.h:485-?`. -/
theorem AC_PosControl.get_pos_offset_NED_m_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_pos_offset_NED_m this = pure (Vehicle_lib.AC_PosControl.get_pos_offset_NED_m.pure' this) := rfl

/-- Case: the member's address `this + 888`. -/
theorem AC_PosControl.get_pos_offset_NED_m_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_pos_offset_NED_m.pure' this) = this + 888 := rfl

/-- Meaning: the address `this + 888` as a number, when it does not wrap. -/
theorem AC_PosControl.get_pos_offset_NED_m_toNat {this : UInt64} (h : this.toNat + 888 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_pos_offset_NED_m.pure' this)).toNat = this.toNat + 888 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_pos_estimate_NED_m : const Vector3p &() const`, `AP_Common.h:313-?`. -/
theorem AC_PosControl.get_pos_estimate_NED_m_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_pos_estimate_NED_m this = pure (Vehicle_lib.AC_PosControl.get_pos_estimate_NED_m.pure' this) := rfl

/-- Case: the member's address `this + 704`. -/
theorem AC_PosControl.get_pos_estimate_NED_m_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_pos_estimate_NED_m.pure' this) = this + 704 := rfl

/-- Meaning: the address `this + 704` as a number, when it does not wrap. -/
theorem AC_PosControl.get_pos_estimate_NED_m_toNat {this : UInt64} (h : this.toNat + 704 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_pos_estimate_NED_m.pure' this)).toNat = this.toNat + 704 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_vel_estimate_NED_ms : const Vector3f &() const`, `AP_Common.h:377-?`. -/
theorem AC_PosControl.get_vel_estimate_NED_ms_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_vel_estimate_NED_ms this = pure (Vehicle_lib.AC_PosControl.get_vel_estimate_NED_ms.pure' this) := rfl

/-- Case: the member's address `this + 776`. -/
theorem AC_PosControl.get_vel_estimate_NED_ms_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_vel_estimate_NED_ms.pure' this) = this + 776 := rfl

/-- Meaning: the address `this + 776` as a number, when it does not wrap. -/
theorem AC_PosControl.get_vel_estimate_NED_ms_toNat {this : UInt64} (h : this.toNat + 776 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_vel_estimate_NED_ms.pure' this)).toNat = this.toNat + 776 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_pos_desired_NED_m : const Vector3p &() const`, `AP_Common.h:325-?`. -/
theorem AC_PosControl.get_pos_desired_NED_m_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_pos_desired_NED_m this = pure (Vehicle_lib.AC_PosControl.get_pos_desired_NED_m.pure' this) := rfl

/-- Case: the member's address `this + 728`. -/
theorem AC_PosControl.get_pos_desired_NED_m_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_pos_desired_NED_m.pure' this) = this + 728 := rfl

/-- Meaning: the address `this + 728` as a number, when it does not wrap. -/
theorem AC_PosControl.get_pos_desired_NED_m_toNat {this : UInt64} (h : this.toNat + 728 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_pos_desired_NED_m.pure' this)).toNat = this.toNat + 728 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_AttitudeControl::get_attitude_target_ang_vel : const Vector3f &() const`, `<scratch space>:338-?`. -/
theorem AC_AttitudeControl.get_attitude_target_ang_vel_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_attitude_target_ang_vel this = pure (Vehicle_lib.AC_AttitudeControl.get_attitude_target_ang_vel.pure' this) := rfl

/-- Case: the member's address `this + 156`. -/
theorem AC_AttitudeControl.get_attitude_target_ang_vel_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_attitude_target_ang_vel.pure' this) = this + 156 := rfl

/-- Meaning: the address `this + 156` as a number, when it does not wrap. -/
theorem AC_AttitudeControl.get_attitude_target_ang_vel_toNat {this : UInt64} (h : this.toNat + 156 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl.get_attitude_target_ang_vel.pure' this)).toNat = this.toNat + 156 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::get_accel_target_NED_mss : const Vector3f &() const`, `AP_Common.h:426-?`. -/
theorem AC_PosControl.get_accel_target_NED_mss_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.get_accel_target_NED_mss this = pure (Vehicle_lib.AC_PosControl.get_accel_target_NED_mss.pure' this) := rfl

/-- Case: the member's address `this + 824`. -/
theorem AC_PosControl.get_accel_target_NED_mss_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.get_accel_target_NED_mss.pure' this) = this + 824 := rfl

/-- Meaning: the address `this + 824` as a number, when it does not wrap. -/
theorem AC_PosControl.get_accel_target_NED_mss_toNat {this : UInt64} (h : this.toNat + 824 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.get_accel_target_NED_mss.pure' this)).toNat = this.toNat + 824 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_AttitudeControl::get_roll_trim_cd : float ()`, `<scratch space>:483-?`. -/
theorem AC_AttitudeControl.get_roll_trim_cd_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd this = pure (Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem AC_AttitudeControl.get_roll_trim_cd_val (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure' this) = Binary32.ofBits 0x00000000 := rfl

/-- C++ `AC_AttitudeControl_Multi::get_rate_yaw_pid : const AC_PID &() const`, `AC_AttitudeControl_Multi.h:55-?`. -/
theorem AC_AttitudeControl_Multi.get_rate_yaw_pid'2_eq (this : UInt64) :
    Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid'2 this = pure (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid'2.pure' this) := rfl

/-- Case: the member's address `this + 856`. -/
theorem AC_AttitudeControl_Multi.get_rate_yaw_pid'2_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid'2.pure' this) = this + 856 := rfl

/-- Meaning: the address `this + 856` as a number, when it does not wrap. -/
theorem AC_AttitudeControl_Multi.get_rate_yaw_pid'2_toNat {this : UInt64} (h : this.toNat + 856 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid'2.pure' this)).toNat = this.toNat + 856 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PosControl::NE_get_vel_pid : AC_PID_2D &()`, `AP_Common.h:558-?`. -/
theorem AC_PosControl.NE_get_vel_pid_eq (this : UInt64) :
    Vehicle_lib.AC_PosControl.NE_get_vel_pid this = pure (Vehicle_lib.AC_PosControl.NE_get_vel_pid.pure' this) := rfl

/-- Case: the member's address `this + 84`. -/
theorem AC_PosControl.NE_get_vel_pid_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PosControl.NE_get_vel_pid.pure' this) = this + 84 := rfl

/-- Meaning: the address `this + 84` as a number, when it does not wrap. -/
theorem AC_PosControl.NE_get_vel_pid_toNat {this : UInt64} (h : this.toNat + 84 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PosControl.NE_get_vel_pid.pure' this)).toNat = this.toNat + 84 :=
  Corpus.Int.toNat_add_of_lt h

end Corpus.AC_AttitudeControl
