import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AC_PID`, part 1 of 2. Sources: `libraries/AC_PID/AC_PID.cpp`, `libraries/AC_PID/AC_PID_2D.cpp`, `libraries/AC_PID/AC_P_2D.cpp`, `libraries/AC_PID/AC_PID_Basic.cpp`, `libraries/AC_PID/AC_P_1D.cpp`, `libraries/AC_PID/AC_P.h`, `libraries/AC_PID/AC_PID.h`, `libraries/AC_PID/AC_P_1D.h` and 2 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- `AC_PID.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_PID::kP : AP_Float &()`, `AP_Common.h:97-?`. -/
def AC_PID.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.kP.pure' this)

/-- C++ `AC_PID_Basic::reset_filter : void ()`, `AP_Common.h:41-?`. -/
def AC_PID_Basic.reset_filter (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 44) true
  return ()

/-- C++ `AC_PID_Basic::set_integrator : void (float)`, `AC_PID_Basic.cpp:180-183`. -/
def AC_PID_Basic.set_integrator (this : UInt64) (i : Binary32) : PMem.M Unit := do
  let mut i := i
  let t'1 ← AP_ParamT'float_4.operator_'3 (this + 16)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← constrain_value_line'float i t'1 t'3 (Int32.toUInt32 ((182 : Int32)))
  PMem.stF32 (this + 40) t'4
  return ()

/-- C++ `AC_PID::reset_filter : void ()`, `AP_Common.h:85-87`. -/
def AC_PID.reset_filter (this : UInt64) : PMem.M Unit := do
  PMem.stBits (this + 128) 0 1 (if true then (1 : UInt64) else 0)
  return ()

/-- C++ `AC_PID::set_integrator : void (float)`, `AC_PID.cpp:433-437`. -/
def AC_PID.set_integrator (this : UInt64) (integrator : Binary32) : PMem.M Unit := do
  let mut integrator := integrator
  PMem.stBits (this + 128) 1 1 (if true then (1 : UInt64) else 0)
  let t'1 ← AP_ParamT'float_4.operator_'3 (this + 16)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← constrain_value_line'float integrator t'1 t'3 (Int32.toUInt32 ((436 : Int32)))
  PMem.stF32 (this + 132) t'4
  return ()

/-- `AC_PID.ff` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.ff.pure' (this : UInt64) : Id UInt64 := do
  return (this + 12)

/-- C++ `AC_PID::ff : AP_Float &()`, `AP_Common.h:102-?`. -/
def AC_PID.ff (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.ff.pure' this)

/-- `AC_PID.filt_T_hz` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.filt_T_hz.pure' (this : UInt64) : Id UInt64 := do
  return (this + 24)

/-- C++ `AC_PID::filt_T_hz : AP_Float &()`, `AP_Common.h:103-?`. -/
def AC_PID.filt_T_hz (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.filt_T_hz.pure' this)

/-- `AC_PID.filt_E_hz` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.filt_E_hz.pure' (this : UInt64) : Id UInt64 := do
  return (this + 28)

/-- C++ `AC_PID::filt_E_hz : AP_Float &()`, `AP_Common.h:104-?`. -/
def AC_PID.filt_E_hz (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.filt_E_hz.pure' this)

/-- C++ `AC_PID_2D::reset_filter : void ()`, `AP_Common.h:44-?`. -/
def AC_PID_2D.reset_filter (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 60) true
  return ()

/-- C++ `AC_PID_2D::set_integrator : void (const Vector2f &)`, `AC_PID_2D.cpp:212-216`. -/
def AC_PID_2D.set_integrator (this : UInt64) (i : UInt64) : PMem.M Unit := do
  discard <| PMem.memcpy (this + 52) i 8
  discard <| pure ((this + 52))
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← Vector2'float.limit_length (this + 52) t'2
  discard <| pure (t'3)
  return ()

/-- `AC_PID_2D.ff` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID_2D.ff.pure' (this : UInt64) : Id UInt64 := do
  return (this + 12)

/-- C++ `AC_PID_2D::ff : AP_Float &()`, `AP_Common.h:53-?`. -/
def AC_PID_2D.ff (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID_2D.ff.pure' this)

/-- `AC_P_1D.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_P_1D.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_P_1D::kP : AP_Float &()`, `AC_P_1D.h:42-?`. -/
def AC_P_1D.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_P_1D.kP.pure' this)

/-- `AC_P_2D.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_P_2D.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_P_2D::kP : AP_Float &()`, `AC_P_2D.h:39-?`. -/
def AC_P_2D.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_P_2D.kP.pure' this)

/-- `AC_PID_Basic.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID_Basic.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_PID_Basic::kP : AP_Float &()`, `AP_Common.h:47-?`. -/
def AC_PID_Basic.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID_Basic.kP.pure' this)

/-- `AC_PID.kI` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.kI.pure' (this : UInt64) : Id UInt64 := do
  return (this + 4)

/-- C++ `AC_PID::kI : AP_Float &()`, `AP_Common.h:98-?`. -/
def AC_PID.kI (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.kI.pure' this)

/-- `AC_P.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_P.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_P::kP : AP_Float &()`, `AP_Common.h:51-?`. -/
def AC_P.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_P.kP.pure' this)

/-- `AC_PID.kD` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.kD.pure' (this : UInt64) : Id UInt64 := do
  return (this + 8)

/-- C++ `AC_PID::kD : AP_Float &()`, `AP_Common.h:99-?`. -/
def AC_PID.kD (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.kD.pure' this)

/-- C++ `AC_P_2D::set_error_max : void (float)`, `AC_P_2D.cpp:67-77`. -/
def AC_P_2D.set_error_max.body (fp : UInt64) (this : UInt64) (error_max : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) error_max
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 ← is_positive'float t'1
  if t'2 then
    let t'3 ← PMem.ldF32 (this + 12)
    let t'4 ← is_zero t'3
    if !t'4 then
      let t'5 ← MIN'float_float (this + 12) (fp + 0)
      let t'6 ← PMem.ldF32 t'5
      PMem.stF32 (this + 12) t'6
    else
      let t'7 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (this + 12) t'7
  return ()

def AC_P_2D.set_error_max (this : UInt64) (error_max : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_P_2D.set_error_max.body fp this error_max
  PMem.leave fp
  return r

/-- `AC_PID.get_pid_info` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.get_pid_info.pure' (this : UInt64) : Id UInt64 := do
  return (this + 156)

/-- C++ `AC_PID::get_pid_info : const AP_PIDInfo &() const`, `AP_Common.h:149-?`. -/
def AC_PID.get_pid_info (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID.get_pid_info.pure' this)

/-- C++ `AC_P_1D::get_error : float () const`, `AP_Common.h:44-?`. -/
def AC_P_1D.get_error (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 4)
  return t'1

/-- `AC_P_2D.get_error` as a pure function of its arguments (it reads and writes no memory). -/
def AC_P_2D.get_error.pure' (this : UInt64) : Id UInt64 := do
  return (this + 4)

/-- C++ `AC_P_2D::get_error : const Vector2f &() const`, `AP_Common.h:41-?`. -/
def AC_P_2D.get_error (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_P_2D.get_error.pure' this)

/-- C++ `AC_P::AC_P : void (const float &)`, `AC_P.h:24-28`. -/
def AC_P.AC_P (this : UInt64) (initial_p : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  let t'1 ← PMem.ldF32 initial_p
  PMem.stF32 (this + 4) t'1
  AP_Param.setup_object_defaults this (0x7d80 : UInt64) /- &AC_P::var_info -/
  return ()

/-- `AP_PIDInfo.AP_PIDInfo` as a pure function of its arguments (it reads and writes no memory). -/
def AP_PIDInfo.AP_PIDInfo.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_PIDInfo::AP_PIDInfo : void () noexcept`, `AP_PIDInfo.h:?-?`. -/
def AP_PIDInfo.AP_PIDInfo (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_PIDInfo.AP_PIDInfo.pure' this)

/-- `AC_PID.ac_pid_flags.ac_pid_flags` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.ac_pid_flags.ac_pid_flags.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AC_PID::ac_pid_flags::ac_pid_flags : void () noexcept`, `AP_Common.h:?-?`. -/
def AC_PID.ac_pid_flags.ac_pid_flags (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AC_PID.ac_pid_flags.ac_pid_flags.pure' this)

/-- C++ `AC_PID::AC_PID : void (float, float, float, float, float, float, float, float, float, float, float)`, `AC_PID.cpp:103-130`. -/
def AC_PID.AC_PID'2.body (fp : UInt64) (this : UInt64) (initial_p : Binary32) (initial_i : Binary32) (initial_d : Binary32) (initial_ff : Binary32) (initial_imax : Binary32) (initial_filt_T_hz : Binary32) (initial_filt_E_hz : Binary32) (initial_filt_D_hz : Binary32) (initial_srmax : Binary32) (initial_srtau : Binary32) (initial_dff : Binary32) : PMem.M Unit := do
  let mut initial_p := initial_p
  let mut initial_i := initial_i
  let mut initial_d := initial_d
  let mut initial_ff := initial_ff
  let mut initial_imax := initial_imax
  let mut initial_filt_T_hz := initial_filt_T_hz
  let mut initial_filt_E_hz := initial_filt_E_hz
  let mut initial_filt_D_hz := initial_filt_D_hz
  let mut initial_srmax := initial_srmax
  PMem.stF32 (fp + 0) initial_srtau
  let mut initial_dff := initial_dff
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AP_Param.AP_Param'2 (this + 36)
  AP_Param.AP_Param'2 (this + 40)
  AP_Param.AP_Param'2 (this + 44)
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 36)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 44)
  SlewLimiter.SlewLimiter (this + 48) t'1 t'2
  AC_PID.ac_pid_flags.ac_pid_flags (this + 128)
  AP_PIDInfo.AP_PIDInfo (this + 156)
  PMem.stF32 (this + 200) initial_p
  PMem.stF32 (this + 204) initial_i
  PMem.stF32 (this + 208) initial_d
  PMem.stF32 (this + 212) initial_ff
  PMem.stF32 (this + 216) initial_dff
  PMem.stF32 (this + 220) initial_imax
  PMem.stF32 (this + 224) initial_filt_T_hz
  PMem.stF32 (this + 228) initial_filt_E_hz
  PMem.stF32 (this + 232) initial_filt_D_hz
  PMem.stF32 (this + 236) initial_srmax
  AP_Param.setup_object_defaults this (0x5ec0 : UInt64) /- &AC_PID::var_info -/
  AP_ParamTBase'float_4.set (this + 44) (fp + 0)
  PMem.stBits (this + 128) 0 1 (if true then (1 : UInt64) else 0)
  let t'3 ← PMem.memset (this + 156) (0 : Int32) (44 : UInt64)
  discard <| pure (t'3)
  let t'4 := Int32.toInt8 ((1 : Int32))
  PMem.stI8 (this + 148) t'4
  return ()

def AC_PID.AC_PID'2 (this : UInt64) (initial_p : Binary32) (initial_i : Binary32) (initial_d : Binary32) (initial_ff : Binary32) (initial_imax : Binary32) (initial_filt_T_hz : Binary32) (initial_filt_E_hz : Binary32) (initial_filt_D_hz : Binary32) (initial_srmax : Binary32) (initial_srtau : Binary32) (initial_dff : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_PID.AC_PID'2.body fp this initial_p initial_i initial_d initial_ff initial_imax initial_filt_T_hz initial_filt_E_hz initial_filt_D_hz initial_srmax initial_srtau initial_dff
  PMem.leave fp
  return r

/-- C++ `AC_PID::AC_PID : void (const AC_PID::Defaults &)`, `AC_PID.h:44-58`. -/
def AC_PID.AC_PID (this : UInt64) (defaults : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 defaults
  let t'2 ← PMem.ldF32 (defaults + 4)
  let t'3 ← PMem.ldF32 (defaults + 8)
  let t'4 ← PMem.ldF32 (defaults + 12)
  let t'5 ← PMem.ldF32 (defaults + 16)
  let t'6 ← PMem.ldF32 (defaults + 20)
  let t'7 ← PMem.ldF32 (defaults + 24)
  let t'8 ← PMem.ldF32 (defaults + 28)
  let t'9 ← PMem.ldF32 (defaults + 32)
  let t'10 ← PMem.ldF32 (defaults + 36)
  let t'11 ← PMem.ldF32 (defaults + 40)
  AC_PID.AC_PID'2 this t'1 t'2 t'3 t'4 t'5 t'6 t'7 t'8 t'9 t'10 t'11
  return ()

/-- C++ `AC_P_2D::AC_P_2D : void (float)`, `AC_P_2D.cpp:16-21`. -/
def AC_P_2D.AC_P_2D (this : UInt64) (initial_p : Binary32) : PMem.M Unit := do
  let mut initial_p := initial_p
  AP_Param.AP_Param'2 (this + 0)
  Vector2'float.Vector2 (this + 4)
  PMem.stF32 (this + 20) initial_p
  AP_Param.setup_object_defaults this (0x6208 : UInt64) /- &AC_P_2D::var_info -/
  return ()

/-- C++ `AC_P_1D::AC_P_1D : void (float)`, `AC_P_1D.cpp:16-21`. -/
def AC_P_1D.AC_P_1D (this : UInt64) (initial_p : Binary32) : PMem.M Unit := do
  let mut initial_p := initial_p
  AP_Param.AP_Param'2 (this + 0)
  PMem.stF32 (this + 20) initial_p
  AP_Param.setup_object_defaults this (0x61b8 : UInt64) /- &AC_P_1D::var_info -/
  return ()

/-- C++ `AC_PID_2D::AC_PID_2D : void (float, float, float, float, float, float, float)`, `AC_PID_2D.cpp:51-65`. -/
def AC_PID_2D.AC_PID_2D (this : UInt64) (initial_kP : Binary32) (initial_kI : Binary32) (initial_kD : Binary32) (initial_kFF : Binary32) (initial_imax : Binary32) (initial_filt_E_hz : Binary32) (initial_filt_D_hz : Binary32) : PMem.M Unit := do
  let mut initial_kP := initial_kP
  let mut initial_kI := initial_kI
  let mut initial_kD := initial_kD
  let mut initial_kFF := initial_kFF
  let mut initial_imax := initial_imax
  let mut initial_filt_E_hz := initial_filt_E_hz
  let mut initial_filt_D_hz := initial_filt_D_hz
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  Vector2'float.Vector2 (this + 28)
  Vector2'float.Vector2 (this + 36)
  Vector2'float.Vector2 (this + 44)
  Vector2'float.Vector2 (this + 52)
  AP_PIDInfo.AP_PIDInfo (this + 64)
  AP_PIDInfo.AP_PIDInfo (this + 108)
  PMem.stF32 (this + 152) initial_kP
  PMem.stF32 (this + 156) initial_kI
  PMem.stF32 (this + 160) initial_kD
  PMem.stF32 (this + 164) initial_kFF
  PMem.stF32 (this + 168) initial_imax
  PMem.stF32 (this + 172) initial_filt_E_hz
  PMem.stF32 (this + 176) initial_filt_D_hz
  AP_Param.setup_object_defaults this (0x6398 : UInt64) /- &AC_PID_2D::var_info -/
  PMem.stB (this + 60) true
  return ()

/-- C++ `AC_PID_Basic::AC_PID_Basic : void (float, float, float, float, float, float, float)`, `AC_PID_Basic.cpp:53-67`. -/
def AC_PID_Basic.AC_PID_Basic (this : UInt64) (initial_p : Binary32) (initial_i : Binary32) (initial_d : Binary32) (initial_ff : Binary32) (initial_imax : Binary32) (initial_filt_E_hz : Binary32) (initial_filt_D_hz : Binary32) : PMem.M Unit := do
  let mut initial_p := initial_p
  let mut initial_i := initial_i
  let mut initial_d := initial_d
  let mut initial_ff := initial_ff
  let mut initial_imax := initial_imax
  let mut initial_filt_E_hz := initial_filt_E_hz
  let mut initial_filt_D_hz := initial_filt_D_hz
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_PIDInfo.AP_PIDInfo (this + 48)
  PMem.stF32 (this + 92) initial_p
  PMem.stF32 (this + 96) initial_i
  PMem.stF32 (this + 100) initial_d
  PMem.stF32 (this + 104) initial_ff
  PMem.stF32 (this + 108) initial_imax
  PMem.stF32 (this + 112) initial_filt_E_hz
  PMem.stF32 (this + 116) initial_filt_D_hz
  AP_Param.setup_object_defaults this (0x6258 : UInt64) /- &AC_PID_Basic::var_info -/
  PMem.stB (this + 44) true
  return ()

/-- C++ `AC_PID::get_ff : float () const`, `AC_PID.cpp:368-371`. -/
def AC_PID.get_ff (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 ((this + 156) + 24)
  let t'2 ← PMem.ldF32 ((this + 156) + 28)
  return (t'1 + t'2)

/-- C++ `AC_PID::reset_I : void ()`, `AC_PID.cpp:384-388`. -/
def AC_PID.reset_I (this : UInt64) : PMem.M Unit := do
  PMem.stBits (this + 128) 1 1 (if true then (1 : UInt64) else 0)
  let t'1 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 132) t'1
  return ()

/-- C++ `AC_PID::relax_integrator : void (float, float, float)`, `AC_PID.cpp:441-448`. -/
def AC_PID.relax_integrator (this : UInt64) (integrator : Binary32) (dt : Binary32) (time_constant : Binary32) : PMem.M Unit := do
  let mut integrator := integrator
  let mut dt := dt
  let mut time_constant := time_constant
  let t'1 ← AP_ParamT'float_4.operator_'3 (this + 16)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← constrain_value_line'float integrator t'1 t'3 (Int32.toUInt32 ((443 : Int32)))
  integrator := t'4
  let t'5 ← is_positive'float dt
  if t'5 then
    PMem.stBits (this + 128) 1 1 (if true then (1 : UInt64) else 0)
    let t'6 ← PMem.ldF32 (this + 132)
    let t'7 ← PMem.ldF32 (this + 132)
    let t'8 := (t'6 + ((integrator - t'7) * (dt / (dt + time_constant))))
    PMem.stF32 (this + 132) t'8
  return ()

/-- C++ `AC_PID_Basic::get_error : float () const`, `AP_Common.h:35-?`. -/
def AC_PID_Basic.get_error (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 32)
  return t'1

/-- C++ `AC_PID::imax : float () const`, `AP_Common.h:109-?`. -/
def AC_PID.imax (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 16)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_P_1D::update_all : float (postype_t &, postype_t)`, `AC_P_1D.cpp:26-42`. -/
def AC_P_1D.update_all (this : UInt64) (target : UInt64) (measurement : Binary64) : PMem.M Binary32 := do
  let mut measurement := measurement
  let t'1 ← PMem.ldF64 target
  let t'2 := Binary64.toBinary32 ((t'1 - measurement))
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← is_negative'float t'3
  let mut sc'7 := t'4
  if sc'7 then
    let t'5 ← PMem.ldF32 (this + 4)
    let t'6 ← PMem.ldF32 (this + 8)
    sc'7 := (decide (t'5 < t'6))
  if sc'7 then
    let t'8 ← PMem.ldF32 (this + 8)
    PMem.stF32 (this + 4) t'8
    let t'9 ← PMem.ldF32 (this + 4)
    let t'10 := (measurement + (Binary32.toBinary64 (t'9)))
    PMem.stF64 target t'10
  else
    let t'11 ← PMem.ldF32 (this + 12)
    let t'12 ← is_positive'float t'11
    let mut sc'15 := t'12
    if sc'15 then
      let t'13 ← PMem.ldF32 (this + 4)
      let t'14 ← PMem.ldF32 (this + 12)
      sc'15 := (decide (t'13 > t'14))
    if sc'15 then
      let t'16 ← PMem.ldF32 (this + 12)
      PMem.stF32 (this + 4) t'16
      let t'17 ← PMem.ldF32 (this + 4)
      let t'18 := (measurement + (Binary32.toBinary64 (t'17)))
      PMem.stF64 target t'18
  let t'19 ← PMem.ldF32 (this + 4)
  let t'20 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'21 ← PMem.ldF32 t'20
  let t'22 ← PMem.ldF32 (this + 16)
  let t'23 ← sqrt_controller t'19 t'21 t'22 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  return t'23

/-- C++ `AC_PID::set_imax : void (const float)`, `AP_Common.h:124-?`. -/
def AC_PID.set_imax.body (fp : UInt64) (this : UInt64) (v : Binary32) : PMem.M Unit := do
  let mut v := v
  PMem.stF32 (fp + 0) (Binary32.abs v)
  AP_ParamTBase'float_4.set (this + 16) (fp + 0)
  return ()

def AC_PID.set_imax (this : UInt64) (v : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_PID.set_imax.body fp this v
  PMem.leave fp
  return r

/-- C++ `AC_PID::get_i : float () const`, `AC_PID.cpp:358-361`. -/
def AC_PID.get_i (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 132)
  return t'1

/-- `AC_PID_2D.get_error` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID_2D.get_error.pure' (this : UInt64) : Id UInt64 := do
  return (this + 36)

/-- C++ `AC_PID_2D::get_error : const Vector2f &() const`, `AP_Common.h:38-?`. -/
def AC_PID_2D.get_error (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID_2D.get_error.pure' this)

/-- C++ `AC_P_2D::update_all : Vector2f (Vector2p &, const Vector2p &)`, `AC_P_2D.cpp:26-38`. -/
def AC_P_2D.update_all.body (fp : UInt64) (this : UInt64) (sret : UInt64) (target : UInt64) (measurement : UInt64) : PMem.M Unit := do
  Vector2'double.operator_ target (fp + 0) measurement
  let t'1 := (fp + 0)
  Vector2'double.tofloat t'1 (fp + 16)
  let t'2 := (fp + 16)
  discard <| PMem.memcpy (this + 4) t'2 8
  discard <| pure ((this + 4))
  let t'3 ← PMem.ldF32 (this + 12)
  let t'4 ← is_positive'float t'3
  let mut sc'7 := t'4
  if sc'7 then
    let t'5 ← PMem.ldF32 (this + 12)
    let t'6 ← Vector2'float.limit_length (this + 4) t'5
    sc'7 := t'6
  if sc'7 then
    Vector2'float.todouble (this + 4) (fp + 24)
    let t'8 := (fp + 24)
    Vector2'double.operator_'2 measurement (fp + 40) t'8
    let t'9 := (fp + 40)
    discard <| PMem.memcpy target t'9 16
    discard <| pure (target)
  let t'10 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'11 ← PMem.ldF32 t'10
  let t'12 ← PMem.ldF32 (this + 16)
  sqrt_controller'2 (fp + 56) (this + 4) t'11 t'12 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'13 := (fp + 56)
  Vector2'float.Vector2'3 sret t'13
  return ()

def AC_P_2D.update_all (this : UInt64) (sret : UInt64) (target : UInt64) (measurement : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← AC_P_2D.update_all.body fp this sret target measurement
  PMem.leave fp
  return r

/-- C++ `AC_PID_2D::update_i : void (float, const Vector2f &)`, `AC_PID_2D.cpp:129-145`. -/
def AC_PID_2D.update_i.body (fp : UInt64) (this : UInt64) (dt : Binary32) (limit : UInt64) : PMem.M Unit := do
  let mut dt := dt
  PMem.stB ((this + 64) + 40) false
  PMem.stB ((this + 108) + 40) false
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 4)
  let t'2 ← PMem.ldF32 t'1
  Vector2'float.operator_'2 (this + 36) (fp + 8) t'2
  let t'3 := (fp + 8)
  Vector2'float.operator_'2 t'3 (fp + 16) dt
  let t'4 := (fp + 16)
  Vector2'float.Vector2'3 (fp + 0) t'4
  let t'5 ← Vector2'float.length (this + 52)
  let mut integrator_length : Binary32 := t'5
  let t'6 ← Vector2'float.operator__ (this + 52) (fp + 0)
  discard <| pure (t'6)
  let t'7 ← Vector2'float.operator_'4 (fp + 0) limit
  let t'8 ← is_positive'float t'7
  let mut sc'10 := t'8
  if sc'10 then
    let t'9 ← Vector2'float.limit_length (this + 52) integrator_length
    sc'10 := t'9
  if sc'10 then
    PMem.stB ((this + 64) + 40) true
    PMem.stB ((this + 108) + 40) true
  let t'11 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'12 ← PMem.ldF32 t'11
  let t'13 ← Vector2'float.limit_length (this + 52) t'12
  discard <| pure (t'13)
  return ()

def AC_PID_2D.update_i (this : UInt64) (dt : Binary32) (limit : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_PID_2D.update_i.body fp this dt limit
  PMem.leave fp
  return r

/-- C++ `AC_PID_2D::reset_I : void ()`, `AC_PID_2D.cpp:170-173`. -/
def AC_PID_2D.reset_I (this : UInt64) : PMem.M Unit := do
  Vector2'float.zero (this + 52)
  return ()

/-- `AC_PID_2D.kP` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID_2D.kP.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AC_PID_2D::kP : AP_Float &()`, `AP_Common.h:50-?`. -/
def AC_PID_2D.kP (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PID_2D.kP.pure' this)

/-- `AC_PID.set_notch_sample_rate` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PID.set_notch_sample_rate.pure' (this : UInt64) (sample_rate : Binary32) : Id Unit := do
  let mut sample_rate := sample_rate
  return ()

/-- C++ `AC_PID::set_notch_sample_rate : void (float)`, `AC_PID.cpp:158-191`. -/
def AC_PID.set_notch_sample_rate (this : UInt64) (sample_rate : Binary32) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AC_PID.set_notch_sample_rate.pure' this sample_rate)

end Vehicle_lib
