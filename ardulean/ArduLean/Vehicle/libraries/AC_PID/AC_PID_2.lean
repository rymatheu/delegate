import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.Filter.Filter_2

/-!
ArduPilot `libraries/AC_PID`, part 2 of 2. Sources: `libraries/AC_PID/AC_PID.cpp`, `libraries/AC_PID/AC_PID_2D.cpp`, `libraries/AC_PID/AC_PID_Basic.cpp`, `libraries/AC_PID/AC_P_1D.cpp`, `libraries/AC_PID/AC_P_2D.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AC_P_1D::set_limits : void (float, float, float, float)`, `AC_P_1D.cpp:46-71`. -/
def AC_P_1D.set_limits.body (fp : UInt64) (this : UInt64) (output_min : Binary32) (output_max : Binary32) (D_Out_max : Binary32) (D2_Out_max : Binary32) : PMem.M Unit := do
  let mut output_min := output_min
  let mut output_max := output_max
  let mut D_Out_max := D_Out_max
  let mut D2_Out_max := D2_Out_max
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 16) t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 8) t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 12) t'3
  let t'4 ← is_positive'float D_Out_max
  if t'4 then
    PMem.stF32 (this + 16) D_Out_max
  let t'5 ← is_positive'float D2_Out_max
  let mut sc'7 := t'5
  if sc'7 then
    discard <| PMem.memcpy (fp + 0) this 4
    let t'6 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
    sc'7 := t'6
  if sc'7 then
    let t'8 ← AP_ParamT'float_4.operator_const_float__'1 this
    let t'9 ← PMem.ldF32 t'8
    PMem.stF32 (fp + 4) (D2_Out_max / t'9)
    let t'10 ← MIN'float_float (this + 16) (fp + 4)
    let t'11 ← PMem.ldF32 t'10
    PMem.stF32 (this + 16) t'11
  let t'12 ← is_negative'float output_min
  let mut sc'14 := t'12
  if sc'14 then
    discard <| PMem.memcpy (fp + 8) this 4
    let t'13 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 8)
    sc'14 := t'13
  if sc'14 then
    let t'15 ← AP_ParamT'float_4.operator_const_float__'1 this
    let t'16 ← PMem.ldF32 t'15
    let t'17 ← PMem.ldF32 (this + 16)
    let t'18 ← inv_sqrt_controller output_min t'16 t'17
    PMem.stF32 (this + 8) t'18
  let t'19 ← is_positive'float output_max
  let mut sc'21 := t'19
  if sc'21 then
    discard <| PMem.memcpy (fp + 16) this 4
    let t'20 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 16)
    sc'21 := t'20
  if sc'21 then
    let t'22 ← AP_ParamT'float_4.operator_const_float__'1 this
    let t'23 ← PMem.ldF32 t'22
    let t'24 ← PMem.ldF32 (this + 16)
    let t'25 ← inv_sqrt_controller output_max t'23 t'24
    PMem.stF32 (this + 12) t'25
  return ()

def AC_P_1D.set_limits (this : UInt64) (output_min : Binary32) (output_max : Binary32) (D_Out_max : Binary32) (D2_Out_max : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← AC_P_1D.set_limits.body fp this output_min output_max D_Out_max D2_Out_max
  PMem.leave fp
  return r

/-- C++ `AC_P_2D::set_limits : void (float, float, float)`, `AC_P_2D.cpp:42-63`. -/
def AC_P_2D.set_limits.body (fp : UInt64) (this : UInt64) (output_max : Binary32) (D_Out_max : Binary32) (D2_Out_max : Binary32) : PMem.M Unit := do
  let mut output_max := output_max
  let mut D_Out_max := D_Out_max
  let mut D2_Out_max := D2_Out_max
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 16) t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 12) t'2
  let t'3 ← is_positive'float D_Out_max
  if t'3 then
    PMem.stF32 (this + 16) D_Out_max
  let t'4 ← is_positive'float D2_Out_max
  let mut sc'6 := t'4
  if sc'6 then
    discard <| PMem.memcpy (fp + 0) this 4
    let t'5 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
    sc'6 := t'5
  if sc'6 then
    let t'7 ← AP_ParamT'float_4.operator_const_float__'1 this
    let t'8 ← PMem.ldF32 t'7
    PMem.stF32 (fp + 4) (D2_Out_max / t'8)
    let t'9 ← MIN'float_float (this + 16) (fp + 4)
    let t'10 ← PMem.ldF32 t'9
    PMem.stF32 (this + 16) t'10
  let t'11 ← is_positive'float output_max
  let mut sc'13 := t'11
  if sc'13 then
    discard <| PMem.memcpy (fp + 8) this 4
    let t'12 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 8)
    sc'13 := t'12
  if sc'13 then
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 this
    let t'15 ← PMem.ldF32 t'14
    let t'16 ← PMem.ldF32 (this + 16)
    let t'17 ← inv_sqrt_controller output_max t'15 t'16
    PMem.stF32 (this + 12) t'17
  return ()

def AC_P_2D.set_limits (this : UInt64) (output_max : Binary32) (D_Out_max : Binary32) (D2_Out_max : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_P_2D.set_limits.body fp this output_max D_Out_max D2_Out_max
  PMem.leave fp
  return r

/-- C++ `AC_PID::get_filt_T_alpha : float (float) const`, `AC_PID.cpp:415-418`. -/
def AC_PID.get_filt_T_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID::get_filt_E_alpha : float (float) const`, `AC_PID.cpp:421-424`. -/
def AC_PID.get_filt_E_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 28)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID::get_filt_D_alpha : float (float) const`, `AC_PID.cpp:427-430`. -/
def AC_PID.get_filt_D_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 32)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID::update_i : void (float, bool, float)`, `AC_PID.cpp:340-351`. -/
def AC_PID.update_i.body (fp : UInt64) (this : UInt64) (dt : Binary32) (limit : Bool) (i_scale : Binary32) : PMem.M Unit := do
  let mut dt := dt
  let mut limit := limit
  let mut i_scale := i_scale
  discard <| PMem.memcpy (fp + 0) (this + 4) 4
  let t'1 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  let mut sc'3 := !t'1
  if sc'3 then
    let t'2 ← is_positive'float dt
    sc'3 := t'2
  if sc'3 then
    let mut sc'15 := !limit
    if !sc'15 then
      let t'4 ← PMem.ldF32 (this + 132)
      let t'5 ← is_positive'float t'4
      let mut sc'8 := t'5
      if sc'8 then
        let t'6 ← PMem.ldF32 (this + 140)
        let t'7 ← is_negative'float t'6
        sc'8 := t'7
      let mut sc'14 := sc'8
      if !sc'14 then
        let t'9 ← PMem.ldF32 (this + 132)
        let t'10 ← is_negative'float t'9
        let mut sc'13 := t'10
        if sc'13 then
          let t'11 ← PMem.ldF32 (this + 140)
          let t'12 ← is_positive'float t'11
          sc'13 := t'12
        sc'14 := sc'13
      sc'15 := sc'14
    if sc'15 then
      let t'16 := (this + 132)
      let t'17 ← PMem.ldF32 t'16
      let t'18 ← PMem.ldF32 (this + 140)
      let t'19 ← AP_ParamT'float_4.operator_const_float__'1 (this + 4)
      let t'20 ← PMem.ldF32 t'19
      let t'21 := (t'17 + (((t'18 * t'20) * i_scale) * dt))
      PMem.stF32 t'16 t'21
      let t'22 ← PMem.ldF32 (this + 132)
      let t'23 ← AP_ParamT'float_4.operator_'3 (this + 16)
      let t'24 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
      let t'25 ← PMem.ldF32 t'24
      let t'26 ← constrain_value_line'float t'22 t'23 t'25 (Int32.toUInt32 ((346 : Int32)))
      PMem.stF32 (this + 132) t'26
  else
    let t'27 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 132) t'27
  return ()

def AC_PID.update_i (this : UInt64) (dt : Binary32) (limit : Bool) (i_scale : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_PID.update_i.body fp this dt limit i_scale
  PMem.leave fp
  return r

/-- C++ `AC_PID::update_all : float (float, float, float, bool, float, float)`, `AC_PID.cpp:196-311`. -/
def AC_PID.update_all.body (fp : UInt64) (this : UInt64) (target : Binary32) (measurement : Binary32) (dt : Binary32) (limit : Bool) (pd_scale : Binary32) (i_scale : Binary32) : PMem.M Binary32 := do
  let mut target := target
  let mut measurement := measurement
  let mut dt := dt
  let mut limit := limit
  let mut pd_scale := pd_scale
  let mut i_scale := i_scale
  if ((!(Binary32.isFinite target)) || (!(Binary32.isFinite measurement))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldBits (this + 128) 0 1
  let t'2 := (t'1 != 0)
  PMem.stB ((this + 156) + 42) t'2
  let t'3 ← PMem.ldBits (this + 128) 0 1
  if (t'3 != 0) then
    PMem.stBits (this + 128) 0 1 (if false then (1 : UInt64) else 0)
    PMem.stF32 (this + 136) target
    let t'4 ← PMem.ldF32 (this + 136)
    let t'5 := (t'4 - measurement)
    PMem.stF32 (this + 140) t'5
    let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 144) t'6
    let t'7 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 152) t'7
  else
    let t'8 ← PMem.ldF32 (this + 136)
    let mut target_last : Binary32 := t'8
    let t'9 := (this + 136)
    let t'10 ← PMem.ldF32 t'9
    let t'11 ← AC_PID.get_filt_T_alpha this dt
    let t'12 ← PMem.ldF32 (this + 136)
    let t'13 := (t'10 + (t'11 * (target - t'12)))
    PMem.stF32 t'9 t'13
    let t'14 ← PMem.ldF32 (this + 140)
    let mut error_last : Binary32 := t'14
    let t'15 ← PMem.ldF32 (this + 136)
    let mut error : Binary32 := (t'15 - measurement)
    let t'16 := (this + 140)
    let t'17 ← PMem.ldF32 t'16
    let t'18 ← AC_PID.get_filt_E_alpha this dt
    let t'19 ← PMem.ldF32 (this + 140)
    let t'20 := (t'17 + (t'18 * (error - t'19)))
    PMem.stF32 t'16 t'20
    let t'21 ← is_positive'float dt
    if t'21 then
      let t'22 ← PMem.ldF32 (this + 140)
      let mut derivative : Binary32 := ((t'22 - error_last) / dt)
      let t'23 := (this + 144)
      let t'24 ← PMem.ldF32 t'23
      let t'25 ← AC_PID.get_filt_D_alpha this dt
      let t'26 ← PMem.ldF32 (this + 144)
      let t'27 := (t'24 + (t'25 * (derivative - t'26)))
      PMem.stF32 t'23 t'27
      let t'28 ← PMem.ldF32 (this + 136)
      let t'29 := ((t'28 - target_last) / dt)
      PMem.stF32 (this + 152) t'29
  AC_PID.update_i this dt limit i_scale
  let t'30 ← PMem.ldF32 (this + 140)
  let t'31 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'32 ← PMem.ldF32 t'31
  let mut P_out : Binary32 := (t'30 * t'32)
  let t'33 ← PMem.ldF32 (this + 144)
  let t'34 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'35 ← PMem.ldF32 t'34
  let mut D_out : Binary32 := (t'33 * t'35)
  let t'36 ← PMem.ldF32 (this + 132)
  let mut I_out : Binary32 := t'36
  let t'37 ← PMem.ldF32 ((this + 156) + 12)
  let t'38 ← PMem.ldF32 ((this + 156) + 20)
  let t'39 ← PMem.ldI8 (this + 148)
  let t'40 ← SlewLimiter.modifier (this + 48) ((t'37 + t'38) * (Int32.toBinary32 ((Int8.toInt32 (t'39))))) dt
  PMem.stF32 ((this + 156) + 32) t'40
  let t'41 ← SlewLimiter.get_slew_rate (this + 48)
  PMem.stF32 ((this + 156) + 36) t'41
  let t'42 ← PMem.ldF32 ((this + 156) + 32)
  let t'43 := (P_out * t'42)
  P_out := t'43
  let t'44 ← PMem.ldF32 ((this + 156) + 32)
  let t'45 := (D_out * t'44)
  D_out := t'45
  let t'46 := (P_out * pd_scale)
  P_out := t'46
  let t'47 := (D_out * pd_scale)
  D_out := t'47
  PMem.stB ((this + 156) + 41) false
  discard <| PMem.memcpy (fp + 0) (this + 20) 4
  let t'48 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if t'48 then
    let mut PD_sum_abs : Binary32 := (Binary32.abs (P_out + D_out))
    let t'49 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
    let t'50 ← PMem.ldF32 t'49
    if (decide (PD_sum_abs > t'50)) then
      let t'51 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
      let t'52 ← PMem.ldF32 t'51
      let mut pd_limit_scale : Binary32 := (t'52 / PD_sum_abs)
      let t'53 := (P_out * pd_limit_scale)
      P_out := t'53
      let t'54 := (D_out * pd_limit_scale)
      D_out := t'54
      PMem.stB ((this + 156) + 41) true
  let t'55 ← PMem.ldF32 (this + 136)
  PMem.stF32 (this + 156) t'55
  PMem.stF32 ((this + 156) + 4) measurement
  let t'56 ← PMem.ldF32 (this + 140)
  PMem.stF32 ((this + 156) + 8) t'56
  PMem.stF32 ((this + 156) + 12) P_out
  PMem.stF32 ((this + 156) + 20) D_out
  PMem.stF32 ((this + 156) + 16) I_out
  PMem.stB ((this + 156) + 40) limit
  let t'57 ← PMem.ldBits (this + 128) 1 1
  let t'58 := (t'57 != 0)
  PMem.stB ((this + 156) + 43) t'58
  PMem.stBits (this + 128) 1 1 (if false then (1 : UInt64) else 0)
  let t'59 ← PMem.ldF32 (this + 136)
  let t'60 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'61 ← PMem.ldF32 t'60
  let t'62 := (t'59 * t'61)
  PMem.stF32 ((this + 156) + 24) t'62
  let t'63 ← PMem.ldF32 (this + 152)
  let t'64 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
  let t'65 ← PMem.ldF32 t'64
  let t'66 := (t'63 * t'65)
  PMem.stF32 ((this + 156) + 28) t'66
  return ((P_out + D_out) + I_out)

def AC_PID.update_all (this : UInt64) (target : Binary32) (measurement : Binary32) (dt : Binary32) (limit : Bool) (pd_scale : Binary32) (i_scale : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_PID.update_all.body fp this target measurement dt limit pd_scale i_scale
  PMem.leave fp
  return r

/-- C++ `AC_PID_Basic::get_filt_E_alpha : float (float) const`, `AC_PID_Basic.cpp:156-159`. -/
def AC_PID_Basic.get_filt_E_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID_Basic::get_filt_D_alpha : float (float) const`, `AC_PID_Basic.cpp:162-165`. -/
def AC_PID_Basic.get_filt_D_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID_Basic::update_i : void (float, bool, bool)`, `AC_PID_Basic.cpp:125-136`. -/
def AC_PID_Basic.update_i.body (fp : UInt64) (this : UInt64) (dt : Binary32) (limit_neg : Bool) (limit_pos : Bool) : PMem.M Unit := do
  let mut dt := dt
  let mut limit_neg := limit_neg
  let mut limit_pos := limit_pos
  discard <| PMem.memcpy (fp + 0) (this + 4) 4
  let t'1 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'1 then
    let mut sc'4 := limit_neg
    if sc'4 then
      let t'2 ← PMem.ldF32 (this + 32)
      let t'3 ← is_negative'float t'2
      sc'4 := t'3
    let mut sc'8 := sc'4
    if !sc'8 then
      let mut sc'7 := limit_pos
      if sc'7 then
        let t'5 ← PMem.ldF32 (this + 32)
        let t'6 ← is_positive'float t'5
        sc'7 := t'6
      sc'8 := sc'7
    if !sc'8 then
      let t'9 := (this + 40)
      let t'10 ← PMem.ldF32 t'9
      let t'11 ← PMem.ldF32 (this + 32)
      let t'12 ← AP_ParamT'float_4.operator_const_float__'1 (this + 4)
      let t'13 ← PMem.ldF32 t'12
      let t'14 := (t'10 + ((t'11 * t'13) * dt))
      PMem.stF32 t'9 t'14
      let t'15 ← PMem.ldF32 (this + 40)
      let t'16 ← AP_ParamT'float_4.operator_'3 (this + 16)
      let t'17 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
      let t'18 ← PMem.ldF32 t'17
      let t'19 ← constrain_value_line'float t'15 t'16 t'18 (Int32.toUInt32 ((131 : Int32)))
      PMem.stF32 (this + 40) t'19
  else
    let t'20 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 40) t'20
  return ()

def AC_PID_Basic.update_i (this : UInt64) (dt : Binary32) (limit_neg : Bool) (limit_pos : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_PID_Basic.update_i.body fp this dt limit_neg limit_pos
  PMem.leave fp
  return r

/-- C++ `AC_PID_Basic::update_all : float (float, float, float, bool, bool)`, `AC_PID_Basic.cpp:77-120`. -/
def AC_PID_Basic.update_all (this : UInt64) (target : Binary32) (measurement : Binary32) (dt : Binary32) (limit_neg : Bool) (limit_pos : Bool) : PMem.M Binary32 := do
  let mut target := target
  let mut measurement := measurement
  let mut dt := dt
  let mut limit_neg := limit_neg
  let mut limit_pos := limit_pos
  if ((((!(Binary32.isFinite target)) || (Binary32.isNaN target)) || (!(Binary32.isFinite measurement))) || (Binary32.isNaN measurement)) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 28) target
  let t'1 ← PMem.ldB (this + 44)
  if t'1 then
    PMem.stB (this + 44) false
    let t'2 ← PMem.ldF32 (this + 28)
    let t'3 := (t'2 - measurement)
    PMem.stF32 (this + 32) t'3
    let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 36) t'4
  else
    let t'5 ← PMem.ldF32 (this + 32)
    let mut error_last : Binary32 := t'5
    let t'6 := (this + 32)
    let t'7 ← PMem.ldF32 t'6
    let t'8 ← AC_PID_Basic.get_filt_E_alpha this dt
    let t'9 ← PMem.ldF32 (this + 28)
    let t'10 ← PMem.ldF32 (this + 32)
    let t'11 := (t'7 + (t'8 * ((t'9 - measurement) - t'10)))
    PMem.stF32 t'6 t'11
    let t'12 ← is_positive'float dt
    if t'12 then
      let t'13 ← PMem.ldF32 (this + 32)
      let mut derivative : Binary32 := ((t'13 - error_last) / dt)
      let t'14 := (this + 36)
      let t'15 ← PMem.ldF32 t'14
      let t'16 ← AC_PID_Basic.get_filt_D_alpha this dt
      let t'17 ← PMem.ldF32 (this + 36)
      let t'18 := (t'15 + (t'16 * (derivative - t'17)))
      PMem.stF32 t'14 t'18
  AC_PID_Basic.update_i this dt limit_neg limit_pos
  let t'19 ← PMem.ldF32 (this + 32)
  let t'20 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'21 ← PMem.ldF32 t'20
  let mut P_out : Binary32 := (t'19 * t'21)
  let t'22 ← PMem.ldF32 (this + 36)
  let t'23 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'24 ← PMem.ldF32 t'23
  let mut D_out : Binary32 := (t'22 * t'24)
  let t'25 ← PMem.ldF32 (this + 28)
  PMem.stF32 (this + 48) t'25
  PMem.stF32 ((this + 48) + 4) measurement
  let t'26 ← PMem.ldF32 (this + 32)
  PMem.stF32 ((this + 48) + 8) t'26
  let t'27 ← PMem.ldF32 (this + 32)
  let t'28 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'29 ← PMem.ldF32 t'28
  let t'30 := (t'27 * t'29)
  PMem.stF32 ((this + 48) + 12) t'30
  let t'31 ← PMem.ldF32 (this + 40)
  PMem.stF32 ((this + 48) + 16) t'31
  let t'32 ← PMem.ldF32 (this + 36)
  let t'33 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'34 ← PMem.ldF32 t'33
  let t'35 := (t'32 * t'34)
  PMem.stF32 ((this + 48) + 20) t'35
  let t'36 ← PMem.ldF32 (this + 28)
  let t'37 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'38 ← PMem.ldF32 t'37
  let t'39 := (t'36 * t'38)
  PMem.stF32 ((this + 48) + 24) t'39
  let t'40 ← PMem.ldF32 (this + 40)
  let t'41 ← PMem.ldF32 (this + 28)
  let t'42 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'43 ← PMem.ldF32 t'42
  return (((P_out + t'40) + D_out) + (t'41 * t'43))

/-- C++ `AC_PID_2D::get_filt_E_alpha : float (float) const`, `AC_PID_2D.cpp:188-191`. -/
def AC_PID_2D.get_filt_E_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID_2D::get_filt_D_alpha : float (float) const`, `AC_PID_2D.cpp:194-197`. -/
def AC_PID_2D.get_filt_D_alpha (this : UInt64) (dt : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← calc_lowpass_alpha_dt dt t'2
  return t'3

/-- C++ `AC_PID_2D::update_all : Vector2f (const Vector2f &, const Vector2f &, float, const Vector2f &)`, `AC_PID_2D.cpp:70-120`. -/
def AC_PID_2D.update_all.body (fp : UInt64) (this : UInt64) (sret : UInt64) (target : UInt64) (measurement : UInt64) (dt : Binary32) (limit : UInt64) : PMem.M Unit := do
  let mut dt := dt
  let t'1 ← Vector2'float.is_nan target
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← Vector2'float.is_inf target
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← Vector2'float.is_nan measurement
    sc'5 := t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← Vector2'float.is_inf measurement
    sc'7 := t'6
  if sc'7 then
    Vector2'float.Vector2 (fp + 0)
    Vector2'float.Vector2'3 sret (fp + 0)
    return ()
  discard <| PMem.memcpy (this + 28) target 8
  discard <| pure ((this + 28))
  let t'8 ← PMem.ldB (this + 60)
  if t'8 then
    PMem.stB (this + 60) false
    Vector2'float.operator_ (this + 28) (fp + 8) measurement
    let t'9 := (fp + 8)
    discard <| PMem.memcpy (this + 36) t'9 8
    discard <| pure ((this + 36))
    Vector2'float.zero (this + 44)
  else
    Vector2'float.Vector2'4 (fp + 16) (this + 36)
    Vector2'float.operator_ (this + 28) (fp + 24) measurement
    let t'10 := (fp + 24)
    Vector2'float.operator_ t'10 (fp + 32) (this + 36)
    let t'11 := (fp + 32)
    let t'12 ← AC_PID_2D.get_filt_E_alpha this dt
    Vector2'float.operator_'2 t'11 (fp + 40) t'12
    let t'13 := (fp + 40)
    let t'14 ← Vector2'float.operator__ (this + 36) t'13
    discard <| pure (t'14)
    let t'15 ← is_positive'float dt
    if t'15 then
      Vector2'float.operator_ (this + 36) (fp + 56) (fp + 16)
      let t'16 := (fp + 56)
      Vector2'float.operator_'5 t'16 (fp + 64) dt
      let t'17 := (fp + 64)
      Vector2'float.Vector2'3 (fp + 48) t'17
      Vector2'float.operator_ (fp + 48) (fp + 72) (this + 44)
      let t'18 := (fp + 72)
      let t'19 ← AC_PID_2D.get_filt_D_alpha this dt
      Vector2'float.operator_'2 t'18 (fp + 80) t'19
      let t'20 := (fp + 80)
      let t'21 ← Vector2'float.operator__ (this + 44) t'20
      discard <| pure (t'21)
  AC_PID_2D.update_i this dt limit
  let t'22 ← PMem.ldF32 (this + 28)
  PMem.stF32 (this + 64) t'22
  let t'23 ← PMem.ldF32 measurement
  PMem.stF32 ((this + 64) + 4) t'23
  let t'24 ← PMem.ldF32 (this + 36)
  PMem.stF32 ((this + 64) + 8) t'24
  let t'25 ← PMem.ldF32 (this + 36)
  let t'26 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'27 ← PMem.ldF32 t'26
  let t'28 := (t'25 * t'27)
  PMem.stF32 ((this + 64) + 12) t'28
  let t'29 ← PMem.ldF32 (this + 52)
  PMem.stF32 ((this + 64) + 16) t'29
  let t'30 ← PMem.ldF32 (this + 44)
  let t'31 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'32 ← PMem.ldF32 t'31
  let t'33 := (t'30 * t'32)
  PMem.stF32 ((this + 64) + 20) t'33
  let t'34 ← PMem.ldF32 (this + 28)
  let t'35 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'36 ← PMem.ldF32 t'35
  let t'37 := (t'34 * t'36)
  PMem.stF32 ((this + 64) + 24) t'37
  let t'38 ← PMem.ldF32 ((this + 28) + 4)
  PMem.stF32 (this + 108) t'38
  let t'39 ← PMem.ldF32 (measurement + 4)
  PMem.stF32 ((this + 108) + 4) t'39
  let t'40 ← PMem.ldF32 ((this + 36) + 4)
  PMem.stF32 ((this + 108) + 8) t'40
  let t'41 ← PMem.ldF32 ((this + 36) + 4)
  let t'42 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'43 ← PMem.ldF32 t'42
  let t'44 := (t'41 * t'43)
  PMem.stF32 ((this + 108) + 12) t'44
  let t'45 ← PMem.ldF32 ((this + 52) + 4)
  PMem.stF32 ((this + 108) + 16) t'45
  let t'46 ← PMem.ldF32 ((this + 44) + 4)
  let t'47 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'48 ← PMem.ldF32 t'47
  let t'49 := (t'46 * t'48)
  PMem.stF32 ((this + 108) + 20) t'49
  let t'50 ← PMem.ldF32 ((this + 28) + 4)
  let t'51 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'52 ← PMem.ldF32 t'51
  let t'53 := (t'50 * t'52)
  PMem.stF32 ((this + 108) + 24) t'53
  let t'54 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'55 ← PMem.ldF32 t'54
  Vector2'float.operator_'2 (this + 36) (fp + 88) t'55
  let t'56 := (fp + 88)
  Vector2'float.operator_'3 t'56 (fp + 96) (this + 52)
  let t'57 := (fp + 96)
  let t'58 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'59 ← PMem.ldF32 t'58
  Vector2'float.operator_'2 (this + 44) (fp + 104) t'59
  let t'60 := (fp + 104)
  Vector2'float.operator_'3 t'57 (fp + 112) t'60
  let t'61 := (fp + 112)
  let t'62 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'63 ← PMem.ldF32 t'62
  Vector2'float.operator_'2 (this + 28) (fp + 120) t'63
  let t'64 := (fp + 120)
  Vector2'float.operator_'3 t'61 (fp + 128) t'64
  let t'65 := (fp + 128)
  Vector2'float.Vector2'3 sret t'65
  return ()

def AC_PID_2D.update_all (this : UInt64) (sret : UInt64) (target : UInt64) (measurement : UInt64) (dt : Binary32) (limit : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 136
  let r ← AC_PID_2D.update_all.body fp this sret target measurement dt limit
  PMem.leave fp
  return r

end Vehicle_lib
