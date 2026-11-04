import AP_Motors

/-!
# Spot checks for the `AP_Motors` port

Builds the quad X object with the code defaults (`init {}`), sets `_dt_s = 0.0025` (400 Hz),
`air_density_ratio = 1`, and runs `output` on three inputs: hover throttle with zero roll, pitch
and yaw; a roll input; and an input that saturates. A fourth case uses the linear configuration
(`MOT_THST_EXPO = 0`, `MOT_SPIN_MIN = 0`, `MOT_SPIN_MAX = 1`), where `thrust_to_actuator` is the
identity on [0, 1]. Prints values in decimal and as bit patterns.
Run with `lake env lean --run AP_Motors/MotorsCheck.lean` after `lake build AP_Motors`.
-/

open AP_Math AP_Motors AP_MotorsMulticopter AP_MotorsMatrix

namespace AP_Motors.MotorsCheck

def hex (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (8 - s.length) '0') ++ s

def f (x : Float32) : String := s!"{x} [{hex x.toBits.toNat}]"
def v4 (v : Vector Float32 4) : String := ", ".intercalate (v.toList.map f)
def lim (l : Limit) : String :=
  s!"roll={l.roll} pitch={l.pitch} yaw={l.yaw} throttle_lower={l.throttle_lower} throttle_upper={l.throttle_upper}"

/-- One tick from `s0` with the given inputs, as the Copter loop would call it. -/
def tick (p : Params) (s0 : AP_MotorsMatrix.State) (roll pitch yaw thr avg_max : ftype) :
    AP_MotorsMatrix.State × Vector ftype 4 :=
  let s := AP_MotorsMatrix.set_dt_s s0 0.0025
  let m := s.toInputs
  let m := set_roll m roll
  let m := set_pitch m pitch
  let m := set_yaw m yaw
  let m := set_throttle m thr
  let m := set_throttle_avg_max m avg_max
  let s := { s with toInputs := m, air_density_ratio := 1.0 }
  output p s

def report (name : String) (r : AP_MotorsMatrix.State × Vector ftype 4) : IO Unit := do
  let (s, a) := r
  IO.println s!"== {name}"
  IO.println s!"  _thrust_rpyt_out: {v4 s._thrust_rpyt_out}"
  IO.println s!"  _actuator:        {v4 a}"
  IO.println s!"  _throttle_out:    {f s._throttle_out}"
  IO.println s!"  limit:            {lim s.limit}"

def main : IO Unit := do
  let p : Params := {}
  let s0 := init p
  IO.println "== quad X factors after setup_motors (motor slots 0..3)"
  IO.println s!"  _roll_factor:     {v4 s0._roll_factor}"
  IO.println s!"  _pitch_factor:    {v4 s0._pitch_factor}"
  IO.println s!"  _yaw_factor:      {v4 s0._yaw_factor}"
  IO.println s!"  _throttle_factor: {v4 s0._throttle_factor}"
  IO.println s!"  _test_order:      {s0._test_order.toList}"
  IO.println s!"  _initialised_ok:  {s0._initialised_ok}"
  IO.println s!"  limit at init:    {lim s0.limit}"
  -- hover throttle (MOT_THST_HOVER = 0.35), zero rpy: expect four equal actuators
  report "1. hover throttle 0.35, rpy = 0 (expect four equal actuators)"
    (tick p s0 0 0 0 0.35 0.35)
  -- roll input 0.1: motors 1 and 2 (left, roll factor +0.5) up, motors 0 and 3 down
  report "2. throttle 0.35, roll 0.1 (expect slots 1,2 up and 0,3 down by the same amount)"
    (tick p s0 0.1 0 0 0.35 0.35)
  -- roll 1.0, yaw 0.5, throttle 0.9: yaw limited to the headroom 0.2, rpy scaled by 1/1.2
  report "3. throttle 0.9, roll 1.0, yaw 0.5 (expect limit.roll/pitch/yaw and throttle_upper)"
    (tick p s0 1.0 0 0.5 0.9 0.9)
  -- linear configuration: actuator = thrust
  let pl : Params := { MOT_THST_EXPO := 0, MOT_SPIN_MIN := 0, MOT_SPIN_MAX := 1 }
  report "4. linear configuration, throttle 0.35, roll 0.1 (expect actuator = _thrust_rpyt_out)"
    (tick pl (init pl) 0.1 0 0 0.35 0.35)

end AP_Motors.MotorsCheck

def main : IO Unit := AP_Motors.MotorsCheck.main
