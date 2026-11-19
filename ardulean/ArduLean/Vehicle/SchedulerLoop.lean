import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.AP_Notify.AP_Notify
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_InternalError.AP_InternalError
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_3
import ArduLean.Vehicle.World
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig_2
import ArduLean.Vehicle.Arming
import ArduLean.Vehicle.ModeSwitching
import ArduLean.Vehicle.GcsMessages

/-!
Cross-library module `SchedulerLoop`: the scheduler loop: the task table's functors and their dispatcher, AP_Scheduler::run and loop, AP_Vehicle::loop. It belongs to the top of the call graph, where ArduPilot's libraries call each other in a cycle, so it cannot be cut by library. Largest functions: `AP_Scheduler.run`, `AP_Scheduler.loop`, `fnptr'0`, `fnptr'0'at'AP_Scheduler_Task'function`, `AP_Vehicle.scheduler_delay_callback`, `AP_Vehicle.loop`, `Functor'void.method_wrapper'Copter_rc_loop`, `Functor'void.method_wrapper'Copter_update_batt_compass`, `Functor'void.method_wrapper'Copter_update_flight_mode`, `Functor'void.method_wrapper'GCS_update_receive`. Sources: `libraries/AP_Scheduler/AP_Scheduler.cpp`, `(generated)`, `libraries/AP_Vehicle/AP_Vehicle.cpp`, `libraries/AP_HAL/utility/functor.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Vehicle::scheduler_delay_callback : void ()`, `AP_Vehicle.cpp:738-780`. -/
def AP_Vehicle.scheduler_delay_callback.body (fp : UInt64)  : PMem.M Unit := do
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (0xbf00 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_1hz -/
  if (decide ((tnow - t'1) > (Int32.toUInt32 ((1000 : Int32))))) then
    PMem.stU32 (0xbf00 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_1hz -/ tnow
    let t'2 ← gcs
    GCS.send_message t'2 (0 : UInt8)
    let t'3 ← gcs
    GCS.send_message t'3 (7 : UInt8)
  let t'4 ← PMem.ldU32 (0xbf08 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_50hz -/
  if (decide ((tnow - t'4) > (Int32.toUInt32 ((20 : Int32))))) then
    PMem.stU32 (0xbf08 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_50hz -/ tnow
    let t'5 ← gcs
    GCS.update_receive t'5
    let t'6 ← gcs
    GCS.update_send t'6
  let t'7 ← PMem.ldU32 (0xbf10 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_5s -/
  if (decide ((tnow - t'7) > (Int32.toUInt32 ((5000 : Int32))))) then
    PMem.stU32 (0xbf10 : UInt64) /- &AP_Vehicle::scheduler_delay_callback(...)::last_5s -/ tnow
    let t'8 ← AP_BoardConfig.in_config_error
    if t'8 then
      let t'9 ← gcs
      GCS.send_text t'9 (2 : UInt32) (0x185f8 : UInt64) /- "Config Error: fix problem then reboot" -/ (fp + 0)
    else
      let t'10 ← gcs
      GCS.send_text t'10 (6 : UInt32) (0x1861e : UInt64) /- "Initialising ArduPilot" -/ (fp + 8)
  return ()

def AP_Vehicle.scheduler_delay_callback  : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AP_Vehicle.scheduler_delay_callback.body fp 
  PMem.leave fp
  return r

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_flight_mode (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_flight_mode t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_rc_loop (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.rc_loop t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_batt_compass (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_batt_compass t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'RC_Channels_read_aux_all (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  RC_Channels.read_aux_all t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'GCS_update_receive (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  GCS.update_receive t
  return ()

/-- Calls through a function pointer of type `void (void *)` at one call site of the Functor's operator: the functions the Functor objects read there can hold (34 of 37; the Functor values of AP_Scheduler::Task::function). -/
def fnptr'0'at'AP_Scheduler_Task'function (f : UInt64) (a0 : UInt64) : PMem.M Unit := do
  if f == 0x7f000050 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_InertialSensor_update a0
  else if f == 0x7f000060 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_run_rate_controller_main a0
  else if f == 0x7f000070 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_motors_output_main a0
  else if f == 0x7f000080 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_read_AHRS a0
  else if f == 0x7f000090 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_read_inertia a0
  else if f == 0x7f0000a0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_check_ekf_reset a0
  else if f == 0x7f0000b0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_flight_mode a0
  else if f == 0x7f0000c0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_home_from_EKF a0
  else if f == 0x7f0000d0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_land_and_crash_detectors a0
  else if f == 0x7f0000e0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_rangefinder_terrain_offset a0
  else if f == 0x7f0000f0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_rc_loop a0
  else if f == 0x7f000100 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_throttle_loop a0
  else if f == 0x7f000110 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_GPS_update a0
  else if f == 0x7f000120 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_batt_compass a0
  else if f == 0x7f000130 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'RC_Channels_read_aux_all a0
  else if f == 0x7f000140 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_auto_disarm_check a0
  else if f == 0x7f000150 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_altitude a0
  else if f == 0x7f000160 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_run_nav_updates a0
  else if f == 0x7f000170 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_throttle_hover a0
  else if f == 0x7f000180 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_three_hz_loop a0
  else if f == 0x7f000190 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_one_hz_loop a0
  else if f == 0x7f0001a0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_ekf_check a0
  else if f == 0x7f0001b0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_check_vibration a0
  else if f == 0x7f0001c0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_gpsglitch_check a0
  else if f == 0x7f0001d0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_takeoff_check a0
  else if f == 0x7f0001e0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_standby_update a0
  else if f == 0x7f0001f0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_lost_vehicle_check a0
  else if f == 0x7f000200 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'GCS_update_receive a0
  else if f == 0x7f000210 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'GCS_update_send a0
  else if f == 0x7f000220 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_InertialSensor_periodic a0
  else if f == 0x7e000020 then  -- AP_Notify::update (FUNCTOR_BIND_MEMBER)
    AP_Notify.update a0
  else if f == 0x7e000030 then  -- AP_Vehicle::send_watchdog_reset_statustext (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.send_watchdog_reset_statustext a0
  else if f == 0x7e000040 then  -- AP_Vehicle::one_Hz_update (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.one_Hz_update a0
  else if f == 0x7e000050 then  -- AP_Vehicle::update_arming (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.update_arming a0
  else
    PMem.unreached "function pointer void (void *)"
    return ()

/-- (at the call sites reading AP_Scheduler::Task::function) C++ `Functor<void>::operator() : void () const`, `functor.h:52-55`. -/
def Functor'void.operator__'at'AP_Scheduler_Task'function (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'0'at'AP_Scheduler_Task'function t'1 t'2
  return ()

/-- C++ `AP_Scheduler::run : void (uint32_t)`, `AP_Scheduler.cpp:191-317`. -/
def AP_Scheduler.run (this : UInt64) (time_available : UInt32) : PMem.M Unit := do
  let mut time_available := time_available
  let mut run_started_usec : UInt32 := (← PMem.clock).toUInt32
  let mut now : UInt32 := run_started_usec
  let mut vehicle_tasks_offset : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut common_tasks_offset : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 (this + 97)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let mut run_vehicle_task : Bool := false
    let t'5 ← PMem.ldU8 (this + 80)
    let mut sc'7 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (vehicle_tasks_offset))) < (UInt32.toInt32 (UInt8.toUInt32 (t'5)))))
    if sc'7 then
      let t'6 ← PMem.ldU8 (this + 96)
      sc'7 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (common_tasks_offset))) < (UInt32.toInt32 (UInt8.toUInt32 (t'6)))))
    if sc'7 then
      let t'8 ← PMem.ldU64 (this + 72)
      let vehicle_task : UInt64 := (t'8 + ((UInt64.toInt64 (UInt8.toUInt64 (vehicle_tasks_offset))) * 32).toUInt64)
      let t'9 ← PMem.ldU64 (this + 88)
      let common_task : UInt64 := (t'9 + ((UInt64.toInt64 (UInt8.toUInt64 (common_tasks_offset))) * 32).toUInt64)
      let t'10 ← PMem.ldU8 (vehicle_task + 30)
      let t'11 ← PMem.ldU8 (common_task + 30)
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) ≤ (UInt32.toInt32 (UInt8.toUInt32 (t'11))))) then
        run_vehicle_task := true
    else
      let t'12 ← PMem.ldU8 (this + 80)
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (vehicle_tasks_offset))) < (UInt32.toInt32 (UInt8.toUInt32 (t'12))))) then
        run_vehicle_task := true
      else
        let t'13 ← PMem.ldU8 (this + 96)
        if (decide ((UInt32.toInt32 (UInt8.toUInt32 (common_tasks_offset))) < (UInt32.toInt32 (UInt8.toUInt32 (t'13))))) then
          run_vehicle_task := false
        else
          break
    let mut c'14 : UInt64 := 0
    if run_vehicle_task then
      let t'15 ← PMem.ldU64 (this + 72)
      c'14 := (t'15 + ((UInt64.toInt64 (UInt8.toUInt64 (vehicle_tasks_offset))) * 32).toUInt64)
    else
      let t'16 ← PMem.ldU64 (this + 88)
      c'14 := (t'16 + ((UInt64.toInt64 (UInt8.toUInt64 (common_tasks_offset))) * 32).toUInt64)
    let task : UInt64 := c'14
    if run_vehicle_task then
      let t'17 := vehicle_tasks_offset
      let t'18 := (t'17 + 1)
      vehicle_tasks_offset := t'18
    else
      let t'19 := common_tasks_offset
      let t'20 := (t'19 + 1)
      common_tasks_offset := t'20
    let t'21 ← PMem.ldU8 (task + 30)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'21))) > (UInt32.toInt32 ((3 : UInt32))))) then
      let t'22 ← PMem.ldU16 (this + 98)
      let t'23 ← PMem.ldU64 (this + 104)
      let t'24 ← PMem.ldU16 (t'23 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64)
      let mut dt : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'22))) - (UInt32.toInt32 (UInt16.toUInt32 (t'24))))))
      let t'25 ← PMem.ldF32 (task + 24)
      let t'26 ← is_zero t'25
      let mut c'27 : Binary32 := default
      if t'26 then
        c'27 := Int32.toBinary32 ((1 : Int32))
      else
        let t'28 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
        let t'29 ← PMem.ldI16 t'28
        let t'30 ← PMem.ldF32 (task + 24)
        c'27 := ((Int32.toBinary32 ((Int16.toInt32 (t'29)))) / t'30)
      let mut interval_ticks : UInt32 := Binary32.toUInt32 (c'27)
      if (decide (interval_ticks < (Int32.toUInt32 ((1 : Int32))))) then
        let t'31 := Int32.toUInt32 ((1 : Int32))
        interval_ticks := t'31
      if (decide ((UInt16.toUInt32 (dt)) < interval_ticks)) then
        continue
      let t'32 ← PMem.ldU16 (task + 28)
      let t'33 := UInt16.toUInt32 (t'32)
      PMem.stU32 (this + 112) t'33
      if (decide ((UInt16.toUInt32 (dt)) ≥ (interval_ticks * (Int32.toUInt32 ((2 : Int32)))))) then
        AP.PerfInfo.task_slipped this i
      if (decide ((UInt16.toUInt32 (dt)) ≥ (interval_ticks * (UInt8.toUInt32 ((4 : UInt8)))))) then
        let t'34 := (this + 148)
        let t'35 ← PMem.ldU32 t'34
        let t'36 := (t'35 + 1)
        PMem.stU32 t'34 t'36
      let t'37 ← PMem.ldU32 (this + 112)
      if (decide (t'37 > time_available)) then
        continue
    else
      let t'38 ← AP_Scheduler.get_loop_period_us this
      PMem.stU32 (this + 112) t'38
    PMem.stU32 (this + 116) now
    let t'39 := UInt8.toInt8 (i)
    let t'40 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    PMem.stI8 ((t'40 + 8) + 72) t'39
    fill_nanf_stack
    Functor'void.operator__'at'AP_Scheduler_Task'function task
    let t'41 := Int32.toInt8 ((-(1 : Int32)))
    let t'42 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    PMem.stI8 ((t'42 + 8) + 72) t'41
    let t'43 ← PMem.ldU16 (this + 98)
    let t'44 ← PMem.ldU64 (this + 104)
    PMem.stU16 (t'44 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'43
    let t'45 := (← PMem.clock).toUInt32
    now := t'45
    let t'46 ← PMem.ldU32 (this + 116)
    let mut time_taken : UInt32 := (now - t'46)
    let mut overrun : Bool := false
    let t'47 ← PMem.ldU32 (this + 112)
    if (decide (time_taken > t'47)) then
      overrun := true
      for _ in [0:1] do
        let t'48 ← AP_ParamTBase'signed_char_1.get (this + 56)
        let t'49 ← PMem.ldI8 t'48
        if (decide ((3 : Int32) ≤ (Int8.toInt32 (t'49)))) then
          let t'50 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
          let t'51 ← PMem.ldU64 (task + 16)
          let t'52 ← PMem.ldU32 (this + 112)
          discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'50 #[(0x1830c : UInt64) /- "Scheduler overrun task[%u-%s] (%u/%u)\n" -/, (UInt32.toUInt64 ((UInt8.toUInt32 (i)))), t'51, (UInt32.toUInt64 (time_taken)), (UInt32.toUInt64 (t'52))]
    AP.PerfInfo.update_task_info this i (UInt32.toUInt16 (time_taken)) overrun
    if (decide (time_taken ≥ time_available)) then
      let t'53 := Int32.toUInt32 ((0 : Int32))
      time_available := t'53
    else
      let t'54 := (time_available - time_taken)
      time_available := t'54
  let t'55 := (this + 120)
  let t'56 ← PMem.ldU32 t'55
  let t'57 := (t'56 + time_available)
  PMem.stU32 t'55 t'57
  let t'58 := (this + 124)
  let t'59 ← PMem.ldU8 t'58
  let t'60 := (t'59 + 1)
  PMem.stU8 t'58 t'60
  let t'61 ← PMem.ldU8 (this + 124)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'61))) == (32 : Int32)) then
    let t'62 := (this + 124)
    let t'63 ← PMem.ldU8 t'62
    let t'64 := (t'63 / (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))))
    PMem.stU8 t'62 t'64
    let t'65 := (this + 120)
    let t'66 ← PMem.ldU32 t'65
    let t'67 := (t'66 / (Int32.toUInt32 ((2 : Int32))))
    PMem.stU32 t'65 t'67
  return ()

/-- C++ `AP_Scheduler::loop : void ()`, `AP_Scheduler.cpp:348-431`. -/
def AP_Scheduler.loop.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toInt8 ((-(3 : Int32)))
  let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stI8 ((t'2 + 8) + 72) t'1
  discard <| pure (true)
  let t'3 ← VehicleBridge.ins'0
  VehicleBridge.AP_InertialSensor.wait_for_sample'0 t'3
  worldOutputs'drain
  let t'4 := Int32.toInt8 ((-(1 : Int32)))
  let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stI8 ((t'5 + 8) + 72) t'4
  let t'6 := (← PMem.clock)
  PMem.stU64 (this + 136) t'6
  let t'7 ← PMem.ldU64 (this + 136)
  let mut sample_time_us : UInt32 := UInt64.toUInt32 (t'7)
  let t'8 ← PMem.ldU32 (this + 128)
  if (t'8 == (Int32.toUInt32 ((0 : Int32)))) then
    PMem.stU32 (this + 128) sample_time_us
    let t'9 ← AP_Scheduler.get_loop_period_s this
    PMem.stF32 (this + 132) t'9
  else
    let t'10 ← PMem.ldU32 (this + 128)
    let t'11 := ((UInt32.toBinary32 ((sample_time_us - t'10))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3eb0c6f7a0b5ed8d /- 19999999999999999/20000000000000000000000 -/))))
    PMem.stF32 (this + 132) t'11
  let t'12 ← VehicleBridge.sitl'0
  let mut sitl : UInt64 := t'12
  let mut c'13 : UInt32 := default
  if (sitl != 0) then
    let t'14 ← AP_ParamTBase'int_3.get (sitl + 248)
    let t'15 ← PMem.ldI32 t'14
    c'13 := Int32.toUInt32 (t'15)
  else
    c'13 := (1000 : UInt32)
  let mut loop_delay_us : UInt32 := c'13
  let t'16 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.hal "AP_HAL::Scheduler::delay_microseconds" t'16 #[(UInt16.toUInt64 ((UInt32.toUInt16 (loop_delay_us))))]
  AP_Scheduler.tick this
  let t'17 ← AP_Scheduler.get_loop_period_us this
  let mut loop_us : UInt32 := t'17
  let mut now : UInt32 := (← PMem.clock).toUInt32
  let mut time_available : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut loop_tick_us : UInt32 := (now - sample_time_us)
  if (decide (loop_tick_us < loop_us)) then
    let t'18 := (loop_us - loop_tick_us)
    time_available := t'18
  let t'19 ← PMem.ldU32 (this + 156)
  let t'20 := (time_available + t'19)
  time_available := t'20
  AP_Scheduler.run this time_available
  let t'21 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.hal "AP_HAL::Scheduler::delay_microseconds" t'21 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((1 : Int32))))))]
  let t'22 ← PMem.ldU32 (this + 148)
  if (decide (t'22 > (Int32.toUInt32 ((0 : Int32))))) then
    let t'23 ← PMem.ldU32 (this + 156)
    PMem.stU32 (fp + 0) (t'23 + (100 : UInt32))
    PMem.stU32 (fp + 4) (5000 : UInt32)
    let t'24 ← MIN'unsigned_int_unsigned_int (fp + 0) (fp + 4)
    let t'25 ← PMem.ldU32 t'24
    PMem.stU32 (this + 156) t'25
    let t'26 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 148) t'26
    let t'27 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 152) t'27
  else
    let t'28 ← PMem.ldU32 (this + 156)
    if (decide (t'28 > (Int32.toUInt32 ((0 : Int32))))) then
      let t'29 := (this + 152)
      let t'30 ← PMem.ldU32 t'29
      let t'31 := (t'30 + 1)
      PMem.stU32 t'29 t'31
      let t'32 ← PMem.ldU32 (this + 152)
      if (decide (t'32 > (Int32.toUInt32 ((50 : Int32))))) then
        let t'33 := Int32.toUInt32 ((0 : Int32))
        PMem.stU32 (this + 152) t'33
        PMem.stU32 (fp + 8) (0 : UInt32)
        let t'34 ← PMem.ldU32 (this + 156)
        PMem.stU32 (fp + 12) (t'34 - (50 : UInt32))
        let t'35 ← MAX'unsigned_int_unsigned_int (fp + 8) (fp + 12)
        let t'36 ← PMem.ldU32 t'35
        PMem.stU32 (this + 156) t'36
  let t'37 ← PMem.ldU32 (this + 128)
  AP.PerfInfo.check_loop_time this (sample_time_us - t'37)
  PMem.stU32 (this + 128) sample_time_us
  return ()

def AP_Scheduler.loop (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AP_Scheduler.loop.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Vehicle::loop : void ()`, `AP_Vehicle.cpp:577-610`. -/
def AP_Vehicle.loop.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Scheduler.loop (this + 208)
  let t'1 ← AP_Scheduler.get_loop_period_s (this + 208)
  PMem.stF32 (this + 376) t'1
  let t'2 ← PMem.ldB (this + 6768)
  if !t'2 then
    PMem.stB (this + 6768) true
    AP_BoardConfig.init_safety (this + 8)
    let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    let t'4 ← PMem.halDev "AP_HAL::RCOutput::get_output_mode_banner" t'3 #[(fp + 0), (UInt8.toUInt64 ((UInt64.toUInt8 ((50 : UInt64)))))]
    if (t'4 != 0) then
      PMem.stU64 (fp + 56) (fp + 0)
      let t'5 ← gcs
      GCS.send_text t'5 (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 56)
  let t'6 := (0 : UInt64)
  let t'7 ← AP_InternalError.errors t'6
  let mut new_internal_errors : UInt32 := t'7
  let t'8 ← PMem.ldU32 (this + 6772)
  if (t'8 != new_internal_errors) then
    PMem.stU64 (fp + 64) (UInt32.toUInt64 (new_internal_errors))
    let t'9 ← gcs
    GCS.send_text t'9 (2 : UInt32) (0x18572 : UInt64) /- "Internal Errors 0x%x" -/ (fp + 64)
    PMem.stU32 (this + 6772) new_internal_errors
  return ()

def AP_Vehicle.loop (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 72
  let r ← AP_Vehicle.loop.body fp this
  PMem.leave fp
  return r

/-- Calls through a function pointer of type `void (void *)`: the functions whose address the program takes with this type (30). -/
def fnptr'0 (f : UInt64) (a0 : UInt64) : PMem.M Unit := do
  if f == 0x7f000050 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_InertialSensor_update a0
  else if f == 0x7f000060 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_run_rate_controller_main a0
  else if f == 0x7f000070 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_motors_output_main a0
  else if f == 0x7f000080 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_read_AHRS a0
  else if f == 0x7f000090 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_read_inertia a0
  else if f == 0x7f0000a0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_check_ekf_reset a0
  else if f == 0x7f0000b0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_flight_mode a0
  else if f == 0x7f0000c0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_home_from_EKF a0
  else if f == 0x7f0000d0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_land_and_crash_detectors a0
  else if f == 0x7f0000e0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_rangefinder_terrain_offset a0
  else if f == 0x7f0000f0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_rc_loop a0
  else if f == 0x7f000100 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_throttle_loop a0
  else if f == 0x7f000110 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_GPS_update a0
  else if f == 0x7f000120 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_batt_compass a0
  else if f == 0x7f000130 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'RC_Channels_read_aux_all a0
  else if f == 0x7f000140 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_auto_disarm_check a0
  else if f == 0x7f000150 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_altitude a0
  else if f == 0x7f000160 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_run_nav_updates a0
  else if f == 0x7f000170 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_update_throttle_hover a0
  else if f == 0x7f000180 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_three_hz_loop a0
  else if f == 0x7f000190 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_one_hz_loop a0
  else if f == 0x7f0001a0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_ekf_check a0
  else if f == 0x7f0001b0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_check_vibration a0
  else if f == 0x7f0001c0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_gpsglitch_check a0
  else if f == 0x7f0001d0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_takeoff_check a0
  else if f == 0x7f0001e0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_standby_update a0
  else if f == 0x7f0001f0 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'Copter_lost_vehicle_check a0
  else if f == 0x7f000200 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'GCS_update_receive a0
  else if f == 0x7f000210 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'GCS_update_send a0
  else if f == 0x7f000220 then  -- Functor<void>::method_wrapper
    Functor'void.method_wrapper'AP_InertialSensor_periodic a0
  else if f == 0x7e000000 then  -- AP_Param::save_io_handler (FUNCTOR_BIND_MEMBER)
    AP_Param.save_io_handler a0
  else if f == 0x7e000010 then  -- GCS_MAVLINK::param_io_timer (FUNCTOR_BIND_MEMBER)
    GCS_MAVLINK.param_io_timer a0
  else if f == 0x7e000020 then  -- AP_Notify::update (FUNCTOR_BIND_MEMBER)
    AP_Notify.update a0
  else if f == 0x7e000030 then  -- AP_Vehicle::send_watchdog_reset_statustext (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.send_watchdog_reset_statustext a0
  else if f == 0x7e000040 then  -- AP_Vehicle::one_Hz_update (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.one_Hz_update a0
  else if f == 0x7e000050 then  -- AP_Vehicle::update_arming (FUNCTOR_BIND_MEMBER)
    AP_Vehicle.update_arming a0
  else if f == 0x7e000090 then  -- ModeAuto::exit_mission (FUNCTOR_BIND_MEMBER)
    ModeAuto.exit_mission a0
  else
    PMem.unreached "function pointer void (void *)"
    return ()

/-- C++ `Functor<void>::operator() : void () const`, `functor.h:52-55`. -/
def Functor'void.operator__ (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'0 t'1 t'2
  return ()

end Vehicle_lib
