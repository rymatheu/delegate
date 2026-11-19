import Leanfc.Mavlink.Mission
import Leanfc.Mavlink.ParamTable

/-!
# Gcs (the MAVLink services, one pure state machine)

`step cfg st telemetry incoming = (st', out, commands)`, called once per controller tick (400 Hz)
with at most one received message; time is `Telemetry.tick` (`cfg.tickUs` µs per tick). `out` are
the messages to send this tick, in order (the caller frames them with its own sequence numbers);
`commands` go to the vehicle, which answers each one, in order, in the next tick's
`Telemetry.results` (`Vehicle.lean`). Nothing here performs IO or reads a clock.

ArduCopter's conventions are followed (ArduPilot `libraries/GCS_MAVLink`, `ArduCopter/
GCS_MAVLink_Copter.cpp`, checkout 802db19de1, V4.8.0-dev), so that QGroundControl uses its ArduPilot
support; README.md, "MAVLink interface", and `sim/mavlink/QGC-REQUIREMENTS.md` list the behaviors and
where each comes from. In short:

- Identity: system `cfg.sysid`, component 1. HEARTBEAT every second and at once on an arm or mode
  change: type QUADROTOR, autopilot ARDUPILOTMEGA, base_mode CUSTOM_MODE | STABILIZE |
  MANUAL_INPUT, plus SAFETY_ARMED when armed and GUIDED_ENABLED when armed in a mode that runs the
  position controller; custom_mode the ArduCopter mode number; system_status CRITICAL on a
  failsafe, STANDBY on the ground, ACTIVE otherwise.
- Streams: ArduPilot's groups (EXTENDED_STATUS: SYS_STATUS, MISSION_CURRENT, GPS_RAW_INT,
  NAV_CONTROLLER_OUTPUT; POSITION: GLOBAL_POSITION_INT, LOCAL_POSITION_NED; EXTRA1: ATTITUDE;
  EXTRA2: VFR_HUD; EXTRA3: SYSTEM_TIME, BATTERY_STATUS) with ArduCopter's default rate 0 (only
  HEARTBEAT until asked), set by REQUEST_DATA_STREAM (Hz) or MAV_CMD_SET_MESSAGE_INTERVAL (µs, also
  for ATTITUDE_QUATERNION, EXTENDED_SYS_STATE, HOME_POSITION, GPS_GLOBAL_ORIGIN);
  MAV_CMD_REQUEST_MESSAGE sends one message after its COMMAND_ACK.
- Commands (COMMAND_LONG and COMMAND_INT, answered with COMMAND_ACK to the sender): translated to
  `Command`s, the vehicle's result becoming the ACK one tick later; unsupported ones UNSUPPORTED.
- Parameters: list paced at one PARAM_VALUE per `cfg.paramTicks` ticks (ArduPilot: 5 per 100 ms),
  read by index or name, set with the PARAM_VALUE echo; values numeric floats (ArduPilot's
  encoding, MAV_PARAM_TYPE of the parameter).
- Mission (type 0): upload by MISSION_COUNT, the vehicle requesting each item with
  MISSION_REQUEST_INT, again every `cfg.missionRetryTicks` (1 s) until it arrives, abandoned with
  OPERATION_CANCELLED `cfg.missionTimeoutTicks` (8 s) after the last item; MISSION_ACK at the end.
  Download, clear, set current, MISSION_CURRENT, MISSION_ITEM_REACHED. Item 0 is home. Fence and
  rally (types 1, 2) are empty: their lists have count 0, an upload of 0 items is accepted, more is
  NO_SPACE. Other types UNSUPPORTED. A MISSION_ITEM(_INT) with current 2 (go to) or 3 (change
  altitude) is a guided command answered by MISSION_ACK, as in ArduPilot.
- MAVLink FTP: every request is refused (QGroundControl then loads parameters by PARAM_REQUEST_LIST
  at once): open and list FileNotFound, session reset and terminate acknowledged.
- TIMESYNC (tc1 = 0) and PING (target 0) answered; STATUSTEXT queue, one per tick, with a banner on
  first contact, on PARAM_REQUEST_LIST (as ArduPilot) and on MAV_CMD_DO_SEND_BANNER.
- The tick of the last ground-station HEARTBEAT (`GcsState.gcsSeen`; sender type MAV_TYPE_GCS) is
  kept for the vehicle's ground-station failsafe.

`step` is total; its loops are folds over bounded arrays.
-/

namespace Mavlink

open Format FloatLib.Floats

/-- The services' configuration. -/
structure GcsConfig where
  sysid : UInt8 := 1
  compid : UInt8 := 1
  /-- µs per tick (400 Hz) -/
  tickUs : Nat := 2500
  /-- one PARAM_VALUE of a list every this many ticks (50 per second) -/
  paramTicks : Nat := 8
  /-- an upload item not received is requested again after this many ticks (1 s) -/
  missionRetryTicks : Nat := 400
  /-- an upload is abandoned this many ticks after the last item (8 s) -/
  missionTimeoutTicks : Nat := 3200
  /-- AUTOPILOT_VERSION flight_sw_version: major << 24 | minor << 16 | patch << 8 | type
  (4.7.0, FIRMWARE_VERSION_TYPE_DEV) -/
  swVersion : UInt32 := 0x04070000
  banner : Array String := #["leanfc V0.1.0 (ArduCopter 4.7 MAVLink)", "Frame: QUAD/X"]
  /-- SYS_STATUS onboard_control_sensors_present and _enabled -/
  sensors : UInt32 := 0x1020FC23

/-- The telemetry messages the services generate, each with its stream group. -/
inductive Out where
  | heartbeat | sysStatus | systemTime | gpsRawInt | attitude | attitudeQuaternion
  | localPositionNed | globalPositionInt | missionCurrent | navControllerOutput | vfrHud
  | extendedSysState | batteryStatus | homePosition | gpsGlobalOrigin | autopilotVersion
  deriving Repr, BEq, Inhabited

namespace Out

def all : Array Out :=
  #[.heartbeat, .sysStatus, .systemTime, .gpsRawInt, .attitude, .attitudeQuaternion,
    .localPositionNed, .globalPositionInt, .missionCurrent, .navControllerOutput, .vfrHud,
    .extendedSysState, .batteryStatus, .homePosition, .gpsGlobalOrigin, .autopilotVersion]

def index : Out → Nat
  | .heartbeat => 0 | .sysStatus => 1 | .systemTime => 2 | .gpsRawInt => 3 | .attitude => 4
  | .attitudeQuaternion => 5 | .localPositionNed => 6 | .globalPositionInt => 7
  | .missionCurrent => 8 | .navControllerOutput => 9 | .vfrHud => 10 | .extendedSysState => 11
  | .batteryStatus => 12 | .homePosition => 13 | .gpsGlobalOrigin => 14 | .autopilotVersion => 15

def msgid : Out → Nat
  | .heartbeat => 0 | .sysStatus => 1 | .systemTime => 2 | .gpsRawInt => 24 | .attitude => 30
  | .attitudeQuaternion => 31 | .localPositionNed => 32 | .globalPositionInt => 33
  | .missionCurrent => 42 | .navControllerOutput => 62 | .vfrHud => 74 | .extendedSysState => 245
  | .batteryStatus => 147 | .homePosition => 242 | .gpsGlobalOrigin => 49 | .autopilotVersion => 148

def ofMsgid (id : Nat) : Option Out := all.find? (·.msgid == id)

/-- MAV_DATA_STREAM group (ArduPilot `GCS_MAVLink_Parameters.cpp` stream lists); 0 for none. -/
def group : Out → Nat
  | .sysStatus | .missionCurrent | .gpsRawInt | .navControllerOutput => 2
  | .globalPositionInt | .localPositionNed => 6
  | .attitude => 10
  | .vfrHud => 11
  | .systemTime | .batteryStatus => 12
  | _ => 0

end Out

/-- What a command's result becomes once the vehicle reports it. -/
inductive Reply where
  | none
  /-- COMMAND_ACK for `command` to the sender -/
  | commandAck (command : UInt16) (sys comp : UInt8)
  /-- MISSION_ACK (mission type 0) to the sender of a guided MISSION_ITEM -/
  | missionAck (sys comp : UInt8)
  deriving Inhabited

/-- A mission upload in progress. -/
structure Upload where
  count : Nat
  next : Nat
  sys : UInt8
  comp : UInt8
  items : Array MissionItemInt
  lastRecv : Nat
  lastReq : Nat
  deriving Inhabited

structure GcsState where
  /-- a ground station has been heard -/
  contact : Bool := false
  /-- stream intervals in ticks (0: off) and next due tick, indexed by `Out.index` -/
  intervals : Array Nat := Out.all.map fun o => if o == .heartbeat then 400 else 0
  due : Array Nat := Out.all.map fun _ => 0
  /-- single messages requested (MAV_CMD_REQUEST_MESSAGE ...), sent next -/
  requested : Array Out := #[]
  params : ParamTable.Store
  /-- next index of a parameter list being sent, and the tick it is due -/
  paramNext : Option Nat := none
  paramDue : Nat := 0
  /-- items 1..n of the stored mission -/
  mission : Array MissionItemInt := #[]
  upload : Option Upload := none
  /-- replies awaiting the results of the commands sent last tick, in order -/
  pending : Array Reply := #[]
  texts : Array (Severity × String) := #[]
  /-- last reported arm state, mode and mission item (to send on change); none before the first tick -/
  last : Option (Bool × Nat × Nat) := none
  /-- tick of the last HEARTBEAT from a ground station (MAV_TYPE_GCS), for the vehicle's
  ground-station failsafe (ArduPilot: `sysid_mygcs_last_seen_time_ms`); none before the first -/
  gcsSeen : Option Nat := none

/-- A received message and its sender. -/
structure Incoming where
  sysid : UInt8
  compid : UInt8
  msg : Msg

namespace Gcs

def init (params : ParamTable.Store) (mission : Array MissionItemInt := #[]) : GcsState :=
  { params, mission }

/-! ## Constants (common.xml) -/

def resAccepted : UInt8 := 0
def resDenied : UInt8 := 2
def resUnsupported : UInt8 := 3
def resFailed : UInt8 := 4
def resCommandIntOnly : UInt8 := 8

def resultCode : CommandResult → UInt8
  | .accepted => resAccepted | .denied => resDenied | .failed => resFailed

def bootMs (cfg : GcsConfig) (t : Telemetry) : UInt32 := (t.tick * cfg.tickUs / 1000).toUInt32
def timeUs (cfg : GcsConfig) (t : Telemetry) : UInt64 := (t.tick * cfg.tickUs).toUInt64

def i32 (n : Int) : Int32 := Int32.ofInt (clampInt (-2147483648) 2147483647 n)
def i16 (n : Int) : Int16 := Int16.ofInt (clampInt (-32768) 32767 n)
def u16c (n : Int) : UInt16 := (clampInt 0 65535 n).toNat.toUInt16
def nanR : R := ExecFloat.Binary.ofBits32 0x7FC00000

/-! ## Telemetry messages -/

def heartbeat (t : Telemetry) : Msg :=
  let armed : UInt8 := if t.armed then 0x80 else 0
  let guided : UInt8 := if t.armed && Mode.usesPosition t.mode then 0x08 else 0
  .heartbeat { «type» := 2, autopilot := 3, base_mode := 0x51 ||| armed ||| guided,
               custom_mode := t.mode.toUInt32,
               system_status := if t.failsafe then 5 else if t.landed == .onGround then 3 else 4,
               mavlink_version := 3 }

def statusText (sev : Severity) (s : String) : Msg :=
  .statustext { severity := sev.toUInt8, text := (Bytes.ofString s).extract 0 50 }

def missionStateCode : MissionState → UInt8
  | .noMission => 1 | .notStarted => 2 | .active => 3 | .paused => 4 | .complete => 5

def landedCode : Landed → UInt8
  | .onGround => 1 | .inAir => 2 | .takeoff => 3 | .landing => 4

def missionCurrent (st : GcsState) (t : Telemetry) : Msg :=
  .missionCurrent
    { seq := t.missionSeq.toUInt16, total := st.mission.size.toUInt16,
      mission_state := if st.mission.isEmpty then 1 else missionStateCode t.missionState,
      mission_mode := if t.mode == Mode.auto then 1 else 0 }

def homePosition (cfg : GcsConfig) (t : Telemetry) : Msg :=
  let (lat, lon) := toLatLon t.origin t.home
  .homePosition
    { latitude := i32 lat, longitude := i32 lon, altitude := i32 (amslMm t.origin t.home.z),
      x := t.home.x, y := t.home.y, z := t.home.z, q := #[nanR, nanR, nanR, nanR],
      time_usec := timeUs cfg t }

def autopilotVersion (cfg : GcsConfig) : Msg :=
  -- MISSION_FLOAT | PARAM_FLOAT | MISSION_INT | COMMAND_INT | SET_POSITION_TARGET_LOCAL_NED | MAVLINK2
  .autopilotVersion
    { capabilities := 1 ||| 2 ||| 4 ||| 8 ||| 128 ||| 8192,
      flight_sw_version := cfg.swVersion, flight_custom_version := Bytes.ofString "leanfc01" |>.data,
      vendor_id := 0, product_id := 0, uid := 0 }

/-- The message `o` from the telemetry. -/
def telemetryMsg (cfg : GcsConfig) (st : GcsState) (t : Telemetry) : Out → Msg
  | .heartbeat => heartbeat t
  | .sysStatus =>
    .sysStatus
      { onboard_control_sensors_present := cfg.sensors,
        onboard_control_sensors_enabled := cfg.sensors,
        onboard_control_sensors_health := t.health &&& cfg.sensors,
        load := 0, voltage_battery := 0, current_battery := -1, battery_remaining := -1 }
  | .systemTime => .systemTime { time_unix_usec := 0, time_boot_ms := bootMs cfg t }
  | .gpsRawInt =>
    let (lat, lon) := toLatLon t.origin t.position
    let v := t.velocity
    .gpsRawInt
      { time_usec := timeUs cfg t, fix_type := 3, lat := i32 lat, lon := i32 lon,
        alt := i32 (amslMm t.origin t.position.z), eph := 100, epv := 100,
        vel := u16c (roundR (R.sqrt (v.x * v.x + v.y * v.y) * 100)),
        cog := (cdeg36000 (mid (atan2Q (ratOf v.y) (ratOf v.x)).1)).toUInt16,
        satellites_visible := 10 }
  | .attitude =>
    let (r, p, y) := euler t.attitude
    .attitude
      { time_boot_ms := bootMs cfg t, roll := r, pitch := p, yaw := y,
        rollspeed := t.rates.x, pitchspeed := t.rates.y, yawspeed := t.rates.z }
  | .attitudeQuaternion =>
    .attitudeQuaternion
      { time_boot_ms := bootMs cfg t, q1 := t.attitude.w, q2 := t.attitude.x,
        q3 := t.attitude.y, q4 := t.attitude.z, rollspeed := t.rates.x, pitchspeed := t.rates.y,
        yawspeed := t.rates.z }
  | .localPositionNed =>
    .localPositionNed
      { time_boot_ms := bootMs cfg t, x := t.position.x, y := t.position.y,
        z := t.position.z, vx := t.velocity.x, vy := t.velocity.y, vz := t.velocity.z }
  | .globalPositionInt =>
    let (lat, lon) := toLatLon t.origin t.position
    let yaw := yawQ t.attitude
    .globalPositionInt
      { time_boot_ms := bootMs cfg t, lat := i32 lat, lon := i32 lon,
        alt := i32 (amslMm t.origin t.position.z),
        relative_alt := i32 (roundR ((t.home.z - t.position.z) * 1000)),
        vx := i16 (roundR (t.velocity.x * 100)), vy := i16 (roundR (t.velocity.y * 100)),
        vz := i16 (roundR (t.velocity.z * 100)), hdg := (cdeg36000 yaw).toUInt16 }
  | .missionCurrent => missionCurrent st t
  | .navControllerOutput =>
    let d := t.target - t.position
    let dist := R.sqrt (d.x * d.x + d.y * d.y)
    .navControllerOutput
      { nav_roll := 0, nav_pitch := 0,
        nav_bearing := i16 (deg180 (mid (atan2Q (ratOf t.targetHeading.2) (ratOf t.targetHeading.1)).1)),
        target_bearing := i16 (deg360 (mid (atan2Q (ratOf d.y) (ratOf d.x)).1)),
        wp_dist := u16c (roundR dist), alt_error := d.z, aspd_error := 0, xtrack_error := 0 }
  | .vfrHud =>
    let v := t.velocity
    let yaw := yawQ t.attitude
    let gs := R.sqrt (v.x * v.x + v.y * v.y)
    .vfrHud
      { airspeed := gs, groundspeed := gs, heading := i16 (deg360 yaw),
        throttle := u16c (roundR (t.throttle * 100)),
        alt := ofRat ((amslMm t.origin t.position.z : ℚ) / 1000), climb := -v.z }
  | .extendedSysState => .extendedSysState { vtol_state := 0, landed_state := landedCode t.landed }
  | .batteryStatus =>
    -- no battery measurement: ArduPilot's "unknown" values
    .batteryStatus
      { id := 0, battery_function := 0, «type» := 0, temperature := 32767,
        voltages := Array.replicate 10 65535, current_battery := -1, current_consumed := -1,
        energy_consumed := -1, battery_remaining := -1 }
  | .homePosition => homePosition cfg t
  | .gpsGlobalOrigin =>
    .gpsGlobalOrigin
      { latitude := i32 t.origin.latE7, longitude := i32 t.origin.lonE7,
        altitude := i32 t.origin.altMm, time_usec := timeUs cfg t }
  | .autopilotVersion => autopilotVersion cfg

/-! ## Parameters -/

def paramValue (s : ParamTable.Store) (i : Nat) : Option Msg :=
  (s.get i).map fun (name, ty, v) =>
    .paramValue { param_id := Bytes.ofString name, param_value := v, param_type := ty.code,
                  param_count := ParamTable.count.toUInt16, param_index := i.toUInt16 }

def paramError (sys comp : UInt8) (name : ByteArray) (index : Int16) (err : UInt8) : Msg :=
  .paramError { target_system := sys, target_component := comp, param_id := name.extract 0 16,
                param_index := index, error := err }

/-! ## Step plumbing -/

/-- What one tick produces. -/
structure Acc where
  st : GcsState
  out : Array Msg := #[]
  cmds : Array Command := #[]
  replies : Array Reply := #[]

def Acc.send (a : Acc) (m : Msg) : Acc := { a with out := a.out.push m }
def Acc.cmd (a : Acc) (c : Command) (r : Reply) : Acc :=
  { a with cmds := a.cmds.push c, replies := a.replies.push r }
def Acc.text (a : Acc) (sev : Severity) (s : String) : Acc :=
  { a with st := { a.st with texts := a.st.texts.push (sev, s) } }
def Acc.banner (cfg : GcsConfig) (a : Acc) : Acc := cfg.banner.foldl (fun a s => a.text 6 s) a

def commandAck (cmd : UInt16) (res : UInt8) (sys comp : UInt8) : Msg :=
  .commandAck { command := cmd, result := res, target_system := sys, target_component := comp }

def missionAck (sys comp : UInt8) (ty res : UInt8) : Msg :=
  .missionAck { target_system := sys, target_component := comp, «type» := res, mission_type := ty }

/-- Set the interval of `o` to `ticks` (0: off), due now. -/
def setInterval (st : GcsState) (now : Nat) (o : Out) (ticks : Nat) : GcsState :=
  { st with intervals := st.intervals.set! o.index ticks, due := st.due.set! o.index now }

/-- The default interval of a message (ArduCopter: every stream rate 0; HEARTBEAT 1 Hz). -/
def defaultTicks (o : Out) : Nat := if o == .heartbeat then 400 else 0

/-! ## Commands -/

/-- A command from COMMAND_LONG or COMMAND_INT, parameters 5 and 6 kept in both forms. -/
structure Cmd where
  command : UInt16
  p1 : R
  p2 : R
  p3 : R
  p4 : R
  /-- COMMAND_LONG param5/param6 (degrees) or COMMAND_INT x/y (degrees · 1e7) as integers ·1e7 -/
  latE7 : Int
  lonE7 : Int
  z : R
  /-- COMMAND_INT frame; COMMAND_LONG: GLOBAL_RELATIVE_ALT (3), as ArduPilot -/
  frame : UInt8
  isInt : Bool

def isInt (x : R) (n : Int) : Bool := ratOf x == (n : ℚ)

/-- Down coordinate of a command's altitude in its frame (absolute or relative to home). -/
def cmdDown (t : Telemetry) (c : Cmd) : Option R :=
  if c.frame == 0 || c.frame == 5 then some (downOfAmsl t.origin c.z)
  else if c.frame == 3 || c.frame == 6 then some (t.home.z - c.z)
  else none

/-- The point of a command's location; latitude = longitude = 0 means the current position. -/
def cmdPoint (t : Telemetry) (c : Cmd) : Option Vec3 :=
  (cmdDown t c).map fun d =>
    if c.latE7 == 0 && c.lonE7 == 0 then { t.position with z := d }
    else let (n, e) := toNE t.origin c.latE7 c.lonE7; ⟨n, e, d⟩

/-- A COMMAND_LONG / COMMAND_INT from `inc`. -/
def command (cfg : GcsConfig) (t : Telemetry) (inc : Incoming) (c : Cmd) (a : Acc) : Acc :=
  let ack (res : UInt8) (a : Acc) := a.send (commandAck c.command res inc.sysid inc.compid)
  let toVehicle (cmd : Command) (a : Acc) := a.cmd cmd (.commandAck c.command inc.sysid inc.compid)
  let now := t.tick
  match c.command.toNat with
  | 400 => -- COMPONENT_ARM_DISARM
    if isInt c.p1 1 then toVehicle (.arm (isInt c.p2 2989 || isInt c.p2 21196)) a
    else if isInt c.p1 0 then toVehicle (.disarm (isInt c.p2 21196)) a
    else ack resUnsupported a
  | 176 => -- DO_SET_MODE
    if (roundR c.p1) % 2 == 1 then toVehicle (.setMode (roundR c.p2).toNat) a else ack resDenied a
  | 22 => -- NAV_TAKEOFF (altitude above home in param7)
    if c.isInt && c.frame != 3 then ack resDenied a else toVehicle (.takeoff c.z) a
  | 300 => -- MISSION_START
    if !(isInt c.p1 0 && isInt c.p2 0) then ack resDenied a else toVehicle .missionStart a
  | 21 => toVehicle .land a                 -- NAV_LAND
  | 20 => toVehicle .returnToLaunch a       -- NAV_RETURN_TO_LAUNCH
  | 179 => -- DO_SET_HOME: param1 1 or no location = current position
    if isInt c.p1 1 || (c.latE7 == 0 && c.lonE7 == 0) then toVehicle (.setHome none) a
    else if !isInt c.p1 0 then ack resFailed a
    else
      let c' := if c.isInt then c else { c with frame := 0 }  -- COMMAND_LONG: altitude AMSL
      match cmdPoint t c' with
      | some p => toVehicle (.setHome (some p)) a
      | none => ack resDenied a
  | 192 => -- DO_REPOSITION (COMMAND_INT only)
    if !c.isInt then ack resCommandIntOnly a else
    let changeMode := (roundR c.p2) % 2 == 1
    if !changeMode && t.mode != Mode.guided then ack resDenied a else
    match cmdPoint t c with
    | some p => toVehicle (.goTo p changeMode) a
    | none => ack resDenied a
  | 178 => -- DO_CHANGE_SPEED (param2 m/s)
    if c.p2 > 0 then toVehicle (.changeSpeed c.p2) a else ack resDenied a
  | 224 => -- DO_SET_MISSION_CURRENT
    let s := roundR c.p1
    if s ≥ 1 && s ≤ a.st.mission.size then toVehicle (.setCurrent s.toNat) a else ack resFailed a
  | 410 => -- GET_HOME_POSITION
    let a := ack resAccepted a
    { a with st := { a.st with requested := a.st.requested ++ #[.homePosition, .gpsGlobalOrigin] } }
  | 520 => -- REQUEST_AUTOPILOT_CAPABILITIES
    if isInt c.p1 1 then
      let a := ack resAccepted a
      { a with st := { a.st with requested := a.st.requested.push .autopilotVersion } }
    else ack resFailed a
  | 512 => -- REQUEST_MESSAGE (param1 msgid; MESSAGE_INTERVAL: param2 the msgid asked about)
    let id := (roundR c.p1).toNat
    if id == 244 then
      let q := (roundR c.p2).toNat
      match Out.ofMsgid q with
      | some o =>
        let iv := a.st.intervals.getD o.index 0
        let a := ack resAccepted a
        a.send (.messageInterval
          { message_id := q.toUInt16,
            interval_us := if iv == 0 then -1 else Int32.ofInt (iv * cfg.tickUs) })
      | none => ack resUnsupported a
    else match Out.ofMsgid id with
      | some o =>
        let a := ack resAccepted a
        { a with st := { a.st with requested := a.st.requested.push o } }
      | none => ack resUnsupported a
  | 511 => -- SET_MESSAGE_INTERVAL (param1 msgid, param2 µs: -1 off, 0 default)
    match Out.ofMsgid (roundR c.p1).toNat with
    | none => ack resDenied a
    | some o =>
      let us := roundR c.p2
      if !isInt c.p3 0 || us < -1 then ack resDenied a else
      let ticks := if us == -1 then 0 else if us == 0 then defaultTicks o
        else max 1 (us.toNat / cfg.tickUs)
      let a := ack resAccepted a
      { a with st := setInterval a.st now o ticks }
  | 510 => -- GET_MESSAGE_INTERVAL
    match Out.ofMsgid (roundR c.p1).toNat with
    | some o =>
      let iv := a.st.intervals.getD o.index 0
      let a := a.send (.messageInterval
        { message_id := o.msgid.toUInt16,
          interval_us := if iv == 0 then -1 else Int32.ofInt (iv * cfg.tickUs) })
      ack resAccepted a
    | none => ack resFailed a
  | 42428 => (ack resAccepted a).banner cfg  -- DO_SEND_BANNER
  | _ => ack resUnsupported a

/-! ## Mission protocol -/

/-- Request item `seq` of the upload in progress. -/
def requestItem (now : Nat) (u : Upload) (a : Acc) : Acc :=
  let a := a.send (.missionRequestInt
    { target_system := u.sys, target_component := u.comp,
      seq := u.next.toUInt16, mission_type := 0 })
  { a with st := { a.st with upload := some { u with lastReq := now } } }

/-- The vehicle's form of the stored mission (items that do not convert are skipped; uploads
reject them, so a stored mission converts entirely). -/
def missionCmds (t : Telemetry) (items : Array MissionItemInt) : Array MissionCmd :=
  items.filterMap fun it => match Mission.toCmd t.origin t.home it with
    | .ok c => some c
    | .error _ => none

/-- A MISSION_ITEM_INT with current 2 (go to) or 3 (change altitude) in GUIDED. -/
def guidedItem (t : Telemetry) (inc : Incoming) (it : MissionItemInt) (a : Acc) : Acc :=
  let c : Cmd :=
    { command := it.command, p1 := it.param1, p2 := it.param2, p3 := it.param3,
      p4 := it.param4, latE7 := it.x.toInt, lonE7 := it.y.toInt, z := it.z, frame := it.frame, isInt := true }
  let target :=
    if it.current == 3 then (cmdDown t c).map fun d => { t.position with z := d } else cmdPoint t c
  match target with
  | some p => a.cmd (.goTo p false) (.missionAck inc.sysid inc.compid)
  | none => a.send (missionAck inc.sysid inc.compid 0 Mission.unsupportedFrame)

/-- One uploaded item. -/
def uploadItem (t : Telemetry) (inc : Incoming) (it : MissionItemInt) (a : Acc) : Acc :=
  let now := t.tick
  if it.current == 2 || it.current == 3 then guidedItem t inc it a else
  if it.mission_type != 0 then a.send (missionAck inc.sysid inc.compid it.mission_type Mission.unsupported) else
  match a.st.upload with
  | none => a.send (missionAck inc.sysid inc.compid 0 1)  -- ERROR: not receiving
  | some u =>
    if inc.sysid != u.sys || inc.compid != u.comp then a.send (missionAck inc.sysid inc.compid 0 14)
    else if it.seq.toNat != u.next then a.send (missionAck u.sys u.comp 0 13)  -- INVALID_SEQUENCE
    else
      let check := if it.seq == 0 then .ok .rtl else Mission.toCmd t.origin t.home it
      match check with
      | .error e =>
        let a := a.send (missionAck u.sys u.comp 0 e)
        { a with st := { a.st with upload := none } }
      | .ok _ =>
        let u := { u with items := if it.seq == 0 then u.items else u.items.push it,
                          next := u.next + 1, lastRecv := now }
        if u.next < u.count then requestItem now u a
        else
          let a := a.send (missionAck u.sys u.comp 0 0)
          let a := a.text 6 "Flight plan received"
          let a := { a with st := { a.st with upload := none, mission := u.items } }
          a.cmd (.setMission (missionCmds t u.items)) .none

/-- A received message. -/
def handle (cfg : GcsConfig) (t : Telemetry) (inc : Incoming) (a : Acc) : Acc :=
  let forMe (sys : UInt8) := sys == 0 || sys == cfg.sysid
  let forMeC (sys comp : UInt8) := forMe sys && (comp == 0 || comp == cfg.compid)
  let now := t.tick
  let first := !a.st.contact
  let a := if first then ({ a with st := { a.st with contact := true } }).banner cfg else a
  match inc.msg with
  | .heartbeat m => if m.«type» == 6 then { a with st := { a.st with gcsSeen := some now } } else a
  | .paramRequestList m =>
    if !forMe m.target_system then a else
    let a := if first then a else a.banner cfg
    { a with st := { a.st with paramNext := some 0, paramDue := now } }
  | .paramRequestRead m =>
    if !forMe m.target_system then a else
    let idx := if m.param_index.toInt ≥ 0 then some m.param_index.toInt.toNat
      else ParamTable.Store.indexOf (Bytes.toString m.param_id)
    match idx.bind (paramValue a.st.params) with
    | some v => a.send v
    | none => a.send (paramError inc.sysid inc.compid m.param_id m.param_index 1)
  | .paramSet m =>
    if !forMeC m.target_system m.target_component then a else
    let name := Bytes.toString m.param_id
    match ParamTable.Store.indexOf name with
    | none => a.send (paramError inc.sysid inc.compid m.param_id (-1) 1)
    | some i =>
      if !Mission.isFinite m.param_value then a.send (paramError inc.sysid inc.compid m.param_id (-1) 2)
      else match a.st.params.set i m.param_value with
        | .ok s =>
          let a := { a with st := { a.st with params := s } }
          let a := match paramValue s i with | some v => a.send v | none => a
          if i < ParamTable.entries.size then a.cmd (.setParams s.params) .none else a
        | .error e =>
          let a := a.text 4 (String.ofList (s!"Param write denied ({name}): {e}".toList.take 50))
          match paramValue a.st.params i with | some v => a.send v | none => a
  | .commandLong m =>
    if !forMeC m.target_system m.target_component then a else
    command cfg t inc
      { command := m.command, p1 := m.param1, p2 := m.param2, p3 := m.param3,
        p4 := m.param4, latE7 := roundQ (ratOf m.param5 * 10000000),
        lonE7 := roundQ (ratOf m.param6 * 10000000), z := m.param7, frame := 3, isInt := false } a
  | .commandInt m =>
    if !forMeC m.target_system m.target_component then a else
    command cfg t inc
      { command := m.command, p1 := m.param1, p2 := m.param2, p3 := m.param3,
        p4 := m.param4, latE7 := m.x.toInt, lonE7 := m.y.toInt, z := m.z, frame := m.frame,
        isInt := true } a
  | .setMode m =>
    if m.target_system == cfg.sysid && m.base_mode &&& 1 == 1 then
      a.cmd (.setMode m.custom_mode.toNat) .none
    else a
  | .requestDataStream m =>
    if !forMe m.target_system then a else
    let ticks := if m.start_stop == 0 || m.req_message_rate == 0 then 0
      else max 1 (400 / m.req_message_rate.toNat)
    let id := m.req_stream_id.toNat
    let st := Out.all.foldl (fun st o =>
      if o.group != 0 && (id == 0 || o.group == id) then setInterval st now o ticks else st) a.st
    { a with st }
  | .setPositionTargetLocalNed m =>
    -- position only (velocity, acceleration and yaw bits set in type_mask), LOCAL_NED or LOCAL_OFFSET_NED
    if !forMe m.target_system || m.type_mask &&& 7 != 0 then a
    else if m.coordinate_frame == 1 then a.cmd (.goTo ⟨m.x, m.y, m.z⟩ false) .none
    else if m.coordinate_frame == 7 then a.cmd (.goTo (t.position + ⟨m.x, m.y, m.z⟩) false) .none
    else a
  | .missionCount m =>
    if !forMe m.target_system then a else
    if m.mission_type == 1 || m.mission_type == 2 then
      a.send (missionAck inc.sysid inc.compid m.mission_type (if m.count == 0 then 0 else 4))
    else if m.mission_type != 0 then a.send (missionAck inc.sysid inc.compid m.mission_type 3)
    else if m.count == 0 then
      let a := a.send (missionAck inc.sysid inc.compid 0 0)
      let a := { a with st := { a.st with upload := none, mission := #[] } }
      (a.text 6 "Flight plan received").cmd (.setMission #[]) .none
    else
      requestItem now
        { count := m.count.toNat, next := 0, sys := inc.sysid, comp := inc.compid,
          items := #[], lastRecv := now, lastReq := now } a
  | .missionItemInt m => if !forMe m.target_system then a else uploadItem t inc m a
  | .missionItem m =>
    -- legacy float item (QGroundControl's guided "go to" uses it): degrees → degrees · 1e7
    if !forMe m.target_system then a else
    uploadItem t inc
      { target_system := m.target_system, target_component := m.target_component,
        seq := m.seq, frame := m.frame, command := m.command, current := m.current,
        autocontinue := m.autocontinue, param1 := m.param1, param2 := m.param2, param3 := m.param3,
        param4 := m.param4, x := i32 (roundQ (ratOf m.x * 10000000)),
        y := i32 (roundQ (ratOf m.y * 10000000)), z := m.z, mission_type := m.mission_type } a
  | .missionRequestList m =>
    if !forMe m.target_system then a else
    let n := if m.mission_type == 0 then a.st.mission.size + 1 else 0
    if m.mission_type > 2 then a.send (missionAck inc.sysid inc.compid m.mission_type 3) else
    if m.mission_type == 0 && a.st.upload.isSome then a.send (missionAck inc.sysid inc.compid 0 14) else
    a.send (.missionCount
      { target_system := inc.sysid, target_component := inc.compid,
        count := n.toUInt16, mission_type := m.mission_type })
  | .missionRequestInt m =>
    if !forMe m.target_system || m.mission_type != 0 then a else
    let s := m.seq.toNat
    if s == 0 then
      a.send (.missionItemInt
        { Mission.homeItem t.origin t.home with
          target_system := inc.sysid, target_component := inc.compid })
    else match a.st.mission[s - 1]? with
      | some it => a.send (.missionItemInt
        { Mission.downloadItem it s with
          target_system := inc.sysid, target_component := inc.compid })
      | none => a.send (missionAck inc.sysid inc.compid 0 13)
  | .missionRequest m =>
    -- deprecated: answered with the float MISSION_ITEM (degrees)
    if !forMe m.target_system || m.mission_type != 0 then a else
    let s := m.seq.toNat
    let it? := if s == 0 then some (Mission.homeItem t.origin t.home)
      else (a.st.mission[s - 1]?).map (Mission.downloadItem · s)
    match it? with
    | some it => a.send (.missionItem
      { target_system := inc.sysid, target_component := inc.compid,
        seq := it.seq, frame := it.frame, command := it.command, current := 0,
        autocontinue := it.autocontinue, param1 := it.param1, param2 := it.param2,
        param3 := it.param3, param4 := it.param4, x := ofRat ((it.x.toInt : ℚ) / 10000000),
        y := ofRat ((it.y.toInt : ℚ) / 10000000), z := it.z, mission_type := 0 })
    | none => a.send (missionAck inc.sysid inc.compid 0 13)
  | .missionClearAll m =>
    if !forMe m.target_system then a else
    if m.mission_type == 1 || m.mission_type == 2 then a.send (missionAck inc.sysid inc.compid m.mission_type 0)
    else if m.mission_type != 0 then a.send (missionAck inc.sysid inc.compid m.mission_type 3)
    else if t.armed && t.mode == Mode.auto then a.send (missionAck inc.sysid inc.compid 0 1)
    else
      let a := a.send (missionAck inc.sysid inc.compid 0 0)
      { a with st := { a.st with mission := #[], upload := none } }.cmd (.setMission #[]) .none
  | .missionSetCurrent m =>
    if !forMe m.target_system then a else
    let s := m.seq.toNat
    if s ≥ 1 && s ≤ a.st.mission.size then a.cmd (.setCurrent s) .none else a
  | .missionAck _ => a
  | .timesync m =>
    if m.tc1 == 0 then
      a.send (.timesync
        { tc1 := Int64.ofInt (t.tick * cfg.tickUs * 1000), ts1 := m.ts1,
          target_system := inc.sysid, target_component := inc.compid })
    else a
  | .ping m =>
    if m.target_system == 0 && m.target_component == 0 then
      a.send (.ping
        { time_usec := m.time_usec, seq := m.seq, target_system := inc.sysid,
          target_component := inc.compid })
    else a
  | .fileTransferProtocol m =>
    if m.target_system != cfg.sysid then a else
    -- payload: seq u16, session u8, opcode u8, size u8, req_opcode u8, burst u8, pad u8, offset u32
    let p := m.payload
    let seq := (p.getD 0 0).toUInt16 ||| ((p.getD 1 0).toUInt16 <<< 8)
    let opcode := p.getD 3 0
    let (rsp, err?) : UInt8 × Option UInt8 :=
      if opcode ≤ 2 then (128, none)                                   -- none, terminate, reset: ACK
      else if opcode == 5 || opcode == 7 || opcode == 15 then (129, some 4)  -- no open session
      else (129, some 10)                                               -- FileNotFound
    let seq' := seq + 1
    let hdr : Array UInt8 := #[seq'.toUInt8, (seq' >>> 8).toUInt8, p.getD 2 0, rsp,
      if err?.isSome then 1 else 0, opcode, 0, 0, 0, 0, 0, 0]
    let body := hdr ++ (match err? with | some e => #[e] | none => #[])
    a.send (.fileTransferProtocol
      { target_network := 0, target_system := inc.sysid,
        target_component := inc.compid, payload := Bytes.padded 251 0 body })
  | _ => a

/-! ## The tick -/

/-- Messages that follow the vehicle's state: HEARTBEAT on an arm or mode change, MISSION_CURRENT
on a change of the current item, MISSION_ITEM_REACHED. -/
def onChange (t : Telemetry) (a : Acc) : Acc :=
  let cur := (t.armed, t.mode, t.missionSeq)
  let a := match a.st.last with
    | some (arm, mode, seq) =>
      let a := if arm != t.armed || mode != t.mode then a.send (heartbeat t) else a
      if seq != t.missionSeq then a.send (missionCurrent a.st t) else a
    | none => a
  let a := match t.reached with
    | some s => a.send (.missionItemReached { seq := s.toUInt16 })
    | none => a
  { a with st := { a.st with last := some cur } }

/-- Streams due this tick, then single requested messages. -/
def streams (cfg : GcsConfig) (t : Telemetry) (a : Acc) : Acc :=
  let now := t.tick
  let a := Out.all.foldl (fun a o =>
    let iv := a.st.intervals.getD o.index 0
    if iv == 0 || now < a.st.due.getD o.index 0 then a
    else
      let a := a.send (telemetryMsg cfg a.st t o)
      { a with st := { a.st with due := a.st.due.set! o.index (now + iv) } }) a
  let a := a.st.requested.foldl (fun a o => a.send (telemetryMsg cfg a.st t o)) a
  { a with st := { a.st with requested := #[] } }

/-- The next PARAM_VALUE of a list, the next status text, the upload's retry and timeout. -/
def background (cfg : GcsConfig) (t : Telemetry) (a : Acc) : Acc :=
  let now := t.tick
  let a := match a.st.paramNext with
    | some i =>
      if now < a.st.paramDue then a else
      match paramValue a.st.params i with
      | some v =>
        let a := a.send v
        { a with st := { a.st with paramNext := some (i + 1), paramDue := now + cfg.paramTicks } }
      | none => { a with st := { a.st with paramNext := none } }
    | none => a
  let a := match a.st.texts[0]? with
    | some (sev, s) =>
      let a := a.send (statusText sev s)
      { a with st := { a.st with texts := a.st.texts.extract 1 } }
    | none => a
  match a.st.upload with
  | some u =>
    if now ≥ u.lastRecv + cfg.missionTimeoutTicks then
      let a := a.send (missionAck u.sys u.comp 0 15)
      { a with st := { a.st with upload := none } }.text 4 "Mission upload timeout"
    else if now ≥ u.lastReq + cfg.missionRetryTicks then requestItem now u a
    else a
  | none => a

/-- One tick of the services. -/
def step (cfg : GcsConfig) (st : GcsState) (t : Telemetry) (incoming : Option Incoming) :
    GcsState × Array Msg × Array Command :=
  -- replies to last tick's commands, from the vehicle's results
  let a : Acc := { st := { st with pending := #[] } }
  let a := st.pending.zipIdx.foldl (fun a (r, i) =>
    let res := resultCode (t.results.getD i .failed)
    match r with
    | .none => a
    | .commandAck c sys comp => a.send (commandAck c res sys comp)
    | .missionAck sys comp => a.send (missionAck sys comp 0 (if res == resAccepted then 0 else 1))) a
  let a := t.texts.foldl (fun a (sev, s) => a.text sev s) a
  let a := match incoming with
    | some inc => if inc.sysid == cfg.sysid then a else handle cfg t inc a
    | none => a
  let a := onChange t a
  let a := streams cfg t a
  let a := background cfg t a
  ({ a.st with pending := a.replies }, a.out, a.cmds)

end Gcs

end Mavlink
