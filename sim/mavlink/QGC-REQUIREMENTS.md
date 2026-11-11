# What QGroundControl 5.1.5 requires of an ArduPilot multicopter, and what leanfc does

Source: QGroundControl tag `v5.1.5` (commit 3a67d31f), the installed `/Applications/QGroundControl.app`.
It was exported read-only to `sim/mavlink/qgc-5.1.5/src` (`git archive v5.1.5 src`; in this tree a link
to the export in `/Users/ryan/Research/leanfc-mavlink`; git-ignored). Paths below are relative to `src/`, and line numbers are those of 5.1.5. The last section lists
where the development branch (v5.2.0-dev-244, in `/Users/ryan/Research/delegate/qgroundcontrol`) differs.

Status codes:

- **impl**: implemented and exercised by `sim/mavlink/test_services.py`.
- **impl, observed**: also seen working with the real QGroundControl 5.1.5 (`sim/mavlink/run_qgc.py`). The
  first observations were made against the kinematic stand-in vehicle of the separate clone
  (`/Users/ryan/Research/leanfc-mavlink/sim/mavlink/out/qgc-run*/`); the connect sequence was observed again
  against the real controller in the real-time simulation (`sim/mavlink/out/qgc-real1/`).
- **stub**: answered so that QGroundControl stops cleanly, with no feature behind the answer.
- **not impl**: not implemented; the consequence is stated.

## Items QGroundControl uses that are not implemented

| item | consequence |
|---|---|
| MAV_CMD_CONDITION_YAW ("change heading" in the Fly view, `APMFirmwarePlugin.cc` guidedModeChangeHeading) | COMMAND_ACK UNSUPPORTED, so QGroundControl shows its "command not supported" error. The heading would need a sine and cosine of the requested angle in the services. |
| Mission commands other than NAV_WAYPOINT, NAV_SPLINE_WAYPOINT, NAV_TAKEOFF, NAV_LAND and NAV_RETURN_TO_LAUNCH (DO_CHANGE_SPEED items, loiters, DO_JUMP, camera items, ...) | The upload ends with MISSION_ACK UNSUPPORTED and QGroundControl reports "Mission transfer failed". |
| Terrain frames (GLOBAL_TERRAIN_ALT) | MISSION_ACK UNSUPPORTED_FRAME, as ArduPilot without terrain support answers. |
| Geofence and rally points | Not advertised (no MISSION_FENCE or MISSION_RALLY capability), so QGroundControl skips loading them and hides them in the Plan view. If asked anyway, the lists are empty. |
| MAVLink FTP (parameter file, logs) | Every request is refused, and QGroundControl falls back to PARAM_REQUEST_LIST at once. No onboard logs. |
| Gimbal, camera, ADS-B, RC_CHANNELS, SERVO_OUTPUT_RAW, VIBRATION, EKF_STATUS_REPORT, AVAILABLE_MODES | Not sent. The matching widgets stay empty. The gimbal probe (six REQUEST_MESSAGE GIMBAL_MANAGER_INFORMATION) is answered UNSUPPORTED. |
| Battery measurement | BATTERY_STATUS carries ArduPilot's "unknown" values (-1, 65535 cells), so the battery widget shows no value. It is still sent at QGroundControl's rate, which stops QGroundControl re-requesting streams. |
| Vehicle Setup pages beyond the summaries (motor test, calibrations, ESC, servo outputs) | The parameters they read are compatibility values with nothing behind them. A calibration started there does nothing. |
| MAVLink signing | Signed frames are checked and skipped. QGroundControl does not sign by default. |

## Connect: what QGroundControl does by itself

| # | QGroundControl request (5.1.5 source) | response needed | if missing or wrong | leanfc | status |
|---|---|---|---|---|---|
| 1 | Creates a vehicle on a HEARTBEAT from component 1. GCS, ONBOARD_CONTROLLER, GIMBAL and ADSB types are ignored, and so is sysid 0 (`Vehicle/MultiVehicleManager.cc:68-114`). The plugin is chosen by autopilot, and ARDUPILOTMEGA + QUADROTOR gives ArduCopterFirmwarePlugin (`FirmwarePlugin/APM/APMFirmwarePluginFactory.cc`). | HEARTBEAT 1 Hz from 1/1: type 2, autopilot 3, base_mode with CUSTOM_MODE_ENABLED | no vehicle, or the PX4/generic plugin | HEARTBEAT 1 Hz and on every arm or mode change. base_mode follows ArduCopter's GCS_MAVLink_Copter.cpp. | impl, observed |
| 2 | Communication is lost after 3.5 s without a heartbeat (`Vehicle/VehicleLinkManager.h:85`). | heartbeats | "communication lost" | 1 Hz | impl, observed |
| 3 | MAVLink 1 frames other than HEARTBEAT and RADIO_STATUS are dropped (`Comms/MAVLinkProtocol.cc:128-134`). Without MAVLink 2 within 10 s it shows a warning (`Comms/LinkInterface.cc:184-208`). | MAVLink 2 | messages ignored, then the "MAVLink v1 traffic" warning | MAVLink 2 only (MAVLink 1 is parsed on input) | impl, observed |
| 4 | Stream setup at vehicle creation (`FirmwarePlugin/APM/APMFirmwarePlugin.cc:385-435`): REQUEST_DATA_STREAM, each sent 5 times, with RAW_SENSORS 2, EXTENDED_STATUS 2, RC_CHANNELS 2, POSITION 3, EXTRA1 10, EXTRA2 10, EXTRA3 3 Hz. Then SET_MESSAGE_INTERVAL for HOME_POSITION and EXTENDED_SYS_STATE at 1 s, with errors not shown. | the streams at those rates; COMMAND_ACK | no telemetry | ArduPilot's stream groups for the supported messages, with ACK ACCEPTED. Measured rates are in the test output. | impl, observed |
| 5 | Stream re-initialisation (`APMFirmwarePlugin.cc:288-326`): everything in item 4 is sent again about every 10 s while BATTERY_STATUS or HOME_POSITION has not been seen for 10 s. | BATTERY_STATUS and HOME_POSITION at least every 10 s | repeated stream requests (no dialog) | BATTERY_STATUS in EXTRA3 (3 Hz), HOME_POSITION 1 Hz | impl, observed (35 REQUEST_DATA_STREAM in 75 s = the initial 7×5 only) |
| 6 | `InitialConnectStateMachine` (`Vehicle/InitialConnectStateMachine.cc:49-151`), state AutopilotVersion: REQUEST_MESSAGE(148) to component 1. It needs ACK ACCEPTED and the message within 1 s of the ACK (`Vehicle/RequestMessageCoordinator.cc:202-246`). Two attempts, with a 5 s state timeout. | COMMAND_ACK ACCEPTED, then AUTOPILOT_VERSION | after the retries QGroundControl assumes MAVLINK2, MISSION_INT, COMMAND_INT, FENCE and RALLY (it would then ask for fence and rally) | ACK, then AUTOPILOT_VERSION in the same tick. Capabilities MISSION_FLOAT, PARAM_FLOAT, MISSION_INT, COMMAND_INT, SET_POSITION_TARGET_LOCAL_NED, MAVLINK2 (8335). flight_sw_version 4.7.0 type DEV. | impl, observed (6 ms) |
| 7 | With AUTOPILOT_VERSION it also runs `checkIfIsLatestStable` (`FirmwarePlugin.cc:304-362`). If the version type is OFFICIAL and older than the stable release downloaded from firmware.ardupilot.org, it shows "Vehicle is not running latest stable firmware!". | a non-OFFICIAL type | the dialog | type DEV (0) | impl, observed (it logged "Latest stable version = 4.7.2" and showed nothing) |
| 8 | 4.7 also selects the parameter-name remapping (`ArduCopterFirmwarePlugin.cc:68-160`, WP_SPD, RTL_ALT_M, PILOT_TKO_ALT_M, ...) and the metadata file `APMParameterFactMetaData.Copter.4.7.json` (`APMFirmwarePlugin.cc:700-745`). | names consistent with 4.7 | wrong metadata or missing names | ArduPilot 4.7/4.8 names | impl, observed |
| 9 | StandardModes: REQUEST_MESSAGE(AVAILABLE_MODES=435, param2 1) (`Vehicle/StandardModes.cc:114-136`). It ends at once on any non-ACCEPTED ACK. | UNSUPPORTED, or the modes | about 3.6 s waiting on silence | UNSUPPORTED. QGroundControl then uses its static ArduCopter mode table. | stub, observed |
| 10 | Component information: REQUEST_MESSAGE(COMPONENT_METADATA=397), then (395) (`Vehicle/ComponentInformation/RequestMetaDataTypeStateMachine.cc:234-325`). Timeouts 5/30/15 s. | UNSUPPORTED to both | up to 50 s of waiting | UNSUPPORTED | stub, observed |
| 11 | Parameters: for ArduPilot it first tries FTP (`FactSystem/ParameterManager.cc:42, 647-664`, `Vehicle/FTPManager.cc`): OpenFileRO "@PARAM/param.pck?withdefaults=1", seq 1, to component 1. While that is pending it ignores everything from component 1 in the parameter manager (`ParameterManager.cc:101-102`). | NAK: opcode 129, req_opcode 4, seq = request seq + 1, size 1, data[0] = 10 (FileNotFound) (`FTPManager.cc:725-797`) | without an answer: two 1 s attempts 5 s apart, then the fallback, about 12 s later | exactly that NAK. ResetSessions and Terminate get an ACK, and read requests InvalidSession. | stub, observed ("No Parameterfile on vehicle - Start Conventional Parameter Download", 3 ms) |
| 12 | PARAM_REQUEST_LIST (target component 0). A 5 s list timeout with up to 4 resends, then "Vehicle 1 did not respond to request for parameters" (`ParameterManager.cc:676-697, 1381-1406`). The count is taken from the first PARAM_VALUE (`:176-188`). | PARAM_VALUE for every index, the count constant, ArduPilot encoding (numeric float, `APMFirmwarePlugin.cc:128-185`) | missing parameters (item 13) | all 160 (80 leanfc + 80 compatibility; 159 before `nav.yawReverse`), 50 per second, in index order | impl, observed (with the stand-in: all 147 of that time in 2.3 s; with the real controller: see `sim/mavlink/out/qgc-real1/`) |
| 13 | Gap filling: after 3 s of silence, PARAM_REQUEST_READ by index for the missing indices, up to 11 at a time, 1 s wait, 2 resends, 5 rounds (`ParameterManager.cc:824-1050`). Indices still missing give "QGC was unable to retrieve the full set of parameters". | PARAM_VALUE with the real index | the dialog | PARAM_REQUEST_READ by index and by name, with the real index in the reply | impl (5 dropped values recovered in the test) |
| 14 | `parametersReadyPreChecks` (`AutoPilotPlugins/AutoPilotPlugin.cc:45-62`): if a setup component is incomplete, it shows "Configuration tasks remain before this vehicle is ready to fly". The checks: Airframe FRAME_CLASS ≠ 0 if present (`APMAirframeComponent.cc:10-33`). Radio RCMAP_ROLL/PITCH/YAW/THROTTLE > 0, and one mapped channel off 1100/1900/1500 (`APMRadioComponent.cc:6-70`). Sensors: per COMPASS_DEV_IDn ≠ 0 with COMPASS_USEn, all three offsets ≠ 0, and INS_ACCOFFS_X/Y/Z not all 0 (`APMSensorsComponent.cc:25-82`). | those parameters with "done" values | the dialog | compatibility table: FRAME_CLASS 1, FRAME_TYPE 1, RCMAP 1-4, RC1..RC4 MIN 1000 MAX 2000 TRIM 1500 (RC3 TRIM 1000), COMPASS_DEV_ID* 0 (no compass to calibrate), INS_ACCOFFS_* 0.001 | impl (source; dialogs are not logged) |
| 15 | Unguarded parameter reads produce "Parameters are missing from firmware..." (`ParameterManager.cc:798-807`, `QGCApplication.cc:368-398`). At connect they come from the components of item 14. In the toolbar's expanded indicators (`APMFirmwarePlugin.cc:1398-1408`, `APMBatteryIndicator.qml`, `APMMainStatusIndicator.qml`, `APMFlightModeIndicator.qml`) they are BATT_MONITOR, BATT_FS_LOW_ACT, BATT_LOW_VOLT, BATT_LOW_MAH, BATT_FS_CRT_ACT, BATT_CRT_VOLT, BATT_CRT_MAH, FS_GCS_ENABLE, FS_GCS_TIMEOUT, FS_OPTIONS, RTL_ALT_M. In the setup summaries they are FLTMODE1..6, FLTMODE_CH and BATT_MONITOR. On the Sensors page they are COMPASS_*, INS_ACC*_ID, BARO*_DEVID, AHRS_ORIENTATION, and on the tuning channel selector RC7..12_OPTION. | the parameters | the dialog listing them | all present in the compatibility table, with ArduPilot's defaults | impl (source) |
| 16 | After parameters: SYSTEM_TIME, twice in each of two places (`InitialConnectStateMachine.cc:436-441`, `Vehicle.cc:1668-1710`). | none | none | ignored | impl, observed |
| 17 | Mission download (`MissionManager/PlanManager.cc:123-480`): MISSION_REQUEST_LIST (1.5 s, 6 retries), then MISSION_COUNT. Then MISSION_REQUEST_INT per item (250 ms, 6 retries). Only MISSION_ITEM_INT is accepted (`:644-686`). It ends with MISSION_ACK. | count including home; item 0 = home | "Mission transfer failed" | count = stored items + 1. Item 0 is home (frame GLOBAL, AMSL); the rest are stored items with the INT frames folded (ArduPilot) | impl, observed (5 items) |
| 18 | Fence and rally loads run only with the MISSION_FENCE or MISSION_RALLY capability (`InitialConnectStateMachine.cc:130, 151`). The Plan view uses the same gate (`PlanMasterController.cc:236-297`). | the capability bits off, or proper lists | a load error dialog on an error ACK | bits off (skipped). If asked: MISSION_COUNT 0, an upload of 0 items is ACCEPTED, more is NO_SPACE | impl, observed ("Skipping geofence load (not supported by vehicle)") |
| 19 | Gimbal probe after connect: REQUEST_MESSAGE GIMBAL_MANAGER_INFORMATION (280) once per heartbeat, six times (`Gimbal/GimbalController.cc:79-93`). | an ACK | six retries over time | UNSUPPORTED | stub, observed (six requests, then it stopped) |

## Fly view

| request (5.1.5 source) | response needed | if missing | leanfc | status |
|---|---|---|---|---|
| Vehicle position and altitude: GLOBAL_POSITION_INT; lat/lon 0 is ignored for position (`Vehicle.cc:861-887`) | lat/lon 1e7, alt AMSL mm, relative_alt mm, hdg cdeg | no map icon | from the vehicle's NED position via the origin (integers, cos(lat) supplied) | impl, observed (map plan bounding box at CMAC) |
| Attitude: ATTITUDE, or ATTITUDE_QUATERNION, after which ATTITUDE is ignored (`FactGroups/VehicleFactGroup.cc:129-145`) | rad | flat instrument | ATTITUDE (EXTRA1) from certified FloatLib enclosures. ATTITUDE_QUATERNION on request | impl, observed (streamed) |
| Speeds and heading: VFR_HUD (`VehicleFactGroup.cc:208-226`) | m/s, deg 0..359 | blank values | VFR_HUD (EXTRA2) | impl, observed |
| Armed state: HEARTBEAT base_mode SAFETY_ARMED (`Vehicle.cc:1292-1296`; ARMING_REQUIRE is absent, so it is never 0) | the flag | wrong state | from Telemetry.armed | impl |
| Flight mode: custom_mode with CUSTOM_MODE_ENABLED (`APMFirmwarePlugin.cc:97-105`), names from the static table (`ArduCopterFirmwarePlugin.cc:11-69`) | ArduCopter numbers | "Unknown" | ArduCopter numbers | impl, observed |
| Underway (shows the in-flight actions): armed and system_status ACTIVE, CRITICAL or EMERGENCY (`APMFirmwarePlugin.cc:265-286`), plus EXTENDED_SYS_STATE landed_state (`Vehicle.cc:1030-1055`) | consistent values | wrong buttons | STANDBY on the ground, ACTIVE in the air; landed_state from the vehicle | impl |
| Ready to fly: SYS_STATUS PREARM_CHECK enabled and healthy (`Vehicle.cc:1073-1128`, `VehicleReadiness`) | the bit | Arm/Takeoff disabled | present, enabled, and healthy when the vehicle says so | impl |
| Home: HOME_POSITION (`Vehicle.cc:1199-1213`) | lat/lon/alt | no home icon, no RTL line | 1 Hz (QGroundControl's interval), and on GET_HOME_POSITION or REQUEST_MESSAGE | impl, observed |
| Mission progress: MISSION_CURRENT (`MissionManager.cc:267-272`) | seq | no current marker | EXTENDED_STATUS stream, and on every change | impl, observed (current index 1→4 during `--demo`) |
| STATUSTEXT: severity 0..3 pops up (`MAVLink/StatusTextHandler.cc:18-30`); text starting "PreArm" sets the pre-arm error (`Vehicle.cc:3462-3470`) | ArduPilot texts | none | one per tick from a queue. Vehicle texts pass through ("Arm: Auto mode not armable" is CRITICAL, as in ArduPilot) | impl |
| Change mode (`FirmwarePlugin.cc:246-274`, `Vehicle.cc:1478-1516`): COMMAND_LONG DO_SET_MODE (param1 1, param2 mode), then HEARTBEAT with the mode within 1.3 s, up to 3 attempts | ACK and HEARTBEAT | "did not respond" | ACK one tick later (the vehicle's verdict) and an immediate HEARTBEAT on the change | impl |
| Arm / Disarm: COMMAND_LONG ARM_DISARM (`Vehicle.cc:1439-1446`). Inside takeoff and start mission, HEARTBEAT armed within 1.5 s (`FirmwarePlugin.cc:222-244`) | ACK; HEARTBEAT | error toast | the vehicle's result, an immediate HEARTBEAT | impl |
| Takeoff (`APMFirmwarePlugin.cc:1008-1045`): mode GUIDED (validated), arm (validated), COMMAND_LONG NAV_TAKEOFF param7 = max(slider, PILOT_TKO_ALT_M or 3.048 m) | ACK ACCEPTED | "Unable to takeoff" | Command.takeoff; the vehicle layer follows ArduCopter's rules (`Leanfc/Copter/Modes.lean`) | impl |
| Start mission (`APMFirmwarePlugin.cc:1066-1106`): flying, mode AUTO; on the ground, GUIDED, arm, MISSION_START | ACK | error toast | Command.missionStart (AUTO; the first item must be a takeoff when armed on the ground, as in ArduCopter) | impl |
| Pause: mode BRAKE (17) (`ArduCopterFirmwarePlugin.cc:182-185`); with an altitude change, GUIDED then SET_POSITION_TARGET_LOCAL_NED, frame LOCAL_OFFSET_NED, mask 0xFFF8, no ACK (`APMFirmwarePlugin.cc:846-891`) | mode change; position target | "Unable to pause vehicle" | BRAKE holds; the offset becomes Command.goTo | impl |
| Change altitude: as pause, without BRAKE | position target | none | Command.goTo | impl |
| RTL: mode RTL (6) or SMART_RTL (21) (`APMFirmwarePlugin.cc:841-844`) | mode change | error toast | RTL; SMART_RTL is refused ("No such mode 21", FAILED) | impl |
| Land: mode LAND (9) | mode change | error toast | LAND | impl |
| Go to location (`APMFirmwarePlugin.cc:775-839`): COMMAND_INT DO_REPOSITION, frame GLOBAL, param2 CHANGE_MODE, z AMSL. Until an ACCEPTED ACK has been seen, it also falls back to GUIDED plus MISSION_ITEM (float) with current = 2, needing MISSION_ACK ACCEPTED within 1.5 s (`MissionManager.cc:25-67`, `PlanManager.cc:233-238`) | ACK; MISSION_ACK | "Mission transfer failed" | both. Command.goTo; the ACK and the MISSION_ACK from the vehicle's result | impl |
| Set waypoint: DO_SET_MISSION_CURRENT, with MISSION_SET_CURRENT as the fallback on UNSUPPORTED (`Vehicle.cc:2111-2144`) | ACK | error toast | Command.setCurrent | impl |
| Set home: COMMAND_LONG DO_SET_HOME, param5/6 lat/lon, param7 AMSL (from the terrain service, which needs the internet) (`TerrainQueryCoordinator.cc:30-85`) | ACK | error toast | Command.setHome | impl |
| Change speed: DO_CHANGE_SPEED param2 m/s (offered only if WP_SPD or WPNAV_SPEED exists, `APMFirmwarePlugin.cc:900-930`) | ACK | error toast | Command.changeSpeed | impl |
| Change heading: CONDITION_YAW | ACK | error toast | UNSUPPORTED | not impl |
| PING with target 0/0 is answered by QGroundControl; it does not send TIMESYNC (`Vehicle.cc:1239-1264`) | none | none | PING and TIMESYNC requests are answered (the brief) | impl |

## Plan view

| request (5.1.5 source) | response needed | if missing | leanfc | status |
|---|---|---|---|---|
| Upload (`PlanManager.cc:57-121, 487-554`): MISSION_COUNT including home (ArduPilot: `APMFirmwarePlugin.h:54`). The vehicle requests each item with MISSION_REQUEST or MISSION_REQUEST_INT, and QGroundControl answers MISSION_ITEM_INT. The final MISSION_ACK ACCEPTED is due within 1.5 s; 5.1.5 does not retry a lost final ACK | requests in order; the ACK | "Mission transfer failed" | MISSION_REQUEST_INT. Each request is re-sent after 1 s; the upload is abandoned with OPERATION_CANCELLED 8 s after the last item (ArduPilot). Item 0 is ignored (home is not overwritten) | impl |
| Frames: takeoff GLOBAL_RELATIVE_ALT; positioned items use the plan's altitude frame; RTL uses MAV_FRAME_MISSION (`SimpleMissionItem.cc:745-862`) | accept them | upload error | GLOBAL, GLOBAL_INT, MISSION (absolute), GLOBAL_RELATIVE_ALT(_INT) (relative); terrain UNSUPPORTED_FRAME | impl |
| Download: as connect item 17 | as item 17 | as item 17 | as item 17 | impl, observed |
| Remove all: MISSION_CLEAR_ALL | MISSION_ACK | error toast | ACCEPTED (ERROR while armed in AUTO, as ArduPilot) | impl |

## Parameter editor

| request | response needed | if missing | leanfc | status |
|---|---|---|---|---|
| PARAM_SET, then a PARAM_VALUE echo with the same name and value within 1 s, 2 retries (`ParameterManager.cc:291-420`) | the echo | "Parameter write failed" | Echo with the index. A leanfc parameter goes through `ParamFile.build` and is handed to the vehicle (Command.setParams). A rejected value echoes the old one, with "Param write denied (NAME): reason" (WARNING); QGroundControl then reports the failed write, as it should. | impl |
| Refresh: PARAM_REQUEST_LIST | as connect item 12 | | | impl |

## Where the development branch differs (v5.2.0-dev-244)

- FTP is also tried for PX4, and only PARAM_VALUE is dropped while it is pending. The dev branch also takes
  FailErrno/ENOENT as "File Not Found"; 5.1.5 needs error code 10, which is what we send.
- Mission retries: 6 in 5.1.5 (`> 5`), 5 in dev. Dev re-sends the last item when the final ACK is lost;
  5.1.5 fails at once.
- Dev has `APMVehicleReadiness`; 5.1.5 does not.
- Dev checks the AVAILABLE_MODES mode_index. Neither matters here, because we answer UNSUPPORTED.
- The "skip initial download" setting is named `noInitialDownloadWhenArmed` in dev and
  `noInitialDownloadWhenFlying` in 5.1.5. Both default to false.
