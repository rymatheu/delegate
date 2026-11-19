import px4.modules.px4_mavlink.Ports

/-! # px4_mavlink: PX4's MAVLink module on a serial-link byte stream

PX4's `mavlink` (src/modules/mavlink: the streams, the parameter, mission, command, FTP, log, shell
and timesync protocols, with the libraries its CMakeLists.txt links), real and unmodified, PX4
v1.17.0, started as on a serial link: `mavlink start -d /dev/ttyHARNESS0 -b 921600` (mode
normal), then `mavlink boot_complete`, as rcS does. PX4's data manager runs in the same process
(`dataman start -r`): the mission manager's DatamanClient asks it for a client id when the module
starts, synchronously, and logs "Failed to get client ID!" if no dataman answers within 1 s.

The serial port is a byte-stream port (px4/shim/stream.cpp): `mavlink_rx_len` bytes in
`mavlink_rx_0..127` per tick into the port's receive buffer, up to 512 bytes per tick out of its
transmit buffer into `mavlink_tx_len` / `mavlink_tx_*`; each buffer holds 4096 bytes; a byte on a
full receive buffer is dropped (`mavlink_rx_dropped`), a write on a full transmit buffer is short
(mavlink counts it as a transmit overrun). 921600 baud is 230 bytes per 2.5 ms tick, and mavlink
limits its streams to 46080 B/s on that link (115 bytes per tick), so 512 bytes per tick leaves
room for bursts (parameter lists, mission transfers).

Three activities, all run by the shim (tasks.cpp): the module's task (Mavlink::task_main: a pass
every `_main_loop_delay`, px4_usleep, sending the due streams and the protocol replies), its
receiver thread (MavlinkReceiver, made with pthread_create, blocked in poll on the port until
bytes arrive), and dataman's task. What a step runs: the receiver for the step's bytes, the task's
pass if due.

The parameter set is the whole stack's (px4.txt `params-of`: rate controller, allocator,
commander, navigator, and mavlink's own: 743), under the same names as in those modules, so that
composeAll gives every module the same values; it is served read-only (px4.txt `params readonly`):
a PARAM_SET is answered as PX4 answers every PARAM_SET, with PARAM_VALUE of the stored value
(mavlink_parameters.cpp:124-136), which the store did not change.

The storage requests of the mission manager go out whole on the mirror port
`dataman_request_mirror_*` (px4.txt `mirror 170`), to be replayed into navigator's dataman. 170
slots is the most one tick can carry. Per tick at most 512 bytes come in, and the receiver handles
only what came in (it drains the port every step). The frame that causes the most storage writes
per byte is a MAVLink 2 MISSION_CLEAR_ALL with mission_type ALL (255): 15 bytes (10 header, 3
payload: target system, target component, mission type; 2 checksum), handled whenever the
mission manager is idle, and it writes 5 times: the mission state (update_active_mission), the
fence state and the mission state again (update_geofence_count), the safe point state and the
mission state again (update_safepoint_count) (mavlink_mission.cpp:1328-1370, :191-262). No frame
causes more writes per byte (a MISSION_ITEM_INT writes at most 3: the item, then at the end of a
transfer a state and the mission state; it is at least 45 bytes). 512 / 15 = 34 frames, 34 * 5 =
170 requests. Every other request of the mission manager is a read or a client-id request, at
most one per handled frame, fewer than 170 per tick as well.

Contract:
* `tx_within_port`: no more than the port's 512 bytes per tick, the transmit buffer within 4096.
* `mirror_complete`: every storage request of the step is on the mirror port (none lost).
* `mirror_from_mission_manager`: the mirror port carries the mission manager's storage requests,
  whole and in order, and says so by its mark `dataman_request_mirror_by_px4_mavlink` (set at
  every tick by the generated glue, px4/ports.py). From the code: in this process dataman_request
  is published only through DatamanClient (DatamanClient.cpp:93, :107, :276; dataman itself only
  subscribes to it, dataman.cpp:685), and the only DatamanClient is the mission manager's
  (`MavlinkMissionManager::_dataman_client`, mavlink_mission.h:108); the shim's tap copies every
  publication of the step whole, in publication order (px4/shim/bus.cpp, `tap`, `collect_tap`).
  The clause states the mark; the rest is this argument, carried by the mark to the subscriber
  (px4_navigator's `storage_from_mavlink`).
* `no_px4_error`. -/

namespace Px4.Modules.Px4Mavlink

open Harness Harness.Contract.Lang

def guarantee : List Clause := [
  ⟨"tx_within_port", "mavlink_tx_len" ≤. 512 ∧. "mavlink_tx_pending" ≤. 4096⟩,
  ⟨"mirror_complete", "dataman_request_mirror_lost" =. 0⟩,
  ⟨"mirror_from_mission_manager", "dataman_request_mirror_by_px4_mavlink"⟩,
  ⟨"no_px4_error", "px4_mavlink_errors" =. 0⟩]

/-- The first statement. Refuted once mavlink subscribed to mission_result (fuzzed_link, seeds
1-3, 5 x 400, all 400 steps of one case each): "readSync failed! status=3, item=0, index=2708".
A mission_result with item_do_jump_changed and item_changed_index < seq_total makes the mission
manager send that item to the ground station (mavlink_mission.cpp:536-545), reading it from
storage; generated results name items that were never stored, and the failed read is logged at
error level (DatamanClient.cpp:171-175). -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges
  guarantee := guarantee

/-- The contract: a mission_result reports a changed jump item only of the mission mavlink stored
(navigator's results do); stated, short of the stored count, as: no jump-change report beyond
the mission's items, with no mission stored here outside the composite. -/
def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++
    [⟨"no_jump_report_outside_mission", ¬. "mission_result_updated" ∨.
        "mission_result_item_do_jump_changed" =. ff⟩]
  guarantee := guarantee

/-- PX4's defaults; the link silent or carrying arbitrary bytes (a fuzzed link: whatever the
generator draws), the clock at 400 Hz. -/
def fuzzedLink : Regime where
  name := "fuzzed_link"
  doc := "PX4 defaults; arbitrary bytes on the serial link; nothing else published"
  clauses := Ports.paramDefaults ++ [
    ⟨"no_status", "vehicle_status_updated" =. ff⟩, ⟨"no_ack", "vehicle_command_ack_count" =. 0⟩]
  hints := [.increasing "t_us" 1000000 2500 2500]

def coverage : List Clause := [
  ⟨"sent", 0 <. "mavlink_tx_len"⟩,
  ⟨"received", 0 <. "mavlink_rx_len"⟩,
  ⟨"command_out", 0 <. "vehicle_command_count"⟩,
  ⟨"backlog", 0 <. "mavlink_tx_pending"⟩]

def module : Module where
  name := "px4_mavlink"
  doc := "PX4 mavlink (v1.17.0), unmodified, on a serial-link byte-stream port"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_mavlink/px4_mavlink"
  stack := .px4
  regimes := [fuzzedLink]
  coverage := coverage

end Px4.Modules.Px4Mavlink
