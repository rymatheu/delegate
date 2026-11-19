import px4.modules.px4_merge_ack.Ports

/-! # px4_merge_ack: one vehicle_command_ack queue from two publishers

On the vehicle commander and navigator publish vehicle_command_ack on one uORB topic, a queue of
4 (ORB_QUEUE_LENGTH); a subscriber sees the messages in the order they were written and loses the
oldest beyond 4. In the harness each publisher's messages of a step come on its own ports
(`pub vehicle_command_ack by`); this node, generated (no PX4 code), puts them in one queue:
commander's first, then navigator's, each in its own order, at most 4, the rest counted lost.
Within a step the order between the two publishers is the order of composition, not of their
writes (they are separate processes). -/

namespace Px4.Modules.Px4MergeAck

open Harness Harness.Contract.Lang

private def total : Expr :=
  "vehicle_command_ack_by_px4_commander_count" + "vehicle_command_ack_by_px4_navigator_count"

def guarantee : List Clause := [
  ⟨"count_within_queue", ("vehicle_command_ack_count" =. total ∧. total ≤. 4) ∨.
      ("vehicle_command_ack_count" =. 4 ∧. 4 <. total)⟩,
  ⟨"lost_rest", "vehicle_command_ack_count" + "vehicle_command_ack_lost" =. total⟩,
  ⟨"updated_iff_any", "vehicle_command_ack_updated" =. (0 <. "vehicle_command_ack_count")⟩,
  ⟨"commander_first", "vehicle_command_ack_by_px4_commander_count" =. 0 ∨.
      ("vehicle_command_ack_command" =. "vehicle_command_ack_by_px4_commander_command" ∧.
       "vehicle_command_ack_result" =. "vehicle_command_ack_by_px4_commander_result")⟩]

def contract : Contract where
  assume := Ports.widths
  guarantee := guarantee

def module : Module where
  name := "px4_merge_ack"
  doc := "merge of vehicle_command_ack from commander and navigator (generated, no PX4 code)"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := contract
  exe := "build/modules/px4_merge_ack/px4_merge_ack"
  stack := .px4

end Px4.Modules.Px4MergeAck
