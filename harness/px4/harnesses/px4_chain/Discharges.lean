import Harness.Compose

/-! # The PX4 stack's discharge table, shared

How obligations between PX4 modules are discharged, stated once and used by every composite that
contains the modules concerned (`harness obligations NAME --status` says of each entry whether the
link's checkers prove it). Every entry cites guarantees that are facts of the PX4 code (file and
line in the module's Module.lean) or of the generated glue; no flight envelope is invented here. -/

namespace Px4.Harnesses.Chain

open Harness

/-- navigator's mission storage comes from MAVLink's mission manager: in a composite where
px4_mavlink's mirror port feeds px4_navigator (px4_full). -/
def storage : List Discharge := [
  { path := "px4_navigator", clause := "storage_from_mavlink", kind := "guarantee",
    by_ := ["px4_mavlink.mirror_from_mission_manager"],
    note := "the mark is set at every tick by px4_mavlink's glue; px4_mavlink runs before \
      px4_navigator in the tick (a same-tick wire)" }]

/-- navigator's command window counts the tick's own commands: in a composite where px4_cmd_window
observes the vehicle_command that navigator reads (px4_nav_loop, px4_full). -/
def window : List Discharge := [
  { path := "px4_navigator", clause := "window_holds_tick", kind := "guarantee",
    by_ := ["px4_cmd_window.window_holds_tick"],
    note := "the observer and navigator read the same vehicle_command_count wire" }]

/-- The width and slot obligations between generated PX4 ports, discharged by the publisher's
generated guarantee of the same name: a subscriber assumes `width_F` (a field narrower on the
bus than in its record is within its C type's range) or `slots_P_count` (at most its slots of a
queued topic), and the publisher's glue guarantees `width_F` (it copies a field of that C type
with a cast) or `slots_P_count` (it copies at most its own slots): `Ports.outWidths` of every
generated module, from px4/ports.py. One entry per such wire of `n`'s children (`out` or `prev`,
the same field name on both ends); the range checker then proves the entry, or leaves it stated
when the publisher's bound is wider than the subscriber's (more slots than the subscriber reads).
Computed from the composite's wiring, so every PX4 composite gets the entries of its own wires. -/
def fromGlue (n : Node) : List Discharge :=
  match n with
  | .system s => s.children.flatMap fun ch =>
      let asm := ch.node.view.contract.assume
      ch.input.filterMap fun w =>
        let src : Option String := match w.source with
          | .out c g => if g == w.field then some c else none
          | .prev c g _ => if g == w.field then some c else none
          | _ => none
        src.bind fun c =>
          let names := [s!"width_{w.field}", s!"slots_{w.field}"]
          (names.find? fun nm => asm.any (·.name == nm)).bind fun nm =>
            (s.children.find? (·.name == c)).bind fun p =>
              if p.node.view.contract.guarantee.any (·.name == nm) then
                some { path := ch.name, clause := nm, kind := "guarantee", by_ := [s!"{c}.{nm}"],
                       note := s!"{c}'s glue copies {w.field} from its C struct field \
                         (px4/modules/{c}/Ports.lean, outWidths)" }
              else none
  | _ => []

/-- The system with `fromGlue`'s entries added to its discharge table. -/
def withGlue (n : Node) : Node := withDischarges n (fromGlue n)

end Px4.Harnesses.Chain
