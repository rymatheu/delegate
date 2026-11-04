import Contracts.CopterCode

/-!
# Axioms of the ArduCopter-port contracts

`#print axioms` for every theorem of `Contracts.CopterLift` and `Contracts.CopterCode` that the
paper may cite. Each must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

open Contracts.CopterLift Contracts.CopterCode

#print axioms Mcopter_receptive
#print axioms Mcopter_inter_nonempty
#print axioms Mcopter_nonempty
#print axioms Mcopter_eq_proj
#print axioms loop_isSome
#print axioms tick_of_mission
#print axioms defaults_mission_ne
#print axioms midpoint_unit
#print axioms constrain_unit
#print axioms set_actuator_with_slew_eq
#print axioms set_actuator_with_slew_unit
#print axioms output_to_motors_unit
#print axioms output_unit
#print axioms loop_unit
#print axioms tick_unit
#print axioms actuators_in_unit
#print axioms actuators_in_unit_defaults
#print axioms actuators_in_unit_nonvacuous
