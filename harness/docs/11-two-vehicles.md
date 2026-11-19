# 11. Two vehicles

**Status (2026-11-19):** built for the ArduPilot stack (`ap_formation`); the PX4 stack declares its own the same way.

Formation flight is two stacks and one plant in one served session. Nothing new is needed in the semantics: a
formation is an ordinary system, built by `composeAll`, so the checks, the runtime, the monitors, the campaigns,
the ledger and the formal link apply unchanged. What the generic layer adds is small.

## The pieces

| Piece | What it is | Where |
|---|---|---|
| plant | `plant_formation`: the same gorge simulator with two X500s in one world (the shared simulator's `FormationPlant`), one executable, plant_sim's interface twice: every field prefixed `v1_` or `v2_`, the time `t_us` and the parameters shared, plus `formation` (1 abreast, 2 staggered). Its contract is plant_sim's for each vehicle, renamed. | `sim/modules/plant_formation/Module.lean`; executable `sim/modules/plant_sim/adapter.py --vehicles 2` |
| one vehicle's stack | the single-vehicle system without its plant (ArduPilot: `ap_vehicle`, the stages of `ap_full_ekf`) | `ardupilot/harnesses/ap_formation/Composed.lean` |
| two instances | `inst stack "v1" shared`, `inst stack "v2" shared`: the same node twice, every field prefixed, the clock (`dt`, `now_us`, `now_ms` and the plant's `t_us`) shared. An instance is an adapter, which `composeAll` absorbs: the child is the stack itself under the instance name, so its evidence, contract and monitors are the stack's | `Harness/Compose.lean` (`inst`, existing) |
| the formation | `composeAll [plant, v1, v2]`: the plant first, then the two stacks, which read the plant's outputs of the same tick by name and feed it their PWM through `prev` | |
| its contract | the computed one (every child's guarantee, renamed), plus what the formation as a whole is to achieve, added with `withGuarantee`: `min_separation` (the two vehicles' true positions at least 1.5 m apart) and `wall_clearance` (each vehicle's clearance from the gorge's side surfaces at least 0.5 m; `wall_clear`, a plant output: PyBullet's closest points of the gorge no lower than 5 cm under the vehicle's center, so the floor beneath is not a wall) | `Harness/Compose.lean` (`withGuarantee`) |
| concurrency | `concurrently`: the two stacks, which do not read each other's outputs of the same tick, are stepped at the same time, each in its own thread | `Harness/Runtime.lean` (`CSysOf.stepGroups`), `Harness/Compose.lean` (`concurrently`) |
| the link to a ground station | each vehicle has its own UDP socket and its own MAVLink system id (1, 2), both sending to the ground station's one port | `ardupilot/qgc_bridge.py` (on `gorgesim.udp_bridge`) |

## Concurrency without a new semantics

`Running.step` steps a system's children in groups (`CSysOf.stepGroups`): consecutive children, a child joining the
group before it when it reads no `out` source (an output of the same tick) of a child of that group. The inputs of
every child of a group are assembled before the group runs, from the system's inputs, parameters, constants, `prev`
values and outputs of earlier groups, which is exactly what each would read when stepped one after the other (an
`out` source of a later child is excluded by the check before anything runs). The group's children are then stepped
in their own threads, all awaited, and their outputs and exchange records kept in child order. The records are
therefore those of the sequential runtime, so the formal link's model of the runtime (`Consistent`, doc 10), the
monitors, the saved cases and the code hash do not change; only the wall time does. A system is stepped this way only
when declared `concurrently`; `HARNESS_SEQUENTIAL=1` turns it off for a run (to compare the records).

## What the formal link says about a formation

The added clauses are not guarantees of any child: the link reports them as uncovered (`OpenCover` hypotheses),
monitored at every tick and backed by the served sessions' records, not derived. Every other clause is the stacks'
and the plant's, and their obligations are discharged as in the single-vehicle system, per vehicle. `harness link
ap_formation` prints the plan. For `ap_formation` (2026-11-19): 154 obligations, 64 proved (transport or range checker), 6 stated (each vehicle's `imu_range` from the plant's full scale, and per vehicle the two `rate_c` scale ranges as in ap_ctl), 84 open (per vehicle the 42 of ap_full_ekf); the two formation clauses `min_separation` and `wall_clearance` are uncovered (`OpenCover`). The link theorem and its axioms (`propext`, `Classical.choice`, `Quot.sound`) are unchanged: concurrency changes no record, and `withGuarantee`, `inst` and the plant are ordinary declarations.

## Declaring a two-vehicle system for another stack

1. A system for one vehicle's stack without its plant (all stages of the single-vehicle system after the plant).
2. `inst` it twice with the shared fields (the clock, if the stack reads one, and the plant's `t_us`: forgetting it leaves each stack's `t_us` an unwired input, 0, and ArduPilot's estimator never starts), and the plant's input and output names
   as the stack expects them (`rename` the plant if the names differ, as `ap_formation` renames `pwm0` to `pwm_1`).
3. `composeAll [plant_formation, v1, v2]`, then `withGuarantee` with the formation clauses, `withDischarges` with the
   stack's discharges per vehicle (paths `v1/…`, `v2/…` are the instances), `concurrently`.
4. Register the system in `Main.lean`; its evidence is in `STACK/harnesses/NAME/evidence/`.
