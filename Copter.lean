import Copter.Text
import Copter.Parameters
import Copter.AHRS
import Copter.State
import Copter.AutoYaw
import Copter.ModeAuto
import Copter.Loop

/-!
# `Copter`

Lean port of the part of `ArduCopter/` (see PORT.md) that runs Auto-mode waypoint flight, at
ArduPilot 802db19de1:

- `Copter.Parameters`: every parameter record of the stack with Copter defaults and the run
  overrides; the name table used by the executable.
- `Copter.AHRS`: one tick's sensor and estimator readings and the AHRS view built from them.
- `Copter.State`: the vehicle object (library states, AutoYaw, ModeAuto, mission, scheduler).
- `Copter.AutoYaw`: `autoyaw.cpp`, the heading command.
- `Copter.ModeAuto`: `mode_auto.cpp` on a waypoint mission (`wp_start`, `wp_run`, mission
  sequencing).
- `Copter.Loop`: `Copter.loop`, one tick in the order of the fast-task table.
- `Copter.Main` (the `copter` executable, not imported here): lock-step over standard streams;
  protocol in `Copter/PROTOCOL.md`.
-/
