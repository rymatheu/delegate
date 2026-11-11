import Leanfc.Copter.Fly
import Leanfc.Mavlink.Gcs

/-!
# Autopilot (one tick of the whole flight controller, pure)

The services (`Mavlink.Gcs`), the vehicle layer (`Copter`) and the flight law (`Controller`, called
by the vehicle layer) in one pure function, so that the executable's loop (`Main.lean`) only moves
bytes and lines:

`step a sensors incoming = (a', motors, outgoing)`:

1. the services read the vehicle's telemetry of the previous tick (with the results of the
   previous tick's commands) and at most one received message, and return the messages to send
   and the commands for the vehicle (`Gcs.step`);
2. the vehicle applies the commands and runs one tick on the sensors (`Copter.step`), with the
   tick of the last ground-station HEARTBEAT for its failsafe.

`run a sensors` is the vehicle alone, without services (no ground station: the batch runs).
`origin` is the geodetic origin of the NED frame with its cosine of latitude, which the IO shell
computes once.
-/

open Mavlink

structure Autopilot where
  cfg : GcsConfig
  gcs : GcsState
  veh : Copter.State
  origin : Origin

namespace Autopilot

def step (a : Autopilot) (s : Sensors) (inc : Option Incoming) : Autopilot × Motors × Array Msg :=
  let (gcs, out, cmds) := Gcs.step a.cfg a.gcs (Copter.telemetry a.veh a.origin) inc
  let (veh, m) := Copter.step a.veh cmds gcs.gcsSeen s
  ({ a with gcs, veh }, m, out)

/-- The vehicle without services. -/
def run (a : Autopilot) (s : Sensors) : Autopilot × Motors :=
  let (veh, m) := Copter.step a.veh #[] none s
  ({ a with veh }, m)

end Autopilot
