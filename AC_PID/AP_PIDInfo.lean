import AC_PID.Compat

/-!
# `AP_PIDInfo`

Mirrors `libraries/AC_PID/AP_PIDInfo.h:9-24` (ArduPilot commit 802db19de1): the record of a
PID's internal values that ArduPilot keeps for logging, and that `AC_PID::get_p`, `get_d`,
`get_ff` read back.

Left out: nothing; every field is kept. Field `slew_rate` is never updated by this port (see
`AC_PID.update_all`).
-/

open AC_PID.Compat

/-- `struct AP_PIDInfo`, `AP_PIDInfo.h:9-24`. -/
structure AP_PIDInfo where
  target : ftype := 0
  actual : ftype := 0
  error : ftype := 0
  P : ftype := 0
  I : ftype := 0
  D : ftype := 0
  FF : ftype := 0
  DFF : ftype := 0
  Dmod : ftype := 0
  slew_rate : ftype := 0
  limit : Bool := false
  PD_limit : Bool := false
  reset : Bool := false
  I_term_set : Bool := false
deriving Repr, Inhabited
