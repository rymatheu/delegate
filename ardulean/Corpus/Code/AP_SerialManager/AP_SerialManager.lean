import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AP_SerialManager: `AP_SerialManager.cpp`

The baud-rate code table: the listed codes, the default for codes `≤ 0`, rates above 2000 taken as baud.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AP_SerialManager

theorem AP_SerialManager.map_baudrate_eq (rate : Int32) :
    Vehicle_lib.AP_SerialManager.map_baudrate rate = pure (Vehicle_lib.AP_SerialManager.map_baudrate.pure' rate) := rfl

/-- Protocol: the baud-rate codes (`AP_SerialManager.cpp:738-771`). -/
theorem AP_SerialManager.map_baudrate_table :
    ([(1, 1200), (2, 2400), (4, 4800), (9, 9600), (19, 19200), (38, 38400), (57, 57600), (100, 100000),
      (111, 111100), (115, 115200), (230, 230400), (256, 256000), (460, 460800), (500, 500000), (921, 921600),
      (1500, 1500000), (2000, 2000000)] : List (Int32 × UInt32)).all
      (fun p => Id.run (Vehicle_lib.AP_SerialManager.map_baudrate.pure' p.1) == p.2) = true := by
  unfold Vehicle_lib.AP_SerialManager.map_baudrate.pure'; decide

/-- Case: a code `≤ 0` is the default, 57600 baud. -/
theorem AP_SerialManager.map_baudrate_of_nonpos {rate : Int32} (h : rate.toInt ≤ 0) :
    Id.run (Vehicle_lib.AP_SerialManager.map_baudrate.pure' rate) = 57600 := by
  unfold Vehicle_lib.AP_SerialManager.map_baudrate.pure'
  simp only [Id.run, pure, bind]
  rw [if_pos (by simp only [decide_eq_true_eq, Int32.le_iff_toInt_le]; exact h)]
  decide

end Corpus.AP_SerialManager
