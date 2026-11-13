import ParamHarnessData

/-!
The AP_Param boot sequence of the vehicle on the translated AP_Param (README.md, "Phase 4: AP_Param"), as
reference/hal/param_dump.cpp runs it in the reference: static construction (`AP_Param::_storage`'s constructor, the
constructors' `setup_object_defaults`, `copter.param_loader`'s `AP_Param(var_info)`), `AP_Vehicle::setup`'s
`AP_Param::setup_sketch_defaults()`, `check_var_info()`, `AP_Vehicle::load_parameters`'s format-version check and
`AP_Param::load_all()`. Every call is a translated ArduPilot function; this file only sequences them and reads results.
-/

open FloatLib.Floats (Binary32 Binary64)
open AP_Param_lib ParamHarnessData

namespace ParamBoot

/-- Static construction: AP_Param.cpp's `StorageAccess AP_Param::_storage(StorageManager::StorageParam)`, the static
objects' constructors' `setup_object_defaults(this, var_info)`, Copter's `param_loader(var_info)`. -/
def staticInit : PMem.M Unit := do
  StorageAccess.StorageAccess addr'AP_Param___storage 0
  -- ParametersG2's initializer list: `mode_rtl_ptr(&copter.mode_rtl)`, ...
  for (c, v) in ctorPointers do
    PMem.stU64 c v
  for (o, t) in ctorDefaults do
    AP_Param.setup_object_defaults o t
  -- ParametersG2's initializer list: `command_model_pilot_y(PILOT_Y_RATE_DEFAULT, PILOT_Y_EXPO_DEFAULT, 0.0f)`
  for (o, a, b, c) in ctorCommandModels do
    AC_CommandModel.AC_CommandModel o (Binary32.ofBits a) (Binary32.ofBits b) (Binary32.ofBits c)
  SRV_Channels.SRV_Channels servoChannels
  AP_Param.AP_Param paramLoader addr'Copter__var_info

/-- Static construction runs before the HAL loads the storage image (lockstep.cpp loads it in `run`, after the
constructors): the constructors see blank storage (`set_default` asks `configured()`); then the image is in place. -/
def initWith (st : ByteArray) : PMem.Mem :=
  let blank := ByteArray.mk (Array.replicate st.size 0)
  let ((), m) := staticInit.run (initMem blank)
  { m with st := st }

/-- AP_Vehicle::load_parameters(g.format_version, Parameters::k_format_version) up to and including load_all
(AP_Vehicle/Parameters.cpp:12-28). -/
def formatCheckAndLoad : PMem.M Bool := do
  let fp ← PMem.enter 16
  let ok ← AP_Param.load formatVersion
  let v ← PMem.ldI16 formatVersion        -- `format_version != expected_format_version` (operator const T &)
  if !ok || v != formatVersionExpected then
    StorageManager.erase
    AP_Param.erase_all
    PMem.stI16 fp formatVersionExpected
    AP_ParamTBase'short_2.set_and_save formatVersion fp
  PMem.stI16 (fp + 8) formatVersionExpected
  AP_ParamTBase'short_2.set_default formatVersion (fp + 8)
  let r ← AP_Param.load_all
  PMem.leave fp
  return r

def hex8 (u : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  "".pushn '0' (8 - s.length) ++ s

def cstr (a : UInt64) (n : Nat) : PMem.M String := do
  let mut cs : List Char := []
  for k in [0:n] do
    let c ← PMem.rd (a + k.toUInt64)
    if c == 0 then break
    cs := cs ++ [Char.ofNat c.toNat]
  return String.ofList cs

/-- One parameter's value as the reference prints it (integers in decimal, floats as their bits). -/
def valueText (vp : UInt64) (ty : UInt32) : PMem.M String := do
  match ty with
  | 1 => return toString (← PMem.ldI8 vp).toInt
  | 2 => return toString (← PMem.ldI16 vp).toInt
  | 3 => return toString (← PMem.ldI32 vp).toInt
  | 4 => return hex8 (← PMem.ldU32 vp)
  | _ => return "?"

/-- AP_Param::first / next_scalar with copy_name_token (GCS_Param's calls); the lines (or only the count). -/
def enumerate (lines : Bool) : PMem.M (Array String × Nat) := do
  let fp ← PMem.enter 64
  let token := fp
  let ptype := fp + 8
  let name := fp + 16
  let mut out : Array String := #[]
  let mut n := 0
  let mut vp ← AP_Param.first token ptype 0
  while vp != 0 do
    discard <| PMem.memset name 0 17
    AP_Param.copy_name_token vp token name 16 true
    if lines then
      let ty ← PMem.ldU32 ptype
      let key ← PMem.ldBits token 0 9
      let idx ← PMem.ldBits token 9 4
      let ge ← PMem.ldBits token 13 18
      out := out.push s!"{n} {key},{ge},{idx} {← cstr name 17} {ty} {← valueText vp ty}"
    n := n + 1
    vp ← AP_Param.next_scalar token ptype 0
  PMem.leave fp
  return (out, n)

def fnv (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 1469598103934665603
  for x in b.data do
    h := (h ^^^ x.toUInt64) * 1099511628211
  return h

def phase (tag : String) : PMem.M (Array String) := do
  let (ls, n) ← enumerate true
  let c ← AP_Param.count_parameters
  let st := (← get).st
  let h := fnv st
  let hs := String.ofList (Nat.toDigits 16 h.toNat)
  return #[s!"# {tag}"] ++ ls ++ #[s!"# count {n}", s!"# count_parameters {c}", s!"# storage {"".pushn '0' (16 - hs.length) ++ hs}"]

/-- The memory after static construction and AP_Param's boot sequence on the storage image `st`, with the dump
lines of the two phases. -/
def boot (st : ByteArray) : Array String × PMem.Mem := Id.run do
  let m0 := initWith st
  let act : PMem.M (Array String) := do
    AP_Param.setup_sketch_defaults
    let d ← phase "defaults"
    AP_Param.invalidate_count
    AP_Param.check_var_info
    discard <| formatCheckAndLoad
    AP_Param.invalidate_count
    let l ← phase "loaded"
    return d ++ l
  let (ls, m) := act.run m0
  return (ls, m)

/-- The memory after load_all (no dump). -/
def loadOnly (st : ByteArray) : PMem.Mem :=
  let act : PMem.M Unit := do
    AP_Param.setup_sketch_defaults
    AP_Param.check_var_info
    discard <| formatCheckAndLoad
  (act.run (initWith st)).2

/-- An estimator World parameter's value as est_probe.cpp prints it in `# params`. -/
def estValue (m : PMem.Mem) (a : UInt64) (size kind : Nat) : String :=
  let rd : PMem.M String := do
    match kind, size with
    | 2, _ => return hex8 (← PMem.ldU32 a)
    | 1, 1 => return toString (← PMem.ldI8 a).toInt
    | 1, 2 => return toString (← PMem.ldI16 a).toInt
    | 1, 4 => return toString (← PMem.ldI32 a).toInt
    | 0, 1 => return toString (← PMem.ldU8 a).toNat
    | 0, 2 => return toString (← PMem.ldU16 a).toNat
    | 0, 4 => return toString (← PMem.ldU32 a).toNat
    | _, _ => return "?"
  (rd.run m).1

end ParamBoot

namespace ParamBoot
open AP_Param_lib

/-- Write a C string into the memory at `a`. -/
def putStr (a : UInt64) (s : String) : PMem.M Unit := do
  let bs := s.toUTF8
  for k in [0:bs.size] do
    PMem.wr (a + k.toUInt64) bs[k]!
  PMem.wr (a + bs.size.toUInt64) 0

def named (vp token ptype : UInt64) : PMem.M String := do
  if vp == 0 then return "null"
  let fp ← PMem.enter 32
  AP_Param.copy_name_token vp token fp 16 true
  let ty ← PMem.ldU32 ptype
  let key ← PMem.ldBits token 0 9
  let idx ← PMem.ldBits token 9 4
  let ge ← PMem.ldBits token 13 18
  let r := s!"{key},{ge},{idx} {← cstr fp 17} {ty} {← valueText vp ty}"
  PMem.leave fp
  return r

def digestText : PMem.M String := do
  let h := fnv (← get).st
  let hs := String.ofList (Nat.toDigits 16 h.toNat)
  return "".pushn '0' (16 - hs.length) ++ hs

def parseHex (s : String) : Nat := s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0

/-- The per-function differential test's commands (reference/hal/param_dump.cpp, `test`), on the translated AP_Param. -/
def testCmd (line : String) : PMem.M String := do
  let t := ((line.splitOn " ").filter (· ≠ "")).toArray
  let fp ← PMem.enter 128
  let token := fp
  let ptype := fp + 8
  let ptype2 := fp + 16
  let name := fp + 32
  let n (i : Nat) : Nat := (t[i]!).toNat!
  let mut out := line ++ "\n"
  match t[0]! with
  | "enum" =>
    PMem.stBits token 0 9 (n 1).toUInt64
    PMem.stBits token 13 18 (n 2).toUInt64
    PMem.stBits token 9 4 (n 3).toUInt64
    let vp ← AP_Param.next_scalar token ptype 0
    out := out ++ (← named vp token ptype)
  | "name" =>
    putStr name t[1]!
    let vp ← AP_Param.find_by_name name ptype token
    out := out ++ (← named vp token ptype)
    let vp2 ← AP_Param.find name ptype2 0
    let ty2 ← PMem.ldU32 ptype2
    out := out ++ s!" find {if vp2 == vp then 1 else 0} {if vp2 != 0 then ty2 else 0}"
  | "index" =>
    let vp ← AP_Param.find_by_index (n 1).toUInt16 ptype token
    out := out ++ (← named vp token ptype)
  | "set" =>
    putStr name t[1]!
    let vp ← AP_Param.find_by_name name ptype token
    if vp != 0 then
      AP_Param.set_float vp (Binary32.ofBits (parseHex t[3]!).toUInt32) (n 2).toUInt32
      AP_Param.save_sync vp (n 4 != 0) false
    out := out ++ (← named vp token ptype) ++ " " ++ (← digestText)
  | "load" =>
    putStr name t[1]!
    let vp ← AP_Param.find_by_name name ptype token
    let r ← if vp != 0 then (do let b ← AP_Param.load vp; pure (if b then "1" else "0")) else pure "-1"
    out := out ++ (← named vp token ptype) ++ " " ++ r
  | "count" =>
    AP_Param.invalidate_count
    out := out ++ toString (← AP_Param.count_parameters).toNat
  | "dump" =>
    let (ls, _) ← enumerate true
    out := out ++ "\n" ++ String.intercalate "\n" ls.toList ++ (if ls.isEmpty then "" else "\n")
  | "loadall" =>
    let b ← AP_Param.load_all
    out := out ++ s!"{if b then 1 else 0} {← digestText}"
  | _ => pure ()
  PMem.leave fp
  return out

def test (st : ByteArray) (script : Array String) : Array String := Id.run do
  let act : PMem.M (Array String) := do
    AP_Param.setup_sketch_defaults
    AP_Param.check_var_info
    let b ← formatCheckAndLoad
    let mut out := #[s!"boot {if b then 1 else 0} {← digestText}"]
    for l in script do
      if l.trimAscii.toString.isEmpty then continue
      out := out.push (← testCmd l.trimAscii.toString)
    return out
  return (act.run (initWith st)).1

end ParamBoot
