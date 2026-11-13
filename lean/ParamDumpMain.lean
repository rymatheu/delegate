import ParamBoot

/-! `param_dump STORAGE OUT [--est]` (README.md, "Phase 4: AP_Param"): the translated AP_Param's boot sequence on a
storage image and the enumeration before and after load_all, in the format of `copter_ref --param-dump`; with `--est`,
the estimator World's parameters after load_all as `path=value` lines (the replay's parameter source). -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [stPath, outPath] =>
    let st ← IO.FS.readBinFile stPath
    let t0 ← IO.monoNanosNow
    let (ls, m) := ParamBoot.boot st
    IO.FS.writeFile outPath (String.intercalate "\n" ls.toList ++ "\n")
    let t1 ← IO.monoNanosNow
    -- speed: load_all alone, and one enumeration pass (first/next_scalar/copy_name_token)
    let m1 := ParamBoot.loadOnly st
    let t2 ← IO.monoNanosNow
    let st0 := ParamBoot.initWith st
    let ((), mb) := (do AP_Param_lib.AP_Param.setup_sketch_defaults; AP_Param_lib.AP_Param.check_var_info : PMem.M Unit).run st0
    let t3 ← IO.monoNanosNow
    let (r, _) := ParamBoot.formatCheckAndLoad.run mb
    let t4 ← IO.monoNanosNow
    let ((_, n), _) := (ParamBoot.enumerate false).run m1
    let t5 ← IO.monoNanosNow
    IO.eprintln s!"param_dump (Lean): whole run {(t1 - t0).toFloat / 1e6} ms; static init (outside) + defaults + check {(t3 - t2).toFloat / 1e3} us; format check + load_all {(t4 - t3).toFloat / 1e3} us ({r}); enumeration {(t5 - t4).toFloat / 1e3} us per pass ({n} parameters); heap used {m.hp}"
    return 0
  | [stPath, "--est", outPath] =>
    let st ← IO.FS.readBinFile stPath
    let m := ParamBoot.loadOnly st
    let ls := ParamHarnessData.estParams.map fun (p, a, sz, k) => s!"{p}={ParamBoot.estValue m a sz k}"
    IO.FS.writeFile outPath (String.intercalate "\n" ls.toList ++ "\n")
    return 0
  | [stPath, outPath, "--test", script] =>
    let st ← IO.FS.readBinFile stPath
    let ls ← IO.FS.lines script
    let out := ParamBoot.test st ls
    IO.FS.writeFile outPath (String.intercalate "\n" out.toList ++ "\n")
    return 0
  | _ => IO.eprintln "usage: param_dump STORAGE OUT | param_dump STORAGE --est OUT"; return 2
