/-
# deps_report.lean : which declarations does the proof of the headline theorems really use?  Builds NOTHING.

Walks the constants reachable (types and values) from `four_speed_spectrum` and `four_speed_attained`, groups them by the module
that declares them, and prints
  1. per project module (LRSpectrumFull.*): the number of reached constants;
  2. for the ten modules that predate the four-speed work (kind `base` in MANIFEST.tsv): every reached declaration, with its kind;
  3. the number of reached Mathlib / Batteries / Lean-core modules and constants (the part of the trust base that is not ours).
Run by `deps_report.sh` (under the same wrapper as check_axioms.sh).
-/
import LRSpectrumFull.L4S5.FourSpeed

open Lean Elab Command

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .axiomInfo _ => "AXIOM" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : List Name := [`LRSpectrumFull.L4S5.four_speed_spectrum, `LRSpectrumFull.L4S5.four_speed_attained]
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in ci.type.getUsedConstants do
        if !seen.contains c then todo := todo.push c
      match ci.value? (allowOpaque := true) with
      | some v => for c in v.getUsedConstants do
                    if !seen.contains c then todo := todo.push c
      | none => pure ()
  let baseMods : List Name := [`LRSpectrumFull.NearestInteger, `LRSpectrumFull.MaxLoneliness, `LRSpectrumFull.ObsRootTorus,
    `LRSpectrumFull.ObsCrystallographic, `LRSpectrumFull.L5S3.Babai, `LRSpectrumFull.L5S3.LayerStep, `LRSpectrumFull.L5S4.Compl,
    `LRSpectrumFull.L5S4.Bordered, `LRSpectrumFull.L5S4.IntForm, `LRSpectrumFull.DValue]
  let mut perMod : Std.HashMap Name Nat := {}
  let mut baseDecls : Std.HashMap Name (Array String) := {}
  let mut ext : Std.HashMap Name Nat := {}
  let mut total := 0
  for n in seen.toList do
    total := total + 1
    match env.getModuleIdxFor? n with
    | none => pure ()   -- declared in this file (none here)
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if m.getRoot == `LRSpectrumFull then
        perMod := perMod.insert m (perMod.getD m 0 + 1)
        if baseMods.contains m then
          let k := match env.find? n with | some ci => kindOf ci | none => "?"
          baseDecls := baseDecls.insert m ((baseDecls.getD m #[]).push s!"{n} [{k}]")
      else
        ext := ext.insert m.getRoot (ext.getD m.getRoot 0 + 1)
  IO.println s!"reachable constants: {total}"
  IO.println "== project modules reached (module: constants) =="
  for (m, c) in (perMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)).toList do
    IO.println s!"{m}: {c}"
  IO.println "== pre-existing (base) modules: reached declarations =="
  for m in baseMods do
    let ds := (baseDecls.getD m #[]).qsort (· < ·)
    IO.println s!"-- {m}: {ds.size} declarations"
    for d in ds do IO.println s!"   {d}"
  IO.println "== non-project constants by root namespace (module root: constants) =="
  for (m, c) in (ext.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)).toList do
    IO.println s!"{m}: {c}"
