import NLAlib
open Lean Elab Command

/-! # Axiom audit

Every declaration reachable through `import NLAlib` (public and private, theorems, definitions
and instances) may depend only on `propext`, `Classical.choice` and `Quot.sound`. In particular
nothing depends on `sorryAx`. Run with `lake env lean scripts/Audit.lean`; a nonzero exit code
means a violation. -/

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    let inLibrary := match env.getModuleIdxFor? name with
      | some i => (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]!
      | none => false
    if inLibrary then
      count := count + 1
      let extra := (← collectAxioms name).filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        bad := bad + 1
        logError m!"{name} depends on forbidden axioms {extra}"
  logInfo m!"audited {count} declarations reachable through import NLAlib; {bad} violations"
