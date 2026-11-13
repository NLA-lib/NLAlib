/-! # Axiom audit of the new core (body; `scripts/ops/audit.py` prepends the imports)

Every constant declared in a module `NLAlib.Ops.*` may depend only on `propext`,
`Classical.choice` and `Quot.sound` (so no `sorryAx`, no `Lean.ofReduceBool` from
`native_decide`), is neither `unsafe` nor `partial` (except the compiler's `_unsafe_rec` copy of a
safe definition), and has no `implemented_by`. A violation is an error, so `lean` exits nonzero.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut thms : Nat := 0
  let mut bad : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless (`NLAlib.Ops).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    count := count + 1
    if info matches .thmInfo _ then thms := thms + 1
    let aux := match name with
      | .str p "_unsafe_rec" => info.isPartial && match env.find? p with
        | some (.defnInfo d) => d.safety == .safe
        | _ => false
      | _ => false
    if (info.isUnsafe || info.isPartial) && !aux then
      bad := bad + 1
      logError m!"{name} is unsafe or partial"
    if (Compiler.implementedByAttr.getParam? env name).isSome then
      bad := bad + 1
      logError m!"{name} has implemented_by"
    let extra := (← collectAxioms name).filter (fun a => !allowed.contains a)
    unless extra.isEmpty do
      bad := bad + 1
      logError m!"{name} depends on {extra}"
  logInfo m!"AUDIT: {count} constants ({thms} theorems) in NLAlib.Ops.*; {bad} violations"
