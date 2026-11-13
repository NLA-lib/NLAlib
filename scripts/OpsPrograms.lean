import NLAlib
open Lean Meta Elab Command

/-! # Fixed Ops programs and canonical certificates

Programs are finite first-order `Ops.Program` values. `Ops.Algorithm` certifies the declared
problem, jointly realizable primitive model and output/resource specification on the same
total instrumented execution. These requirements are checked by Lean's types, without the
former registry of `Computation.Prog` trees.

This integration check inventories the new program and certificate interfaces, checks that
declared programs have executable definitions, and rejects an imported old execution core.
The whole-library axiom audit and kernel replay remain separate mandatory checks. The
canonical rejection and accounting fixtures are checked by importing the library below.
-/

run_cmd liftTermElabM do
  let env ← getEnv
  let mut programs : Nat := 0
  let mut algorithms : Nat := 0
  for moduleName in env.header.moduleNames do
    if (`NLAlib.Computation).isPrefixOf moduleName ||
        (`NLAlib.Matrix.Computation).isPrefixOf moduleName ||
        (`NLAlib.RandomMatrix.Computation).isPrefixOf moduleName then
      logError m!"retired execution module is still imported: {moduleName}"
  for (name, info) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    if name.isInternal then continue
    let head ← forallTelescopeReducing info.type fun _ target =>
      pure target.getAppFn.constName?
    if head == some ``NLAlib.Ops.Program then
      programs := programs + 1
      if let .opaqueInfo _ := info then
        logError m!"E2 program {name} is opaque"
      if info.isUnsafe || info.isPartial then
        logError m!"E2 program {name} is unsafe or partial"
      if (Compiler.implementedByAttr.getParam? env name).isSome then
        logError m!"E2 program {name} has implemented_by"
      if isNoncomputable env name then
        logError m!"E2 program {name} is noncomputable"
    if head == some ``NLAlib.Ops.Algorithm then
      algorithms := algorithms + 1
  if programs = 0 ∨ algorithms = 0 then
    logError m!"missing Ops coverage: {programs} programs, {algorithms} certificates"
  logInfo m!"ops programs: {programs} program declarations, {algorithms} certificate declarations"

-- These are total canonical proofs, rather than conclusions accepted by a heuristic linter.
#check NLAlib.Ops.Examples.Certification.certifies_repeatProgram
#check NLAlib.Ops.Examples.Certification.repeatAlgorithmLinked
#check NLAlib.Ops.Tools.profileProgram_work
#check NLAlib.Ops.Tools.profileProgram_span

-- Structural rejection laws used by the kernel-checked examples: totality cannot be replaced
-- by a liberal assertion, and the program cannot be an unconditional abort.
#check NLAlib.Ops.Algorithm.not_nonempty
#check NLAlib.Ops.Algorithm.body_ne_abort
#check NLAlib.Ops.Algorithm.run_ne_none
