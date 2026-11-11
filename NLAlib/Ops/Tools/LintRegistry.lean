/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public meta import Lean

/-!
# Tools: the registry of the target linter

Diagnostic linter registration; formal certification is independent of these registrations.
Three kinds of names that the target linter
(`NLAlib/Ops/Tools/Lint.lean`) cannot infer from types, registered by commands:

* `ops_register_xi c₁ c₂ …`: operations that take a random word as an operand (`sraddXi`), which
  may occur only in the trees of implementation tables. Constructor names ending in `Xi` are
  ξ-taking by convention without registration.
* `ops_register_model c₁ …`: model primitives, interpretations a headline may name instead of
  quantifying over them.
* `ops_register_witness c₁ …`: witness theorems whose name does not start with `exists_`.

## Main results

The registration commands record names used by conditional headline guidance.
-/

@[expose] public section

meta section

namespace NLAlib.Ops.Tools.Lint

open Lean Elab Command

/-- The kind of a registered name. -/
inductive RegKind where
  /-- A ξ-taking primitive. -/
  | xi
  /-- A model primitive (an interpretation). -/
  | model
  /-- A witness theorem. -/
  | witness
  deriving BEq, Repr, Inhabited

/-- The registry. -/
initialize opsRegistry : SimplePersistentEnvExtension (RegKind × Name) (Array (RegKind × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- The name `n` is registered with the kind `k`. -/
def registered (env : Environment) (k : RegKind) (n : Name) : Bool :=
  (opsRegistry.getState env).any fun e => e.1 == k && e.2 == n

/-- Register names. -/
def registerNames (k : RegKind) (ids : Array Syntax) : CommandElabM Unit := do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    modifyEnv (opsRegistry.addEntry · (k, n))

/-- `ops_register_xi c …`: ξ-taking primitives. -/
syntax (name := regXi) "ops_register_xi " ident+ : command
/-- `ops_register_model c …`: model primitives. -/
syntax (name := regModel) "ops_register_model " ident+ : command
/-- `ops_register_witness c …`: witness theorems. -/
syntax (name := regWitness) "ops_register_witness " ident+ : command

/-- Elaborate `ops_register_xi`. -/
@[command_elab regXi] def elabRegXi : CommandElab := fun stx => registerNames .xi stx[1].getArgs
/-- Elaborate `ops_register_model`. -/
@[command_elab regModel] def elabRegModel : CommandElab := fun stx =>
  registerNames .model stx[1].getArgs
/-- Elaborate `ops_register_witness`. -/
@[command_elab regWitness] def elabRegWitness : CommandElab := fun stx =>
  registerNames .witness stx[1].getArgs

end NLAlib.Ops.Tools.Lint
