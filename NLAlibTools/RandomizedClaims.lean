/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib

/-!
# Every termination-only certificate has a randomized claim

A certificate whose routine has the specification `NLAlib.Ops.Routine.Spec.terminates` states
that the run succeeds within its resources and writes only its operands; it states nothing of
the values written. Its accuracy is a statement about the law of the tape, a
`NLAlib.Ops.RandomizedClaim` of that certificate.

This file checks, when it is built, that every such certificate of the library has one:

* a *certificate* is a declaration of the library whose type ends in `NLAlib.Ops.Algorithm`,
  for a model that is not a variable;
* it is *termination-only* when its definition or the proofs it carries use
  `Routine.Spec.terminates`, through the definitions of the specifications and certificates it
  is built from;
* a *claim of* a certificate is a declaration whose type ends in `RandomizedClaim A` with `A` an
  application of that certificate.

A termination-only certificate with no claim is an error, unless it is listed in `exempt` with
its reason. The list of claims is printed, so that a report can read which certificate each
claim is about from the type of the claim alone.
-/

open Lean Meta Elab Command

namespace NLAlibTools.RandomizedClaims

/-- Termination-only certificates that need no claim of their own, each with its reason. -/
def exempt : List (Name × String) :=
  [(`NLAlib.Schur.schurPipelineAlgorithm,
    "generic in its four stages, which are hypotheses; the claim is that of its instance " ++
      "NLAlib.Schur.denseSchurAlgorithm")]

/-- The constant at the head of the target of a type, and the constant at the head of its last
argument. -/
def targetHeads (ty : Expr) : MetaM (Option Name × Option Name × Bool) :=
  forallTelescopeReducing ty fun _ t => do
    let args := t.getAppArgs
    let last := args.back?.bind fun a => a.getAppFn.constName?
    let generic := args.size ≥ 2 && args[args.size - 2]!.getAppFn.isFVar
    pure (t.getAppFn.constName?, last, generic)

/-- Whether the definition of `c` uses `Routine.Spec.terminates`, following the definitions of
the constants in `follow`. `none` when the search does not finish. -/
def usesTerminates (env : Environment) (follow : NameSet) (c : Name) : Option Bool := Id.run do
  let mut todo : List Name := [c]
  let mut seen : NameSet := {}
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => return some false
    | a :: rest =>
      todo := rest
      if seen.contains a then continue
      seen := seen.insert a
      let value? := match env.find? a with
        | some (.defnInfo info) => some info.value
        | some (.thmInfo info) => some info.value
        | _ => none
      let some value := value? | continue
      let used := value.getUsedConstants
      if used.contains ``NLAlib.Ops.Routine.Spec.terminates then return some true
      -- the proof fields of a certificate are auxiliary declarations under its name
      todo := (used.toList.filter fun u => follow.contains u || (a.isPrefixOf u && u != a)) ++
        todo
  return none

run_cmd liftTermElabM do
  let env ← getEnv
  let mut certificates : Array Name := #[]
  let mut follow : NameSet := {}
  let mut claims : Array (Name × Name) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    if name.isInternal then continue
    let (head, last, generic) ← targetHeads info.type
    if head == some ``NLAlib.Ops.Algorithm then
      follow := follow.insert name
      unless generic do certificates := certificates.push name
    if head == some ``NLAlib.Ops.Routine.Spec then follow := follow.insert name
    if head == some ``NLAlib.Ops.RandomizedClaim then
      match last with
      | some certificate => claims := claims.push (name, certificate)
      | none =>
        unless (``NLAlib.Ops.RandomizedClaim).isPrefixOf name do
          logInfo m!"randomized claim {name}: for any certificate of its problem"
  let mut bare : Nat := 0
  for c in certificates.qsort (·.toString < ·.toString) do
    match usesTerminates env follow c with
    | none => logError m!"randomized claims: the search of {c} did not finish"
    | some false => pure ()
    | some true =>
      let own := claims.filter (·.2 == c)
      if own.isEmpty then
        match exempt.find? (·.1 == c) with
        | some (_, reason) => logInfo m!"termination-only {c}: exempt ({reason})"
        | none =>
          bare := bare + 1
          logError m!"the certificate {c} is termination-only and has no RandomizedClaim"
      else
        logInfo m!"termination-only {c}: claims {own.map (·.1)}"
  for (claim, certificate) in claims.qsort (·.1.toString < ·.1.toString) do
    logInfo m!"randomized claim {claim} of {certificate}"
  for (name, _) in exempt do
    unless certificates.contains name do
      logError m!"randomized claims: the exempt name {name} is not a certificate"
  logInfo m!"randomized claims: {claims.size} claims, {bare} termination-only certificates {""
    }without a claim"

end NLAlibTools.RandomizedClaims
