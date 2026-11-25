/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar
public import NLAlib.Ops.Catalog.Functional

/-!
# Scalar contracts with an exact-result range

Finite-exponent arithmetic can reject an operation. These local block functions require
the exact decoded target to lie in a declared range before returning the machine word.
Division also requires a nonzero decoded denominator, and square root a nonnegative input.
Copying and negation do not round. A numerical algorithm must prove these local conditions
before its calls; a mixed accuracy law for a total machine alone does not imply that it runs
under this rejecting interpretation.

## Main results

* `NLAlib.Ops.Machine.guardedFn`: explicit partial scalar functions.
* `NLAlib.Ops.IsGuardedScalar`: their local operation contracts.
* `NLAlib.Ops.isGuardedScalar_interp`: one joint realization of the contracts.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

open Classical in
/-- Scalar arithmetic that rejects an out-of-range exact target and invalid divisors or
roots. The returned word is the given machine's word, so its separate mixed accuracy law
applies on precisely the declared exact-result range. -/
noncomputable def Machine.guardedFn (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) :
    ScalarOp → BlockFn K
  | .lit q => { M.fn (.lit q) with
      fn := fun d w xs => if safe q then (M.fn (.lit q)).fn d w xs else none }
  | .add => .bin fun a b => if safe (dec a + dec b) then some (M.add a b) else none
  | .sub => .bin fun a b => if safe (dec a - dec b) then some (M.sub a b) else none
  | .mul => .bin fun a b => if safe (dec a * dec b) then some (M.mul a b) else none
  | .div => .bin fun a b =>
      if dec b ≠ 0 ∧ safe (dec a / dec b) then some (M.div a b) else none
  | .neg => M.fn .neg
  | .sqrt => .un fun a =>
      if 0 ≤ dec a ∧ safe (Real.sqrt (dec a)) then some (M.sqrt a) else none
  | .copy => M.fn .copy

/-- Every primitive satisfies its guarded local block-function contract. These contracts
promise success only when the target is in range; they contain no factorization or run. -/
def IsGuardedScalar [Has ScalarOp Op] (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop)
    (I : Interp Op Tst K) : Prop :=
  ∀ o : ScalarOp, I.IsFn .total (Has.inj o) (M.guardedFn dec safe o) AnyOperands

/-- Guarding does not change the declared dimensions of any scalar operation. -/
@[simp] theorem Machine.guardedFn_nd (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop)
    (o : ScalarOp) : (M.guardedFn dec safe o).nd = 0 := by
  cases o <;> rfl

/-- Guarding preserves the original scalar input block lengths. -/
@[simp] theorem Machine.guardedFn_inLens (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop)
    (o : ScalarOp) (d : List ℕ) :
    (M.guardedFn dec safe o).inLens d = (M.fn o).inLens d := by
  cases o <;> rfl

/-- Guarding preserves the one-cell scalar output shape. -/
@[simp] theorem Machine.guardedFn_outLens (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop)
    (o : ScalarOp) (d : List ℕ) : (M.guardedFn dec safe o).outLens d = [1] := by
  cases o <;> rfl

/-- The declared partial functions and exact comparisons have a joint interpretation.
Their domain is local scalar safety, so this witness does not assume any algorithm succeeds. -/
theorem isGuardedScalar_interp (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) :
    IsGuardedScalar M dec safe (Functional.interp dec (M.guardedFn dec safe)) ∧
      IsCmp dec (Functional.interp dec (M.guardedFn dec safe)) := by
  obtain ⟨hs, hc⟩ := Functional.interp_contracts dec (M.guardedFn dec safe)
  exact ⟨fun o => hs o, hc⟩

end NLAlib.Ops
