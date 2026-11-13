/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Iteration
public import NLAlib.Eigensolvers.ShiftedQR.IterationWords
public import NLAlib.Eigensolvers.ShiftedQR.IterationSearch
public import NLAlib.Eigensolvers.ShiftedQR.DecoupleState

/-!
# The concrete scalar iteration in capped decoupling

The actual scalar promising search and the exhaustive local Ritz kernel establish the
iteration's total word theorem. The same routine supplies the Ritz list's mathematical
optimality for the rapid-decoupling analysis. No additional primitive or execution assumption
is introduced when the iteration is composed into the capped loop.

## Main results

* `NLAlib.ShiftedQR.iteration_contract`: the concrete implemented iteration's local total law.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Actual scalar strategy code, under the declared scalar/index/comparison and local Ritz
contracts, supplies both its exact stored step and the mathematical Ritz optimality needed by
capped decoupling. The promising search is the concrete scalar binary-search tree. -/
theorem iteration_contract {M : Machine ℝ} {I : Interp O Q ℝ} {θ : ℝ}
    {K : KernelRoutines θ} (hS : IsScalar M I) (hE : ExactModel id M)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hK : IsEigenvalueKernels K I) : IterationContract θ iteration I := by
  intro n m D τ B α γ w p c tape μ H hHess hk hτ hB hD hDp hH hP hCst hl _ _
  have hFind : RitzSearchContract (findRitzSearch (Op := O) (Tst := Q)) I :=
    ritzSearchContract_findRitzSearch hS hE hC hL hQ
  have hIter := iterationWith_writes (tape := tape) (μ := μ) hS hE hL hC hK hFind
    hHess hk hτ hB hDp hD hH hP hCst hl
  change Writes .total I tape (iterationWith findRitzSearch).body _ _ _ μ
  refine hIter.mono le_rfl ?_
  intro μ' _ ⟨hp, hW⟩
  exact ⟨hp, K.ritz (n + 1) (2 ^ m) H, K.length_ritz _ _ _,
    K.optimal n (2 ^ m) H hHess (by positivity) hk, hW⟩

end NLAlib.ShiftedQR
