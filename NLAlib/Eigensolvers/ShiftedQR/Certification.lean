/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.StepProgram

/-!
# Canonical total exact shifted QR certification

The exact arithmetic model declares only scalar arithmetic and comparisons. The same scalar
program returns the mathematical shifted step for every raw input matrix and shift and meets
its full count, work, span, scratch and resident-payload bounds. No numerical kernel outside
the scalar signature is assumed for a single shifted step.

## Main results

* `NLAlib.ShiftedQR.stepAlgorithm`: the canonical certificate under any exact real machine.
* `NLAlib.ShiftedQR.exactStepAlgorithm`: the closed exact-arithmetic instance.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The scalar-only model certifies the raw shifted QR step, with total output and complete
resources from its fixed syntax. Exact arithmetic is the only numerical hypothesis; input
matrix words and shift words are unrestricted.
Algorithm: shifted-qr-step (run model) -/
noncomputable def stepAlgorithm (M : Machine ℝ) (hE : ExactModel id M) :
    Algorithm (RoundedScalarBlas.model stepProblem M) stepSpecification := by
  refine stepInputs.algorithm (fun _ _ => stepSpec) (ht := wellTyped_stepProgram)
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hCmp⟩ := RoundedScalarBlas.model_laws hI
    exact stepRoutine_meets hS hE hCmp
  · intro d _ x _ _
    trivial
  · intro d _ x τ m' hfr hpos ys hys hrel c _
    read_outputs hys as (zs)
    have hval : zs = matrixWords (shiftedQRStep (stepInputMatrix d x) (stepInputShift d x)) := by
      have h : zs = matrixWords (shiftedQRStep
          (matrixOfWords (d 0 + 1) (matrixWords (stepInputMatrix d x)))
          (stepInputShift d x)) := hrel
      rw [matrixOfWords_matrixWords] at h
      exact h
    refine ⟨hpos, by simpa [Problem.initial] using hfr.length_eq, ?_⟩
    rw [hval] at hzs
    exact hzs
  · intro d _ x
    rw [initialBytes_stepProblem]
    exact le_rfl

/-- The canonical exact real scalar machine gives a closed, jointly realized exact operation
model for the single shifted step. The word-level output and every resource obligation are
included in this value. -/
noncomputable def exactStepAlgorithm :
    Algorithm (RoundedScalarBlas.model stepProblem exactMachine) stepSpecification :=
  stepAlgorithm exactMachine exactModel_exactMachine

end NLAlib.ShiftedQR
