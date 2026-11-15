/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DeflationCertificate
public import NLAlib.Eigensolvers.ShiftedQR.IterationCorrect
public import NLAlib.Eigensolvers.ShiftedQR.Decouple

/-!
# Canonical exact scalar shifted QR deflation

One fixed scalar/index program implements the full shifted QR strategy and deflation
worklist. Its only spectral primitives are the explicit local Ritz and small-block root
kernels. Actual raw matrix/parameter words are supplied; tolerance initialization, shifts,
Givens rotations, inverse-row searches, candidate tests, capped decoupling and the worklist
all execute in the same fixed tree.

The total certificate returns actual stored roots of a matrix within the declared deflation
backward error. It includes every instruction count, work/span charge, scratch bound and
initial-plus-scratch payload under the same jointly realized operation model.

## Main results

* `NLAlib.ShiftedQR.scalarDecouple`: concrete implemented scalar capped decoupling.
* `NLAlib.ShiftedQR.scalarDecouple_contract`: its total local theorem.
* `NLAlib.ShiftedQR.exactAlgorithm`: the closed raw-input total deflation certificate.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Fixed scalar capped decoupling with the actual promising-Ritz search substituted into
its actual strategy iteration. Neither an iteration nor a decoupling loop is a primitive. -/
def scalarDecouple : Impl Op Tst := decouple (iteration (O := Op) (Q := Tst))

/-- Standard scalar/index/comparison contracts and the two declared local spectral routines
prove total decoupling for the fixed concrete implementation under raw quantitative input
hypotheses. No iteration or successful-execution assumption is left to the caller. -/
theorem scalarDecouple_contract {M : Machine ℝ} {I : Interp Op Tst ℝ} {θ : ℝ}
    {K : KernelRoutines θ} (hS : IsScalar M I) (hE : ExactModel id M)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hK : IsEigenvalueKernels K I) : DecouplingContract θ scalarDecouple I := by
  have hIter : IterationContract θ (iteration (O := Op) (Q := Tst)) I :=
    iteration_contract hS hE hL hC hQ hK
  change DecouplingContract θ (decouple (iteration (O := Op) (Q := Tst))) I
  exact decouple_contract hS hE hL hC (iteration (O := Op) (Q := Tst)) hIter

/-- Every call in the full fixed program has the declared scalar/index/spectral operand
formats. The check is structural and independent of numerical data and kernel cost choices. -/
theorem wellTyped_exactProgram
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    (deflationProgram scalarDecouple).wellTyped (resources kernelWork kernelWorkspace)
      deflationProblem.formats = true := by
  rfl

/-- The closed exact shifted QR algorithm computes actual stored roots of a nearby matrix
under its raw Hessenberg, spectral separation, eigenvector-conditioning and parameter
hypotheses. Every resource bound refers to this same concrete scalar program. Explicit local
spectral-kernel work and workspace charges are supplied by the operation model.
Algorithm: shifted-qr (run model) -/
noncomputable def exactAlgorithm
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Algorithm (model deflationProblem exactRoutines (resources kernelWork kernelWorkspace))
      (deflationSpecification scalarDecouple kernelWork kernelWorkspace) :=
  deflationAlgorithm scalarDecouple kernelWork kernelWorkspace
    (wellTyped_exactProgram kernelWork kernelWorkspace)
    (fun _ _ _ hS hL hC hQ hK =>
      scalarDecouple_contract hS exactModel_exactMachine hL hC hQ hK)

end NLAlib.ShiftedQR
