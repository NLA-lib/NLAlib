/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Contracts
public import NLAlib.Eigensolvers.ShiftedQR.StorageNorm

/-!
# The rounded Frobenius norm as a pipeline stage

The norm estimate of the dense Schur pipeline is the merged Frobenius norm of the stored words
(`NLAlib.ShiftedQR.matrixNorm`, the scalar-lowered sequential Euclidean norm of the $2N^2$
component words) at a square order. Under the standard model it is two-sided accurate
(`NLAlib.Ops.RoundedScalarBlas.writes_nrm2_stdModel`), so it meets the norm-estimate contract
with the constants $1 \mp (2N_{\max}^2 + 2)\boldsymbol{u}$.

## Main definitions

* `NLAlib.Schur.frobNormStage`: the stage `[N] (A) → (S)`.

## Main results

* `NLAlib.Schur.frobNormStage_frobNormEstimateContract`: the stage meets
  `NLAlib.Schur.FrobNormEstimateContract`.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops

variable {O Q : Type} [Has ScalarOp O]

/-- **The Frobenius norm stage**: `NLAlib.ShiftedQR.matrixNorm` at the square order $N$. The
interface is `[N] (A) → (S)`, that of a norm-estimate stage. -/
def frobNormStage : Impl O Q := opsImpl% [N] (A) → (S) {
  run (ShiftedQR.matrixNorm (Op := O) (Tst := Q)).body [N, N] (A, S)
}

variable [Inhabited ℝ]

/-- **The rounded Frobenius norm is a two-sided norm estimate**: on a scalar machine with the
standard model at $\boldsymbol{u}$ and $(2N_{\max}^2 + 2)\boldsymbol{u} \le 1/2$,
`NLAlib.Schur.frobNormStage` meets `NLAlib.Schur.FrobNormEstimateContract` on the orders
$N \le N_{\max}$ with $c_1 = 1 - (2N_{\max}^2 + 2)\boldsymbol{u}$ and
$c_2 = 1 + (2N_{\max}^2 + 2)\boldsymbol{u}$ (`NLAlib.Ops.RoundedScalarBlas.writes_nrm2_stdModel`
on the $2N^2$ words, `NLAlib.ShiftedQR.sum_sq_matrixWords`). -/
theorem frobNormStage_frobNormEstimateContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) {nmax : ℕ}
    (hu : (2 * (nmax : ℝ) ^ 2 + 2) * u ≤ 1 / 2) :
    FrobNormEstimateContract (1 - (2 * (nmax : ℝ) ^ 2 + 2) * u)
      (1 + (2 * (nmax : ℝ) ^ 2 + 2) * u) nmax (frobNormStage (O := O) (Q := Q)) I :=
  sorry

end NLAlib.Schur
