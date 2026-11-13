/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Profiles.DenseWeight

/-!
# Matrix-free fragments of the fixed spectral bisection solver

Initialization, sampling, leaves, the bottom boundary and final copies contain no matrix
primitive. Their matrix-kernel projection is zero for arbitrary matrix weights and index
environments. Scalar instructions, samples, queries and structural work remain charged by
the full canonical resource configuration.

## Main results

* `NLAlib.SpectralBisection.initializeArenas_matrixWork_zero`: actual solver initialization.
* `NLAlib.SpectralBisection.bottomLevel_matrixWork_zero`: initialized recursion boundary.
* `NLAlib.SpectralBisection.rootResultCopy_matrixWork_zero`: supplied-output copies.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable (W : MatrixOp → List ℕ → ℕ)

local notation "mw" => Dense.matrixWeight W
local notation "qz" => (fun (_ : CmpTst ⊕ IdxTst) (_ : List ℕ) => 0)

/-- Actual constants, root matrix, size slots and level parameters use only scalar/index calls. -/
theorem initializeArenas_matrixWork_zero (idx : List ℕ) :
    stmtWeightedCost mw qz
      (initializeArenas (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body idx = 0 :=
  stmtWeightedCost_matrix_zero_of_allOps W _ (by rfl) idx

/-- The complete preparation stage retains its sampling and scalar costs outside this projection. -/
theorem downPrepareImpl_matrixWork_zero (idx : List ℕ) :
    stmtWeightedCost mw qz
      (downPrepareImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body idx = 0 :=
  stmtWeightedCost_matrix_zero_of_allOps W _ (by rfl) idx

/-- Both terminal leaf variants contain no matrix primitives. -/
theorem leaf_matrixWork_zero (diagonal : Bool) (idx : List ℕ) :
    stmtWeightedCost mw qz
      (leaf (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst) diagonal) idx = 0 := by
  apply stmtWeightedCost_matrix_zero_of_allOps
  cases diagonal <;> rfl

/-- A recursion-boundary identity and zero eigenvalues are computed by visible scalar loops. -/
theorem bottomResultImpl_matrixWork_zero (idx : List ℕ) :
    stmtWeightedCost mw qz
      (bottomResultImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body idx = 0 :=
  stmtWeightedCost_matrix_zero_of_allOps W _ (by rfl) idx

/-- The entire bottom pass has zero matrix-kernel weight, including all bounded size queries. -/
theorem bottomLevel_matrixWork_zero (idx : List ℕ) :
    stmtWeightedCost mw qz
      (bottomLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) idx = 0 :=
  stmtWeightedCost_matrix_zero_of_allOps W _ (by rfl) idx

/-- Copying the final reconstructed basis and eigenvalues calls scalar-copy primitives. -/
theorem rootResultCopy_matrixWork_zero (idx : List ℕ) :
    stmtWeightedCost mw qz
      (rootResultCopy (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body idx = 0 :=
  stmtWeightedCost_matrix_zero_of_allOps W _ (by rfl) idx

end NLAlib.SpectralBisection
