/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Transfer
public import NLAlib.Ops.WeightedCost

/-!
# Matrix-kernel weights in the dense signature

Kernel weights isolate matrix calls for partition-sensitive analysis. Scalar operations,
samples, index literals and queries retain their separate full canonical accounting.

## Main results

* `NLAlib.Ops.Dense.matrixWeight`: supplied matrix weights and zero for other primitives.
* `NLAlib.Ops.Dense.kernelWeight`: weight by the largest matrix dimension.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Weight a matrix operation by a supplied cost of its largest dimension. Empty dimension
lists use zero as their largest dimension; well-formed calls have their declared shape. -/
def MatrixOp.dimensionWeight (T : ℕ → ℕ) (_ : MatrixOp) (ds : List ℕ) : ℕ :=
  T (ds.foldr max 0)

/-- Isolate the supplied matrix-operation weights. Other primitive classes have zero weight
in this projection, while the canonical full count continues to include them. -/
def Dense.matrixWeight (matrix : MatrixOp → List ℕ → ℕ) : DenseOp → List ℕ → ℕ
  | .matrix o, ds => matrix o ds
  | _, _ => 0

/-- Matrix-kernel weight of original operation/query counts. A matrix call costs the
supplied function of its largest dimension; other primitive classes and queries cost zero.
For a canonical instrumented count, compose this map with `Count.original`. -/
noncomputable def Dense.kernelWeight {Tst : Type} (T : ℕ → ℕ) : Count DenseOp Tst →+ ℕ :=
  Count.lift (Sum.elim (Dense.matrixWeight (MatrixOp.dimensionWeight T)) (fun _ _ => 0))

/-- A syntactically matrix-free dense program has zero matrix weight, for arbitrary matrix
weight functions and operand dimensions. Queries have zero weight in this projection. -/
theorem stmtWeightedCost_matrix_zero_of_allOps {Tst : Type}
    (W : MatrixOp → List ℕ → ℕ) (s : Stmt DenseOp Tst)
    (hs : s.allOps (fun o => match o with | .matrix _ => false | _ => true) = true)
    (idx : List ℕ) : stmtWeightedCost (Dense.matrixWeight W) (fun _ _ => 0) s idx = 0 := by
  apply stmtWeightedCost_zero_of_allOps _ _ _ s hs idx
  intro o ho ds
  cases o <;> first | rfl | cases ho

end NLAlib.Ops
