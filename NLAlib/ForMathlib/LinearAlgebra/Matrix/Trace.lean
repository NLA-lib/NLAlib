/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The trace of a block matrix

Upstream candidate for `Mathlib.LinearAlgebra.Matrix.Trace`.

## Main results

* `Matrix.trace_fromBlocks`: the trace of a block matrix is the sum of the traces of its diagonal
  blocks.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [AddCommMonoid R] {m n : Type*} [Fintype m] [Fintype n]

/-- The trace of a block matrix is the sum of the traces of its diagonal blocks. -/
theorem trace_fromBlocks (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) : (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp only [trace, diag_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂]

end Matrix
