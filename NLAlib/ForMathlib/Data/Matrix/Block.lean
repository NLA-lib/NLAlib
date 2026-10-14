/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Block

/-!
# Sums of block matrices

A finite sum of block matrices is the block matrix of the sums of the blocks, the `Finset.sum`
companion of Mathlib's `Matrix.fromBlocks_add`. Upstream candidate for `Mathlib.Data.Matrix.Block`.

## Main results

* `Matrix.sum_fromBlocks`.
-/

@[expose] public section

namespace Matrix

variable {α ι : Type*} [AddCommMonoid α] {l m n o : Type*}

/-- A finite sum of block matrices is the block matrix of the sums of the blocks. -/
theorem sum_fromBlocks (s : Finset ι) (A : ι → Matrix n l α) (B : ι → Matrix n m α)
    (C : ι → Matrix o l α) (D : ι → Matrix o m α) :
    ∑ i ∈ s, fromBlocks (A i) (B i) (C i) (D i) =
      fromBlocks (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) (∑ i ∈ s, D i) := by
  ext (i | i) (j | j) <;>
    simp only [sum_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂]

end Matrix
