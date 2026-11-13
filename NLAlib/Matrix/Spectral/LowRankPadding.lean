/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Matrix.Norms.Block
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Low-rank residuals under compression and zero padding

Restricting rows and columns contracts the error of a factored approximation. Zero padding
cannot increase the optimal rank-constrained Frobenius residual: pad an optimal competitor
with zeros and use Eckart–Young. Relabelling coordinates preserves that optimal residual.
These facts allow oracle lower bounds to pass from a hard coordinate subspace to larger spaces.

## Main results

* `NLAlib.frobNorm_submatrix_sub_mul_le`: error contracts under coordinate compression.
* `NLAlib.frobNorm_fromBlocks_sub_truncatedSVD_le`: zero-padded optimal residual bound.
* `NLAlib.frobNorm_submatrix_sub_truncatedSVD`: coordinate-equivalence invariance.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q r u v : Type*}
  [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

/-- Restricting distinct rows and columns of a factored approximation contracts its Frobenius
error. The middle factor dimension is unchanged. No rank or field-specific assumption is needed
beyond $\Bbbk$ being real or complex. -/
theorem frobNorm_submatrix_sub_mul_le (A : Matrix m n 𝕜) (X : Matrix m r 𝕜)
    (Y : Matrix r n 𝕜) {i : p → m} {j : q → n}
    (hi : Function.Injective i) (hj : Function.Injective j) :
    frobNorm (A.submatrix i j - X.submatrix i id * Y.submatrix id j) ≤ frobNorm (A - X * Y) :=
  frobNorm_submatrix_le (A - X * Y) hi hj

/-- Padding a matrix with zero rows and columns cannot increase its optimal rank-$k$ Frobenius
residual: the zero padding of its truncated SVD is an admissible competitor of the same rank.
This inequality needs no full-rank or positive-dimensional assumption. -/
theorem frobNorm_fromBlocks_sub_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (Matrix.fromBlocks A (0 : Matrix m q 𝕜) (0 : Matrix p n 𝕜) 0 -
      truncatedSVD (Matrix.fromBlocks A (0 : Matrix m q 𝕜) (0 : Matrix p n 𝕜) 0) k) ≤
        frobNorm (A - truncatedSVD A k) := by
  let B := Matrix.fromBlocks (truncatedSVD A k) (0 : Matrix m q 𝕜) (0 : Matrix p n 𝕜) 0
  have hB : B.rank ≤ k := by
    dsimp only [B]
    rw [Matrix.rank_fromBlocks_zero₁₂_zero₂₁, Matrix.rank_zero, add_zero]
    exact rank_truncatedSVD_le A k
  refine (frobNorm_sub_truncatedSVD_le_of_rank_le _ hB).trans_eq ?_
  have hsub : Matrix.fromBlocks A (0 : Matrix m q 𝕜) (0 : Matrix p n 𝕜) 0 - B =
      Matrix.fromBlocks (A - truncatedSVD A k) (0 : Matrix m q 𝕜) (0 : Matrix p n 𝕜) 0 := by
    ext (i | i) (j | j) <;> simp [B, Matrix.fromBlocks]
  rw [hsub]
  apply (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1
  simp only [frobNorm_fromBlocks_sq, frobNorm_zero, zero_pow two_ne_zero, add_zero]

/-- A bijective relabelling of rows and columns preserves the optimal rank-$k$ Frobenius
residual. The chosen truncated matrices themselves need not commute with relabelling. -/
theorem frobNorm_submatrix_sub_truncatedSVD [Fintype u] [Fintype v]
    (A : Matrix m n 𝕜) (e₁ : u ≃ m) (e₂ : v ≃ n) (k : ℕ) :
    frobNorm (A.submatrix e₁ e₂ - truncatedSVD (A.submatrix e₁ e₂) k) =
      frobNorm (A - truncatedSVD A k) := by
  apply (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1
  simp only [frobNorm_sub_truncatedSVD_sq, singularValues_submatrix_equiv,
    Fintype.card_congr e₁, Fintype.card_congr e₂]

end NLAlib
