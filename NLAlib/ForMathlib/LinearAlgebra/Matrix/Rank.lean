/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Rank inequalities for matrices over a field

Facts about `Matrix.rank` that Mathlib does not yet have. Upstream candidates for
`Mathlib.LinearAlgebra.Matrix.Rank`.

Sylvester's and Frobenius's inequalities are stated additively, with no truncated subtraction,
so that `omega` and `linarith` can use them.

## Main results

* `Matrix.rank_eq_zero`: a matrix over a field has rank zero exactly when it is zero.
* `Matrix.rank_add_le`: subadditivity of rank.
* `Matrix.rank_add_rank_le_card_add_rank_mul`: Sylvester's rank inequality.
* `Matrix.rank_mul_add_rank_mul_le`: Frobenius's rank inequality.
* `Matrix.rank_fromBlocks_zero₁₂_zero₂₁`: rank of a block diagonal matrix.
* `Matrix.rank_fromBlocks₁₁`: rank additivity of the Schur complement.
* `Matrix.rank_fromCols_replicateCol_eq_iff`: the Rouché–Capelli solvability criterion.
* `Matrix.finrank_ker_toBlock_eq_finrank_ker_inv_toBlock_not`: complementary nullities.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- A matrix over a field has rank zero exactly when it is the zero matrix.
Port of `NLAlib.eq_zero_of_matrix_rank_eq_zero`. -/
@[simp]
theorem rank_eq_zero {A : Matrix m n K} : A.rank = 0 ↔ A = 0 := by
  sorry

/-- **Subadditivity of rank.** The rank of a sum is at most the sum of the ranks.
[HornJohnson2013, §0.4.5]; stated there for complex matrices, here over any field and any finite
index types. Port of `NLAlib.rank_add_le`.
Result: rank-inequalities -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  sorry

/-- The rank of a difference is at most the sum of the ranks. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  sorry

/-- **Sylvester's rank inequality.** For `A` with `n` columns and `B` with `n` rows,
`rank A + rank B ≤ n + rank (A * B)`.
[HornJohnson2013, §0.4.5]; stated there as `rank A + rank B - n ≤ rank (A B)`, here additively and
over any field. Port of `NLAlib.rank_add_rank_sub_card_le_rank_mul`.
Result: sylvester-rank-inequality, rank-inequalities -/
theorem rank_add_rank_le_card_add_rank_mul (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank ≤ Fintype.card n + (A * B).rank := by
  sorry

/-- **Frobenius's rank inequality.** `rank (A * B) + rank (B * C) ≤ rank B + rank (A * B * C)`.
[HornJohnson2013, §0.4.5]; here over any field and any finite index types.
Port of `NLAlib.rank_mul_add_rank_mul_le_rank_add_rank_mul_mul`.
Result: frobenius-rank-inequality, rank-inequalities -/
theorem rank_mul_add_rank_mul_le (A : Matrix l m K) (B : Matrix m n K) (C : Matrix n p K) :
    (A * B).rank + (B * C).rank ≤ B.rank + (A * B * C).rank := by
  sorry

/-- The rank of a block diagonal matrix is the sum of the ranks of its blocks. The blocks may be
rectangular. Port of `NLAlib.rank_fromBlocks_zero_zero_eq`, there over `ℝ`. -/
theorem rank_fromBlocks_zero₁₂_zero₂₁ (A : Matrix l m K) (D : Matrix p n K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  sorry

/-- **Rank additivity of the Schur complement.** With an invertible leading block `A`, the rank
of `fromBlocks A B C D` is the size of `A` plus the rank of the Schur complement
`D - C * ⅟A * B`. The trailing blocks may be rectangular.
[HornJohnson2013, §0.8.5]; here over any field. Port of
`NLAlib.rank_fromBlocks_eq_rank_add_rank_schur`, there over `ℝ`.
Result: schur-complement-rank -/
theorem rank_fromBlocks₁₁ [DecidableEq m] (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix l m K) (D : Matrix l n K) [Invertible A] :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * ⅟A * B).rank := by
  sorry

/-- **Rouché–Capelli.** Adjoining the column `b` to `A` leaves the rank unchanged exactly when
`A *ᵥ x = b` has a solution.
[HornJohnson2013, §0.4.2]. Port of `NLAlib.rank_fromCols_eq_iff_exists_mulVec_eq`.
Result: rouche-capelli -/
theorem rank_fromCols_replicateCol_eq_iff (A : Matrix m n K) (b : m → K) :
    (fromCols A (replicateCol Unit b)).rank = A.rank ↔ ∃ x, A *ᵥ x = b := by
  sorry

/-- **Complementary nullities.** For an invertible `A` and predicates `r` on rows and `c` on
columns, the block of `A` on rows `r` and columns `c` and the block of `A⁻¹` on rows `¬ c` and
columns `¬ r` have kernels of the same dimension. The blocks need not be square.
[HornJohnson2013, §0.7.5]; here over any field.
Port of `NLAlib.finrank_ker_toBlock_eq_finrank_ker_inverse_complement`.
Result: complementary-nullities -/
theorem finrank_ker_toBlock_eq_finrank_ker_inv_toBlock_not [DecidableEq n] (A : Matrix n n K)
    (hA : IsUnit A) (r c : n → Prop) [DecidablePred r] [DecidablePred c] :
    Module.finrank K (LinearMap.ker (A.toBlock r c).mulVecLin) =
      Module.finrank K
        (LinearMap.ker (A⁻¹.toBlock (fun i => ¬ c i) (fun i => ¬ r i)).mulVecLin) := by
  sorry

/-- The rank form of complementary nullities, stated additively: the rank of the block of `A`
on rows `r` and columns `c`, plus the number of columns outside `r`, equals the rank of the
complementary block of `A⁻¹` plus the number of columns in `c`.
[HornJohnson2013, §0.7.5]. Port of `NLAlib.card_columns_sub_rank_toBlock_eq_inverse_complement`,
there with truncated subtraction.
Result: complementary-nullities -/
theorem rank_toBlock_add_card_eq_rank_inv_toBlock_not_add_card [DecidableEq n] (A : Matrix n n K)
    (hA : IsUnit A) (r c : n → Prop) [DecidablePred r] [DecidablePred c] :
    (A.toBlock r c).rank + Fintype.card {j // ¬ r j} =
      (A⁻¹.toBlock (fun i => ¬ c i) (fun i => ¬ r i)).rank + Fintype.card {j // c j} := by
  sorry

end Matrix
