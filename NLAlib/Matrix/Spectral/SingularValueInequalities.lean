/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Inequalities for singular values

Singular values are subadditive in Weyl's sense, `1`-Lipschitz in the spectral norm,
submultiplicative, decrease under projections and under passing to submatrices, and move by at
most `r` positions under a perturbation of rank `r`. Because singular values are padded with
zeros, none of these statements carries an index side condition.

`NLAlib.singularGap A k` is the gap `singularValues A (k - 1) - singularValues A k` separating the
`k` largest singular values from the rest.

## Main definitions

* `NLAlib.singularGap`: the gap below the `k` largest singular values.

## Main results

* `NLAlib.singularValues_add_le`: Weyl's inequality for singular values.
* `NLAlib.abs_singularValues_sub_le_specNorm`: singular values are `1`-Lipschitz.
* `NLAlib.singularValues_mul_le_specNorm_mul`, `NLAlib.singularValues_mul_add_le`: products.
* `NLAlib.singularValues_add_le_of_rank_le`: low-rank perturbations.
* `NLAlib.singularValues_submatrix_le`: submatrices.
* `IsStarProjection.singularValues_mul_le`: projections.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p] [Fintype q]

/-! ### Sums -/

/-- **Weyl's inequality for singular values.** `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`, for all
indices from `0`. [HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_add_add_le`.
Result: weyl-singular-values -/
theorem singularValues_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    singularValues (A + B) (i + j) ≤ singularValues A i + singularValues B j := by
  sorry

/-- A perturbation raises each singular value by at most its spectral norm.
Port of `NLAlib.singularValues_add_le_add_specNorm`. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix m n 𝕜) (k : ℕ) :
    singularValues (A + E) k ≤ singularValues A k + specNorm E := by
  sorry

/-- **Singular values are `1`-Lipschitz in the spectral norm.**
[HornJohnson2013, Corollary 7.3.5].
Port of `NLAlib.abs_singularValues_sub_le_specNorm`.
Result: weyl-singular-values, singular-value-perturbation -/
theorem abs_singularValues_sub_le_specNorm (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularValues A k - singularValues B k| ≤ specNorm (A - B) := by
  sorry

/-- Singular values are `1`-Lipschitz in the Frobenius norm.
Port of `NLAlib.abs_singularValues_sub_le_frobNorm`. -/
theorem abs_singularValues_sub_le_frobNorm (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularValues A k - singularValues B k| ≤ frobNorm (A - B) := by
  sorry

/-- **Low-rank perturbation.** If `B` has rank at most `r` then `σ_{k+r}(A + B) ≤ σ_k(A)`.
[HornJohnson1991, Theorem 3.3.16].
Result: low-rank-interlacing -/
theorem singularValues_add_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {r : ℕ}
    (hB : B.rank ≤ r) (k : ℕ) : singularValues (A + B) (k + r) ≤ singularValues A k := by
  sorry

/-! ### Products -/

/-- A left factor scales singular values by at most its spectral norm.
[HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_mul_le_specNorm_mul`. -/
theorem singularValues_mul_le_specNorm_mul (B : Matrix l m 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (B * A) k ≤ specNorm B * singularValues A k := by
  sorry

/-- A right factor scales singular values by at most its spectral norm.
Port of `NLAlib.singularValues_mul_le_mul_specNorm`. -/
theorem singularValues_mul_le_mul_specNorm (A : Matrix m n 𝕜) (C : Matrix n p 𝕜) (k : ℕ) :
    singularValues (A * C) k ≤ singularValues A k * specNorm C := by
  sorry

/-- **Singular values of a product.** `σ_{i+j}(A * B) ≤ σ_i(A) * σ_j(B)`.
[HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_mul_add_le`, there over `ℝ`.
Result: weyl-singular-values-product -/
theorem singularValues_mul_add_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (i j : ℕ) :
    singularValues (A * B) (i + j) ≤ singularValues A i * singularValues B j := by
  sorry

/-- A left factor `T` with `Tᴴ * T ≤ a • 1` enlarges squared singular values by at most `a`. -/
theorem sq_singularValues_mul_le_of_conjTranspose_mul_self_le [DecidableEq m]
    {T : Matrix l m 𝕜} {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜)
    (k : ℕ) : singularValues (T * X) k ^ 2 ≤ a * singularValues X k ^ 2 := by
  sorry

/-- A left factor `T` with `a • 1 ≤ Tᴴ * T` shrinks squared singular values by at most `a`. This
is how a subspace embedding transfers singular values from the sketched matrix to the original
one. -/
theorem mul_sq_singularValues_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) (k : ℕ) :
    a * singularValues X k ^ 2 ≤ singularValues (T * X) k ^ 2 := by
  sorry

/-! ### Submatrices and projections -/

/-- **Singular values of a submatrix.** A submatrix selected by injective maps has singular
values at most those of the matrix. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_submatrix_rows_le` and `NLAlib.singularValues_submatrix_cols_le`,
there over `ℝ`.
Result: singular-value-interlacing -/
theorem singularValues_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) (k : ℕ) :
    singularValues (A.submatrix r c) k ≤ singularValues A k := by
  sorry

/-- **Interlacing for deleted columns.** If `c` selects `card p` of the `card p + d` columns of
`A`, then `σ_{k+d}(A) ≤ σ_k(A.submatrix id c)`. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_le_submatrix_cols`, there over `ℝ` with truncated subtraction.
Result: singular-value-interlacing -/
theorem singularValues_le_singularValues_submatrix_cols (A : Matrix m n 𝕜) {c : p → n}
    (hc : Function.Injective c) {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) (k : ℕ) :
    singularValues A (k + d) ≤ singularValues (A.submatrix id c) k := by
  sorry

/-- **Interlacing for deleted rows.** If `r` selects `card l` of the `card l + d` rows of `A`,
then `σ_{k+d}(A) ≤ σ_k(A.submatrix r id)`. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_le_submatrix_rows`, there over `ℝ` with truncated subtraction.
Result: singular-value-interlacing -/
theorem singularValues_le_singularValues_submatrix_rows (A : Matrix m n 𝕜) {r : l → m}
    (hr : Function.Injective r) {d : ℕ} (hd : Fintype.card l + d = Fintype.card m) (k : ℕ) :
    singularValues A (k + d) ≤ singularValues (A.submatrix r id) k := by
  sorry

/-- Left multiplication by an orthogonal projector does not increase any singular value.
Port of `NLAlib.singularValues_residual_le`, there for the residual of an orthonormal `Q`. -/
theorem _root_.IsStarProjection.singularValues_mul_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (P * A) k ≤ singularValues A k := by
  sorry

/-- The projection residual has singular values at most those of the matrix. -/
theorem singularValues_one_sub_rangeProjector_mul_le [DecidableEq m] (Y : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues ((1 - rangeProjector Y) * A) k ≤ singularValues A k := by
  sorry

/-! ### The singular gap -/

/-- The **singular gap** below the `k` largest singular values: `σ_{k-1}(A) - σ_k(A)` with
singular values indexed from `0`, the gap that separates the leading `k`-dimensional singular
subspaces from the rest. The index is the dimension of those subspaces. With truncated
subtraction `singularGap A 0 = 0`, so a hypothesis `0 < singularGap A k` already excludes
`k = 0`. -/
noncomputable def singularGap (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  singularValues A (k - 1) - singularValues A k

/-- The singular gap at dimension zero is zero. -/
@[simp]
theorem singularGap_zero (A : Matrix m n 𝕜) : singularGap A 0 = 0 := by
  sorry

/-- The singular gap at dimension `k + 1` is `σ_k - σ_{k+1}`. This is the form to compute
with. -/
theorem singularGap_succ (A : Matrix m n 𝕜) (k : ℕ) :
    singularGap A (k + 1) = singularValues A k - singularValues A (k + 1) := by
  sorry

/-- The singular gap is nonnegative. -/
theorem singularGap_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularGap A k := by
  sorry

/-- **Stability of the singular gap.** A perturbation changes the gap by at most twice its
spectral norm. -/
theorem abs_singularGap_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularGap A k - singularGap B k| ≤ 2 * specNorm (A - B) := by
  sorry

end NLAlib
