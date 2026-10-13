/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Norms.Block
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Singular values

`NLAlib.singularValues A k` is the `k`-th largest singular value of a matrix `A` of any shape,
indexed from `0`, non-increasing, and `0` for `k` at least the rank of `A`. It is Mathlib's
`LinearMap.singularValues` of the map `x ↦ A *ᵥ x` between Euclidean spaces, as a function
`ℕ → ℝ`; `NLAlib.singularValues_eq_linearMap` is the bridge, by `rfl`.

The largest singular value is `singularValues A 0 = specNorm A`. For a matrix with `n` columns,
the smallest singular value is `singularValues A k` with `k + 1 = Fintype.card n`; it is positive
exactly when `A` has full column rank.

## Main definitions

* `NLAlib.singularValues`: the sorted, zero-padded singular values.

## Main results

* `NLAlib.sq_singularValues`: `singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k`, for every `k`.
* `NLAlib.singularValues_pos_iff`: positivity exactly below the rank.
* `NLAlib.singularValues_zero_eq_specNorm`, `NLAlib.frobNorm_sq_eq_sum_singularValues_sq`: the two
  norms in terms of singular values.
* `NLAlib.HasOrthonormalCols.singularValues_mul_left`: invariance under orthonormal factors.
* `NLAlib.le_singularValues_of_forall_mem`, `NLAlib.singularValues_le_of_forall_mem`: the
  variational bounds.
* `NLAlib.singularValues_last_mul_norm_le`: the smallest singular value bounds `‖A x‖` below.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **singular values** of a matrix, in non-increasing order, indexed from `0` and padded with
zeros: `singularValues A k = 0` for `k ≥ rank A`. This is Mathlib's `LinearMap.singularValues` of
the map `x ↦ A *ᵥ x` from `EuclideanSpace 𝕜 n` to `EuclideanSpace 𝕜 m`, as a function.
[HornJohnson2013, §2.6]. -/
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ :=
  ⇑(LinearMap.singularValues
    ((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap))

/-- **Bridge to Mathlib.** `singularValues A` is `LinearMap.singularValues` of
`Matrix.toEuclideanLin A`. Port of `NLAlib.singularValues_eq_linearMap`. -/
theorem singularValues_eq_linearMap [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValues A = ⇑(Matrix.toEuclideanLin A).singularValues :=
  rfl

/-! ### Basic properties -/

/-- Singular values are nonnegative. -/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularValues A k := by
  sorry

/-- Singular values are non-increasing. -/
theorem singularValues_antitone (A : Matrix m n 𝕜) : Antitone (singularValues A) := by
  sorry

/-- **Singular values are the square roots of the eigenvalues of the Gram matrix**, for every
index: both sequences are zero-padded. [HornJohnson2013, §2.6].
Port of `NLAlib.sq_singularValues_eq_eigenvalues₀`. -/
theorem sq_singularValues (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k := by
  sorry

/-- The same with the other Gram matrix: `singularValues A k ^ 2 = eigenvalue (A * Aᴴ) k`. -/
theorem sq_singularValues_eq_eigenvalue_mul_conjTranspose_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (A * Aᴴ) k := by
  sorry

/-- A singular value is positive exactly when its index is below the rank.
Port of `NLAlib.singularValues_pos_iff`. -/
theorem singularValues_pos_iff (A : Matrix m n 𝕜) {k : ℕ} :
    0 < singularValues A k ↔ k < A.rank := by
  sorry

/-- A singular value vanishes exactly when its index is at least the rank. -/
theorem singularValues_eq_zero_iff (A : Matrix m n 𝕜) {k : ℕ} :
    singularValues A k = 0 ↔ A.rank ≤ k := by
  sorry

/-- Singular values vanish from the number of rows on. -/
theorem singularValues_of_card_rows_le (A : Matrix m n 𝕜) {k : ℕ} (hk : Fintype.card m ≤ k) :
    singularValues A k = 0 := by
  sorry

/-- Singular values vanish from the number of columns on. -/
theorem singularValues_of_card_cols_le (A : Matrix m n 𝕜) {k : ℕ} (hk : Fintype.card n ≤ k) :
    singularValues A k = 0 := by
  sorry

/-- The singular values of the zero matrix are zero. -/
@[simp]
theorem singularValues_zero : singularValues (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- Only the zero matrix has all singular values zero. -/
theorem singularValues_eq_zero {A : Matrix m n 𝕜} : singularValues A = 0 ↔ A = 0 := by
  sorry

/-! ### Norms -/

/-- **The largest singular value is the spectral norm.**
Port of `NLAlib.singularValues_zero_eq_specNorm`. -/
theorem singularValues_zero_eq_specNorm (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A := by
  sorry

/-- Every singular value is at most the spectral norm. -/
theorem singularValues_le_specNorm (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≤ specNorm A := by
  sorry

/-- **The squared Frobenius norm is the sum of the squared singular values.** The sum may be
taken over any range that reaches the rank; this is the form over the number of columns.
[HornJohnson2013, §2.6]. Port of `NLAlib.frobSq_eq_sum_sq_singularValues`. -/
theorem frobNorm_sq_eq_sum_singularValues_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range (Fintype.card n), singularValues A k ^ 2 := by
  sorry

/-- The squared Frobenius norm is the sum of the squared singular values up to any index that
reaches the rank. Port of `NLAlib.frobSq_eq_sum_rank_singularValues_sq`. -/
theorem frobNorm_sq_eq_sum_range_singularValues_sq (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range N, singularValues A k ^ 2 := by
  sorry

/-- The squared Frobenius norm is at most the rank times the squared spectral norm.
Port of `NLAlib.frobSq_le_rank_mul_specNorm_sq`. -/
theorem frobNorm_sq_le_rank_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ A.rank * specNorm A ^ 2 := by
  sorry

/-- The Frobenius norm is at most `√(rank A)` times the spectral norm.
[GolubVanLoan2013, (2.3.7)]. Port of `NLAlib.frobNorm_le_sqrt_rank_mul_specNorm`. -/
theorem frobNorm_le_sqrt_rank_mul_specNorm (A : Matrix m n 𝕜) :
    frobNorm A ≤ √(A.rank : ℝ) * specNorm A := by
  sorry

/-! ### Transformations -/

/-- The conjugate transpose has the same singular values.
Port of `NLAlib.singularValues_conjTranspose`. -/
@[simp]
theorem singularValues_conjTranspose (A : Matrix m n 𝕜) :
    singularValues Aᴴ = singularValues A := by
  sorry

/-- The transpose has the same singular values. -/
@[simp]
theorem singularValues_transpose (A : Matrix m n 𝕜) : singularValues Aᵀ = singularValues A := by
  sorry

/-- Scaling a matrix scales its singular values by the modulus of the scalar. -/
theorem singularValues_smul (c : 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = ‖c‖ * singularValues A k := by
  sorry

/-- Scaling a matrix by a real number scales its singular values by the absolute value.
Port of `NLAlib.singularValues_smul`, there over `ℝ`. -/
theorem singularValues_real_smul (c : ℝ) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = |c| * singularValues A k := by
  sorry

/-- Negation does not change the singular values. -/
@[simp]
theorem singularValues_neg (A : Matrix m n 𝕜) : singularValues (-A) = singularValues A := by
  sorry

/-- Relabelling rows and columns by bijections does not change the singular values.
Port of `NLAlib.singularValues_reindex`. -/
@[simp]
theorem singularValues_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    singularValues (A.submatrix e₁ e₂) = singularValues A := by
  sorry

/-- Matrices with the same Gram matrix have the same singular values, whatever their numbers of
rows. Port of `NLAlib.singularValues_eq_of_gram_eq`. -/
theorem singularValues_eq_of_conjTranspose_mul_self_eq {A : Matrix m n 𝕜} {B : Matrix l n 𝕜}
    (h : Aᴴ * A = Bᴴ * B) : singularValues A = singularValues B := by
  sorry

/-- Left multiplication by a matrix with orthonormal columns preserves the singular values.
Port of `NLAlib.singularValues_isometry_mul`. -/
theorem HasOrthonormalCols.singularValues_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (Q * A) = singularValues A := by
  sorry

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the singular values. Port of `NLAlib.singularValues_mul_isometry_conjTranspose`. -/
theorem HasOrthonormalCols.singularValues_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (A * Qᴴ) = singularValues A := by
  sorry

/-! ### Variational bounds -/

/-- **Courant–Fischer for singular values, lower bound.** If `c * ‖x‖ ≤ ‖A x‖` on a subspace of
dimension at least `k + 1`, then `c ≤ singularValues A k`.
[HornJohnson2013, Theorem 7.3.8].
Port of `NLAlib.le_singularValues_of_forall_mem`, there with squared norms as dot products. -/
theorem le_singularValues_of_forall_mem (A : Matrix m n 𝕜) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜))
    (hS : k + 1 ≤ Module.finrank 𝕜 S) {c : ℝ}
    (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) :
    c ≤ singularValues A k := by
  sorry

/-- **Courant–Fischer for singular values, upper bound.** If `‖A x‖ ≤ c * ‖x‖` on a subspace of
codimension at most `k`, with `0 ≤ c`, then `singularValues A k ≤ c`.
[HornJohnson2013, Theorem 7.3.8].
Port of `NLAlib.singularValues_le_of_forall_mem`. -/
theorem singularValues_le_of_forall_mem (A : Matrix m n 𝕜) {k : ℕ} (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ W, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖) :
    singularValues A k ≤ c := by
  sorry

/-! ### The smallest singular value -/

/-- **The smallest singular value bounds `‖A x‖` from below.** For a matrix with `n` columns and
`k + 1 = Fintype.card n`, `singularValues A k * ‖x‖ ≤ ‖A x‖`.
Port of `NLAlib.singularValues_last_mul_norm_le`. -/
theorem singularValues_last_mul_norm_le (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (x : n → 𝕜) : singularValues A k * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  sorry

/-- A lower bound `c * ‖x‖ ≤ ‖A x‖` for all `x` is a lower bound on the smallest singular value.
Port of `NLAlib.le_singularValues_last`. -/
theorem le_singularValues_last (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ}
    (h : ∀ x, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) : c ≤ singularValues A k := by
  sorry

/-- The smallest singular value in the Loewner order: `σ_min(A) ^ 2 • 1 ≤ Aᴴ * A`. -/
theorem sq_singularValues_last_smul_one_le [DecidableEq n] (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    (singularValues A k ^ 2) • (1 : Matrix n n 𝕜) ≤ Aᴴ * A := by
  sorry

/-- A lower Loewner bound on the Gram matrix is a lower bound on the smallest singular value.
This is how a subspace embedding bounds `σ_min`. -/
theorem le_sq_singularValues_last_of_smul_one_le [DecidableEq n] {A : Matrix m n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) {a : ℝ} (h : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) :
    a ≤ singularValues A k ^ 2 := by
  sorry

/-- The smallest singular value is positive exactly when the matrix has full column rank.
Port of `NLAlib.singularValues_last_pos_iff_rank_eq_card`. -/
theorem singularValues_last_pos_iff_injective (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : 0 < singularValues A k ↔ Function.Injective A.mulVec := by
  sorry

/-! ### Positive semidefinite matrices and the dilation -/

/-- The singular values of a positive semidefinite matrix are its eigenvalues. -/
theorem _root_.Matrix.PosSemidef.singularValues_eq_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : singularValues A = eigenvalue A := by
  sorry

/-- The largest eigenvalue of the Hermitian dilation is the spectral norm of the matrix.
[Tropp2015, (2.1.28)]. -/
theorem eigenvalue_zero_dilation (A : Matrix m n 𝕜) : eigenvalue (dilation A) 0 = specNorm A := by
  sorry

/-- The leading eigenvalues of the Hermitian dilation are the singular values of the matrix.
The dilation has eigenvalues `± σ_i` and zeros, so the statement holds below the larger
dimension. [HornJohnson2013, Theorem 7.3.3]. -/
theorem eigenvalue_dilation (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < max (Fintype.card m) (Fintype.card n)) :
    eigenvalue (dilation A) k = singularValues A k := by
  sorry

end NLAlib
