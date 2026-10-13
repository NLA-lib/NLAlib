/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Pseudoinverse.LeastSquares

/-!
# The QR factorization

`NLAlib.IsQR A Q R` says that `A = Q * R` with `Q` having orthonormal columns and `R` square upper
triangular: the thin QR factorization of a matrix with at least as many rows as columns. `R` has
the Gram matrix, singular values and condition number of `A`; when `A` has full column rank, `R`
is invertible, `Q * Qᴴ` is the orthogonal projector onto the range, the least-squares problem is
the triangular system `R x = Qᴴ b`, and the factorization with positive diagonal is unique.

The full factorization, with a square unitary factor and an upper trapezoidal one, is stated for
matrices indexed by `Fin`.

## Main definitions

* `NLAlib.IsQR`: the factorization predicate.

## Main results

* `NLAlib.exists_isQR`, `NLAlib.exists_isQR_of_injective`, `NLAlib.IsQR.unique`.
* `NLAlib.IsQR.conjTranspose_mul_self`, `NLAlib.IsQR.singularValues_eq`,
  `NLAlib.IsQR.conditionNumber_eq`.
* `NLAlib.IsQR.pinv_eq`, `NLAlib.IsQR.mul_conjTranspose_eq_rangeProjector`.
* `NLAlib.IsQR.isLeastSquaresSolution_backSubst`: the triangular solve.
* `NLAlib.IsQR.isLeastSquaresSolution_iff`: least squares through QR.
* `NLAlib.IsQR.isCholesky`: `Rᴴ` is the Cholesky factor of the Gram matrix.
* `NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`: the full factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  [LinearOrder n] [DecidableEq n]

/-- `IsQR A Q R`: **`A = Q * R` is a thin QR factorization**, with `Q` having orthonormal columns
and `R` upper triangular. [GolubVanLoan2013, Theorem 5.2.3]; [HornJohnson2013, Theorem 2.1.14].
Port of `NLAlib.IsQR`. -/
structure IsQR (A Q : Matrix m n 𝕜) (R : Matrix n n 𝕜) : Prop where
  /-- The matrix is the product of the factors. -/
  eq_mul : A = Q * R
  /-- The first factor has orthonormal columns. -/
  hasOrthonormalCols : HasOrthonormalCols Q
  /-- The second factor is upper triangular. -/
  isUpperTriangular : R.IsUpperTriangular

section

variable {A Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}

/-! ### What `R` knows about `A` -/

/-- `R = Qᴴ * A`. Port of `NLAlib.IsQR.conjTranspose_mul_eq`. -/
theorem IsQR.conjTranspose_mul_eq (h : IsQR A Q R) : Qᴴ * A = R := by
  sorry

/-- `R` has the Gram matrix of `A`. Port of `NLAlib.IsQR.conjTranspose_mul_self_eq`. -/
theorem IsQR.conjTranspose_mul_self (h : IsQR A Q R) : Aᴴ * A = Rᴴ * R := by
  sorry

/-- `R` has the singular values of `A`. Port of `NLAlib.singularValues_eq_of_qr`. -/
theorem IsQR.singularValues_eq (h : IsQR A Q R) (k : ℕ) :
    singularValues R k = singularValues A k := by
  sorry

/-- `R` has the rank of `A`. -/
theorem IsQR.rank_eq (h : IsQR A Q R) : R.rank = A.rank := by
  sorry

/-- `R` has the condition number of `A`.
Port of `NLAlib.moorePenroseConditionNumber_eq_of_qr`. -/
theorem IsQR.conditionNumber_eq (h : IsQR A Q R) : conditionNumber R = conditionNumber A := by
  sorry

/-! ### Full column rank -/

/-- `A` has full column rank exactly when the diagonal of `R` has no zero.
Port of `NLAlib.IsQR.isUnit_conjTranspose_mul_self_iff`. -/
theorem IsQR.injective_mulVec_iff (h : IsQR A Q R) :
    Function.Injective A.mulVec ↔ ∀ i, R i i ≠ 0 := by
  sorry

/-- For `A` of full column rank, a nonnegative diagonal of `R` is positive.
Port of `NLAlib.diag_pos_of_qr_of_rank_eq_card`. -/
theorem IsQR.apply_self_pos (h : IsQR A Q R) (hA : Function.Injective A.mulVec)
    (hd : ∀ i, 0 ≤ R i i) (i : n) : 0 < R i i := by
  sorry

/-- **The pseudoinverse through QR**: `A⁺ = R⁺ Qᴴ`, with no rank assumption. -/
theorem IsQR.pinv_eq (h : IsQR A Q R) : pinv A = pinv R * Qᴴ := by
  sorry

/-- The pseudoinverse through QR for `A` of full column rank: `A⁺ = R⁻¹ Qᴴ`.
Port of `NLAlib.moorePenroseInverse_eq_of_isQR`. -/
theorem IsQR.pinv_eq_inv_mul (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : pinv A = R⁻¹ * Qᴴ := by
  sorry

/-- For `A` of full column rank, `Q Qᴴ` is the orthogonal projector onto the range of `A`.
Port of `NLAlib.IsQR.mul_conjTranspose_eq`. -/
theorem IsQR.mul_conjTranspose_eq_rangeProjector [DecidableEq m] (h : IsQR A Q R)
    (hR : ∀ i, R i i ≠ 0) : Q * Qᴴ = rangeProjector A := by
  sorry

/-- While the diagonal of `R` has no zero, the first columns of `Q` span the same subspace as
the first columns of `A`. Port of `NLAlib.IsQR.isGradedColumnBasis`. -/
theorem IsQR.span_col_image_Iic (h : IsQR A Q R) {j : n} (hR : ∀ i, i ≤ j → R i i ≠ 0) :
    Submodule.span 𝕜 (Q.col '' Set.Iic j) = Submodule.span 𝕜 (A.col '' Set.Iic j) := by
  sorry

/-- **Least squares through QR.** For `A` of full column rank, `x` solves the least-squares
problem exactly when `R x = Qᴴ b`. [GolubVanLoan2013, §5.3.3]; [TrefethenBau1997, Lecture 11].
Result: least-squares-qr -/
theorem IsQR.isLeastSquaresSolution_iff (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) {b : m → 𝕜}
    {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ R *ᵥ x = Qᴴ *ᵥ b := by
  sorry

/-- A solution of `R x = Qᴴ b` solves the least-squares problem, with no rank assumption. -/
theorem IsQR.isLeastSquaresSolution_of_mulVec_eq (h : IsQR A Q R) {b : m → 𝕜} {x : n → 𝕜}
    (hx : R *ᵥ x = Qᴴ *ᵥ b) : IsLeastSquaresSolution A b x := by
  sorry

/-- For `R` with positive diagonal, `Rᴴ` is the Cholesky factor of the Gram matrix `Aᴴ A`. -/
theorem IsQR.isCholesky (h : IsQR A Q R) (hR : ∀ i, 0 < R i i) : IsCholesky (Aᴴ * A) Rᴴ := by
  sorry

/-! ### Changing the factorization -/

/-- A QR factorization can be rescaled by a diagonal of unit modulus.
Port of `NLAlib.IsQR.diagonal_mul`. -/
theorem IsQR.mul_diagonal (h : IsQR A Q R) {d : n → 𝕜} (hd : ∀ i, star (d i) * d i = 1) :
    IsQR A (Q * Matrix.diagonal d) (Matrix.diagonal (star d) * R) := by
  sorry

/-- A QR factorization is preserved by relabelling the rows.
Port of `NLAlib.IsQR.submatrix_rows`. -/
theorem IsQR.submatrix_rows (h : IsQR A Q R) (e : l ≃ m) :
    IsQR (A.submatrix e id) (Q.submatrix e id) R := by
  sorry

/-- A unitary factor on the left passes to `Q`. -/
theorem IsQR.mul_left [DecidableEq m] (h : IsQR A Q R) {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) : IsQR (W * A) (W * Q) R := by
  sorry

/-- **The QR factorization with positive diagonal is unique.**
[HornJohnson2013, Theorem 2.1.14]. Port of `NLAlib.IsQR.eq_of_diag_pos`, there over `ℝ`. -/
theorem IsQR.unique {Q' : Matrix m n 𝕜} {R' : Matrix n n 𝕜} (h : IsQR A Q R)
    (h' : IsQR A Q' R') (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) : Q = Q' ∧ R = R' := by
  sorry

end

/-! ### Existence -/

/-- **Every matrix with at least as many rows as columns has a QR factorization**, with
nonnegative diagonal. [HornJohnson2013, Theorem 2.1.14]; [GolubVanLoan2013, Theorem 5.2.3].
Port of `NLAlib.exists_isQR`, there over `ℝ`.
Result: qr-existence -/
theorem exists_isQR (A : Matrix m n 𝕜) (h : Fintype.card n ≤ Fintype.card m) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 ≤ R i i := by
  sorry

/-- A matrix of full column rank has a QR factorization with positive diagonal.
Port of `NLAlib.exists_isQR_of_isUnit`, there over `ℝ`. -/
theorem exists_isQR_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 < R i i := by
  sorry

/-- A matrix of full column rank has exactly one QR factorization with positive diagonal.
Port of `NLAlib.existsUnique_qr_of_rank_eq_card`, there over `ℝ`. -/
theorem existsUnique_isQR_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    ∃! QR : Matrix m n 𝕜 × Matrix n n 𝕜, IsQR A QR.1 QR.2 ∧ ∀ i, 0 < QR.2 i i := by
  sorry

/-- **The full QR factorization.** Every matrix indexed by `Fin m` and `Fin n` is a square
unitary matrix times an upper trapezoidal one.
Port of `NLAlib.exists_isFullQR`, there over `ℝ`. -/
theorem exists_hasOrthonormalCols_mul_isUpperTrapezoidal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ (Q : Matrix (Fin m) (Fin m) 𝕜) (R : Matrix (Fin m) (Fin n) 𝕜),
      HasOrthonormalCols Q ∧ IsUpperTrapezoidal R ∧ A = Q * R := by
  sorry

/-- The thin factorization from the full one: the first `n` columns of `Q` and the first `n` rows
of `R`. Port of `NLAlib.IsFullQR.isQR_castLE`. -/
theorem isQR_submatrix_castLE {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜}
    {Q : Matrix (Fin m) (Fin m) 𝕜} {R : Matrix (Fin m) (Fin n) 𝕜} (hQ : HasOrthonormalCols Q)
    (hR : IsUpperTrapezoidal R) (hA : A = Q * R) (h : n ≤ m) :
    IsQR A (Q.submatrix id (Fin.castLE h)) (R.submatrix (Fin.castLE h) id) := by
  sorry

/-! ### The QR iteration step -/

/-- **One step of the QR iteration is a unitary similarity**: if `H = Q R` then `R Q = Qᴴ H Q`.
[GolubVanLoan2013, §7.3]. Port of `NLAlib.IsQR.mul_eq_transpose_mul_mul`, there over `ℝ`. -/
theorem IsQR.mul_eq_conjTranspose_mul_mul {H Q R : Matrix n n 𝕜} (h : IsQR H Q R) :
    R * Q = Qᴴ * H * Q := by
  sorry

/-- A step of the QR iteration keeps a Hermitian matrix Hermitian.
Port of `NLAlib.isHermitian_mul_of_isQR`. -/
theorem IsQR.isHermitian_mul {H Q R : Matrix n n 𝕜} (h : IsQR H Q R) (hH : H.IsHermitian) :
    (R * Q).IsHermitian := by
  sorry

/-- **One shifted step of the QR iteration is a unitary similarity**: if `H - μ • 1 = Q R` then
`R Q + μ • 1 = Qᴴ H Q`. [GolubVanLoan2013, §7.5.2]. -/
theorem IsQR.mul_add_smul_one_eq {H Q R : Matrix n n 𝕜} {μ : 𝕜}
    (h : IsQR (H - μ • (1 : Matrix n n 𝕜)) Q R) :
    R * Q + μ • (1 : Matrix n n 𝕜) = Qᴴ * H * Q := by
  sorry

/-- **The least-squares solution by back substitution**: for a QR factorization with no zero on
the diagonal of `R`, `x = R⁻¹ Qᴴ b`, computed by back substitution, solves the least-squares
problem. [GolubVanLoan2013, Algorithm 5.3.2]. -/
theorem IsQR.isLeastSquaresSolution_backSubst {k : ℕ} {A Q : Matrix m (Fin k) 𝕜}
    {R : Matrix (Fin k) (Fin k) 𝕜} (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (backSubst R (Qᴴ *ᵥ b)) := by
  sorry

end NLAlib
