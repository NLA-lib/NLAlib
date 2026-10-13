/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.AbsoluteValue
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Majorization.TraceInequalities

/-!
# The polar decomposition and Procrustes problems

Every matrix is `A = U |A|` with `|A| = (Aᴴ A)^{1/2}`, spelled `CFC.sqrt (Aᴴ * A)`, and `U` a
partial isometry. The canonical choice is `NLAlib.polarFactor A = A |A|⁺`, which is `U Vᴴ` for a
thin SVD `A = U Σ Vᴴ` with positive singular values; it has orthonormal columns exactly when `A`
has full column rank. The positive semidefinite factor is unique, and the isometric factor is
unique exactly at full column rank.

The polar factor is the nearest matrix with orthonormal columns in every unitarily invariant
norm, and it solves the orthogonal Procrustes problem.

## Main definitions

* `NLAlib.polarFactor`: the partial isometry `A * pinv (CFC.sqrt (Aᴴ * A))`.

## Main results

* `NLAlib.polarFactor_mul_sqrt`, `NLAlib.sqrt_mul_polarFactor`: the two polar decompositions.
* `NLAlib.IsSVD.polarFactor_eq`: the polar factor through an SVD.
* `NLAlib.exists_hasOrthonormalCols_mul_sqrt_eq`, `NLAlib.eq_sqrt_of_hasOrthonormalCols_mul_eq`.
* `NLAlib.SymmetricGauge.matrixNorm_sub_le_matrixNorm_sub_of_mul_sqrt_eq`: the nearest isometry.
* `NLAlib.isLeast_frobNorm_sub_mul_sq`: the orthogonal Procrustes problem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-! ### The polar factor -/

/-- The **polar factor** of a matrix: the partial isometry `A |A|⁺`, where `|A| = (Aᴴ A)^{1/2}`.
[HornJohnson2013, Theorem 7.3.1]; [Higham2008, Theorem 8.1].
Port of `NLAlib.polarFrame`, there for real matrices of full column rank. -/
noncomputable def polarFactor (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  A * pinv (CFC.sqrt (Aᴴ * A))

/-- **The polar decomposition** `A = U |A|`.
Port of `NLAlib.exists_isometry_mul_sqrt_gram_eq`, for the canonical factor. -/
theorem polarFactor_mul_sqrt (A : Matrix m n 𝕜) :
    polarFactor A * CFC.sqrt (Aᴴ * A) = A := by
  sorry

/-- **The left polar decomposition** `A = |Aᴴ| U`, with the same factor `U`.
Port of `NLAlib.sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq`. -/
theorem sqrt_mul_polarFactor (A : Matrix m n 𝕜) :
    CFC.sqrt (A * Aᴴ) * polarFactor A = A := by
  sorry

/-- The polar factor is a partial isometry with initial space the row space of `A`. -/
theorem conjTranspose_polarFactor_mul_self (A : Matrix m n 𝕜) :
    (polarFactor A)ᴴ * polarFactor A = rangeProjector Aᴴ := by
  sorry

/-- The polar factor is a partial isometry with final space the range of `A`. -/
theorem polarFactor_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    polarFactor A * (polarFactor A)ᴴ = rangeProjector A := by
  sorry

/-- The polar factor of the conjugate transpose. -/
theorem polarFactor_conjTranspose (A : Matrix m n 𝕜) :
    polarFactor Aᴴ = (polarFactor A)ᴴ := by
  sorry

/-- **The polar factor through an SVD**: for `A = U Σ Vᴴ`, the polar factor is `U E Vᴴ` with
`E` the diagonal indicator of the positive singular values. -/
theorem IsSVD.polarFactor_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    polarFactor A = U * Matrix.diagonal (fun i => if σ i = 0 then (0 : 𝕜) else 1) * Vᴴ := by
  sorry

/-- The polar factor has orthonormal columns exactly when the matrix has full column rank.
Port of `NLAlib.hasOrthonormalCols_polarFrame`. -/
theorem hasOrthonormalCols_polarFactor_iff {A : Matrix m n 𝕜} :
    HasOrthonormalCols (polarFactor A) ↔ Function.Injective A.mulVec := by
  sorry

/-- The polar factor commutes with a unitary factor on the left. -/
theorem polarFactor_mul_left {W : Matrix l m 𝕜} (hW : HasOrthonormalCols W)
    (A : Matrix m n 𝕜) : polarFactor (W * A) = W * polarFactor A := by
  sorry

/-- The polar factor of a positive definite matrix is the identity. -/
theorem _root_.Matrix.PosDef.polarFactor_eq_one {A : Matrix n n 𝕜} (hA : A.PosDef) :
    polarFactor A = 1 := by
  sorry

/-- **The polar factor intertwines.** If `A T = T B` and `Aᴴ T = T Bᴴ`, then
`A U = U B` for the polar factor `U` of `T`.
Port of `NLAlib.mul_polarFrame_eq_polarFrame_mul_of_intertwining`, there for `T` of full column
rank. -/
theorem mul_polarFactor_eq_polarFactor_mul {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {T : Matrix m n 𝕜} (h : A * T = T * B) (h' : Aᴴ * T = T * Bᴴ) :
    A * polarFactor T = polarFactor T * B := by
  sorry

/-! ### Existence and uniqueness -/

/-- **A matrix with at least as many rows as columns is an isometry times its absolute value.**
[HornJohnson2013, Theorem 7.3.1]. Port of `NLAlib.exists_isometry_mul_sqrt_gram_eq`.
Result: polar-decomposition -/
theorem exists_hasOrthonormalCols_mul_sqrt_eq (A : Matrix m n 𝕜)
    (h : Fintype.card n ≤ Fintype.card m) :
    ∃ U : Matrix m n 𝕜, HasOrthonormalCols U ∧ U * CFC.sqrt (Aᴴ * A) = A := by
  sorry

/-- **The positive semidefinite polar factor is unique**: if `A = U P` with `U` having
orthonormal columns and `P` positive semidefinite, then `P = (Aᴴ A)^{1/2}`.
Port of `NLAlib.eq_sqrt_gram_of_isometry_mul_eq`. -/
theorem eq_sqrt_of_hasOrthonormalCols_mul_eq {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (hP : P.PosSemidef) (h : U * P = A) :
    P = CFC.sqrt (Aᴴ * A) := by
  sorry

/-- For a matrix of full column rank, the isometric polar factor is the polar factor.
Port of `NLAlib.eq_polarFrame_of_isometry_mul_sqrt_gram_eq`. -/
theorem eq_polarFactor_of_mul_sqrt_eq {A U : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    (h : U * CFC.sqrt (Aᴴ * A) = A) : U = polarFactor A := by
  sorry

/-- **The isometric polar factor is unique exactly when the matrix has full column rank.**
Port of `NLAlib.polar_isometry_unique_iff_rank_eq_card`. -/
theorem forall_eq_of_mul_sqrt_eq_iff {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (h : U * CFC.sqrt (Aᴴ * A) = A) :
    (∀ V : Matrix m n 𝕜, HasOrthonormalCols V → V * CFC.sqrt (Aᴴ * A) = A → V = U) ↔
      Function.Injective A.mulVec := by
  sorry

/-! ### The nearest isometry -/

/-- **The polar factor is the nearest matrix with orthonormal columns** in every unitarily
invariant norm (Fan and Hoffman). [Higham2008, Theorem 8.4]; [HornJohnson2013, §7.4.9 context].
Port of `NLAlib.invariantNorm_sub_polar_le_sub_isometry`, there over `ℝ`.
Result: nearest-unitary -/
theorem SymmetricGauge.matrixNorm_sub_le_matrixNorm_sub_of_mul_sqrt_eq (Φ : SymmetricGauge)
    {A U V : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᴴ * A) = A)
    (hV : HasOrthonormalCols V) : Φ.matrixNorm (A - U) ≤ Φ.matrixNorm (A - V) := by
  sorry

/-- No matrix with orthonormal columns is farther from `A` than minus the polar factor.
[Higham2008, Theorem 8.4 context]. -/
theorem SymmetricGauge.matrixNorm_sub_le_matrixNorm_add_of_mul_sqrt_eq (Φ : SymmetricGauge)
    {A U V : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᴴ * A) = A)
    (hV : HasOrthonormalCols V) : Φ.matrixNorm (A - V) ≤ Φ.matrixNorm (A + U) := by
  sorry

/-- The trace of a square matrix equals its nuclear norm exactly when it is positive
semidefinite. Port of `NLAlib.trace_eq_nuclearNorm_iff_posSemidef`, there over `ℝ`. -/
theorem trace_eq_nuclearNorm_iff_posSemidef {M : Matrix n n 𝕜} :
    M.trace = (nuclearNorm M : 𝕜) ↔ M.PosSemidef := by
  sorry

/-! ### Procrustes problems -/

/-- The Procrustes objective at a polar factor of `A Bᴴ`.
Port of `NLAlib.frobSq_sub_mul_eq_of_cross_polar`. -/
theorem frobNorm_sub_mul_sq_of_mul_sqrt_eq {A B : Matrix m n 𝕜} {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U)
    (h : U * CFC.sqrt ((A * Bᴴ)ᴴ * (A * Bᴴ)) = A * Bᴴ) :
    frobNorm (A - U * B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ) := by
  sorry

/-- **The orthogonal Procrustes problem.** The least value of `‖A - U B‖_F²` over unitary `U` is
`‖A‖_F² + ‖B‖_F² - 2 ‖A Bᴴ‖_*`, attained at a polar factor of `A Bᴴ`.
[GolubVanLoan2013, §6.4.1]; [HornJohnson2013, §7.4.5].
Port of `NLAlib.isLeast_frobSq_sub_orthogonal_mul`, there over `ℝ`.
Result: procrustes -/
theorem isLeast_frobNorm_sub_mul_sq (A B : Matrix m n 𝕜) :
    IsLeast ((fun U : Matrix m m 𝕜 => frobNorm (A - U * B) ^ 2) '' {U | HasOrthonormalCols U})
      (frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ)) := by
  sorry

/-- **The two-sided Procrustes problem.** The least value of `‖A - U B W‖_F²` over unitary `U`,
`W` is `∑ (σ_i(A) - σ_i(B))²`. [HornJohnson2013, §7.4.1 context].
Port of `NLAlib.isLeast_frobSq_sub_orthogonal_mul_mul`, there over `ℝ`. -/
theorem isLeast_frobNorm_sub_mul_mul_sq (A B : Matrix m n 𝕜) :
    IsLeast
      ((fun P : Matrix m m 𝕜 × Matrix n n 𝕜 => frobNorm (A - P.1 * B * P.2) ^ 2) ''
        {P | HasOrthonormalCols P.1 ∧ HasOrthonormalCols P.2})
      (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) := by
  sorry

/-- **The nearest scaled unitary matrix.** The least value of `‖A - c U‖_F²` over real `c` and
unitary `U` is `‖A‖_F² - ‖A‖_*² / n`, attained at `c = ‖A‖_* / n` and a polar factor.
Port of `NLAlib.isLeast_frobSq_sub_scaled_orthogonal`, there over `ℝ`. -/
theorem isLeast_frobNorm_sub_smul_sq [Nonempty n] (A : Matrix n n 𝕜) :
    IsLeast
      ((fun P : ℝ × Matrix n n 𝕜 => frobNorm (A - P.1 • P.2) ^ 2) ''
        {P | HasOrthonormalCols P.2})
      (frobNorm A ^ 2 - nuclearNorm A ^ 2 / Fintype.card n) := by
  sorry

end NLAlib
