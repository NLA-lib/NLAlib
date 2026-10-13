/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
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
matrices indexed by `Fin`. Existence is read off Mathlib's
`InnerProductSpace.gramSchmidtOrthonormalBasis`, applied to the columns padded with zero vectors.

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

/-- A triangular factor with no zero on its diagonal is invertible. -/
private theorem IsQR.isUnit (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : IsUnit R :=
  (Matrix.isUnit_iff_isUnit_det R).mpr
    (h.isUpperTriangular.isUnit_det_iff.mpr fun i => (hR i).isUnit)

/-- A column of `A` is the combination of the columns of `Q` with the entries of `R`. -/
private theorem IsQR.col_eq_sum (h : IsQR A Q R) (k : n) : A.col k = ∑ i, R i k • Q.col i := by
  ext x
  rw [h.eq_mul]
  simp only [Matrix.col_apply, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm]

/-- `R = Qᴴ * A`. Port of `NLAlib.IsQR.conjTranspose_mul_eq`. -/
theorem IsQR.conjTranspose_mul_eq (h : IsQR A Q R) : Qᴴ * A = R := by
  rw [h.eq_mul, h.hasOrthonormalCols.conjTranspose_mul_cancel_left]

/-- `R` has the Gram matrix of `A`. Port of `NLAlib.IsQR.conjTranspose_mul_self_eq`. -/
theorem IsQR.conjTranspose_mul_self (h : IsQR A Q R) : Aᴴ * A = Rᴴ * R := by
  rw [h.eq_mul, h.hasOrthonormalCols.conjTranspose_mul_mul]

/-- `R` has the singular values of `A`. Port of `NLAlib.singularValues_eq_of_qr`. -/
theorem IsQR.singularValues_eq (h : IsQR A Q R) (k : ℕ) :
    singularValues R k = singularValues A k := by
  rw [singularValues_eq_of_conjTranspose_mul_self_eq h.conjTranspose_mul_self]

/-- `R` has the rank of `A`. -/
theorem IsQR.rank_eq (h : IsQR A Q R) : R.rank = A.rank := by
  rw [h.eq_mul, h.hasOrthonormalCols.rank_mul]

/-- `R` has the condition number of `A`.
Port of `NLAlib.moorePenroseConditionNumber_eq_of_qr`. -/
theorem IsQR.conditionNumber_eq (h : IsQR A Q R) : conditionNumber R = conditionNumber A := by
  classical
  rw [h.eq_mul, h.hasOrthonormalCols.conditionNumber_mul_left]

/-! ### Full column rank -/

/-- `A` has full column rank exactly when the diagonal of `R` has no zero.
Port of `NLAlib.IsQR.isUnit_conjTranspose_mul_self_iff`. -/
theorem IsQR.injective_mulVec_iff (h : IsQR A Q R) :
    Function.Injective A.mulVec ↔ ∀ i, R i i ≠ 0 := by
  rw [mulVec_injective_iff_rank_eq, ← h.rank_eq, ← mulVec_injective_iff_rank_eq,
    Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    h.isUpperTriangular.isUnit_det_iff]
  simp only [isUnit_iff_ne_zero]

/-- For `A` of full column rank, a nonnegative diagonal of `R` is positive.
Port of `NLAlib.diag_pos_of_qr_of_rank_eq_card`. -/
theorem IsQR.apply_self_pos (h : IsQR A Q R) (hA : Function.Injective A.mulVec)
    (hd : ∀ i, 0 ≤ R i i) (i : n) : 0 < R i i := by
  exact (hd i).lt_of_ne' (h.injective_mulVec_iff.mp hA i)

/-- **The pseudoinverse through QR**: `A⁺ = R⁺ Qᴴ`, with no rank assumption. -/
theorem IsQR.pinv_eq (h : IsQR A Q R) : pinv A = pinv R * Qᴴ := by
  classical
  rw [h.eq_mul, h.hasOrthonormalCols.pinv_mul_left]

/-- The pseudoinverse through QR for `A` of full column rank: `A⁺ = R⁻¹ Qᴴ`.
Port of `NLAlib.moorePenroseInverse_eq_of_isQR`. -/
theorem IsQR.pinv_eq_inv_mul (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : pinv A = R⁻¹ * Qᴴ := by
  rw [h.pinv_eq, pinv_of_isUnit (h.isUnit hR)]

/-- For `A` of full column rank, `Q Qᴴ` is the orthogonal projector onto the range of `A`.
Port of `NLAlib.IsQR.mul_conjTranspose_eq`. -/
theorem IsQR.mul_conjTranspose_eq_rangeProjector (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) :
    Q * Qᴴ = rangeProjector A := by
  rw [h.eq_mul, rangeProjector_mul_of_isUnit Q (h.isUnit hR),
    h.hasOrthonormalCols.rangeProjector_eq]

/-- While the diagonal of `R` has no zero, the first columns of `Q` span the same subspace as
the first columns of `A`. Port of `NLAlib.IsQR.isGradedColumnBasis`. -/
theorem IsQR.span_col_image_Iic (h : IsQR A Q R) {j : n} (hR : ∀ i, i ≤ j → R i i ≠ 0) :
    Submodule.span 𝕜 (Q.col '' Set.Iic j) = Submodule.span 𝕜 (A.col '' Set.Iic j) := by
  have hQ : ∀ k, k ≤ j → Q.col k ∈ Submodule.span 𝕜 (A.col '' Set.Iic k) := by
    intro k
    induction k using WellFoundedLT.induction with
    | ind k ih =>
      intro hk
      have hcol := h.col_eq_sum k
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hcol
      have hq : Q.col k = (R k k)⁻¹ • (A.col k - ∑ i ∈ Finset.univ.erase k, R i k • Q.col i) := by
        rw [hcol, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (hR k hk), one_smul]
      rw [hq]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span ⟨k, le_rfl, rfl⟩) (Submodule.sum_mem _ fun i hi => ?_))
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hik | hik
      · exact Submodule.smul_mem _ _ (Submodule.span_mono
          (Set.image_mono (Set.Iic_subset_Iic.mpr hik.le)) (ih i hik (hik.le.trans hk)))
      · rw [h.isUpperTriangular hik, zero_smul]
        exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨k, hk, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr hk)) (hQ k hk)
  · rintro _ ⟨k, hk, rfl⟩
    rw [h.col_eq_sum k]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases le_or_gt i k with hik | hik
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hik.trans hk, rfl⟩)
    · rw [h.isUpperTriangular hik, zero_smul]
      exact Submodule.zero_mem _

/-- A solution of `R x = Qᴴ b` solves the least-squares problem, with no rank assumption. -/
theorem IsQR.isLeastSquaresSolution_of_mulVec_eq (h : IsQR A Q R) {b : m → 𝕜} {x : n → 𝕜}
    (hx : R *ᵥ x = Qᴴ *ᵥ b) : IsLeastSquaresSolution A b x := by
  rw [isLeastSquaresSolution_iff_normal_equations, h.eq_mul, Matrix.conjTranspose_mul]
  simp only [← Matrix.mulVec_mulVec]
  rw [h.hasOrthonormalCols.conjTranspose_mulVec_mulVec, hx]

/-- **Least squares through QR.** For `A` of full column rank, `x` solves the least-squares
problem exactly when `R x = Qᴴ b`. [GolubVanLoan2013, §5.3.3]; [TrefethenBau1997, Lecture 11].
Result: least-squares-qr -/
theorem IsQR.isLeastSquaresSolution_iff (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) {b : m → 𝕜}
    {x : n → 𝕜} : IsLeastSquaresSolution A b x ↔ R *ᵥ x = Qᴴ *ᵥ b := by
  refine ⟨fun hx => ?_, h.isLeastSquaresSolution_of_mulVec_eq⟩
  rw [isLeastSquaresSolution_iff_normal_equations, h.eq_mul, Matrix.conjTranspose_mul] at hx
  simp only [← Matrix.mulVec_mulVec] at hx
  rw [h.hasOrthonormalCols.conjTranspose_mulVec_mulVec] at hx
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((h.isUnit hR).star) hx

/-- For `R` with positive diagonal, `Rᴴ` is the Cholesky factor of the Gram matrix `Aᴴ A`. -/
theorem IsQR.isCholesky (h : IsQR A Q R) (hR : ∀ i, 0 < R i i) : IsCholesky (Aᴴ * A) Rᴴ := by
  refine ⟨h.isUpperTriangular.conjTranspose, fun i => ?_, ?_⟩
  · rw [Matrix.conjTranspose_apply]
    exact star_pos_iff.mpr (hR i)
  · rw [Matrix.conjTranspose_conjTranspose, h.conjTranspose_mul_self]

/-! ### Changing the factorization -/

/-- A QR factorization can be rescaled by a diagonal of unit modulus.
Port of `NLAlib.IsQR.diagonal_mul`. -/
theorem IsQR.mul_diagonal (h : IsQR A Q R) {d : n → 𝕜} (hd : ∀ i, star (d i) * d i = 1) :
    IsQR A (Q * Matrix.diagonal d) (Matrix.diagonal (star d) * R) := by
  have hdd : Matrix.diagonal d * Matrix.diagonal (star d) = (1 : Matrix n n 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext fun i => (mul_comm _ _).trans (hd i))
  refine ⟨?_, ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), hdd, Matrix.one_mul]
    exact h.eq_mul
  · rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
      h.hasOrthonormalCols.conjTranspose_mul_self, Matrix.one_mul, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hd)
  · rw [Matrix.diagonal_mul, h.isUpperTriangular hij, mul_zero]

/-- A QR factorization is preserved by relabelling the rows.
Port of `NLAlib.IsQR.submatrix_rows`. -/
theorem IsQR.submatrix_rows (h : IsQR A Q R) (e : l ≃ m) :
    IsQR (A.submatrix e id) (Q.submatrix e id) R := by
  refine ⟨?_, h.hasOrthonormalCols.submatrix e Function.injective_id, h.isUpperTriangular⟩
  rw [h.eq_mul]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]

/-- A unitary factor on the left passes to `Q`. -/
theorem IsQR.mul_left [DecidableEq m] (h : IsQR A Q R) {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) : IsQR (W * A) (W * Q) R := by
  exact ⟨by rw [h.eq_mul, Matrix.mul_assoc], hW.mul h.hasOrthonormalCols, h.isUpperTriangular⟩

/-- **The QR factorization with positive diagonal is unique.**
[HornJohnson2013, Theorem 2.1.14]. Port of `NLAlib.IsQR.eq_of_diag_pos`, there over `ℝ`. -/
theorem IsQR.unique {Q' : Matrix m n 𝕜} {R' : Matrix n n 𝕜} (h : IsQR A Q R)
    (h' : IsQR A Q' R') (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) : Q = Q' ∧ R = R' := by
  have hRR : R = R' :=
    Matrix.conjTranspose_injective ((h.isCholesky hR).unique (h'.isCholesky hR'))
  subst hRR
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp (h.isUnit fun i => (hR i).ne')
  refine ⟨?_, rfl⟩
  rw [← Matrix.mul_nonsing_inv_cancel_right R Q hdet, ← h.eq_mul, h'.eq_mul,
    Matrix.mul_nonsing_inv_cancel_right R Q' hdet]

end

/-! ### The full factorization -/

/-- **The full QR factorization.** Every matrix indexed by `Fin m` and `Fin n` is a square
unitary matrix times an upper trapezoidal one.
Port of `NLAlib.exists_isFullQR`, there over `ℝ`. -/
theorem exists_hasOrthonormalCols_mul_isUpperTrapezoidal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ (Q : Matrix (Fin m) (Fin m) 𝕜) (R : Matrix (Fin m) (Fin n) 𝕜),
      HasOrthonormalCols Q ∧ IsUpperTrapezoidal R ∧ A = Q * R := by
  let f : Fin m → EuclideanSpace 𝕜 (Fin m) := fun k =>
    if hk : (k : ℕ) < n then WithLp.toLp 2 (A.col ⟨k, hk⟩) else 0
  have hcard : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin m)) = Fintype.card (Fin m) :=
    finrank_euclideanSpace
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hcard f
  let Q : Matrix (Fin m) (Fin m) 𝕜 := Matrix.of fun i k => b k i
  have hQ : HasOrthonormalCols Q := by
    rw [hasOrthonormalCols_iff_orthonormal]
    exact b.orthonormal
  refine ⟨Q, Qᴴ * A, hQ, fun i j hji => ?_, ?_⟩
  · have hjm : (j : ℕ) < m := hji.trans i.2
    have h0 := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hcard f
      (i := ⟨j, hjm⟩) (j := i) (Fin.lt_def.mpr hji)
    have hf : f ⟨j, hjm⟩ = WithLp.toLp 2 (A.col j) := dif_pos j.2
    rw [hf, EuclideanSpace.inner_eq_star_dotProduct] at h0
    rw [← h0, Matrix.mul_apply, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, mul_comm]
    rfl
  · rw [← Matrix.mul_assoc, hQ.mul_conjTranspose_self, Matrix.one_mul]

/-- The thin factorization from the full one: the first `n` columns of `Q` and the first `n` rows
of `R`. Port of `NLAlib.IsFullQR.isQR_castLE`. -/
theorem isQR_submatrix_castLE {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜}
    {Q : Matrix (Fin m) (Fin m) 𝕜} {R : Matrix (Fin m) (Fin n) 𝕜} (hQ : HasOrthonormalCols Q)
    (hR : IsUpperTrapezoidal R) (hA : A = Q * R) (h : n ≤ m) :
    IsQR A (Q.submatrix id (Fin.castLE h)) (R.submatrix (Fin.castLE h) id) := by
  refine ⟨?_, hQ.submatrix (Equiv.refl _) (Fin.castLE_injective h),
    hR.isUpperTriangular_submatrix_castLE h⟩
  rw [hA]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _
    (fun k hk => ?_) fun k => rfl).symm
  rw [hR.apply_eq_zero_of_le (i := k) ?_ j, mul_zero]
  by_contra hkn
  exact hk ⟨⟨k, not_le.mp hkn⟩, Fin.ext rfl⟩

/-! ### Existence -/

/-- A QR factorization can be rescaled to have a nonnegative diagonal. -/
private theorem IsQR.exists_nonneg {A Q : Matrix m n 𝕜} {R : Matrix n n 𝕜} (h : IsQR A Q R) :
    ∃ Q' R', IsQR A Q' R' ∧ ∀ i, 0 ≤ R' i i := by
  let d : n → 𝕜 := fun i => if R i i = 0 then 1 else R i i / (‖R i i‖ : 𝕜)
  have hd : ∀ i, star (d i) * d i = 1 := by
    intro i
    by_cases h0 : R i i = 0
    · simp only [d, if_pos h0, star_one, mul_one]
    · have hn : (‖R i i‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      simp only [d, if_neg h0, star_div₀, RCLike.star_def, RCLike.conj_ofReal]
      rw [div_mul_div_comm, RCLike.conj_mul, ← sq, div_self (pow_ne_zero 2 hn)]
  refine ⟨_, _, h.mul_diagonal hd, fun i => ?_⟩
  rw [Matrix.diagonal_mul, Pi.star_apply]
  by_cases h0 : R i i = 0
  · rw [h0, mul_zero]
  · have hn : (‖R i i‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
    have hval : star (d i) * R i i = (‖R i i‖ : 𝕜) := by
      simp only [d, if_neg h0, star_div₀, RCLike.star_def, RCLike.conj_ofReal]
      rw [div_mul_eq_mul_div, RCLike.conj_mul, sq, mul_div_assoc, div_self hn, mul_one]
    rw [hval]
    exact RCLike.ofReal_nonneg.mpr (norm_nonneg _)

/-- A thin QR factorization of a matrix indexed by `Fin`, from the full one. -/
private theorem exists_isQR_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (h : n ≤ m) :
    ∃ (Q : Matrix (Fin m) (Fin n) 𝕜) (R : Matrix (Fin n) (Fin n) 𝕜), IsQR A Q R := by
  obtain ⟨Q, R, hQ, hR, hA⟩ := exists_hasOrthonormalCols_mul_isUpperTrapezoidal A
  exact ⟨_, _, isQR_submatrix_castLE hQ hR hA h⟩

/-- **Every matrix with at least as many rows as columns has a QR factorization**, with
nonnegative diagonal. [HornJohnson2013, Theorem 2.1.14]; [GolubVanLoan2013, Theorem 5.2.3].
Port of `NLAlib.exists_isQR`, there over `ℝ`.
Result: qr-existence -/
theorem exists_isQR (A : Matrix m n 𝕜) (h : Fintype.card n ≤ Fintype.card m) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 ≤ R i i := by
  set em := Fintype.equivFin m
  set en := Fintype.orderIsoFinOfCardEq n rfl
  obtain ⟨Q, R, hQR⟩ := exists_isQR_fin (A.submatrix em.symm en) h
  have hA : IsQR A (Q.submatrix em en.symm) (R.submatrix en.symm en.symm) := by
    refine ⟨?_, hQR.hasOrthonormalCols.submatrix em en.symm.injective,
      hQR.isUpperTriangular.submatrix_of_strictMono en.symm.strictMono⟩
    refine Eq.trans ?_ (Matrix.submatrix_mul_equiv Q R em en.symm.toEquiv en.symm).symm
    rw [← hQR.eq_mul]
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, OrderIso.apply_symm_apply]
  exact hA.exists_nonneg

/-- A matrix of full column rank has a QR factorization with positive diagonal.
Port of `NLAlib.exists_isQR_of_isUnit`, there over `ℝ`. -/
theorem exists_isQR_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 < R i i := by
  have hcard : Fintype.card n ≤ Fintype.card m :=
    (mulVec_injective_iff_rank_eq.mp hA).symm.trans_le A.rank_le_card_height
  obtain ⟨Q, R, h, hR⟩ := exists_isQR A hcard
  exact ⟨Q, R, h, h.apply_self_pos hA hR⟩

/-- A matrix of full column rank has exactly one QR factorization with positive diagonal.
Port of `NLAlib.existsUnique_qr_of_rank_eq_card`, there over `ℝ`. -/
theorem existsUnique_isQR_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    ∃! QR : Matrix m n 𝕜 × Matrix n n 𝕜, IsQR A QR.1 QR.2 ∧ ∀ i, 0 < QR.2 i i := by
  obtain ⟨Q, R, h, hR⟩ := exists_isQR_of_injective hA
  refine ⟨(Q, R), ⟨h, hR⟩, fun QR hQR => ?_⟩
  obtain ⟨hQ, hR'⟩ := hQR.1.unique h hQR.2 hR
  exact Prod.ext hQ hR'

/-! ### The QR iteration step -/

/-- **One step of the QR iteration is a unitary similarity**: if `H = Q R` then `R Q = Qᴴ H Q`.
[GolubVanLoan2013, §7.3]. Port of `NLAlib.IsQR.mul_eq_transpose_mul_mul`, there over `ℝ`. -/
theorem IsQR.mul_eq_conjTranspose_mul_mul {H Q R : Matrix n n 𝕜} (h : IsQR H Q R) :
    R * Q = Qᴴ * H * Q := by
  rw [h.conjTranspose_mul_eq]

/-- A step of the QR iteration keeps a Hermitian matrix Hermitian.
Port of `NLAlib.isHermitian_mul_of_isQR`. -/
theorem IsQR.isHermitian_mul {H Q R : Matrix n n 𝕜} (h : IsQR H Q R) (hH : H.IsHermitian) :
    (R * Q).IsHermitian := by
  rw [h.mul_eq_conjTranspose_mul_mul]
  exact Matrix.isHermitian_conjTranspose_mul_mul Q hH

/-- **One shifted step of the QR iteration is a unitary similarity**: if `H - μ • 1 = Q R` then
`R Q + μ • 1 = Qᴴ H Q`. [GolubVanLoan2013, §7.5.2]. -/
theorem IsQR.mul_add_smul_one_eq {H Q R : Matrix n n 𝕜} {μ : 𝕜}
    (h : IsQR (H - μ • (1 : Matrix n n 𝕜)) Q R) :
    R * Q + μ • (1 : Matrix n n 𝕜) = Qᴴ * H * Q := by
  rw [← h.conjTranspose_mul_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, h.hasOrthonormalCols.conjTranspose_mul_self, sub_add_cancel]

/-- **The least-squares solution by back substitution**: for a QR factorization with no zero on
the diagonal of `R`, `x = R⁻¹ Qᴴ b`, computed by back substitution, solves the least-squares
problem. [GolubVanLoan2013, Algorithm 5.3.2]. -/
theorem IsQR.isLeastSquaresSolution_backSubst {k : ℕ} {A Q : Matrix m (Fin k) 𝕜}
    {R : Matrix (Fin k) (Fin k) 𝕜} (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (backSubst R (Qᴴ *ᵥ b)) := by
  exact h.isLeastSquaresSolution_of_mulVec_eq (mulVec_backSubst h.isUpperTriangular hR _)

end NLAlib
