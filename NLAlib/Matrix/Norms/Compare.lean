/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral

/-!
# Comparing the spectral and Frobenius norms

The inequalities between `specNorm` and `frobNorm`, the mixed bounds for products, and the
behaviour of both norms under factors with orthonormal columns.

Bounds that are linear in the norms are stated once, linearly; their squares follow by `gcongr`.

## Main results

* `NLAlib.specNorm_le_frobNorm`: `specNorm A ≤ frobNorm A`.
* `NLAlib.frobNorm_mul_le_specNorm_mul_frobNorm`,
  `NLAlib.frobNorm_mul_le_frobNorm_mul_specNorm`: the mixed product bounds.
* `NLAlib.HasOrthonormalCols.specNorm_mul_left`, `NLAlib.HasOrthonormalCols.frobNorm_mul_left`:
  both norms are invariant under left multiplication by a matrix with orthonormal columns, and
  under right multiplication by the conjugate transpose of one.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Spectral against Frobenius -/

omit [Fintype l] [Fintype n] in
private theorem col_mul (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) (j : n) :
    (A * B).col j = A *ᵥ B.col j :=
  rfl

/-- The spectral norm is at most the Frobenius norm.
[GolubVanLoan2013, (2.3.7)]. Port of `NLAlib.specNorm_le_frobNorm`. -/
theorem specNorm_le_frobNorm (A : Matrix m n 𝕜) : specNorm A ≤ frobNorm A := by
  exact (specNorm_le_iff (frobNorm_nonneg A)).2 (norm_toLp_mulVec_le_frobNorm_mul A)

/-- The Frobenius norm is at most `√(number of columns)` times the spectral norm, in squared
form. [GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_sq_le_card_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ Fintype.card n * specNorm A ^ 2 := by
  rw [frobNorm_sq_eq_sum_col, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
  gcongr
  exact norm_toLp_col_le_specNorm A j

/-- The Frobenius norm is at most `√(number of columns)` times the spectral norm.
[GolubVanLoan2013, (2.3.7)]. The squared form is `NLAlib.frobNorm_sq_le_card_mul_specNorm_sq`. -/
theorem frobNorm_le_sqrt_card_mul_specNorm (A : Matrix m n 𝕜) :
    frobNorm A ≤ √(Fintype.card n : ℝ) * specNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg A) (by positivity)).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact frobNorm_sq_le_card_mul_specNorm_sq A

/-- The squared Frobenius norm is at most the number of rows times the squared spectral norm:
the row-count twin of `NLAlib.frobNorm_sq_le_card_mul_specNorm_sq`, which counts columns.
[GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_sq_le_card_rows_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ Fintype.card m * specNorm A ^ 2 := by
  have h := frobNorm_sq_le_card_mul_specNorm_sq Aᴴ
  rwa [frobNorm_conjTranspose, specNorm_conjTranspose] at h

/-- The mixed product bound with the spectral norm on the left factor.
[HornJohnson2013, §5.6, Problem 20]. Port of `NLAlib.frobNorm_mul_le_specNorm_mul_frobNorm`. -/
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B := by
  refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
  rw [mul_pow, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [col_mul, ← mul_pow]
  gcongr
  exact norm_toLp_mulVec_le A (B.col j)

/-- The mixed product bound with the spectral norm on the right factor.
Port of `NLAlib.frobNorm_mul_le_frobNorm_mul_specNorm`. -/
theorem frobNorm_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B := by
  have h := frobNorm_mul_le_specNorm_mul_frobNorm Bᴴ Aᴴ
  rwa [← Matrix.conjTranspose_mul, frobNorm_conjTranspose, specNorm_conjTranspose,
    frobNorm_conjTranspose, mul_comm] at h

/-- The Frobenius norm is submultiplicative. Port of `NLAlib.frobNorm_mul_le`. -/
theorem frobNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  refine (frobNorm_mul_le_specNorm_mul_frobNorm A B).trans ?_
  gcongr
  exact specNorm_le_frobNorm A

/-- The spectral norm is `1`-Lipschitz for the Frobenius norm.
Port of `NLAlib.abs_specNorm_sub_specNorm_le_frobNorm`. -/
theorem abs_specNorm_sub_specNorm_le_frobNorm (A B : Matrix m n 𝕜) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) := by
  exact (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm (A - B))

/-- The Frobenius inner product is bounded by a Frobenius norm times a spectral-Frobenius
product: `|⟨A * B, C⟩| ≤ specNorm A * frobNorm B * frobNorm C`. -/
theorem abs_frobInner_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) (C : Matrix l n 𝕜) :
    |frobInner (A * B) C| ≤ specNorm A * frobNorm B * frobNorm C := by
  refine (abs_frobInner_le (A * B) C).trans ?_
  gcongr
  exact frobNorm_mul_le_specNorm_mul_frobNorm A B

/-- The Frobenius inner product bound with the spectral norm on the right factor of the product:
`|⟨A * B, C⟩| ≤ frobNorm A * specNorm B * frobNorm C`. -/
theorem abs_frobInner_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜)
    (C : Matrix l n 𝕜) : |frobInner (A * B) C| ≤ frobNorm A * specNorm B * frobNorm C := by
  refine (abs_frobInner_le (A * B) C).trans ?_
  gcongr
  exact frobNorm_mul_le_frobNorm_mul_specNorm A B

/-! ### Factors with orthonormal columns -/

namespace HasOrthonormalCols

variable [DecidableEq n]

/-- Left multiplication by a matrix with orthonormal columns preserves the spectral norm.
Port of `NLAlib.specNorm_mul_left_of_hasOrthonormalCols`. -/
theorem specNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    specNorm (Q * A) = specNorm A := by
  have h (x : p → 𝕜) : ‖WithLp.toLp 2 ((Q * A) *ᵥ x)‖ = ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
    rw [← Matrix.mulVec_mulVec, hQ.norm_toLp_mulVec]
  refine le_antisymm ((specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_)
    ((specNorm_le_iff (specNorm_nonneg (Q * A))).2 fun x => ?_)
  · rw [h]
    exact norm_toLp_mulVec_le A x
  · rw [← h]
    exact norm_toLp_mulVec_le (Q * A) x

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the spectral norm.
Port of `NLAlib.specNorm_mul_conjTranspose_right_of_hasOrthonormalCols`. -/
theorem specNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : specNorm (A * Qᴴ) = specNorm A := by
  rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hQ.specNorm_mul_left, specNorm_conjTranspose]

/-- Left multiplication by a matrix with orthonormal columns preserves the Frobenius norm.
Port of `NLAlib.frobSq_mul_left_of_orthonormal`. -/
theorem frobNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    frobNorm (Q * A) = frobNorm A := by
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_re_trace, frobNorm_sq_eq_re_trace, hQ.conjTranspose_mul_mul]

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the Frobenius norm. Port of `NLAlib.frobSq_mul_right_of_orthonormal`. -/
theorem frobNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : frobNorm (A * Qᴴ) = frobNorm A := by
  rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hQ.frobNorm_mul_left, frobNorm_conjTranspose]

/-- Left multiplication of both arguments by a matrix with orthonormal columns preserves the
Frobenius inner product. Port of `NLAlib.frobInner_mul_left_of_orthonormal`. -/
theorem frobInner_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A B : Matrix n p 𝕜) :
    frobInner (Q * A) (Q * B) = frobInner A B := by
  rw [frobInner, frobInner, hQ.conjTranspose_mul_mul]

/-- Right multiplication of both arguments by the conjugate transpose of a matrix with
orthonormal columns preserves the Frobenius inner product. -/
theorem frobInner_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A B : Matrix p n 𝕜) : frobInner (A * Qᴴ) (B * Qᴴ) = frobInner A B := by
  rw [← frobInner_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.frobInner_mul_left, frobInner_conjTranspose]

/-- Left multiplication by `Qᴴ` does not increase the spectral norm. -/
theorem specNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : specNorm (Qᴴ * A) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  exact (hQ.norm_toLp_conjTranspose_mulVec_le (A *ᵥ x)).trans (norm_toLp_mulVec_le A x)

/-- Left multiplication by `Qᴴ` does not increase the Frobenius norm.
Port of `NLAlib.frobSq_conjTranspose_mul_le`. -/
theorem frobNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : frobNorm (Qᴴ * A) ≤ frobNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [col_mul]
  gcongr
  exact hQ.norm_toLp_conjTranspose_mulVec_le (A.col j)

/-- Right multiplication by a matrix with orthonormal columns does not increase the spectral
norm. -/
theorem specNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    specNorm (A * Q) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← hQ.norm_toLp_mulVec x]
  exact norm_toLp_mulVec_le A (Q *ᵥ x)

/-- A compression does not increase the spectral norm: `‖Qᴴ A Q‖₂ ≤ ‖A‖₂` for `Q` with
orthonormal columns. -/
theorem specNorm_conjTranspose_mul_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m m 𝕜) : specNorm (Qᴴ * A * Q) ≤ specNorm A :=
  (hQ.specNorm_mul_right_le (Qᴴ * A)).trans (hQ.specNorm_conjTranspose_mul_le A)

/-- Right multiplication by a matrix with orthonormal columns does not increase the Frobenius
norm. -/
theorem frobNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    frobNorm (A * Q) ≤ frobNorm A := by
  have h := hQ.frobNorm_conjTranspose_mul_le Aᴴ
  rwa [← Matrix.conjTranspose_mul, frobNorm_conjTranspose, frobNorm_conjTranspose] at h

/-- Right multiplication by a matrix with orthonormal columns and as many rows as columns
preserves the spectral norm. The row and column index types may differ. -/
theorem specNorm_mul_right_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) (A : Matrix p m 𝕜) :
    specNorm (A * Q) = specNorm A := by
  classical
  have h' := (hQ.conjTranspose_of_card_eq h).specNorm_mul_conjTranspose_right A
  rwa [Matrix.conjTranspose_conjTranspose] at h'

/-- Right multiplication by a matrix with orthonormal columns and as many rows as columns
preserves the Frobenius norm. The row and column index types may differ. -/
theorem frobNorm_mul_right_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) (A : Matrix p m 𝕜) :
    frobNorm (A * Q) = frobNorm A := by
  classical
  have h' := (hQ.conjTranspose_of_card_eq h).frobNorm_mul_conjTranspose_right A
  rwa [Matrix.conjTranspose_conjTranspose] at h'

/-- Right multiplication by a unitary matrix preserves the spectral norm. -/
theorem specNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    specNorm (A * Q) = specNorm A :=
  hQ.specNorm_mul_right_of_card_eq rfl A

/-- Right multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    frobNorm (A * Q) = frobNorm A :=
  hQ.frobNorm_mul_right_of_card_eq rfl A

/-- A matrix with orthonormal columns has spectral norm at most one.
Port of `NLAlib.specNorm_le_one_of_orthonormal`. -/
theorem specNorm_le_one {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : specNorm Q ≤ 1 := by
  rw [← Matrix.mul_one Q, hQ.specNorm_mul_left]
  exact specNorm_one_le

/-- A matrix with orthonormal columns, and at least one column, has spectral norm one. -/
theorem specNorm_eq_one [Nonempty n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    specNorm Q = 1 := by
  rw [← Matrix.mul_one Q, hQ.specNorm_mul_left, specNorm_one]

/-- The squared Frobenius norm of a matrix with orthonormal columns is its number of columns.
Port of `NLAlib.frobSq_frame_eq_card`. -/
theorem frobNorm_sq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    frobNorm Q ^ 2 = Fintype.card n := by
  rw [← Matrix.mul_one Q, hQ.frobNorm_mul_left, frobNorm_one_sq]

end HasOrthonormalCols

end NLAlib
