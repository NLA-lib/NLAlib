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

/-- The spectral norm is at most the Frobenius norm.
[GolubVanLoan2013, (2.3.7)]. Port of `NLAlib.specNorm_le_frobNorm`. -/
theorem specNorm_le_frobNorm (A : Matrix m n 𝕜) : specNorm A ≤ frobNorm A := by
  sorry

/-- The Frobenius norm is at most `√(number of columns)` times the spectral norm, in squared
form. [GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_sq_le_card_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ Fintype.card n * specNorm A ^ 2 := by
  sorry

/-- The mixed product bound with the spectral norm on the left factor.
[HornJohnson2013, §5.6, Problem 20]. Port of `NLAlib.frobNorm_mul_le_specNorm_mul_frobNorm`. -/
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B := by
  sorry

/-- The mixed product bound with the spectral norm on the right factor.
Port of `NLAlib.frobNorm_mul_le_frobNorm_mul_specNorm`. -/
theorem frobNorm_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B := by
  sorry

/-- The Frobenius norm is submultiplicative. Port of `NLAlib.frobNorm_mul_le`. -/
theorem frobNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  sorry

/-- The spectral norm is `1`-Lipschitz for the Frobenius norm.
Port of `NLAlib.abs_specNorm_sub_specNorm_le_frobNorm`. -/
theorem abs_specNorm_sub_specNorm_le_frobNorm (A B : Matrix m n 𝕜) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) := by
  sorry

/-- The Frobenius inner product is bounded by a Frobenius norm times a spectral-Frobenius
product: `|⟨A * B, C⟩| ≤ specNorm A * frobNorm B * frobNorm C`. -/
theorem abs_frobInner_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) (C : Matrix l n 𝕜) :
    |frobInner (A * B) C| ≤ specNorm A * frobNorm B * frobNorm C := by
  sorry

/-! ### Factors with orthonormal columns -/

namespace HasOrthonormalCols

variable [DecidableEq n]

/-- Left multiplication by a matrix with orthonormal columns preserves the spectral norm.
Port of `NLAlib.specNorm_mul_left_of_hasOrthonormalCols`. -/
theorem specNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    specNorm (Q * A) = specNorm A := by
  sorry

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the spectral norm.
Port of `NLAlib.specNorm_mul_conjTranspose_right_of_hasOrthonormalCols`. -/
theorem specNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : specNorm (A * Qᴴ) = specNorm A := by
  sorry

/-- Left multiplication by a matrix with orthonormal columns preserves the Frobenius norm.
Port of `NLAlib.frobSq_mul_left_of_orthonormal`. -/
theorem frobNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    frobNorm (Q * A) = frobNorm A := by
  sorry

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the Frobenius norm. Port of `NLAlib.frobSq_mul_right_of_orthonormal`. -/
theorem frobNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : frobNorm (A * Qᴴ) = frobNorm A := by
  sorry

/-- Left multiplication of both arguments by a matrix with orthonormal columns preserves the
Frobenius inner product. Port of `NLAlib.frobInner_mul_left_of_orthonormal`. -/
theorem frobInner_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A B : Matrix n p 𝕜) :
    frobInner (Q * A) (Q * B) = frobInner A B := by
  sorry

/-- Left multiplication by `Qᴴ` does not increase the spectral norm. -/
theorem specNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : specNorm (Qᴴ * A) ≤ specNorm A := by
  sorry

/-- Left multiplication by `Qᴴ` does not increase the Frobenius norm.
Port of `NLAlib.frobSq_conjTranspose_mul_le`. -/
theorem frobNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : frobNorm (Qᴴ * A) ≤ frobNorm A := by
  sorry

/-- Right multiplication by a matrix with orthonormal columns does not increase the spectral
norm. -/
theorem specNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    specNorm (A * Q) ≤ specNorm A := by
  sorry

/-- Right multiplication by a matrix with orthonormal columns does not increase the Frobenius
norm. -/
theorem frobNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    frobNorm (A * Q) ≤ frobNorm A := by
  sorry

/-- Right multiplication by a unitary matrix preserves the spectral norm. -/
theorem specNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    specNorm (A * Q) = specNorm A := by
  sorry

/-- Right multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    frobNorm (A * Q) = frobNorm A := by
  sorry

/-- A matrix with orthonormal columns has spectral norm at most one.
Port of `NLAlib.specNorm_le_one_of_orthonormal`. -/
theorem specNorm_le_one {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : specNorm Q ≤ 1 := by
  sorry

/-- A matrix with orthonormal columns, and at least one column, has spectral norm one. -/
theorem specNorm_eq_one [Nonempty n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    specNorm Q = 1 := by
  sorry

/-- The squared Frobenius norm of a matrix with orthonormal columns is its number of columns.
Port of `NLAlib.frobSq_frame_eq_card`. -/
theorem frobNorm_sq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    frobNorm Q ^ 2 = Fintype.card n := by
  sorry

end HasOrthonormalCols

end NLAlib
