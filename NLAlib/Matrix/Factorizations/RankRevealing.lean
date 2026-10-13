/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Rank-revealing column selection

A choice of `k` columns `C = A.submatrix id e` of a matrix `A` is rank-revealing when the selected
columns are as well conditioned as the leading part of `A` allows and what they miss is as small
as the trailing part. The interface is in terms of three matrices built from the selection: the
selected columns `C`, the interpolation coefficients `pinv C * A`, and the residual
`(1 - rangeProjector C) * A`. A rank-revealing QR factorization is a thin QR factorization of
`C`; a CUR or interpolative decomposition uses `C` and `pinv C * A` directly.

The certificate is local maximality of the volume `det (Cᴴ C)` up to a factor `f²` under
exchanges of one selected column (Gu and Eisenstat). It bounds the interpolation coefficients by
`f` and the singular values of `C` and of the residual against those of `A` within
`√(1 + f² k (n - k))`. A selection of maximum volume exists and satisfies the certificate with
`f = 1`.

## Main results

* `NLAlib.re_det_conjTranspose_mul_self_updateCol`: the volume after exchanging a column.
* `NLAlib.norm_pinv_mul_apply_le_of_forall_re_det_le`: the coefficient bound.
* `NLAlib.singularValues_le_sqrt_mul_singularValues_submatrix`,
  `NLAlib.singularValues_one_sub_rangeProjector_mul_le_sqrt_mul`: the singular value bounds.
* `NLAlib.exists_embedding_forall_re_det_le`: a selection of maximum volume exists.
* `NLAlib.exists_embedding_rank_revealing`: existence of a strong rank-revealing selection.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ### Volume under a column exchange -/

/-- **The Gram determinant after replacing a column.** If column `i` of `C` is replaced by
`C t + d` with `d` orthogonal to the range of `C`, the Gram determinant is multiplied by
`|t i|² + ‖d‖² ((Cᴴ C)⁻¹)_{ii}`. [GuEisenstat1996, Lemma 3.1].
Port of `NLAlib.det_gram_updateCol_eq_det_mul`, there over `ℝ`. -/
theorem re_det_conjTranspose_mul_self_updateCol {C : Matrix m p 𝕜}
    (hC : Function.Injective C.mulVec) (i : p) (t : p → 𝕜) {d : m → 𝕜} (hd : Cᴴ *ᵥ d = 0) :
    RCLike.re ((C.updateCol i (C *ᵥ t + d))ᴴ * C.updateCol i (C *ᵥ t + d)).det =
      RCLike.re (Cᴴ * C).det *
        (‖t i‖ ^ 2 + ‖WithLp.toLp 2 d‖ ^ 2 * RCLike.re ((Cᴴ * C)⁻¹ i i)) := by
  sorry

/-! ### The certificate, in block form -/

/-- **Local maximality of the volume bounds the coefficients.** Let `C` have full column rank and
let the other columns be `C T + D` with `D` orthogonal to the range of `C`. If exchanging any
column of `C` for any other column increases the Gram determinant by at most `f²`, then every
entry of `T` is at most `f` in absolute value. [GuEisenstat1996, §3].
Port of `NLAlib.frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume`, first part. -/
theorem norm_apply_le_of_forall_re_det_updateCol_le {C : Matrix m p 𝕜} {T : Matrix p q 𝕜}
    {D : Matrix m q 𝕜} {f : ℝ} (hf : 0 ≤ f) (hC : Function.Injective C.mulVec)
    (hD : Cᴴ * D = 0)
    (hmax : ∀ i j, RCLike.re ((C.updateCol i ((C * T + D).col j))ᴴ *
      C.updateCol i ((C * T + D).col j)).det ≤ f ^ 2 * RCLike.re (Cᴴ * C).det)
    (i : p) (j : q) : ‖T i j‖ ≤ f := by
  sorry

/-- **Local maximality of the volume bounds the budget**
`‖T‖_F² + ‖C⁺‖_F² ‖D‖_F² ≤ f² · p · q`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume`, second part. -/
theorem frobNorm_sq_add_frobNorm_pinv_sq_mul_le {C : Matrix m p 𝕜} {T : Matrix p q 𝕜}
    {D : Matrix m q 𝕜} {f : ℝ} (hC : Function.Injective C.mulVec) (hD : Cᴴ * D = 0)
    (hmax : ∀ i j, RCLike.re ((C.updateCol i ((C * T + D).col j))ᴴ *
      C.updateCol i ((C * T + D).col j)).det ≤ f ^ 2 * RCLike.re (Cᴴ * C).det) :
    frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤
      f ^ 2 * Fintype.card p * Fintype.card q := by
  sorry

/-- **The selected columns capture the leading singular values**: with budget
`b ≥ ‖T‖_F² + ‖C⁺‖_F² ‖D‖_F²`, `σ_i([C, C T + D]) ≤ √(1 + b) σ_i(C)` for `i` below the number of
columns of `C`.
Port of `NLAlib.singularValues_upper_block_le_sqrt_budget_mul`, there for a triangular `C`. -/
theorem singularValues_fromCols_le_sqrt_mul {C : Matrix m p 𝕜} {T : Matrix p q 𝕜}
    {D : Matrix m q 𝕜} {b : ℝ} (hC : Function.Injective C.mulVec) (hD : Cᴴ * D = 0)
    (hb : frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤ b) {i : ℕ}
    (hi : i < Fintype.card p) :
    singularValues (Matrix.fromCols C (C * T + D)) i ≤ √(1 + b) * singularValues C i := by
  sorry

/-- **The residual is no larger than the trailing singular values allow**: with budget
`b ≥ ‖T‖_F² + ‖C⁺‖_F² ‖D‖_F²`, `σ_j(D) ≤ √(1 + b) σ_{p+j}([C, C T + D])`.
Port of `NLAlib.singularValues_trailing_le_sqrt_budget_mul`, there for a triangular `C`. -/
theorem singularValues_le_sqrt_mul_singularValues_fromCols {C : Matrix m p 𝕜}
    {T : Matrix p q 𝕜} {D : Matrix m q 𝕜} {b : ℝ} (hC : Function.Injective C.mulVec)
    (hD : Cᴴ * D = 0) (hb : frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤ b)
    (j : ℕ) :
    singularValues D j ≤
      √(1 + b) * singularValues (Matrix.fromCols C (C * T + D)) (Fintype.card p + j) := by
  sorry

/-! ### The certificate, for a selection of columns -/

section Selection

variable {k : ℕ} {A : Matrix m n 𝕜} {e : Fin k → n} {f : ℝ}

/-- **Bounded interpolation coefficients.** If the selected columns have full rank and no
exchange of one selected column increases the volume by more than `f²`, every entry of
`pinv C * A` is at most `f` in absolute value. [GuEisenstat1996, Theorem 3.2].
Result: strong-rrqr -/
theorem norm_pinv_mul_apply_le_of_forall_re_det_le
    (he : Function.Injective (A.submatrix id e).mulVec)
    (hmax : ∀ (i : Fin k) (j : n),
      RCLike.re ((A.submatrix id (Function.update e i j))ᴴ *
        A.submatrix id (Function.update e i j)).det ≤
      f ^ 2 * RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det)
    (i : Fin k) (j : n) : ‖(pinv (A.submatrix id e) * A) i j‖ ≤ f := by
  sorry

/-- **The selected columns are well conditioned**:
`σ_i(A) ≤ √(1 + f² k (n - k)) σ_i(C)` for `i < k`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, first bound, as a certificate.
Result: strong-rrqr -/
theorem singularValues_le_sqrt_mul_singularValues_submatrix
    (he : Function.Injective (A.submatrix id e).mulVec)
    (hmax : ∀ (i : Fin k) (j : n),
      RCLike.re ((A.submatrix id (Function.update e i j))ᴴ *
        A.submatrix id (Function.update e i j)).det ≤
      f ^ 2 * RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det)
    {i : ℕ} (hi : i < k) :
    singularValues A i ≤
      √(1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k)) * singularValues (A.submatrix id e) i := by
  sorry

/-- **The residual of the selection is small**:
`σ_j((1 - P_C) A) ≤ √(1 + f² k (n - k)) σ_{k+j}(A)`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, second bound, as a certificate.
Result: strong-rrqr -/
theorem singularValues_one_sub_rangeProjector_mul_le_sqrt_mul
    (he : Function.Injective (A.submatrix id e).mulVec)
    (hmax : ∀ (i : Fin k) (j : n),
      RCLike.re ((A.submatrix id (Function.update e i j))ᴴ *
        A.submatrix id (Function.update e i j)).det ≤
      f ^ 2 * RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det)
    (j : ℕ) :
    singularValues ((1 - rangeProjector (A.submatrix id e)) * A) j ≤
      √(1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k)) * singularValues A (k + j) := by
  sorry

end Selection

/-! ### Existence -/

/-- **A selection of maximum volume exists**: for `k ≤ rank A` there are `k` columns of `A` of
full rank whose Gram determinant is the largest among all choices of `k` columns.
Port of `NLAlib.exists_maximum_volume_column_embedding`, there over `ℝ`. -/
theorem exists_embedding_forall_re_det_le (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, Function.Injective (A.submatrix id e).mulVec ∧
      ∀ g : Fin k → n, RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det ≤
        RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det := by
  sorry

/-- **A strong rank-revealing selection exists.** For `k ≤ rank A` there are `k` columns `C` of
`A` with interpolation coefficients `pinv C * A` bounded by one, with
`σ_i(A) ≤ √(1 + k (n - k)) σ_i(C)` for `i < k`, and with residual
`σ_j((1 - P_C) A) ≤ √(1 + k (n - k)) σ_{k+j}(A)`.
[GuEisenstat1996, Theorem 3.2]; [GolubVanLoan2013, §5.4.6].
Port of `NLAlib.exists_strong_rank_revealing_qr` and `NLAlib.exists_maximum_volume_qr_blocks`,
in column-selection form.
Result: strong-rrqr -/
theorem exists_embedding_rank_revealing (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, Function.Injective (A.submatrix id e).mulVec ∧
      (∀ i j, ‖(pinv (A.submatrix id e) * A) i j‖ ≤ 1) ∧
      (∀ i, i < k → singularValues A i ≤
        √(1 + k * ((Fintype.card n : ℝ) - k)) * singularValues (A.submatrix id e) i) ∧
      ∀ j, singularValues ((1 - rangeProjector (A.submatrix id e)) * A) j ≤
        √(1 + k * ((Fintype.card n : ℝ) - k)) * singularValues A (k + j) := by
  sorry

/-- **At the rank, a selection of maximum volume reproduces the matrix**: for `k = rank A` the
residual vanishes, `A = C (C⁺ A)`, an interpolative decomposition with coefficients bounded by
one. Port of `NLAlib.exists_rank_adapted_maximum_volume_qr`. -/
theorem exists_embedding_eq_mul_pinv_mul (A : Matrix m n 𝕜) :
    ∃ e : Fin A.rank ↪ n, Function.Injective (A.submatrix id e).mulVec ∧
      A = A.submatrix id e * (pinv (A.submatrix id e) * A) ∧
      ∀ i j, ‖(pinv (A.submatrix id e) * A) i j‖ ≤ 1 := by
  sorry

end NLAlib
