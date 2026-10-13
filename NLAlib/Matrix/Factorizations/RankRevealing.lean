/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.UnitarilyInvariant

/-!
# Rank-revealing column selection

A choice of `k` columns `C = A.submatrix id e` of a matrix `A` is rank-revealing when the selected
columns are as well conditioned as the leading part of `A` allows and what they miss is as small
as the trailing part. The interface is in terms of three matrices built from the selection: the
selected columns `C`, the interpolation coefficients `pinv C * A`, and the residual
`(1 - rangeProjector C) * A`. A rank-revealing QR factorization is a thin QR factorization of
`C`; a CUR or interpolative decomposition uses `C` and `pinv C * A` directly; a selection of rows
is a selection of columns of `Aᴴ`.

The certificate is `NLAlib.IsLocalMaxVolume A e f`: the selected columns are independent and no
exchange of one selected column for another column of `A` increases the volume `det (Cᴴ C)` by
more than `f²` (Gu and Eisenstat). It bounds the interpolation coefficients by `f` and the
singular values of `C` and of the residual against those of `A` within `√(1 + f² k (n - k))`. A
selection of maximum volume exists and satisfies the certificate with `f = 1`.

## Main definitions

* `NLAlib.IsLocalMaxVolume`: the certificate.

## Main results

* `NLAlib.re_det_conjTranspose_mul_self_updateCol`: the volume after exchanging a column.
* `NLAlib.IsLocalMaxVolume.norm_pinv_mul_apply_le`: the coefficient bound.
* `NLAlib.IsLocalMaxVolume.singularValues_le_sqrt_mul`,
  `NLAlib.IsLocalMaxVolume.singularValues_one_sub_rangeProjector_mul_le`: singular value bounds.
* `NLAlib.IsLocalMaxVolume.matrixNorm_one_sub_rangeProjector_mul_le`: the residual against the
  best rank-`k` error in every unitarily invariant norm.
* `NLAlib.exists_embedding_isLocalMaxVolume`: a selection of maximum volume exists.
* `NLAlib.exists_embedding_eq_mul_pinv_mul`: an interpolative decomposition at the rank.
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

/-- **The Gram determinant after appending a column**: the volume is multiplied by the distance
of the new column to the range of the old ones, `det (Gram [C, v]) = det (Gram C) ‖(1 - P_C) v‖²`.
Port of `NLAlib.det_gram_fromCols_eq_mul_frobSq_sub_projector`, there over `ℝ`. -/
theorem re_det_conjTranspose_mul_self_fromCols (C : Matrix m p 𝕜) (v : m → 𝕜) :
    RCLike.re ((Matrix.fromCols C (Matrix.replicateCol Unit v))ᴴ *
      Matrix.fromCols C (Matrix.replicateCol Unit v)).det =
      RCLike.re (Cᴴ * C).det * ‖WithLp.toLp 2 ((1 - rangeProjector C) *ᵥ v)‖ ^ 2 := by
  sorry

/-! ### Bounds from a budget -/

/-- **The budget of a locally maximal selection.** Let `C` have full column rank and let the
other columns be `C T + D` with `D` orthogonal to the range of `C`. If
`|T i j|² + ‖D_j‖² ((Cᴴ C)⁻¹)_{ii} ≤ f²` for all `i`, `j` (which by the volume formula says that
no exchange increases the volume by more than `f²`), then
`‖T‖_F² + ‖C⁺‖_F² ‖D‖_F² ≤ f² · p · q`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume`. -/
theorem frobNorm_sq_add_frobNorm_pinv_sq_mul_le {C : Matrix m p 𝕜} {T : Matrix p q 𝕜}
    {D : Matrix m q 𝕜} {f : ℝ} (hC : Function.Injective C.mulVec)
    (h : ∀ i j, ‖T i j‖ ^ 2 +
      ‖WithLp.toLp 2 (D.col j)‖ ^ 2 * RCLike.re ((Cᴴ * C)⁻¹ i i) ≤ f ^ 2) :
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

/-! ### The certificate -/

/-- `IsLocalMaxVolume A e f`: the columns of `A` selected by `e` are linearly independent, and
exchanging any one of them for any column of `A` increases the volume `det (Cᴴ C)` by a factor
at most `f²`. This is the stopping criterion of the strong rank-revealing QR algorithm.
[GuEisenstat1996, §3]. -/
structure IsLocalMaxVolume (A : Matrix m n 𝕜) (e : p → n) (f : ℝ) : Prop where
  /-- The selected columns are linearly independent. -/
  injective_mulVec : Function.Injective (A.submatrix id e).mulVec
  /-- The tolerance is nonnegative. -/
  nonneg : 0 ≤ f
  /-- No single exchange increases the volume by more than `f²`. -/
  re_det_le : ∀ (i : p) (j : n),
    RCLike.re ((A.submatrix id (Function.update e i j))ᴴ *
      A.submatrix id (Function.update e i j)).det ≤
    f ^ 2 * RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det

section Certificate

variable {A : Matrix m n 𝕜} {e : p → n} {f : ℝ}

/-- The tolerance of a nonempty locally maximal selection is at least one. -/
theorem IsLocalMaxVolume.one_le [Nonempty p] (h : IsLocalMaxVolume A e f) : 1 ≤ f := by
  sorry

/-- A locally maximal selection stays so for a larger tolerance. -/
theorem IsLocalMaxVolume.mono (h : IsLocalMaxVolume A e f) {g : ℝ} (hfg : f ≤ g) :
    IsLocalMaxVolume A e g := by
  sorry

/-- A selection of independent columns of the largest volume is locally maximal with tolerance
one. -/
theorem isLocalMaxVolume_one_of_forall_re_det_le
    (he : Function.Injective (A.submatrix id e).mulVec)
    (h : ∀ g : p → n, RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det ≤
      RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det) :
    IsLocalMaxVolume A e 1 := by
  sorry

/-- The interpolation coefficients of the selected columns are the identity. -/
theorem IsLocalMaxVolume.submatrix_pinv_mul (h : IsLocalMaxVolume A e f) :
    (pinv (A.submatrix id e) * A).submatrix id e = 1 := by
  sorry

/-- **Bounded interpolation coefficients.** For a locally maximal selection, every entry of
`pinv C * A` is at most `f` in absolute value. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, third bound, as a certificate. -/
theorem IsLocalMaxVolume.norm_pinv_mul_apply_le (h : IsLocalMaxVolume A e f) (i : p) (j : n) :
    ‖(pinv (A.submatrix id e) * A) i j‖ ≤ f := by
  sorry

/-- **The selected columns are well conditioned**:
`σ_i(A) ≤ √(1 + f² k (n - k)) σ_i(C)` for `i < k`, with `k` the number of selected columns.
[GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, first bound, as a certificate. -/
theorem IsLocalMaxVolume.singularValues_le_sqrt_mul (h : IsLocalMaxVolume A e f) {i : ℕ}
    (hi : i < Fintype.card p) :
    singularValues A i ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        singularValues (A.submatrix id e) i := by
  sorry

/-- **The residual of the selection is small**:
`σ_j((1 - P_C) A) ≤ √(1 + f² k (n - k)) σ_{k+j}(A)`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, second bound, as a certificate. -/
theorem IsLocalMaxVolume.singularValues_one_sub_rangeProjector_mul_le
    (h : IsLocalMaxVolume A e f) (j : ℕ) :
    singularValues ((1 - rangeProjector (A.submatrix id e)) * A) j ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        singularValues A (Fintype.card p + j) := by
  sorry

/-- **The column selection error against the best low-rank error**, in every unitarily invariant
norm: `‖A - C C⁺ A‖ ≤ √(1 + f² k (n - k)) ‖A - A_k‖`. This is the bound that CUR and
interpolative decompositions cite. -/
theorem IsLocalMaxVolume.matrixNorm_one_sub_rangeProjector_mul_le (Φ : SymmetricGauge)
    (h : IsLocalMaxVolume A e f) :
    Φ.matrixNorm ((1 - rangeProjector (A.submatrix id e)) * A) ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        Φ.matrixNorm (A - truncatedSVD A (Fintype.card p)) := by
  sorry

end Certificate

/-! ### Existence -/

/-- **A selection of maximum volume exists**: for `k ≤ rank A` there are `k` columns of `A` of
full rank whose Gram determinant is the largest among all choices of `k` columns.
Port of `NLAlib.exists_maximum_volume_column_embedding`, there over `ℝ`. -/
theorem exists_embedding_forall_re_det_le (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, Function.Injective (A.submatrix id e).mulVec ∧
      ∀ g : Fin k → n, RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det ≤
        RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det := by
  sorry

/-- **A strong rank-revealing selection exists.** For `k ≤ rank A` there are `k` columns of `A`
that are locally of maximum volume with tolerance one: coefficients `pinv C * A` bounded by one,
`σ_i(A) ≤ √(1 + k (n - k)) σ_i(C)` and residual
`σ_j((1 - P_C) A) ≤ √(1 + k (n - k)) σ_{k+j}(A)`.
[GuEisenstat1996, Theorem 3.2]; [GolubVanLoan2013, §5.4.6].
Port of `NLAlib.exists_strong_rank_revealing_qr` and `NLAlib.exists_maximum_volume_qr_blocks`,
in column-selection form.
Result: strong-rrqr -/
theorem exists_embedding_isLocalMaxVolume (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, IsLocalMaxVolume A e 1 := by
  sorry

/-- **At the rank, a selection of maximum volume reproduces the matrix**: for `k = rank A` the
residual vanishes, `A = C (C⁺ A)`, an interpolative decomposition with coefficients bounded by
one. Port of `NLAlib.exists_rank_adapted_maximum_volume_qr`. -/
theorem exists_embedding_eq_mul_pinv_mul (A : Matrix m n 𝕜) :
    ∃ e : Fin A.rank ↪ n, IsLocalMaxVolume A e 1 ∧
      A = A.submatrix id e * (pinv (A.submatrix id e) * A) := by
  sorry

end NLAlib
