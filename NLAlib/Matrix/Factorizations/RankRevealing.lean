/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.ColumnVolume

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
selection of maximum volume exists and satisfies the certificate with `f = 1`. The volume formulas
and the bounds from a budget that the certificate rests on are in
`NLAlib.Matrix.Factorizations.ColumnVolume`.

## Main definitions

* `NLAlib.IsLocalMaxVolume`: the certificate.

## Main results

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

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype p] [DecidableEq p]

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

omit [RCLike 𝕜] [Fintype m] [Fintype p] in
/-- Exchanging a selected column is a column update of the selected matrix. -/
private theorem submatrix_update (A : Matrix m n 𝕜) (e : p → n) (i : p) (j : n) :
    A.submatrix id (Function.update e i j) = (A.submatrix id e).updateCol i (A.col j) := by
  ext a b
  by_cases hb : b = i
  · subst hb
    simp only [Matrix.submatrix_apply, Function.update_self, Matrix.updateCol_self, id,
      Matrix.col_apply]
  · simp only [Matrix.submatrix_apply, Function.update_of_ne hb, Matrix.updateCol_ne hb]

/-- The Gram determinant of independent columns is positive. -/
private theorem re_det_conjTranspose_mul_self_pos {C : Matrix m p 𝕜}
    (hC : Function.Injective C.mulVec) : 0 < RCLike.re (Cᴴ * C).det :=
  (RCLike.pos_iff.mp (posDef_conjTranspose_mul_self_iff.mpr hC).det_pos).1

/-- The Gram determinant after replacing a column by an arbitrary vector, split into its
component in the range and the residual. -/
private theorem re_det_conjTranspose_mul_self_updateCol_eq [DecidableEq m] {C : Matrix m p 𝕜}
    (hC : Function.Injective C.mulVec) (i : p) (a : m → 𝕜) :
    RCLike.re ((C.updateCol i a)ᴴ * C.updateCol i a).det = RCLike.re (Cᴴ * C).det *
      (‖(pinv C *ᵥ a) i‖ ^ 2 + ‖WithLp.toLp 2 ((1 - rangeProjector C) *ᵥ a)‖ ^ 2 *
        RCLike.re ((Cᴴ * C)⁻¹ i i)) := by
  have ha : a = C *ᵥ (pinv C *ᵥ a) + (1 - rangeProjector C) *ᵥ a := by
    rw [Matrix.mulVec_mulVec, mul_pinv, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  have hd : Cᴴ *ᵥ ((1 - rangeProjector C) *ᵥ a) = 0 := by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_one_sub_rangeProjector, Matrix.zero_mulVec]
  conv_lhs => rw [ha]
  exact re_det_conjTranspose_mul_self_updateCol hC i _ hd

omit [Fintype m] [DecidableEq p] in
/-- A selection of independent columns has no repeated column. -/
private theorem injective_of_injective_mulVec_submatrix {A : Matrix m n 𝕜} {e : p → n}
    (h : Function.Injective (A.submatrix id e).mulVec) : Function.Injective e := by
  classical
  intro a b hab
  by_contra hne
  have h1 : A.submatrix id e *ᵥ Pi.single a 1 = A.submatrix id e *ᵥ Pi.single b 1 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    ext l
    simp only [Matrix.col_apply, Matrix.submatrix_apply, hab]
  have h2 := congrFun (h h1) a
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h2
  exact one_ne_zero h2

omit [DecidableEq p] in
/-- The singular values of a matrix padded with zero columns. -/
private theorem singularValues_fromCols_zero [Fintype q] (D : Matrix m q 𝕜) :
    singularValues (Matrix.fromCols (0 : Matrix m p 𝕜) D) = singularValues D := by
  rw [← singularValues_conjTranspose, ← singularValues_conjTranspose D]
  refine singularValues_eq_of_conjTranspose_mul_self_eq ?_
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.zero_mul, zero_add]

omit [DecidableEq p] in
/-- A matrix with its columns permuted so that the selected ones come first, written through the
interpolation coefficients and the residual of the other columns. -/
private theorem submatrix_eq_fromCols [DecidableEq m] (A : Matrix m n 𝕜) {e : p → n}
    (ec : p ⊕ q ≃ n) (hec : ∀ a, ec (Sum.inl a) = e a) :
    A.submatrix id ec = Matrix.fromCols (A.submatrix id e)
      (A.submatrix id e * (pinv (A.submatrix id e) * A).submatrix id (ec ∘ Sum.inr) +
        ((1 - rangeProjector (A.submatrix id e)) * A).submatrix id (ec ∘ Sum.inr)) := by
  have h : A.submatrix id e * (pinv (A.submatrix id e) * A) +
      (1 - rangeProjector (A.submatrix id e)) * A = A := by
    rw [← Matrix.mul_assoc, mul_pinv, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  ext a (b | b)
  · simp only [Matrix.submatrix_apply, id, hec, Matrix.fromCols_apply_inl]
  · exact (congrFun (congrFun h a) (ec (Sum.inr b))).symm

omit [DecidableEq p] in
/-- The residual with its columns permuted so that the selected ones come first. -/
private theorem one_sub_rangeProjector_mul_submatrix_eq_fromCols [DecidableEq m]
    (A : Matrix m n 𝕜) {e : p → n} (ec : p ⊕ q ≃ n) (hec : ∀ a, ec (Sum.inl a) = e a) :
    ((1 - rangeProjector (A.submatrix id e)) * A).submatrix id ec =
      Matrix.fromCols (0 : Matrix m p 𝕜)
        (((1 - rangeProjector (A.submatrix id e)) * A).submatrix id (ec ∘ Sum.inr)) := by
  have h := one_sub_rangeProjector_mul_self (A.submatrix id e)
  ext a (b | b)
  · simp only [Matrix.submatrix_apply, id, hec, Matrix.fromCols_apply_inl, Matrix.zero_apply]
    exact congrFun (congrFun h a) b
  · rfl

omit [DecidableEq p] in
/-- The residual is orthogonal to the selected columns. -/
private theorem conjTranspose_mul_one_sub_rangeProjector_mul_submatrix [DecidableEq m]
    (A : Matrix m n 𝕜) (e : p → n) (g : q → n) :
    (A.submatrix id e)ᴴ * ((1 - rangeProjector (A.submatrix id e)) * A).submatrix id g =
      (0 : Matrix p q 𝕜) := by
  have h : (A.submatrix id e)ᴴ * ((1 - rangeProjector (A.submatrix id e)) * A) = 0 := by
    rw [← Matrix.mul_assoc, conjTranspose_mul_one_sub_rangeProjector, Matrix.zero_mul]
  ext a b
  exact congrFun (congrFun h a) (g b)

omit [Fintype p] [DecidableEq p] in
/-- The complement of an injective selection, as a splitting of the column index type. -/
private theorem exists_equiv_sum_compl {e : p → n} (he : Function.Injective e) :
    ∃ ec : p ⊕ ↥(Set.range e)ᶜ ≃ n, ∀ a, ec (Sum.inl a) = e a := by
  classical
  exact ⟨((Equiv.ofInjective e he).sumCongr (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e)), fun _ => rfl⟩

/-- The tolerance of a nonempty locally maximal selection is at least one. -/
theorem IsLocalMaxVolume.one_le [Nonempty p] (h : IsLocalMaxVolume A e f) : 1 ≤ f := by
  obtain ⟨i⟩ := ‹Nonempty p›
  have h1 := h.re_det_le i (e i)
  rw [Function.update_eq_self] at h1
  have hpos := re_det_conjTranspose_mul_self_pos h.injective_mulVec
  exact (one_le_sq_iff₀ h.nonneg).mp (le_of_mul_le_mul_right (by linarith) hpos)

/-- A locally maximal selection stays so for a larger tolerance. -/
theorem IsLocalMaxVolume.mono (h : IsLocalMaxVolume A e f) {g : ℝ} (hfg : f ≤ g) :
    IsLocalMaxVolume A e g := by
  refine ⟨h.injective_mulVec, h.nonneg.trans hfg, fun i j => (h.re_det_le i j).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.nonneg hfg 2)
    (re_det_conjTranspose_mul_self_pos h.injective_mulVec).le

/-- A selection of independent columns of the largest volume is locally maximal with tolerance
one. -/
theorem isLocalMaxVolume_one_of_forall_re_det_le
    (he : Function.Injective (A.submatrix id e).mulVec)
    (h : ∀ g : p → n, RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det ≤
      RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det) :
    IsLocalMaxVolume A e 1 := by
  refine ⟨he, zero_le_one, fun i j => ?_⟩
  rw [one_pow, one_mul]
  exact h _

/-- The interpolation coefficients of the selected columns are the identity. -/
theorem IsLocalMaxVolume.submatrix_pinv_mul (h : IsLocalMaxVolume A e f) :
    (pinv (A.submatrix id e) * A).submatrix id e = 1 := by
  rw [Matrix.submatrix_mul _ _ id id e Function.bijective_id, Matrix.submatrix_id_id,
    pinv_mul_self_of_injective h.injective_mulVec]

/-- The exchange inequality of a locally maximal selection, entry by entry: this is the budget
hypothesis of `frobNorm_sq_add_frobNorm_pinv_sq_mul_le`. -/
private theorem IsLocalMaxVolume.norm_sq_add_le [DecidableEq m] (h : IsLocalMaxVolume A e f)
    (i : p) (j : n) :
    ‖(pinv (A.submatrix id e) * A) i j‖ ^ 2 +
      ‖WithLp.toLp 2 (((1 - rangeProjector (A.submatrix id e)) * A).col j)‖ ^ 2 *
        RCLike.re (((A.submatrix id e)ᴴ * A.submatrix id e)⁻¹ i i) ≤ f ^ 2 := by
  have h1 := h.re_det_le i j
  rw [submatrix_update, re_det_conjTranspose_mul_self_updateCol_eq h.injective_mulVec,
    mul_comm (f ^ 2)] at h1
  exact le_of_mul_le_mul_left h1 (re_det_conjTranspose_mul_self_pos h.injective_mulVec)

/-- The budget of a locally maximal selection against any family of columns. -/
private theorem IsLocalMaxVolume.frobNorm_sq_add_le [DecidableEq m] [Fintype q]
    (h : IsLocalMaxVolume A e f) (g : q → n) :
    frobNorm ((pinv (A.submatrix id e) * A).submatrix id g) ^ 2 +
      frobNorm (pinv (A.submatrix id e)) ^ 2 *
        frobNorm (((1 - rangeProjector (A.submatrix id e)) * A).submatrix id g) ^ 2 ≤
      f ^ 2 * Fintype.card p * Fintype.card q :=
  frobNorm_sq_add_frobNorm_pinv_sq_mul_le h.injective_mulVec fun i j => h.norm_sq_add_le i (g j)

/-- **Bounded interpolation coefficients.** For a locally maximal selection, every entry of
`pinv C * A` is at most `f` in absolute value. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, third bound, as a certificate. -/
theorem IsLocalMaxVolume.norm_pinv_mul_apply_le (h : IsLocalMaxVolume A e f) (i : p) (j : n) :
    ‖(pinv (A.submatrix id e) * A) i j‖ ≤ f := by
  classical
  have h1 := h.norm_sq_add_le i j
  have h2 : 0 ≤ RCLike.re (((A.submatrix id e)ᴴ * A.submatrix id e)⁻¹ i i) :=
    (RCLike.nonneg_iff.mp
      (posDef_conjTranspose_mul_self_iff.mpr h.injective_mulVec).inv.posSemidef.diag_nonneg).1
  exact abs_le_of_sq_le_sq' (by nlinarith [mul_nonneg (sq_nonneg
    ‖WithLp.toLp 2 (((1 - rangeProjector (A.submatrix id e)) * A).col j)‖) h2]) h.nonneg |>.2

/-- **The selected columns are well conditioned**:
`σ_i(A) ≤ √(1 + f² k (n - k)) σ_i(C)` for `i < k`, with `k` the number of selected columns.
[GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, first bound, as a certificate. -/
theorem IsLocalMaxVolume.singularValues_le_sqrt_mul [Fintype n] (h : IsLocalMaxVolume A e f)
    {i : ℕ} (hi : i < Fintype.card p) :
    singularValues A i ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        singularValues (A.submatrix id e) i := by
  classical
  obtain ⟨ec, hec⟩ := exists_equiv_sum_compl
    (injective_of_injective_mulVec_submatrix h.injective_mulVec)
  have hcard : (Fintype.card n : ℝ) - Fintype.card p = Fintype.card ↥(Set.range e)ᶜ := by
    rw [← Fintype.card_congr ec, Fintype.card_sum, Nat.cast_add, add_sub_cancel_left]
  rw [hcard, ← singularValues_submatrix_equiv A (Equiv.refl m) ec, Equiv.coe_refl,
    submatrix_eq_fromCols A ec hec]
  exact singularValues_fromCols_le_sqrt_mul h.injective_mulVec
    (conjTranspose_mul_one_sub_rangeProjector_mul_submatrix A e _) (h.frobNorm_sq_add_le _) hi

/-- **The residual of the selection is small**:
`σ_j((1 - P_C) A) ≤ √(1 + f² k (n - k)) σ_{k+j}(A)`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.exists_strong_rank_revealing_qr`, second bound, as a certificate. -/
theorem IsLocalMaxVolume.singularValues_one_sub_rangeProjector_mul_le [Fintype n] [DecidableEq m]
    (h : IsLocalMaxVolume A e f) (j : ℕ) :
    singularValues ((1 - rangeProjector (A.submatrix id e)) * A) j ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        singularValues A (Fintype.card p + j) := by
  classical
  obtain ⟨ec, hec⟩ := exists_equiv_sum_compl
    (injective_of_injective_mulVec_submatrix h.injective_mulVec)
  have hcard : (Fintype.card n : ℝ) - Fintype.card p = Fintype.card ↥(Set.range e)ᶜ := by
    rw [← Fintype.card_congr ec, Fintype.card_sum, Nat.cast_add, add_sub_cancel_left]
  have h1 : singularValues ((1 - rangeProjector (A.submatrix id e)) * A) =
      singularValues
        (((1 - rangeProjector (A.submatrix id e)) * A).submatrix id (ec ∘ Sum.inr)) := by
    rw [← singularValues_submatrix_equiv _ (Equiv.refl m) ec, Equiv.coe_refl,
      one_sub_rangeProjector_mul_submatrix_eq_fromCols A ec hec, singularValues_fromCols_zero]
  have h2 : singularValues A = singularValues (A.submatrix id ec) := by
    rw [← singularValues_submatrix_equiv A (Equiv.refl m) ec, Equiv.coe_refl]
  rw [hcard, h1, h2, submatrix_eq_fromCols A ec hec]
  exact singularValues_le_sqrt_mul_singularValues_fromCols h.injective_mulVec
    (conjTranspose_mul_one_sub_rangeProjector_mul_submatrix A e _) (h.frobNorm_sq_add_le _) j

/-- **The column selection error against the best low-rank error**, in every unitarily invariant
norm: `‖A - C C⁺ A‖ ≤ √(1 + f² k (n - k)) ‖A - A_k‖`. This is the bound that CUR and
interpolative decompositions cite. -/
theorem IsLocalMaxVolume.matrixNorm_one_sub_rangeProjector_mul_le [Fintype n] [DecidableEq m]
    (Φ : SymmetricGauge) (h : IsLocalMaxVolume A e f) :
    Φ.matrixNorm ((1 - rangeProjector (A.submatrix id e)) * A) ≤
      √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) *
        Φ.matrixNorm (A - truncatedSVD A (Fintype.card p)) := by
  set c : ℝ := √(1 + f ^ 2 * Fintype.card p * ((Fintype.card n : ℝ) - Fintype.card p)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have h1 : ∀ j, singularValues ((1 - rangeProjector (A.submatrix id e)) * A) j ≤
      singularValues ((c : 𝕜) • (A - truncatedSVD A (Fintype.card p))) j := fun j => by
    rw [singularValues_smul, singularValues_sub_truncatedSVD, RCLike.norm_ofReal,
      abs_of_nonneg hc0]
    exact h.singularValues_one_sub_rangeProjector_mul_le j
  calc Φ.matrixNorm ((1 - rangeProjector (A.submatrix id e)) * A)
      ≤ Φ.matrixNorm ((c : 𝕜) • (A - truncatedSVD A (Fintype.card p))) :=
        Φ.matrixNorm_le_of_singularValues_le h1
    _ = c * Φ.matrixNorm (A - truncatedSVD A (Fintype.card p)) := by
        rw [Φ.matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg hc0]

end Certificate

/-! ### Existence -/

/-- **A selection of maximum volume exists**: for `k ≤ rank A` there are `k` columns of `A` of
full rank whose Gram determinant is the largest among all choices of `k` columns.
Port of `NLAlib.exists_maximum_volume_column_embedding`, there over `ℝ`. -/
theorem exists_embedding_forall_re_det_le [Fintype n] (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, Function.Injective (A.submatrix id e).mulVec ∧
      ∀ g : Fin k → n, RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det ≤
        RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det := by
  classical
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin k → n, Function.Injective (A.submatrix id e₀).mulVec := by
    obtain ⟨c, hc, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq 𝕜 (Set.range A.col)
    choose a ha using hc
    have hk' : k ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range A.col)) :=
      hk.trans_eq (Matrix.rank_eq_finrank_span_cols A)
    refine ⟨fun i => a (Fin.castLE hk' i), Matrix.mulVec_injective_iff.mpr ?_⟩
    have hcol : (A.submatrix id fun i => a (Fin.castLE hk' i)).col = c ∘ Fin.castLE hk' :=
      funext fun i => ha (Fin.castLE hk' i)
    rw [hcol]
    exact hli.comp _ (Fin.castLE_injective hk')
  obtain ⟨e, -, he⟩ := Finset.exists_max_image Finset.univ
    (fun g : Fin k → n => RCLike.re ((A.submatrix id g)ᴴ * A.submatrix id g).det)
    ⟨e₀, Finset.mem_univ _⟩
  have hpos : 0 < RCLike.re ((A.submatrix id e)ᴴ * A.submatrix id e).det :=
    (re_det_conjTranspose_mul_self_pos he₀).trans_le (he e₀ (Finset.mem_univ _))
  have hinj : Function.Injective (A.submatrix id e).mulVec := by
    refine isUnit_conjTranspose_mul_self_iff.mp
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr fun h0 => ?_))
    rw [h0, map_zero] at hpos
    exact lt_irrefl _ hpos
  exact ⟨⟨e, injective_of_injective_mulVec_submatrix hinj⟩, hinj,
    fun g => he g (Finset.mem_univ _)⟩

/-- **A strong rank-revealing selection exists.** For `k ≤ rank A` there are `k` columns of `A`
that are locally of maximum volume with tolerance one: coefficients `pinv C * A` bounded by one,
`σ_i(A) ≤ √(1 + k (n - k)) σ_i(C)` and residual
`σ_j((1 - P_C) A) ≤ √(1 + k (n - k)) σ_{k+j}(A)`.
[GuEisenstat1996, Theorem 3.2]; [GolubVanLoan2013, §5.4.6].
Port of `NLAlib.exists_strong_rank_revealing_qr` and `NLAlib.exists_maximum_volume_qr_blocks`,
in column-selection form.
Result: strong-rrqr -/
theorem exists_embedding_isLocalMaxVolume [Fintype n] (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, IsLocalMaxVolume A e 1 := by
  obtain ⟨e, he, hmax⟩ := exists_embedding_forall_re_det_le A hk
  exact ⟨e, isLocalMaxVolume_one_of_forall_re_det_le he hmax⟩

/-- **At the rank, a selection of maximum volume reproduces the matrix**: for `k = rank A` the
residual vanishes, `A = C (C⁺ A)`, an interpolative decomposition with coefficients bounded by
one. Port of `NLAlib.exists_rank_adapted_maximum_volume_qr`. -/
theorem exists_embedding_eq_mul_pinv_mul [Fintype n] (A : Matrix m n 𝕜) :
    ∃ e : Fin A.rank ↪ n, IsLocalMaxVolume A e 1 ∧
      A = A.submatrix id e * (pinv (A.submatrix id e) * A) := by
  classical
  obtain ⟨e, he, hmax⟩ := exists_embedding_forall_re_det_le A le_rfl
  refine ⟨e, isLocalMaxVolume_one_of_forall_re_det_le he hmax, ?_⟩
  have hle : LinearMap.range (A.submatrix id e).mulVecLin ≤ LinearMap.range A.mulVecLin :=
    range_mulVecLin_le_iff_exists_mul.mpr ⟨selectionMatrix e, (mul_selectionMatrix A e).symm⟩
  have heq : LinearMap.range (A.submatrix id e).mulVecLin = LinearMap.range A.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    change (A.submatrix id e).rank = A.rank
    rw [mulVec_injective_iff_rank_eq.mp he, Fintype.card_fin]
  rw [← Matrix.mul_assoc]
  exact (mul_pinv_mul_eq_of_range_le heq.ge).symm

end NLAlib
