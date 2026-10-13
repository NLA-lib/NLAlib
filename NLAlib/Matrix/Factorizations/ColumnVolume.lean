/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Adjugate
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.UnitarilyInvariant

/-!
# The volume of a set of columns

The volume of the columns of a matrix `C` is measured by the Gram determinant `det (Cᴴ C)`. This
file computes how it changes when a column is exchanged or appended, and derives the singular
value bounds that follow when no exchange with the columns of a second block increases it by much.
These are the estimates behind strong rank-revealing QR factorizations; the certificate that
packages them for a column selection is in `NLAlib.Matrix.Factorizations.RankRevealing`.

The second block is written `C T + D` with `D` orthogonal to the range of `C`, so that `T` holds
the interpolation coefficients and `D` the residual. The hypothesis on the exchanges enters only
through the budget `‖T‖_F² + ‖C⁺‖_F² ‖D‖_F²`.

## Main results

* `NLAlib.re_det_conjTranspose_mul_self_updateCol`: the volume after exchanging a column.
* `NLAlib.re_det_conjTranspose_mul_self_fromCols`: the volume after appending a column.
* `NLAlib.frobNorm_sq_add_frobNorm_pinv_sq_mul_le`: the budget of a locally maximal selection.
* `NLAlib.singularValues_fromCols_le_sqrt_mul`,
  `NLAlib.singularValues_le_sqrt_mul_singularValues_fromCols`: singular value bounds for
  `[C, C T + D]` from a budget.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]

/-! ### Volume under a column exchange -/

/-- **The Gram determinant after replacing a column.** If column `i` of `C` is replaced by
`C t + d` with `d` orthogonal to the range of `C`, the Gram determinant is multiplied by
`|t i|² + ‖d‖² ((Cᴴ C)⁻¹)_{ii}`. [GuEisenstat1996, Lemma 3.1].
Port of `NLAlib.det_gram_updateCol_eq_det_mul`, there over `ℝ`. -/
theorem re_det_conjTranspose_mul_self_updateCol [DecidableEq p] {C : Matrix m p 𝕜}
    (hC : Function.Injective C.mulVec) (i : p) (t : p → 𝕜) {d : m → 𝕜} (hd : Cᴴ *ᵥ d = 0) :
    RCLike.re ((C.updateCol i (C *ᵥ t + d))ᴴ * C.updateCol i (C *ᵥ t + d)).det =
      RCLike.re (Cᴴ * C).det *
        (‖t i‖ ^ 2 + ‖WithLp.toLp 2 d‖ ^ 2 * RCLike.re ((Cᴴ * C)⁻¹ i i)) := by
  have hGu : IsUnit (Cᴴ * C).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_conjTranspose_mul_self_iff.mpr hC)
  have hGH : (Cᴴ * C).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self C
  set K : Matrix p p 𝕜 := (1 : Matrix p p 𝕜).updateCol i t with hK
  set R : Matrix m p 𝕜 := (0 : Matrix m p 𝕜).updateCol i d with hR
  have hM : C * K = C.updateCol i (C *ᵥ t) := by rw [hK, Matrix.mul_updateCol, Matrix.mul_one]
  have hUpd : C.updateCol i (C *ᵥ t + d) = C * K + R := by
    rw [hM, hR]
    ext a b
    by_cases hb : b = i
    · subst hb
      simp only [Matrix.updateCol_self, Matrix.add_apply, Pi.add_apply]
    · simp only [Matrix.updateCol_ne hb, Matrix.add_apply, Matrix.zero_apply, add_zero]
  have hCR : Cᴴ * R = 0 := by
    rw [hR, Matrix.mul_updateCol, Matrix.mul_zero, hd, Matrix.updateCol_zero_zero]
  have hRC : Rᴴ * C = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose C, ← Matrix.conjTranspose_mul, hCR,
      Matrix.conjTranspose_zero]
  have hRR : Rᴴ * R = Matrix.single i i (star d ⬝ᵥ d) := by
    ext a b
    simp only [hR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.updateCol_apply,
      Matrix.zero_apply, Matrix.single_apply, dotProduct, Pi.star_apply]
    by_cases ha : a = i
    · by_cases hb : b = i
      · simp [ha, hb]
      · simp [ha, hb, Ne.symm hb]
    · simp [ha, Ne.symm ha]
  have hGram : (C * K + R)ᴴ * (C * K + R) =
      Kᴴ * (Cᴴ * C) * K + Matrix.single i i (star d ⬝ᵥ d) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hRR,
      Matrix.conjTranspose_mul, Matrix.mul_assoc Kᴴ Cᴴ R, hCR, Matrix.mul_zero,
      ← Matrix.mul_assoc Rᴴ C K, hRC, Matrix.zero_mul, add_zero, zero_add]
    simp only [Matrix.mul_assoc]
  have hKdet : K.det = t i := by
    rw [hK, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have hadj : (Kᴴ * (Cᴴ * C) * K).adjugate i i = (Cᴴ * C).adjugate i i := by
    refine Matrix.adjugate_apply_self_congr i fun a b ha hb => ?_
    have h1 : Kᴴ * (Cᴴ * C) * K = (C * K)ᴴ * (C * K) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hM, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.updateCol_ne ha,
      Matrix.updateCol_ne hb]
  have hinv : (Cᴴ * C).adjugate i i = (Cᴴ * C).det * (Cᴴ * C)⁻¹ i i := by
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
      mul_inv_cancel_left₀ hGu.ne_zero]
  have hdet : ((C * K + R)ᴴ * (C * K + R)).det = (Cᴴ * C).det *
      (star (t i) * t i + (star d ⬝ᵥ d) * (Cᴴ * C)⁻¹ i i) := by
    rw [hGram, Matrix.det_add_single, hadj, hinv, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose, hKdet]
    ring
  rw [hUpd, hdet, hGH.re_det_mul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, map_add,
    RCLike.re_ofReal_mul, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

/-- **The Gram determinant after appending a column**: the volume is multiplied by the distance
of the new column to the range of the old ones, `det (Gram [C, v]) = det (Gram C) ‖(1 - P_C) v‖²`.
Port of `NLAlib.det_gram_fromCols_eq_mul_frobSq_sub_projector`, there over `ℝ`. -/
theorem re_det_conjTranspose_mul_self_fromCols [DecidableEq m] [DecidableEq p]
    (C : Matrix m p 𝕜) (v : m → 𝕜) :
    RCLike.re ((Matrix.fromCols C (Matrix.replicateCol Unit v))ᴴ *
      Matrix.fromCols C (Matrix.replicateCol Unit v)).det =
      RCLike.re (Cᴴ * C).det * ‖WithLp.toLp 2 ((1 - rangeProjector C) *ᵥ v)‖ ^ 2 := by
  set V : Matrix m Unit 𝕜 := Matrix.replicateCol Unit v with hV
  set w : m → 𝕜 := (1 - rangeProjector C) *ᵥ v with hw
  have hGram : (Matrix.fromCols C V)ᴴ * Matrix.fromCols C V =
      Matrix.fromBlocks (Cᴴ * C) (Cᴴ * V) (Cᴴ * V)ᴴ (Vᴴ * V) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hGH : (Cᴴ * C).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self C
  by_cases hC : Function.Injective C.mulVec
  · have hu : IsUnit (Cᴴ * C) := isUnit_conjTranspose_mul_self_iff.mpr hC
    have hP : (1 - rangeProjector C)ᴴ * (1 - rangeProjector C) = 1 - rangeProjector C := by
      rw [(isStarProjection_one_sub_rangeProjector C).conjTranspose_eq,
        (isStarProjection_one_sub_rangeProjector C).mul_self]
    have hS : Vᴴ * V - (Cᴴ * V)ᴴ * (Cᴴ * C)⁻¹ * (Cᴴ * V) =
        (Matrix.replicateCol Unit w)ᴴ * Matrix.replicateCol Unit w := by
      have h1 : Matrix.replicateCol Unit w = (1 - rangeProjector C) * V := by
        rw [hw, hV, Matrix.replicateCol_mulVec]
      rw [h1, Matrix.conjTranspose_mul (1 - rangeProjector C) V, Matrix.mul_assoc Vᴴ,
        ← Matrix.mul_assoc (1 - rangeProjector C)ᴴ, hP,
        rangeProjector_eq_mul_inv_mul_conjTranspose hu, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.conjTranspose_mul Cᴴ V, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hGram, det_eq_det_toBlocks₁₁_mul_det _ (by rwa [Matrix.toBlocks_fromBlocks₁₁]),
      Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, hGH.re_det_mul, hS,
      Matrix.det_unique ((Matrix.replicateCol Unit w)ᴴ * Matrix.replicateCol Unit w),
      Matrix.mul_apply]
    congr 1
    rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct]
    rfl
  · have h0 : (Cᴴ * C).det = 0 := by
      by_contra h
      exact hC (isUnit_conjTranspose_mul_self_iff.mp
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)))
    have hle := re_det_fromBlocks_le_of_posSemidef (hGram ▸
      Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols C V))
    have hge := (Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols C V)).det_nonneg
    rw [h0, map_zero, zero_mul] at hle ⊢
    rw [hGram] at hge ⊢
    exact le_antisymm hle (RCLike.nonneg_iff.mp hge).1

/-! ### Bounds from a budget -/

/-- **The budget of a locally maximal selection.** Let `C` have full column rank and let the
other columns be `C T + D` with `D` orthogonal to the range of `C`. If
`|T i j|² + ‖D_j‖² ((Cᴴ C)⁻¹)_{ii} ≤ f²` for all `i`, `j` (which by the volume formula says that
no exchange increases the volume by more than `f²`), then
`‖T‖_F² + ‖C⁺‖_F² ‖D‖_F² ≤ f² · p · q`. [GuEisenstat1996, Theorem 3.2].
Port of `NLAlib.frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume`. -/
theorem frobNorm_sq_add_frobNorm_pinv_sq_mul_le [DecidableEq p] {C : Matrix m p 𝕜}
    {T : Matrix p q 𝕜} {D : Matrix m q 𝕜} {f : ℝ} (hC : Function.Injective C.mulVec)
    (h : ∀ i j, ‖T i j‖ ^ 2 +
      ‖WithLp.toLp 2 (D.col j)‖ ^ 2 * RCLike.re ((Cᴴ * C)⁻¹ i i) ≤ f ^ 2) :
    frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤
      f ^ 2 * Fintype.card p * Fintype.card q := by
  have hsum : ∑ i : p, ∑ j : q, (‖T i j‖ ^ 2 +
      ‖WithLp.toLp 2 (D.col j)‖ ^ 2 * RCLike.re ((Cᴴ * C)⁻¹ i i)) ≤ ∑ _i : p, ∑ _j : q, f ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
  have htr : RCLike.re ((Cᴴ * C)⁻¹).trace = ∑ i, RCLike.re ((Cᴴ * C)⁻¹ i i) := by
    rw [Matrix.trace, map_sum]
    rfl
  rw [frobNorm_pinv_sq_eq_re_trace_inv hC, frobNorm_sq_eq_sum T, frobNorm_sq_eq_sum_col D, htr,
    Finset.sum_mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ _ := hsum
    _ = _ := by ring

/-- A singular value below the rank times the Frobenius norm of the pseudoinverse is at least
one. -/
private theorem one_le_sq_singularValues_mul_frobNorm_pinv_sq (C : Matrix m p 𝕜) {i : ℕ}
    (hi : i < C.rank) : 1 ≤ singularValues C i ^ 2 * frobNorm (pinv C) ^ 2 := by
  have hpos : 0 < singularValues C i ^ 2 := pow_pos ((singularValues_pos_iff C).mpr hi) 2
  have hle : (singularValues C i ^ 2)⁻¹ ≤ frobNorm (pinv C) ^ 2 := by
    rw [frobNorm_pinv_sq]
    exact Finset.single_le_sum (f := fun k => (singularValues C k ^ 2)⁻¹)
      (fun k _ => inv_nonneg.mpr (sq_nonneg _)) (Finset.mem_range.mpr hi)
  calc (1 : ℝ) = singularValues C i ^ 2 * (singularValues C i ^ 2)⁻¹ :=
        (mul_inv_cancel₀ hpos.ne').symm
    _ ≤ singularValues C i ^ 2 * frobNorm (pinv C) ^ 2 := by gcongr

/-- **The selected columns capture the leading singular values**: with budget
`b ≥ ‖T‖_F² + ‖C⁺‖_F² ‖D‖_F²`, `σ_i([C, C T + D]) ≤ √(1 + b) σ_i(C)` for `i` below the number of
columns of `C`.
Port of `NLAlib.singularValues_upper_block_le_sqrt_budget_mul`, there for a triangular `C`. -/
theorem singularValues_fromCols_le_sqrt_mul {C : Matrix m p 𝕜} {T : Matrix p q 𝕜}
    {D : Matrix m q 𝕜} {b : ℝ} (hC : Function.Injective C.mulVec) (hD : Cᴴ * D = 0)
    (hb : frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤ b) {i : ℕ}
    (hi : i < Fintype.card p) :
    singularValues (Matrix.fromCols C (C * T + D)) i ≤ √(1 + b) * singularValues C i := by
  classical
  set Ci := truncatedSVD C i with hCi
  set E := C - Ci with hE
  set σ := singularValues C i with hσ
  have hσ0 : 0 ≤ σ := singularValues_nonneg C i
  have hB : (Ci * Matrix.fromCols (1 : Matrix p p 𝕜) T).rank ≤ i :=
    (Matrix.rank_mul_le_left _ _).trans (rank_truncatedSVD_le C i)
  have hdiff : Matrix.fromCols C (C * T + D) - Ci * Matrix.fromCols (1 : Matrix p p 𝕜) T =
      E * Matrix.fromCols (1 : Matrix p p 𝕜) T + Matrix.fromCols (0 : Matrix m p 𝕜) D := by
    rw [hE, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_one]
    ext a (b | b)
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.fromCols_apply_inl,
        Matrix.zero_apply, add_zero]
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.fromCols_apply_inr, Matrix.sub_mul]
      ring
  have hCiD : Ciᴴ * D = 0 := by
    have h1 : rangeProjector C * Ci = Ci :=
      rangeProjector_mul_eq_self_iff.mpr (range_mulVecLin_truncatedSVD_le C i)
    rw [← h1, Matrix.conjTranspose_mul, conjTranspose_rangeProjector, Matrix.mul_assoc,
      rangeProjector_mul_eq_zero_iff.mpr hD, Matrix.mul_zero]
  have horth : (E * Matrix.fromCols (1 : Matrix p p 𝕜) T)ᴴ * Matrix.fromCols (0 : Matrix m p 𝕜) D
      = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.mul_zero, hE,
      Matrix.conjTranspose_sub, Matrix.sub_mul, hD, hCiD, sub_zero, Matrix.fromCols_zero,
      Matrix.mul_zero]
  have hX : specNorm (E * Matrix.fromCols (1 : Matrix p p 𝕜) T) ^ 2 ≤
      σ ^ 2 * (1 + frobNorm T ^ 2) := by
    have h1 := specNorm_mul_le E (Matrix.fromCols (1 : Matrix p p 𝕜) T)
    rw [hE, hCi, specNorm_sub_truncatedSVD] at h1
    have h2 := specNorm_fromCols_sq_le (1 : Matrix p p 𝕜) T
    have h3 : specNorm (1 : Matrix p p 𝕜) ^ 2 ≤ 1 :=
      pow_le_one₀ (specNorm_nonneg _) specNorm_one_le
    have h4 : specNorm T ^ 2 ≤ frobNorm T ^ 2 :=
      pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm T) 2
    calc specNorm (E * Matrix.fromCols (1 : Matrix p p 𝕜) T) ^ 2
        ≤ (σ * specNorm (Matrix.fromCols (1 : Matrix p p 𝕜) T)) ^ 2 :=
          pow_le_pow_left₀ (specNorm_nonneg _) h1 2
      _ = σ ^ 2 * specNorm (Matrix.fromCols (1 : Matrix p p 𝕜) T) ^ 2 := mul_pow _ _ _
      _ ≤ σ ^ 2 * (1 + frobNorm T ^ 2) := by gcongr; linarith
  have hY : specNorm (Matrix.fromCols (0 : Matrix m p 𝕜) D) ^ 2 ≤ frobNorm D ^ 2 := by
    have h1 := specNorm_fromCols_sq_le (0 : Matrix m p 𝕜) D
    rw [specNorm_zero] at h1
    have h2 : specNorm D ^ 2 ≤ frobNorm D ^ 2 :=
      pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm D) 2
    linarith
  have hinv := one_le_sq_singularValues_mul_frobNorm_pinv_sq C
    (hi.trans_eq (mulVec_injective_iff_rank_eq.mp hC).symm)
  have hsq : specNorm (Matrix.fromCols C (C * T + D) -
      Ci * Matrix.fromCols (1 : Matrix p p 𝕜) T) ^ 2 ≤ (√(1 + b) * σ) ^ 2 := by
    have hb0 : 0 ≤ b := le_trans (add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) hb
    rw [hdiff, mul_pow, Real.sq_sqrt (by linarith)]
    have h1 := specNorm_add_sq_le_of_conjTranspose_mul_eq_zero horth
    have h2 : frobNorm D ^ 2 ≤ σ ^ 2 * frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hinv
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg σ)]
  exact (singularValues_le_specNorm_sub_of_rank_le _ hB).trans
    ((sq_le_sq₀ (specNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hσ0)).mp hsq)

/-- The scalar inequality behind the trailing bound. -/
private theorem sq_mul_add_le_one_add_mul {s X Y U V Fc Ft Fd b : ℝ} (hs : 0 ≤ s) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hFt : 0 ≤ Ft)
    (hx : X ≤ Fc * U + Ft * Y) (hy : s * Y ≤ V) (hsd : s ≤ Fd)
    (hb : Ft ^ 2 + Fc ^ 2 * Fd ^ 2 ≤ b) : s ^ 2 * (X ^ 2 + Y ^ 2) ≤ (1 + b) * (U ^ 2 + V ^ 2) := by
  have h1 : s * X ≤ s * Fc * U + Ft * V := by
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy hFt]
  have h2 : (s * X) ^ 2 ≤ (s * Fc * U + Ft * V) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hs hX) h1 2
  have h3 : (s * Fc * U + Ft * V) ^ 2 ≤ ((s * Fc) ^ 2 + Ft ^ 2) * (U ^ 2 + V ^ 2) := by
    nlinarith [sq_nonneg (s * Fc * V - Ft * U)]
  have h4 : (s * Fc) ^ 2 ≤ Fc ^ 2 * Fd ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsd 2) (sq_nonneg Fc)
  have h5 : ((s * Fc) ^ 2 + Ft ^ 2) * (U ^ 2 + V ^ 2) ≤ b * (U ^ 2 + V ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h6 : (s * Y) ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (mul_nonneg hs hY) hy 2
  nlinarith [sq_nonneg U]

omit [Fintype q] in
/-- The subspace of vectors on `p ⊕ q` whose `q`-part lies in a subspace of dimension `d` has
dimension `card p + d`. -/
private theorem exists_submodule_sum_finrank [Finite q] (Y : Submodule 𝕜 (q → 𝕜)) :
    ∃ S : Submodule 𝕜 (p ⊕ q → 𝕜), Module.finrank 𝕜 S = Fintype.card p + Module.finrank 𝕜 Y ∧
      ∀ z ∈ S, (fun b => z (Sum.inr b)) ∈ Y := by
  let tail : ((p ⊕ q) → 𝕜) →ₗ[𝕜] (q → 𝕜) :=
    { toFun := fun z b => z (Sum.inr b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : Y.comap tail ≃ₗ[𝕜] ((p → 𝕜) × Y) :=
    { toFun := fun z => (fun a => z.val (Sum.inl a), ⟨tail z.val, z.property⟩)
      invFun := fun z => ⟨Sum.elim z.1 z.2.val, z.2.property⟩
      left_inv := fun z => Subtype.ext (funext fun a => by cases a <;> rfl)
      right_inv := fun z => Prod.ext rfl rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨Y.comap tail, by rw [e.finrank_eq, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card], fun z hz => hz⟩

/-- **The residual is no larger than the trailing singular values allow**: with budget
`b ≥ ‖T‖_F² + ‖C⁺‖_F² ‖D‖_F²`, `σ_j(D) ≤ √(1 + b) σ_{p+j}([C, C T + D])`.
Port of `NLAlib.singularValues_trailing_le_sqrt_budget_mul`, there for a triangular `C`. -/
theorem singularValues_le_sqrt_mul_singularValues_fromCols {C : Matrix m p 𝕜}
    {T : Matrix p q 𝕜} {D : Matrix m q 𝕜} {b : ℝ} (hC : Function.Injective C.mulVec)
    (hD : Cᴴ * D = 0) (hb : frobNorm T ^ 2 + frobNorm (pinv C) ^ 2 * frobNorm D ^ 2 ≤ b)
    (j : ℕ) :
    singularValues D j ≤
      √(1 + b) * singularValues (Matrix.fromCols C (C * T + D)) (Fintype.card p + j) := by
  classical
  have hb0 : 0 ≤ b := le_trans (add_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))) hb
  have hc : 0 < √(1 + b) := Real.sqrt_pos.mpr (by linarith)
  by_cases hj : j < Fintype.card q
  swap
  · rw [singularValues_of_card_cols_le D (not_lt.mp hj)]
    exact mul_nonneg hc.le (singularValues_nonneg _ _)
  set s := singularValues D j with hs
  have hs0 : 0 ≤ s := singularValues_nonneg D j
  obtain ⟨Y, hYdim, hY⟩ := exists_submodule_singularValues_mul_norm_le D hj
  obtain ⟨S, hSdim, hS⟩ := exists_submodule_sum_finrank (p := p) Y
  have hlow : s / √(1 + b) ≤
      singularValues (Matrix.fromCols C (C * T + D)) (Fintype.card p + j) := by
    refine le_singularValues_of_forall_mem _ S (by rw [hSdim, hYdim, add_assoc]) fun z hz => ?_
    set x : p → 𝕜 := fun a => z (Sum.inl a) with hx
    set y : q → 𝕜 := fun a => z (Sum.inr a) with hy
    set u : m → 𝕜 := C *ᵥ (x + T *ᵥ y) with hu
    set v : m → 𝕜 := D *ᵥ y with hv
    have hz' : z = Sum.elim x y := by
      funext a
      cases a <;> rfl
    have hMz : Matrix.fromCols C (C * T + D) *ᵥ z = u + v := by
      rw [hz', Matrix.fromCols_mulVec_sumElim, Matrix.add_mulVec, hu, hv, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, add_assoc]
    have huv : star u ⬝ᵥ v = 0 := by
      rw [hu, hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hD,
        Matrix.zero_mulVec, dotProduct_zero]
    have hnorm : ‖WithLp.toLp 2 (u + v)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 + ‖WithLp.toLp 2 v‖ ^ 2 := by
      rw [WithLp.toLp_add, @norm_add_sq 𝕜, EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct,
        huv, map_zero, mul_zero, add_zero]
    have hxe : x = pinv C *ᵥ u - T *ᵥ y := by
      rw [hu, pinv_mulVec_mulVec_of_injective hC, add_sub_cancel_right]
    have hxn : ‖WithLp.toLp 2 x‖ ≤
        frobNorm (pinv C) * ‖WithLp.toLp 2 u‖ + frobNorm T * ‖WithLp.toLp 2 y‖ := by
      rw [hxe, WithLp.toLp_sub]
      exact (norm_sub_le _ _).trans (add_le_add (norm_toLp_mulVec_le_frobNorm_mul _ _)
        (norm_toLp_mulVec_le_frobNorm_mul _ _))
    have hmain := sq_mul_add_le_one_add_mul hs0 (norm_nonneg (WithLp.toLp 2 x))
      (norm_nonneg (WithLp.toLp 2 y)) (frobNorm_nonneg T) hxn (hY y (hS z hz))
      ((singularValues_le_specNorm D j).trans (specNorm_le_frobNorm D)) hb
    rw [hMz]
    refine (sq_le_sq₀ (mul_nonneg (div_nonneg hs0 hc.le) (norm_nonneg _)) (norm_nonneg _)).mp ?_
    rw [hnorm, mul_pow, div_pow, Real.sq_sqrt (by linarith), hz',
      EuclideanSpace.norm_toLp_sumElim_sq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  exact ((div_le_iff₀ hc).mp hlow).trans_eq (mul_comm _ _)

end NLAlib
