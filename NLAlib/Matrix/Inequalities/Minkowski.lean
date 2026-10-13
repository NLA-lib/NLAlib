/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Inequalities.Determinant

/-!
# Minkowski's determinant inequality

Minkowski's inequality `(det A)^(1/N) + (det B)^(1/N) ≤ (det (A + B))^(1/N)` for positive
semidefinite matrices of size `N ≥ 1`, with its two consequences: `A ↦ (det A)^(1/N)` is concave
on the positive definite matrices, and the determinant is superadditive. Determinants of
Hermitian matrices are real; the inequalities are stated for `RCLike.re (det A)`.

## Main results

* `Matrix.PosSemidef.re_det_rpow_add_le`: Minkowski's inequality.
* `NLAlib.concaveOn_re_det_rpow`: concavity of the `N`-th root of the determinant.
* `Matrix.PosSemidef.re_det_add_le`: superadditivity of the determinant.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Superadditivity of the geometric mean against the constant sequence `1`. -/
private theorem one_add_prod_rpow_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {μ : ι → ℝ}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    1 + (∏ i ∈ s, μ i) ^ (s.card : ℝ)⁻¹ ≤ (∏ i ∈ s, (μ i + 1)) ^ (s.card : ℝ)⁻¹ := by
  have hw : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  have hsum : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs))]
  have hz : ∀ i ∈ s, 0 < μ i + 1 := fun i hi => by linarith [hμ i hi]
  have hz' : 0 ≤ ∏ i ∈ s, (μ i + 1) := Finset.prod_nonneg fun i hi => (hz i hi).le
  have h1 := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
    (fun i => (μ i + 1)⁻¹) (fun _ _ => hw) hsum fun i hi => (inv_pos.mpr (hz i hi)).le
  have h2 := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
    (fun i => μ i / (μ i + 1)) (fun _ _ => hw) hsum fun i hi => div_nonneg (hμ i hi) (hz i hi).le
  have h3 : ∑ i ∈ s, (s.card : ℝ)⁻¹ * (μ i + 1)⁻¹ + ∑ i ∈ s, (s.card : ℝ)⁻¹ * (μ i / (μ i + 1)) =
      1 := by
    rw [← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_) hsum
    rw [← mul_add, inv_eq_one_div (μ i + 1), ← add_div, add_comm 1, div_self (hz i hi).ne',
      mul_one]
  have hG : 0 < (∏ i ∈ s, (μ i + 1)) ^ (s.card : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (Finset.prod_pos hz) _
  rw [Real.finsetProd_rpow _ _ fun i hi => (inv_pos.mpr (hz i hi)).le, Finset.prod_inv_distrib,
    Real.inv_rpow hz'] at h1
  rw [Real.finsetProd_rpow _ _ fun i hi => div_nonneg (hμ i hi) (hz i hi).le,
    Finset.prod_div_distrib, Real.div_rpow (Finset.prod_nonneg hμ) hz'] at h2
  have h4 := mul_le_mul_of_nonneg_right (h3 ▸ add_le_add h1 h2) hG.le
  rwa [add_mul, inv_mul_cancel₀ hG.ne', div_mul_cancel₀ _ hG.ne', one_mul] at h4

/-- Minkowski's inequality against the identity. -/
private theorem one_add_re_det_rpow_le [Nonempty n] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    1 + RCLike.re M.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (M + (1 : ℝ) • (1 : Matrix n n 𝕜)).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have h := one_add_prod_rpow_le (s := Finset.range (Fintype.card n))
    (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero) (μ := eigenvalue M)
    fun i _ => hM.eigenvalue_nonneg i
  rw [Finset.card_range] at h
  rw [hM.isHermitian.det_eq_prod_range_eigenvalue, RCLike.ofReal_re,
    (hM.isHermitian.add (isHermitian_real_smul_one 1)).det_eq_prod_range_eigenvalue,
    RCLike.ofReal_re,
    Finset.prod_congr rfl fun k hk =>
      hM.isHermitian.eigenvalue_add_smul_one 1 (Finset.mem_range.mp hk)]
  exact h

/-- A positive definite matrix is congruent to the identity. -/
private theorem exists_conjTranspose_mul_mul_eq_one {A : Matrix n n 𝕜} (hA : A.PosDef) :
    ∃ C : Matrix n n 𝕜, Cᴴ * A * C = 1 := by
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSu : IsUnit (CFC.sqrt A) := by
    refine IsUnit.of_mul_eq_one (CFC.sqrt A * A⁻¹) ?_
    rw [← Matrix.mul_assoc, hSS,
      Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hSu
  refine ⟨(CFC.sqrt A)⁻¹, ?_⟩
  calc (CFC.sqrt A)⁻¹ᴴ * A * (CFC.sqrt A)⁻¹
      = (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by rw [hS.inv.eq, hSS]
    _ = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hdet]

/-- The determinant of a congruence. -/
private theorem re_det_conjTranspose_mul_mul (X C : Matrix n n 𝕜) :
    RCLike.re (Cᴴ * X * C).det = ‖C.det‖ ^ 2 * RCLike.re X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- Minkowski's inequality when the first matrix is positive definite. -/
private theorem re_det_rpow_add_le_of_posDef [Nonempty n] {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_conjTranspose_mul_mul_eq_one hA
  have h := one_add_re_det_rpow_le (hB.conjTranspose_mul_mul_same C)
  have hsum : Cᴴ * B * C + (1 : ℝ) • (1 : Matrix n n 𝕜) = Cᴴ * (A + B) * C := by
    rw [one_smul, ← hC, Matrix.mul_add, Matrix.add_mul, add_comm]
  have h1 : ‖C.det‖ ^ 2 * RCLike.re A.det = 1 := by
    rw [← re_det_conjTranspose_mul_mul, hC, Matrix.det_one, RCLike.one_re]
  have hc : 0 ≤ ‖C.det‖ ^ 2 := sq_nonneg _
  have hc' : 0 < (‖C.det‖ ^ 2) ^ (Fintype.card n : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (lt_of_le_of_ne hc fun h0 => by simp [← h0] at h1) _
  have ha : 0 ≤ RCLike.re A.det := (RCLike.nonneg_iff.mp hA.posSemidef.det_nonneg).1
  have hb : 0 ≤ RCLike.re B.det := (RCLike.nonneg_iff.mp hB.det_nonneg).1
  have hab : 0 ≤ RCLike.re (A + B).det :=
    (RCLike.nonneg_iff.mp (hA.posSemidef.add hB).det_nonneg).1
  rw [hsum, re_det_conjTranspose_mul_mul, re_det_conjTranspose_mul_mul, Real.mul_rpow hc hb,
    Real.mul_rpow hc hab] at h
  have h2 : (‖C.det‖ ^ 2) ^ (Fintype.card n : ℝ)⁻¹ * RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ =
      1 := by
    rw [← Real.mul_rpow hc ha, h1, Real.one_rpow]
  refine le_of_mul_le_mul_left ?_ hc'
  rw [mul_add, h2]
  exact h

/-- **Minkowski's determinant inequality.** For positive semidefinite `A`, `B` of size `N ≥ 1`,
`(det A)^(1/N) + (det B)^(1/N) ≤ (det (A + B))^(1/N)`.
[HornJohnson2013, Theorem 7.8.21].
Port of `NLAlib.det_rpow_inv_card_add_le`, there over `ℝ` for positive definite matrices.
Result: minkowski-determinant-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_rpow_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have hw : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  have hcont : Continuous fun X : Matrix n n 𝕜 => RCLike.re X.det ^ (Fintype.card n : ℝ)⁻¹ :=
    (Real.continuous_rpow_const hw).comp (RCLike.continuous_re.comp (continuous_id.matrix_det))
  exact Matrix.PosSemidef.le_of_forall_posDef_le
    (f := fun X : Matrix n n 𝕜 =>
      RCLike.re X.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹)
    (g := fun X : Matrix n n 𝕜 => RCLike.re (X + B).det ^ (Fintype.card n : ℝ)⁻¹)
    (hcont.add continuous_const) (hcont.comp (continuous_id.add continuous_const))
    (fun _ hM => re_det_rpow_add_le_of_posDef hM hB) hA

/-- The determinant root is positively homogeneous of degree one. -/
private theorem re_det_real_smul_rpow [Nonempty n] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {a : ℝ} (ha : 0 ≤ a) :
    RCLike.re (a • A).det ^ (Fintype.card n : ℝ)⁻¹ =
      a * RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), Matrix.det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul, Real.mul_rpow (pow_nonneg ha _) (RCLike.nonneg_iff.mp hA.det_nonneg).1,
    Real.pow_rpow_inv_natCast ha Fintype.card_ne_zero]

/-- `A ↦ (det A)^(1/N)` is concave on the positive definite matrices.
[HornJohnson2013, Theorem 7.8.21]. Port of `NLAlib.concaveOn_det_rpow_inv_card`. -/
theorem concaveOn_re_det_rpow [Nonempty n] :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      fun A => RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  refine ⟨fun A hA B hB a b ha hb hab => ?_, fun A hA B hB a b ha hb _ => ?_⟩
  · rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      simpa [hab] using hB
    · exact (Matrix.PosDef.smul hA ha').add_posSemidef (hB.posSemidef.smul hb)
  · have h := (hA.posSemidef.smul ha).re_det_rpow_add_le (hB.posSemidef.smul hb)
    rwa [re_det_real_smul_rpow hA.posSemidef ha, re_det_real_smul_rpow hB.posSemidef hb] at h

/-- The determinant is superadditive on positive semidefinite matrices of positive size:
`det A + det B ≤ det (A + B)`. [HornJohnson2013, §7.8]. -/
theorem _root_.Matrix.PosSemidef.re_det_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef) : RCLike.re A.det + RCLike.re B.det ≤ RCLike.re (A + B).det := by
  have hN : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have ha : 0 ≤ RCLike.re A.det := (RCLike.nonneg_iff.mp hA.det_nonneg).1
  have hb : 0 ≤ RCLike.re B.det := (RCLike.nonneg_iff.mp hB.det_nonneg).1
  have hab : 0 ≤ RCLike.re (A + B).det := (RCLike.nonneg_iff.mp (hA.add hB).det_nonneg).1
  have h := pow_le_pow_left₀ (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
    (hA.re_det_rpow_add_le hB) (Fintype.card n)
  rw [Real.rpow_inv_natCast_pow hab hN] at h
  refine le_trans ?_ ((pow_add_pow_le (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _) hN).trans h)
  rw [Real.rpow_inv_natCast_pow ha hN, Real.rpow_inv_natCast_pow hb hN]

end NLAlib
