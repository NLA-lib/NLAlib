/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import NLAlib.Matrix.Functions.OperatorConvex
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Matrix.Inequalities.Determinant

/-!
# The logarithm of the determinant and the trace of the inverse

For a positive definite matrix, `log det A = tr log A`. The function `A ↦ log det A` is strictly
concave on positive definite matrices, `log det (1 + A) ≤ tr A`, and `A ↦ tr A⁻¹` is strictly
convex. These are the objective functions of D-optimal and A-optimal experimental design and the
potential functions of barrier arguments.

Determinants of Hermitian matrices are written `RCLike.re A.det`.

## Main results

* `Matrix.PosDef.log_re_det_eq_re_trace_cfc_log`: `log det A = tr log A`.
* `Matrix.PosSemidef.log_re_det_one_add_le_re_trace`: `log det (1 + A) ≤ tr A`.
* `NLAlib.strictConcaveOn_log_re_det`: strict concavity of `log det`.
* `NLAlib.strictConvexOn_re_trace_inv`: strict convexity of `tr A⁻¹`.
* `Matrix.PosDef.inv_smul_add_smul_le`: the inverse is operator convex.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The determinant through the eigenvalues -/

/-- The determinant of a function of a Hermitian matrix is the product over the eigenvalues. -/
theorem _root_.Matrix.IsHermitian.re_det_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    RCLike.re (cfc f A).det = ∏ i ∈ Finset.range (Fintype.card n), f (eigenvalue A i) := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  have hf := cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU f
  obtain ⟨e, he⟩ := exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose hU hr.symm hf
  have hH : (cfc f A).IsHermitian := cfc_predicate f A
  rw [hH.det_eq_prod_range_eigenvalue, RCLike.ofReal_re,
    ← Fin.prod_univ_eq_prod_range (fun i => eigenvalue (cfc f A) i),
    ← Fin.prod_univ_eq_prod_range (fun i => f (eigenvalue A i)), ← Equiv.prod_comp e]
  exact Finset.prod_congr rfl fun i _ => (he i).symm

/-- **`log det A = tr log A`** for positive definite `A`. -/
theorem _root_.Matrix.PosDef.log_re_det_eq_re_trace_cfc_log {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) = RCLike.re (cfc Real.log A).trace := by
  rw [hA.isHermitian.re_trace_cfc, hA.isHermitian.det_eq_prod_range_eigenvalue, RCLike.ofReal_re,
    Real.log_prod]
  exact fun i hi =>
    (hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA i (Finset.mem_range.mp hi)).ne'

/-- `det (exp A) = exp (tr A)` for Hermitian `A`. -/
theorem _root_.Matrix.IsHermitian.re_det_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (NormedSpace.exp A).det = Real.exp (RCLike.re A.trace) := by
  rw [hA.exp_eq_cfc, hA.re_det_cfc, hA.re_trace_eq_sum_range_eigenvalue, Real.exp_sum]

/-- **`log det (1 + A) ≤ tr A`** for positive semidefinite `A`. This is the inequality behind the
elliptical potential lemma and volume-based pivoting arguments. -/
theorem _root_.Matrix.PosSemidef.log_re_det_one_add_le_re_trace {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : Real.log (RCLike.re (1 + A).det) ≤ RCLike.re A.trace := by
  have h1 : (1 + A).PosDef := Matrix.PosDef.one.add_posSemidef hA
  rw [h1.log_re_det_eq_re_trace_cfc_log]
  exact re_trace_le_re_trace_of_le hA.cfc_log_one_add_le

/-- The product of `1 + x_i` over nonnegative reals is at least one plus their sum. -/
private theorem one_add_sum_le_prod {ι : Type*} (s : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) : 1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (x i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h2 := hx a (Finset.mem_insert_self a s)
    have h3 : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ x a + 1), mul_nonneg h2 h3]

/-- `1 + tr A ≤ det (1 + A)` for positive semidefinite `A`. -/
theorem _root_.Matrix.PosSemidef.one_add_re_trace_le_re_det_one_add {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : 1 + RCLike.re A.trace ≤ RCLike.re (1 + A).det := by
  have h1 : 1 + A = A + (1 : ℝ) • (1 : Matrix n n 𝕜) := by rw [one_smul, add_comm]
  rw [h1, (hA.isHermitian.add (isHermitian_real_smul_one 1)).det_eq_prod_range_eigenvalue,
    RCLike.ofReal_re, hA.isHermitian.re_trace_eq_sum_range_eigenvalue,
    Finset.prod_congr rfl fun k hk =>
      hA.isHermitian.eigenvalue_add_smul_one 1 (Finset.mem_range.mp hk)]
  exact one_add_sum_le_prod _ fun i _ => hA.eigenvalue_nonneg i

/-! ### Concavity of the logarithm of the determinant -/

/-- Two positive definite matrices are simultaneously congruent to diagonal matrices, the first
to the identity: with `A = R²` and `R⁻¹ B R⁻¹ = U diag(d) Uᴴ`, every real combination is
`a A + b B = R U diag(a + b d) Uᴴ R`. -/
private theorem exists_smul_add_smul_eq {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    ∃ (R : Matrix n n 𝕜) (U : Matrix n (Fin (Fintype.card n)) 𝕜)
      (d : Fin (Fintype.card n) → ℝ), R * R = A ∧ IsUnit R.det ∧ HasOrthonormalCols U ∧
      U * Uᴴ = 1 ∧ (∀ i, 0 < d i) ∧ ((∀ i, d i = 1) → A = B) ∧ ∀ a b : ℝ,
        a • A + b • B =
          R * (U * Matrix.diagonal (fun i => ((a + b * d i : ℝ) : 𝕜)) * Uᴴ) * R := by
  have hR : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hRR : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hdet : IsUnit (CFC.sqrt A).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit_sqrt
  have hM : ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosDef := by
    have h := hB.conjTranspose_mul_mul_same (B := (CFC.sqrt A)⁻¹)
      (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.mpr hA.isUnit_sqrt))
    rwa [hR.inv.eq] at h
  obtain ⟨U, hU, hMU⟩ := hM.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  have hUU : U * Uᴴ = 1 :=
    hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin (Fintype.card n)).symm
  have hB' : B = CFC.sqrt A * ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  generalize (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ = M at hM hMU hB'
  refine ⟨CFC.sqrt A, U, fun i => eigenvalue M i, hRR, hdet, hU, hUU,
    fun i => hM.isHermitian.posDef_iff_eigenvalue_pos.mp hM i i.isLt, fun h1 => ?_, fun a b => ?_⟩
  · rw [hB', hMU]
    simp only [h1, RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, hUU, hRR]
  · have h : Matrix.diagonal (fun i : Fin (Fintype.card n) =>
        ((a + b * eigenvalue M i : ℝ) : 𝕜)) = a • (1 : Matrix _ _ 𝕜) +
          b • Matrix.diagonal (fun i : Fin (Fintype.card n) => ((eigenvalue M i : ℝ) : 𝕜)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_add,
          RCLike.ofReal_mul]
      · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne hij, smul_zero, add_zero]
    rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, hUU, ← hMU, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR, Matrix.mul_smul, Matrix.smul_mul,
      ← hB']

/-- The determinant along the segment between two positive definite matrices, in simultaneously
diagonalising coordinates. -/
private theorem exists_re_det_smul_add_smul_eq {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) :
    ∃ d : Fin (Fintype.card n) → ℝ, (∀ i, 0 < d i) ∧ ((∀ i, d i = 1) → A = B) ∧
      ∀ a b : ℝ, RCLike.re (a • A + b • B).det = RCLike.re A.det * ∏ i, (a + b * d i) := by
  obtain ⟨R, U, d, hRR, -, hU, hUU, hd, hd1, hRd⟩ := exists_smul_add_smul_eq hA hB
  refine ⟨d, hd, hd1, fun a b => ?_⟩
  rw [hRd, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hRR,
    Matrix.det_conj_of_mul_eq_one hUU hU, Matrix.det_diagonal, ← RCLike.ofReal_prod,
    hA.isHermitian.re_det_mul, RCLike.ofReal_re]

/-- **The weighted geometric mean of determinants** is at most the determinant of the weighted
mean: `det A ^ a · det B ^ b ≤ det (a A + b B)` for positive definite `A`, `B` and weights
`a + b = 1`. [HornJohnson2013, Theorem 7.6.6 context].
Port of `NLAlib.det_rpow_mul_le_det_smul_add`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.re_det_rpow_mul_re_det_rpow_le {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    RCLike.re A.det ^ a * RCLike.re B.det ^ b ≤ RCLike.re (a • A + b • B).det := by
  obtain ⟨d, hd, -, hdet⟩ := exists_re_det_smul_add_smul_eq hA hB
  have hc : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1
  have hBd : RCLike.re B.det = RCLike.re A.det * ∏ i, d i := by simpa using hdet 0 1
  rw [hdet a b, hBd, Real.mul_rpow hc.le (Finset.prod_nonneg fun i _ => (hd i).le),
    ← mul_assoc, ← Real.rpow_add hc, hab, Real.rpow_one,
    ← Real.finsetProd_rpow _ _ (fun i _ => (hd i).le)]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
    (fun i _ => Real.rpow_nonneg (hd i).le b) fun i _ => ?_) hc.le
  have h := Real.geom_mean_le_arith_mean2_weighted ha hb zero_le_one (hd i).le hab
  rwa [Real.one_rpow, one_mul, mul_one] at h

/-- **`log det` is strictly concave** on the positive definite matrices.
[HornJohnson2013, Theorem 7.6.6]. Port of `NLAlib.strictConcaveOn_log_det`, there over `ℝ`.
Result: log-det-concavity -/
theorem strictConcaveOn_log_re_det :
    StrictConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef} fun A => Real.log (RCLike.re A.det) := by
  refine ⟨convex_setOf_posDef, fun A hA B hB hAB a b ha hb hab => ?_⟩
  obtain ⟨d, hd, hd1, hdet⟩ := exists_re_det_smul_add_smul_eq hA hB
  have hc : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1
  have hBd : RCLike.re B.det = RCLike.re A.det * ∏ i, d i := by simpa using hdet 0 1
  have hpos : ∀ i, 0 < a + b * d i := fun i => add_pos ha (mul_pos hb (hd i))
  change a • Real.log (RCLike.re A.det) + b • Real.log (RCLike.re B.det) <
    Real.log (RCLike.re (a • A + b • B).det)
  rw [hdet a b, hBd, Real.log_mul hc.ne' (Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne'),
    Real.log_mul hc.ne' (Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'),
    Real.log_prod fun i _ => (hd i).ne', Real.log_prod fun i _ => (hpos i).ne', smul_eq_mul,
    smul_eq_mul]
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 1 := by
    by_contra h
    exact hAB (hd1 fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  have hle : ∀ j, b * Real.log (d j) ≤ Real.log (a + b * d j) := fun j => by
    have h := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr one_pos)
      (Set.mem_Ioi.mpr (hd j)) ha.le hb.le hab
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] using h
  have hlt : b * Real.log (d i) < Real.log (a + b * d i) := by
    have h := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (hd i))
      hi.symm ha hb hab
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] using h
  have hsum := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
  rw [← Finset.mul_sum] at hsum
  have hscale : a * Real.log (RCLike.re A.det) + b * Real.log (RCLike.re A.det) =
      Real.log (RCLike.re A.det) := by rw [← add_mul, hab, one_mul]
  linarith

/-- Equality in the concavity of `log det` holds only at `A = B`.
Port of `NLAlib.log_det_smul_add_eq_iff`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.log_re_det_smul_add_smul_eq_iff {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (RCLike.re (a • A + b • B).det) =
        a * Real.log (RCLike.re A.det) + b * Real.log (RCLike.re B.det) ↔ A = B := by
  refine ⟨fun heq => ?_, ?_⟩
  · by_contra hne
    have h := strictConcaveOn_log_re_det.2 hA hB hne ha hb hab
    simp only [smul_eq_mul] at h
    exact h.ne' heq
  · rintro rfl
    rw [← add_smul, hab, one_smul, ← add_mul, hab, one_mul]

/-! ### The inverse -/

/-- **The inverse is operator convex** on positive definite matrices:
`(a A + b B)⁻¹ ≤ a A⁻¹ + b B⁻¹`. [Bhatia1997, Exercise V.1.15 context]. -/
theorem _root_.Matrix.PosDef.inv_smul_add_smul_le {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹ := by
  rw [Matrix.PosDef.inv_eq_cfc (convex_setOf_posDef hA hB ha hb hab), hA.inv_eq_cfc, hB.inv_eq_cfc]
  exact operatorConvexOn_inv.cfc_smul_add_smul_le hA.isHermitian hB.isHermitian
    hA.spectrum_subset_Ioi hB.spectrum_subset_Ioi ha hb hab

/-- The gap in the convexity of the reciprocal. -/
private theorem add_mul_inv_sub_inv {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hd : 0 < d) :
    a + b * d⁻¹ - (a + b * d)⁻¹ = a * b * (d - 1) ^ 2 / (d * (a + b * d)) := by
  have hpos : 0 < a + b * d := add_pos ha (mul_pos hb hd)
  obtain rfl : b = 1 - a := by linarith
  field_simp
  ring

/-- The trace of the inverse along the segment between two positive definite matrices, in
simultaneously diagonalising coordinates. -/
private theorem exists_re_trace_inv_smul_add_smul_eq {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) :
    ∃ w d : Fin (Fintype.card n) → ℝ, (∀ i, 0 < w i) ∧ (∀ i, 0 < d i) ∧
      ((∀ i, d i = 1) → A = B) ∧ ∀ a b : ℝ, (∀ i, a + b * d i ≠ 0) →
        RCLike.re (a • A + b • B)⁻¹.trace = ∑ i, (a + b * d i)⁻¹ * w i := by
  obtain ⟨R, U, d, hRR, hR, hU, hUU, hd, hd1, hRd⟩ := exists_smul_add_smul_eq hA hB
  have hG : (Uᴴ * A⁻¹ * U).PosDef := hA.inv.conjTranspose_mul_mul_same hU.mulVec_injective
  refine ⟨fun i => RCLike.re ((Uᴴ * A⁻¹ * U) i i), d, fun i => (RCLike.pos_iff.mp hG.diag_pos).1,
    hd, hd1, fun a b hab => ?_⟩
  have hDD : Matrix.diagonal (fun i => (((a + b * d i)⁻¹ : ℝ) : 𝕜)) *
      Matrix.diagonal (fun i => ((a + b * d i : ℝ) : 𝕜)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul, inv_mul_cancel₀ (hab i), RCLike.ofReal_one]
  have hinv : (a • A + b • B)⁻¹ =
      R⁻¹ * (U * Matrix.diagonal (fun i => (((a + b * d i)⁻¹ : ℝ) : 𝕜)) * Uᴴ) * R⁻¹ := by
    rw [hRd]
    refine Matrix.inv_eq_left_inv ?_
    calc R⁻¹ * (U * Matrix.diagonal (fun i => (((a + b * d i)⁻¹ : ℝ) : 𝕜)) * Uᴴ) * R⁻¹ *
          (R * (U * Matrix.diagonal (fun i => ((a + b * d i : ℝ) : 𝕜)) * Uᴴ) * R)
        = R⁻¹ * (U * (Matrix.diagonal (fun i => (((a + b * d i)⁻¹ : ℝ) : 𝕜)) * (Uᴴ *
            ((R⁻¹ * R) * U)) * Matrix.diagonal (fun i => ((a + b * d i : ℝ) : 𝕜))) * Uᴴ) * R := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul R hR, Matrix.one_mul, hU.conjTranspose_mul_self,
          Matrix.mul_one, hDD, Matrix.mul_one, hUU, Matrix.mul_one, Matrix.nonsing_inv_mul R hR]
  rw [hinv, Matrix.trace_mul_cycle, ← Matrix.mul_inv_rev, hRR, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, map_sum,
    RCLike.re_mul_ofReal, mul_comm]

/-- **`tr A⁻¹` is strictly convex** on the positive definite matrices.
Port of `NLAlib.strictConvexOn_trace_inv`, there over `ℝ`.
Result: trace-inverse-convexity -/
theorem strictConvexOn_re_trace_inv :
    StrictConvexOn ℝ {A : Matrix n n 𝕜 | A.PosDef} fun A => RCLike.re A⁻¹.trace := by
  refine ⟨convex_setOf_posDef, fun A hA B hB hAB a b ha hb hab => ?_⟩
  obtain ⟨w, d, hw, hd, hd1, htr⟩ := exists_re_trace_inv_smul_add_smul_eq hA hB
  have hA' := htr 1 0 fun i => by simp
  have hB' := htr 0 1 fun i => by simpa using (hd i).ne'
  simp only [one_smul, zero_smul, add_zero, zero_add, zero_mul, one_mul, inv_one] at hA' hB'
  change RCLike.re (a • A + b • B)⁻¹.trace < a • RCLike.re A⁻¹.trace + b • RCLike.re B⁻¹.trace
  rw [htr a b fun i => (add_pos ha (mul_pos hb (hd i))).ne', hA', hB', smul_eq_mul, smul_eq_mul,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 1 := by
    by_contra h
    exact hAB (hd1 fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  have hgap : ∀ j, 0 ≤ a + b * (d j)⁻¹ - (a + b * d j)⁻¹ := fun j => by
    rw [add_mul_inv_sub_inv ha hb hab (hd j)]
    exact div_nonneg (mul_nonneg (mul_pos ha hb).le (sq_nonneg _))
      (mul_pos (hd j) (add_pos ha (mul_pos hb (hd j)))).le
  have hgap' : 0 < a + b * (d i)⁻¹ - (a + b * d i)⁻¹ := by
    rw [add_mul_inv_sub_inv ha hb hab (hd i)]
    exact div_pos (mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi)))
      (mul_pos (hd i) (add_pos ha (mul_pos hb (hd i))))
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · nlinarith [mul_nonneg (hgap j) (hw j).le]
  · nlinarith [mul_pos hgap' (hw i)]

end NLAlib
