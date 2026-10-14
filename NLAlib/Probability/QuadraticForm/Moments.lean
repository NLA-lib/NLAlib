/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.Rademacher

/-!
# Second moments of quadratic forms

For a random vector `X` in `𝕜ⁿ` with independent coordinates of mean zero, `E |X i|² = 1`,
pseudo-variance `E X i² = s` and `E |X i|⁴ = m₄`, the quadratic form `Xᴴ A X` has mean `tr A`
(Hutchinson; `NLAlib.IsIsotropic.integral_quadForm`) and

`E |Xᴴ A X - tr A|² = ‖A‖_F² + |s|² re ⟨A, Aᵀ⟩_F + (m₄ - 2 - |s|²) ∑ |A i i|²`.

One statement covers real probes (`s = 1`: Gaussian `m₄ = 3`, Rademacher `m₄ = 1`) and complex
ones (`s = 0`: complex Gaussian `m₄ = 2`, Steinhaus `m₄ = 1`). For real symmetric `A` it is the
variance `2 ‖A‖_F² + (m₄ - 3) ∑ A i i²`, stated with its Gaussian and Rademacher cases.

## Main results

* `NLAlib.memLp_quadForm`: the quadratic form is square integrable.
* `NLAlib.integral_norm_quadForm_sub_trace_sq`: the second moment about the mean.
* `NLAlib.variance_quadForm_of_isHermitian`: the real symmetric case.
* `NLAlib.variance_quadForm_of_hasLaw_gaussianVector`,
  `NLAlib.variance_quadForm_of_hasLaw_rademacherVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {𝕜 : Type*} [RCLike 𝕜] {X : Ω → n → 𝕜}

private theorem memLp_star_mul {f g : Ω → 𝕜} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω => star (f ω) * g ω) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← two_mul,
      ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩
  exact hg.mul' hf.star

private theorem quadForm_eq_sum_smul (A : Matrix n n 𝕜) (x : n → 𝕜) :
    quadForm A x = ∑ i, ∑ j, A i j * (star (x i) * x j) := by
  rw [quadForm_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem quadForm_mul_star_quadForm (A : Matrix n n 𝕜) (x : n → 𝕜) :
    quadForm A x * star (quadForm A x) =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * star (A k l) * (star (x i) * x j * (x k * star (x l))) := by
  rw [quadForm_eq_sum_smul, star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [star_mul', star_star]
  ring

/-- The monomial `conj (x i) x j x k conj (x l)` as a product over coordinates. -/
private theorem star_mul_mul_mul_star_eq_prod [DecidableEq n] (x : n → 𝕜) (i j k l : n) :
    star (x i) * x j * (x k * star (x l)) =
      ∏ m, (star (x m) ^ ((if m = i then 1 else 0) + (if m = l then 1 else 0)) *
        x m ^ ((if m = j then 1 else 0) + (if m = k then 1 else 0))) := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true]
  ring

omit [Fintype n] in
private theorem integrable_star_mul_mul_mul_star (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ)
    (i j k l : n) : Integrable (fun ω => star (X ω i) * X ω j * (X ω k * star (X ω l))) μ := by
  have h := memLp_star_mul (hL4 l) (hL4 k)
  simp only [mul_comm (star (X _ l))] at h
  exact (memLp_star_mul (hL4 i) (hL4 j)).integrable_mul h

/-- The product of one-coordinate moments behind the fourth mixed moment, from the table of
moments `g m a b = E [conj (X m) ^ a * X m ^ b]`. -/
private theorem prod_moments_eq [DecidableEq n] (g : n → ℕ → ℕ → 𝕜) {s : 𝕜} {m₄ : ℝ}
    (e00 : ∀ m, g m 0 0 = 1) (e10 : ∀ m, g m 1 0 = 0) (e01 : ∀ m, g m 0 1 = 0)
    (e11 : ∀ m, g m 1 1 = 1) (e20 : ∀ m, g m 2 0 = star s) (e02 : ∀ m, g m 0 2 = s)
    (e22 : ∀ m, g m 2 2 = m₄) (i j k l : n) :
    ∏ m, g m ((if m = i then 1 else 0) + (if m = l then 1 else 0))
        ((if m = j then 1 else 0) + (if m = k then 1 else 0)) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        ((‖s‖ ^ 2 : ℝ) : 𝕜) * ((if i = l then 1 else 0) * (if j = k then 1 else 0)) +
        ((m₄ - 2 - ‖s‖ ^ 2 : ℝ) : 𝕜) *
          ((if i = j then 1 else 0) * (if i = k then 1 else 0) * (if i = l then 1 else 0)) := by
  have hss : star s * s = ((‖s‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k
        rw [Finset.prod_eq_single i (fun m _ hm => by simp only [hm, if_false, e00])
          (by simp)]
        simp only [if_true, Nat.reduceAdd, e22, mul_one]
        push_cast
        ring
      · rw [Finset.prod_eq_mul i k hik (fun m _ hm => by simp only [hm.1, hm.2, if_false, e00])
          (by simp) (by simp)]
        simp only [hik, Ne.symm hik, if_true, if_false, add_zero, zero_add, e11]
        ring
    · by_cases hik : i = k
      · subst k
        rw [Finset.prod_eq_zero (Finset.mem_univ l)
          (by simp only [Ne.symm hkl, if_true, if_false, add_zero, zero_add, e10])]
        simp only [hkl, if_true, if_false]
        ring
      · rw [Finset.prod_eq_zero (Finset.mem_univ k)
          (by simp only [hkl, Ne.symm hik, if_true, if_false, add_zero, zero_add, e01])]
        simp only [hkl, hik, if_true, if_false]
        ring
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        rw [Finset.prod_eq_mul i j hij (fun m _ hm => by simp only [hm.1, hm.2, if_false, e00])
          (by simp) (by simp)]
        simp only [hij, Ne.symm hij, if_true, if_false, add_zero, zero_add, e11]
        ring
      · rw [Finset.prod_eq_zero (Finset.mem_univ j)
          (by simp only [hjl, Ne.symm hij, if_true, if_false, add_zero, e01])]
        simp only [hij, Ne.symm hij, hjl, if_true, if_false]
        ring
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          rw [Finset.prod_eq_mul i j hij (fun m _ hm => by simp only [hm.1, hm.2, if_false, e00])
            (by simp) (by simp)]
          simp only [hij, Ne.symm hij, if_true, if_false, add_zero, Nat.reduceAdd, e20, e02, hss]
          ring
        · rw [Finset.prod_eq_zero (Finset.mem_univ j)
            (by simp only [hjk, Ne.symm hij, if_true, if_false, add_zero, e01])]
          simp only [hij, hjk, hik, if_true, if_false]
          ring
      · rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (by simp only [hij, hik, hil, if_true, if_false, add_zero, e10])]
        simp only [hij, hik, hil, if_false]
        ring

omit [Fintype n] in
/-- The fourth mixed moment `E [conj (X i) X j X k conj (X l)]` of independent coordinates. -/
private theorem integral_star_mul_mul_mul_star [Finite n] [DecidableEq n]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ)
    (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0) (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) {s : 𝕜}
    (hs : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = s) {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄)
    (i j k l : n) :
    ∫ ω, star (X ω i) * X ω j * (X ω k * star (X ω l)) ∂μ =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        ((‖s‖ ^ 2 : ℝ) : 𝕜) * ((if i = l then 1 else 0) * (if j = k then 1 else 0)) +
        ((m₄ - 2 - ‖s‖ ^ 2 : ℝ) : 𝕜) *
          ((if i = j then 1 else 0) * (if i = k then 1 else 0) * (if i = l then 1 else 0)) := by
  have := hind.isProbabilityMeasure
  have := Fintype.ofFinite n
  have hnorm (z : 𝕜) : star z * z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  have hprod := hind.integral_fun_prod_comp
    (f := fun m z => star z ^ ((if m = i then 1 else 0) + (if m = l then 1 else 0)) *
      z ^ ((if m = j then 1 else 0) + (if m = k then 1 else 0)))
    (fun m => (hL4 m).aestronglyMeasurable.aemeasurable)
    (fun m => (by fun_prop : Continuous fun z : 𝕜 => _).aestronglyMeasurable)
  simp only [star_mul_mul_mul_star_eq_prod (X _) i j k l]
  refine hprod.trans (prod_moments_eq (fun m a b => ∫ ω, star (X ω m) ^ a * X ω m ^ b ∂μ)
    (fun m => ?_) (fun m => ?_) (fun m => ?_) (fun m => ?_) (fun m => ?_) (fun m => ?_)
    (fun m => ?_) i j k l)
  · simp only [pow_zero, mul_one, integral_const, probReal_univ, one_smul]
  · simp only [pow_one, pow_zero, mul_one, RCLike.star_def, integral_conj, hmean, map_zero]
  · simp only [pow_one, pow_zero, one_mul, hmean]
  · simp only [pow_one, hnorm, integral_ofReal, hvar, RCLike.ofReal_one]
  · simp only [pow_zero, mul_one, RCLike.star_def, ← map_pow, integral_conj, hs]
  · simp only [pow_zero, one_mul, hs]
  · have h (z : 𝕜) : star z ^ 2 * z ^ 2 = ((‖z‖ ^ 4 : ℝ) : 𝕜) := by
      rw [← mul_pow, hnorm]
      push_cast
      ring
    simp only [h, integral_ofReal, hm₄]

/-- The index contraction of the fourth mixed moments. -/
private theorem sum_contraction [DecidableEq n] (A : Matrix n n 𝕜) (c d : 𝕜) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * star (A k l) *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        c * ((if i = l then 1 else 0) * (if j = k then 1 else 0)) +
        d * ((if i = j then 1 else 0) * (if i = k then 1 else 0) * (if i = l then 1 else 0))) =
      A.trace * star A.trace + ∑ i, ∑ j, A i j * star (A i j) +
        c * ∑ i, ∑ j, A i j * star (A j i) + d * ∑ i, A i i * star (A i i) := by
  simp only [mul_add, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp only [RCLike.star_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_ite_irrel, Finset.sum_const_zero, Matrix.trace, Matrix.diag_apply,
      star_sum, Finset.sum_mul_sum]
  · simp only [RCLike.star_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  · simp only [RCLike.star_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The second moment `E |Xᴴ A X|²` as an index contraction. -/
private theorem integral_quadForm_mul_star (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) {s : 𝕜} (hs : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = s)
    {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄) (A : Matrix n n 𝕜) :
    ∫ ω, quadForm A (X ω) * star (quadForm A (X ω)) ∂μ =
      A.trace * star A.trace + ∑ i, ∑ j, A i j * star (A i j) +
        ((‖s‖ ^ 2 : ℝ) : 𝕜) * ∑ i, ∑ j, A i j * star (A j i) +
        ((m₄ - 2 - ‖s‖ ^ 2 : ℝ) : 𝕜) * ∑ i, A i i * star (A i i) := by
  classical
  have hP := integrable_star_mul_mul_mul_star hL4
  simp only [quadForm_mul_star_quadForm]
  rw [← sum_contraction]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hP i j k l).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => (hP i j k l).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hP i j k l).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hP i j k l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_star_mul_mul_mul_star hind hL4 hmean hvar hs hm₄]

/-- A quadratic form in a vector with fourth moments is square integrable. -/
theorem memLp_quadForm (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (A : Matrix n n 𝕜) :
    MemLp (fun ω => quadForm A (X ω)) 2 μ := by
  simp only [quadForm_eq_sum_smul]
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (memLp_star_mul (hL4 i) (hL4 j)).const_mul (A i j)

/-- **The second moment of a quadratic form** about its mean `tr A`, for independent
coordinates with mean zero, `E |X i|² = 1`, `E X i² = s` and `E |X i|⁴ = m₄`. -/
theorem integral_norm_quadForm_sub_trace_sq (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) {s : 𝕜} (hs : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = s)
    {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄) (A : Matrix n n 𝕜) :
    ∫ ω, ‖quadForm A (X ω) - A.trace‖ ^ 2 ∂μ =
      frobNorm A ^ 2 + ‖s‖ ^ 2 * frobInner A Aᵀ + (m₄ - 2 - ‖s‖ ^ 2) * ∑ i, ‖A i i‖ ^ 2 := by
  classical
  have := hind.isProbabilityMeasure
  have hL2 (i : n) : MemLp (fun ω => X ω i) 2 μ := (hL4 i).mono_exponent (by norm_num)
  have hmeanq := (IsIsotropic.of_iIndepFun hind hL2 hmean hvar).integral_quadForm A
  have hq2 := memLp_quadForm hL4 A
  have hq1 : Integrable (fun ω => quadForm A (X ω)) μ := hq2.integrable one_le_two
  have hq1' : Integrable (fun ω => star (quadForm A (X ω))) μ := hq2.star.integrable one_le_two
  have hqq : Integrable (fun ω => quadForm A (X ω) * star (quadForm A (X ω))) μ :=
    hq2.integrable_mul hq2.star
  have hE := integral_quadForm_mul_star hind hL4 hmean hvar hs hm₄ A
  have hnorm (z : 𝕜) : ((‖z‖ ^ 2 : ℝ) : 𝕜) = z * star z := by
    rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
  have hc : ∫ ω, (quadForm A (X ω) - A.trace) * star (quadForm A (X ω) - A.trace) ∂μ =
      ∫ ω, quadForm A (X ω) * star (quadForm A (X ω)) ∂μ - A.trace * star A.trace := by
    have h (ω : Ω) : (quadForm A (X ω) - A.trace) * star (quadForm A (X ω) - A.trace) =
        quadForm A (X ω) * star (quadForm A (X ω)) - quadForm A (X ω) * star A.trace -
          A.trace * star (quadForm A (X ω)) + A.trace * star A.trace := by
      rw [star_sub]
      ring
    have h1 : Integrable (fun ω => quadForm A (X ω) * star (quadForm A (X ω)) -
        quadForm A (X ω) * star A.trace) μ := hqq.sub (hq1.mul_const _)
    have h2 : Integrable (fun ω => quadForm A (X ω) * star (quadForm A (X ω)) -
        quadForm A (X ω) * star A.trace - A.trace * star (quadForm A (X ω))) μ :=
      h1.sub (hq1'.const_mul _)
    simp only [h]
    rw [integral_add h2 (integrable_const _), integral_sub h1 (hq1'.const_mul _),
      integral_sub hqq (hq1.mul_const _), integral_mul_const, integral_const_mul,
      RCLike.star_def, integral_conj, hmeanq, integral_const, probReal_univ, one_smul]
    ring
  have hre : ∫ ω, ‖quadForm A (X ω) - A.trace‖ ^ 2 ∂μ =
      RCLike.re (∫ ω, (quadForm A (X ω) - A.trace) * star (quadForm A (X ω) - A.trace) ∂μ) := by
    simp only [← hnorm, integral_ofReal, RCLike.ofReal_re]
  have e1 : RCLike.re (∑ i, ∑ j, A i j * star (A i j)) = frobNorm A ^ 2 := by
    simp only [frobNorm_sq_eq_sum, map_sum, ← hnorm, RCLike.ofReal_re]
  have e2 : RCLike.re (∑ i, ∑ j, A i j * star (A j i)) = frobInner A Aᵀ := by
    simp only [frobInner_eq_sum, map_sum, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : A i j * star (A j i) = star (star (A i j) * A j i) := by
      rw [star_mul', star_star, mul_comm]
    rw [h, RCLike.star_def, RCLike.conj_re]
  have e3 : RCLike.re (∑ i, A i i * star (A i i)) = ∑ i, ‖A i i‖ ^ 2 := by
    simp only [map_sum, ← hnorm, RCLike.ofReal_re]
  rw [hre, hc, hE, show ∀ x y z w : 𝕜, x + y + z + w - x = y + z + w from fun _ _ _ _ => by ring,
    map_add, map_add, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul, e1, e2, e3]

/-- The variance of a real quadratic form with symmetric `A`:
`Var (Xᵀ A X) = 2 ‖A‖_F² + (m₄ - 3) ∑ A i i²`. -/
theorem variance_quadForm_of_isHermitian {X : Ω → n → ℝ} (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = 1) {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, X ω i ^ 4 ∂μ = m₄)
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ =
      2 * frobNorm A ^ 2 + (m₄ - 3) * ∑ i, A i i ^ 2 := by
  classical
  have := hind.isProbabilityMeasure
  have hvar' (i : n) : ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1 := by
    simp only [Real.norm_eq_abs, sq_abs, hvar]
  have hm₄' (i : n) : ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄ := by
    simp only [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩, hm₄]
  have hL2 (i : n) : MemLp (fun ω => X ω i) 2 μ := (hL4 i).mono_exponent (by norm_num)
  have hmeanq := (IsIsotropic.of_iIndepFun hind hL2 hmean hvar').integral_quadForm A
  have h := integral_norm_quadForm_sub_trace_sq hind hL4 hmean hvar' hvar hm₄' A
  have hT : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hA
  simp only [Real.norm_eq_abs, sq_abs, abs_one, one_pow, one_mul, hT, frobInner_self] at h
  rw [variance_eq_integral (memLp_quadForm hL4 A).aestronglyMeasurable.aemeasurable, hmeanq, h]
  ring

/-- Hutchinson's variance with a Gaussian probe: `Var (Xᵀ A X) = 2 ‖A‖_F²` for symmetric `A`. -/
theorem variance_quadForm_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ = 2 * frobNorm A ^ 2 := by
  have hL4 (i : n) : MemLp (fun ω => X ω i) 4 μ :=
    ((hX.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      (memLp_id_gaussianReal' 4 (by simp))
  have hvar (i : n) : ∫ ω, X ω i ^ 2 ∂μ = 1 := by
    rw [integral_sq_of_hasLaw_gaussianReal (hX.eval i), NNReal.coe_one]
  have hm₄ (i : n) : ∫ ω, X ω i ^ 4 ∂μ = 3 := by
    rw [integral_pow_four_of_hasLaw_gaussianReal (hX.eval i), NNReal.coe_one]
    norm_num
  rw [variance_quadForm_of_isHermitian hX.iIndepFun_eval hL4
    (fun i => integral_of_hasLaw_gaussianReal (hX.eval i)) hvar hm₄ hA]
  ring

/-- Hutchinson's variance with a Rademacher probe:
`Var (Xᵀ A X) = 2 (‖A‖_F² - ∑ A i i²)` for symmetric `A`. -/
theorem variance_quadForm_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ = 2 * (frobNorm A ^ 2 - ∑ i, A i i ^ 2) := by
  have hL4 (i : n) : MemLp (fun ω => X ω i) 4 μ :=
    ((hX.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      ((integrable_norm_rpow_iff aestronglyMeasurable_id (by norm_num) (by norm_num)).1
        (integrable_rademacherMeasure _))
  rw [variance_quadForm_of_isHermitian hX.iIndepFun_eval hL4
    (fun i => integral_of_hasLaw_rademacherMeasure (hX.eval i))
    (fun i => integral_sq_of_hasLaw_rademacherMeasure (hX.eval i))
    (fun i => integral_pow_four_of_hasLaw_rademacherMeasure (hX.eval i)) hA]
  ring

end NLAlib
