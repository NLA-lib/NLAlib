/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import NLAlib.Probability.Isotropic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Standard Gaussian vectors

`NLAlib.gaussianVector n` is the law of a vector in `ℝⁿ` with independent standard Gaussian
coordinates, the product `Measure.pi fun _ => gaussianReal 0 1`. It is an `abbrev`, so the
product-law lemmas of `NLAlib/Probability/Law.lean` apply to it directly; `rw` with a lemma
stated for one spelling does not fire on the other, so use `simp only` or `exact` across the two.
Its image in `EuclideanSpace ℝ n` is Mathlib's `stdGaussian`
(`ProbabilityTheory.map_pi_eq_stdGaussian`), and it is an `IsGaussian` measure, so Mathlib's
`HasGaussianLaw` API applies.

This file proves, for a random variable with a centred Gaussian law, the interfaces and moments
the probability layers use: the sub-Gaussian proxy, the second and fourth moments, isotropy of a
standard Gaussian vector and the law of its linear forms. The laws are real; a complex Gaussian
law will be a separate definition (`docs/design/Probability-P2.md` §7).

## Main definitions

* `NLAlib.gaussianVector n`.

## Main results

* `NLAlib.hasSubgaussianMGF_of_hasLaw_gaussianReal`: a centred Gaussian of variance `v` has proxy
  `v`.
* `NLAlib.integral_pow_four_of_hasLaw_gaussianReal`: `E X⁴ = 3 v²`.
* `NLAlib.isIsotropic_of_hasLaw_gaussianVector`.
* `NLAlib.hasLaw_dotProduct_of_hasLaw_gaussianVector`: `u ⬝ᵥ X` has law `N(0, ‖u‖²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- The standard Gaussian law on `ℝⁿ`: independent coordinates, each `N(0, 1)`. -/
noncomputable abbrev gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => gaussianReal 0 1

/-- The standard Gaussian vector is a Gaussian measure. -/
instance isGaussian_gaussianVector : IsGaussian (gaussianVector n) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ fun _ : n => ℝ
  have hc : ⇑L ∘ WithLp.toLp 2 = id := rfl
  have h : gaussianVector n = (stdGaussian (EuclideanSpace ℝ n)).map L := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop), hc,
      Measure.map_id]
  rw [h]
  infer_instance

/-- A centred Gaussian of variance `v` is sub-Gaussian with proxy `v`. -/
theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simpa only [id_eq] using integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
  · simp only [mgf_id_gaussianReal, zero_mul, zero_add, le_refl]

/-- A centred Gaussian has mean zero. -/
theorem integral_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ∂μ = 0 := by
  rw [hX.integral_eq, integral_id_gaussianReal]

/-- The second moment of a centred Gaussian is its variance. -/
theorem integral_sq_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 2 ∂μ = v := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  rw [← h]
  exact hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)

/-- The fourth moment of the standard Gaussian. -/
private theorem integral_pow_four_gaussianReal_one :
    ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    have e4 : |x| ^ (4:ℝ) = x ^ 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_abs]
      exact abs_of_nonneg (by positivity)
    have e2 : |x| ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e4, e2]; ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ =>
      (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((4 + 1) / 2) = 3 / 4 * √Real.pi := by
    have := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at this
    rw [show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, this]; ring
  rw [hg]
  have hb : (1/2 : ℝ) ^ (-(4 + 1) / 2 : ℝ) = 4 * √2 := by
    rw [show (-(4 + 1) / 2 : ℝ) = -(2 + 1/2) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_add (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [hb, Real.sqrt_mul (by norm_num)]
  have : (0:ℝ) < √2 := by positivity
  have : (0:ℝ) < √Real.pi := by positivity
  field_simp

private theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (√(v : ℝ) * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp only [NNReal.coe_mk, Real.sq_sqrt v.coe_nonneg]
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  rw [integral_const_mul, integral_pow_four_gaussianReal_one,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt v.coe_nonneg]
  ring

/-- The fourth moment of a centred Gaussian of variance `v` is `3 v²`. -/
theorem integral_pow_four_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 4 ∂μ = 3 * (v : ℝ) ^ 2 := by
  rw [← integral_pow_four_gaussianReal v]
  exact hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)

/-- A standard Gaussian vector is isotropic. -/
theorem isIsotropic_of_hasLaw_gaussianVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsIsotropic X μ := by
  refine IsIsotropic.of_iIndepFun hX.iIndepFun_eval (fun i => ?_)
    (fun i => integral_of_hasLaw_gaussianReal (hX.eval i)) (fun i => ?_)
  · exact ((hX.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      (memLp_id_gaussianReal' 2 (by simp))
  · simp only [Real.norm_eq_abs, sq_abs]
    rw [integral_sq_of_hasLaw_gaussianReal (hX.eval i), NNReal.coe_one]

private theorem hasLaw_dotProduct_gaussianVector (u : n → ℝ) :
    HasLaw (fun z => u ⬝ᵥ z) (gaussianReal 0 (‖WithLp.toLp 2 u‖₊ ^ 2)) (gaussianVector n) := by
  let w : EuclideanSpace ℝ n := WithLp.toLp 2 u
  let L : StrongDual ℝ (EuclideanSpace ℝ n) := innerSL ℝ w
  have hfun : (fun z : n → ℝ => u ⬝ᵥ z) = L ∘ (WithLp.toLp 2) := by
    funext z
    simp [L, w, PiLp.inner_apply, dotProduct, mul_comm]
  refine ⟨(by rw [hfun]; fun_prop : Measurable (fun z : n → ℝ => u ⬝ᵥ z)).aemeasurable, ?_⟩
  rw [hfun, ← Measure.map_map L.continuous.measurable (by fun_prop), map_pi_eq_stdGaussian,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  congr 1
  ext
  simp [L, w, innerSL_apply_norm]

/-- A linear form `u ⬝ᵥ X` of a standard Gaussian vector is a centred Gaussian of variance
`‖u‖²`. -/
theorem hasLaw_dotProduct_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) (u : n → ℝ) :
    HasLaw (fun ω => u ⬝ᵥ X ω) (gaussianReal 0 (‖WithLp.toLp 2 u‖₊ ^ 2)) μ := by
  exact (hasLaw_dotProduct_gaussianVector u).comp hX

end NLAlib
