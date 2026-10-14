/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Gaussian

/-!
# The squared norm of a standard Gaussian vector

The squared norm of a standard Gaussian vector in `ℝⁿ` is `χ²_n`. This file gives its Laplace
transform and the Laurent–Massart lower tail. The upper tail is the sub-Gaussian-vector bound
`NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` at proxy `1`, which is Laurent and
Massart's exactly.

## Main results

* `NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`: `E exp (θ‖X‖²) = (1 - 2θ)^{-n/2}`.
* `NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector`:
  `P(‖X‖² ≤ n - 2√(n t)) ≤ e^{-t}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ}

private theorem integral_exp_mul_sq_gaussianReal {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ y, rexp (θ * y ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < 1 - 2 * θ := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h (x : ℝ) : (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (θ * x ^ 2)
      = (√(2 * π))⁻¹ * rexp (-((1 - 2 * θ) / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp only [h]
  rw [integral_const_mul, integral_gaussian,
    show π / ((1 - 2 * θ) / 2) = (2 * π) / (1 - 2 * θ) by field_simp,
    Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * π) ≠ 0 := by positivity
  field_simp

private theorem integral_exp_mul_norm_sq_gaussianVector {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ x, rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2) ∂(gaussianVector n) =
      (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have h (x : n → ℝ) : rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2) = ∏ i, rexp (θ * x i ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp only [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => rexp (θ * y ^ 2))]
  simp only [integral_exp_mul_sq_gaussianReal hθ, Finset.prod_const, Finset.card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  congr 1
  ring

/-- The Laplace transform of `χ²_n`: `E exp (θ ‖X‖²) = (1 - 2θ)^{-n/2}` for `θ < 1/2`. -/
theorem integral_exp_mul_norm_sq_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ = (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  rw [← integral_exp_mul_norm_sq_gaussianVector hθ]
  exact hX.integral_comp (f := fun x => rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2)) (by fun_prop)

private theorem log_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (1 - u) ≤ -u - u ^ 2 / 2 := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this
  linarith

/-- The Chernoff bound for the lower tail with the exact Laplace transform. -/
private theorem measureReal_norm_sq_le_le_exp_mul_rpow (hX : HasLaw X (gaussianVector n) μ)
    (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ c} ≤
      rexp (s * c) * (1 + 2 * s) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hlap := integral_exp_mul_norm_sq_of_hasLaw_gaussianVector hX (θ := -s) (by linarith)
  rw [show 1 - 2 * -s = 1 + 2 * s by ring] at hlap
  have hint : Integrable (fun ω => rexp (-s * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (by rw [hlap]; exact (Real.rpow_pos_of_pos (by linarith) _).ne')
  have h := measure_le_le_exp_mul_mgf (X := fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) c
    (neg_nonpos.2 hs) hint
  rwa [mgf, hlap, neg_neg] at h

/-- **The lower tail of `χ²_n`** (Laurent and Massart 2000, Lemma 1):
`P(‖X‖² ≤ n - 2√(n t)) ≤ e^{-t}`. The dimension must be positive: for `n = 0` the event is
everything.
Result: laurent-massart -/
theorem measureReal_norm_sq_le_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ Fintype.card n - 2 * √(Fintype.card n * t)} ≤
      rexp (-t) := by
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  set N : ℝ := (Fintype.card n : ℝ)
  set u := 2 * √(t / N) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = 4 * (t / N) := by
    rw [hu_def, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have ht' : t = N * u ^ 2 / 4 := by rw [hu2]; field_simp
  have hc : N - 2 * √(N * t) = N * (1 - u) := by
    rw [show N * t = N ^ 2 * (t / N) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hN.le, hu_def]
    ring
  rw [hc]
  rcases lt_or_ge u 1 with hu1 | hu1
  · have hs : 0 ≤ u / (2 * (1 - u)) := div_nonneg hu0 (by linarith)
    refine (measureReal_norm_sq_le_le_exp_mul_rpow hX _ hs).trans ?_
    have h1u : 0 < 1 - u := by linarith
    rw [show 1 + 2 * (u / (2 * (1 - u))) = (1 - u)⁻¹ by field_simp; ring,
      Real.inv_rpow h1u.le, ← Real.rpow_neg h1u.le, neg_neg, Real.rpow_def_of_pos h1u,
      ← Real.exp_add, Real.exp_le_exp, ht']
    have hlog := log_one_sub_le hu0 hu1
    have : u / (2 * (1 - u)) * (N * (1 - u)) = N * u / 2 := by field_simp
    rw [this]
    nlinarith
  · have hs : 0 ≤ (rexp (u ^ 2 / 2) - 1) / 2 := by
      have := Real.one_le_exp (by positivity : 0 ≤ u ^ 2 / 2)
      linarith
    refine (measureReal_norm_sq_le_le_exp_mul_rpow hX _ hs).trans ?_
    rw [show 1 + 2 * ((rexp (u ^ 2 / 2) - 1) / 2) = rexp (u ^ 2 / 2) by ring, ← Real.exp_mul,
      ← Real.exp_add, Real.exp_le_exp, ht']
    have : (rexp (u ^ 2 / 2) - 1) / 2 * (N * (1 - u)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs (mul_nonpos_of_nonneg_of_nonpos hN.le (by linarith))
    nlinarith

end NLAlib
