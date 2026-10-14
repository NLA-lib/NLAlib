/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.SubGaussian.Moments

/-!
# Squares of sub-Gaussian random variables

The exponential square moment `E exp (θ X²)` of a sub-Gaussian variable, and the fact that its
centred square `X² - E X²` is sub-exponential, which is what Bernstein's inequality and the
diagonal part of the Hanson–Wright inequality consume.

The constants of the centred square, `32` and `4`, are the literature's and are written in the
statement (`CONTRIBUTING.md` §5.2, "Numerical bounds").

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le`:
  `E exp (θ X²) ≤ (1 - 2θc)^{-1/2}`.
* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`: the centred square
  is sub-exponential with variance proxy `32 c²` and scale `4 c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Gaussian linearisation -/

private lemma lintegral_exp_mul_sq_gaussianReal {a : ℝ} (ha : 2 * a < 1) :
    ∫⁻ g, ENNReal.ofReal (rexp (a * g ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (1 / √(1 - 2 * a)) := by
  have hb : 0 < 1 / 2 - a := by linarith
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF _ _).aemeasurable
      (by fun_prop)]
  have hpt : ∀ x : ℝ, gaussianPDF 0 1 x * ENNReal.ofReal (rexp (a * x ^ 2)) =
      ENNReal.ofReal ((√(2 * π))⁻¹ * rexp (-(1 / 2 - a) * x ^ 2)) := by
    intro x
    rw [gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, mul_assoc, ← exp_add]
    ring_nf
  simp only [Pi.mul_apply, hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun _ => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have h1 : π / (1 / 2 - a) = 2 * π / (1 - 2 * a) := by field_simp
  have h2 : 0 < 1 - 2 * a := by linarith
  rw [h1, sqrt_div' _ h2.le]
  have : 0 < √(2 * π) := by positivity
  have : 0 < √(1 - 2 * a) := sqrt_pos.mpr h2
  field_simp

private lemma lintegral_exp_mul_gaussianReal (t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (rexp (t * g)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (rexp (t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
    (ae_of_all _ fun _ => (exp_pos _).le)]
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id, zero_mul, NNReal.coe_one, one_mul, zero_add] at this
  rw [this]

private lemma lintegral_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2)) ∂μ ≤ ENNReal.ofReal (1 / √(1 - 2 * θ * c)) := by
  have := h.isFiniteMeasure
  set s := √(2 * θ)
  have hs : s ^ 2 = 2 * θ := sq_sqrt (by linarith)
  have hpt : ∀ x : ℝ, ENNReal.ofReal (rexp (θ * x ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (rexp (s * x * g)) ∂(gaussianReal 0 1) := by
    intro x
    rw [lintegral_exp_mul_gaussianReal, mul_pow, hs]
    ring_nf
  have hX := h.aemeasurable
  have hmeas : AEMeasurable (Function.uncurry fun (ω : Ω) (g : ℝ) =>
      ENNReal.ofReal (rexp (s * X ω * g))) (μ.prod (gaussianReal 0 1)) := by
    have h1 : AEMeasurable (fun p : Ω × ℝ => X p.1) (μ.prod (gaussianReal 0 1)) := hX.comp_fst
    have h2 : AEMeasurable (fun p : Ω × ℝ => p.2) (μ.prod (gaussianReal 0 1)) :=
      measurable_snd.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_exp.comp_aemeasurable ((h1.const_mul s).mul h2))
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (rexp (s * X ω * g)) ∂(gaussianReal 0 1) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (rexp (s * X ω * g)) ∂μ ∂(gaussianReal 0 1) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ g, ENNReal.ofReal (rexp ((θ * c) * g ^ 2)) ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun g => ?_
        have hint := h.integrable_exp_mul (s * g)
        have heq : ∫⁻ ω, ENNReal.ofReal (rexp (s * X ω * g)) ∂μ =
            ENNReal.ofReal (mgf X μ (s * g)) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (exp_pos _).le)]
          congr 1 with ω
          ring_nf
        rw [heq]
        refine ENNReal.ofReal_le_ofReal ((h.mgf_le (s * g)).trans (exp_le_exp.mpr ?_))
        rw [mul_pow, hs]
        ring_nf
        rfl
    _ = ENNReal.ofReal (1 / √(1 - 2 * θ * c)) := by
        rw [lintegral_exp_mul_sq_gaussianReal (by linarith)]
        ring_nf

/-- `exp (θ X²)` is integrable for a sub-Gaussian `X` when `2 θ c < 1` (in particular for every
`θ ≤ 0`). -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul_sq
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 2 * θ * c < 1) :
    Integrable (fun ω => rexp (θ * X ω ^ 2)) μ := by
  have := h.isFiniteMeasure
  have hX := h.aemeasurable
  have hm : AEStronglyMeasurable (fun ω => rexp (θ * X ω ^ 2)) μ :=
    (measurable_exp.comp_aemeasurable ((hX.pow_const 2).const_mul θ)).aestronglyMeasurable
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · refine Integrable.mono' (integrable_const 1) hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hθ0 (sq_nonneg _)
  · refine ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (exp_pos _).le)).mpr ?_⟩
    exact (lintegral_exp_mul_sq_le h hθ0.le hθ).trans_lt ENNReal.ofReal_lt_top

/-- `E exp (θ X²) ≤ (1 - 2θc)^{-1/2}` for a sub-Gaussian `X` and `0 ≤ θ < 1 / (2c)`: the value
for a centred Gaussian of variance `c`, by Gaussian linearisation
`exp (θ x²) = E_g exp (√(2θ) g x)`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * X ω ^ 2) ∂μ ≤ 1 / √(1 - 2 * θ * c) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (exp_pos _).le)
    (h.integrable_exp_mul_sq hθ).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_exp_mul_sq_le h hθ0 hθ)

/-! ### Moments and the series of `exp (θ X²)` -/

private lemma integral_pow_two_mul_le (h : HasSubgaussianMGF X c μ) (k : ℕ) :
    ∫ ω, X ω ^ (2 * (k + 1)) ∂μ ≤ 2 * (k + 1)! * (2 * c) ^ (k + 1) := by
  have := h.integral_abs_rpow_le (p := 2 * ((k : ℝ) + 1)) (by positivity)
  have hcast : ((2 * (k + 1) : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have hpt : ∀ ω, |X ω| ^ (2 * ((k : ℝ) + 1)) = X ω ^ (2 * (k + 1)) := by
    intro ω
    rw [← hcast, rpow_natCast, pow_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
  have hhalf : 2 * ((k : ℝ) + 1) / 2 = (k : ℝ) + 1 := by ring
  simp only [hpt, hhalf, Real.Gamma_nat_eq_factorial] at this
  rw [← Nat.cast_succ, rpow_natCast] at this
  refine this.trans_eq ?_
  rw [Nat.factorial_succ]
  push_cast [Nat.succ_eq_add_one]
  ring

private lemma integrable_pow (h : HasSubgaussianMGF X c μ) (n : ℕ) :
    Integrable (fun ω => X ω ^ n) μ :=
  integrable_pow_of_integrable_exp_mul one_ne_zero (h.integrable_exp_mul 1)
    (h.integrable_exp_mul (-1)) n

private lemma integral_exp_mul_sq_sub_le (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫ ω, (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) ∂μ ≤
      2 * (2 * θ * c) ^ 2 / (1 - 2 * θ * c) := by
  have := h.isFiniteMeasure
  set u := 2 * θ * c with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 0 < 1 - u := by linarith
  set g : ℕ → Ω → ℝ := fun n ω => (θ * X ω ^ 2) ^ (n + 2) / (n + 2)! with hg
  have hg0 : ∀ n ω, 0 ≤ g n ω := fun n ω => by positivity
  have hsum : ∀ ω, HasSum (fun n => g n ω) (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) := by
    intro ω
    have := NormedSpace.expSeries_div_hasSum_exp (θ * X ω ^ 2)
    rw [← exp_eq_exp_ℝ, ← hasSum_nat_add_iff' 2] at this
    simpa [Finset.sum_range_succ, sub_sub] using this
  have hgeq : ∀ n, g n = fun ω => θ ^ (n + 2) / (n + 2)! * X ω ^ (2 * (n + 2)) := by
    intro n
    ext ω
    simp only [hg]
    rw [mul_pow, ← pow_mul]
    ring
  have hint : ∀ n, Integrable (g n) μ := fun n => by
    rw [hgeq]
    exact (integrable_pow h _).const_mul _
  have hle : ∀ n, ∫ ω, g n ω ∂μ ≤ 2 * u ^ (n + 2) := by
    intro n
    rw [hgeq, integral_const_mul]
    calc θ ^ (n + 2) / (n + 2)! * ∫ ω, X ω ^ (2 * (n + 2)) ∂μ
        ≤ θ ^ (n + 2) / (n + 2)! * (2 * (n + 2)! * (2 * c) ^ (n + 2)) := by
          gcongr
          exact integral_pow_two_mul_le h (n + 1)
      _ = 2 * u ^ (n + 2) := by
          rw [hu]
          field_simp
          ring
  have hgeom : (fun n : ℕ => 2 * u ^ (n + 2)) = fun n => 2 * u ^ 2 * u ^ n := by
    ext n
    ring
  have hsumm : Summable fun n : ℕ => 2 * u ^ (n + 2) := by
    rw [hgeom]
    exact (summable_geometric_of_lt_one hu0 (by linarith)).mul_left _
  have hφ0 : 0 ≤ᵐ[μ] fun ω => rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2 :=
    ae_of_all _ fun ω => (hsum ω).nonneg (hg0 · ω)
  have hφm : AEStronglyMeasurable (fun ω => rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) μ :=
    (((h.integrable_exp_mul_sq hθ).sub (integrable_const 1)).sub
      ((integrable_pow h 2).const_mul θ)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hφ0 hφm]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) ∂μ
      = ∫⁻ ω, ∑' n, ENNReal.ofReal (g n ω) ∂μ := by
        congr with ω
        rw [← (hsum ω).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (hg0 · ω) (hsum ω).summable]
    _ = ∑' n, ∫⁻ ω, ENNReal.ofReal (g n ω) ∂μ :=
        lintegral_tsum fun n => (hint n).aemeasurable.ennreal_ofReal
    _ ≤ ∑' n, ENNReal.ofReal (2 * u ^ (n + 2)) := ENNReal.tsum_le_tsum fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hg0 n))]
        exact ENNReal.ofReal_le_ofReal (hle n)
    _ = ENNReal.ofReal (∑' n, 2 * u ^ (n + 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
    _ = ENNReal.ofReal (2 * u ^ 2 / (1 - u)) := by
        rw [hgeom, tsum_mul_left, tsum_geometric_of_lt_one hu0 (by linarith), div_eq_mul_inv]

private lemma exp_neg_le_one_sub_add_sq {y : ℝ} (hy : 0 ≤ y) : rexp (-y) ≤ 1 - y + y ^ 2 := by
  rcases le_or_gt y 1 with hy1 | hy1
  · have := abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy]; exact hy1)
    rw [neg_sq] at this
    linarith [le_abs_self (rexp (-y) - 1 - -y)]
  · have : rexp (-y) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith

/-! ### The centred square -/

private lemma mgf_sq_sub_integral_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ)
    {l : ℝ} (hl : 4 * c * |l| < 1) :
    mgf (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ) μ l ≤ rexp (32 * c ^ 2 * l ^ 2 / 2) := by
  set m := ∫ ω', X ω' ^ 2 ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  have hl2 : 2 * l * c < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self l) hc, mul_nonneg hc (abs_nonneg l)]
  have hexp := h.integrable_exp_mul_sq hl2
  have hsq := integrable_pow h 2
  have hmgf : mgf (fun ω => X ω ^ 2 - m) μ l = rexp (-l * m) * ∫ ω, rexp (l * X ω ^ 2) ∂μ := by
    rw [mgf, ← integral_const_mul]
    congr 1 with ω
    rw [← exp_add]
    ring_nf
  rw [hmgf]
  rcases le_or_gt 0 l with hl0 | hl0
  · rw [abs_of_nonneg hl0] at hl
    set T := ∫ ω, (rexp (l * X ω ^ 2) - 1 - l * X ω ^ 2) ∂μ with hT
    have hI : ∫ ω, rexp (l * X ω ^ 2) ∂μ = T + 1 + l * m := by
      rw [hT, integral_sub (f := fun ω => rexp (l * X ω ^ 2) - 1)
        (hexp.sub (integrable_const 1)) (hsq.const_mul l),
        integral_sub hexp (integrable_const 1), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      ring
    have htail : T ≤ 4 * (2 * l * c) ^ 2 := by
      refine (integral_exp_mul_sq_sub_le h hl0 hl2).trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg (2 * l * c)]
    have hT0 : 0 ≤ T := integral_nonneg fun ω => by
      change (0 : ℝ) ≤ _
      linarith [add_one_le_exp (l * X ω ^ 2)]
    have hE : rexp (-l * m) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have hE' : rexp (-l * m) * (1 + l * m) ≤ 1 := by
      calc rexp (-l * m) * (1 + l * m) ≤ rexp (-l * m) * rexp (l * m) := by
            gcongr
            linarith [add_one_le_exp (l * m)]
        _ = 1 := by rw [← exp_add]; simp
    have hET : rexp (-l * m) * T ≤ T := mul_le_of_le_one_left hT0 hE
    rw [hI]
    calc rexp (-l * m) * (T + 1 + l * m) = rexp (-l * m) * (1 + l * m) + rexp (-l * m) * T := by
          ring
      _ ≤ 1 + 4 * (2 * l * c) ^ 2 := by linarith
      _ ≤ rexp (4 * (2 * l * c) ^ 2) := by linarith [add_one_le_exp (4 * (2 * l * c) ^ 2)]
      _ = rexp (32 * c ^ 2 * l ^ 2 / 2) := by ring_nf
  · have hX4 := integrable_pow h 4
    have hM4 := integral_pow_two_mul_le h 1
    norm_num [Nat.factorial] at hM4
    have hpt : ∀ ω, rexp (l * X ω ^ 2) ≤ 1 + l * X ω ^ 2 + l ^ 2 * X ω ^ 4 := by
      intro ω
      have := exp_neg_le_one_sub_add_sq (mul_nonneg (neg_nonneg.mpr hl0.le) (sq_nonneg (X ω)))
      calc rexp (l * X ω ^ 2) = rexp (-(-l * X ω ^ 2)) := by ring_nf
        _ ≤ 1 - -l * X ω ^ 2 + (-l * X ω ^ 2) ^ 2 := this
        _ = 1 + l * X ω ^ 2 + l ^ 2 * X ω ^ 4 := by ring
    have hI : ∫ ω, rexp (l * X ω ^ 2) ∂μ ≤ 1 + l * m + l ^ 2 * ∫ ω, X ω ^ 4 ∂μ := by
      refine (integral_mono hexp (g := fun ω => 1 + l * X ω ^ 2 + l ^ 2 * X ω ^ 4)
        (((integrable_const 1).add (hsq.const_mul l)).add (hX4.const_mul (l ^ 2))) hpt).trans_eq ?_
      rw [integral_add (f := fun ω => 1 + l * X ω ^ 2)
        ((integrable_const 1).add (hsq.const_mul l)) (hX4.const_mul (l ^ 2)),
        integral_add (integrable_const 1) (hsq.const_mul l), integral_const_mul,
        integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      rfl
    calc rexp (-l * m) * ∫ ω, rexp (l * X ω ^ 2) ∂μ
        ≤ rexp (-l * m) * (1 + l * m + l ^ 2 * ∫ ω, X ω ^ 4 ∂μ) := by gcongr
      _ ≤ rexp (-l * m) * rexp (l * m + l ^ 2 * ∫ ω, X ω ^ 4 ∂μ) := by
          gcongr
          linarith [add_one_le_exp (l * m + l ^ 2 * ∫ ω, X ω ^ 4 ∂μ)]
      _ = rexp (l ^ 2 * ∫ ω, X ω ^ 4 ∂μ) := by rw [← exp_add]; ring_nf
      _ ≤ rexp (32 * c ^ 2 * l ^ 2 / 2) := by
          gcongr
          nlinarith [sq_nonneg l]

/-- The centred square of a sub-Gaussian variable is sub-exponential: if `X` has proxy `c`, then
`X² - E X²` has variance proxy `32 c²` and scale `4 c`, the constants of Honorio and Jaakkola
(2014), reached by summing the series of `exp (θ X²)` against `E X^{2k} ≤ 2 k! (2c)^k`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral
    [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    HasSubexponentialMGF (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ) (32 * c ^ 2) (4 * c) μ := by
  have hb : ((4 * c : ℝ≥0) : ℝ) = 4 * c := by push_cast; ring
  have hv : ((32 * c ^ 2 : ℝ≥0) : ℝ) = 32 * c ^ 2 := by push_cast; ring
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · rw [hb] at hl
    have hl2 : 2 * l * c < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right (le_abs_self l) hc, mul_nonneg hc (abs_nonneg l)]
    refine ((h.integrable_exp_mul_sq hl2).const_mul
      (rexp (-l * ∫ ω', X ω' ^ 2 ∂μ))).congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [← exp_add]
    ring_nf
  · rw [hb] at hl
    rw [hv]
    exact mgf_sq_sub_integral_le h hl

end NLAlib
