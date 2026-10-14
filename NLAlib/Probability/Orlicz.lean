/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Orlicz conditions: the `ψ₂` and `ψ₁` bridges

Much of the literature (Vershynin's book in particular) states sub-Gaussian and sub-exponential
hypotheses through Orlicz conditions. Here they are constructor hypotheses of the library's
interfaces, never hypotheses of a concentration theorem: the `ψ₂` condition with squared scale
`K`, `E exp (X² / K) ≤ 2`, makes a centred `X` satisfy Mathlib's `HasSubgaussianMGF` with proxy
`C K`, and the `ψ₁` condition with scale `K`, `E exp (|X| / K) ≤ 2`, makes a centred `X` satisfy
`NLAlib.HasSubexponentialMGF` with proxy `C₁ K²` and scale `C₂ K`. Each condition is written as
two hypotheses, integrability and the integral bound; no Orlicz norm is defined. Vershynin's
`‖X‖_ψ₂ ≤ K'` is `K = K' ^ 2`, his `‖X‖_ψ₁ ≤ K` is `K`.

Every conclusion is centred, so the bridges need `E X = 0`; for a variable that is not centred
the `sub_integral` forms bound `X - E X`, at the price of a factor in the scale (the centring
lemma, [Vershynin2018, Lemma 2.6.8]).

`0 < K` is needed: `X² / 0 = 0` in Lean, so the condition at `K = 0` holds for every `X`.
A probability measure is needed: under `2 • δ₀` the variable `0` satisfies the `ψ₂` condition but
has `mgf 0 = 2 > 1`. `AEMeasurable X` is a hypothesis: integrability of `exp (X² / K)` does not
give it (the sign is lost).

A `ψ₂` Hanson–Wright inequality is the `ψ₂` bridge followed by
`NLAlib.measureReal_quadForm_sub_integral_ge_le`, and a `ψ₁` Bernstein inequality is the `ψ₁`
bridge followed by `NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`; neither is
restated (`docs/design/Probability-P7.md` §7 D3, D4).

## Main definitions

* `NLAlib.psiTwoSubgaussianConstant`, `NLAlib.psiOneSubexponentialVarianceConstant`,
  `NLAlib.psiOneSubexponentialScaleConstant`: the constants of the bridges.

## Main results

* `NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`: the `ψ₂` bridge.
* `NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`: the `ψ₁` bridge.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two`,
  `NLAlib.hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two`: the centred forms.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], §2.5–§2.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Elementary inequalities -/

private theorem exp_le_add_exp_sq (y : ℝ) : rexp y ≤ y + rexp (y ^ 2) := by
  rcases le_or_gt |y| 1 with hy | hy
  · have h1 := Real.abs_exp_sub_one_sub_id_le hy
    have h2 := Real.add_one_le_exp (y ^ 2)
    have h3 := le_abs_self (rexp y - 1 - y)
    linarith
  · rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy
      have : rexp y ≤ rexp (y ^ 2) := Real.exp_le_exp.2 (by nlinarith)
      linarith
    · rw [abs_of_neg h0] at hy
      have h1 : rexp y ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h2 := Real.add_one_le_exp (y ^ 2)
      nlinarith

private theorem exp_le_one_add_add_sq_mul_exp_abs_div_two (y : ℝ) :
    rexp y ≤ 1 + y + y ^ 2 * rexp |y| / 2 := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0]
    have hmono : Monotone (fun x => 1 + x + x ^ 2 * rexp x / 2 - rexp x) := by
      refine monotone_of_hasDerivAt_nonneg
        (f' := fun x => 1 + (2 * x * rexp x + x ^ 2 * rexp x) / 2 - rexp x) (fun x => ?_)
        (fun x => ?_)
      · have h := (((hasDerivAt_id x).const_add 1).add
          (((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_exp x)).div_const 2)).sub
          (Real.hasDerivAt_exp x)
        exact h.congr_deriv (by norm_num)
      · dsimp only [Pi.zero_apply]
        have h1 : 1 - x ≤ rexp (-x) := by linarith [Real.add_one_le_exp (-x)]
        have h2 : rexp x * rexp (-x) = 1 := by rw [← Real.exp_add]; simp
        have hx := Real.exp_pos x
        nlinarith [mul_le_mul_of_nonneg_left h1 hx.le, mul_nonneg (sq_nonneg x) hx.le]
    have h := hmono h0
    simp only [Real.exp_zero] at h
    norm_num at h
    linarith
  · have hanti : Antitone (fun x => 1 + x + x ^ 2 / 2 - rexp x) := by
      refine antitone_of_hasDerivAt_nonpos (f' := fun x => 1 + x - rexp x) (fun x => ?_)
        (fun x => ?_)
      · have h := (((hasDerivAt_id x).const_add 1).add
          ((hasDerivAt_pow 2 x).div_const 2)).sub (Real.hasDerivAt_exp x)
        exact h.congr_deriv (by norm_num)
      · dsimp only [Pi.zero_apply]
        linarith [Real.add_one_le_exp x]
    have h := hanti h0
    simp only [Real.exp_zero] at h
    norm_num at h
    have h1 : y ^ 2 ≤ y ^ 2 * rexp |y| :=
      le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (abs_nonneg y))
    linarith

/-- `x² ≤ (16 K² / e²) e^{|x| / (2K)}`, from `w ≤ e^{w - 1}` at `w = |x| / (4K)`. -/
private theorem sq_le_mul_exp_abs_div {K : ℝ} (hK : 0 < K) (x : ℝ) :
    x ^ 2 ≤ 16 * K ^ 2 / rexp 2 * rexp (|x| / (2 * K)) := by
  set w := |x| / (4 * K) with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 : w ≤ rexp (w - 1) := by linarith [Real.add_one_le_exp (w - 1)]
  have h2 : w ^ 2 ≤ rexp (w - 1) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have h3 : rexp (w - 1) ^ 2 = rexp (|x| / (2 * K)) / rexp 2 := by
    rw [← Real.exp_sub, ← Real.exp_nat_mul]
    congr 1
    rw [hw]
    field_simp
    ring
  have h4 : x ^ 2 = 16 * K ^ 2 * w ^ 2 := by
    rw [hw, div_pow, ← sq_abs x]
    field_simp
    ring
  rw [h4]
  calc 16 * K ^ 2 * w ^ 2 ≤ 16 * K ^ 2 * rexp (w - 1) ^ 2 := by gcongr
    _ = _ := by rw [h3]; ring

/-! ### Jensen's inequality for the Orlicz conditions -/

/-- If `E e^Z ≤ 2` for `Z ≥ 0`, then `E e^{p Z} ≤ 2^p` for `p ∈ [0, 1]` (Jensen for `x ↦ x^p`). -/
private theorem integral_exp_mul_le_of_integral_exp_le_two [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZm : AEMeasurable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => rexp (Z ω)) μ)
    (hψ : ∫ ω, rexp (Z ω) ∂μ ≤ 2) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun ω => rexp (p * Z ω)) μ ∧
      ∫ ω, rexp (p * Z ω) ∂μ ≤ rexp (p * Real.log 2) := by
  have hpi : Integrable (fun ω => rexp (p * Z ω)) μ := by
    refine hint.mono' (by fun_prop) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [hZ0 ω])
  refine ⟨hpi, ?_⟩
  have heq : ((fun x : ℝ => x ^ p) ∘ fun ω => rexp (Z ω)) = fun ω => rexp (p * Z ω) := by
    ext ω
    simp only [Function.comp_apply]
    rw [← Real.exp_mul, mul_comm]
  have hJ := (Real.concaveOn_rpow hp0 hp1).le_map_integral (μ := μ)
    (f := fun ω => rexp (Z ω)) (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (ae_of_all _ fun ω => (Real.exp_pos _).le) hint (by rw [heq]; exact hpi)
  have hJ' : ∫ ω, rexp (p * Z ω) ∂μ ≤ (∫ ω, rexp (Z ω) ∂μ) ^ p := by
    refine le_of_eq_of_le ?_ hJ
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rw [← Real.exp_mul, mul_comm]
  calc ∫ ω, rexp (p * Z ω) ∂μ ≤ (∫ ω, rexp (Z ω) ∂μ) ^ p := hJ'
    _ ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow (integral_nonneg fun _ => (Real.exp_pos _).le) hψ hp0
    _ = rexp (p * Real.log 2) := by rw [Real.rpow_def_of_pos two_pos, mul_comm]

/-- If `E e^Z ≤ 2`, then `E Z ≤ log 2` (Jensen for `exp`). -/
private theorem integral_le_log_two_of_integral_exp_le_two [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Integrable Z μ) (hint : Integrable (fun ω => rexp (Z ω)) μ)
    (hψ : ∫ ω, rexp (Z ω) ∂μ ≤ 2) : ∫ ω, Z ω ∂μ ≤ Real.log 2 := by
  have hJ := convexOn_exp.map_integral_le (μ := μ) (f := Z) Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hZ hint
  rw [Real.le_log_iff_exp_le two_pos]
  exact hJ.trans hψ

private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9
  linarith

private theorem exp_half_log_two_mul_self :
    rexp (1 / 2 * Real.log 2) * rexp (1 / 2 * Real.log 2) = 2 := by
  rw [← Real.exp_add, show 1 / 2 * Real.log 2 + 1 / 2 * Real.log 2 = Real.log 2 by ring,
    Real.exp_log two_pos]

/-! ### The `ψ₂` bound on the moment generating function -/

private theorem integrable_of_integral_exp_sq_div {X : Ω → ℝ} [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ) : Integrable X μ := by
  refine ((integrable_const (K / 2)).add (hint.div_const 2)).mono' hX.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |X ω| ≤ K / 2 + X ω ^ 2 / K / 2 := by
    rw [← sub_nonneg]
    have : K / 2 + X ω ^ 2 / K / 2 - |X ω| = (|X ω| - K) ^ 2 / (2 * K) := by
      rw [sub_sq, sq_abs]
      field_simp
      ring
    rw [this]
    positivity
  have h2 := Real.add_one_le_exp (X ω ^ 2 / K)
  simp only [Pi.add_apply]
  linarith

private theorem mgf_le_of_integral_exp_sq_div [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) (t : ℝ) :
    Integrable (fun ω => rexp (t * X ω)) μ ∧
      mgf X μ t ≤ rexp ((1 + Real.log 2) * K * t ^ 2 / 2) := by
  have hZm : AEMeasurable (fun ω => X ω ^ 2 / K) μ := by fun_prop
  have hZ0 : ∀ ω, 0 ≤ X ω ^ 2 / K := fun ω => by positivity
  obtain ⟨hhalf, hhalfle⟩ := integral_exp_mul_le_of_integral_exp_le_two hZm hZ0 hint hψ
    (p := 1 / 2) (by norm_num) (by norm_num)
  have hpt : ∀ ω, rexp (t * X ω) ≤ rexp (t ^ 2 * K / 2) * rexp (1 / 2 * (X ω ^ 2 / K)) := by
    intro ω
    rw [← Real.exp_add, Real.exp_le_exp, ← sub_nonneg]
    have : t ^ 2 * K / 2 + 1 / 2 * (X ω ^ 2 / K) - t * X ω = (t * K - X ω) ^ 2 / (2 * K) := by
      field_simp
      ring
    rw [this]
    positivity
  have hti : Integrable (fun ω => rexp (t * X ω)) μ :=
    (hhalf.const_mul _).mono' (by fun_prop) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω)
  refine ⟨hti, ?_⟩
  have hl2 := log_two_le_one
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  rcases le_or_gt (t ^ 2 * K) 1 with hp | hp
  · obtain ⟨hpi, hple⟩ := integral_exp_mul_le_of_integral_exp_le_two hZm hZ0 hint hψ
      (p := t ^ 2 * K) (by positivity) hp
    have hXi := integrable_of_integral_exp_sq_div hX hK hint
    have hpt2 : ∀ ω, rexp (t * X ω) ≤ t * X ω + rexp (t ^ 2 * K * (X ω ^ 2 / K)) := by
      intro ω
      have h := exp_le_add_exp_sq (t * X ω)
      have : (t * X ω) ^ 2 = t ^ 2 * K * (X ω ^ 2 / K) := by field_simp
      rwa [this] at h
    calc mgf X μ t = ∫ ω, rexp (t * X ω) ∂μ := rfl
      _ ≤ ∫ ω, (t * X ω + rexp (t ^ 2 * K * (X ω ^ 2 / K))) ∂μ :=
        integral_mono hti ((hXi.const_mul t).add hpi) hpt2
      _ = ∫ ω, rexp (t ^ 2 * K * (X ω ^ 2 / K)) ∂μ := by
        rw [integral_add (hXi.const_mul t) hpi, integral_const_mul, hmean]; ring
      _ ≤ rexp (t ^ 2 * K * Real.log 2) := hple
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) hK.le])
  · calc mgf X μ t = ∫ ω, rexp (t * X ω) ∂μ := rfl
      _ ≤ ∫ ω, rexp (t ^ 2 * K / 2) * rexp (1 / 2 * (X ω ^ 2 / K)) ∂μ :=
        integral_mono hti (hhalf.const_mul _) hpt
      _ ≤ rexp (t ^ 2 * K / 2) * rexp (1 / 2 * Real.log 2) := by
        rw [integral_const_mul]; gcongr
      _ ≤ _ := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith

/-! ### The `ψ₁` bound on the moment generating function -/

private theorem integrable_of_integral_exp_abs_div {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ) : Integrable X μ := by
  refine (hint.const_mul K).mono' hX.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h := Real.add_one_le_exp (|X ω| / K)
  calc |X ω| = K * (|X ω| / K) := by field_simp
    _ ≤ K * rexp (|X ω| / K) := by gcongr; linarith

private theorem mgf_le_of_integral_exp_abs_div [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) {t : ℝ} (ht : 2 * K * |t| < 1) :
    Integrable (fun ω => rexp (t * X ω)) μ ∧
      mgf X μ t ≤ rexp (32 / rexp 2 * K ^ 2 * t ^ 2 / 2) := by
  have hlin : ∀ ω, |t * X ω| ≤ |X ω| / (2 * K) := by
    intro ω
    rw [abs_mul, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg (X ω), abs_nonneg t]
  have hhalf : ∀ ω, |X ω| / (2 * K) ≤ |X ω| / K := fun ω =>
    div_le_div_of_nonneg_left (abs_nonneg _) hK (by linarith)
  have hti : Integrable (fun ω => rexp (t * X ω)) μ :=
    hint.mono' (by fun_prop) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      exact (le_abs_self _).trans ((hlin ω).trans (hhalf ω)))
  refine ⟨hti, ?_⟩
  have hXi := integrable_of_integral_exp_abs_div hX hK hint
  set C : ℝ := 8 * K ^ 2 / rexp 2 * t ^ 2 with hC
  have hpt : ∀ ω, rexp (t * X ω) ≤ 1 + t * X ω + C * rexp (|X ω| / K) := by
    intro ω
    have h1 := exp_le_one_add_add_sq_mul_exp_abs_div_two (t * X ω)
    have h2 : rexp |t * X ω| ≤ rexp (|X ω| / (2 * K)) := Real.exp_le_exp.2 (hlin ω)
    have h3 := sq_le_mul_exp_abs_div hK (X ω)
    have h4 : rexp (|X ω| / (2 * K)) * rexp (|X ω| / (2 * K)) = rexp (|X ω| / K) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have h5 : (t * X ω) ^ 2 * rexp |t * X ω| ≤
        t ^ 2 * (16 * K ^ 2 / rexp 2 * rexp (|X ω| / (2 * K))) * rexp (|X ω| / (2 * K)) := by
      rw [mul_pow]
      gcongr
    have h6 : t ^ 2 * (16 * K ^ 2 / rexp 2 * rexp (|X ω| / (2 * K))) * rexp (|X ω| / (2 * K)) =
        2 * C * rexp (|X ω| / K) := by
      rw [← h4, hC]; ring
    linarith
  have hC0 : 0 ≤ C := by positivity
  calc mgf X μ t = ∫ ω, rexp (t * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + t * X ω + C * rexp (|X ω| / K)) ∂μ :=
      integral_mono hti (((integrable_const 1).add (hXi.const_mul t)).add (hint.const_mul C)) hpt
    _ = 1 + C * ∫ ω, rexp (|X ω| / K) ∂μ := by
      rw [integral_add (f := fun ω => 1 + t * X ω)
          ((integrable_const 1).add (hXi.const_mul t)) (hint.const_mul C),
        integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => t * X ω) (integrable_const 1)
          (hXi.const_mul t), integral_const_mul,
        integral_const_mul, hmean]
      simp
    _ ≤ 1 + C * 2 := by gcongr
    _ ≤ rexp (C * 2) := by linarith [Real.add_one_le_exp (C * 2)]
    _ = _ := by rw [hC]; ring_nf

/-- The proxy constant of the `ψ₂` bridge `NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`.
[Vershynin2018, Proposition 2.5.2] leaves it unspecified. The proof (`e^y ≤ y + e^{y²}`, then
Jensen for `λ² K ≤ 1`, and `λ X ≤ λ² K / 2 + X² / (2K)` otherwise) reaches `1 + log 2`, which is
the body. A smaller value is a better bound. Use only `psiTwoSubgaussianConstant_le`. -/
noncomputable irreducible_def psiTwoSubgaussianConstant : ℝ≥0 := Real.toNNReal (1 + Real.log 2)

/-- An explicit upper bound on `psiTwoSubgaussianConstant`.
Proof: `psiTwoSubgaussianConstant_def`. Easy. -/
theorem psiTwoSubgaussianConstant_le : psiTwoSubgaussianConstant ≤ 2 := by
  rw [psiTwoSubgaussianConstant_def, Real.toNNReal_le_iff_le_coe]
  have := log_two_le_one
  push_cast
  linarith

/-- **A centred variable with a `ψ₂` bound is sub-Gaussian**: if `E X = 0`, `exp (X² / K)` is
integrable and `E exp (X² / K) ≤ 2`, then `HasSubgaussianMGF X (C K)` with
`C = psiTwoSubgaussianConstant`. [Vershynin2018, Proposition 2.5.2], (iv) ⟹ (v), with Vershynin's
`‖X‖_ψ₂ ≤ K'` as `K = K' ^ 2` and the constant named. The hypothesis `E X = 0` is needed (every
`HasSubgaussianMGF` variable is centred); for a variable that is not centred, use
`NLAlib.hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two`. A `ψ₂` Hanson–Wright
inequality is `measureReal_quadForm_sub_integral_ge_le hind fun i => this (hψ i)`, with exponent
Vershynin's at `c = psiTwoSubgaussianConstant * K`.
Proof: `e^y ≤ y + e^{y²}`, so `mgf X μ λ ≤ E exp (λ² X²)` (the linear term vanishes). If
`λ² K ≤ 1`, Jensen for the concave `x ↦ x ^ (λ² K)` gives `≤ 2 ^ (λ² K) = e^{λ² K log 2}`;
otherwise `λ X ≤ λ² K / 2 + X² / (2K)` and Jensen at exponent `1 / 2` give
`≤ e^{λ² K / 2} √2`. Both are at most `e^{(1 + log 2) K λ² / 2}`. Integrability of `exp (λ X)`
from `exp (λ X) ≤ e^{λ² K / 2} exp (X² / (2K))`. Medium.
Result: subgaussian-def -/
theorem hasSubgaussianMGF_of_integral_exp_sq_div_le_two [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) :
    HasSubgaussianMGF X (psiTwoSubgaussianConstant * K) μ := by
  have hK' : (0 : ℝ) < K := hK
  have hc : ((psiTwoSubgaussianConstant * K : ℝ≥0) : ℝ) = (1 + Real.log 2) * K := by
    rw [NNReal.coe_mul, psiTwoSubgaussianConstant_def,
      Real.coe_toNNReal _ (by linarith [Real.log_nonneg one_le_two])]
  refine ⟨fun t => (mgf_le_of_integral_exp_sq_div hX hmean hK' hint hψ t).1, fun t => ?_⟩
  rw [hc]
  exact (mgf_le_of_integral_exp_sq_div hX hmean hK' hint hψ t).2

/-- **The centred `ψ₂` bridge**: if `exp (X² / K)` is integrable and `E exp (X² / K) ≤ 2`, then
`X - E X` is sub-Gaussian with proxy `C · 4K`, `C = psiTwoSubgaussianConstant`.
[Vershynin2018, Lemma 2.6.8] (centring costs a constant factor in the `ψ₂` norm), here with the
explicit factor `4` in the squared scale.
Proof: `X - E X` satisfies the `ψ₂` condition with squared scale `4K`: `(EX)² ≤ K log 2` by
Jensen (`exp ((EX)² / K) ≤ E exp (X² / K) ≤ 2`), `(X - EX)² ≤ 2X² + 2(EX)²`, and
`E exp (X² / (2K)) ≤ √2` by Jensen, so `E exp ((X - EX)² / (4K)) ≤ √2 · √2 = 2`; then
`NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`. Integrability of `X` from
`|X| ≤ K + exp (X² / K)`, up to constants. Easy to medium. -/
theorem hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) :
    HasSubgaussianMGF (fun ω => X ω - ∫ ω', X ω' ∂μ) (psiTwoSubgaussianConstant * (4 * K)) μ := by
  have hK' : (0 : ℝ) < K := hK
  set m := ∫ ω', X ω' ∂μ with hm
  have hXi := integrable_of_integral_exp_sq_div hX hK' hint
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := by
    refine (hint.const_mul K).mono' (hX.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := Real.add_one_le_exp (X ω ^ 2 / K)
    calc X ω ^ 2 = K * (X ω ^ 2 / K) := by field_simp
      _ ≤ K * rexp (X ω ^ 2 / K) := by gcongr; linarith
  have hm2 : m ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ :=
    (even_two.convexOn_pow (𝕜 := ℝ)).map_integral_le (μ := μ) (f := X)
      (continuous_pow 2).continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hXi hX2
  have hlog := integral_le_log_two_of_integral_exp_le_two (hX2.div_const (K : ℝ)) hint hψ
  rw [integral_div] at hlog
  have hmK : m ^ 2 / K ≤ Real.log 2 := (div_le_div_of_nonneg_right hm2 hK'.le).trans hlog
  obtain ⟨hhalf, hhalfle⟩ := integral_exp_mul_le_of_integral_exp_le_two (by fun_prop)
    (fun ω => by positivity) hint hψ (p := 1 / 2) (by norm_num) (by norm_num)
  have hpt : ∀ ω, rexp ((X ω - m) ^ 2 / ((4 * K : ℝ≥0) : ℝ)) ≤
      rexp (m ^ 2 / (2 * K)) * rexp (1 / 2 * (X ω ^ 2 / K)) := by
    intro ω
    rw [← Real.exp_add, Real.exp_le_exp, NNReal.coe_mul, NNReal.coe_ofNat, ← sub_nonneg]
    have : m ^ 2 / (2 * K) + 1 / 2 * (X ω ^ 2 / K) - (X ω - m) ^ 2 / (4 * K) =
        (X ω + m) ^ 2 / (4 * K) := by
      field_simp
      ring
    rw [this]
    positivity
  have hYi : Integrable (fun ω => rexp ((X ω - m) ^ 2 / ((4 * K : ℝ≥0) : ℝ))) μ :=
    (hhalf.const_mul _).mono' (by fun_prop) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω)
  have hYle : ∫ ω, rexp ((X ω - m) ^ 2 / ((4 * K : ℝ≥0) : ℝ)) ∂μ ≤ 2 := by
    calc ∫ ω, rexp ((X ω - m) ^ 2 / ((4 * K : ℝ≥0) : ℝ)) ∂μ
        ≤ ∫ ω, rexp (m ^ 2 / (2 * K)) * rexp (1 / 2 * (X ω ^ 2 / K)) ∂μ :=
          integral_mono hYi (hhalf.const_mul _) hpt
      _ ≤ rexp (1 / 2 * Real.log 2) * rexp (1 / 2 * Real.log 2) := by
        rw [integral_const_mul]
        gcongr
        rw [show m ^ 2 / (2 * K) = 1 / 2 * (m ^ 2 / K) by ring]
        linarith
      _ = 2 := exp_half_log_two_mul_self
  have hYmean : ∫ ω, (X ω - m) ∂μ = 0 := by
    rw [integral_sub hXi (integrable_const m)]
    simp [hm]
  exact hasSubgaussianMGF_of_integral_exp_sq_div_le_two (hX.sub_const m) hYmean
    (by positivity) hYi hYle

/-- The variance-proxy constant of the `ψ₁` bridge
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. [Vershynin2018,
Proposition 2.7.1] leaves it unspecified. The proof (`e^y ≤ 1 + y + y² e^{|y|} / 2` on
`|λ| < 1 / (2K)`, and `u² ≤ 4 e^{u - 2}`) reaches `32 / e²`, which is the body. A smaller value
is a better bound. Use only `psiOneSubexponentialVarianceConstant_le`. -/
noncomputable irreducible_def psiOneSubexponentialVarianceConstant : ℝ≥0 :=
  Real.toNNReal (32 / rexp 2)

/-- The scale constant of the `ψ₁` bridge
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. [Vershynin2018,
Proposition 2.7.1] leaves it unspecified; the proof reaches `2`. A smaller value is a better
bound. Use only `psiOneSubexponentialScaleConstant_le`. -/
noncomputable irreducible_def psiOneSubexponentialScaleConstant : ℝ≥0 := 2

/-- An explicit upper bound on `psiOneSubexponentialVarianceConstant`.
Proof: `psiOneSubexponentialVarianceConstant_def`. Easy. -/
theorem psiOneSubexponentialVarianceConstant_le : psiOneSubexponentialVarianceConstant ≤ 5 := by
  rw [psiOneSubexponentialVarianceConstant_def, Real.toNNReal_le_iff_le_coe]
  rw [NNReal.coe_ofNat, div_le_iff₀ (Real.exp_pos 2)]
  have h1 := Real.exp_one_gt_d9
  have h2 : rexp 2 = rexp 1 * rexp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

/-- An explicit upper bound on `psiOneSubexponentialScaleConstant`.
Proof: `psiOneSubexponentialScaleConstant_def`. Easy. -/
theorem psiOneSubexponentialScaleConstant_le : psiOneSubexponentialScaleConstant ≤ 2 := by
  rw [psiOneSubexponentialScaleConstant_def]

/-- **A centred variable with a `ψ₁` bound is sub-exponential**: if `E X = 0`, `exp (|X| / K)`
is integrable and `E exp (|X| / K) ≤ 2`, then `X` is sub-exponential with variance proxy
`C₁ K²` and scale `C₂ K`, `C₁ = psiOneSubexponentialVarianceConstant`,
`C₂ = psiOneSubexponentialScaleConstant`. [Vershynin2018, Proposition 2.7.1], (iv) ⟹ (v), with
the constants named. The hypothesis `E X = 0` is needed (every `HasSubexponentialMGF` variable
is centred, `NLAlib.HasSubexponentialMGF.integral_eq_zero`); for a variable that is not
centred, use `NLAlib.hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two`. A `ψ₁`
Bernstein inequality is this bridge followed by
`NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`.
Proof: for `|λ| < 1 / (2K)`, `e^y ≤ 1 + y + y² e^{|y|} / 2` gives
`mgf X μ λ ≤ 1 + λ² E[X² e^{|X| / (2K)}] / 2`, and `X² ≤ (16 K² / e²) e^{|X| / (2K)}` (from
`u² ≤ 4 e^{u - 2}`) bounds the expectation by `(16 K² / e²) E e^{|X| / K} ≤ 32 K² / e²`; then
`1 + a ≤ e^a`. Medium.
Result: subexponential-def -/
theorem hasSubexponentialMGF_of_integral_exp_abs_div_le_two [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) :
    HasSubexponentialMGF X (psiOneSubexponentialVarianceConstant * K ^ 2)
      (psiOneSubexponentialScaleConstant * K) μ := by
  have hK' : (0 : ℝ) < K := hK
  have hw : ∀ l : ℝ, ((psiOneSubexponentialScaleConstant * K : ℝ≥0) : ℝ) * |l| < 1 →
      2 * K * |l| < 1 := fun l hl => by
    rwa [NNReal.coe_mul, psiOneSubexponentialScaleConstant_def, NNReal.coe_ofNat] at hl
  have hc : ((psiOneSubexponentialVarianceConstant * K ^ 2 : ℝ≥0) : ℝ) =
      32 / rexp 2 * K ^ 2 := by
    rw [NNReal.coe_mul, psiOneSubexponentialVarianceConstant_def,
      Real.coe_toNNReal _ (by positivity), NNReal.coe_pow]
  refine ⟨fun l hl => (mgf_le_of_integral_exp_abs_div hX hmean hK' hint hψ (hw l hl)).1,
    fun l hl => ?_⟩
  rw [hc]
  exact (mgf_le_of_integral_exp_abs_div hX hmean hK' hint hψ (hw l hl)).2

/-- **The centred `ψ₁` bridge**: if `exp (|X| / K)` is integrable and `E exp (|X| / K) ≤ 2`,
then `X - E X` is sub-exponential with variance proxy `C₁ (2K)²` and scale `C₂ (2K)`. The `ψ₁`
analogue of the centring lemma [Vershynin2018, Lemma 2.6.8], with the explicit factor `2` in the
scale.
Proof: `X - E X` satisfies the `ψ₁` condition with scale `2K`: `|EX| ≤ K log 2` by Jensen,
`E exp (|X| / (2K)) ≤ √2` by Jensen, and `|X - EX| ≤ |X| + |EX|`, so
`E exp (|X - EX| / (2K)) ≤ 2`; then
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. Easy to medium. -/
theorem hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) :
    HasSubexponentialMGF (fun ω => X ω - ∫ ω', X ω' ∂μ)
      (psiOneSubexponentialVarianceConstant * (2 * K) ^ 2)
      (psiOneSubexponentialScaleConstant * (2 * K)) μ := by
  have hK' : (0 : ℝ) < K := hK
  set m := ∫ ω', X ω' ∂μ with hm
  have hXi := integrable_of_integral_exp_abs_div hX hK' hint
  have hlog := integral_le_log_two_of_integral_exp_le_two (hXi.abs.div_const (K : ℝ)) hint hψ
  rw [integral_div] at hlog
  have hmK : |m| / K ≤ Real.log 2 :=
    (div_le_div_of_nonneg_right (abs_integral_le_integral_abs) hK'.le).trans hlog
  obtain ⟨hhalf, hhalfle⟩ := integral_exp_mul_le_of_integral_exp_le_two (by fun_prop)
    (fun ω => by positivity) hint hψ (p := 1 / 2) (by norm_num) (by norm_num)
  have hpt : ∀ ω, rexp (|X ω - m| / ((2 * K : ℝ≥0) : ℝ)) ≤
      rexp (|m| / (2 * K)) * rexp (1 / 2 * (|X ω| / K)) := by
    intro ω
    rw [← Real.exp_add, Real.exp_le_exp, NNReal.coe_mul, NNReal.coe_ofNat]
    have h := abs_sub (X ω) m
    have : |m| / (2 * K) + 1 / 2 * (|X ω| / K) = (|X ω| + |m|) / (2 * K) := by
      field_simp
      ring
    rw [this]
    gcongr
  have hYi : Integrable (fun ω => rexp (|X ω - m| / ((2 * K : ℝ≥0) : ℝ))) μ :=
    (hhalf.const_mul _).mono' (by fun_prop) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω)
  have hYle : ∫ ω, rexp (|X ω - m| / ((2 * K : ℝ≥0) : ℝ)) ∂μ ≤ 2 := by
    calc ∫ ω, rexp (|X ω - m| / ((2 * K : ℝ≥0) : ℝ)) ∂μ
        ≤ ∫ ω, rexp (|m| / (2 * K)) * rexp (1 / 2 * (|X ω| / K)) ∂μ :=
          integral_mono hYi (hhalf.const_mul _) hpt
      _ ≤ rexp (1 / 2 * Real.log 2) * rexp (1 / 2 * Real.log 2) := by
        rw [integral_const_mul]
        gcongr
        rw [show |m| / (2 * K) = 1 / 2 * (|m| / K) by ring]
        linarith
      _ = 2 := exp_half_log_two_mul_self
  have hYmean : ∫ ω, (X ω - m) ∂μ = 0 := by
    rw [integral_sub hXi (integrable_const m)]
    simp [hm]
  exact hasSubexponentialMGF_of_integral_exp_abs_div_le_two (hX.sub_const m) hYmean
    (by positivity) hYi hYle

end NLAlib
