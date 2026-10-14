/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import NLAlib.ForMathlib.Analysis.Calculus.ContDiff.Hessian
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Gaussian integration by parts

For a Gaussian vector `X` in `ℝ^ι` (any mean, any covariance, possibly singular) and a function
`f` of class `C¹` with bounded derivative, Stein's identity in covariance form:
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`. It is the tool behind the Gaussian
interpolation inequality and hence every Gaussian comparison theorem
(`NLAlib/Probability/Distributions/GaussianComparison.lean`).

The regularity class is the one the interpolation needs: it applies the identity to the partial
derivatives of a `C²` test function with bounded Hessian. A bounded derivative gives linear growth,
so both integrands are integrable and the identity is never between junk values.

## Main results

* `NLAlib.integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw`:
  Gaussian integration by parts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

open scoped NNReal

/-- The derivative of the standard Gaussian density. -/
private theorem hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      (-(2 * (x - 0)) / (2 * ((1 : ℝ≥0) : ℝ))) x := by
    simpa using (((hasDerivAt_id x).sub_const 0).pow 2).neg.div_const (2 * ((1 : ℝ≥0) : ℝ))
  have h2 := h1.exp.const_mul (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
  rw [gaussianPDFReal_def]
  refine h2.congr_deriv ?_
  simp only [sub_zero, NNReal.coe_one]
  ring

private theorem integrable_gaussianReal_one_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

/-- Stein's identity for the standard Gaussian, under integrability hypotheses. -/
theorem integral_mul_eq_integral_deriv_gaussianReal_one {h : ℝ → ℝ}
    (hh : Differentiable ℝ h) (hhi : Integrable h (gaussianReal 0 1))
    (hxh : Integrable (fun x => x * h x) (gaussianReal 0 1))
    (hdi : Integrable (deriv h) (gaussianReal 0 1)) :
    ∫ x, x * h x ∂gaussianReal 0 1 = ∫ x, deriv h x ∂gaussianReal 0 1 := by
  rw [integrable_gaussianReal_one_iff] at hxh hdi hhi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h)
    (v := fun x => -gaussianPDFReal 0 1 x) (u' := deriv h)
    (v' := fun x => x * gaussianPDFReal 0 1 x)
    (fun x _ => (hh x).hasDerivAt)
    (fun x _ => (hasDerivAt_gaussianPDFReal_zero_one x).neg.congr_deriv (neg_neg _))
    (hxh.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply]; ring))
    (hdi.neg.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
    (hhi.neg.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
  calc ∫ x, gaussianPDFReal 0 1 x * (x * h x)
      = ∫ x, h x * (x * gaussianPDFReal 0 1 x) := by congr 1; funext x; ring
    _ = -∫ x, deriv h x * -gaussianPDFReal 0 1 x := key
    _ = ∫ x, gaussianPDFReal 0 1 x * deriv h x := by
      rw [← integral_neg]; congr 1; funext x; ring

/-- Stein's identity for `N(m, v)`, for a function with bounded derivative:
`E [(x - m) h(x)] = v E [h'(x)]`. -/
private theorem integral_sub_mul_eq_mul_integral_deriv_gaussianReal (m : ℝ) (v : ℝ≥0)
    {h : ℝ → ℝ} (hh : Differentiable ℝ h) {K : ℝ} (hK : ∀ x, ‖deriv h x‖ ≤ K) :
    ∫ x, (x - m) * h x ∂gaussianReal m v = v * ∫ x, deriv h x ∂gaussianReal m v := by
  set s : ℝ := √(v : ℝ) with hs
  have hss : s * s = v := Real.mul_self_sqrt v.coe_nonneg
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hmap : gaussianReal m v = (gaussianReal 0 1).map (fun y => s * y + m) := by
    have : (fun y => s * y + m) = (· + m) ∘ (s * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const, mul_zero, zero_add]
    congr 1
    ext
    simp [sq, hss]
  set g : ℝ → ℝ := fun y => h (s * y + m) with hg
  have hgd : ∀ y, HasDerivAt g (s * deriv h (s * y + m)) y := by
    intro y
    have h1 : HasDerivAt (fun y => s * y + m) s y := by
      simpa using ((hasDerivAt_id y).const_mul s).add_const m
    exact ((hh (s * y + m)).hasDerivAt.comp y h1).congr_deriv (mul_comm _ _)
  have hgdiff : Differentiable ℝ g := fun y => (hgd y).differentiableAt
  have hderiv : deriv g = fun y => s * deriv h (s * y + m) := funext fun y => (hgd y).deriv
  have hgrowth : ∀ y, |g y| ≤ |h m| + K * s * |y| := by
    intro y
    have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hh x) (fun x _ => hK x)
      convex_univ (Set.mem_univ m) (Set.mem_univ (s * y + m))
    simp only [Real.norm_eq_abs, add_sub_cancel_right, abs_mul, abs_of_nonneg hs0] at this
    have h3 := abs_sub_abs_le_abs_sub (g y) (h m)
    simp only [hg] at h3 ⊢
    nlinarith
  have hγ1 : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
    (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)).abs
  have hγ2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hgi : Integrable g (gaussianReal 0 1) :=
    Integrable.mono' ((integrable_const |h m|).add (hγ1.const_mul (K * s)))
      hgdiff.continuous.aestronglyMeasurable
      (ae_of_all _ fun y => by
        simpa only [Real.norm_eq_abs, Pi.add_apply] using hgrowth y)
  have hxg : Integrable (fun y => y * g y) (gaussianReal 0 1) := by
    refine Integrable.mono' ((hγ1.const_mul |h m|).add (hγ2.const_mul (K * s)))
      (continuous_id.mul hgdiff.continuous).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_left (hgrowth y) (abs_nonneg y)
    simp only [Pi.add_apply]
    rw [show K * s * y ^ 2 = |y| * (K * s * |y|) by rw [← sq_abs]; ring]
    linarith
  have hdg : Integrable (deriv g) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (s * K))
      (measurable_deriv g).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [hderiv, norm_mul, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left (hK _) hs0
  have hstein := integral_mul_eq_integral_deriv_gaussianReal_one hgdiff hgi hxg hdg
  have e1 : ∫ x, (x - m) * h x ∂(gaussianReal 0 1).map (fun y => s * y + m)
      = ∫ y, (s * y + m - m) * h (s * y + m) ∂gaussianReal 0 1 :=
    integral_map (by fun_prop)
      ((continuous_id.sub continuous_const).mul hh.continuous).aestronglyMeasurable
  have e2 : ∫ x, deriv h x ∂(gaussianReal 0 1).map (fun y => s * y + m)
      = ∫ y, deriv h (s * y + m) ∂gaussianReal 0 1 :=
    integral_map (by fun_prop) (measurable_deriv h).aestronglyMeasurable
  rw [hmap, e1, e2]
  calc ∫ y, (s * y + m - m) * h (s * y + m) ∂gaussianReal 0 1
      = s * ∫ y, y * g y ∂gaussianReal 0 1 := by
        rw [← integral_const_mul]; congr 1; funext y; simp only [hg]; ring
    _ = s * ∫ y, s * deriv h (s * y + m) ∂gaussianReal 0 1 := by rw [hstein, hderiv]
    _ = v * ∫ y, deriv h (s * y + m) ∂gaussianReal 0 1 := by
        rw [integral_const_mul, ← mul_assoc, hss]

/-- Integration against the law of an independent pair, iterated: for independent `U` and `W`
and `F` continuous with `F (U, W)` integrable, `E F(U, W) = ∫ ∫ F (u, w) dU du dW`. -/
theorem integral_comp_eq_integral_integral_of_indepFun {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [IsProbabilityMeasure μ] {U : Ω → ℝ} {W : Ω → E} (hU : AEMeasurable U μ)
    (hW : AEMeasurable W μ) (hUW : IndepFun U W μ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hFi : Integrable (fun ω => F (U ω, W ω)) μ) :
    ∫ ω, F (U ω, W ω) ∂μ = ∫ w, ∫ u, F (u, w) ∂(μ.map U) ∂(μ.map W) := by
  have hpm : AEMeasurable (fun ω => (U ω, W ω)) μ := hU.prodMk hW
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hU hW).1 hUW
  have h1 : ∫ ω, F (U ω, W ω) ∂μ = ∫ p, F p ∂(μ.map (fun ω => (U ω, W ω))) :=
    (integral_map hpm hF.aestronglyMeasurable).symm
  have hint : Integrable F (μ.map (fun ω => (U ω, W ω))) :=
    (integrable_map_measure hF.aestronglyMeasurable hpm).2 hFi
  rw [h1, hprod]
  rw [hprod] at hint
  exact integral_prod_symm F hint

omit [Fintype ι] [DecidableEq ι] in
/-- The regression residual `X - X i • a` of a Gaussian vector is independent of `X i` when
`Cov(X i, X j) = Var (X i) a j` for every `j`. -/
theorem indepFun_residual_of_hasGaussianLaw [Finite ι] {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) (i : ι) (a : ι → ℝ)
    (hcov : ∀ j, cov[fun ω => X ω i, fun ω => X ω j; μ] = Var[fun ω => X ω i; μ] * a j) :
    IndepFun (fun ω => X ω i) (fun ω => X ω - X ω i • a) μ := by
  have := Fintype.ofFinite ι
  have hP := hX.isProbabilityMeasure
  have hXm : ∀ j, MemLp (fun ω => X ω j) 2 μ := fun j =>
    (hX.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)).memLp_two
  set L : (ι → ℝ) →L[ℝ] (Unit → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).prod
      (ContinuousLinearMap.id ℝ (ι → ℝ) -
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).smulRight a) with hL
  have hjoint : HasGaussianLaw
      (fun ω => (fun _ : Unit => X ω i, fun j => X ω j - X ω i * a j)) μ := by
    have heq : (fun ω => (fun _ : Unit => X ω i, fun j => X ω j - X ω i * a j))
        = fun ω => L (X ω) := by
      funext ω
      ext <;> simp [hL]
    rw [heq]
    exact hX.map_fun L
  have hind := hjoint.indepFun_of_covariance_eval (X := fun (_ : Unit) ω => X ω i)
    (Y := fun j ω => X ω j - X ω i * a j) (fun _ j => by
      rw [covariance_fun_sub_right (hXm i) (hXm j) ((hXm i).mul_const _),
        covariance_mul_const_right, covariance_self (hXm i).aemeasurable, hcov]
      ring)
  refine (hind.comp (measurable_pi_apply ()) measurable_id).congr ?_ ?_
  · exact Filter.EventuallyEq.rfl
  · exact ae_of_all _ fun ω => by ext j; simp

omit [DecidableEq ι] in
/-- A function with derivative bounded by `C` of a Gaussian vector is square-integrable: it has
linear growth. -/
private theorem memLp_two_comp_of_norm_fderiv_le {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ)
    {f : (ι → ℝ) → ℝ} (hdiff : Differentiable ℝ f) {C : ℝ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    MemLp (fun ω => f (X ω)) 2 μ := by
  have hP := hX.isProbabilityMeasure
  have hC : 0 ≤ C := (norm_nonneg _).trans (hdf 0)
  refine MemLp.of_le (((memLp_const |f 0|).add (hX.memLp_two.norm.const_mul C)))
    (hdiff.continuous.comp_aestronglyMeasurable hX.aemeasurable.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hdf x)
    convex_univ (Set.mem_univ 0) (Set.mem_univ (X ω))
  rw [sub_zero] at this
  have h2 := norm_sub_norm_le (f (X ω)) (f 0)
  simp only [Pi.add_apply, Real.norm_eq_abs] at this h2 ⊢
  rw [abs_of_nonneg (by positivity : 0 ≤ |f 0| + C * ‖X ω‖)]
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- `Cov(U, V) = Var U * (Cov(U, V) / Var U)`, also when `Var U = 0`. -/
theorem covariance_eq_variance_mul_div [IsProbabilityMeasure μ] {U V : Ω → ℝ}
    (hU : MemLp U 2 μ) : cov[U, V; μ] = Var[U; μ] * (cov[U, V; μ] / Var[U; μ]) := by
  by_cases hσ : Var[U; μ] = 0
  · have hae := ae_eq_integral_of_variance_eq_zero hU hσ
    rw [hσ, zero_mul, covariance]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω, sub_self, zero_mul, Pi.zero_apply]
  · field_simp

omit [DecidableEq ι] in
/-- The one-dimensional identity along the line `u ↦ u • a + w`. -/
private theorem integral_sub_mul_comp_smul_add_eq_gaussianReal (m : ℝ) (v : ℝ≥0)
    {f : (ι → ℝ) → ℝ} (hdiff : Differentiable ℝ f) {C : ℝ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (a w : ι → ℝ) :
    ∫ u, (u - m) * f (u • a + w) ∂gaussianReal m v
      = v * ∫ u, fderiv ℝ f (u • a + w) a ∂gaussianReal m v := by
  have hd : ∀ u, HasDerivAt (fun u : ℝ => f (u • a + w)) (fderiv ℝ f (u • a + w) a) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u • a + w) a u := by
      simpa using ((hasDerivAt_id u).smul_const a).add_const w
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt u h1
  have hderiv : deriv (fun u : ℝ => f (u • a + w)) = fun u => fderiv ℝ f (u • a + w) a :=
    funext fun u => (hd u).deriv
  have h := integral_sub_mul_eq_mul_integral_deriv_gaussianReal m v
    (h := fun u : ℝ => f (u • a + w)) (fun u => (hd u).differentiableAt) (K := C * ‖a‖)
    (fun u => by
      rw [hderiv]
      exact ((fderiv ℝ f _).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hdf _) (norm_nonneg a)))
  rwa [hderiv] at h

/-- **Gaussian integration by parts** (Stein's identity, covariance form): for a Gaussian vector
`X` and `f` of class `C¹` with derivative bounded by `C`,
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`.
[Vershynin2018, Lemma 7.2.5]; stated there for a standard Gaussian, `E [g f(g)] = E f'(g)`; here
any mean and any covariance, possibly singular, and no centring hypothesis (a centred consumer
rewrites with `sub_zero`).
Result: gaussian-integration-by-parts -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ := by
  have hP := hX.isProbabilityMeasure
  have hXj : ∀ j, HasGaussianLaw (fun ω => X ω j) μ := fun j =>
    hX.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)
  have hXm : ∀ j, MemLp (fun ω => X ω j) 2 μ := fun j => (hXj j).memLp_two
  have hXae : AEMeasurable X μ := hX.aemeasurable
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  set m : ℝ := ∫ ω, X ω i ∂μ with hm
  set σ2 : ℝ := Var[fun ω => X ω i; μ] with hσ2
  set a : ι → ℝ := fun j => cov[fun ω => X ω i, fun ω => X ω j; μ] / σ2 with ha
  have hcov : ∀ j, cov[fun ω => X ω i, fun ω => X ω j; μ] = σ2 * a j := fun j =>
    covariance_eq_variance_mul_div (hXm i)
  -- the regression residual `W = X - X i • a` is independent of `X i`
  set W : Ω → ι → ℝ := fun ω => X ω - X ω i • a with hW
  have hXW : ∀ ω, X ω i • a + W ω = X ω := fun ω => by simp only [hW]; abel
  have hind : IndepFun (fun ω => X ω i) W μ :=
    indepFun_residual_of_hasGaussianLaw hX i a fun j => by rw [hcov, hσ2]
  have hUae : AEMeasurable (fun ω => X ω i) μ := (hXj i).aemeasurable
  have hWae : AEMeasurable W μ := hXae.sub (hUae.smul_const a)
  have hmapU : μ.map (fun ω => X ω i) = gaussianReal m σ2.toNNReal :=
    (hXj i).map_eq_gaussianReal
  have hσnn : ((σ2.toNNReal : ℝ≥0) : ℝ) = σ2 := Real.coe_toNNReal _ (variance_nonneg _ _)
  -- the two integrands
  set F1 : ℝ × (ι → ℝ) → ℝ := fun p => (p.1 - m) * f (p.1 • a + p.2) with hF1
  set F2 : ℝ × (ι → ℝ) → ℝ := fun p => fderiv ℝ f (p.1 • a + p.2) a with hF2
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hF1c : Continuous F1 := by simp only [hF1]; fun_prop
  have hF2c : Continuous F2 :=
    (hdfc.comp (by fun_prop : Continuous fun p : ℝ × (ι → ℝ) => p.1 • a + p.2)).clm_apply
      continuous_const
  have hF2b : ∀ p, ‖F2 p‖ ≤ C * ‖a‖ := fun p =>
    ((fderiv ℝ f _).le_opNorm a).trans (mul_le_mul_of_nonneg_right (hdf _) (norm_nonneg a))
  have hfX : MemLp (fun ω => f (X ω)) 2 μ := memLp_two_comp_of_norm_fderiv_le hX hdiff hdf
  have hF1i : Integrable (fun ω => F1 (X ω i, W ω)) μ := by
    simp only [hF1, hXW]
    exact ((hXm i).sub (memLp_const m)).integrable_mul hfX
  have hF2i : Integrable (fun ω => F2 (X ω i, W ω)) μ :=
    Integrable.mono' (integrable_const (C * ‖a‖))
      (hF2c.comp_aestronglyMeasurable (hUae.prodMk hWae).aestronglyMeasurable)
      (ae_of_all _ fun ω => hF2b _)
  -- the one-dimensional identity in the `X i` direction, for each value of `W`
  have hinner : ∀ w : ι → ℝ, ∫ u, F1 (u, w) ∂(μ.map fun ω => X ω i)
      = σ2 * ∫ u, F2 (u, w) ∂(μ.map fun ω => X ω i) := by
    intro w
    have h := integral_sub_mul_comp_smul_add_eq_gaussianReal m σ2.toNNReal hdiff hdf a w
    rw [hσnn] at h
    rw [hmapU]
    exact h
  have hfa : ∀ x, fderiv ℝ f x a = ∑ j, a j * fderiv ℝ f x (Pi.single j 1) := fun x =>
    apply_eq_sum_mul_apply_single _ a
  have hDi : ∀ j, Integrable (fun ω => fderiv ℝ f (X ω) (Pi.single j 1)) μ := fun j =>
    Integrable.mono' (integrable_const (C * ‖(Pi.single j 1 : ι → ℝ)‖))
      ((hdfc.clm_apply continuous_const).comp_aestronglyMeasurable hXae.aestronglyMeasurable)
      (ae_of_all _ fun ω => ((fderiv ℝ f _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hdf _) (norm_nonneg _)))
  calc ∫ ω, (X ω i - m) * f (X ω) ∂μ = ∫ ω, F1 (X ω i, W ω) ∂μ := by simp only [hF1, hXW]
    _ = ∫ w, ∫ u, F1 (u, w) ∂(μ.map fun ω => X ω i) ∂(μ.map W) :=
      integral_comp_eq_integral_integral_of_indepFun hUae hWae hind hF1c hF1i
    _ = σ2 * ∫ w, ∫ u, F2 (u, w) ∂(μ.map fun ω => X ω i) ∂(μ.map W) := by
      simp_rw [hinner]; rw [integral_const_mul]
    _ = σ2 * ∫ ω, F2 (X ω i, W ω) ∂μ := by
      rw [integral_comp_eq_integral_integral_of_indepFun hUae hWae hind hF2c hF2i]
    _ = σ2 * ∫ ω, ∑ j, a j * fderiv ℝ f (X ω) (Pi.single j 1) ∂μ := by
      simp only [hF2, hXW, hfa]
    _ = _ := by
      rw [integral_finsetSum _ fun j _ => (hDi j).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hcov, mul_assoc]

end NLAlib
