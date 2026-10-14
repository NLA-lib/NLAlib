/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianIntegrationByParts

/-!
# Gaussian integration by parts for derivatives of polynomial growth

Stein's identity in covariance form, `E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`,
for a Gaussian vector `X` and `f` of class `C¹` whose derivative grows at most polynomially,
`‖Df(x)‖ ≤ C (1 + ‖x‖)^k`. The bounded-derivative identity of
`NLAlib/Probability/Distributions/GaussianIntegrationByParts.lean` is the case `k = 0`. The
polynomial class is the one trace polynomials `x ↦ re tr (B (∑ x j • A j)^q)` belong to, as the
Gaussian moment recursion of the noncommutative Khintchine inequality needs
(`NLAlib/Probability/MatrixConcentration/Khintchine.lean`).

This skeleton file is to be merged into `GaussianIntegrationByParts.lean`, which owns the
subject; the bounded version is then reproved from this one at `k = 0` and keeps its name
(P5c D4 and §8).

## Main results

* Stein's identity for derivatives of polynomial growth:
  `integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow`.
* `NLAlib.integrable_one_add_norm_pow_of_memLp`: the dominating functions `(1 + ‖X‖) ^ j`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

open scoped ENNReal NNReal

omit [Fintype ι] [DecidableEq ι] in
/-- A random variable with moments of every finite order has `(1 + ‖X‖) ^ j` integrable, for
every `j`: the dominating function of every polynomial-growth integrand of a Gaussian vector. -/
theorem integrable_one_add_norm_pow_of_memLp {E : Type*} [NormedAddCommGroup E]
    [IsFiniteMeasure μ] {X : Ω → E} (hX : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp X p μ) (j : ℕ) :
    Integrable (fun ω => (1 + ‖X ω‖) ^ j) μ := by
  have hn : MemLp (fun ω => ‖X ω‖) (j : ℝ≥0∞) μ := (hX j (ENNReal.natCast_ne_top j)).norm
  have h : MemLp (fun ω => 1 + ‖X ω‖) (j : ℝ≥0∞) μ := (memLp_const (1 : ℝ)).add hn
  refine h.integrable_norm_pow'.congr (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖X ω‖)]

/-- `(1 + |y|) ^ j` is integrable for the standard Gaussian. -/
private theorem integrable_one_add_abs_pow_gaussianReal (j : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ j) (gaussianReal 0 1) := by
  simpa only [id, Real.norm_eq_abs] using
    integrable_one_add_norm_pow_of_memLp (μ := gaussianReal 0 1) (X := id)
      (fun p hp => memLp_id_gaussianReal' p hp) j

omit [Fintype ι] [DecidableEq ι] in
/-- A function whose derivative grows like `C (1 + ‖x‖) ^ k` grows like `(1 + ‖x‖) ^ (k + 1)`. -/
private theorem abs_le_of_norm_fderiv_le_pow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : Differentiable ℝ f) {C : ℝ} {k : ℕ}
    (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (x : E) :
    |f x| ≤ |f 0| + C * (1 + ‖x‖) ^ (k + 1) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hdf 0)
  have hb : ∀ z ∈ Metric.closedBall (0 : E) ‖x‖, ‖fderiv ℝ f z‖ ≤ C * (1 + ‖x‖) ^ k :=
    fun z hz => (hdf z).trans (by
      have : ‖z‖ ≤ ‖x‖ := by simpa using hz
      gcongr)
  have h1 := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf z) hb (Metric.mem_closedBall_self (norm_nonneg x))
    (by simp : x ∈ Metric.closedBall (0 : E) ‖x‖)
  have h2 := abs_sub_abs_le_abs_sub (f x) (f 0)
  have h3 : C * (1 + ‖x‖) ^ k * ‖x‖ ≤ C * (1 + ‖x‖) ^ (k + 1) := by
    rw [pow_succ, mul_assoc]
    gcongr
    linarith
  simp only [Real.norm_eq_abs, sub_zero] at h1
  linarith

/-- Stein's identity for the standard Gaussian, for a derivative of polynomial growth. -/
private theorem integral_mul_eq_integral_deriv_gaussianReal_one_of_le_pow {g : ℝ → ℝ}
    (hg : Differentiable ℝ g) {K : ℝ} {k : ℕ} (hK : ∀ y, ‖deriv g y‖ ≤ K * (1 + |y|) ^ k) :
    ∫ y, y * g y ∂gaussianReal 0 1 = ∫ y, deriv g y ∂gaussianReal 0 1 := by
  have hdf : ∀ y, ‖fderiv ℝ g y‖ ≤ K * (1 + ‖y‖) ^ k := fun y => by
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs y]
    exact hK y
  have hgr : ∀ y, |g y| ≤ (|g 0| + K) * (1 + |y|) ^ (k + 1) := fun y => by
    have h := abs_le_of_norm_fderiv_le_pow hg hdf y
    have h1 : 1 ≤ (1 + |y|) ^ (k + 1) := one_le_pow₀ (by linarith [abs_nonneg y])
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (g 0)]
  have hgi : Integrable g (gaussianReal 0 1) :=
    Integrable.mono' ((integrable_one_add_abs_pow_gaussianReal (k + 1)).const_mul _)
      hg.continuous.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hgr y)
  have hxg : Integrable (fun y => y * g y) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_one_add_abs_pow_gaussianReal (k + 2)).const_mul
      (|g 0| + K)) (continuous_id.mul hg.continuous).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h0 : 0 ≤ (|g 0| + K) * (1 + |y|) ^ (k + 1) := (abs_nonneg _).trans (hgr y)
    calc |y| * |g y| ≤ (1 + |y|) * ((|g 0| + K) * (1 + |y|) ^ (k + 1)) :=
          mul_le_mul (by linarith) (hgr y) (abs_nonneg _) (by positivity)
      _ = (|g 0| + K) * (1 + |y|) ^ (k + 2) := by ring
  have hdg : Integrable (deriv g) (gaussianReal 0 1) :=
    Integrable.mono' ((integrable_one_add_abs_pow_gaussianReal k).const_mul K)
      (measurable_deriv g).aestronglyMeasurable (ae_of_all _ hK)
  exact integral_mul_eq_integral_deriv_gaussianReal_one hg hgi hxg hdg

/-- Stein's identity for `N(m, v)`, for a derivative of polynomial growth:
`E [(x - m) h(x)] = v E [h'(x)]`. -/
private theorem integral_sub_mul_eq_mul_integral_deriv_gaussianReal_of_le_pow (m : ℝ)
    (v : ℝ≥0) {h : ℝ → ℝ} (hh : Differentiable ℝ h) {K : ℝ} {k : ℕ}
    (hK : ∀ x, ‖deriv h x‖ ≤ K * (1 + |x|) ^ k) :
    ∫ x, (x - m) * h x ∂gaussianReal m v = v * ∫ x, deriv h x ∂gaussianReal m v := by
  set s : ℝ := √(v : ℝ) with hs
  have hss : s * s = v := Real.mul_self_sqrt v.coe_nonneg
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hK 0)
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
  have hgK : ∀ y, ‖deriv g y‖ ≤ s * K * (1 + s + |m|) ^ k * (1 + |y|) ^ k := by
    intro y
    rw [hderiv, norm_mul, Real.norm_eq_abs s, abs_of_nonneg hs0, mul_assoc, mul_assoc,
      ← mul_pow]
    refine mul_le_mul_of_nonneg_left ((hK _).trans ?_) hs0
    gcongr
    have h1 := abs_add_le (s * y) m
    rw [abs_mul, abs_of_nonneg hs0] at h1
    nlinarith [abs_nonneg y, abs_nonneg m]
  have hstein := integral_mul_eq_integral_deriv_gaussianReal_one_of_le_pow hgdiff hgK
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

omit [DecidableEq ι] in
/-- The one-dimensional identity along the line `u ↦ u • a + w`, for a derivative of polynomial
growth. -/
private theorem integral_sub_mul_comp_smul_add_eq_gaussianReal_of_le_pow (m : ℝ) (v : ℝ≥0)
    {f : (ι → ℝ) → ℝ} (hdiff : Differentiable ℝ f) {C : ℝ} {k : ℕ}
    (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (a w : ι → ℝ) :
    ∫ u, (u - m) * f (u • a + w) ∂gaussianReal m v
      = v * ∫ u, fderiv ℝ f (u • a + w) a ∂gaussianReal m v := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hdf 0)
  have hd : ∀ u, HasDerivAt (fun u : ℝ => f (u • a + w)) (fderiv ℝ f (u • a + w) a) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u • a + w) a u := by
      simpa using ((hasDerivAt_id u).smul_const a).add_const w
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt u h1
  have hderiv : deriv (fun u : ℝ => f (u • a + w)) = fun u => fderiv ℝ f (u • a + w) a :=
    funext fun u => (hd u).deriv
  have h := integral_sub_mul_eq_mul_integral_deriv_gaussianReal_of_le_pow m v
    (h := fun u : ℝ => f (u • a + w)) (fun u => (hd u).differentiableAt)
    (K := C * ‖a‖ * (1 + ‖a‖ + ‖w‖) ^ k) (k := k) (fun u => by
      rw [hderiv]
      refine ((fderiv ℝ f _).le_opNorm a).trans ?_
      rw [mul_comm C ‖a‖, mul_assoc, mul_assoc, ← mul_pow, mul_comm _ ‖a‖]
      refine mul_le_mul_of_nonneg_left ((hdf _).trans ?_) (norm_nonneg a)
      gcongr
      have h1 := norm_add_le (u • a) w
      rw [norm_smul, Real.norm_eq_abs] at h1
      nlinarith [abs_nonneg u, norm_nonneg a, norm_nonneg w])
  rwa [hderiv] at h

omit [DecidableEq ι] in
/-- For a Gaussian vector `X` and `f` whose derivative grows polynomially, `(X i - m) f(X)` is
integrable. -/
private theorem integrable_sub_mul_comp_of_le_pow {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ)
    {f : (ι → ℝ) → ℝ} (hdiff : Differentiable ℝ f) {C : ℝ} {k : ℕ}
    (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (i : ι) (m : ℝ) :
    Integrable (fun ω => (X ω i - m) * f (X ω)) μ := by
  have hP := hX.isProbabilityMeasure
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hdf 0)
  have hXi_ae : AEMeasurable (fun ω => X ω i) μ :=
    (hX.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)).aemeasurable
  refine Integrable.mono'
    ((integrable_one_add_norm_pow_of_memLp (fun p hp => hX.memLp hp) (k + 2)).const_mul
      ((1 + |m|) * (|f 0| + C)))
    ((hXi_ae.sub_const m).aestronglyMeasurable.mul
      (hdiff.continuous.comp_aestronglyMeasurable hX.aemeasurable.aestronglyMeasurable))
    (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  have hXi : |X ω i| ≤ ‖X ω‖ := by simpa using norm_le_pi_norm (X ω) i
  have h1 : |X ω i - m| ≤ (1 + |m|) * (1 + ‖X ω‖) := by
    have := abs_sub (X ω i) m
    nlinarith [abs_nonneg m, norm_nonneg (X ω)]
  have h2 : |f (X ω)| ≤ (|f 0| + C) * (1 + ‖X ω‖) ^ (k + 1) := by
    have h := abs_le_of_norm_fderiv_le_pow hdiff hdf (X ω)
    have h3 : 1 ≤ (1 + ‖X ω‖) ^ (k + 1) := one_le_pow₀ (by linarith [norm_nonneg (X ω)])
    nlinarith [abs_nonneg (f 0)]
  calc |X ω i - m| * |f (X ω)|
      ≤ ((1 + |m|) * (1 + ‖X ω‖)) * ((|f 0| + C) * (1 + ‖X ω‖) ^ (k + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (1 + |m|) * (|f 0| + C) * (1 + ‖X ω‖) ^ (k + 2) := by ring

/-- **Gaussian integration by parts** (Stein's identity, covariance form) for `f` of class `C¹`
whose derivative grows at most polynomially, `‖Df(x)‖ ≤ C (1 + ‖x‖)^k`:
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`.
[Vershynin2018, Lemma 7.2.5]; stated there for a standard Gaussian, here any mean and any
covariance, possibly singular. `‖x‖` is the sup norm of `ι → ℝ`; any norm gives the same class.
Both integrands are integrable (Gaussian moments of every order), so the identity is never
between junk values. Proof: the route of
`integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw`, whose
one-dimensional step `integral_mul_eq_integral_deriv_gaussianReal_one` takes only integrability;
the bounded derivative is used there only for the growth and `L²` bounds, which polynomial growth
replaces through `memLp_id_gaussianReal` and `HasGaussianLaw.memLp`.
Result: gaussian-integration-by-parts -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} {k : ℕ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ := by
  have hP := hX.isProbabilityMeasure
  have hXj : ∀ j, HasGaussianLaw (fun ω => X ω j) μ := fun j =>
    hX.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)
  have hXm : ∀ j, MemLp (fun ω => X ω j) 2 μ := fun j => (hXj j).memLp_two
  have hXae : AEMeasurable X μ := hX.aemeasurable
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hdf 0)
  have hpow : ∀ j : ℕ, Integrable (fun ω => (1 + ‖X ω‖) ^ j) μ := fun j =>
    integrable_one_add_norm_pow_of_memLp (fun p hp => hX.memLp hp) j
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
  have hF1i : Integrable (fun ω => F1 (X ω i, W ω)) μ := by
    simp only [hF1, hXW]
    exact integrable_sub_mul_comp_of_le_pow hX hdiff hdf i m
  have hDb : ∀ (v : ι → ℝ) ω, ‖fderiv ℝ f (X ω) v‖ ≤ C * ‖v‖ * (1 + ‖X ω‖) ^ k := fun v ω =>
    ((fderiv ℝ f _).le_opNorm v).trans (by
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right (hdf _) (norm_nonneg v))
  have hF2i : Integrable (fun ω => F2 (X ω i, W ω)) μ :=
    Integrable.mono' ((hpow k).const_mul (C * ‖a‖))
      (hF2c.comp_aestronglyMeasurable (hUae.prodMk hWae).aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa only [hF2, hXW] using hDb a ω)
  -- the one-dimensional identity in the `X i` direction, for each value of `W`
  have hinner : ∀ w : ι → ℝ, ∫ u, F1 (u, w) ∂(μ.map fun ω => X ω i)
      = σ2 * ∫ u, F2 (u, w) ∂(μ.map fun ω => X ω i) := by
    intro w
    have h := integral_sub_mul_comp_smul_add_eq_gaussianReal_of_le_pow m σ2.toNNReal hdiff hdf
      a w
    rw [hσnn] at h
    rw [hmapU]
    exact h
  have hfa : ∀ x, fderiv ℝ f x a = ∑ j, a j * fderiv ℝ f x (Pi.single j 1) := fun x =>
    apply_eq_sum_mul_apply_single _ a
  have hDi : ∀ j, Integrable (fun ω => fderiv ℝ f (X ω) (Pi.single j 1)) μ := fun j =>
    Integrable.mono' ((hpow k).const_mul (C * ‖(Pi.single j 1 : ι → ℝ)‖))
      ((hdfc.clm_apply continuous_const).comp_aestronglyMeasurable hXae.aestronglyMeasurable)
      (ae_of_all _ fun ω => hDb _ ω)
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
