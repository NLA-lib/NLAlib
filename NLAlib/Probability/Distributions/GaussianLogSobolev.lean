/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.GaussianLogSobolevOneDim
public import NLAlib.Probability.EntropyTensorization
public import NLAlib.Probability.LogSobolev

/-!
# Gross's logarithmic Sobolev inequality

For the standard Gaussian, $\operatorname{Ent}(g^2) \le 2\, \mathbb{E}\|\nabla g\|^2$ for every
$C^1$ function $g$ with $g^2$ and $\|\nabla g\|^2$ integrable, where
$\operatorname{Ent}(f) = \mathbb{E}[f \log f] - \mathbb{E} f \log \mathbb{E} f$ is the entropy
(`NLAlib.entropy`); then $g^2 \log g^2$ is integrable too, so the entropy is not a junk value. The
one-dimensional inequality is proved first and tensorized. The standard Gaussian on a Euclidean
space therefore satisfies `NLAlib.HasLogSobolev` with constant $1$.

## Main results

* `NLAlib.entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal`: Gross's inequality on
  $\mathbb{R}$.
* `NLAlib.entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian`: on a Euclidean space.
* `NLAlib.hasLogSobolev_stdGaussian`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 5.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace NLAlib
private lemma norm_fderiv_sq_eq (g : ℝ → ℝ) (x : ℝ) : ‖fderiv ℝ g x‖ ^ 2 = deriv g x ^ 2 := by
  rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs]

/-! ### From compact support to the integrable case on the line -/

/-- Gross's inequality on $\mathbb{R}$ for $g$ with $g^2$, $g^2 \log g^2$ and $g'^2$ integrable,
from the compactly supported case by a smooth cutoff $g\, \chi(\cdot / (n + 1))$ and dominated
convergence. -/
private lemma entropy_sq_le_gaussianReal_of_integrable {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 := by
  obtain ⟨c, K, hc_contDiff, hc_supp, hc01, hc_deriv_bound, hc_one⟩ :=
    exists_seq_contDiff_hasCompactSupport_eventuallyEq_one (E := ℝ)
  replace hc_deriv_bound (n : ℕ) (x : ℝ) : |deriv (c n) x| ≤ K := by
    rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]
    exact hc_deriv_bound n x
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  let gn : ℕ → ℝ → ℝ := fun n x => g x * c n x
  have hgn_contDiff : ∀ n, ContDiff ℝ 1 (gn n) := fun n => hg.mul (hc_contDiff n)
  have hgn_deriv_sq : ∀ n x, deriv (gn n) x ^ 2 ≤ 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2 := by
    intro n x
    have hd : deriv (gn n) x = deriv g x * c n x + g x * deriv (c n) x :=
      ((hgd x).hasDerivAt.mul (((hc_contDiff n).differentiable one_ne_zero) x).hasDerivAt).deriv
    rw [hd]
    obtain ⟨h0, h1⟩ := hc01 n x
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    have e1 : (deriv g x * c n x) ^ 2 ≤ deriv g x ^ 2 := by
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (deriv g x))]
    have hd2 : deriv (c n) x ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hc_deriv_bound n x) 2
    have e2 : (g x * deriv (c n) x) ^ 2 ≤ K ^ 2 * g x ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    nlinarith [sq_nonneg (deriv g x * c n x - g x * deriv (c n) x)]
  -- pointwise eventual equality
  have hev : ∀ x, ∀ᶠ n in atTop, gn n x = g x ∧ deriv (gn n) x = deriv g x := by
    intro x
    filter_upwards [hc_one x] with n hn
    have : gn n =ᶠ[𝓝 x] g := hn.mono fun y hy => by simp only [gn, hy, mul_one]
    exact ⟨this.eq_of_nhds, this.deriv_eq⟩
  have hineq : ∀ n, entropy (gaussianReal 0 1) (fun x => gn n x ^ 2) ≤
      2 * ∫ x, deriv (gn n) x ^ 2 ∂gaussianReal 0 1 := fun n =>
    entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal_of_hasCompactSupport (hgn_contDiff n)
      (hc_supp n).mul_left
  have hgn_cont : ∀ n, Continuous (gn n) := fun n => (hgn_contDiff n).continuous
  have hconst : ∀ {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}, (∀ x, ∀ᶠ n in atTop, F n x = f x) →
      ∀ᵐ x ∂gaussianReal 0 1, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := fun h =>
    ae_of_all _ fun x => tendsto_const_nhds.congr' ((h x).mono fun n hn => hn.symm)
  have L1 : Tendsto (fun n => ∫ x, gn n x ^ 2 ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, g x ^ 2 ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => g x ^ 2)
      (fun n => ((hgn_cont n).pow 2).aestronglyMeasurable) hg2 (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    obtain ⟨h0, h1⟩ := hc01 n x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [gn, mul_pow]
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (g x))]
  have L2 : Tendsto (fun n => ∫ x, gn n x ^ 2 * Real.log (gn n x ^ 2) ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x ^ 2 * Real.log (g x ^ 2)| + g x ^ 2)
      (fun n => (Real.continuous_mul_log.comp ((hgn_cont n).pow 2)).aestronglyMeasurable)
      (hglog.abs.add hg2) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    obtain ⟨h0, h1⟩ := hc01 n x
    rw [Real.norm_eq_abs, show gn n x ^ 2 = g x ^ 2 * c n x ^ 2 by simp only [gn, mul_pow]]
    exact Real.abs_mul_mul_log_mul_le (sq_nonneg _) (sq_nonneg _) (by nlinarith)
  have L3 : Tendsto (fun n => ∫ x, deriv (gn n) x ^ 2 ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, deriv g x ^ 2 ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2)
      (fun n => ((measurable_deriv _).pow_const 2).aestronglyMeasurable)
      ((hdg.const_mul 2).add (hg2.const_mul _)) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgn_deriv_sq n x
  exact le_of_tendsto_of_tendsto (L2.sub ((Real.continuous_mul_log.tendsto _).comp L1))
    (L3.const_mul 2) (Eventually.of_forall hineq)

/-! ### Bounded test functions -/

/-- A bounded $C^1$ function with bounded derivative has $g^2$, $g^2 \log g^2$ and
$\|\nabla g\|^2$ integrable under a finite measure. -/
private lemma integrable_of_abs_le_of_norm_fderiv_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F] {ν : Measure F}
    [IsFiniteMeasure ν] {g : F → ℝ} (hg : ContDiff ℝ 1 g) {M M' : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hM' : ∀ x, ‖fderiv ℝ g x‖ ≤ M') :
    Integrable (fun x => g x ^ 2) ν ∧ Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) ν ∧
      Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν := by
  have h2 (x : F) : g x ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  refine ⟨?_, ?_, ?_⟩
  · refine Integrable.of_bound (hg.continuous.pow 2).aestronglyMeasurable (M ^ 2)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h2 x
  · refine Integrable.of_bound
      (Real.continuous_mul_log.comp (hg.continuous.pow 2)).aestronglyMeasurable
      ((M ^ 2) ^ 2 + 1) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (Real.abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
    have := pow_le_pow_left₀ (sq_nonneg _) (h2 x) 2
    linarith
  · refine Integrable.of_bound ((hg.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
      (M' ^ 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM' x) 2

/-- The standard Gaussian on $\mathbb{R}$ satisfies a logarithmic Sobolev inequality with constant
$1$, from the case where $g^2 \log g^2$ is integrable. -/
private lemma hasLogSobolev_gaussianReal : HasLogSobolev (gaussianReal 0 1) 1 := by
  refine ⟨fun g hg ⟨M, hM⟩ ⟨M', hM'⟩ => ?_⟩
  obtain ⟨h2, hlog, hd⟩ :=
    integrable_of_abs_le_of_norm_fderiv_le (ν := gaussianReal 0 1) hg hM hM'
  rw [NNReal.coe_one, mul_one]
  simp only [norm_fderiv_sq_eq] at hd ⊢
  exact entropy_sq_le_gaussianReal_of_integrable hg h2 hlog hd

/-! ### Gross's inequality on the line -/

/-- $g^2 \log g^2$ is integrable for the standard Gaussian on $\mathbb{R}$ when $g$ is $C^1$ with
$g^2$ and $g'^2$ integrable. -/
theorem integrable_sq_mul_log_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (gaussianReal 0 1) :=
  hasLogSobolev_gaussianReal.integrable_sq_mul_log_sq hg hg2
    (by simpa only [norm_fderiv_sq_eq] using hdg)

/-- **Gross's logarithmic Sobolev inequality** on $\mathbb{R}$:
$\operatorname{Ent}(g^2) \le 2\, \mathbb{E}[g'^2]$ for the standard Gaussian, for $g$ of class
$C^1$ with $g^2$ and $g'^2$ integrable.
[BoucheronLugosiMassart2013, §5.3, Theorem 5.4], specialized to one coordinate. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 :=
  entropy_sq_le_gaussianReal_of_integrable hg hg2 (integrable_sq_mul_log_sq_gaussianReal hg hg2 hdg)
    hdg

/-! ### Tensorization and transport to a Euclidean space -/

/-- Gross's inequality for the standard Gaussian on `ι → ℝ`, with $G^2 \log G^2$ integrable:
$\operatorname{Ent}(G^2) \le 2\, \mathbb{E} \sum_i (\partial_i G)^2$. -/
private lemma entropy_sq_le_gaussianVector {ι : Type*} [Fintype ι] [DecidableEq ι] {G : (ι → ℝ) → ℝ}
    (hG : ContDiff ℝ 1 G) (hG2 : Integrable (fun x => G x ^ 2) (gaussianVector ι))
    (hGlog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) (gaussianVector ι))
    (hdG : Integrable (fun x => ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2) (gaussianVector ι)) :
    entropy (gaussianVector ι) (fun x => G x ^ 2) ≤
      2 * ∫ x, ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2 ∂gaussianVector ι := by
  set P := gaussianVector ι with hP
  have hDi : ∀ i, Integrable (fun x => fderiv ℝ G x (Pi.single i 1) ^ 2) P := by
    intro i
    refine hdG.mono' ((((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow
      2).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j => fderiv ℝ G x (Pi.single j 1) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  refine (entropy_pi_le_sum (fun _ : ι => gaussianReal 0 1) (f := fun x => G x ^ 2)
    (hG.continuous.pow 2).measurable (fun x => sq_nonneg _) hG2 hGlog).trans ?_
  rw [integral_finsetSum _ fun i _ => hDi i, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hae : ∀ᵐ x ∂P, entropy (gaussianReal 0 1) (fun y => G (Function.update x i y) ^ 2) ≤
      2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2 ∂gaussianReal 0 1 := by
    filter_upwards [ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i hG2,
      ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)] with x h1 h2
    have hd : deriv (fun t => G (Function.update x i t)) =
        fun t => fderiv ℝ G (Function.update x i t) (Pi.single i 1) := funext fun t =>
      (((hG.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t)).deriv
    have := entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal
      (g := fun t => G (Function.update x i t)) (hG.comp (contDiff_update 1 x i)) h1
      (by rw [hd]; exact h2)
    rwa [hd] at this
  have hR : Integrable (fun x => 2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2
      ∂gaussianReal 0 1) P :=
    (integrable_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)).const_mul 2
  calc _ ≤ ∫ x, 2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2
        ∂gaussianReal 0 1 ∂P := by
        by_cases hE : Integrable
          (fun x => entropy (gaussianReal 0 1) (fun y => G (Function.update x i y) ^ 2)) P
        · exact integral_mono_ae hE hR hae
        · rw [integral_undef hE]
          exact integral_nonneg fun x =>
            mul_nonneg zero_le_two (integral_nonneg fun t => sq_nonneg _)
    _ = 2 * ∫ x, fderiv ℝ G x (Pi.single i 1) ^ 2 ∂P := by
        rw [integral_const_mul,
          integral_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Gross's inequality for the standard Gaussian on a Euclidean space, with $g^2 \log g^2$
integrable: transport of the product case through an orthonormal basis. -/
private lemma entropy_sq_le_stdGaussian_of_integrable {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤ 2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E := by
  set b := stdOrthonormalBasis ℝ E
  let L : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (b i)
  have hL : (⇑L : (Fin (Module.finrank ℝ E) → ℝ) → E) = fun x => ∑ i, x i • b i := by
    funext x; simp [L]
  have hstd : stdGaussian E = (gaussianVector (Fin (Module.finrank ℝ E))).map L := by
    rw [hL]; rfl
  have hLm : AEMeasurable L (gaussianVector (Fin (Module.finrank ℝ E))) :=
    L.continuous.measurable.aemeasurable
  have hfd : ∀ x, fderiv ℝ (fun x => g (L x)) x = (fderiv ℝ g (L x)).comp L := fun x =>
    (((hg.differentiable one_ne_zero) (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hen : ∀ x, ∑ i, fderiv ℝ (fun x => g (L x)) x (Pi.single i 1) ^ 2 =
      ‖fderiv ℝ g (L x)‖ ^ 2 := fun x => by
    have hLs : ∀ i, L (Pi.single i 1) = b i := fun i => by
      rw [hL]; simp [Pi.single_apply]
    simp only [hfd, ContinuousLinearMap.comp_apply, hLs]
    exact (b.norm_dual _).symm
  have hc2 : Continuous (fun x => g x ^ 2) := hg.continuous.pow 2
  have hclog : Continuous (fun x => g x ^ 2 * Real.log (g x ^ 2)) :=
    Real.continuous_mul_log.comp hc2
  have hcd : Continuous (fun x => ‖fderiv ℝ g x‖ ^ 2) :=
    ((hg.continuous_fderiv one_ne_zero).norm.pow 2)
  rw [hstd] at hg2 hglog hdg ⊢
  rw [integrable_map_measure hc2.aestronglyMeasurable hLm] at hg2
  rw [integrable_map_measure hclog.aestronglyMeasurable hLm] at hglog
  rw [integrable_map_measure hcd.aestronglyMeasurable hLm] at hdg
  simp only [Function.comp_def] at hg2 hglog hdg
  have key := entropy_sq_le_gaussianVector (G := fun x => g (L x)) (hg.comp L.contDiff) hg2 hglog
    (by simpa only [hen] using hdg)
  simp only [hen] at key
  rw [entropy, integral_map hLm hclog.aestronglyMeasurable,
    integral_map hLm hc2.aestronglyMeasurable, integral_map hLm hcd.aestronglyMeasurable]
  exact key

/-- The standard Gaussian satisfies a logarithmic Sobolev inequality with constant $1$. -/
theorem hasLogSobolev_stdGaussian : HasLogSobolev (stdGaussian E) 1 := by
  refine ⟨fun g hg ⟨M, hM⟩ ⟨M', hM'⟩ => ?_⟩
  obtain ⟨h2, hlog, hd⟩ :=
    integrable_of_abs_le_of_norm_fderiv_le (ν := stdGaussian E) hg hM hM'
  rw [NNReal.coe_one, mul_one]
  exact entropy_sq_le_stdGaussian_of_integrable hg h2 hlog hd

/-- $g^2 \log g^2$ is integrable for the standard Gaussian on a Euclidean space when $g$ is $C^1$
with $g^2$ and $\|\nabla g\|^2$ integrable. -/
theorem integrable_sq_mul_log_sq_stdGaussian {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (stdGaussian E) :=
  hasLogSobolev_stdGaussian.integrable_sq_mul_log_sq hg hg2 hdg

/-- **Gross's logarithmic Sobolev inequality** for the standard Gaussian on a Euclidean space:
$\operatorname{Ent}(g^2) \le 2\, \mathbb{E}\|\nabla g\|^2$ for $g$ of class $C^1$ with $g^2$ and
$\|\nabla g\|^2$ integrable ([BoucheronLugosiMassart2013, Theorem 5.4]).
Result: gaussian-log-sobolev -/
theorem entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤
      2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E :=
  entropy_sq_le_stdGaussian_of_integrable hg hg2 (integrable_sq_mul_log_sq_stdGaussian hg hg2 hdg)
    hdg

end NLAlib
