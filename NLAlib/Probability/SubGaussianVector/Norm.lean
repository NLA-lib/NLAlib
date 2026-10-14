/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic

/-!
# The squared norm of a sub-Gaussian random vector

For a real sub-Gaussian vector `X` with proxy `c`, `E exp (θ ‖X‖²)` is at most the Laplace
transform of `c χ²_n`, and the upper tail of `‖X‖²` is the Laurent–Massart bound
`P(c (n + 2√(n t) + 2t) ≤ ‖X‖²) ≤ e^{-t}` (Hsu, Kakade and Zhang). For independent sub-Gaussian
coordinates, the two-sided tail of `‖X‖²` about its mean is Bernstein's inequality for the
centred squares.

The statements are over `ℝ`: the proofs linearise with a standard Gaussian vector of the same
dimension (`NLAlib.lintegral_exp_mul_dotProduct_gaussianVector`), which exists over `ℝ` only in
this library for now; the complex versions are the real ones in dimension `2 n`.

## Main results

* `NLAlib.IsSubgaussianVector.integral_exp_mul_norm_sq_le`: `E exp (θ‖X‖²) ≤ (1 - 2θc)^{-n/2}`.
* `NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le`: the upper tail of `‖X‖²`.
* `NLAlib.measureReal_abs_norm_sq_sub_integral_ge_le`: the two-sided tail for independent
  coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {c : ℝ≥0}

private lemma norm_sq_eq (x : n → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, x i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- The Laplace transform of `χ²_n`, as an upper bound. -/
private lemma lintegral_exp_mul_norm_sq_gaussianVector_le {a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * a < 1) :
    ∫⁻ g, ENNReal.ofReal (rexp (a * ‖WithLp.toLp 2 g‖ ^ 2)) ∂(gaussianVector n) ≤
      ENNReal.ofReal ((1 - 2 * a) ^ (-(Fintype.card n / 2 : ℝ))) := by
  have hg : HasSubgaussianMGF id 1 (gaussianReal 0 1) :=
    hasSubgaussianMGF_of_hasLaw_gaussianReal ⟨aemeasurable_id, Measure.map_id⟩
  have ha' : 2 * a * ((1 : ℝ≥0) : ℝ) < 1 := by simpa using ha
  have hint : ∀ _i : n, Integrable (fun x : ℝ => rexp (a * x ^ 2)) (gaussianReal 0 1) :=
    fun _ => hg.integrable_exp_mul_sq ha'
  have hprod : ∀ g : n → ℝ, rexp (a * ‖WithLp.toLp 2 g‖ ^ 2) = ∏ i, rexp (a * g i ^ 2) := by
    intro g
    rw [norm_sq_eq, Finset.mul_sum, exp_sum]
  simp only [hprod]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hint)
    (ae_of_all _ fun _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_fintype_prod_eq_prod (fun _ x => rexp (a * x ^ 2))]
  have h2a : 0 < 1 - 2 * a := by linarith
  calc ∏ _i : n, ∫ x, rexp (a * x ^ 2) ∂(gaussianReal 0 1) ≤ ∏ _i : n, 1 / √(1 - 2 * a) :=
        Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (exp_pos _).le)
          fun _ _ => by simpa using hg.integral_exp_mul_sq_le ha0 ha'
    _ = (1 - 2 * a) ^ (-(Fintype.card n / 2 : ℝ)) := by
      rw [Finset.prod_const, Finset.card_univ, one_div, sqrt_eq_rpow, ← rpow_neg h2a.le,
        ← rpow_natCast, ← rpow_mul h2a.le]
      ring_nf

namespace IsSubgaussianVector

private lemma lintegral_exp_mul_norm_sq_le (h : IsSubgaussianVector X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) ∂μ ≤
      ENNReal.ofReal ((1 - 2 * θ * c) ^ (-(Fintype.card n / 2 : ℝ))) := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  set s := √(2 * θ)
  have hs : s ^ 2 = 2 * θ := sq_sqrt (by linarith)
  have hpt : ∀ x : n → ℝ, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (rexp (s * (x ⬝ᵥ g))) ∂(gaussianVector n) := by
    intro x
    rw [lintegral_exp_mul_dotProduct_gaussianVector, hs]
    ring_nf
  have hXi : ∀ i, AEMeasurable (fun p : Ω × (n → ℝ) => X p.1 i) (μ.prod (gaussianVector n)) :=
    fun i => (aemeasurable_pi_iff.mp h.aemeasurable i).comp_fst
  have hdot : AEMeasurable (fun p : Ω × (n → ℝ) => X p.1 ⬝ᵥ p.2) (μ.prod (gaussianVector n)) :=
    Finset.aemeasurable_fun_sum _ fun i _ =>
      (hXi i).mul ((measurable_pi_apply i).comp measurable_snd).aemeasurable
  have hmeas : AEMeasurable (Function.uncurry fun ω (g : n → ℝ) =>
      ENNReal.ofReal (rexp (s * (X ω ⬝ᵥ g)))) (μ.prod (gaussianVector n)) :=
    (measurable_exp.comp_aemeasurable (hdot.const_mul s)).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (rexp (s * (X ω ⬝ᵥ g))) ∂(gaussianVector n) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (rexp (s * (X ω ⬝ᵥ g))) ∂μ ∂(gaussianVector n) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ g, ENNReal.ofReal (rexp ((θ * c) * ‖WithLp.toLp 2 g‖ ^ 2)) ∂(gaussianVector n) := by
        refine lintegral_mono fun g => ?_
        have hu := h.hasSubgaussianMGF g
        simp only [RCLike.re_to_real] at hu
        have heq : ∫⁻ ω, ENNReal.ofReal (rexp (s * (X ω ⬝ᵥ g))) ∂μ =
            ENNReal.ofReal (mgf (fun ω => g ⬝ᵥ X ω) μ s) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal (hu.integrable_exp_mul s)
            (ae_of_all _ fun _ => (exp_pos _).le)]
          simp only [dotProduct_comm g]
        rw [heq]
        refine ENNReal.ofReal_le_ofReal ((hu.mgf_le s).trans (exp_le_exp.mpr (le_of_eq ?_)))
        push_cast
        rw [hs]
        ring
    _ ≤ _ := by
        have h2 : 2 * θ * c = 2 * (θ * c) := by ring
        rw [h2]
        exact lintegral_exp_mul_norm_sq_gaussianVector_le (by positivity) (by linarith)

/-- The mean squared norm of a sub-Gaussian vector is at most `c n`. -/
theorem integral_norm_sq_le [IsProbabilityMeasure μ] (h : IsSubgaussianVector X c μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ ≤ c * Fintype.card n := by
  have hi : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ := fun i => by
    simpa only [RCLike.re_to_real] using h.hasSubgaussianMGF_re_apply i
  simp only [norm_sq_eq]
  rw [integral_finsetSum _ fun i _ => ((hi i).memLp 2).integrable_sq]
  calc ∑ i, ∫ ω, X ω i ^ 2 ∂μ ≤ ∑ _i : n, (c : ℝ) :=
        Finset.sum_le_sum fun i _ => (hi i).integral_sq_le
    _ = c * Fintype.card n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- `exp (θ ‖X‖²)` is integrable for a sub-Gaussian vector when `2 θ c < 1`. -/
theorem integrable_exp_mul_norm_sq (h : IsSubgaussianVector X c μ) {θ : ℝ}
    (hθ : 2 * θ * c < 1) : Integrable (fun ω => rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  have hcont : Continuous fun x : n → ℝ => rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2) := by
    simp only [norm_sq_eq]
    fun_prop
  have hm : AEStronglyMeasurable (fun ω => rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ :=
    hcont.comp_aestronglyMeasurable h.aemeasurable.aestronglyMeasurable
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · refine Integrable.mono' (integrable_const 1) hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hθ0 (sq_nonneg _)
  · refine ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (exp_pos _).le)).mpr ?_⟩
    exact (h.lintegral_exp_mul_norm_sq_le hθ0.le hθ).trans_lt ENNReal.ofReal_lt_top

/-- `E exp (θ ‖X‖²) ≤ (1 - 2θc)^{-n/2}` for a sub-Gaussian vector and `0 ≤ θ < 1 / (2c)`: the
Laplace transform of `c χ²_n`, by Gaussian linearisation. -/
theorem integral_exp_mul_norm_sq_le (h : IsSubgaussianVector X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ ≤
      (1 - 2 * θ * c) ^ (-(Fintype.card n / 2 : ℝ)) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (exp_pos _).le)
    (h.integrable_exp_mul_norm_sq hθ).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (h.lintegral_exp_mul_norm_sq_le hθ0 hθ)

private lemma measure_norm_sq_ge_le_aux (h : IsSubgaussianVector X c μ) (hc0 : (0 : ℝ) < c)
    {t : ℝ} (ht : 0 < t) (hd : (0 : ℝ) < Fintype.card n) :
    μ.real {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
      ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤ rexp (-t) := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  set d : ℝ := (Fintype.card n : ℝ)
  set a := √(t / d)
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have ha2 : a ^ 2 = t / d := sq_sqrt (by positivity)
  have hta : t = a ^ 2 * d := by rw [ha2]; field_simp
  set ε := 2 * a + 2 * a ^ 2
  have hε : 0 ≤ ε := by positivity
  have hsqrt : √(d * t) = d * a := by
    rw [show d * t = d ^ 2 * (t / d) by field_simp, sqrt_mul (by positivity), sqrt_sq hd.le]
  have hthr : c * (d + 2 * √(d * t) + 2 * t) = c * (1 + ε) * d := by
    rw [hsqrt, hta]
    ring
  rw [hthr]
  set θ := ε / (2 * c * (1 + ε))
  have hθ0 : 0 ≤ θ := by positivity
  have h2θ : 1 - 2 * θ * c = (1 + ε)⁻¹ := by
    simp only [θ]
    field_simp
    ring
  have hθc : 2 * θ * c < 1 := by
    have : 0 < (1 + ε)⁻¹ := by positivity
    linarith
  refine (measure_ge_le_exp_mul_mgf _ hθ0 (h.integrable_exp_mul_norm_sq hθc)).trans ?_
  have hmgf : mgf (fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) μ θ ≤ (1 - 2 * θ * c) ^ (-(d / 2)) :=
    h.integral_exp_mul_norm_sq_le hθ0 hθc
  have h1ε : 0 < 1 + ε := by positivity
  have hlog : log (1 + ε) ≤ 2 * a := by
    rw [log_le_iff_le_exp h1ε]
    have := quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by positivity)
    simp only [ε]
    nlinarith
  calc rexp (-θ * (c * (1 + ε) * d)) * mgf (fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) μ θ
      ≤ rexp (-θ * (c * (1 + ε) * d)) * (1 - 2 * θ * c) ^ (-(d / 2)) := by gcongr
    _ = rexp (-(d / 2) * (ε - log (1 + ε))) := by
      rw [h2θ, inv_rpow h1ε.le, ← rpow_neg h1ε.le, neg_neg, rpow_def_of_pos h1ε, ← exp_add]
      congr 1
      simp only [θ]
      field_simp
      ring
    _ ≤ rexp (-t) := by
      refine exp_le_exp.mpr ?_
      rw [hta]
      simp only [ε]
      nlinarith [mul_le_mul_of_nonneg_left hlog hd.le]

/-- **The upper tail of `‖X‖²`** for a sub-Gaussian vector (Hsu, Kakade and Zhang 2012,
Theorem 2.1 with `A = 1`; for a standard Gaussian vector this is Laurent and Massart's bound).
`c ≠ 0` is needed for the non-strict event: with `c = 0` the vector is `0` almost surely and the
event is everything.
Result: hsu-kakade-zhang -/
theorem measure_norm_sq_ge_le (h : IsSubgaussianVector X c μ) (hc : c ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
      ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤ rexp (-t) := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  rcases ht.eq_or_lt with rfl | htpos
  · have huniv := h.integral_exp_mul_norm_sq_le le_rfl (by simp)
    simp only [zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one, mul_zero, sub_zero,
      one_rpow] at huniv
    rw [neg_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans huniv
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card n)).eq_or_lt with hd | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hd.symm)
    have hset : {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
        ‖WithLp.toLp 2 (X ω)‖ ^ 2} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, norm_sq_eq,
        Finset.univ_eq_empty, Finset.sum_empty, ← hd, zero_mul, sqrt_zero, mul_zero, zero_add]
      positivity
    rw [hset, measureReal_empty]
    positivity
  exact measure_norm_sq_ge_le_aux h hc0 htpos hd

end IsSubgaussianVector

/-- The two-sided tail of `‖X‖²` about its mean for independent sub-Gaussian coordinates:
Bernstein's inequality for the centred squares, whose variance proxy and scale are `32 c²` and
`4 c`. -/
theorem measureReal_abs_norm_sq_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (X ω')‖ ^ 2 ∂μ|} ≤
      2 * rexp (-min (t ^ 2 / (2 * (Fintype.card n * (32 * c ^ 2)))) (t / (2 * (4 * c)))) := by
  have := hind.isProbabilityMeasure
  have hint : ∀ i, Integrable (fun ω => X ω i ^ 2) μ := fun i => ((h i).memLp 2).integrable_sq
  have hind' : iIndepFun (fun i ω => X ω i ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ) μ :=
    hind.comp (fun i x => x ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ) fun i => by fun_prop
  have hsum := (HasSubexponentialMGF.sum_of_iIndepFun hind' (s := Finset.univ)
    fun i _ => (h i).hasSubexponentialMGF_sq_sub_integral).mono le_rfl
      (Finset.sup_le fun i _ => le_rfl)
  have hfun : ∀ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (X ω')‖ ^ 2 ∂μ =
      ∑ i, (X ω i ^ 2 - ∫ ω', X ω' i ^ 2 ∂μ) := by
    intro ω
    simp only [norm_sq_eq]
    rw [integral_finsetSum _ fun i _ => hint i, Finset.sum_sub_distrib]
  have hv : ((∑ _i : n, 32 * c ^ 2 : ℝ≥0) : ℝ) = Fintype.card n * (32 * (c : ℝ) ^ 2) := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hb : ((4 * c : ℝ≥0) : ℝ) = 4 * c := by push_cast; ring
  have key := hsum.measure_abs_ge_le ht
  rw [hv, hb] at key
  simp only [hfun]
  exact key

end NLAlib
