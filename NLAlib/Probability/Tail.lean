/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Gamma.Basic
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
public import NLAlib.ForMathlib.MeasureTheory.Measure.Real

/-!
# Tail probabilities and moments

Tail bounds in NLAlib are failure probabilities in $\mathbb{R}$, with non-strict events:
`μ.real {ω | t ≤ f ω} ≤ bound`. Mathlib's Chernoff bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` and Markov's inequality
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` already have this form; the union bound and the
complement are `MeasureTheory.measureReal_union_le`, `MeasureTheory.measureReal_biUnion_finset_le`
and `MeasureTheory.probReal_compl_eq_one_sub`. This file adds Markov's inequality in quotient
form, Chebyshev's inequality in $\mathbb{R}$, the two-sided tail, Markov's inequality off a
failure event, the passage from a tail bound to integrability and to a bound on the mean and on
the $p$-th moment, the moments of a variable with a sub-exponential tail (the named bound
`NLAlib.subexponentialMomentBound`, <!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)$, the layer-cake integral of the tail
$2e^{-\min(t^2/(2v),\, t/(2b))}$), the two-sided sub-exponential tail of a variable with
Dasgupta and Gupta's one-sided tails, Chernoff's bound inverted for a sub-gamma moment generating
function, and Jensen's inequality for a power of a sum of random variables.

## Main results

* `NLAlib.measureReal_ge_le_integral_div`: Markov's inequality.
* `NLAlib.measureReal_abs_ge_le_integral_rpow_div`: Markov's inequality for a moment.
* `NLAlib.measureReal_ge_le_variance_div_sq`: Chebyshev's inequality.
* `NLAlib.measureReal_abs_ge_le_add`: a two-sided tail is at most the sum of the one-sided tails.
* `NLAlib.measureReal_le_add_one_div`: Markov's inequality off a failure event, the step of
  every subspace-injection tail.
* `NLAlib.integrable_of_measureReal_ge_le`, `NLAlib.integral_le_of_measureReal_ge_le`: a
  nonnegative random variable with an integrable tail bound is integrable, and its mean is at most
  the integral of the bound.
* `NLAlib.integral_rpow_le_of_measureReal_ge_le`: the layer-cake bound for $p$-th moments.
* `NLAlib.integral_rpow_le_of_measureReal_ge_le_two_mul_exp`: the $p$-th moment of a variable
  with a sub-exponential tail, for every $p > 0$; `NLAlib.subexponentialMomentBound_le` is its
  readable form for $p \ge 2$.
* `NLAlib.measureReal_abs_div_sub_one_ge_le_two_mul_exp`: Dasgupta–Gupta tails on both sides
  give a two-sided sub-exponential tail, the input of the Gaussian and Haar JL moments.
* `NLAlib.measureReal_ge_le_exp_neg_of_mgf_le`: Chernoff's bound for a sub-gamma upper tail, with
  the exact constant.
* `NLAlib.integrable_rpow_sum`, `NLAlib.integral_rpow_sum_le`: a power $r \ge 1$ of a finite sum of
  nonnegative random variables is integrable, and weighted Jensen bounds its mean.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Markov's inequality** as a failure probability:
$$\mu\{t \le f\} \le \frac{\int f \, d\mu}{t}\,,$$
for $f$ integrable and nonnegative almost everywhere, and $t > 0$. Integrability is needed:
otherwise the Bochner integral $\int f \, d\mu$ is $0$.
[Vershynin2018, Proposition 1.2.4]; there for a probability measure, here any measure.
Result: markov-inequality -/
theorem measureReal_ge_le_integral_div {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ)
    {t : ℝ} (ht : 0 < t) : μ.real {ω | t ≤ f ω} ≤ (∫ ω, f ω ∂μ) / t := by
  rw [le_div_iff₀ ht, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hf0 hf t

/-- **Markov's inequality for a moment**:
$\mu\{t \le \lvert X\rvert\} \le (\int \lvert X\rvert^p \, d\mu) / t^p$ for real $t, p > 0$. Every
tail derived from a moment bound ends here. Integrability of $\lvert X\rvert^p$ is needed:
otherwise its integral is $0$. [Vershynin2018, Proposition 1.2.4], applied to the nonnegative
variable $\lvert X\rvert^p$; the source uses a probability measure, while this form permits any
measure with the stated integrability. -/
theorem measureReal_abs_ge_le_integral_rpow_div {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : Integrable (fun ω => |X ω| ^ p) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂μ) / t ^ p := by
  have hset : {ω | t ≤ |X ω|} = {ω | t ^ p ≤ |X ω| ^ p} := by
    ext ω
    exact (Real.rpow_le_rpow_iff ht.le (abs_nonneg _) hp).symm
  rw [hset]
  exact measureReal_ge_le_integral_div
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hX
    (Real.rpow_pos_of_pos ht p)

/-- **Chebyshev's inequality** as a failure probability: for a finite measure $\mu$, $X \in L^2$
and $t > 0$,
$$\mu\{t \le \lvert X - \mathbb{E} X\rvert\} \le \frac{\operatorname{Var} X}{t^2}\,,$$
with $\mathbb{E} X = \int X \, d\mu$.
[Vershynin2018, Corollary 1.2.5]; there for a probability measure, here any finite measure.
Result: chebyshev-inequality -/
theorem measureReal_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ variance X μ / t ^ 2 := by
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg t))
    (meas_ge_le_variance_div_sq hX ht)

/-- A two-sided tail is at most the sum of the upper and the lower tail:
$\mu\{t \le \lvert X\rvert\} \le \mu\{t \le X\} + \mu\{X \le -t\}$. -/
theorem measureReal_abs_ge_le_add (X : Ω → ℝ) (t : ℝ) :
    μ.real {ω | t ≤ |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := by
  have h : {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, le_neg]
  rw [h]
  exact measureReal_union_le _ _

/-- **Markov's inequality off a failure event**: if $\mu(G^c) \le \delta$, $M \ge 0$ is integrable
with mean $m$ (and vanishes when $m = 0$), and on $G$ the event $E$ forces $t m < M$, then for
$t > 0$
$$\mu(E) \le \delta + \frac{1}{t}\,.$$
The common step of the subspace-injection tails (`NLAlib.Regression.Oblivious`) and
the oblivious low-rank tails.
[Vershynin2018, Proposition 1.2.4]; the source is the basic Markov inequality for a probability
measure. This form adds the failure event by a union bound and includes the zero-mean case
under the stated vanishing assumption. -/
theorem measureReal_le_add_one_div [IsFiniteMeasure μ] {δ t : ℝ} {G E : Set Ω}
    (hG : μ.real Gᶜ ≤ δ) {M : Ω → ℝ} (hM0 : ∀ ω, 0 ≤ M ω) (hM : Integrable M μ) {m : ℝ}
    (hm : ∫ ω, M ω ∂μ = m) (hm0 : m = 0 → ∀ ω, M ω = 0) (ht : 0 < t)
    (hE : ∀ᵐ ω ∂μ, ω ∈ G → ω ∈ E → t * m < M ω) : μ.real E ≤ δ + 1 / t := by
  have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ Gᶜ ∪ {ω | t * m < M ω} := by
    filter_upwards [hE] with ω hω hωE
    by_cases hωG : ω ∈ G
    · exact Or.inr (hω hωG hωE)
    · exact Or.inl hωG
  have hF : μ.real {ω | t * m < M ω} ≤ 1 / t := by
    rcases eq_or_ne m 0 with h0 | h0
    · have he : {ω | t * m < M ω} = ∅ := by
        ext ω
        simp only [hm0 h0 ω, h0, mul_zero, lt_self_iff_false, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false]
      rw [he, measureReal_empty]
      positivity
    · have hm' : 0 < m := lt_of_le_of_ne (hm ▸ integral_nonneg hM0) (Ne.symm h0)
      calc μ.real {ω | t * m < M ω} ≤ μ.real {ω | t * m ≤ M ω} :=
            measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => hω.le)
        _ ≤ (∫ ω, M ω ∂μ) / (t * m) :=
            measureReal_ge_le_integral_div (ae_of_all _ hM0) hM (mul_pos ht hm')
        _ = 1 / t := by
            rw [hm]
            field_simp
  calc μ.real E ≤ μ.real (Gᶜ ∪ {ω | t * m < M ω}) := measureReal_mono_ae hae
    _ ≤ μ.real Gᶜ + μ.real {ω | t * m < M ω} := measureReal_union_le _ _
    _ ≤ δ + 1 / t := add_le_add hG hF

private theorem lintegral_ofReal_le_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤
      μ Set.univ * ENNReal.ofReal a + ENNReal.ofReal (∫ t in Set.Ioi a, F t) := by
  have hF0 : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact measureReal_nonneg.trans (htail t ht)
  rw [lintegral_eq_lintegral_meas_lt μ hf0 hf, ← Set.Ioc_union_Ioi_eq_Ioi ha,
    lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same,
    ofReal_integral_eq_lintegral_ofReal hF hF0]
  gcongr ?_ + ?_
  · calc ∫⁻ t in Set.Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Set.Ioc 0 a, μ Set.univ :=
          lintegral_mono fun _ => measure_mono (Set.subset_univ _)
      _ = μ Set.univ * ENNReal.ofReal a := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    calc μ {x | t < f x} ≤ μ {x | t ≤ f x} := measure_mono fun _ hx => le_of_lt (α := ℝ) hx
      _ = ENNReal.ofReal (μ.real {x | t ≤ f x}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (F t) := ENNReal.ofReal_le_ofReal (htail t ht)

private theorem integral_le_of_measureReal_ge_le_of_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  have hF0 : 0 ≤ ∫ t in Set.Ioi a, F t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => measureReal_nonneg.trans (htail t ht)
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 ha hF htail
  rw [measure_univ, one_mul, ← ENNReal.ofReal_add ha hF0] at hbound
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hF0) hbound

/-- On a finite measure space, a nonnegative random variable $f$ whose tail beyond $a$ is bounded
by a function $F$ integrable on $(a, \infty)$, $\mu\{t \le f\} \le F(t)$ for $t > a$, is
integrable. A bound on the strict tail $\{t < f\}$ follows from one on $\{t \le f\}$ by
monotonicity, so the hypothesis is stated in the non-strict form that tail theorems produce. -/
theorem integrable_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi a))
    (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) : Integrable f μ := by
  have hF' : IntegrableOn F (Set.Ioi (max a 0)) :=
    hF.mono_set (Set.Ioi_subset_Ioi (le_max_left a 0))
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 (le_max_right a 0) hF'
    fun t ht => htail t ((le_max_left a 0).trans_lt ht)
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf0).2 ?_⟩
  exact hbound.trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (measure_lt_top μ _) ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **The layer-cake bound**: under a probability measure, if $f \ge 0$ almost everywhere and
$\mathbb{P}[t \le f] \le F(t)$ for all $t > a$, with $F$ integrable on $(a, \infty)$, then
$$\mathbb{E} f \le a + \int_a^\infty F(t) \, dt\,.$$
Applied to $f^p$, whose tail at $t$ is the tail of $f$ at $t^{1/p}$, it bounds the moments of $f$.
Integrability of $f$ is `integrable_of_measureReal_ge_le`.
[Vershynin2018, Lemma 1.2.1] gives the tail integral identity. Splitting the integral at $a$ gives
this bound. -/
theorem integral_le_of_measureReal_ge_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  rcases le_or_gt 0 a with ha | ha
  · exact integral_le_of_measureReal_ge_le_of_nonneg hf hf0 ha hF htail
  have hF0 : IntegrableOn F (Set.Ioi 0) := hF.mono_set (Set.Ioi_subset_Ioi ha.le)
  have h0 := integral_le_of_measureReal_ge_le_of_nonneg hf hf0 le_rfl hF0
    fun t ht => htail t (ha.trans ht)
  have h1 : -a ≤ ∫ t in Set.Ioc a 0, F t := by
    have hle : ∫ _ in Set.Ioc a 0, (1 : ℝ) ≤ ∫ t in Set.Ioc a 0, F t := by
      refine setIntegral_mono_on (integrableOn_const (by simp))
        (hF.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
      refine le_trans (le_of_eq ?_) (htail t ht.1)
      rw [measureReal_def, measure_congr (ae_eq_univ.2 ?_), measure_univ, ENNReal.toReal_one]
      exact ae_iff.1 (hf0.mono fun ω hω => ht.2.trans hω)
    simpa [ha.le] using hle
  rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hF.mono_set Set.Ioc_subset_Ioi_self) hF0]
  linarith

/-! ### Moments from tails -/

/-- The **sub-exponential moment bound** <!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)$: for $p > 0$, the bound on the $p$-th moment of a
nonnegative variable whose tail is at most $2\exp(-\min(t^2/(2v), t/(2b)))$
(`NLAlib.integral_rpow_le_of_measureReal_ge_le_two_mul_exp`), the layer-cake integral of
$2e^{-t^2/(2v)} + 2e^{-t/(2b)}$ exactly. For $p \ge 2$ it is at most $2(vp)^{p/2} + 2(2bp)^{p}$
(`subexponentialMomentBound_le`, by $\Gamma(x) \le x^{x-1}$), a comparison that loses a factor
exponential in $p$, about $e^{p/2}/\sqrt{\pi p}$ and $e^{p}/\sqrt{2\pi p}$ on the two terms by
Stirling's formula; the literature's shape is $\|\cdot\|_{L^p} \lesssim \sqrt{vp} + bp$, with
unspecified constants. Consumers use
`subexponentialMomentBound_nonneg`, `subexponentialMomentBound_mono` and
`subexponentialMomentBound_le`. Junk: for $v < 0$ or $b < 0$ the real powers of negative numbers
are Lean's. -/
noncomputable irreducible_def subexponentialMomentBound (v b p : ℝ) : ℝ :=
  p * (2 * v) ^ (p / 2) * Real.Gamma (p / 2) + 2 * p * (2 * b) ^ p * Real.Gamma p

/-- The sub-exponential moment bound <!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)$ is nonnegative for $v, b, p \ge 0$. -/
theorem subexponentialMomentBound_nonneg {v b p : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    0 ≤ subexponentialMomentBound v b p := by
  rw [subexponentialMomentBound_def]
  have h1 : 0 ≤ Real.Gamma (p / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have h2 : 0 ≤ Real.Gamma p := Real.Gamma_nonneg_of_nonneg hp
  positivity

/-- The sub-exponential moment bound <!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)$ is monotone in $v \ge 0$ and $b \ge 0$, for
$p \ge 0$. -/
theorem subexponentialMomentBound_mono {v v' b b' p : ℝ} (hv : 0 ≤ v) (hvv' : v ≤ v')
    (hb : 0 ≤ b) (hbb' : b ≤ b') (hp : 0 ≤ p) :
    subexponentialMomentBound v b p ≤ subexponentialMomentBound v' b' p := by
  rw [subexponentialMomentBound_def, subexponentialMomentBound_def]
  have h1 : 0 ≤ Real.Gamma (p / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have h2 : 0 ≤ Real.Gamma p := Real.Gamma_nonneg_of_nonneg hp
  gcongr

/-- The readable comparison: for $p \ge 2$ and
$v, b \ge 0$, <!-- value subexponentialMomentBound v b p -->
$$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p) \le 2(vp)^{p/2} + 2(2bp)^{p}\,,$$
by $\Gamma(x) \le x^{x-1}$ for $x \ge 1$ (`Real.Gamma_le_rpow_sub_one`). It loses a factor
exponential in $p$; every size form inverts through it, so a Stirling-sharp comparison would
lower their constants without a statement change. -/
theorem subexponentialMomentBound_le {v b p : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 2 ≤ p) :
    subexponentialMomentBound v b p ≤ 2 * (v * p) ^ (p / 2) + 2 * (2 * b * p) ^ p := by
  rw [subexponentialMomentBound_def]
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p / 2 := by positivity
  have hG1 : Real.Gamma (p / 2) ≤ (p / 2) ^ (p / 2 - 1) :=
    Real.Gamma_le_rpow_sub_one (by linarith)
  have hG2 : Real.Gamma p ≤ p ^ (p - 1) := Real.Gamma_le_rpow_sub_one (by linarith)
  have e1 : p * (2 * v) ^ (p / 2) * (p / 2) ^ (p / 2 - 1) = 2 * (v * p) ^ (p / 2) := by
    rw [Real.rpow_sub_one hp2.ne', show v * p = 2 * v * (p / 2) by ring,
      Real.mul_rpow (by positivity) hp2.le]
    field_simp
  have e2 : 2 * p * (2 * b) ^ p * p ^ (p - 1) = 2 * (2 * b * p) ^ p := by
    rw [Real.rpow_sub_one hp0.ne', Real.mul_rpow (by positivity) hp0.le]
    field_simp
  calc p * (2 * v) ^ (p / 2) * Real.Gamma (p / 2) + 2 * p * (2 * b) ^ p * Real.Gamma p
      ≤ p * (2 * v) ^ (p / 2) * (p / 2) ^ (p / 2 - 1) + 2 * p * (2 * b) ^ p * p ^ (p - 1) := by
        gcongr
    _ = 2 * (v * p) ^ (p / 2) + 2 * (2 * b * p) ^ p := by rw [e1, e2]

/-- The inversion step of every JL-moment size form: for $p \ge 2$, $v, b \ge 0$,
$\varepsilon > 0$, $32vp \le \varepsilon^2$ and
$32bp \le \varepsilon$, <!-- value subexponentialMomentBound v b p -->
$$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p) \le \varepsilon^p e^{-p}\,,$$
through the readable comparison `NLAlib.subexponentialMomentBound_le`: each of its two terms is
at most $\varepsilon^p e^{-p}/4$, since $32^{p/2}$ and $16^p$ exceed $4e^p$ for $p \ge 2$. At
$p = \max(2, \log(1/\delta))$ the right side divided by $\varepsilon^p$ is at most $\delta$. -/
theorem subexponentialMomentBound_le_mul_exp_neg {v b p ε : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hp : 2 ≤ p) (hε : 0 < ε) (hvp : 32 * (v * p) ≤ ε ^ 2) (hbp : 32 * (b * p) ≤ ε) :
    subexponentialMomentBound v b p ≤ ε ^ p * Real.exp (-p) := by
  have hp0 : 0 < p := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hq : Real.exp (-p) / 4 = Real.exp (-p - Real.log 4) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have hA : (v * p) ^ (p / 2) ≤ ε ^ p * (Real.exp (-p) / 4) := by
    have h1 : (v * p) ^ (p / 2) ≤ (ε ^ 2 / 32) ^ (p / 2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have h2 : (ε ^ 2 / 32) ^ (p / 2) = ε ^ p * Real.exp (-(p / 2 * Real.log 32)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hε.le,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 32), Real.exp_neg, div_eq_mul_inv,
        mul_comm (Real.log 32)]
      congr 2
      push_cast
      ring
    refine h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    rw [hq]
    exact Real.exp_le_exp.2 (by rw [hl32, hl4]; nlinarith)
  have hB : (2 * b * p) ^ p ≤ ε ^ p * (Real.exp (-p) / 4) := by
    have h1 : (2 * b * p) ^ p ≤ (ε / 16) ^ p :=
      Real.rpow_le_rpow (by positivity) (by linarith) hp0.le
    have h2 : (ε / 16) ^ p = ε ^ p * Real.exp (-(p * Real.log 16)) := by
      rw [Real.div_rpow hε.le (by norm_num), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16),
        Real.exp_neg, div_eq_mul_inv, mul_comm p]
    refine h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    rw [hq]
    exact Real.exp_le_exp.2 (by rw [hl16, hl4]; nlinarith)
  calc subexponentialMomentBound v b p ≤ 2 * (v * p) ^ (p / 2) + 2 * (2 * b * p) ^ p :=
        subexponentialMomentBound_le hv hb hp
    _ ≤ ε ^ p * Real.exp (-p) := by linarith

/-- The layer-cake bound for $p$-th moments: under a finite measure, for $f \ge 0$ almost
everywhere, $p > 0$ and $\mathbb{P}[t \le f] \le F(t)$ for every $t > 0$, with $t^{p-1}F(t)$
integrable on $(0, \infty)$, $f^p$ is integrable and
$$\mathbb{E} f^p \le p\int_0^\infty t^{p-1}F(t)\,dt\,.$$
From Mathlib's `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`. -/
theorem integral_rpow_le_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 0 < p) {F : ℝ → ℝ}
    (hF : IntegrableOn (fun t => t ^ (p - 1) * F t) (Set.Ioi 0))
    (htail : ∀ t, 0 < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    Integrable (fun ω => f ω ^ p) μ ∧
      ∫ ω, f ω ^ p ∂μ ≤ p * ∫ t in Set.Ioi 0, t ^ (p - 1) * F t := by
  have hF0 : ∀ t, 0 < t → 0 ≤ F t := fun t ht => measureReal_nonneg.trans (htail t ht)
  have hI0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun t => t ^ (p - 1) * F t :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) =>
      mul_nonneg (Real.rpow_nonneg ht.le _) (hF0 t ht)
  have hlin : ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤
      ENNReal.ofReal (p * ∫ t in Set.Ioi 0, t ^ (p - 1) * F t) := by
    rw [lintegral_rpow_eq_lintegral_meas_le_mul μ hf0 hf hp, ENNReal.ofReal_mul hp.le,
      ofReal_integral_eq_lintegral_ofReal hF hI0]
    gcongr 1
    refine setLIntegral_mono' measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [mul_comm, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← ofReal_measureReal]
    gcongr
    exact htail t ht
  have hm : AEStronglyMeasurable (fun ω => f ω ^ p) μ := (hf.pow_const p).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[μ] fun ω => f ω ^ p := hf0.mono fun ω h => Real.rpow_nonneg h p
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hp.le (integral_nonneg_of_ae hI0)) hlin

/-- The Gamma integral $\int_0^\infty t^{q}e^{-c t^{r}}\,dt$ with its integrability, for
$q > -1$, $r > 0$, $c > 0$: $c^{-(q+1)/r}\,r^{-1}\,\Gamma((q+1)/r)$. -/
private theorem integrableOn_and_integral_rpow_mul_exp {q r c : ℝ} (hq : -1 < q) (hr : 0 < r)
    (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-c * t ^ r)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, t ^ q * Real.exp (-c * t ^ r) =
        c ^ (-(q + 1) / r) * (1 / r) * Real.Gamma ((q + 1) / r) :=
  ⟨integrableOn_rpow_mul_exp_neg_mul_rpow hq hr hc, integral_rpow_mul_exp_neg_mul_rpow hr hq hc⟩

/-- **Moments from a sub-exponential tail**: under a finite measure, for $f \ge 0$ almost
everywhere with $\mathbb{P}[t \le f] \le 2\exp(-\min(t^2/(2v), t/(2b)))$ for every $t > 0$,
$v, b > 0$ and $p > 0$, $f^p$ is integrable and <!-- value subexponentialMomentBound v b p -->
$$\mathbb{E} f^p \le p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)\,,$$
the bound being `subexponentialMomentBound v b p`, the layer-cake integral of
$2e^{-t^2/(2v)} + 2e^{-t/(2b)}$; for $p \ge 2$ it is at most $2(vp)^{p/2} + 2(2bp)^{p}$
(`NLAlib.subexponentialMomentBound_le`). [Vershynin2018, Proposition 2.7.1] for the equivalence
of tails and moments, with unspecified constants. Here integration of the displayed mixed tail
gives explicit constants. -/
theorem integral_rpow_le_of_measureReal_ge_le_two_mul_exp [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {v b p : ℝ} (hv : 0 < v)
    (hb : 0 < b) (hp : 0 < p)
    (htail : ∀ t, 0 < t → μ.real {ω | t ≤ f ω} ≤
      2 * Real.exp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))) :
    Integrable (fun ω => f ω ^ p) μ ∧ ∫ ω, f ω ^ p ∂μ ≤ subexponentialMomentBound v b p := by
  set F : ℝ → ℝ := fun t => 2 * Real.exp (-(1 / (2 * v)) * t ^ (2 : ℝ)) +
    2 * Real.exp (-(1 / (2 * b)) * t ^ (1 : ℝ)) with hFdef
  have hq : -1 < p - 1 := by linarith
  obtain ⟨hA, eA⟩ := integrableOn_and_integral_rpow_mul_exp hq two_pos
    (show 0 < 1 / (2 * v) by positivity)
  obtain ⟨hB, eB⟩ := integrableOn_and_integral_rpow_mul_exp hq one_pos
    (show 0 < 1 / (2 * b) by positivity)
  have hfun : (fun t => t ^ (p - 1) * F t) = fun t =>
      2 * (t ^ (p - 1) * Real.exp (-(1 / (2 * v)) * t ^ (2 : ℝ))) +
        2 * (t ^ (p - 1) * Real.exp (-(1 / (2 * b)) * t ^ (1 : ℝ))) := by
    funext t
    simp only [hFdef]
    ring
  have hFi : IntegrableOn (fun t => t ^ (p - 1) * F t) (Set.Ioi 0) := by
    rw [hfun]
    exact (hA.const_mul 2).add (hB.const_mul 2)
  have htail' : ∀ t, 0 < t → μ.real {ω | t ≤ f ω} ≤ F t := by
    intro t ht
    refine (htail t ht).trans ?_
    simp only [hFdef, Real.rpow_two, Real.rpow_one]
    have e1 : -(1 / (2 * v)) * t ^ 2 = -(t ^ 2 / (2 * v)) := by ring
    have e2 : -(1 / (2 * b)) * t = -(t / (2 * b)) := by ring
    rw [e1, e2]
    rcases min_choice (t ^ 2 / (2 * v)) (t / (2 * b)) with h | h <;> rw [h] <;>
      nlinarith [Real.exp_pos (-(t ^ 2 / (2 * v))), Real.exp_pos (-(t / (2 * b)))]
  obtain ⟨hint, hle⟩ := integral_rpow_le_of_measureReal_ge_le hf hf0 hp hFi htail'
  refine ⟨hint, hle.trans_eq ?_⟩
  rw [hfun, integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul,
    integral_const_mul, eA, eB, subexponentialMomentBound_def]
  have h1 : (p - 1 + 1) / 2 = p / 2 := by ring
  have h2 : -(p - 1 + 1) / 2 = -(p / 2) := by ring
  have h3 : (p - 1 + 1) / 1 = p := by ring
  have h4 : -(p - 1 + 1) / 1 = -p := by ring
  rw [h1, h2, h3, h4, one_div (2 * v), Real.inv_rpow (by positivity), Real.rpow_neg (by positivity),
    inv_inv, one_div (2 * b), Real.inv_rpow (by positivity), Real.rpow_neg (by positivity),
    inv_inv]
  ring

/-- Two-sided sub-exponential tail from Dasgupta–Gupta tails: under a finite measure, if
$\mathbb{P}[\beta a \le Y] \le e^{(K/2)(1 - \beta + \log\beta)}$ for every $\beta \ge 1$ and
$\mathbb{P}[Y \le \beta a] \le e^{(K/2)(1 - \beta + \log\beta)}$ for every $0 < \beta \le 1$, with
$a > 0$ and $K \ge 0$, then for $t \ge 0$
$$\mathbb{P}\bigl[t \le \lvert Y/a - 1\rvert\bigr] \le 2e^{-(K/8)\min(t^2, t)}\,.$$
The upper side by $\log(1 + s) \le s - s^2/(2(1 + s))$ (`Real.log_one_add_le_sub_sq_div`) and
$s^2/(2(1 + s)) \ge \min(s^2, s)/4$, the lower by $\log(1 - u) \le -u - u^2/2$
(`Real.log_one_sub_le_quadratic`); no hypothesis $\mathbb{P}[Y \le 0] = 0$ is needed, since for
$K > 0$ it is the limit $\beta \to 0$ of the lower tail and for $K = 0$ the bound is $2$. The
input of the Gaussian and Haar JL moments ($K$ the number of rows, $a$ the mean). -/
theorem measureReal_abs_div_sub_one_ge_le_two_mul_exp [IsFiniteMeasure μ] {Y : Ω → ℝ}
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hup : ∀ β : ℝ, 1 ≤ β → μ.real {ω | β * a ≤ Y ω} ≤ Real.exp (K / 2 * (1 - β + Real.log β)))
    (hlow : ∀ β : ℝ, 0 < β → β ≤ 1 →
      μ.real {ω | Y ω ≤ β * a} ≤ Real.exp (K / 2 * (1 - β + Real.log β)))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Y ω / a - 1|} ≤ 2 * Real.exp (-(K / 8 * min (t ^ 2) t)) := by
  set e := Real.exp (-(K / 8 * min (t ^ 2) t)) with he
  have hsub : {ω | t ≤ |Y ω / a - 1|} ⊆ {ω | (1 + t) * a ≤ Y ω} ∪ {ω | Y ω ≤ (1 - t) * a} := by
    intro ω hω
    have hω' : t ≤ |Y ω / a - 1| := hω
    rcases le_abs.1 hω' with h | h
    · left
      have : (1 + t) ≤ Y ω / a := by linarith
      exact (le_div_iff₀ ha).1 this
    · right
      have : Y ω / a ≤ 1 - t := by linarith
      exact (div_le_iff₀ ha).1 this
  have hup' : μ.real {ω | (1 + t) * a ≤ Y ω} ≤ e := by
    refine (hup (1 + t) (by linarith)).trans (Real.exp_le_exp.2 ?_)
    have hlog := Real.log_one_add_le_sub_sq_div ht
    have hmin : min (t ^ 2) t / 4 ≤ t ^ 2 / (2 * (1 + t)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      rcases le_total t 1 with h1 | h1
      · rw [min_eq_left (by nlinarith)]
        nlinarith
      · rw [min_eq_right (by nlinarith)]
        nlinarith
    have : 1 - (1 + t) + Real.log (1 + t) ≤ -(min (t ^ 2) t / 4) := by linarith
    nlinarith
  have hlow' : μ.real {ω | Y ω ≤ (1 - t) * a} ≤ e := by
    rcases lt_or_ge t 1 with h1 | h1
    · refine (hlow (1 - t) (by linarith) (by linarith)).trans (Real.exp_le_exp.2 ?_)
      have hlog := Real.log_one_sub_le_quadratic ht h1
      rw [min_eq_left (by nlinarith)]
      have : 1 - (1 - t) + Real.log (1 - t) ≤ -(t ^ 2 / 2) := by linarith
      nlinarith [sq_nonneg t]
    · set β := Real.exp (-(t / 4) - 1) with hβ
      have hβ0 : 0 < β := Real.exp_pos _
      have hβ1 : β ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have hmono : {ω | Y ω ≤ (1 - t) * a} ⊆ {ω | Y ω ≤ β * a} := fun ω hω => by
        have hω' : Y ω ≤ (1 - t) * a := hω
        change Y ω ≤ β * a
        nlinarith
      refine (measureReal_mono hmono).trans ((hlow β hβ0 hβ1).trans (Real.exp_le_exp.2 ?_))
      rw [min_eq_right (by nlinarith), hβ, Real.log_exp]
      nlinarith [Real.exp_pos (-(t / 4) - 1)]
  calc μ.real {ω | t ≤ |Y ω / a - 1|}
      ≤ μ.real ({ω | (1 + t) * a ≤ Y ω} ∪ {ω | Y ω ≤ (1 - t) * a}) := measureReal_mono hsub
    _ ≤ μ.real {ω | (1 + t) * a ≤ Y ω} + μ.real {ω | Y ω ≤ (1 - t) * a} :=
        measureReal_union_le _ _
    _ ≤ 2 * e := by linarith

/-! ### Sub-gamma tails -/

/-- **Chernoff's bound for a sub-gamma upper tail.** If the moment generating function of $X$
satisfies
$$\mathbb{E}\, e^{\theta X} \le \exp \frac{\theta^2 v}{2 (1 - b\theta)}$$
for every $\theta \ge 0$ with $b\theta < 1$ (and $e^{\theta X}$ is integrable there), then for
$t \ge 0$
$$\mu\bigl(X \ge \sqrt{2 v t} + b t\bigr) \le e^{-t}\,.$$
Chernoff's bound at $\theta = s / (1 + b s)$, $s = \sqrt{2t/v}$, where the exponent is exactly
$-t$. No finiteness assumption on $\mu$: integrability at $\theta = 0$ gives it. $v > 0$ is needed:
at $v = b = 0$ the constant $0$ satisfies the hypothesis and the event is everything. The exact
constant, which the $\min(t^2/v, t/b)$ forms of `NLAlib.Probability.SubExponential.Tail` lose; the
step behind every exact-constant Bernstein-type tail (the Hsu–Kakade–Zhang tail
`NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`). [BoucheronLugosiMassart2013] (the
sub-gamma tail of their Chapter 2; locator not checked against the book). -/
theorem measureReal_ge_le_exp_neg_of_mgf_le {X : Ω → ℝ} {v b : ℝ} (hv : 0 < v) (hb : 0 ≤ b)
    (hint : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 → Integrable (fun ω => Real.exp (θ * X ω)) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 →
      mgf X μ θ ≤ Real.exp (θ ^ 2 * v / (2 * (1 - b * θ))))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(2 * v * t) + b * t ≤ X ω} ≤ Real.exp (-t) := by
  have : IsFiniteMeasure μ := by
    have h0 := hint 0 le_rfl (by simp)
    simp only [zero_mul, Real.exp_zero] at h0
    exact (integrable_const_iff_isFiniteMeasure one_ne_zero).1 h0
  set s := √(2 * t / v) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 * v = 2 * t := by
    rw [hs_def, Real.sq_sqrt (by positivity)]
    field_simp
  have hsa : s * √(2 * v * t) = 2 * t := by
    rw [hs_def, ← Real.sqrt_mul (by positivity),
      show 2 * t / v * (2 * v * t) = (2 * t) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]
  set D := 1 + b * s with hD
  have hD0 : 0 < D := by positivity
  set θ := s / D with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hbθ : 1 - b * θ = D⁻¹ := by
    rw [hθ, hD]
    field_simp
    ring
  have hbθ1 : b * θ < 1 := by
    have : 0 < D⁻¹ := inv_pos.2 hD0
    linarith
  refine (measure_ge_le_exp_mul_mgf _ hθ0 (hint θ hθ0 hbθ1)).trans ?_
  calc Real.exp (-θ * (√(2 * v * t) + b * t)) * mgf X μ θ
      ≤ Real.exp (-θ * (√(2 * v * t) + b * t)) *
          Real.exp (θ ^ 2 * v / (2 * (1 - b * θ))) := by
        gcongr
        exact hmgf θ hθ0 hbθ1
    _ = Real.exp (-t) := by
        rw [← Real.exp_add, hbθ]
        congr 1
        rw [hθ]
        field_simp
        linear_combination (-2) * hsa + hs2 + 2 * t * hD

/-! ### Moments of a sum -/

/-- For $r \ge 1$ and nonnegative $Y_i$ with each $Y_i^r$ integrable, $(\sum_i Y_i)^r$ is
integrable: it is at most $\lvert\iota\rvert^{r-1}\sum_i Y_i^r$
(`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`). -/
theorem integrable_rpow_sum {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} (hY0 : ∀ i ω, 0 ≤ Y i ω)
    {r : ℝ} (hr : 1 ≤ r) (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ)
    (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) :
    Integrable (fun ω => (∑ i, Y i ω) ^ r) μ := by
  have hsum : Integrable (fun ω => ∑ i, Y i ω ^ r) μ :=
    integrable_finsetSum Finset.univ (f := fun i ω => Y i ω ^ r) fun i _ => hint i
  refine (hsum.const_mul ((Fintype.card ι : ℝ) ^ (r - 1))).mono' hm (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => hY0 i ω) r)]
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := fun i => Y i ω)
    hr fun i _ => hY0 i ω
  simpa only [Finset.card_univ] using h

/-- **Weighted Jensen for a sum of nonnegative random variables**: for $r \ge 1$, if
$\mathbb{E}[Y_i^r] \le w_i^r K$ for nonnegative weights $w_i$ summing to one, with $Y_i = 0$
where $w_i = 0$, then $\mathbb{E}[(\sum_i Y_i)^r] \le K$. The sum is integrable by
`NLAlib.integrable_rpow_sum`. [Vershynin2018, §1.2] gives Jensen’s inequality, applied here to the
weights before integration. -/
theorem integral_rpow_sum_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hY0 : ∀ i ω, 0 ≤ Y i ω) {r : ℝ} (hr : 1 ≤ r)
    (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hwY : ∀ i, w i = 0 → ∀ ω, Y i ω = 0)
    (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) {K : ℝ}
    (hK : ∀ i, ∫ ω, Y i ω ^ r ∂μ ≤ w i ^ r * K) :
    ∫ ω, (∑ i, Y i ω) ^ r ∂μ ≤ K := by
  have hpt (ω : Ω) : (∑ i, Y i ω) ^ r ≤ ∑ i, w i * (Y i ω / w i) ^ r := by
    have e : ∑ i, Y i ω = ∑ i, w i * (Y i ω / w i) := Finset.sum_congr rfl fun i _ => by
      rcases eq_or_ne (w i) 0 with h0 | h0
      · rw [h0, hwY i h0 ω, zero_mul]
      · rw [mul_div_cancel₀ _ h0]
    rw [e]
    exact Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w (fun i => Y i ω / w i)
      (fun i _ => hw0 i) hw1 (fun i _ => div_nonneg (hY0 i ω) (hw0 i)) hr
  have hterm (i : ι) : (fun ω => w i * (Y i ω / w i) ^ r) =
      fun ω => w i / w i ^ r * Y i ω ^ r := by
    funext ω
    rw [Real.div_rpow (hY0 i ω) (hw0 i)]
    ring
  have hti (i : ι) : Integrable (fun ω => w i * (Y i ω / w i) ^ r) μ := by
    rw [hterm]
    exact (hint i).const_mul _
  have hdom : Integrable (fun ω => ∑ i, w i * (Y i ω / w i) ^ r) μ :=
    integrable_finsetSum _ fun i _ => hti i
  refine (integral_mono (integrable_rpow_sum hY0 hr hm hint) hdom hpt).trans ?_
  rw [integral_finsetSum _ fun i _ => hti i]
  calc ∑ i, ∫ ω, w i * (Y i ω / w i) ^ r ∂μ ≤ ∑ i, w i * K :=
        Finset.sum_le_sum fun i _ => ?_
    _ = K := by rw [← Finset.sum_mul, hw1, one_mul]
  rw [hterm, integral_const_mul]
  rcases eq_or_lt_of_le (hw0 i) with h0 | hpos
  · rw [← h0, zero_div, zero_mul, zero_mul]
  · have hwr : 0 < w i ^ r := Real.rpow_pos_of_pos hpos r
    calc w i / w i ^ r * ∫ ω, Y i ω ^ r ∂μ ≤ w i / w i ^ r * (w i ^ r * K) :=
          mul_le_mul_of_nonneg_left (hK i) (div_nonneg hpos.le hwr.le)
      _ = w i * K := by field_simp

end NLAlib
