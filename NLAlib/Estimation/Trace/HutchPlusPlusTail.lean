/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus
public import NLAlib.LowRank.Oblivious.SubGaussian

/-!
# Hutch++: high-probability bounds

The deviation of Hutch++ (`NLAlib.hutchpp`) with residual probes that have independent
sub-Gaussian entries. The primary theorem takes the range-finder guarantee as a hypothesis: if
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2 \le
K\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ fails with probability at most
$\delta_1$, the Girard–Hutchinson tail (`NLAlib.measureReal_abs_trace_sub_girardHutchinson_ge_le`,
from Hanson–Wright) on the compressed residual, conditionally on the sketch, adds a sub-exponential
term. The sub-Gaussian range finder
(`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`) and the nuclear-norm
tail bound (`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`) turn it into the relative-error
guarantee of Meyer, Musco, Musco and Woodruff: $O(\sqrt{\log(1/\delta)}/\varepsilon +
\log(1/\delta))$ products give $\lvert \operatorname{tr}\mathbf{A} - \mathsf{hutchpp} \rvert \le
\varepsilon\|\mathbf{A}\|_*$ with probability $1 - \delta$. Real throughout. The constants are
explicit: the range-finder factor <!-- value subgaussianRangeFinderFactor c -->$1 + 5c/2$
replaces MMMW's $2$ (their route through Musco and Musco is not in the library), and the
Hanson–Wright constant is <!-- value hansonWrightConstant -->$1/196$.

## Main results

* `NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le`: the tail given a range-finder guarantee.
* `NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_frobNorm_sub_truncatedSVD_eq_zero`:
  a vanishing rank-$r$ tail leaves only range-finder failure at positive deviation thresholds.
* `NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector`,
  `NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`: sub-Gaussian and
  Gaussian sketches.
* `NLAlib.measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`: the
  relative error in the nuclear norm, and its asymptotic form
  `exists_forall_measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`.
* `Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector`,
  `Matrix.PosSemidef.measureReal_hutchpp_gt_one_add_mul_trace_le_of_isSubgaussianVector`: the two
  one-sided $(1 \pm \varepsilon)$ bounds for positive semidefinite matrices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n s t : Type*} [Fintype n]
  [Fintype s] [Fintype t] [DecidableEq n]

/-- If the best rank-$r$ Frobenius tail vanishes, the strict deviation of
$\mathsf{hutchpp}(\mathbf{A},\mathbf{S},\mathbf{G})$ above any $\tau \ge 0$ is bounded by
the range-finder failure probability. The residual probes may be arbitrary and dependent:
on the good event the sketch recovers $\mathbf{A}$ exactly. -/
theorem measureReal_abs_trace_sub_hutchpp_gt_le_of_frobNorm_sub_truncatedSVD_eq_zero
    [IsFiniteMeasure μ] (A : Matrix n n ℝ) (S : Ω → Matrix n s ℝ)
    (G : Ω → Matrix n t ℝ) {r : ℕ} (hzero : frobNorm (A - truncatedSVD A r) = 0)
    (K : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ < |A.trace - hutchpp A (S ω) (G ω)|} ≤
      μ.real {ω | K * frobNorm (A - truncatedSVD A r) ^ 2 <
        frobNorm (A - rsvd A (S ω)) ^ 2} := by
  refine measureReal_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hzero, zero_pow two_ne_zero, mul_zero]
  by_contra hbad
  have hres : A - rsvd A (S ω) = 0 :=
    frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm (not_lt.1 hbad) (sq_nonneg _)))
  rw [hutchpp_eq_trace_of_rsvd_eq (sub_eq_zero.1 hres).symm, sub_self, abs_zero] at hω
  exact (not_lt.2 hτ) hω

/-- For a positive non-strict deviation threshold $\tau > 0$, a vanishing best rank-$r$
Frobenius tail gives the range-finder failure probability alone as the Hutch++ tail budget.
No law or independence of the residual probes is needed. Positivity matters: at $\tau = 0$
the non-strict deviation event is the entire sample space even for an exact estimator. -/
theorem measureReal_abs_trace_sub_hutchpp_ge_le_of_frobNorm_sub_truncatedSVD_eq_zero
    [IsFiniteMeasure μ] (A : Matrix n n ℝ) (S : Ω → Matrix n s ℝ)
    (G : Ω → Matrix n t ℝ) {r : ℕ} (hzero : frobNorm (A - truncatedSVD A r) = 0)
    (K : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    μ.real {ω | τ ≤ |A.trace - hutchpp A (S ω) (G ω)|} ≤
      μ.real {ω | K * frobNorm (A - truncatedSVD A r) ^ 2 <
        frobNorm (A - rsvd A (S ω)) ^ 2} := by
  refine (measureReal_mono fun ω hω => lt_of_lt_of_le (half_lt_self hτ) hω).trans ?_
  exact measureReal_abs_trace_sub_hutchpp_gt_le_of_frobNorm_sub_truncatedSVD_eq_zero
    A S G hzero K (half_pos hτ).le


/-- **The deviation of Hutch++ given a range-finder guarantee.** Let the sketch test matrix
$\mathbf{S}$ be almost everywhere measurable and the $n \times \ell$ residual test matrix
$\mathbf{G}$ be independent of it, with independent entries that each satisfy the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and have second
moment $1$. If, for some $r$ and $K$, the range-finder event
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2 \le
K\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ fails with probability at most
$\delta_1$, then for every real square $\mathbf{A}$ and every $\tau \ge 0$, with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert \ge \tau\bigr] \le \delta_1 +
2\exp\Bigl(-\frac{1}{196}\min\Bigl( \frac{\ell\tau^2}{c^2 K\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{c\sqrt{K}\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`. On the range-finder event the compressed residual has
Frobenius (hence spectral) norm at most $\sqrt{K}\|\mathbf{E}_r\|_{\mathsf{F}}$; conditionally on
$\mathbf{S}$ the Girard–Hutchinson tail applies
(`NLAlib.measureReal_abs_trace_sub_girardHutchinson_ge_le`), and
`ProbabilityTheory.IndepFun.measureReal_mem_le_add` integrates it over the sketch. A zero
denominator makes its fraction $0$, and the bound is then at least $2$; in particular, when
$\|\mathbf{E}_r\|_{\mathsf{F}} = 0$ the bound says nothing. For $\tau > 0$, use
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_frobNorm_sub_truncatedSVD_eq_zero`
to retain only the range-finder failure budget; its strict-deviation counterpart also allows
$\tau = 0$. These follow from exactness of Hutch++ on the range-finder event. Instances:
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector`,
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and Lemma 2]; there for positive semidefinite
$\mathbf{A}$ with $\|\mathbf{\Delta}\|_{\mathsf{F}} \le 2\|\mathbf{E}_r\|_{\mathsf{F}}$ given,
unspecified constants and a sample-size form.
Result: hutchpp-tail -/
theorem measureReal_abs_trace_sub_hutchpp_ge_le (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c : ℝ≥0} (hS : AEMeasurable S μ) (hSG : IndepFun S G μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) {r : ℕ} {K δ₁ : ℝ}
    (hRF : μ.real {ω | K * frobNorm (A - truncatedSVD A r) ^ 2 <
      frobNorm (A - rsvd A (S ω)) ^ 2} ≤ δ₁) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |A.trace - hutchpp A (S ω) (G ω)|} ≤
      δ₁ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / ((c : ℝ) ^ 2 * K * frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / ((c : ℝ) * √K * frobNorm (A - truncatedSVD A r))))) := by
  simp only [abs_sub_comm A.trace]
  classical
  have := hGind.isProbabilityMeasure
  set F := frobNorm (A - truncatedSVD A r) with hF
  set b := 2 * Real.exp (-(hansonWrightConstant *
    min (Fintype.card t * τ ^ 2 / ((c : ℝ) ^ 2 * K * F ^ 2))
      (Fintype.card t * τ / ((c : ℝ) * √K * F)))) with hb
  have hδ₁ : 0 ≤ δ₁ := measureReal_nonneg.trans hRF
  have hb0 : 0 ≤ b := by positivity
  rcases hτ.eq_or_lt with rfl | hτ0
  · have hb2 : b = 2 := by simp [hb]
    rw [hb2]
    exact measureReal_le_one.trans (by linarith)
  have hG : AEMeasurable G μ := aemeasurable_pi_lambda _ fun i =>
    aemeasurable_pi_lambda _ fun j => (hGsub i j).aemeasurable
  set E : Set (Matrix n t ℝ × Matrix n s ℝ) := {q | τ ≤ |hutchpp A q.2 q.1 - A.trace|} with hEdef
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (continuous_abs.measurable.comp (((measurable_hutchpp A).comp measurable_swap).sub_const _))
  set good : Set (Matrix n s ℝ) := {x | frobNorm (A - rsvd A x) ^ 2 ≤ K * F ^ 2} with hgood
  have hgoodm : MeasurableSet good := measurableSet_le
    ((continuous_frobNorm.measurable.comp (measurable_const.sub (measurable_rsvd A))).pow_const 2)
    measurable_const
  have hbad : μ.real {ω | S ω ∉ good} ≤ δ₁ := by
    refine le_of_eq_of_le ?_ hRF
    congr 1
    ext ω
    simp [hgood, not_le]
  have hsec (x : Matrix n s ℝ) (hx : x ∈ good) : μ.real {ω | (G ω, x) ∈ E} ≤ b := by
    set P := rangeProjector (A * x)
    set Δ := (1 - P) * A * (1 - P) with hΔ
    have hset : {ω | (G ω, x) ∈ E} =
        {ω | τ ≤ |girardHutchinson Δ (G ω) - Δ.trace|} := by
      ext ω
      simp only [hEdef, Set.mem_ofPred_eq]
      rw [abs_sub_comm, trace_sub_hutchpp, abs_sub_comm]
    rw [hset]
    by_cases hΔ0 : Δ = 0
    · have hempty : {ω | τ ≤ |girardHutchinson Δ (G ω) - Δ.trace|} = ∅ := by
        ext ω
        simp [hΔ0, girardHutchinson, not_le.2 hτ0]
      rw [hempty, measureReal_empty]
      exact hb0
    refine (le_of_eq_of_le (by simp only [abs_sub_comm])
      (measureReal_abs_trace_sub_girardHutchinson_ge_le hGind hGsub hGvar Δ hτ)).trans ?_
    rw [hb]
    gcongr 2 * Real.exp (-(hansonWrightConstant * ?_))
    · exact hansonWrightConstant_pos.le
    have hΔF : frobNorm Δ ^ 2 ≤ K * F ^ 2 := by
      refine le_trans ?_ hx
      have h1 : frobNorm Δ ≤ frobNorm (A - rsvd A x) := by
        rw [sub_rsvd, hΔ]
        exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
          (mul_le_of_le_one_right (frobNorm_nonneg _)
            (isStarProjection_one_sub_rangeProjector (A * x)).specNorm_le_one)
      exact pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
    have hΔF' : frobNorm Δ ≤ √K * F := by
      calc frobNorm Δ = √(frobNorm Δ ^ 2) := (Real.sqrt_sq (frobNorm_nonneg Δ)).symm
        _ ≤ √(K * F ^ 2) := Real.sqrt_le_sqrt hΔF
        _ = √K * F := by rw [Real.sqrt_mul' K (sq_nonneg F), Real.sqrt_sq (frobNorm_nonneg _)]
    rcases (c.coe_nonneg).eq_or_lt with hc0 | hc0
    · simp [← hc0]
    have hF0 : 0 < frobNorm Δ := lt_of_le_of_ne (frobNorm_nonneg _)
      (Ne.symm (fun h => hΔ0 (frobNorm_eq_zero_iff.1 h)))
    have hS0 : 0 < specNorm Δ := lt_of_le_of_ne (specNorm_nonneg _)
      (Ne.symm (fun h => hΔ0 (specNorm_eq_zero_iff.1 h)))
    have hL : (0 : ℝ) ≤ Fintype.card t := Nat.cast_nonneg _
    refine min_le_min ?_ ?_
    · rw [mul_assoc]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hΔF (sq_nonneg _))
    · rw [mul_assoc]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left ((specNorm_le_frobNorm Δ).trans hΔF') hc0.le)
  have h := hSG.symm.measureReal_mem_le_add hG hS hE hgoodm hb0 hsec hbad
  rw [add_comm] at h
  exact h

/-- **The deviation of Hutch++ with a sub-Gaussian sketch.** Let the sketch
$\mathbf{S}^{\mathsf{H}}$ of the $n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$,
$\lvert s \rvert \ge 1$, have independent, isotropic, sub-Gaussian rows with proxy $c$, and let the
$n \times \ell$ residual test matrix $\mathbf{G}$ be independent of $\mathbf{S}$, with independent
entries that each satisfy the sub-Gaussian moment generating function bound with variance proxy
$c'$ and have second moment $1$. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/2) -->
$\lvert s \rvert \ge 25 c^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then for every real square $\mathbf{A}$ and
every $\tau \ge 0$, with $\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, we
get <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert \ge \tau\bigr] \le \delta +
2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{c'^2 (1 + 5c/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{c'\sqrt{1 + 5c/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and the constant in the exponent is
`hansonWrightConstant`. `NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le` with the range finder
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`. Sign sketches and
residual probes are the case $c = c' = 1$.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §3, proof of Theorem 1]; there with sign test
matrices, the factor $2$ and unspecified constants.
Result: hutchpp-tail -/
theorem measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector [Nonempty s]
    (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0}
    (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 2) ≤ Fintype.card s) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |A.trace - hutchpp A (S ω) (G ω)|} ≤
      δ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c *
            frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / ((c' : ℝ) * √(subgaussianRangeFinderFactor c) *
            frobNorm (A - truncatedSVD A r))))) := by
  classical
  have hS : AEMeasurable S μ := aemeasurable_pi_lambda _ fun j => aemeasurable_pi_lambda _ fun i =>
    by simpa [Matrix.conjTranspose_apply] using
      ((hSiso i).memLp j).aestronglyMeasurable.aemeasurable
  exact measureReal_abs_trace_sub_hutchpp_ge_le A hS hSG hGind hGsub hGvar
    (measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector A hSind hSsub hSiso hδ hs) hτ

/-- **The deviation of Gaussian Hutch++.** Let the $n \times \lvert s \rvert$ sketch test matrix
$\mathbf{S}$, $\lvert s \rvert \ge 1$, and the $n \times \ell$ residual test matrix $\mathbf{G}$ be
independent and standard Gaussian. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$\lvert s \rvert \ge 25 \cdot 1^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, that is
$\lvert s \rvert \ge 225(r \log 21 + \log(4/\delta))$, then for every real square $\mathbf{A}$
and every $\tau \ge 0$, with $\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, we
get <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert \ge \tau\bigr] \le \delta +
2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 5\cdot 1/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 5\cdot 1/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. The case $c = c' = 1$ of
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector`: the range-finder step goes
through the sub-Gaussian range finder
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector` at $c = 1$, with the
factor $7/2$ and the size $225(r \log 21 + \log(4/\delta))$. This is weaker than the Gaussian
range-finder tail `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
(`NLAlib/LowRank/Gaussian/RangeFinderTail.lean`), whose factor $1 + (tr/d)(1 + u)^2$ at
deviation $u$ (since
$\sigma_r(\mathbf{A}) \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}$) is
reached at the size $\lvert s \rvert = r + d - 1$; the generic
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le` takes that tail as its range-finder hypothesis
directly.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]; there with unspecified constants.
Result: hutchpp-tail -/
theorem measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix [Nonempty s]
    (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ}
    (hS : HasLaw S (gaussianMatrix n s) μ) (hG : HasLaw G (gaussianMatrix n t) μ)
    (hSG : IndepFun S G μ) {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ Fintype.card s) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |A.trace - hutchpp A (S ω) (G ω)|} ≤
      δ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / (subgaussianRangeFinderFactor 1 *
            frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / (√(subgaussianRangeFinderFactor 1) *
            frobNorm (A - truncatedSVD A r))))) := by
  classical
  have hSt := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  have hGu := hasLaw_uncurry_of_hasLaw_gaussianMatrix hG
  have h := measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector A (c := 1) (c' := 1)
    hSt.iIndepFun_eval (fun i => isSubgaussianVector_of_hasLaw_gaussianVector (hSt.eval i))
    (fun i => isIsotropic_of_hasLaw_gaussianVector (hSt.eval i)) hGu.iIndepFun_eval
    (fun i j => hasSubgaussianMGF_of_hasLaw_gaussianReal (hGu.eval (i, j)))
    (fun i j => (integral_sq_of_hasLaw_gaussianReal (hGu.eval (i, j))).trans NNReal.coe_one) hSG hδ
    (by simpa using hs) hτ
  simpa using h

/-- **Hutch++ to relative error in the nuclear norm.** Let the sketch $\mathbf{S}^{\mathsf{H}}$
of the $n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$, $\lvert s \rvert \ge 1$, have
independent, isotropic, sub-Gaussian rows with proxy $c$, and let the $n \times \ell$ residual
test matrix $\mathbf{G}$ be independent of $\mathbf{S}$, with independent entries that each satisfy
the sub-Gaussian moment generating function bound with variance proxy $c'$ and have second moment
$1$. If $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 25 c^2 (r \log 21 + \log(2/(\delta/4)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 5c/2)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 5c/2}}\,,$$
then for every real square $\mathbf{A}$
$$\mathbb{P}\bigl[\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert > \varepsilon\|\mathbf{A}\|_*\bigr] \le
\delta\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. From
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector` at $\delta/2$ and
$\tau = \varepsilon\|\mathbf{A}\|_*$, with
$\|\mathbf{E}_r\|_{\mathsf{F}} \le \|\mathbf{A}\|_*/(2\sqrt{r})$
(`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`); when
$\|\mathbf{E}_r\|_{\mathsf{F}} = 0$ that tail says nothing, and instead the randomized SVD
recovers $\mathbf{A}$ outside probability $\delta/2$, where Hutch++ is exact. Asymptotic form:
`exists_forall_measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`. The
positive semidefinite forms are
`Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector` and
`Matrix.PosSemidef.measureReal_hutchpp_gt_one_add_mul_trace_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 5]; there with sign test matrices and
$m = O(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$, constants unspecified.
Result: hutchpp-relative-error -/
theorem measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector
    [Nonempty s] (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0}
    (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | ε * nuclearNorm A < |A.trace - hutchpp A (S ω) (G ω)|} ≤ δ := by
  classical
  have := hSind.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  set K := subgaussianRangeFinderFactor c with hKdef
  set F := frobNorm (A - truncatedSVD A r) with hF
  set N := nuclearNorm A with hN
  set L : ℝ := (Fintype.card t : ℝ) with hL
  have hK1 : 1 ≤ K := one_le_subgaussianRangeFinderFactor c.coe_nonneg
  have hlog : 0 < Real.log (4 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hs' : subgaussianEmbeddingDim c r (1 / 2) (δ / 2 / 2) ≤ Fintype.card s := by
    rwa [div_div, show (2 : ℝ) * 2 = 4 by norm_num]
  have hr0 : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hr)
  have hFN : 2 * √(r : ℝ) * F ≤ N := by
    have h := frobNorm_sub_truncatedSVD_le_nuclearNorm_div A hr
    rw [le_div_iff₀ (mul_pos two_pos hr0)] at h
    linarith
  rcases (frobNorm_nonneg (A - truncatedSVD A r)).eq_or_lt with hF0 | hF0
  · -- `‖E_r‖_F = 0`: on the range-finder event the sketch captures `A` and Hutch++ is exact
    have hRF := measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector A hSind hSsub
      hSiso (half_pos hδ) hs'
    exact (measureReal_abs_trace_sub_hutchpp_gt_le_of_frobNorm_sub_truncatedSVD_eq_zero
      A S G hF0.symm K (mul_nonneg hε.le (nuclearNorm_nonneg A))).trans
        (hRF.trans (half_le_self hδ.le))
  have hN0 : 0 < N := lt_of_lt_of_le (mul_pos (mul_pos two_pos hr0) hF0) hFN
  have hc' : 0 < (c' : ℝ) := by
    rcases c'.coe_nonneg.eq_or_lt with hc | hc
    · rw [← hc] at ht₁
      simp at ht₁
      linarith
    · exact hc
  have hK0 : 0 < K := by linarith
  have hsK : 0 < √K := Real.sqrt_pos.2 hK0
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have h := measureReal_abs_trace_sub_hutchpp_ge_le_of_isSubgaussianVector A hSind hSsub hSiso
    hGind hGsub hGvar hSG (half_pos hδ) hs' (τ := ε * N) (mul_nonneg hε.le (nuclearNorm_nonneg A))
  have h4 : 4 * r * F ^ 2 ≤ N ^ 2 := by
    have h2 := pow_le_pow_left₀ (mul_nonneg (mul_pos two_pos hr0).le hF0.le) hFN 2
    rwa [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), show (2 : ℝ) ^ 2 = 4 by norm_num]
      at h2
  have ha : 4 * L * r * ε ^ 2 / ((c' : ℝ) ^ 2 * K) ≤
      L * (ε * N) ^ 2 / ((c' : ℝ) ^ 2 * K * F ^ 2) := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hc' 2) hK0)
      (mul_pos (mul_pos (pow_pos hc' 2) hK0) (pow_pos hF0 2))]
    nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg (mul_nonneg hL0 (sq_nonneg ε))
      (mul_pos (pow_pos hc' 2) hK0).le)]
  have hb : 2 * L * √(r : ℝ) * ε / ((c' : ℝ) * √K) ≤
      L * (ε * N) / ((c' : ℝ) * √K * F) := by
    rw [div_le_div_iff₀ (mul_pos hc' hsK) (mul_pos (mul_pos hc' hsK) hF0)]
    nlinarith [mul_le_mul_of_nonneg_left hFN (mul_nonneg (mul_nonneg hL0 hε.le)
      (mul_pos hc' hsK).le)]
  have hC := hansonWrightConstant_pos.le
  have hx : Real.log (4 / δ) ≤ hansonWrightConstant *
      min (L * (ε * N) ^ 2 / ((c' : ℝ) ^ 2 * K * F ^ 2)) (L * (ε * N) / ((c' : ℝ) * √K * F)) := by
    rw [mul_min_of_nonneg _ _ hC]
    exact le_min (ht₁.trans (mul_le_mul_of_nonneg_left ha hC))
      (ht₂.trans (mul_le_mul_of_nonneg_left hb hC))
  have hexp : 2 * Real.exp (-(hansonWrightConstant *
      min (L * (ε * N) ^ 2 / ((c' : ℝ) ^ 2 * K * F ^ 2))
        (L * (ε * N) / ((c' : ℝ) * √K * F)))) ≤ δ / 2 := by
    calc _ ≤ 2 * Real.exp (-Real.log (4 / δ)) := by gcongr
      _ = δ / 2 := by
        rw [Real.exp_neg, Real.exp_log (div_pos four_pos hδ)]
        field_simp
        norm_num
  calc μ.real {ω | ε * N < |A.trace - hutchpp A (S ω) (G ω)|}
      ≤ μ.real {ω | ε * N ≤ |A.trace - hutchpp A (S ω) (G ω)|} :=
        measureReal_mono fun ω (hω : ε * N < _) => (le_of_lt hω : ε * N ≤ _)
    _ ≤ δ / 2 + δ / 2 := h.trans (by linarith)
    _ = δ := add_halves δ

/-- **Hutch++ does not underestimate a positive semidefinite trace by a factor $1 - \varepsilon$.**
With the hypotheses of
`NLAlib.measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`:
the sketch $\mathbf{S}^{\mathsf{H}}$, $\lvert s \rvert \ge 1$, has independent, isotropic,
sub-Gaussian rows with proxy $c$; the $n \times \ell$ residual test matrix $\mathbf{G}$ is
independent of $\mathbf{S}$ with independent entries, sub-Gaussian with variance proxy $c'$ and of
second moment $1$; $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 25 c^2 (r \log 21 + \log(2/(\delta/4)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 5c/2)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 5c/2}}\,.$$
Then for every real positive semidefinite $\mathbf{A}$
$$\mathbb{P}\bigl[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) <
(1 - \varepsilon)\operatorname{tr}\mathbf{A}\bigr] \le \delta\,,$$
since $\|\mathbf{A}\|_* = \operatorname{tr}\mathbf{A}$; the size is
`subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the factor is
`subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. The upper half is
`Matrix.PosSemidef.measureReal_hutchpp_gt_one_add_mul_trace_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 1]; there both halves together, with sign test matrices and
unspecified constants.
Result: hutchpp-relative-error -/
theorem _root_.Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector
    [Nonempty s] {A : Matrix n n ℝ} (hA : A.PosSemidef) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0} (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | hutchpp A (S ω) (G ω) < (1 - ε) * A.trace} ≤ δ := by
  have := hSind.isProbabilityMeasure
  have hN : nuclearNorm A = A.trace := by
    rw [hA.nuclearNorm_eq_re_trace, RCLike.re_to_real]
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector A hSind hSsub
      hSiso hGind hGsub hGvar hSG hr hε hδ hs ht₁ ht₂)
  simp only [Set.mem_ofPred_eq, hN] at hω ⊢
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-- **Hutch++ does not overestimate a positive semidefinite trace by a factor $1 + \varepsilon$.**
With the hypotheses of
`NLAlib.measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`:
the sketch $\mathbf{S}^{\mathsf{H}}$, $\lvert s \rvert \ge 1$, has independent, isotropic,
sub-Gaussian rows with proxy $c$; the $n \times \ell$ residual test matrix $\mathbf{G}$ is
independent of $\mathbf{S}$ with independent entries, sub-Gaussian with variance proxy $c'$ and of
second moment $1$; $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 25 c^2 (r \log 21 + \log(2/(\delta/4)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 5c/2)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 5c/2}}\,.$$
Then for every real positive semidefinite $\mathbf{A}$
$$\mathbb{P}\bigl[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) >
(1 + \varepsilon)\operatorname{tr}\mathbf{A}\bigr] \le \delta\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. The lower half
is `Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 1]; there both halves together, with sign test matrices and
unspecified constants.
Result: hutchpp-relative-error -/
theorem _root_.Matrix.PosSemidef.measureReal_hutchpp_gt_one_add_mul_trace_le_of_isSubgaussianVector
    [Nonempty s] {A : Matrix n n ℝ} (hA : A.PosSemidef) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0} (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | (1 + ε) * A.trace < hutchpp A (S ω) (G ω)} ≤ δ := by
  have := hSind.isProbabilityMeasure
  have hN : nuclearNorm A = A.trace := by
    rw [hA.nuclearNorm_eq_re_trace, RCLike.re_to_real]
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector A hSind hSsub
      hSiso hGind hGsub hGvar hSG hr hε hδ hs ht₁ ht₂)
  simp only [Set.mem_ofPred_eq, hN] at hω ⊢
  rw [abs_sub_comm]
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-! ### Arithmetic for the asymptotic form -/

/-- The sizes in the asymptotic form split into a $\sqrt{L}/\varepsilon$ part and an $L$ part. -/
private theorem asymptotic_size_split {γ Lg u B ε : ℝ} (hε : 0 < ε) (hu0 : 0 ≤ u)
    (hLg0 : 0 ≤ Lg) (hs : 20000 * (γ ^ 4 * (u / ε + Lg)) ≤ B) :
    20000 * γ ^ 4 * u ≤ B * ε ∧ 20000 * γ ^ 4 * Lg ≤ B := by
  have h4 : 0 ≤ γ ^ 4 := by positivity
  have hue : 0 ≤ u / ε := div_nonneg hu0 hε.le
  have h1 : 20000 * (γ ^ 4 * (u / ε)) ≤ B := le_trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hLg0) h4)
      (by norm_num)) hs
  have h2 : 20000 * (γ ^ 4 * Lg) ≤ B := le_trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hue) h4)
      (by norm_num)) hs
  refine ⟨?_, by linarith⟩
  rw [← mul_assoc, mul_div_assoc', div_le_iff₀ hε] at h1
  exact h1

/-- The target rank $r = \lfloor B/(4608\gamma^2) \rfloor$ of the asymptotic form: $r \ge 1$ and
$4608\gamma^2 r \le B \le 9216\gamma^2 r$. -/
private theorem exists_asymptotic_rank {γ Lg B : ℝ} (hγ1 : 1 ≤ γ) (hLg : 1 / 2 ≤ Lg)
    (hBL : 20000 * γ ^ 4 * Lg ≤ B) :
    ∃ r : ℕ, 0 < r ∧ 4608 * γ ^ 2 * r ≤ B ∧ B ≤ 9216 * γ ^ 2 * r := by
  have hγ2 : 0 < 4608 * γ ^ 2 := by positivity
  have hγ24 : γ ^ 2 ≤ γ ^ 4 := pow_le_pow_right₀ hγ1 (by norm_num)
  have hx1 : 1 ≤ B / (4608 * γ ^ 2) := by
    rw [le_div_iff₀ hγ2]
    nlinarith [mul_le_mul_of_nonneg_right hγ24 (by linarith : (0 : ℝ) ≤ Lg),
      mul_le_mul_of_nonneg_left hLg (sq_nonneg γ)]
  refine ⟨⌊B / (4608 * γ ^ 2)⌋₊, Nat.floor_pos.2 hx1, ?_, ?_⟩
  · have h := Nat.floor_le (le_trans zero_le_one hx1)
    rw [le_div_iff₀ hγ2] at h
    linarith
  · have h1 : (1 : ℝ) ≤ ⌊B / (4608 * γ ^ 2)⌋₊ := by exact_mod_cast Nat.floor_pos.2 hx1
    have h2 := Nat.lt_floor_add_one (B / (4608 * γ ^ 2))
    have h3 : B / (4608 * γ ^ 2) ≤ 2 * ⌊B / (4608 * γ ^ 2)⌋₊ := by linarith
    rw [div_le_iff₀ hγ2] at h3
    linarith

/-- The sketch size of the asymptotic form covers the range finder's:
$688\gamma^2(r + \ell_8) \le B$ when $\ell_8 \le 4L$. -/
private theorem asymptotic_sketch_size {γ Lg B l8 r : ℝ} (hγ1 : 1 ≤ γ) (hLg0 : 0 ≤ Lg)
    (hl8 : l8 ≤ 4 * Lg) (hBr : 4608 * γ ^ 2 * r ≤ B) (hBL : 20000 * γ ^ 4 * Lg ≤ B) :
    172 * γ ^ 2 * (r + l8) / (1 / 2) ^ 2 ≤ B := by
  have hγ24 : γ ^ 2 ≤ γ ^ 4 := pow_le_pow_right₀ hγ1 (by norm_num)
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hl8 (sq_nonneg γ),
    mul_le_mul_of_nonneg_right hγ24 hLg0]

/-- The first Hanson–Wright condition of the asymptotic form. -/
private theorem asymptotic_hansonWright₁ {γ K Lg u ℓ r ε : ℝ} (hγ1 : 1 ≤ γ) (hK0 : 0 < K)
    (hK11 : γ ^ 2 * K ≤ 11 * γ ^ 3) (hLg0 : 0 ≤ Lg) (hu2 : u ^ 2 = Lg) (hu0 : 0 ≤ u)
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (hℓu : 20000 * γ ^ 4 * u ≤ ℓ * ε)
    (hrε : 20000 * γ ^ 2 * u ≤ 9216 * r * ε) :
    3 * Lg ≤ hansonWrightConstant * (4 * ℓ * r * ε ^ 2 / (γ ^ 2 * K)) := by
  have hγ0 : 0 < γ := by linarith
  have hγ36 : γ ^ 3 ≤ γ ^ 6 := pow_le_pow_right₀ hγ1 (by norm_num)
  have hprod : (20000 * γ ^ 4 * u) * (20000 * γ ^ 2 * u) ≤ (ℓ * ε) * (9216 * r * ε) :=
    mul_le_mul hℓu hrε (by positivity) (by positivity)
  have h6 : (20000 * γ ^ 4 * u) * (20000 * γ ^ 2 * u) = 400000000 * γ ^ 6 * Lg := by
    rw [← hu2]
    ring
  have hX : 588 * Lg ≤ 4 * ℓ * r * ε ^ 2 / (γ ^ 2 * K) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hK11 (by positivity : (0 : ℝ) ≤ 588 * Lg),
      mul_le_mul_of_nonneg_right hγ36 hLg0]
  have hX0 : 0 ≤ 4 * ℓ * r * ε ^ 2 / (γ ^ 2 * K) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right le_hansonWrightConstant hX0]

/-- The second Hanson–Wright condition of the asymptotic form. -/
private theorem asymptotic_hansonWright₂ {γ K Lg u ℓ r ε : ℝ} (hγ1 : 1 ≤ γ) (hK0 : 0 < K)
    (hK11 : γ ^ 2 * K ≤ 11 * γ ^ 3) (hLg0 : 0 ≤ Lg) (hu2 : u ^ 2 = Lg) (hu0 : 0 ≤ u)
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (hℓu : 20000 * γ ^ 4 * u ≤ ℓ * ε)
    (hrL : 20000 * γ ^ 2 * Lg ≤ 9216 * r) :
    3 * Lg ≤ hansonWrightConstant * (2 * ℓ * √r * ε / (γ * √K)) := by
  have hγ0 : 0 < γ := by linarith
  have hγ310 : γ ^ 3 ≤ γ ^ 10 := pow_le_pow_right₀ hγ1 (by norm_num)
  set Y := 2 * ℓ * √r * ε / (γ * √K) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY2 : Y ^ 2 = 4 * (ℓ * ε) ^ 2 * r / (γ ^ 2 * K) := by
    rw [hY, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hK0.le]
    ring
  have hsq : (20000 * γ ^ 4 * u) ^ 2 ≤ (ℓ * ε) ^ 2 := pow_le_pow_left₀ (by positivity) hℓu 2
  have hprod : (20000 * γ ^ 4 * u) ^ 2 * (20000 * γ ^ 2 * Lg) ≤ (ℓ * ε) ^ 2 * (9216 * r) :=
    mul_le_mul hsq hrL (by positivity) (by positivity)
  have h8 : (20000 * γ ^ 4 * u) ^ 2 * (20000 * γ ^ 2 * Lg) =
      8000000000000 * γ ^ 10 * Lg ^ 2 := by
    rw [mul_pow, hu2]
    ring
  have hY' : (588 * Lg) ^ 2 ≤ Y ^ 2 := by
    rw [hY2, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hK11 (sq_nonneg (588 * Lg)),
      mul_le_mul_of_nonneg_right hγ310 (sq_nonneg Lg)]
  have hYL : 588 * Lg ≤ Y := (pow_le_pow_iff_left₀ (by positivity) hY0 two_ne_zero).1 hY'
  nlinarith [mul_le_mul_of_nonneg_right le_hansonWrightConstant hY0]

-- The theorem's name alone exceeds 100 characters.
/-- **$O(c^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta)))$ products suffice for Hutch++
to relative error $\varepsilon$ in the nuclear norm**: there is an absolute constant $C > 0$
(the proof takes $C = 20000$) such that if the sketch $\mathbf{S}^{\mathsf{H}}$ of the
$n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$, $\lvert s \rvert \ge 1$, has
independent, isotropic, sub-Gaussian rows with proxy $c$, the $n \times \lvert t \rvert$ residual
test matrix $\mathbf{G}$ is independent of $\mathbf{S}$ with independent entries that each satisfy
the sub-Gaussian moment generating function bound with variance proxy $c$ and have second moment
$1$, $\varepsilon > 0$, $0 < \delta \le 1/2$ and both
$\lvert s \rvert$ and $\lvert t \rvert$ are at least
$Cc^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$, then for every real square
$\mathbf{A}$
$$\mathbb{P}\bigl[\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert > \varepsilon\|\mathbf{A}\|_*\bigr] \le
\delta\,,$$ with $m = 2\lvert s \rvert + \lvert t \rvert$ products in all. The asymptotic form of
`NLAlib.measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector`, at
$r = \lfloor \lvert s \rvert/(4608c^2) \rfloor$; the proxy stays in the threshold, and isotropy
forces $c \ge 1$. No cap on $\varepsilon$ is needed: with $L = \log(1/\delta)$, the residual
size gives $\ell\varepsilon \ge Cc^4\sqrt{L}$ and the sketch size $r\varepsilon \gtrsim c^2\sqrt{L}$
and $r \gtrsim c^2 L$, which cover both Hanson–Wright conditions.
[MeyerMuscoMuscoWoodruff2021, Theorem 5 and Theorem 1]; there with sign test matrices ($c = 1$).
Asymptotic: NLAlib.measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector
Result: hutchpp-relative-error -/
theorem exists_forall_measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector
    :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n s t : Type} [MeasurableSpace Ω] [Fintype n]
      [Fintype s] [Fintype t] [DecidableEq n] [Nonempty s] (μ : Measure Ω) (A : Matrix n n ℝ)
      (S : Ω → Matrix n s ℝ) (G : Ω → Matrix n t ℝ) (c : ℝ≥0) (ε δ : ℝ),
      iIndepFun (fun i ω => (S ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ) →
      iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ →
      (∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c μ) → (∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) →
      IndepFun S G μ → 0 < ε → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 4 * (√(Real.log (1 / δ)) / ε + Real.log (1 / δ))) ≤ Fintype.card s →
      C * ((c : ℝ) ^ 4 * (√(Real.log (1 / δ)) / ε + Real.log (1 / δ))) ≤ Fintype.card t →
      μ.real {ω | ε * nuclearNorm A < |A.trace - hutchpp A (S ω) (G ω)|} ≤ δ := by
  refine ⟨20000, by norm_num, ?_⟩
  intro Ω n s t _ _ _ _ _ _ μ A S G c ε δ hSind hSsub hSiso hGind hGsub hGvar hSG hε hδ hδ2 hs ht
  classical
  have := hSind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · -- with `n` empty the error is `0` and the event is empty
    have hset : {ω | ε * nuclearNorm A < |A.trace - hutchpp A (S ω) (G ω)|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hutchpp_eq_trace_of_rsvd_eq (Subsingleton.elim _ _), sub_self, abs_zero]
      exact mul_nonneg hε.le (nuclearNorm_nonneg A)
    rw [hset, measureReal_empty]
    exact hδ.le
  set γ : ℝ := (c : ℝ) with hγ
  have hγ1 : 1 ≤ γ := (hSsub (Classical.arbitrary s)).one_le_of_isIsotropic
    (hSiso (Classical.arbitrary s))
  set Lg := Real.log (1 / δ) with hLg
  set u := √Lg with hu
  set B : ℝ := (Fintype.card s : ℝ) with hB
  set ℓ : ℝ := (Fintype.card t : ℝ) with hℓ
  set K := subgaussianRangeFinderFactor c with hK
  -- logarithms
  have hδ1 : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hLg2 : Real.log 2 ≤ Lg := Real.log_le_log two_pos hδ1
  have hLg0 : 0 < Lg := by linarith
  have hLg12 : 1 / 2 ≤ Lg := hlog2.trans hLg2
  have hu2 : u ^ 2 = Lg := Real.sq_sqrt hLg0.le
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hlog4 : Real.log (4 / δ) ≤ 3 * Lg := by
    rw [show 4 / δ = 2 ^ 2 * (1 / δ) by ring, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast
    linarith
  have hlog8 : Real.log (2 / (δ / 4)) ≤ 4 * Lg := by
    rw [show 2 / (δ / 4) = 2 ^ 3 * (1 / δ) by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    linarith
  -- powers of the proxy
  have hγ0 : 0 < γ := by linarith
  have hK1 : 1 ≤ K := one_le_subgaussianRangeFinderFactor c.coe_nonneg
  have hK0 : 0 < K := by linarith
  have hK11 : γ ^ 2 * K ≤ 11 * γ ^ 3 := by
    have h := mul_le_mul_of_nonneg_left (subgaussianRangeFinderFactor_le (c : ℝ)) (sq_nonneg γ)
    nlinarith
  -- the sizes and the target rank
  obtain ⟨hBu, hBL⟩ := asymptotic_size_split hε hu0 hLg0.le hs
  have hℓu := (asymptotic_size_split hε hu0 hLg0.le ht).1
  obtain ⟨r, hr0, hBr, hrB⟩ := exists_asymptotic_rank hγ1 hLg12 hBL
  have hs' : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s :=
    (subgaussianEmbeddingDim_le (c : ℝ) r (1 / 2) (by positivity) (by linarith)).trans
      (asymptotic_sketch_size hγ1 hLg0.le hlog8 hBr hBL)
  -- the two Hanson–Wright conditions
  have hrε : 20000 * γ ^ 2 * u ≤ 9216 * r * ε := by
    have h1 : 20000 * γ ^ 4 * u ≤ 9216 * γ ^ 2 * r * ε :=
      hBu.trans (mul_le_mul_of_nonneg_right hrB hε.le)
    have h2 : γ ^ 2 * (20000 * γ ^ 2 * u) ≤ γ ^ 2 * (9216 * r * ε) :=
      calc γ ^ 2 * (20000 * γ ^ 2 * u) = 20000 * γ ^ 4 * u := by ring
        _ ≤ 9216 * γ ^ 2 * r * ε := h1
        _ = γ ^ 2 * (9216 * r * ε) := by ring
    exact le_of_mul_le_mul_left h2 (pow_pos hγ0 2)
  have hrL : 20000 * γ ^ 2 * Lg ≤ 9216 * r := by
    have h2 : γ ^ 2 * (20000 * γ ^ 2 * Lg) ≤ γ ^ 2 * (9216 * r) :=
      calc γ ^ 2 * (20000 * γ ^ 2 * Lg) = 20000 * γ ^ 4 * Lg := by ring
        _ ≤ B := hBL
        _ ≤ 9216 * γ ^ 2 * r := hrB
        _ = γ ^ 2 * (9216 * r) := by ring
    exact le_of_mul_le_mul_left h2 (pow_pos hγ0 2)
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have ht₁ := hlog4.trans
    (asymptotic_hansonWright₁ hγ1 hK0 hK11 hLg0.le hu2 hu0 hε hℓ0 hr0' hℓu hrε)
  have ht₂ := hlog4.trans
    (asymptotic_hansonWright₂ hγ1 hK0 hK11 hLg0.le hu2 hu0 hε hℓ0 hr0' hℓu hrL)
  exact measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector A hSind
    hSsub hSiso hGind hGsub hGvar hSG hr0 hε hδ hs' ht₁ ht₂

end NLAlib
