/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianConcentration
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Gaussian concentration for functions of Gaussian matrices

A function of a standard Gaussian matrix that is $L$-Lipschitz for the Frobenius distance is
sub-Gaussian about its mean with proxy $L^2$. The Lipschitz hypothesis is the explicit inequality
$\lvert f(\mathbf{A}) - f(\mathbf{B}) \rvert \le L \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$:
matrices carry no global metric in this library, and the singular values satisfy exactly this
inequality (`NLAlib.abs_singularValues_sub_le_frobNorm`). The proof reads the matrix as a standard
Gaussian vector indexed by $m \times n$.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix`: the upper tail.
* `NLAlib.measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`: the upper tail
  for a function of the Gaussian matrix and an independent random factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ} {f : Matrix m n ℝ → ℝ} {L : ℝ≥0}

/-- The Frobenius-Lipschitz inequality for $f$, read on the flattened entries. -/
private theorem lipschitzWith_curry (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) :
    LipschitzWith L (fun x : EuclideanSpace ℝ (m × n) =>
      f (Matrix.of (Function.curry (WithLp.ofLp x)))) := by
  refine EuclideanSpace.lipschitzWith_ofLp_iff
    (f := fun x => f (Matrix.of (Function.curry x))) |>.2 ?_
  intro x y
  have h := hf (Matrix.of (Function.curry x)) (Matrix.of (Function.curry y))
  rwa [frobNorm_eq_norm_toLp_uncurry] at h

/-- A Frobenius-Lipschitz function of a Gaussian matrix is integrable. -/
theorem integrable_comp_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) : Integrable (fun ω => f (X ω)) μ := by
  exact integrable_comp_of_lipschitzWith_of_hasLaw_gaussianVector
    (f := fun x => f (Matrix.of (Function.curry x)))
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) (lipschitzWith_curry hf)

/-- **Gaussian concentration** for a function of a Gaussian matrix that is $L$-Lipschitz for the
Frobenius distance
($\lvert f(\mathbf{A}) - f(\mathbf{B}) \rvert \le L \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$):
$f(\mathbf{G}) - \mathbb{E} f(\mathbf{G})$ is sub-Gaussian with proxy $L^2$.
[Vershynin2018, Theorem 5.2.2] gives a sub-Gaussian norm bound up to an absolute constant. The
log-Sobolev proof here gives the stated moment-generating function bound. -/
theorem hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ := by
  exact hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector
    (f := fun x => f (Matrix.of (Function.curry x)))
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) (lipschitzWith_curry hf)

/-- The upper tail: for $f$ $L$-Lipschitz for the Frobenius distance and $t \ge 0$,
$\mathbb{P}\bigl[f(\mathbf{G}) \ge \mathbb{E} f(\mathbf{G}) + t\bigr] \le \exp(-t^2 / (2L^2))$. -/
theorem measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  exact measureReal_ge_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector
    (f := fun x => f (Matrix.of (Function.curry x)))
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) (lipschitzWith_curry hf) ht

/-! ### An independent random factor -/

/-- The fixed-factor step of the independent-factor concentration: under the Gaussian law, the
event $f(\mathbf{G}) > c + Lt$ has probability at most $e^{-t^2/2}$. -/
private theorem gaussianMatrix_lt_le {g : Matrix m n ℝ → ℝ} {L c : ℝ} (hL0 : 0 ≤ L)
    (hlip : ∀ A B, |g A - g B| ≤ L * frobNorm (A - B))
    (hmean : ∫ A, g A ∂(gaussianMatrix m n) ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianMatrix m n).real {A | c + L * t < g A} ≤ Real.exp (-t ^ 2 / 2) := by
  rcases hL0.eq_or_lt with hL | hL
  · subst hL
    have hconst : ∀ A, g A = ∫ B, g B ∂(gaussianMatrix m n) := by
      intro A
      have h : ∀ B, g B = g A := fun B => by
        have := hlip B A
        rw [zero_mul] at this
        exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
      simp only [h, integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hempty : {A | c + 0 * t < g A} = ∅ := by
      ext A
      simp only [Set.mem_ofPred_eq, zero_mul, add_zero, Set.mem_empty_iff_false, iff_false,
        not_lt]
      rw [hconst A]
      exact hmean
    rw [hempty, measureReal_empty]
    positivity
  · have hlip' : ∀ A B, |g A - g B| ≤ (‖L‖₊ : ℝ) * frobNorm (A - B) := by
      intro A B
      rw [coe_nnnorm, Real.norm_of_nonneg hL.le]
      exact hlip A B
    have h := measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix (X := id) (f := g)
      (μ := gaussianMatrix m n) HasLaw.id hlip' (t := L * t) (by positivity)
    rw [coe_nnnorm, Real.norm_of_nonneg hL.le] at h
    have he : -(L * t) ^ 2 / (2 * L ^ 2) = -t ^ 2 / 2 := by
      field_simp
    rw [he] at h
    refine (measureReal_mono (fun A (hA : c + L * t < g A) => ?_)).trans h
    change ∫ B, g (id B) ∂(gaussianMatrix m n) + L * t ≤ g (id A)
    simp only [id]
    linarith

/-- **Gaussian concentration with an independent random factor**: if $\mathbf{G}$ is a standard
Gaussian matrix independent of $Y$ and, for each $y$, $f(y, \cdot)$ is $L(y)$-Lipschitz for the
Frobenius distance, with $L \ge 0$ and Gaussian mean at most $c(y)$, then for $t \ge 0$
$$\mathbb{P}[f(Y, \mathbf{G}) > c(Y) + L(Y)\,t] \le e^{-t^2/2}\,.$$
The fixed-factor form is `NLAlib.measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix`; this one
conditions on $Y$ through the product law of the pair. $L \ge 0$ is needed when the matrices are
empty, where the Lipschitz hypothesis holds for every $L$.
Result: gaussian-lipschitz-concentration -/
theorem measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun {β : Type*}
    [MeasurableSpace β] {X : Ω → Matrix m n ℝ} {Y : Ω → β} (hX : HasLaw X (gaussianMatrix m n) μ)
    (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ) {f : β → Matrix m n ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {L c : β → ℝ} (hL : Measurable L)
    (hL0 : ∀ y, 0 ≤ L y) (hc : Measurable c)
    (hlip : ∀ y A B, |f y A - f y B| ≤ L y * frobNorm (A - B))
    (hmean : ∀ y, ∫ A, f y A ∂(gaussianMatrix m n) ≤ c y) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | c (Y ω) + L (Y ω) * t < f (Y ω) (X ω)} ≤ Real.exp (-t ^ 2 / 2) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  set E : Set (β × Matrix m n ℝ) := {p | c p.1 + L p.1 * t < f p.1 p.2} with hE_def
  have hE : MeasurableSet E :=
    measurableSet_lt ((hc.comp measurable_fst).add ((hL.comp measurable_fst).mul_const t)) hf
  have hpair : AEMeasurable (fun ω => (Y ω, X ω)) μ := hY.prodMk hX.aemeasurable
  have hmap : μ.map (fun ω => (Y ω, X ω)) = (μ.map Y).prod (gaussianMatrix m n) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY hX.aemeasurable).1 hXY, hX.map_eq]
  have hset : {ω | c (Y ω) + L (Y ω) * t < f (Y ω) (X ω)} = (fun ω => (Y ω, X ω)) ⁻¹' E := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hE_def]
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY
  have hslice : ∀ y, gaussianMatrix m n (Prod.mk y ⁻¹' E) ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := fun y => by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (gaussianMatrix_lt_le (hL0 y) (hlip y) (hmean y) ht)
  rw [hset, measureReal_def, ← Measure.map_apply_of_aemeasurable hpair hE, hmap,
    Measure.prod_apply hE]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ y, gaussianMatrix m n (Prod.mk y ⁻¹' E) ∂(μ.map Y)
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) ∂(μ.map Y) := lintegral_mono hslice
    _ = ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
        rw [lintegral_const, measure_univ, mul_one]

end NLAlib
