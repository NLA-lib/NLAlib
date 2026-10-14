/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smoothing Lipschitz functions by convolution with a bump function

Convolution with a normed bump function (a probability kernel) preserves the Lipschitz constant,
and on a finite-dimensional space it turns a `K`-Lipschitz function into a `C^∞` one, again
`K`-Lipschitz and uniformly within any `ε > 0` of the original. Upstream candidates for
`Mathlib.Analysis.Calculus.BumpFunction.Convolution`.

## Main results

* `ContDiffBump.lipschitzWith_normed_convolution`: `φ.normed μ ⋆ g` is `K`-Lipschitz when `g` is.
* `LipschitzWith.exists_contDiff_lipschitzWith_dist_le`: uniform smooth approximation of a
  Lipschitz function with the same Lipschitz constant.
-/

@[expose] public section

open ContinuousLinearMap MeasureTheory Metric
open scoped Convolution NNReal ContDiff

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [HasContDiffBump G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ContDiffBump

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]

/-- Convolution with a normed bump function preserves the Lipschitz constant: if `g` is
`K`-Lipschitz, so is `φ.normed μ ⋆[lsmul ℝ ℝ, μ] g`. -/
theorem lipschitzWith_normed_convolution {c : G} (φ : ContDiffBump c) {g : G → F} {K : ℝ≥0}
    (hg : LipschitzWith K g) : LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) := by
  have hex : ConvolutionExists (φ.normed μ) g (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left _ φ.continuous_normed
      hg.continuous.locallyIntegrable
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hi (z : G) : Integrable (fun t => φ.normed μ t • g (z - t)) μ := hex z
  rw [dist_eq_norm, convolution_lsmul, convolution_lsmul, ← integral_sub (hi x) (hi y)]
  calc ‖∫ t, (φ.normed μ t • g (x - t) - φ.normed μ t • g (y - t)) ∂μ‖
      ≤ ∫ t, φ.normed μ t * (K * dist x y) ∂μ := by
        refine norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) ?_
        refine Filter.Eventually.of_forall fun t => ?_
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t), ← dist_eq_norm]
        refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
        simpa only [dist_sub_right] using hg.dist_le_mul (x - t) (y - t)
    _ = K * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

end ContDiffBump

/-- **Smoothing a Lipschitz function**: on a finite-dimensional space, a `K`-Lipschitz function
is uniformly within `ε` of a `C^∞` function that is again `K`-Lipschitz (convolve with a normed
bump function supported in a ball of radius `ε / (K + 1)`). -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_le [CompleteSpace F] {f : G → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : G → F, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧ ∀ x, dist (g x) (f x) ≤ ε := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  set μ : Measure G := Measure.addHaar
  set r : ℝ := ε / (K + 1) with hr
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hr0 : 0 < r := div_pos hε hK
  have hKr : K * r ≤ ε := by
    rw [hr, mul_div_assoc', div_le_iff₀ hK]
    nlinarith [K.coe_nonneg]
  let φ : ContDiffBump (0 : G) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, φ.lipschitzWith_normed_convolution hf, fun x => ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.continuous.locallyIntegrable
  · refine φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable fun y hy => ?_
    refine (hf.dist_le_mul y x).trans ?_
    exact (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le K.coe_nonneg).trans hKr
