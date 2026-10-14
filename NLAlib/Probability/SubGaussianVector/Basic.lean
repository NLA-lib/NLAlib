/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Sub-Gaussian random vectors

`NLAlib.IsSubgaussianVector X c μ` says that every real linear functional `re (u ⬝ᵥ X)` of the
random vector `X : Ω → n → 𝕜` is sub-Gaussian with proxy `c ‖u‖²`. Every real-linear functional
of `𝕜ⁿ` has this form, so over `ℂ` the real and imaginary parts are constrained alike; over `ℝ`,
`re` is the identity (`RCLike.re_to_real`). It is the hypothesis of the tails of `‖X‖²` and of the
net argument for random matrices with sub-Gaussian rows.

Standard Gaussian and Rademacher vectors are sub-Gaussian vectors with proxy `1`, so are real
vectors with independent sub-Gaussian coordinates, and linear images of sub-Gaussian vectors are
sub-Gaussian vectors.

## Main definitions

* `NLAlib.IsSubgaussianVector X c μ`.

## Main results

* `NLAlib.IsSubgaussianVector.mulVec`: `A X` has proxy `c ‖A‖²`.
* `NLAlib.IsSubgaussianVector.of_iIndepFun`: independent real sub-Gaussian coordinates.
* `NLAlib.isSubgaussianVector_of_hasLaw_gaussianVector`,
  `NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`: proxy `1`.
* `ProbabilityTheory.HasLaw.isSubgaussianVector_iff`: the property depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {𝕜 : Type*} [RCLike 𝕜] {X : Ω → n → 𝕜} {c : ℝ≥0}

/-- `X` is a sub-Gaussian random vector with proxy `c` under `μ`: every real linear functional
`re (u ⬝ᵥ X)` is sub-Gaussian with proxy `c ‖u‖²`. -/
structure IsSubgaussianVector (X : Ω → n → 𝕜) (c : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- Every real linear functional of `X` is sub-Gaussian with proxy `c ‖u‖²`. -/
  hasSubgaussianMGF : ∀ u : n → 𝕜,
    HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ X ω)) (c * ‖WithLp.toLp 2 u‖₊ ^ 2) μ

namespace IsSubgaussianVector

/-- A larger proxy. -/
theorem mono (h : IsSubgaussianVector X c μ) {d : ℝ≥0} (hcd : c ≤ d) :
    IsSubgaussianVector X d μ := by
  refine ⟨fun u => (h.hasSubgaussianMGF u).mono ?_⟩
  gcongr

/-- The property depends only on the almost-everywhere class of the vector. -/
theorem congr {Y : Ω → n → 𝕜} (h : IsSubgaussianVector X c μ) (hXY : X =ᵐ[μ] Y) :
    IsSubgaussianVector Y c μ := by
  refine ⟨fun u => (h.hasSubgaussianMGF u).congr ?_⟩
  filter_upwards [hXY] with ω hω
  rw [hω]

/-- The real part of each coordinate is sub-Gaussian with proxy `c`. -/
theorem hasSubgaussianMGF_re_apply (h : IsSubgaussianVector X c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.re (X ω i)) c μ := by
  classical
  simpa only [single_one_dotProduct, PiLp.toLp_single, PiLp.nnnorm_single, nnnorm_one, one_pow,
    mul_one] using h.hasSubgaussianMGF (Pi.single i 1)

private lemma hasSubgaussianMGF_im_apply (h : IsSubgaussianVector X c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.im (X ω i)) c μ := by
  classical
  have hu := h.hasSubgaussianMGF (Pi.single i (-RCLike.I))
  simp only [single_dotProduct, PiLp.toLp_single, PiLp.nnnorm_single, nnnorm_neg, neg_mul,
    map_neg, RCLike.I_mul_re, neg_neg] at hu
  refine hu.mono (mul_le_of_le_one_right' (pow_le_one₀ bot_le ?_))
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, RCLike.norm_I]
  split_ifs <;> norm_num

/-- The coordinates of a sub-Gaussian vector have moments of every order. -/
theorem memLp_apply (h : IsSubgaussianVector X c μ) (i : n) (p : ℝ≥0) :
    MemLp (fun ω => X ω i) p μ := by
  refine memLp_re_im_iff.mp ⟨(h.hasSubgaussianMGF_re_apply i).memLp p, ?_⟩
  exact (h.hasSubgaussianMGF_im_apply i).memLp p

/-- A sub-Gaussian vector is almost everywhere measurable. -/
theorem aemeasurable (h : IsSubgaussianVector X c μ) : AEMeasurable X μ :=
  aemeasurable_pi_lambda _ fun i => (h.memLp_apply i 1).aestronglyMeasurable.aemeasurable

/-- A sub-Gaussian vector has mean zero. -/
theorem integral_apply_eq_zero [IsProbabilityMeasure μ] (h : IsSubgaussianVector X c μ)
    (i : n) : ∫ ω, X ω i ∂μ = 0 := by
  have hint : Integrable (fun ω => X ω i) μ :=
    memLp_one_iff_integrable.mp (by simpa using h.memLp_apply i 1)
  refine RCLike.ext ?_ ?_
  · rw [← integral_re hint, (h.hasSubgaussianMGF_re_apply i).integral_eq_zero, map_zero]
  · rw [← integral_im hint, (h.hasSubgaussianMGF_im_apply i).integral_eq_zero, map_zero]

/-- A linear image of a sub-Gaussian vector is a sub-Gaussian vector with proxy `c ‖A‖²`. -/
theorem mulVec {m : Type*} [Fintype m] (h : IsSubgaussianVector X c μ) (A : Matrix m n 𝕜) :
    IsSubgaussianVector (fun ω => A *ᵥ X ω) (c * ‖specNorm A‖₊ ^ 2) μ := by
  refine ⟨fun u => ?_⟩
  have hu := h.hasSubgaussianMGF (Aᵀ *ᵥ u)
  simp only [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec] at hu
  refine hu.mono ?_
  rw [mul_assoc]
  gcongr
  rw [← mul_pow]
  gcongr
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_of_nonneg (specNorm_nonneg A), ← Matrix.mulVec_transpose, ← specNorm_transpose]
  exact norm_toLp_mulVec_le Aᵀ u

/-- A real vector with independent coordinates, each sub-Gaussian with proxy `c`, is a
sub-Gaussian vector with proxy `c`. -/
theorem of_iIndepFun {X : Ω → n → ℝ} (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) : IsSubgaussianVector X c μ := by
  refine ⟨fun u => ?_⟩
  have hu := HasSubgaussianMGF.sum_const_mul_of_iIndepFun hind (s := Finset.univ)
    (fun i _ => h i) u
  have hc : ∑ i, ‖u i‖₊ ^ 2 * c = c * ‖WithLp.toLp 2 u‖₊ ^ 2 := by
    rw [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt, ← Finset.sum_mul, mul_comm]
  rw [hc] at hu
  simpa only [RCLike.re_to_real, dotProduct] using hu

end IsSubgaussianVector

/-- Being a sub-Gaussian vector depends only on the law. -/
theorem _root_.ProbabilityTheory.HasLaw.isSubgaussianVector_iff {ν : Measure (n → 𝕜)}
    (hX : HasLaw X ν μ) : IsSubgaussianVector X c μ ↔ IsSubgaussianVector id c ν := by
  have key : ∀ u : n → 𝕜, ∀ d : ℝ≥0, HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ X ω)) d μ ↔
      HasSubgaussianMGF (fun x => RCLike.re (u ⬝ᵥ id x)) d ν := by
    intro u d
    have hf : Measurable fun x : n → 𝕜 => RCLike.re (u ⬝ᵥ x) := by
      simp only [dotProduct]
      fun_prop
    have hfX : HasLaw ((fun x : n → 𝕜 => RCLike.re (u ⬝ᵥ x)) ∘ X)
        (ν.map fun x => RCLike.re (u ⬝ᵥ x)) μ :=
      HasLaw.comp ⟨hf.aemeasurable, rfl⟩ hX
    change HasSubgaussianMGF ((fun x : n → 𝕜 => RCLike.re (u ⬝ᵥ x)) ∘ X) d μ ↔
      HasSubgaussianMGF (fun x : n → 𝕜 => RCLike.re (u ⬝ᵥ x)) d ν
    rw [← HasSubgaussianMGF.id_map_iff hfX.aemeasurable, hfX.map_eq,
      ← HasSubgaussianMGF.id_map_iff hf.aemeasurable]
  exact ⟨fun h => ⟨fun u => (key u _).mp (h.hasSubgaussianMGF u)⟩,
    fun h => ⟨fun u => (key u _).mpr (h.hasSubgaussianMGF u)⟩⟩

/-- A standard Gaussian vector is a sub-Gaussian vector with proxy `1`. -/
theorem isSubgaussianVector_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsSubgaussianVector X 1 μ := by
  refine ⟨fun u => ?_⟩
  simpa only [RCLike.re_to_real, one_mul] using
    hasSubgaussianMGF_of_hasLaw_gaussianReal (hasLaw_dotProduct_of_hasLaw_gaussianVector hX u)

/-- A vector of independent random signs is a sub-Gaussian vector with proxy `1`. -/
theorem isSubgaussianVector_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsSubgaussianVector X 1 μ := by
  exact IsSubgaussianVector.of_iIndepFun hX.iIndepFun_eval
    fun i => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hX.eval i)

end NLAlib
