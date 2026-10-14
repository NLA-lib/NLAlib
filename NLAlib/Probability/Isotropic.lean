/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Law

/-!
# Isotropic random vectors

A random vector `X : Ω → n → 𝕜` is isotropic when its coordinates are square integrable and its
second-moment matrix `E [X Xᴴ]` is the identity. No mean is assumed and nothing is said about
`E [X Xᵀ]`. Rademacher and standard Gaussian vectors are isotropic, and so are `√n` times a uniform
point of the unit sphere and `√n` times a column of a Haar-distributed unitary matrix.

Isotropy is what trace estimation and the second moment of a sketch use: for isotropic `X`,
`E [Xᴴ A X] = tr A` (Hutchinson) and `E ‖A X‖² = ‖A‖_F²`. Fourth moments, which the variance of
these estimators needs, are separate hypotheses where they are used.

## Main definitions

* `NLAlib.IsIsotropic X μ`: `X` has square-integrable coordinates and `E [X Xᴴ] = 1`.

## Main results

* `NLAlib.IsIsotropic.integral_quadForm`: Hutchinson's identity `E [Xᴴ A X] = tr A`.
* `NLAlib.IsIsotropic.integral_norm_mulVec_sq`: `E ‖A X‖² = ‖A‖_F²`.
* `NLAlib.IsIsotropic.integral_norm_dotProduct_sq`: `E |⟨u, X⟩|² = ‖u‖²`.
* `NLAlib.IsIsotropic.mulVec`: maps with orthonormal rows preserve isotropy.
* `NLAlib.IsIsotropic.of_iIndepFun`: independent coordinates with mean zero and unit second
  moment.
* `ProbabilityTheory.HasLaw.isIsotropic_iff`: isotropy depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {X : Ω → n → 𝕜}

/-- A random vector `X` in `𝕜ⁿ` is isotropic for `μ` when its coordinates are square integrable
and its second-moment matrix is the identity: `∫ X i * conj (X j) = if i = j then 1 else 0`.
No mean is assumed and nothing is said about `E [X Xᵀ]`. -/
structure IsIsotropic (X : Ω → n → 𝕜) (μ : Measure Ω) : Prop where
  /-- Each coordinate is square integrable. -/
  memLp : ∀ i, MemLp (fun ω => X ω i) 2 μ
  /-- The second-moment matrix `E [X Xᴴ]` is the identity. -/
  integral_mul_star : ∀ i j, ∫ ω, X ω i * star (X ω j) ∂μ = if i = j then 1 else 0

namespace IsIsotropic

/-- The products of two coordinates of an isotropic vector are integrable. -/
theorem integrable_mul_star (hX : IsIsotropic X μ) (i j : n) :
    Integrable (fun ω => X ω i * star (X ω j)) μ := by
  sorry

/-- The quadratic form of an isotropic vector is integrable. -/
theorem integrable_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    Integrable (fun ω => quadForm A (X ω)) μ := by
  sorry

/-- **Hutchinson's identity**: for an isotropic probe `X`, the quadratic form `Xᴴ A X` is an
unbiased estimator of `tr A`. -/
theorem integral_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    ∫ ω, quadForm A (X ω) ∂μ = A.trace := by
  sorry

/-- The squared Euclidean norm of `A X` is integrable for an isotropic `X`. -/
theorem integrable_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2) μ := by
  sorry

/-- `E ‖A X‖² = ‖A‖_F²` for an isotropic `X`. -/
theorem integral_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : ∫ ω, ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2 ∂μ = frobNorm A ^ 2 := by
  sorry

/-- `E |⟨u, X⟩|² = ‖u‖²` for an isotropic `X`: the second moment behind the
Johnson–Lindenstrauss lemma. Over `ℝ`, `‖r‖ ^ 2 = r ^ 2` by `Real.norm_eq_abs` and `sq_abs`. -/
theorem integral_norm_dotProduct_sq (hX : IsIsotropic X μ) (u : n → 𝕜) :
    ∫ ω, ‖u ⬝ᵥ X ω‖ ^ 2 ∂μ = ‖WithLp.toLp 2 u‖ ^ 2 := by
  sorry

/-- The mean squared Euclidean norm of an isotropic vector is the dimension. -/
theorem integral_norm_sq (hX : IsIsotropic X μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ = Fintype.card n := by
  sorry

/-- A map with orthonormal rows preserves isotropy: if `U Uᴴ = 1` (that is,
`HasOrthonormalCols Uᴴ`), then `U X` is isotropic. Rotations of isotropic vectors, the rows of a
randomized Hadamard transform and rescaled columns of a Haar frame get their isotropy this way. -/
theorem mulVec (hX : IsIsotropic X μ) {m : Type*} [Fintype m] [DecidableEq m]
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols Uᴴ) : IsIsotropic (fun ω => U *ᵥ X ω) μ := by
  sorry

/-- Independent coordinates with mean zero and unit second moment form an isotropic vector. -/
theorem of_iIndepFun [IsProbabilityMeasure μ] (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL2 : ∀ i, MemLp (fun ω => X ω i) 2 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) : IsIsotropic X μ := by
  sorry

end IsIsotropic

/-- Isotropy depends only on the law: a random vector with law `ν` is isotropic exactly when the
identity is isotropic for `ν`. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropic_iff {ν : Measure (n → 𝕜)}
    (hX : HasLaw X ν μ) : IsIsotropic X μ ↔ IsIsotropic id ν := by
  sorry

end NLAlib
