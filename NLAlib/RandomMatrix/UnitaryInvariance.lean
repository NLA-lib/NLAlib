/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.PolarFrames
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.Invariance

/-!
# Unitarily invariant laws of random matrices

A law `ν` on `n × k` matrices is **left unitarily invariant** when `U Q` has law `ν` for `Q ~ ν`
and every unitary (over `ℝ`, orthogonal) `U`, and **right unitarily invariant** when `Q V` does
for every unitary `V`. These are the hypotheses of the characterization of the Haar frame
(`NLAlib/RandomMatrix/Haar/Uniqueness.lean`) and of the oblivious-embedding arguments for Gaussian
and Haar sketches. The standard Gaussian matrix is invariant on both sides.

Consequences proved here from invariance alone: a left invariant random matrix has mean zero, and
`E [X B Xᴴ]` is a multiple of the identity, `(E tr (X B Xᴴ) / n) • 1`.

The classes are stated with `HasOrthonormalCols`, not with Mathlib's `SMulInvariantMeasure` of
`Matrix.unitaryGroup` (which would need a global action on rectangular matrices):
`docs/design/Mathlib-deviations.md` entry 14. The bridge to the bundled group is
`isLeftUnitarilyInvariant_iff`.

## Main results

* `NLAlib.IsLeftUnitarilyInvariant`, `NLAlib.IsRightUnitarilyInvariant`, with the bridges
  `NLAlib.isLeftUnitarilyInvariant_iff`, `NLAlib.isRightUnitarilyInvariant_iff`.
* `NLAlib.hasLaw_const_mul_of_isLeftUnitarilyInvariant`,
  `NLAlib.hasLaw_mul_const_of_isRightUnitarilyInvariant`: the `HasLaw` form consumers use.
* `NLAlib.isLeftUnitarilyInvariant_gaussianMatrix`,
  `NLAlib.isRightUnitarilyInvariant_gaussianMatrix`.
* `NLAlib.integral_eq_zero_of_isLeftUnitarilyInvariant`.
* `NLAlib.integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`: `E [X B Xᴴ]` is scalar.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n k : Type*} [Fintype n] [Fintype k]

/-! ### The interfaces -/

/-- A law on `n × k` matrices is **left unitarily invariant** when `U Q` has the law of `Q` for
every unitary (over `ℝ`, orthogonal) `U`. Mirrors Mathlib's `Measure.IsMulLeftInvariant`, with the
unitary given as a matrix with orthonormal columns (`docs/design/Mathlib-deviations.md` entry 14;
bridge `isLeftUnitarilyInvariant_iff`). Consumers use
`hasLaw_const_mul_of_isLeftUnitarilyInvariant`. -/
class IsLeftUnitarilyInvariant [DecidableEq n] (ν : Measure (Matrix n k 𝕜)) : Prop where
  /-- Left multiplication by a unitary preserves the law. -/
  map_mul_left_eq_self : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → ν.map (U * ·) = ν

/-- A law on `n × k` matrices is **right unitarily invariant** when `Q V` has the law of `Q` for
every unitary (over `ℝ`, orthogonal) `V`. Mirrors Mathlib's `Measure.IsMulRightInvariant`
(`docs/design/Mathlib-deviations.md` entry 14; bridge `isRightUnitarilyInvariant_iff`). Consumers
use `hasLaw_mul_const_of_isRightUnitarilyInvariant`. -/
class IsRightUnitarilyInvariant [DecidableEq k] (ν : Measure (Matrix n k 𝕜)) : Prop where
  /-- Right multiplication by a unitary preserves the law. -/
  map_mul_right_eq_self : ∀ V : Matrix k k 𝕜, HasOrthonormalCols V → ν.map (· * V) = ν

omit [Fintype k] in
/-- **Bridge to Mathlib's unitary group**: left unitary invariance is invariance under left
multiplication by every element of `Matrix.unitaryGroup n 𝕜`. -/
theorem isLeftUnitarilyInvariant_iff [DecidableEq n] {ν : Measure (Matrix n k 𝕜)} :
    IsLeftUnitarilyInvariant ν ↔
      ∀ U : Matrix.unitaryGroup n 𝕜, ν.map ((U : Matrix n n 𝕜) * ·) = ν := by
  -- Proof: `hasOrthonormalCols_iff_mem_unitaryGroup`.
  sorry

omit [Fintype n] in
/-- **Bridge to Mathlib's unitary group**: right unitary invariance is invariance under right
multiplication by every element of `Matrix.unitaryGroup k 𝕜`. -/
theorem isRightUnitarilyInvariant_iff [DecidableEq k] {ν : Measure (Matrix n k 𝕜)} :
    IsRightUnitarilyInvariant ν ↔
      ∀ V : Matrix.unitaryGroup k 𝕜, ν.map (· * (V : Matrix k k 𝕜)) = ν := by
  sorry

omit [Fintype k] in
/-- A random matrix whose law is left unitarily invariant keeps its law under left multiplication
by a fixed unitary. -/
theorem hasLaw_const_mul_of_isLeftUnitarilyInvariant [DecidableEq n] {ν : Measure (Matrix n k 𝕜)}
    [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ) {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) : HasLaw (fun ω => U * X ω) ν μ := by
  sorry

omit [Fintype n] in
/-- A random matrix whose law is right unitarily invariant keeps its law under right
multiplication by a fixed unitary. -/
theorem hasLaw_mul_const_of_isRightUnitarilyInvariant [DecidableEq k] {ν : Measure (Matrix n k 𝕜)}
    [IsRightUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ) {V : Matrix k k 𝕜}
    (hV : HasOrthonormalCols V) : HasLaw (fun ω => X ω * V) ν μ := by
  sorry

/-! ### Gaussian matrices -/

/-- The standard Gaussian matrix is left orthogonally invariant. -/
instance isLeftUnitarilyInvariant_gaussianMatrix [DecidableEq n] :
    IsLeftUnitarilyInvariant (gaussianMatrix n k) := by
  -- Proof: `hasLaw_const_mul_of_hasLaw_gaussianMatrix` at `HasLaw.id`, with
  -- `HasOrthonormalCols.conjTranspose_of_card_eq`.
  sorry

/-- The standard Gaussian matrix is right orthogonally invariant. -/
instance isRightUnitarilyInvariant_gaussianMatrix [DecidableEq k] :
    IsRightUnitarilyInvariant (gaussianMatrix n k) := by
  sorry

/-! ### Moments from invariance -/

/-- **A left unitarily invariant random matrix has mean zero** (take `U = -1`). No integrability
is needed: `∫ (-X) = -∫ X` holds for the Bochner integral in every case. -/
theorem integral_eq_zero_of_isLeftUnitarilyInvariant [DecidableEq n] [DecidableEq k]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) : ∫ ω, X ω ∂μ = 0 := by
  sorry

/-- **`E [X B Xᴴ]` is scalar** for a left unitarily invariant `X`: it commutes with every unitary,
so it is `(E tr (X B Xᴴ) / n) • 1`. The integrability hypothesis is needed: without it the left
side is `0` while the trace may still be integrable. Applied to the Gaussian it gives
`E [G B Gᴴ] = tr B • 1`; to the Haar frame, its second moments. [Meckes2019, Ch. 2] for Haar
measure on the orthogonal group; here any left invariant law, over any `RCLike` field. -/
theorem integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant [DecidableEq n]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) (B : Matrix k k 𝕜) (hint : Integrable (fun ω => X ω * B * (X ω)ᴴ) μ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ =
      ((∫ ω, (X ω * B * (X ω)ᴴ).trace ∂μ) / Fintype.card n) • (1 : Matrix n n 𝕜) := by
  -- Proof: `Matrix.integral_const_mul`, `Matrix.integral_mul_const` and the law of `U X` give
  -- `U E Uᴴ = E`; then `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` and
  -- `Matrix.integral_trace`.
  sorry

end NLAlib
