/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Uniqueness of the Haar frame

**Characterization**: a random matrix with almost surely orthonormal columns whose law is left
orthogonally invariant is a Haar frame. Consequences: the Gram–Schmidt factor of a tall Gaussian
matrix is a Haar frame (the QR construction), `Q V` is a Haar frame for a Haar frame `Q` and a
fixed frame `V` (so any set of columns of a Haar frame is one), each column of a Haar frame is
uniform on the sphere, and the square Haar frame is Mathlib's Haar measure on the orthogonal group.

The argument compares an invariant law `ν` with `haarFrame n n` itself, by Tonelli, so it needs
neither the uniqueness of Haar measure nor the compactness of the orthogonal group; the
compactness (`compactSpace_unitaryGroup`) is used only to state the bridge to Mathlib's
`haarMeasure` (`docs/design/Mathlib-deviations.md` entry 15).

## Main results

* `NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`: the characterization.
* `NLAlib.hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix`: the QR construction.
* `NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`: sub-frames.
* `NLAlib.hasLaw_col_of_hasLaw_haarFrame`: a column is uniform on the sphere.
* `NLAlib.compactSpace_unitaryGroup`, `NLAlib.haarFrame_eq_map_haarMeasure`: the square case is
  Haar measure on `Matrix.orthogonalGroup n ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k q : Type*} [Fintype n]
  [Fintype k] [Fintype q] {X : Ω → Matrix n k ℝ}

/-! ### The characterization -/

/-- **Characterization of the Haar frame**: a random matrix with almost surely orthonormal
columns whose law is a left unitarily invariant probability measure is a Haar frame. No
`card k ≤ card n` is needed: without it there are no frames, and `hQ` cannot hold for a
probability law. [Meckes2019, Ch. 1], as uniqueness of the invariant measure on the Stiefel
manifold; here proved against `haarFrame n n` directly. Replaces the prototype's
`measure_eq_haarFrameLaw_of_invariant`.
Result: haar-frame-uniqueness -/
theorem hasLaw_haarFrame_of_isLeftUnitarilyInvariant [DecidableEq n] [DecidableEq k]
    {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    (hX : HasLaw X ν μ) (hQ : ∀ᵐ ω ∂μ, HasOrthonormalCols (X ω)) : HasLaw X (haarFrame n k) μ := by
  -- Proof (about 150 lines): `μ` is a probability by `hX.isProbabilityMeasure`. For a frame `x`
  -- the law `η_x` of `U x`, `U ~ haarFrame n n`, does not depend on `x`
  -- (`HasOrthonormalCols.exists_mul_eq` and right invariance of `haarFrame n n`); then
  -- `ν s = ∫ U, ν ((U * ·)⁻¹' s) = ∫ x, η_x s ∂ν = η s` by `lintegral_lintegral_swap`, and
  -- `haarFrame n k` is one such `ν`.
  sorry

/-! ### Consequences -/

/-- **The QR construction of the Haar frame**: the Gram–Schmidt factor of a tall standard
Gaussian matrix is a Haar frame. [Meckes2019, Ch. 1], there for square matrices; here any tall
shape. Replaces the prototype's `gaussianMatrix_map_canonicalQRFrame`.
Result: haar-frame-gram-schmidt -/
theorem hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix [LinearOrder k] [LocallyFiniteOrderBot k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    HasLaw (fun ω => gramSchmidtQ (G ω)) (haarFrame n k) μ := by
  -- Proof: the characterization, with `gramSchmidtQ_mul_left`, the a.s. full rank
  -- (`ae_rank_eq_min_of_hasLaw_gaussianMatrix`) and `measurable_gramSchmidtQ`.
  sorry

/-- **Sub-frames of a Haar frame**: `Q V` is a Haar frame for a Haar frame `Q` and a fixed `V`
with orthonormal columns; with `V = selectionMatrix s` for an injective `s`, any set of columns.
Square `V` is right invariance (`isRightUnitarilyInvariant_haarFrame`). -/
theorem hasLaw_mul_const_of_hasLaw_haarFrame [DecidableEq k] [DecidableEq q]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) {V : Matrix k q ℝ}
    (hV : HasOrthonormalCols V) : HasLaw (fun ω => X ω * V) (haarFrame n q) μ := by
  -- Proof: `X V` is a.s. a frame with a left invariant law; the characterization.
  sorry

/-- **A column of a Haar frame is uniform on the sphere**: it has law `uniformSphereVector n`,
that of `g / ‖g‖` for a standard Gaussian `g`. [Meckes2019, Ch. 1]. -/
theorem hasLaw_col_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    HasLaw (fun ω i => X ω i j) (uniformSphereVector n) μ := by
  -- Proof: `hasLaw_mul_const_of_hasLaw_haarFrame` with `V = replicateCol Unit (Pi.single j 1)`,
  -- then `hasLaw_col_unit_of_hasLaw_haarFrame`.
  sorry

/-! ### Haar measure on the orthogonal group -/

/-- The unitary group `Matrix.unitaryGroup n 𝕜` (over `ℝ`, the orthogonal group) is compact, in
every dimension including `0`. An upstream candidate (it uses no NLAlib vocabulary), to move to
`NLAlib/ForMathlib` at the wrap-up. Port of the prototype's `orthogonalGroupCompactSpace`, there
for `Fin n` over `ℝ`. -/
instance compactSpace_unitaryGroup {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n] :
    CompactSpace (Matrix.unitaryGroup n 𝕜) := by
  -- Proof: `isCompact_setOf_hasOrthonormalCols` and `hasOrthonormalCols_iff_mem_unitaryGroup`.
  sorry

/-- **The square Haar frame is Haar measure on the orthogonal group**: `haarFrame n n` is the
image under the coercion of Mathlib's Haar measure on `Matrix.orthogonalGroup n ℝ`, normalised to
mass one. The bridge of `docs/design/Mathlib-deviations.md` entry 15. [Meckes2019, Ch. 1]. -/
theorem haarFrame_eq_map_haarMeasure [DecidableEq n] :
    haarFrame n n =
      (Measure.haarMeasure ⊤ : Measure (Matrix.orthogonalGroup n ℝ)).map Subtype.val := by
  -- Proof: the image measure is a probability, concentrated on frames and left invariant
  -- (`MeasureTheory.Measure.IsMulLeftInvariant`); the characterization at `X = id`.
  sorry

end NLAlib
