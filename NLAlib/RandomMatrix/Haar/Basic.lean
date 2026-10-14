/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.Frames
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.RandomMatrix.UnitaryInvariance

/-!
# Haar frames

The law `haarFrame n k` of an orthogonally invariant `n × k` random matrix with orthonormal
columns (a Haar-distributed point of the Stiefel manifold), defined as the law of the polar factor
`G (Gᴴ G)^{-1/2}` of a standard Gaussian matrix `G`. For `card k ≤ card n` it is concentrated on
frames; it is invariant under orthogonal maps on both sides, and its conjugate transpose is a
Haar frame of the transposed shape. For `n × n` it is Haar measure on the orthogonal group
(`haarFrame_eq_map_haarMeasure`, in `NLAlib/RandomMatrix/Haar/Uniqueness.lean`).

The one-column case gives the uniform law on the unit sphere, `uniformSphereVector n`, the law of
`g / ‖g‖` for a standard Gaussian vector `g`.

Access is through the `HasLaw` bridges `hasLaw_polarFactor_of_hasLaw_gaussianMatrix` and
`hasLaw_inv_norm_smul_of_hasLaw_gaussianVector`, not by unfolding.

## Main results

* `NLAlib.haarFrame`, `NLAlib.hasLaw_polarFactor_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_hasOrthonormalCols_of_hasLaw_haarFrame`,
  `NLAlib.ae_specNorm_le_one_of_hasLaw_haarFrame`, `NLAlib.memLp_apply_of_hasLaw_haarFrame`.
* `NLAlib.hasLaw_conjTranspose_of_hasLaw_haarFrame`.
* `NLAlib.isLeftUnitarilyInvariant_haarFrame`, `NLAlib.isRightUnitarilyInvariant_haarFrame`.
* `NLAlib.uniformSphereVector`, `NLAlib.hasLaw_inv_norm_smul_of_hasLaw_gaussianVector`,
  `NLAlib.hasLaw_col_unit_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] {X : Ω → Matrix n k ℝ}

/-! ### The law -/

/-- The law of an `n × k` **Haar frame**: the polar factor `G (Gᴴ G)^{-1/2}` of a standard Gaussian
matrix `G`. For `card k ≤ card n` it is concentrated on matrices with orthonormal columns and
invariant under orthogonal maps on both sides. Junk value: for `card n < card k` it is the law of
`Pᴴ` for a `k × n` Haar frame `P` (orthonormal rows); every theorem using columns assumes
`card k ≤ card n`. [Meckes2019, Ch. 1], where it is constructed by Gram–Schmidt
(`hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix`); here any shape. Replaces the prototype's
`haarFrameLaw`, there a measure on the bundled Stiefel manifold for `k ≤ n`. -/
noncomputable def haarFrame (n k : Type*) [Fintype n] [Fintype k] [DecidableEq k] :
    Measure (Matrix n k ℝ) :=
  (gaussianMatrix n k).map polarFactor

/-- The Haar frame law is a probability measure. -/
instance isProbabilityMeasure_haarFrame [DecidableEq k] : IsProbabilityMeasure (haarFrame n k) := by
  sorry

/-- **The polar factor of a Gaussian matrix is a Haar frame**: the definition of `haarFrame` in
`HasLaw` form. -/
theorem hasLaw_polarFactor_of_hasLaw_gaussianMatrix [DecidableEq k] {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) :
    HasLaw (fun ω => polarFactor (G ω)) (haarFrame n k) μ := by
  -- Proof: `measurable_polarFactor` and `HasLaw.comp`.
  sorry

/-! ### Frames -/

/-- **A Haar frame has orthonormal columns** almost surely, when it is no wider than tall. -/
theorem ae_hasOrthonormalCols_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (X ω) := by
  -- Proof: `ae_rank_eq_min_of_hasLaw_gaussianMatrix`, `hasOrthonormalCols_polarFactor_iff`, and
  -- `HasLaw.ae_iff` through the closed set `isClosed_setOf_hasOrthonormalCols`.
  sorry

/-- **The conjugate transpose of a Haar frame** is a Haar frame of the transposed shape. Every
shape; for `card n ≤ card k` it says that `X` has orthonormal rows almost surely. -/
theorem hasLaw_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) : HasLaw (fun ω => (X ω)ᴴ) (haarFrame k n) μ := by
  -- Proof: `polarFactor_conjTranspose` and `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`.
  sorry

/-- A Haar frame has spectral norm at most one almost surely, in every shape. -/
theorem ae_specNorm_le_one_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ) :
    ∀ᵐ ω ∂μ, specNorm (X ω) ≤ 1 := by
  -- Proof: `specNorm_polarFactor_le_one`.
  sorry

/-- The entries of a Haar frame have moments of every order (they are bounded by `1`). -/
theorem memLp_apply_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ) (i : n)
    (j : k) (p : ℝ≥0∞) : MemLp (fun ω => X ω i j) p μ := by
  sorry

/-! ### Invariance -/

/-- **A Haar frame is left orthogonally invariant**: `U Q` is a Haar frame for every orthogonal
`U`. Every shape. [Meckes2019, Ch. 1]. Replaces the prototype's `haarFrameLaw_map_smul`.
Result: haar-frame-invariance -/
instance isLeftUnitarilyInvariant_haarFrame [DecidableEq n] [DecidableEq k] :
    IsLeftUnitarilyInvariant (haarFrame n k) := by
  -- Proof: `polarFactor_mul_left` and `hasLaw_const_mul_of_hasLaw_gaussianMatrix`.
  sorry

/-- **A Haar frame is right orthogonally invariant**: `Q V` is a Haar frame for every orthogonal
`V`. Every shape. [Meckes2019, Ch. 1].
Result: haar-frame-invariance -/
instance isRightUnitarilyInvariant_haarFrame [DecidableEq k] :
    IsRightUnitarilyInvariant (haarFrame n k) := by
  -- Proof: `polarFactor_mul_right` and `hasLaw_mul_const_of_hasLaw_gaussianMatrix`.
  sorry

/-! ### The uniform law on the sphere -/

/-- The **uniform law on the unit sphere** of `ℝⁿ`: the law of `g / ‖g‖` for a standard Gaussian
vector `g`, the Euclidean norm being `‖WithLp.toLp 2 g‖`. It is the law of a column of a Haar
frame (`hasLaw_col_of_hasLaw_haarFrame`). For nonempty `n` it is concentrated on the sphere; for
empty `n` it is the point mass at the unique vector. -/
noncomputable def uniformSphereVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  (gaussianVector n).map fun g => ‖WithLp.toLp 2 g‖⁻¹ • g

/-- The uniform law on the sphere is a probability measure. -/
instance isProbabilityMeasure_uniformSphereVector :
    IsProbabilityMeasure (uniformSphereVector n) := by
  sorry

/-- **A normalised Gaussian vector is uniform on the sphere**: the definition of
`uniformSphereVector` in `HasLaw` form. -/
theorem hasLaw_inv_norm_smul_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (g ω)‖⁻¹ • g ω) (uniformSphereVector n) μ := by
  sorry

/-- **A one-column Haar frame is uniform on the sphere**: the column of a Haar frame `n × 1` has
law `uniformSphereVector n`. No hypothesis on `n`. The general column is
`hasLaw_col_of_hasLaw_haarFrame`. -/
theorem hasLaw_col_unit_of_hasLaw_haarFrame {X : Ω → Matrix n Unit ℝ}
    (hX : HasLaw X (haarFrame n Unit) μ) :
    HasLaw (fun ω i => X ω i ()) (uniformSphereVector n) μ := by
  -- Proof: `polarFactor_replicateCol` and `hasLaw_col_of_hasLaw_gaussianMatrix`.
  sorry

end NLAlib
