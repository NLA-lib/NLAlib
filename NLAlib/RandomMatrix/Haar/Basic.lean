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
instance isProbabilityMeasure_haarFrame [DecidableEq k] : IsProbabilityMeasure (haarFrame n k) :=
  Measure.isProbabilityMeasure_map measurable_polarFactor.aemeasurable

/-- **The polar factor of a Gaussian matrix is a Haar frame**: the definition of `haarFrame` in
`HasLaw` form. -/
theorem hasLaw_polarFactor_of_hasLaw_gaussianMatrix [DecidableEq k] {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) :
    HasLaw (fun ω => polarFactor (G ω)) (haarFrame n k) μ :=
  HasLaw.fun_comp (Y := polarFactor) ⟨measurable_polarFactor.aemeasurable, rfl⟩
    hG

/-- A function of a Haar frame has the law of that function of the polar factor of a Gaussian. -/
private theorem hasLaw_of_hasLaw_comp_polarFactor [DecidableEq k] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} {f : Matrix n k ℝ → β} (hf : Measurable f)
    (h : HasLaw (fun G => f (polarFactor G)) ν (gaussianMatrix n k)) :
    HasLaw f ν (haarFrame n k) :=
  ⟨hf.aemeasurable, by rw [haarFrame, Measure.map_map hf measurable_polarFactor]; exact h.map_eq⟩

/-- An almost sure property of the polar factor of a Gaussian holds almost surely for a Haar
frame. -/
private theorem ae_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    {p : Matrix n k ℝ → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ G ∂gaussianMatrix n k, p (polarFactor G)) : ∀ᵐ ω ∂μ, p (X ω) := by
  refine ae_of_ae_map hX.aemeasurable ?_
  rw [hX.map_eq]
  exact (ae_map_iff measurable_polarFactor.aemeasurable hp).2 h

/-! ### Frames -/

/-- **A Haar frame has orthonormal columns** almost surely, when it is no wider than tall. -/
theorem ae_hasOrthonormalCols_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (X ω) := by
  refine ae_of_hasLaw_haarFrame hX isClosed_setOf_hasOrthonormalCols.measurableSet ?_
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix n k))]
    with G hG
  rw [hasOrthonormalCols_polarFactor_iff, mulVec_injective_iff_rank_eq]
  rw [show (id G).rank = G.rank from rfl] at hG
  rw [hG, min_eq_right hk]

/-- **The conjugate transpose of a Haar frame** is a Haar frame of the transposed shape. Every
shape; for `card n ≤ card k` it says that `X` has orthonormal rows almost surely. -/
theorem hasLaw_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) : HasLaw (fun ω => (X ω)ᴴ) (haarFrame k n) μ := by
  refine HasLaw.fun_comp (Y := Matrix.conjTranspose)
    (hasLaw_of_hasLaw_comp_polarFactor continuous_id.matrix_conjTranspose.measurable ?_) hX
  exact (hasLaw_polarFactor_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix HasLaw.id)).congr
    (ae_of_all _ fun G => (polarFactor_conjTranspose G).symm)

/-- A Haar frame has spectral norm at most one almost surely, in every shape. -/
theorem ae_specNorm_le_one_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ) :
    ∀ᵐ ω ∂μ, specNorm (X ω) ≤ 1 :=
  ae_of_hasLaw_haarFrame hX (measurableSet_le measurable_specNorm measurable_const)
    (ae_of_all _ specNorm_polarFactor_le_one)

/-- The entries of a Haar frame have moments of every order (they are bounded by `1`). -/
theorem memLp_apply_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ) (i : n)
    (j : k) (p : ℝ≥0∞) : MemLp (fun ω => X ω i j) p μ := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hm : Measurable fun x : Matrix n k ℝ => x i j := Matrix.measurable_apply i j
  refine MemLp.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable 1 ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  exact (norm_apply_le_specNorm (X ω) i j).trans hω

/-! ### Invariance -/

/-- **A Haar frame is left orthogonally invariant**: `U Q` is a Haar frame for every orthogonal
`U`. Every shape. [Meckes2019, Ch. 1]. Replaces the prototype's `haarFrameLaw_map_smul`.
Result: haar-frame-invariance -/
instance isLeftUnitarilyInvariant_haarFrame [DecidableEq n] [DecidableEq k] :
    IsLeftUnitarilyInvariant (haarFrame n k) := by
  refine ⟨fun U hU => (hasLaw_of_hasLaw_comp_polarFactor
    (measurable_const.matrix_mul measurable_id) ?_).map_eq⟩
  exact (hasLaw_polarFactor_of_hasLaw_gaussianMatrix
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id hU.conjTranspose)).congr
    (ae_of_all _ fun G => (polarFactor_mul_left hU G).symm)

/-- **A Haar frame is right orthogonally invariant**: `Q V` is a Haar frame for every orthogonal
`V`. Every shape. [Meckes2019, Ch. 1].
Result: haar-frame-invariance -/
instance isRightUnitarilyInvariant_haarFrame [DecidableEq k] :
    IsRightUnitarilyInvariant (haarFrame n k) := by
  refine ⟨fun V hV => (hasLaw_of_hasLaw_comp_polarFactor
    (measurable_id.matrix_mul measurable_const) ?_).map_eq⟩
  exact (hasLaw_polarFactor_of_hasLaw_gaussianMatrix
    (hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV)).congr
    (ae_of_all _ fun G => (polarFactor_mul_right hV.conjTranspose G).symm)

/-! ### The uniform law on the sphere -/

/-- The **uniform law on the unit sphere** of `ℝⁿ`: the law of `g / ‖g‖` for a standard Gaussian
vector `g`, the Euclidean norm being `‖WithLp.toLp 2 g‖`. It is the law of a column of a Haar
frame (`hasLaw_col_of_hasLaw_haarFrame`). For nonempty `n` it is concentrated on the sphere; for
empty `n` it is the point mass at the unique vector. -/
noncomputable def uniformSphereVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  (gaussianVector n).map fun g => ‖WithLp.toLp 2 g‖⁻¹ • g

/-- Normalisation of a vector is measurable. -/
private theorem measurable_inv_norm_smul :
    Measurable fun g : n → ℝ => ‖WithLp.toLp 2 g‖⁻¹ • g :=
  ((PiLp.continuous_toLp 2 _).measurable.norm.inv).smul measurable_id

/-- The uniform law on the sphere is a probability measure. -/
instance isProbabilityMeasure_uniformSphereVector :
    IsProbabilityMeasure (uniformSphereVector n) :=
  Measure.isProbabilityMeasure_map measurable_inv_norm_smul.aemeasurable

/-- **A normalised Gaussian vector is uniform on the sphere**: the definition of
`uniformSphereVector` in `HasLaw` form. -/
theorem hasLaw_inv_norm_smul_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (g ω)‖⁻¹ • g ω) (uniformSphereVector n) μ :=
  HasLaw.fun_comp (Y := fun g : n → ℝ => ‖WithLp.toLp 2 g‖⁻¹ • g)
    ⟨measurable_inv_norm_smul.aemeasurable, rfl⟩ hg

/-- **A one-column Haar frame is uniform on the sphere**: the column of a Haar frame `n × 1` has
law `uniformSphereVector n`. No hypothesis on `n`. The general column is
`hasLaw_col_of_hasLaw_haarFrame`. -/
theorem hasLaw_col_unit_of_hasLaw_haarFrame {X : Ω → Matrix n Unit ℝ}
    (hX : HasLaw X (haarFrame n Unit) μ) :
    HasLaw (fun ω i => X ω i ()) (uniformSphereVector n) μ := by
  refine HasLaw.fun_comp (Y := fun (x : Matrix n Unit ℝ) i => x i ())
    (hasLaw_of_hasLaw_comp_polarFactor (measurable_pi_lambda _ fun i =>
      (measurable_pi_apply ()).comp (measurable_pi_apply i)) ?_) hX
  have h (G : Matrix n Unit ℝ) : G = Matrix.replicateCol Unit fun i => G i () := by
    ext i j
    rfl
  refine (hasLaw_inv_norm_smul_of_hasLaw_gaussianVector
    (hasLaw_col_of_hasLaw_gaussianMatrix HasLaw.id ())).congr (ae_of_all _ fun G => ?_)
  change (fun i => polarFactor G i ()) = _
  rw [h G, polarFactor_replicateCol]
  rfl

end NLAlib
