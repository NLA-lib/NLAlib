/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import NLAlib.ForMathlib.LinearAlgebra.UnitaryGroup
public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Uniqueness of the Haar frame

**Characterization**: a random matrix with almost surely orthonormal columns whose law is left
orthogonally invariant is a Haar frame. Consequences: the Gram–Schmidt factor of a tall Gaussian
matrix is a Haar frame (the QR construction), `Q V` is a Haar frame for a Haar frame `Q` and a
fixed frame `V` (so any set of columns of a Haar frame is one), each column of a Haar frame is
uniform on the sphere, and the square Haar frame is Mathlib's Haar measure on the orthogonal group.
Comparing with the image of Mathlib's surface measure `Measure.toSphere` the same way identifies
`uniformSphereVector n` with normalised surface measure (`docs/design/Mathlib-deviations.md`
entry 16).

The argument compares an invariant law `ν` with `haarFrame n n` itself, by Tonelli, so it needs
neither the uniqueness of Haar measure nor the compactness of the orthogonal group; the
compactness (`Matrix.compactSpace_unitaryGroup`) is used only to state the bridge to Mathlib's
`haarMeasure` (`docs/design/Mathlib-deviations.md` entry 15).

## Main results

* `NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`: the characterization.
* `NLAlib.hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix`: the QR construction.
* `NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`: sub-frames.
* `NLAlib.hasLaw_col_of_hasLaw_haarFrame`: a column is uniform on the sphere.
* `NLAlib.uniformSphereVector_eq_map_toSphere`: the uniform law on the sphere is Mathlib's
  normalised surface measure `Measure.toSphere`.
* `NLAlib.haarFrame_eq_map_haarMeasure`: the square case is Haar measure on
  `Matrix.orthogonalGroup n ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Pointwise

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k q : Type*} [Fintype n]
  [Fintype k] [Fintype q] {X : Ω → Matrix n k ℝ}

/-! ### The characterization -/

omit [Fintype k] in
/-- The law of `U x` for a square Haar frame `U` does not depend on the frame `x`. -/
private theorem map_mul_eq_of_hasOrthonormalCols [Finite k] [DecidableEq n] [DecidableEq k]
    {x y : Matrix n k ℝ} (hx : HasOrthonormalCols x) (hy : HasOrthonormalCols y) :
    (haarFrame n n).map (· * y) = (haarFrame n n).map (· * x) := by
  obtain ⟨V, hV, rfl⟩ := hx.exists_mul_eq hy
  have h : (fun U : Matrix n n ℝ => U * (V * x)) = (· * x) ∘ (· * V) := by
    funext U
    simp only [Function.comp_apply, Matrix.mul_assoc]
  have hm (c : Matrix n n ℝ) : Measurable fun U : Matrix n n ℝ => U * c :=
    measurable_id.matrix_mul measurable_const
  have hx' : Measurable fun U : Matrix n n ℝ => U * x := measurable_id.matrix_mul measurable_const
  rw [h, ← Measure.map_map hx' (hm V),
    IsRightUnitarilyInvariant.map_mul_right_eq_self V hV]

omit [Fintype k] in
/-- **Averaging over the orthogonal group**: a left unitarily invariant probability law `ν` is the
`ν`-average of the laws of `U x`, `U` a square Haar frame. -/
private theorem apply_eq_lintegral_map_mul [DecidableEq n]
    (ν : Measure (Matrix n k ℝ)) [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    {s : Set (Matrix n k ℝ)} (hs : MeasurableSet s) :
    ν s = ∫⁻ x, (haarFrame n n).map (· * x) s ∂ν := by
  have hU : ∀ᵐ U ∂haarFrame n n, HasOrthonormalCols U :=
    ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl
  have hf : Measurable (s.indicator (1 : Matrix n k ℝ → ℝ≥0∞)) := measurable_one.indicator hs
  have hF : Measurable (Function.uncurry fun (U : Matrix n n ℝ) (x : Matrix n k ℝ) =>
      s.indicator 1 (U * x)) :=
    hf.comp (measurable_fst.matrix_mul measurable_snd)
  have hinner : ∀ᵐ U ∂haarFrame n n, ∫⁻ x, s.indicator 1 (U * x) ∂ν = ν s := by
    filter_upwards [hU] with U hU
    have h := lintegral_map (μ := ν) hf
      (measurable_const.matrix_mul measurable_id : Measurable (U * · : Matrix n k ℝ → _))
    rw [IsLeftUnitarilyInvariant.map_mul_left_eq_self U hU, lintegral_indicator_one hs] at h
    exact h.symm
  have houter (x : Matrix n k ℝ) :
      ∫⁻ U, s.indicator 1 (U * x) ∂haarFrame n n = (haarFrame n n).map (· * x) s := by
    have h := lintegral_map (μ := haarFrame n n) hf
      (measurable_id.matrix_mul measurable_const : Measurable (· * x : Matrix n n ℝ → _))
    rw [lintegral_indicator_one hs] at h
    exact h.symm
  calc ν s = ∫⁻ U, ∫⁻ x, s.indicator 1 (U * x) ∂ν ∂haarFrame n n := by
        rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, ∫⁻ U, s.indicator 1 (U * x) ∂haarFrame n n ∂ν :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by simp only [houter]

omit [Fintype k] in
/-- A left unitarily invariant probability law concentrated on frames is the law of `U x₀`, for
`U` a square Haar frame and `x₀` any fixed frame. -/
private theorem eq_map_mul_of_ae_hasOrthonormalCols [Finite k] [DecidableEq n] [DecidableEq k]
    (ν : Measure (Matrix n k ℝ)) [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    (hν : ∀ᵐ x ∂ν, HasOrthonormalCols x) {x₀ : Matrix n k ℝ} (hx₀ : HasOrthonormalCols x₀) :
    ν = (haarFrame n n).map (· * x₀) := by
  ext s hs
  rw [apply_eq_lintegral_map_mul ν hs, lintegral_congr_ae (hν.mono fun x hx =>
    congrArg (fun ρ : Measure (Matrix n k ℝ) => ρ s) (map_mul_eq_of_hasOrthonormalCols hx₀ hx)),
    lintegral_const, measure_univ, mul_one]

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
  have hν : ∀ᵐ x ∂ν, HasOrthonormalCols x := by
    rw [← hX.map_eq]
    exact (ae_map_iff hX.aemeasurable isClosed_setOf_hasOrthonormalCols.measurableSet).2 hQ
  obtain ⟨x₀, hx₀⟩ := hν.exists
  have h := (eq_map_mul_of_ae_hasOrthonormalCols ν hν hx₀).trans
    (eq_map_mul_of_ae_hasOrthonormalCols (haarFrame n k)
      (ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id hx₀.card_le) hx₀).symm
  exact h ▸ hX

/-! ### Consequences -/

omit [Fintype k] [Fintype q] in
/-- The image of a left unitarily invariant law under a map commuting with left multiplication by
unitaries is left unitarily invariant. -/
private theorem isLeftUnitarilyInvariant_map [DecidableEq n] {ρ : Measure (Matrix n k ℝ)}
    [IsLeftUnitarilyInvariant ρ] {f : Matrix n k ℝ → Matrix n q ℝ} (hf : Measurable f)
    (h : ∀ U : Matrix n n ℝ, HasOrthonormalCols U → ∀ x, f (U * x) = U * f x) :
    IsLeftUnitarilyInvariant (ρ.map f) := by
  refine ⟨fun U hU => ?_⟩
  have hc : (U * ·) ∘ f = f ∘ (U * ·) := funext fun x => (h U hU x).symm
  have h₁ : Measurable fun x : Matrix n q ℝ => U * x := measurable_const.matrix_mul measurable_id
  have h₂ : Measurable fun x : Matrix n k ℝ => U * x := measurable_const.matrix_mul measurable_id
  rw [Measure.map_map h₁ hf, hc, ← Measure.map_map hf h₂,
    IsLeftUnitarilyInvariant.map_mul_left_eq_self U hU]

/-- **The QR construction of the Haar frame**: the Gram–Schmidt factor of a tall standard
Gaussian matrix is a Haar frame. [Meckes2019, Ch. 1], there for square matrices; here any tall
shape. Replaces the prototype's `gaussianMatrix_map_canonicalQRFrame`.
Result: haar-frame-gram-schmidt -/
theorem hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix [LinearOrder k] [LocallyFiniteOrderBot k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    HasLaw (fun ω => gramSchmidtQ (G ω)) (haarFrame n k) μ := by
  classical
  have : IsProbabilityMeasure ((gaussianMatrix n k).map gramSchmidtQ) :=
    Measure.isProbabilityMeasure_map measurable_gramSchmidtQ.aemeasurable
  have : IsLeftUnitarilyInvariant ((gaussianMatrix n k).map gramSchmidtQ) :=
    isLeftUnitarilyInvariant_map measurable_gramSchmidtQ fun _ hU x => gramSchmidtQ_mul_left hU x
  refine hasLaw_haarFrame_of_isLeftUnitarilyInvariant
    (HasLaw.fun_comp (Y := gramSchmidtQ) ⟨measurable_gramSchmidtQ.aemeasurable, rfl⟩ hG) ?_
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hG] with ω hω
  rw [min_eq_right hk] at hω
  exact hasOrthonormalCols_gramSchmidtQ (mulVec_injective_iff_rank_eq.2 hω)

/-- **Sub-frames of a Haar frame**: `Q V` is a Haar frame for a Haar frame `Q` and a fixed `V`
with orthonormal columns; with `V = selectionMatrix s` for an injective `s`, any set of columns.
Square `V` is right invariance (`isRightUnitarilyInvariant_haarFrame`). -/
theorem hasLaw_mul_const_of_hasLaw_haarFrame [DecidableEq k] [DecidableEq q]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) {V : Matrix k q ℝ}
    (hV : HasOrthonormalCols V) : HasLaw (fun ω => X ω * V) (haarFrame n q) μ := by
  classical
  have hm : Measurable (· * V : Matrix n k ℝ → Matrix n q ℝ) :=
    measurable_id.matrix_mul measurable_const
  have : IsProbabilityMeasure ((haarFrame n k).map (· * V)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsLeftUnitarilyInvariant ((haarFrame n k).map (· * V)) :=
    isLeftUnitarilyInvariant_map hm fun _ _ x => Matrix.mul_assoc _ x V
  refine hasLaw_haarFrame_of_isLeftUnitarilyInvariant
    (HasLaw.fun_comp (Y := (· * V)) ⟨hm.aemeasurable, rfl⟩ hX) ?_
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hX hk] with ω hω
  exact hω.mul hV

/-- **A column of a Haar frame is uniform on the sphere**: it has law `uniformSphereVector n`,
that of `g / ‖g‖` for a standard Gaussian `g`. [Meckes2019, Ch. 1]. -/
theorem hasLaw_col_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    HasLaw (fun ω i => X ω i j) (uniformSphereVector n) μ := by
  set V : Matrix k Unit ℝ := Matrix.replicateCol Unit (Pi.single j 1)
  have hV : HasOrthonormalCols V := by
    rw [hasOrthonormalCols_iff]
    ext a b
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply,
      star_trivial, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.one_apply, Subsingleton.elim a b]
  refine (hasLaw_col_unit_of_hasLaw_haarFrame
    (hasLaw_mul_const_of_hasLaw_haarFrame hX hk hV)).congr (ae_of_all _ fun ω => ?_)
  funext i
  simp only [V, Matrix.mul_apply, Matrix.replicateCol_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ### The surface measure on the sphere -/

/-- Mathlib's surface measure on the unit sphere, as a measure on the ambient space: the mass of
`B` is `dim · vol ((0, 1) • (S ∩ B))`. -/
private theorem toSphere_map_val_apply {B : Set (EuclideanSpace ℝ n)} (hB : MeasurableSet B) :
    ((volume : Measure (EuclideanSpace ℝ n)).toSphere.map Subtype.val) B =
      Module.finrank ℝ (EuclideanSpace ℝ n) *
        volume (Set.Ioo (0 : ℝ) 1 • (Metric.sphere (0 : EuclideanSpace ℝ n) 1 ∩ B)) := by
  rw [Measure.map_apply measurable_subtype_coe hB,
    Measure.toSphere_apply' _ (measurable_subtype_coe hB), Subtype.image_preimage_coe]

/-- Mathlib's surface measure on the unit sphere is invariant under linear isometries. -/
private theorem map_toSphere_map_val (L : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n) :
    ((volume : Measure (EuclideanSpace ℝ n)).toSphere.map Subtype.val).map L =
      (volume : Measure (EuclideanSpace ℝ n)).toSphere.map Subtype.val := by
  ext B hB
  rw [Measure.map_apply L.continuous.measurable hB,
    toSphere_map_val_apply (L.continuous.measurable hB), toSphere_map_val_apply hB]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ L ⁻¹' B) =
      L ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ B)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul, Set.mem_inter_iff, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hyB⟩, rfl⟩
      exact ⟨r, hr, L y, ⟨by rw [L.norm_map, hy], hyB⟩, (L.map_smul r y).symm⟩
    · rintro ⟨r, hr, z, ⟨hz, hzB⟩, hx⟩
      refine ⟨r, hr, L.symm z, ⟨by rw [L.symm.norm_map, hz], by rwa [L.apply_symm_apply]⟩, ?_⟩
      rw [← L.symm.map_smul, hx, L.symm_apply_apply]
  rw [hset, ← L.coe_toMeasurableEquiv, L.measurePreserving.measure_preimage_equiv]

/-- A unit vector, as a column, has orthonormal columns. -/
private theorem hasOrthonormalCols_replicateCol {v : n → ℝ} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    HasOrthonormalCols (Matrix.replicateCol Unit v) := by
  have h := EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct v
  rw [hv, one_pow, RCLike.re_to_real, star_trivial] at h
  rw [hasOrthonormalCols_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply, star_trivial,
    Matrix.one_apply, Subsingleton.elim a b, if_true]
  exact h.symm

/-- **The uniform law on the sphere is normalised surface measure**: `uniformSphereVector n` is
Mathlib's `Measure.toSphere` of the volume on `EuclideanSpace ℝ n`, normalised to mass one and
pushed forward to `n → ℝ`. The bridge of `docs/design/Mathlib-deviations.md` entry 16. Needs
nonempty `n`: for empty `n` the sphere is empty, while `uniformSphereVector n` is a point mass. -/
theorem uniformSphereVector_eq_map_toSphere [Nonempty n] :
    uniformSphereVector n =
      (((volume : Measure (EuclideanSpace ℝ n)).toSphere Set.univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ n)).toSphere).map
        fun x : Metric.sphere (0 : EuclideanSpace ℝ n) 1 =>
          WithLp.ofLp (x : EuclideanSpace ℝ n) := by
  classical
  set σ := (volume : Measure (EuclideanSpace ℝ n)).toSphere
  set ρ : Measure (n → ℝ) := ((σ Set.univ)⁻¹ • σ).map
    fun x : Metric.sphere (0 : EuclideanSpace ℝ n) 1 => WithLp.ofLp (x : EuclideanSpace ℝ n)
  have hofLp : Measurable fun x : EuclideanSpace ℝ n => WithLp.ofLp x :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hρ : ρ = (σ Set.univ)⁻¹ • (σ.map Subtype.val).map WithLp.ofLp := by
    rw [Measure.map_map hofLp measurable_subtype_coe, ← Measure.map_smul]
    rfl
  have hcol : Measurable (Matrix.replicateCol Unit : (n → ℝ) → Matrix n Unit ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ => measurable_pi_apply i
  have : IsProbabilityMeasure ((σ Set.univ)⁻¹ • σ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel
      (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)) (measure_ne_top _ _)]
  have : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (hofLp.comp measurable_subtype_coe).aemeasurable
  have : IsProbabilityMeasure (ρ.map (Matrix.replicateCol Unit)) :=
    Measure.isProbabilityMeasure_map hcol.aemeasurable
  have : IsLeftUnitarilyInvariant (ρ.map (Matrix.replicateCol Unit)) := by
    refine ⟨fun U hU => ?_⟩
    let T : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ n :=
      { toLinearMap := Matrix.toEuclideanLin U
        norm_map' := fun x => hU.norm_toLp_mulVec x.ofLp }
    let L := T.toLinearIsometryEquiv rfl
    have hU' : Measurable fun x : Matrix n Unit ℝ => U * x :=
      measurable_const.matrix_mul measurable_id
    have hmv : Measurable fun v : n → ℝ => U *ᵥ v :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    have hc : (U * ·) ∘ Matrix.replicateCol Unit = Matrix.replicateCol Unit ∘ (U *ᵥ ·) :=
      funext fun v => (Matrix.replicateCol_mulVec U v).symm
    have hL : (U *ᵥ ·) ∘ WithLp.ofLp = WithLp.ofLp ∘ L := rfl
    rw [Measure.map_map hU' hcol, hc, ← Measure.map_map hcol hmv, hρ, Measure.map_smul,
      Measure.map_map hmv hofLp, hL, ← Measure.map_map hofLp L.continuous.measurable,
      map_toSphere_map_val]
  have hframe : ∀ᵐ x ∂ρ.map (Matrix.replicateCol Unit), HasOrthonormalCols x := by
    refine (ae_map_iff hcol.aemeasurable isClosed_setOf_hasOrthonormalCols.measurableSet).2 ?_
    refine (ae_map_iff (hofLp.comp measurable_subtype_coe).aemeasurable
      (hcol isClosed_setOf_hasOrthonormalCols.measurableSet)).2 (ae_of_all _ fun x => ?_)
    exact hasOrthonormalCols_replicateCol (mem_sphere_zero_iff_norm.mp x.2)
  have h := (hasLaw_haarFrame_of_isLeftUnitarilyInvariant HasLaw.id hframe).map_eq
  rw [Measure.map_id] at h
  have hm : Measurable fun (x : Matrix n Unit ℝ) (i : n) => x i () :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply ()).comp (measurable_pi_apply i)
  rw [← (hasLaw_col_unit_of_hasLaw_haarFrame (HasLaw.id (μ := haarFrame n Unit))).map_eq, ← h]
  change (ρ.map (Matrix.replicateCol Unit)).map (fun (x : Matrix n Unit ℝ) (i : n) => x i ()) = ρ
  rw [Measure.map_map hm hcol]
  exact Measure.map_id

/-! ### Haar measure on the orthogonal group -/

/-- **The square Haar frame is Haar measure on the orthogonal group**: `haarFrame n n` is the
image under the coercion of Mathlib's Haar measure on `Matrix.orthogonalGroup n ℝ`, normalised to
mass one. The bridge of `docs/design/Mathlib-deviations.md` entry 15. [Meckes2019, Ch. 1]. -/
theorem haarFrame_eq_map_haarMeasure [DecidableEq n] :
    haarFrame n n =
      (Measure.haarMeasure ⊤ : Measure (Matrix.orthogonalGroup n ℝ)).map Subtype.val := by
  set ρ : Measure (Matrix.orthogonalGroup n ℝ) := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure ρ := ⟨Measure.haarMeasure_self⟩
  have : IsProbabilityMeasure (ρ.map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have : IsLeftUnitarilyInvariant (ρ.map Subtype.val) := by
    refine ⟨fun U hU => ?_⟩
    set u : Matrix.orthogonalGroup n ℝ := ⟨U, hasOrthonormalCols_iff_mem_unitaryGroup.mp hU⟩
    have hc : (U * ·) ∘ Subtype.val = Subtype.val ∘ (u * ·) := rfl
    have h₁ : Measurable fun x : Matrix n n ℝ => U * x := measurable_const.matrix_mul measurable_id
    rw [Measure.map_map h₁ measurable_subtype_coe, hc,
      ← Measure.map_map measurable_subtype_coe (continuous_const_mul u).measurable,
      MeasureTheory.map_mul_left_eq_self]
  have hframe : ∀ᵐ x ∂ρ.map Subtype.val, HasOrthonormalCols x :=
    (ae_map_iff measurable_subtype_coe.aemeasurable
      isClosed_setOf_hasOrthonormalCols.measurableSet).2
      (ae_of_all _ fun u => hasOrthonormalCols_iff_mem_unitaryGroup.mpr u.2)
  have h := (hasLaw_haarFrame_of_isLeftUnitarilyInvariant HasLaw.id hframe).map_eq
  rw [Measure.map_id] at h
  exact h.symm

end NLAlib
