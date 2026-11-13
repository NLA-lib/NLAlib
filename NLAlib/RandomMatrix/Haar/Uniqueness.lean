/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import NLAlib.ForMathlib.LinearAlgebra.UnitaryGroup
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Uniqueness of the Haar frame

**Characterization**: a random matrix with almost surely orthonormal columns whose law is left
orthogonally invariant is a Haar frame. Consequences: the Gram–Schmidt factor of a tall Gaussian
matrix is a Haar frame (the QR construction), $\mathbf{Q}\mathbf{V}$ is a Haar frame for a Haar
frame $\mathbf{Q}$ and a fixed frame $\mathbf{V}$ (so any set of columns of a Haar frame is one),
each column of a Haar frame is
uniform on the sphere, and the square Haar frame is Mathlib's Haar measure on the orthogonal group.
Comparing with the image of Mathlib's surface measure `Measure.toSphere` the same way identifies
`uniformSphereVector n` with normalised surface measure (`docs/design/Mathlib-deviations.md`
entry 16).

The argument compares an invariant law $\nu$ with `haarFrame n n` itself, by Tonelli, so it needs
neither the uniqueness of Haar measure nor the compactness of the orthogonal group; the
compactness (`Matrix.compactSpace_unitaryGroup`) is used only to state the bridge to Mathlib's
`haarMeasure` (`docs/design/Mathlib-deviations.md` entry 15).

## Main results

* `NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`: the characterization.
* `NLAlib.hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix`: the QR construction.
* `NLAlib.hasLaw_polarFactor_of_isLeftUnitarilyInvariant`: the polar factor of a full-rank
  rotation-invariant random matrix is a Haar frame.
* `NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`: sub-frames.
* `NLAlib.hasLaw_col_of_hasLaw_haarFrame`: a column is uniform on the sphere.
* `NLAlib.uniformSphereVector_eq_map_toSphere`: the uniform law on the sphere is Mathlib's
  normalised surface measure `Measure.toSphere`.
* `NLAlib.haarFrame_eq_map_haarMeasure`: the square case is Haar measure on
  `Matrix.orthogonalGroup n ℝ`.
* `NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`, and the
  compressed form `NLAlib.indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix`.
* `NLAlib.eq_map_polarFactor_mul_of_forall_map_mul_left_eq`: uniqueness of the Haar frame law in
  the range of a projector.
* `NLAlib.hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix`: Gaussianization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Pointwise

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k q : Type*} [Fintype n]
  [Fintype k] [Fintype q] {X : Ω → Matrix n k ℝ}

/-! ### The characterization -/

omit [Fintype k] in
/-- The law of $\mathbf{U}\mathbf{x}$ for a square Haar frame $\mathbf{U}$ does not depend on the
frame $\mathbf{x}$. -/
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
/-- **Averaging over the orthogonal group**: a left unitarily invariant probability law $\nu$ is
the $\nu$-average of the laws of $\mathbf{U}\mathbf{x}$, $\mathbf{U}$ a square Haar frame. -/
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
/-- A left unitarily invariant probability law concentrated on frames is the law of
$\mathbf{U}\mathbf{x}_0$, for $\mathbf{U}$ a square Haar frame and $\mathbf{x}_0$ any fixed
frame. -/
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
$\lvert k \rvert \le \lvert n \rvert$ is needed: without it there are no frames, and `hQ` cannot
hold for a
probability law. [Meckes2019, Ch. 1], as uniqueness of the invariant measure on the Stiefel
manifold; here proved against `haarFrame n n` directly.
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
Gaussian matrix ($\lvert k \rvert \le \lvert n \rvert$) is a Haar frame. [Meckes2019, Ch. 1],
there for square matrices; here any tall
shape.
Result: haar-frame-gram-schmidt -/
theorem hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix [LinearOrder k] [LocallyFiniteOrderBot k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    HasLaw (fun ω => gramSchmidtQ (G ω)) (haarFrame n k) μ := by
  classical
  have : IsProbabilityMeasure ((gaussianMatrix n k).map gramSchmidtQ) :=
    Measure.isProbabilityMeasure_map measurable_gramSchmidtQ.aemeasurable
  have : IsLeftUnitarilyInvariant ((gaussianMatrix n k).map gramSchmidtQ) :=
    isLeftUnitarilyInvariant_map measurable_gramSchmidtQ fun _ hU x =>
      HasOrthonormalCols.gramSchmidtQ_mul_left hU x
  refine hasLaw_haarFrame_of_isLeftUnitarilyInvariant
    (HasLaw.fun_comp (Y := gramSchmidtQ) ⟨measurable_gramSchmidtQ.aemeasurable, rfl⟩ hG) ?_
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hG] with ω hω
  rw [min_eq_right hk] at hω
  exact hasOrthonormalCols_gramSchmidtQ (mulVec_injective_iff_rank_eq.2 hω)

/-- **The polar factor of a full-rank rotation-invariant random matrix is Haar**: if the law
$\nu$ of $\mathbf{X}$ is a left unitarily invariant probability measure (over $\mathbb{R}$,
$\mathbf{U}\mathbf{X}$ has the law of $\mathbf{X}$ for every orthogonal $\mathbf{U}$) and
$\mathbf{X}$ has full column rank almost surely, then its polar factor
$\mathbf{X}(\mathbf{X}^{\mathsf{H}}\mathbf{X})^{-1/2}$ has the law `haarFrame n k`. The
hypothesis class is the full-rank rotation-invariant embedding of [EpperlyWebber2026, p. 2]; the
Gaussian (`isLeftUnitarilyInvariant_gaussianMatrix`, full rank a.s. for
$\lvert k \rvert \le \lvert n \rvert$) and the Haar frame are instances. A corollary of the
characterization `NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`, since
$\operatorname{polar}(\mathbf{U}\mathbf{X}) = \mathbf{U}\operatorname{polar}(\mathbf{X})$. -/
theorem hasLaw_polarFactor_of_isLeftUnitarilyInvariant [DecidableEq n] [DecidableEq k]
    {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => polarFactor (X ω)) (haarFrame n k) μ := by
  have hm : Measurable (polarFactor : Matrix n k ℝ → Matrix n k ℝ) := measurable_polarFactor
  have : IsProbabilityMeasure (ν.map polarFactor) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsLeftUnitarilyInvariant (ν.map polarFactor) :=
    isLeftUnitarilyInvariant_map hm fun _ hU x => HasOrthonormalCols.polarFactor_mul_left hU x
  refine hasLaw_haarFrame_of_isLeftUnitarilyInvariant
    (HasLaw.fun_comp (Y := polarFactor) ⟨hm.aemeasurable, rfl⟩ hX) ?_
  filter_upwards [hXr] with ω hω
  exact hasOrthonormalCols_polarFactor_iff.2 hω

/-- Sub-frames of a Haar frame: $\mathbf{Q}\mathbf{V}$ is a Haar frame for an $n \times k$
Haar frame $\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$, and a fixed $\mathbf{V}$ with
orthonormal columns; with $\mathbf{V}$ = `selectionMatrix s` for an injective $s$, any set of
columns. Square $\mathbf{V}$ is right invariance (`isRightUnitarilyInvariant_haarFrame`). -/
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

/-- **A column of a Haar frame is uniform on the sphere**: for an $n \times k$ Haar frame with
$\lvert k \rvert \le \lvert n \rvert$, each column has law `uniformSphereVector n`, that of
$\mathbf{g} / \|\mathbf{g}\|$ for a standard Gaussian $\mathbf{g}$. [Meckes2019, Ch. 1]. -/
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

/-- Mathlib's surface measure on the unit sphere $S$, as a measure on the ambient space: the mass
of $B$ is $\dim \cdot \operatorname{vol}\bigl((0, 1) \cdot (S \cap B)\bigr)$. -/
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

/-- The uniform law on the sphere is normalised surface measure: `uniformSphereVector n` is
Mathlib's `Measure.toSphere` of the volume on `EuclideanSpace ℝ n`, normalised to mass one and
pushed forward to `n → ℝ`. The bridge of `docs/design/Mathlib-deviations.md` entry 16. Needs
nonempty $n$: for empty $n$ the sphere is empty, while `uniformSphereVector n` is a point mass. -/
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

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k]

/-- Rotating a standard Gaussian matrix on the left by an independent random orthogonal matrix
keeps the joint law of the polar factor and the Gram matrix of the rotated matrix. -/
private theorem map_mul_polarFactor_prodMk_conjTranspose_mul_self [DecidableEq n] [DecidableEq k]
    (ρ : Measure (Matrix n n ℝ)) {R : Matrix n n ℝ → Matrix n n ℝ}
    (hRm : Measurable R) (hRo : ∀ U, HasOrthonormalCols (R U)) :
    (ρ.prod (gaussianMatrix n k)).map (fun p => (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) =
      (ρ.prod (gaussianMatrix n k)).map (fun p => (polarFactor p.2, p.2ᴴ * p.2)) := by
  have hΦ : Measurable fun x : Matrix n k ℝ => (polarFactor x, xᴴ * x) :=
    measurable_polarFactor.prodMk (by fun_prop)
  have hF1 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ => (polarFactor p.2, p.2ᴴ * p.2) :=
    hΦ.comp measurable_snd
  have hF2 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ =>
      (R p.1 * polarFactor p.2, p.2ᴴ * p.2) :=
    ((hRm.comp measurable_fst).matrix_mul (measurable_polarFactor.comp measurable_snd)).prodMk
      ((by fun_prop : Measurable fun x : Matrix n k ℝ => xᴴ * x).comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hF1 hs, Measure.map_apply hF2 hs, Measure.prod_apply (hF1 hs),
    Measure.prod_apply (hF2 hs)]
  refine lintegral_congr fun U => ?_
  have hm : Measurable (R U * · : Matrix n k ℝ → Matrix n k ℝ) :=
    measurable_const.matrix_mul measurable_id
  have heq : Prod.mk U ⁻¹' ((fun p : Matrix n n ℝ × Matrix n k ℝ =>
      (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) ⁻¹' s) =
      (R U * ·) ⁻¹' ((fun x : Matrix n k ℝ => (polarFactor x, xᴴ * x)) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, (hRo U).polarFactor_mul_left, (hRo U).conjTranspose_mul_mul]
  rw [heq, ← Measure.map_apply hm (hΦ hs),
    IsLeftUnitarilyInvariant.map_mul_left_eq_self _ (hRo U)]
  rfl

/-- The joint law of the polar factor and the Gram matrix of a tall standard Gaussian matrix is
the product of the Haar frame law and the law of the Gram matrix. -/
private theorem map_polarFactor_prodMk_conjTranspose_mul_self [DecidableEq k]
    (hk : Fintype.card k ≤ Fintype.card n) :
    (gaussianMatrix n k).map (fun x => (polarFactor x, xᴴ * x)) =
      (haarFrame n k).prod ((gaussianMatrix n k).map fun x => xᴴ * x) := by
  classical
  set ν := gaussianMatrix n k
  set ρ := haarFrame n n
  set P := ρ.prod ν
  obtain ⟨x₀, hx₀⟩ := (ae_hasOrthonormalCols_of_hasLaw_haarFrame
    (HasLaw.id (μ := haarFrame n k)) hk).exists
  set R : Matrix n n ℝ → Matrix n n ℝ := fun U => if HasOrthonormalCols U then U else 1
  have hRm : Measurable R := Measurable.ite isClosed_setOf_hasOrthonormalCols.measurableSet
    measurable_id measurable_const
  have hRo (U : Matrix n n ℝ) : HasOrthonormalCols (R U) := by
    simp only [R]; split_ifs with h
    exacts [h, hasOrthonormalCols_one]
  set pol : Matrix n k ℝ → Matrix n k ℝ :=
    fun x => if HasOrthonormalCols (polarFactor x) then polarFactor x else x₀
  have hpolm : Measurable pol := Measurable.ite
    (measurable_polarFactor isClosed_setOf_hasOrthonormalCols.measurableSet)
    measurable_polarFactor measurable_const
  have hpolo (x : Matrix n k ℝ) : HasOrthonormalCols (pol x) := by
    simp only [pol]; split_ifs with h
    exacts [h, hx₀]
  have hgm : Measurable fun x : Matrix n k ℝ => xᴴ * x := by fun_prop
  have hPν : P.map Prod.snd = ν := by simp [P, Measure.map_snd_prod]
  have hR0 : ∀ᵐ U ∂ρ, R U = U := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame (HasLaw.id (μ := ρ)) le_rfl]
      with U hU
    exact if_pos hU
  -- (1) rotating the Gaussian by an independent Haar matrix keeps its law
  have h1 := (map_mul_polarFactor_prodMk_conjTranspose_mul_self ρ (k := k) hRm hRo).symm
  -- (2) the polar factor is a frame almost surely
  have h2 : P.map (fun p => (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) =
      P.map (fun p => (R p.1 * pol p.2, p.2ᴴ * p.2)) := by
    have hν : ∀ᵐ x ∂ν, HasOrthonormalCols (polarFactor x) :=
      ae_hasOrthonormalCols_of_hasLaw_haarFrame
        (hasLaw_polarFactor_of_hasLaw_gaussianMatrix HasLaw.id) hk
    refine Measure.map_congr ?_
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable (hPν ▸ hν)] with p hp
    simp only [pol, if_pos hp]
  -- (3) a Haar matrix times any fixed frame is a Haar frame
  have hρ (y : Matrix n k ℝ) (hy : HasOrthonormalCols y) :
      ρ.map (fun U => R U * y) = haarFrame n k := by
    rw [Measure.map_congr (g := (· * y)) (hR0.mono fun U hU => by simp only [hU])]
    exact (hasLaw_mul_const_of_hasLaw_haarFrame (HasLaw.id (μ := ρ)) le_rfl hy).map_eq
  have h3 : P.map (fun p => (R p.1 * pol p.2, p.2ᴴ * p.2)) =
      (haarFrame n k).prod (ν.map fun x => xᴴ * x) := by
    have hF3 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ => (R p.1 * pol p.2, p.2ᴴ * p.2) :=
      ((hRm.comp measurable_fst).matrix_mul (hpolm.comp measurable_snd)).prodMk
        (hgm.comp measurable_snd)
    ext s hs
    rw [Measure.map_apply hF3 hs, Measure.prod_apply_symm (hF3 hs), Measure.prod_apply_symm hs,
      lintegral_map (measurable_measure_prodMk_right hs) hgm]
    refine lintegral_congr fun x => ?_
    rw [← hρ (pol x) (hpolo x),
      Measure.map_apply (hRm.matrix_mul measurable_const) (measurable_prodMk_right hs)]
    rfl
  refine Eq.trans ?_ (h1.trans (h2.trans h3))
  rw [← hPν, Measure.map_map (measurable_polarFactor.prodMk hgm) measurable_snd]
  rfl

/-- **Polar factor and Gram matrix of a Gaussian matrix are independent**: for a standard Gaussian
$\mathbf{G} \in \mathbb{R}^{n \times k}$, the polar factor
$\mathbf{G}(\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1/2}$, a Haar frame, is independent of
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ when $\lvert k \rvert \le \lvert n \rvert$. (For a wide
$\mathbf{G}$ it is not: the Gram matrix fixes the row space of the polar factor.)
[Notarnicola2023, Section 4.2, Lemmas 4.1--4.2, p. 1007]: independence is stated after
equation (4.5) at identity covariance, with the Gaussian matrix transposed relative to this
column-frame convention. Empty-dimensional cases are also included here. -/
theorem indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix
    [DecidableEq k] {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    IndepFun (fun ω => polarFactor (G ω)) (fun ω => (G ω)ᴴ * G ω) μ := by
  have := hG.isProbabilityMeasure
  have hgm : Measurable fun x : Matrix n k ℝ => xᴴ * x := by fun_prop
  refine (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_polarFactor.comp_aemeasurable hG.aemeasurable)
    (hgm.comp_aemeasurable hG.aemeasurable)).2 ?_
  have h := map_polarFactor_prodMk_conjTranspose_mul_self (n := n) (k := k) hk
  rw [← (hasLaw_polarFactor_of_hasLaw_gaussianMatrix hG).map_eq, ← hG.map_eq,
    AEMeasurable.map_map_of_aemeasurable (measurable_polarFactor.prodMk hgm).aemeasurable
      hG.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable hgm.aemeasurable hG.aemeasurable] at h
  exact h

/-- **Compressed form**: for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{n \times k}$ and an
orthogonal projector $\mathbf{P}$ of rank at least $\lvert k \rvert$, the polar factor of
$\mathbf{P}\mathbf{G}$ is independent of
$(\mathbf{P}\mathbf{G})^{\mathsf{H}}\mathbf{P}\mathbf{G}$. For $\mathbf{P} = \mathbf{I}$ this is
`NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`.
[Meckes2019, Ch. 1]; there for $\mathbf{P} = \mathbf{I}$. -/
theorem indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix [DecidableEq k]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) (hk : Fintype.card k ≤ P.rank) :
    IndepFun (fun ω => polarFactor (P * G ω)) (fun ω => (P * G ω)ᴴ * (P * G ω)) μ := by
  obtain ⟨E₀, hE₀, hP₀⟩ :=
    hP.exists_hasOrthonormalCols_mul_conjTranspose_eq (p := Fin P.rank) (Fintype.card_fin _)
  have hY := hasLaw_const_mul_of_hasLaw_gaussianMatrix hG
    (U := E₀ᴴ) (by rwa [Matrix.conjTranspose_conjTranspose])
  have hk' : Fintype.card k ≤ Fintype.card (Fin P.rank) := by simpa using hk
  have h := indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix hY hk'
  have horth : E₀ᴴ * E₀ = 1 := hE₀.conjTranspose_mul_self
  have hPG : ∀ ω, P * G ω = E₀ * (E₀ᴴ * G ω) := fun ω => by
    rw [← Matrix.mul_assoc, hP₀]
  have f1 : (fun ω => polarFactor (P * G ω)) =
      (fun A => E₀ * A) ∘ (fun ω => polarFactor (E₀ᴴ * G ω)) := by
    funext ω
    simp only [Function.comp_apply, hPG]
    exact hE₀.polarFactor_mul_left _
  have f2 : (fun ω => (P * G ω)ᴴ * (P * G ω)) = id ∘ (fun ω => (E₀ᴴ * G ω)ᴴ * (E₀ᴴ * G ω)) := by
    funext ω
    simp only [Function.comp_apply, id]
    rw [hPG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc E₀ᴴ E₀, horth,
      Matrix.one_mul]
  rw [f1, f2]
  exact h.comp (by fun_prop) measurable_id

/-- **The Haar frame law in a subspace is unique**: let $\mathbf{E}$ be an orthogonal projector
and $\nu$ a probability law on $n \times k$ frames (orthonormal columns) inside the range of
$\mathbf{E}$, invariant under left multiplication by every orthogonal $\mathbf{s}$ that fixes the
range of $\mathbf{I} - \mathbf{E}$ pointwise. Then $\nu$ is the law of
$\operatorname{polar}(\mathbf{E}\mathbf{Z})$ for a standard Gaussian $\mathbf{Z}$: the Haar frame
law of $\operatorname{range}\mathbf{E}$. (Such frames exist only if
$\lvert k \rvert \le \operatorname{rank}\mathbf{E}$.)
[Meckes2019, Ch. 1]; there for $\mathbf{E} = \mathbf{I}$
(`NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`). -/
theorem eq_map_polarFactor_mul_of_forall_map_mul_left_eq [DecidableEq n] [DecidableEq k]
    {E : Matrix n n ℝ} (hE : IsStarProjection E) {ν : Measure (Matrix n k ℝ)}
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, HasOrthonormalCols x ∧ E * x = x)
    (hinv : ∀ s : Matrix n n ℝ, HasOrthonormalCols s → s * (1 - E) = 1 - E →
      ν.map (s * ·) = ν) :
    ν = (gaussianMatrix n k).map fun Z => polarFactor (E * Z) := by
  obtain ⟨d, _, _, E₀, hE₀, hEE⟩ : ∃ (d : Type) (_ : Fintype d) (_ : DecidableEq d)
      (E₀ : Matrix n d ℝ), HasOrthonormalCols E₀ ∧ E₀ * E₀ᴴ = E :=
    ⟨Fin E.rank, inferInstance, inferInstance,
      hE.exists_hasOrthonormalCols_mul_conjTranspose_eq (Fintype.card_fin _)⟩
  have hm : Measurable (fun x : Matrix n k ℝ => E₀ᴴ * x) :=
    measurable_const.matrix_mul measurable_id
  have hm' : Measurable (fun y : Matrix d k ℝ => E₀ * y) :=
    measurable_const.matrix_mul measurable_id
  have hE0 : E₀ᴴ * (1 - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← hEE, ← Matrix.mul_assoc, hE₀.conjTranspose_mul_self,
      Matrix.one_mul, sub_self]
  have hpt : ∀ᵐ x ∂ν, E₀ * (E₀ᴴ * x) = x := hν.mono fun x hx => by
    rw [← Matrix.mul_assoc, hEE, hx.2]
  -- the pushforward of `ν` is a.s. orthonormal
  have hν'orth : ∀ᵐ x ∂(ν.map fun x => E₀ᴴ * x), HasOrthonormalCols x := by
    refine (ae_map_iff hm.aemeasurable isClosed_setOf_hasOrthonormalCols.measurableSet).2 ?_
    filter_upwards [hν] with x hx
    rw [hasOrthonormalCols_iff]
    calc (E₀ᴴ * x)ᴴ * (E₀ᴴ * x) = xᴴ * (E₀ * E₀ᴴ) * x := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = xᴴ * x := by rw [hEE, Matrix.mul_assoc, hx.2]
      _ = 1 := hasOrthonormalCols_iff.1 hx.1
  have : IsProbabilityMeasure (ν.map fun x => E₀ᴴ * x) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  -- the pushforward is left unitarily invariant
  have : IsLeftUnitarilyInvariant (ν.map fun x => E₀ᴴ * x) := by
    refine ⟨fun U hU => ?_⟩
    have hs := hE₀.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose hU
    have hsE : (1 + E₀ * (U - 1) * E₀ᴴ) * (1 - E) = 1 - E := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hE0, Matrix.mul_zero, add_zero]
    have hEs : E₀ᴴ * (1 + E₀ * (U - 1) * E₀ᴴ) = U * E₀ᴴ := by
      simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc,
        hE₀.conjTranspose_mul_cancel_left, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have hpt2 : ((fun x : Matrix d k ℝ => U * x) ∘ fun x : Matrix n k ℝ => E₀ᴴ * x) =
        fun x : Matrix n k ℝ => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x) := funext fun x => by
      simp only [Function.comp_apply]
      rw [← Matrix.mul_assoc U, ← hEs, Matrix.mul_assoc]
    have hsm : Measurable (fun x : Matrix n k ℝ => (1 + E₀ * (U - 1) * E₀ᴴ) * x) :=
      measurable_const.matrix_mul measurable_id
    have key : ν.map (fun x => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x)) = ν.map (fun x => E₀ᴴ * x) :=
      calc ν.map (fun x => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x))
          = (ν.map fun x => (1 + E₀ * (U - 1) * E₀ᴴ) * x).map fun x => E₀ᴴ * x :=
            (Measure.map_map hm hsm).symm
        _ = ν.map fun x => E₀ᴴ * x := by rw [hinv _ hs hsE]
    have hUm : Measurable (fun x : Matrix d k ℝ => U * x) :=
      measurable_const.matrix_mul measurable_id
    rw [Measure.map_map hUm hm, hpt2, key]
  -- so it is the Haar frame law
  have hν'eq : ν.map (fun x => E₀ᴴ * x) = haarFrame d k := by
    have h := (hasLaw_haarFrame_of_isLeftUnitarilyInvariant (μ := ν.map fun x => E₀ᴴ * x)
      HasLaw.id hν'orth).map_eq
    rwa [Measure.map_id] at h
  have hνrec : ν = (ν.map fun x => E₀ᴴ * x).map fun y => E₀ * y := by
    rw [Measure.map_map hm' hm]
    exact Measure.map_id.symm.trans (Measure.map_congr (hpt.mono fun x hx => hx.symm))
  -- the right-hand side
  have hgauss : (gaussianMatrix n k).map (fun Z => E₀ᴴ * Z) = gaussianMatrix d k :=
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id (U := E₀ᴴ)
      (by rwa [Matrix.conjTranspose_conjTranspose])).map_eq
  have hEZ : ∀ Z : Matrix n k ℝ, polarFactor (E * Z) = E₀ * polarFactor (E₀ᴴ * Z) := fun Z => by
    rw [← hEE, Matrix.mul_assoc, hE₀.polarFactor_mul_left]
  have hR : (gaussianMatrix n k).map (fun Z : Matrix n k ℝ => polarFactor (E * Z)) =
      (haarFrame d k).map fun y => E₀ * y := by
    have hm'' : Measurable (fun y : Matrix d k ℝ => E₀ * polarFactor y) :=
      measurable_const.matrix_mul measurable_polarFactor
    rw [show (fun Z : Matrix n k ℝ => polarFactor (E * Z)) =
        (fun y => E₀ * polarFactor y) ∘ fun Z => E₀ᴴ * Z from funext hEZ,
      ← Measure.map_map hm'' hm, hgauss, haarFrame, Measure.map_map hm' measurable_polarFactor]
    rfl
  calc ν = (ν.map fun x => E₀ᴴ * x).map fun y => E₀ * y := hνrec
    _ = (haarFrame d k).map fun y => E₀ * y := by rw [hν'eq]
    _ = _ := hR.symm

/-- If $a$ is independent of $b$ and $(a, b)$ of $c$, then $a$ is independent of $(b, c)$. -/
private theorem indepFun_prodMk_of_indepFun_of_indepFun_prodMk {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [IsProbabilityMeasure μ]
    {a : Ω → α} {b : Ω → β} {c : Ω → γ} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hc : AEMeasurable c μ) (hab : IndepFun a b μ)
    (habc : IndepFun (fun ω => (a ω, b ω)) c μ) :
    IndepFun a (fun ω => (b ω, c ω)) μ := by
  have hbc : IndepFun b c μ := habc.comp measurable_snd measurable_id
  rw [indepFun_iff_map_prod_eq_prod_map_map ha (hb.prodMk hc)]
  rw [indepFun_iff_map_prod_eq_prod_map_map (ha.prodMk hb) hc] at habc
  rw [indepFun_iff_map_prod_eq_prod_map_map ha hb] at hab
  rw [indepFun_iff_map_prod_eq_prod_map_map hb hc] at hbc
  rw [hbc, ← Measure.prodAssoc_prod, ← hab, ← habc,
    AEMeasurable.map_map_of_aemeasurable MeasurableEquiv.prodAssoc.measurable.aemeasurable
      ((ha.prodMk hb).prodMk hc)]
  rfl

/-- The compressions of a standard Gaussian matrix to the range of an orthogonal projector and
to its complement are independent. -/
private theorem indepFun_mul_one_sub_mul_of_hasLaw_gaussianMatrix [DecidableEq n]
    {E : Matrix n n ℝ} (hE : IsStarProjection E) {Y : Ω → Matrix n k ℝ}
    (hY : HasLaw Y (gaussianMatrix n k) μ) :
    IndepFun (fun ω => E * Y ω) (fun ω => (1 - E) * Y ω) μ := by
  obtain ⟨Q₁, Q₂, hQ, h₁, h₂⟩ := hE.exists_hasOrthonormalCols_fromCols_mul_conjTranspose_eq
    (p := Fin E.rank) (q := Fin (Fintype.card n - E.rank)) (Fintype.card_fin _)
    (by simp only [Fintype.card_fin]; have := E.rank_le_card_width; omega)
  obtain ⟨hQ₁, hQ₂, h₁₂⟩ := hasOrthonormalCols_fromCols_iff.1 hQ
  have h := (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hY hQ₁ hQ₂ h₁₂).comp
    (measurable_const.matrix_mul measurable_id : Measurable (Q₁ * · : _ → Matrix n k ℝ))
    (measurable_const.matrix_mul measurable_id : Measurable (Q₂ * · : _ → Matrix n k ℝ))
  simpa only [Function.comp_def, ← Matrix.mul_assoc, h₁, h₂] using h

/-- **Gaussianization in a subspace**: let $\mathbf{E}$ be an orthogonal projector of rank at
least $\lvert k \rvert$, $\mathbf{Y}$ a standard Gaussian $n \times k$ matrix and $\mathbf{F}$ a
Haar frame of $\operatorname{range}\mathbf{E}$ (the law of
$\operatorname{polar}(\mathbf{E}\mathbf{Z})$, $\mathbf{Z}$ Gaussian) independent of
$\mathbf{Y}$. Then
$$(\mathbf{I} - \mathbf{E})\mathbf{Y} + \mathbf{F}\bigl((\mathbf{E}\mathbf{Y})^{\mathsf{H}}
\mathbf{E}\mathbf{Y}\bigr)^{1/2}$$
is a standard Gaussian matrix. Its compression to $\operatorname{range}\mathbf{E}$ has the range
of $\mathbf{F}$ whenever $\mathbf{E}\mathbf{Y}$ has full column rank: a Gaussian block whose
unrevealed part spans a prescribed random frame, the step of the Krylov coupling.
[Shamir2026, Lemma 4]; there one column, resp. in an
orthonormal basis of the subspace. -/
theorem hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix [DecidableEq n] [DecidableEq k]
    {E : Matrix n n ℝ} (hE : IsStarProjection E) (hk : Fintype.card k ≤ E.rank)
    {F Y : Ω → Matrix n k ℝ}
    (hF : HasLaw F ((gaussianMatrix n k).map fun Z => polarFactor (E * Z)) μ)
    (hY : HasLaw Y (gaussianMatrix n k) μ) (hFY : IndepFun F Y μ) :
    HasLaw (fun ω => (1 - E) * Y ω + F ω * CFC.sqrt ((E * Y ω)ᴴ * (E * Y ω)))
      (gaussianMatrix n k) μ := by
  have := hY.isProbabilityMeasure
  have hYm := hY.aemeasurable
  let a : Ω → Matrix n k ℝ := fun ω => polarFactor (E * Y ω)
  let b : Ω → Matrix k k ℝ := fun ω => (E * Y ω)ᴴ * (E * Y ω)
  let c : Ω → Matrix n k ℝ := fun ω => (1 - E) * Y ω
  have hgm : Measurable fun x : Matrix n k ℝ => xᴴ * x := by fun_prop
  have hEm : Measurable fun y : Matrix n k ℝ => E * y := measurable_const.matrix_mul measurable_id
  have hEm' : Measurable fun y : Matrix n k ℝ => (1 - E) * y :=
    measurable_const.matrix_mul measurable_id
  have ham : AEMeasurable a μ := (measurable_polarFactor.comp hEm).comp_aemeasurable hYm
  have hbcm : AEMeasurable (fun ω => (b ω, c ω)) μ :=
    ((hgm.comp hEm).prodMk hEm').comp_aemeasurable hYm
  have hab : IndepFun a b μ :=
    indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix hE hY hk
  have habc : IndepFun (fun ω => (a ω, b ω)) c μ :=
    (indepFun_mul_one_sub_mul_of_hasLaw_gaussianMatrix hE hY).comp
      (measurable_polarFactor.prodMk hgm) measurable_id
  have habc' : IndepFun a (fun ω => (b ω, c ω)) μ :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk ham hbcm.fst hbcm.snd hab habc
  have hFbc : IndepFun F (fun ω => (b ω, c ω)) μ :=
    hFY.comp measurable_id ((hgm.comp hEm).prodMk hEm')
  have hlawF : μ.map F = μ.map a := by
    rw [hF.map_eq, ← hY.map_eq, AEMeasurable.map_map_of_aemeasurable
      (g := fun Z => polarFactor (E * Z)) (measurable_polarFactor.comp hEm).aemeasurable hYm]
    rfl
  have hjoint : μ.map (fun ω => (F ω, (b ω, c ω))) = μ.map (fun ω => (a ω, (b ω, c ω))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hbcm).1 hFbc,
      (indepFun_iff_map_prod_eq_prod_map_map ham hbcm).1 habc', hlawF]
  -- the matrix square root is continuous on the positive semidefinite cone and zero off it
  have hsqrt : Measurable (CFC.sqrt : Matrix k k ℝ → Matrix k k ℝ) := by
    classical
    have h : Measurable ({a : Matrix k k ℝ | 0 ≤ a}.piecewise CFC.sqrt 0) := by
      open scoped Matrix.Norms.L2Operator in
      exact CFC.continuousOn_sqrt.measurable_piecewise continuousOn_const
        isClosed_Ici.measurableSet
    convert h using 1
    funext a
    by_cases ha : 0 ≤ a
    · exact (Set.piecewise_eq_of_mem (s := {a : Matrix k k ℝ | 0 ≤ a}) _ _ ha).symm
    · rw [Set.piecewise_eq_of_notMem (s := {a : Matrix k k ℝ | 0 ≤ a}) _ _ ha,
        CFC.sqrt_of_not_nonneg ha, Pi.zero_apply]
  let G : Matrix n k ℝ × (Matrix k k ℝ × Matrix n k ℝ) → Matrix n k ℝ :=
    fun x => x.2.2 + x.1 * CFC.sqrt x.2.1
  have hG : Measurable G := (measurable_snd.comp measurable_snd).add (measurable_fst.matrix_mul
    (hsqrt.comp (measurable_fst.comp measurable_snd)))
  have hGa : G ∘ (fun ω => (a ω, (b ω, c ω))) = Y := funext fun ω => by
    simp only [Function.comp_apply, G, a, b, c]
    rw [polarFactor_mul_sqrt, ← Matrix.add_mul, sub_add_cancel, Matrix.one_mul]
  refine ⟨hG.comp_aemeasurable (hF.aemeasurable.prodMk hbcm), ?_⟩
  change μ.map (G ∘ fun ω => (F ω, (b ω, c ω))) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable (hF.aemeasurable.prodMk hbcm),
    hjoint, AEMeasurable.map_map_of_aemeasurable hG.aemeasurable (ham.prodMk hbcm), hGa,
    hY.map_eq]

end NLAlib
