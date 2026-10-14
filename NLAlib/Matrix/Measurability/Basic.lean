/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Matrix.Perturbation.Continuity
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.GramSchmidt

/-!
# Measurability of spectral quantities

For random matrices, the quantities of this library must be measurable functions of the matrix.
Norms, singular values and eigenvalues are continuous, hence measurable. The rank, the
pseudoinverse, the range projector, the condition number, the polar factor and the Gram–Schmidt
factors are not continuous but are Borel measurable.

Matrices carry the product σ-algebra `Matrix.instMeasurableSpace`.

## Main results

* `NLAlib.measurable_specNorm`, `NLAlib.measurable_frobNorm`, `NLAlib.measurable_matrixNorm`.
* `NLAlib.measurable_singularValues`, `NLAlib.measurable_eigenvalue`.
* `NLAlib.measurable_rank`, `NLAlib.measurable_pinv`, `NLAlib.measurable_rangeProjector`,
  `NLAlib.measurable_conditionNumber`.
* `NLAlib.measurable_polarFactor`, `NLAlib.measurable_gramSchmidtQ`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Continuous quantities -/

/-- A function that is continuous on each fibre of a measurable map to `ℕ` is measurable. -/
private theorem measurable_of_continuousOn_fiber {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {r : X → ℕ} (hr : Measurable r)
    (hf : ∀ k, ContinuousOn f {x | r x = k}) : Measurable f := by
  refine measurable_of_isOpen fun s hs => ?_
  have h : f ⁻¹' s = ⋃ k, f ⁻¹' s ∩ {x | r x = k} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq,
      exists_and_left, exists_eq', and_true]
  rw [h]
  refine MeasurableSet.iUnion fun k => ?_
  obtain ⟨u, hu, huk⟩ := continuousOn_iff'.1 (hf k) s hs
  rw [huk]
  exact hu.measurableSet.inter (hr (measurableSet_singleton k))

/-- The spectral norm is measurable. Port of `NLAlib.measurable_specNorm_of_entries`. -/
theorem measurable_specNorm : Measurable (specNorm : Matrix m n 𝕜 → ℝ) := by
  exact continuous_specNorm.measurable

/-- The Frobenius norm is measurable. Port of `NLAlib.measurable_frobSq_of_entries`. -/
theorem measurable_frobNorm : Measurable (frobNorm : Matrix m n 𝕜 → ℝ) := by
  exact continuous_frobNorm.measurable

/-- Every unitarily invariant norm is measurable. -/
theorem SymmetricGauge.measurable_matrixNorm (Φ : SymmetricGauge) :
    Measurable (Φ.matrixNorm : Matrix m n 𝕜 → ℝ) := by
  exact Φ.continuous_matrixNorm.measurable

/-- Each singular value is measurable. -/
theorem measurable_singularValues (k : ℕ) :
    Measurable fun A : Matrix m n 𝕜 => singularValues A k := by
  exact (continuous_singularValues k).measurable

/-- Each sorted eigenvalue is measurable (it is continuous on the closed set of Hermitian
matrices and zero elsewhere). -/
theorem measurable_eigenvalue (k : ℕ) :
    Measurable fun A : Matrix n n 𝕜 => eigenvalue A k := by
  have hs : MeasurableSet {A : Matrix n n 𝕜 | A.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · exact (continuousOn_iff_continuous_domRestrict.1 (continuousOn_eigenvalue k)).measurable
  · have h : ({A : Matrix n n 𝕜 | A.IsHermitian}ᶜ).domRestrict (fun A => eigenvalue A k) =
        fun _ => 0 := by
      funext A
      exact eigenvalue_of_not_isHermitian A.2 k
    rw [h]
    exact measurable_const

/-! ### Quantities that are not continuous -/

omit [Fintype m] in
/-- The rank is measurable. -/
theorem measurable_rank [Finite m] : Measurable fun A : Matrix m n 𝕜 => A.rank := by
  refine measurable_to_countable' fun r => ?_
  have h : (fun A : Matrix m n 𝕜 => A.rank) ⁻¹' {r} =
      {A : Matrix m n 𝕜 | A.rank ≤ r} ∩ {A : Matrix m n 𝕜 | r ≤ A.rank} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      le_antisymm_iff]
  rw [h]
  exact (isClosed_setOf_rank_le r).measurableSet.inter (isOpen_setOf_le_rank r).measurableSet

/-- **The pseudoinverse is measurable.** Port of `NLAlib.measurable_pinvL_entry_of` and
`NLAlib.measurable_pinvR_entry`. -/
theorem measurable_pinv :
    Measurable (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  exact measurable_of_continuousOn_fiber measurable_rank continuousOn_pinv_setOf_rank_eq

/-- The orthogonal projector onto the range is measurable. -/
theorem measurable_rangeProjector :
    Measurable (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) := by
  have h : (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) = fun A => A * pinv A :=
    funext fun A => (mul_pinv A).symm
  rw [h]
  exact measurable_id.matrix_mul measurable_pinv

/-- The condition number is measurable. -/
theorem measurable_conditionNumber :
    Measurable (conditionNumber : Matrix m n 𝕜 → ℝ) := by
  exact measurable_specNorm.mul (measurable_specNorm.comp measurable_pinv)

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Classical in
/-- The absolute value `(Aᴴ A)^{1/2}` is a continuous function of the matrix. -/
private theorem continuous_sqrt_gram :
    Continuous fun A : Matrix m n 𝕜 => CFC.sqrt (Aᴴ * A) := by
  have h : Continuous fun A : Matrix m n 𝕜 => Aᴴ * A :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := ⟨fun c A => by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])⟩
  exact CFC.continuousOn_sqrt.comp_continuous h fun A =>
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg

omit [Fintype n] in
/-- Each Gram–Schmidt vector of the columns is a measurable function of the matrix. -/
private theorem measurable_gramSchmidt [Finite n] [LinearOrder n] [LocallyFiniteOrderBot n]
    (j : n) :
    Measurable fun A : Matrix m n 𝕜 =>
      InnerProductSpace.gramSchmidt 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j := by
  have hcol : ∀ k : n, Measurable fun A : Matrix m n 𝕜 =>
      (WithLp.toLp 2 (A.col k) : EuclideanSpace 𝕜 m) := fun k =>
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => continuous_id.matrix_elem i k)).measurable
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    simp only [InnerProductSpace.gramSchmidt_def 𝕜 _ j, Submodule.starProjection_singleton]
    refine (hcol j).sub (Finset.measurable_fun_sum _ fun i hi => ?_)
    have hi' := ih i (Finset.mem_Iio.1 hi)
    exact ((Measurable.inner (𝕜 := 𝕜) hi' (hcol j)).div
      (RCLike.continuous_ofReal.measurable.comp (hi'.norm.pow_const 2))).smul hi'

/-- The polar factor is measurable. Port of `NLAlib.measurable_polarFrame_entry`. -/
theorem measurable_polarFactor [DecidableEq n] :
    Measurable (polarFactor : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  have h := (continuous_sqrt_gram (𝕜 := 𝕜) (m := m) (n := n)).measurable
  exact measurable_id.matrix_mul (measurable_pinv.comp h)

/-- The Gram–Schmidt orthonormalisation is measurable.
Port of `NLAlib.measurable_qrNormalizedArray`. -/
theorem measurable_gramSchmidtQ [LinearOrder n] [LocallyFiniteOrderBot n] :
    Measurable (gramSchmidtQ : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  have h := measurable_gramSchmidt (𝕜 := 𝕜) (m := m) j
  have hn : Measurable fun A : Matrix m n 𝕜 =>
      InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j := by
    unfold InnerProductSpace.gramSchmidtNormed
    exact ((RCLike.continuous_ofReal (K := 𝕜)).measurable.comp h.norm).inv.smul h
  exact (PiLp.continuous_apply 2 (fun _ : m => 𝕜) i).measurable.comp hn

end NLAlib
