/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import NLAlib.ForMathlib.MeasureTheory.Constructions.BorelSpace.MeasurableSelection
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Matrix.Perturbation.Continuity
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.GramSchmidt
public import NLAlib.Matrix.Factorizations.NystromGram
public import NLAlib.Matrix.Factorizations.SketchedLowRank

/-!
# Measurability of matrix quantities

For random matrices, the quantities of the Matrix layer must be measurable functions of the
matrix. This file belongs to the Probability layer: the Matrix layer itself has no measure theory.
Norms and singular values are continuous, hence measurable. Sorted eigenvalues are continuous
on the Hermitian locus and extended by zero elsewhere, so are Borel measurable on all matrices.
The rank, the
pseudoinverse, the range projector, the pseudo-condition number, the inverse Gram matrix, the
randomized SVD, (generalized) Nyström, the chosen SVD, the truncated SVD, the early-truncated
outputs, the polar factor and the Gram–Schmidt factors are not continuous but are Borel
measurable. The chosen SVD (`NLAlib.svdU`, `NLAlib.svdV`) is measurable by the measurable
selection theorem `IsClosed.measurable_of_forall_toLex_equivFun_le`: it is the lexicographically
least point of the closed set of SVDs.

Matrices carry the product σ-algebra `Matrix.instMeasurableSpace`. A bounded measurable function
of a random matrix is integrable on a finite measure space; the squared projection residuals are
recorded here.

## Main results

* `NLAlib.measurable_specNorm`, `NLAlib.measurable_frobNorm`, `NLAlib.measurable_matrixNorm`.
* `NLAlib.measurable_singularValues`, `NLAlib.measurable_eigenvalue`.
* `NLAlib.measurable_quadForm`, `NLAlib.measurable_rayleighQuotient`: functions of the vector.
* `NLAlib.measurableSet_setOf_posDef`: the positive definite matrices form a measurable set.
* `NLAlib.measurable_rank`, `NLAlib.measurable_pinv`, `NLAlib.measurable_rangeProjector`,
  `NLAlib.measurable_pseudoConditionNumber`.
* `NLAlib.integrable_frobNorm_one_sub_rangeProjector_mul_sq`,
  `NLAlib.integrable_specNorm_one_sub_rangeProjector_mul_sq`: a squared projection residual of a
  random sketch is integrable, being bounded.
* `NLAlib.measurable_mul_conjTranspose_inv`: the inverse Gram matrix
  $(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{-1}$; `NLAlib.measurable_rsvd`,
  `NLAlib.measurable_generalizedNystrom`, `NLAlib.measurable_nystrom`: the randomized SVD and
  (generalized) Nyström as functions of the test matrices.
* `NLAlib.measurable_svdU`, `NLAlib.measurable_svdV`: the chosen SVD;
  `NLAlib.measurable_truncatedSVD`: the truncated SVD. With it every theorem stated for a
  measurable choice of best approximations $\mathbf{Y}$ applies to the truncation of a random
  output, for instance with `hYm := ((measurable_truncatedSVD k).comp_aemeasurable
  ((measurable_rsvd A).comp_aemeasurable hX)).aestronglyMeasurable`.
* `NLAlib.measurable_earlyTruncatedRSVD`, `NLAlib.measurable_earlyTruncatedGeneralizedNystrom`:
  the early-truncated randomized SVD and generalized Nyström, built from the truncated SVD of the
  sketch.
* `NLAlib.measurable_polarFactor`, `NLAlib.measurable_gramSchmidtQ`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Continuous quantities -/

/-- A function that is continuous on each fibre of a measurable map to $\mathbb{N}$ is
measurable. -/
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

/-- The spectral norm $\mathbf{A} \mapsto \|\mathbf{A}\|_2$ is measurable. -/
@[fun_prop]
theorem measurable_specNorm : Measurable (specNorm : Matrix m n 𝕜 → ℝ) := by
  exact continuous_specNorm.measurable

/-- The Frobenius norm $\mathbf{A} \mapsto \|\mathbf{A}\|_{\mathsf{F}}$ is measurable. -/
@[fun_prop]
theorem measurable_frobNorm : Measurable (frobNorm : Matrix m n 𝕜 → ℝ) := by
  exact continuous_frobNorm.measurable

/-- Every unitarily invariant norm $\mathbf{A} \mapsto \|\mathbf{A}\|_{\Phi}$ is measurable. -/
@[fun_prop]
theorem SymmetricGauge.measurable_matrixNorm (Φ : SymmetricGauge) :
    Measurable (Φ.matrixNorm : Matrix m n 𝕜 → ℝ) := by
  exact Φ.continuous_matrixNorm.measurable

/-- Each singular value $\mathbf{A} \mapsto \sigma_k(\mathbf{A})$ is measurable. -/
@[fun_prop]
theorem measurable_singularValues (k : ℕ) :
    Measurable fun A : Matrix m n 𝕜 => singularValues A k := by
  exact (continuous_singularValues k).measurable

/-- Each sorted eigenvalue $\mathbf{A} \mapsto \lambda_k(\mathbf{A})$ is measurable (it is
continuous on the closed set of Hermitian matrices and zero elsewhere). -/
@[fun_prop]
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

omit [Fintype m] in
/-- The quadratic form $\mathbf{x} \mapsto \mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}$ of a
fixed square matrix is a measurable function of the vector (it is continuous). -/
@[fun_prop]
theorem measurable_quadForm (A : Matrix n n 𝕜) : Measurable fun x : n → 𝕜 => quadForm A x := by
  have h : Continuous fun x : n → 𝕜 => quadForm A x := by
    unfold quadForm
    fun_prop
  exact h.measurable

omit [Fintype m] in
/-- The Rayleigh quotient
$\mathbf{x} \mapsto \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) /
\|\mathbf{x}\|^2$ of a fixed square matrix is a measurable function of the vector. -/
@[fun_prop]
theorem measurable_rayleighQuotient (A : Matrix n n 𝕜) :
    Measurable fun x : n → 𝕜 => rayleighQuotient A x := by
  have hn : Continuous fun x : n → 𝕜 => ‖WithLp.toLp 2 x‖ ^ 2 :=
    ((PiLp.continuous_toLp 2 _).norm).pow 2
  exact (RCLike.continuous_re.measurable.comp (measurable_quadForm A)).div hn.measurable

omit [Fintype m] [Fintype n] in
open scoped ComplexOrder in
/-- The set of positive definite matrices is measurable: it is the set of Hermitian matrices whose
sorted eigenvalues are all positive. -/
theorem measurableSet_setOf_posDef [Finite n] :
    MeasurableSet {A : Matrix n n 𝕜 | A.PosDef} := by
  have : Fintype n := Fintype.ofFinite n
  have hH : MeasurableSet {A : Matrix n n 𝕜 | A.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have h : {A : Matrix n n 𝕜 | A.PosDef} = {A | A.IsHermitian} ∩
      ⋂ k ∈ Finset.range (Fintype.card n), {A | 0 < eigenvalue A k} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
    exact ⟨fun h => ⟨h.isHermitian, h.isHermitian.posDef_iff_eigenvalue_pos.mp h⟩,
      fun h => h.1.posDef_iff_eigenvalue_pos.mpr h.2⟩
  rw [h]
  exact hH.inter (Finset.measurableSet_biInter _ fun k _ =>
    measurableSet_lt measurable_const (measurable_eigenvalue k))

/-! ### Quantities that are not continuous -/

omit [Fintype m] in
/-- The rank $\mathbf{A} \mapsto \operatorname{rank} \mathbf{A}$ is measurable. -/
@[fun_prop]
theorem measurable_rank [Finite m] : Measurable fun A : Matrix m n 𝕜 => A.rank := by
  refine measurable_to_countable' fun r => ?_
  have h : (fun A : Matrix m n 𝕜 => A.rank) ⁻¹' {r} =
      {A : Matrix m n 𝕜 | A.rank ≤ r} ∩ {A : Matrix m n 𝕜 | r ≤ A.rank} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      le_antisymm_iff]
  rw [h]
  exact (isClosed_setOf_rank_le r).measurableSet.inter (isOpen_setOf_le_rank r).measurableSet

/-- The pseudoinverse is measurable: $\mathbf{A} \mapsto \mathbf{A}^{+}$. -/
@[fun_prop] theorem measurable_pinv :
    Measurable (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  exact measurable_of_continuousOn_fiber measurable_rank continuousOn_pinv_setOf_rank_eq

/-- The orthogonal projector onto the range, $\mathbf{A} \mapsto \mathbf{P}_{\mathbf{A}}$, is
measurable. -/
@[fun_prop]
theorem measurable_rangeProjector :
    Measurable (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) := by
  have h : (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) = fun A => A * pinv A :=
    funext fun A => (mul_pinv A).symm
  rw [h]
  exact measurable_id.matrix_mul measurable_pinv

section Integrable

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The squared Frobenius norm of a projection residual,
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{Y}})\mathbf{M}\|_{\mathsf{F}}^2$, is integrable for
an almost everywhere measurable random $\mathbf{Y}$ on a finite measure space: it is measurable
and at most $\|\mathbf{M}\|_{\mathsf{F}}^2$. -/
theorem integrable_frobNorm_one_sub_rangeProjector_mul_sq [IsFiniteMeasure μ] [DecidableEq m]
    {k p : Type*} [Fintype k] [Fintype p] (B : Matrix m n 𝕜) (M : Matrix m p 𝕜)
    {Y : Ω → Matrix n k 𝕜} (hY : AEMeasurable Y μ) :
    Integrable (fun ω => frobNorm ((1 - rangeProjector (B * Y ω)) * M) ^ 2) μ := by
  have hm : Measurable fun Z : Matrix n k 𝕜 => frobNorm ((1 - rangeProjector (B * Z)) * M) ^ 2 := by
    fun_prop
  exact Integrable.of_bound (hm.comp_aemeasurable hY).aestronglyMeasurable (frobNorm M ^ 2)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_one_sub_rangeProjector_mul_le _ _) 2)

/-- The squared spectral norm of a projection residual,
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{Y}})\mathbf{M}\|_2^2$, is integrable for an almost
everywhere measurable random $\mathbf{Y}$ on a finite measure space: it is measurable and at most
$\|\mathbf{M}\|_2^2$. -/
theorem integrable_specNorm_one_sub_rangeProjector_mul_sq [IsFiniteMeasure μ] [DecidableEq m]
    {k p : Type*} [Fintype k] [Fintype p] (B : Matrix m n 𝕜) (M : Matrix m p 𝕜)
    {Y : Ω → Matrix n k 𝕜} (hY : AEMeasurable Y μ) :
    Integrable (fun ω => specNorm ((1 - rangeProjector (B * Y ω)) * M) ^ 2) μ := by
  have hm : Measurable fun Z : Matrix n k 𝕜 => specNorm ((1 - rangeProjector (B * Z)) * M) ^ 2 := by
    fun_prop
  exact Integrable.of_bound (hm.comp_aemeasurable hY).aestronglyMeasurable (specNorm M ^ 2)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_one_sub_rangeProjector_mul_le _ _) 2)

end Integrable

/-- The pseudo-condition number $\mathbf{A} \mapsto \|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$ is
measurable. -/
@[fun_prop]
theorem measurable_pseudoConditionNumber :
    Measurable (pseudoConditionNumber : Matrix m n 𝕜 → ℝ) := by
  exact measurable_specNorm.mul (measurable_specNorm.comp measurable_pinv)

/-- The inverse Gram matrix $\mathbf{A} \mapsto (\mathbf{A}\mathbf{A}^{\mathsf{H}})^{-1}$ is
measurable (Lean's inverse, $\mathbf{0}$ where $\mathbf{A}\mathbf{A}^{\mathsf{H}}$ is singular). -/
@[fun_prop]
theorem measurable_mul_conjTranspose_inv [DecidableEq m] :
    Measurable fun A : Matrix m n 𝕜 => (A * Aᴴ)⁻¹ :=
  (measurable_id.matrix_mul (continuous_id.matrix_conjTranspose).measurable).matrix_inv

/-- The randomized SVD $\mathbf{\Omega} \mapsto \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$
is a measurable function of the test matrix. -/
@[fun_prop]
theorem measurable_rsvd {l : Type*} [Fintype l] (A : Matrix m n 𝕜) :
    Measurable fun Ω : Matrix n l 𝕜 => rsvd A Ω :=
  (measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)).matrix_mul
    measurable_const

/-- Generalized Nyström $(\mathbf{\Omega}, \mathbf{\Psi}) \mapsto \mathsf{gn}(\mathbf{A},
\mathbf{\Omega}, \mathbf{\Psi})$ is a measurable function of the two test matrices. -/
@[fun_prop]
theorem measurable_generalizedNystrom {l p : Type*} [Fintype l] [Fintype p] (A : Matrix m n 𝕜) :
    Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => generalizedNystrom A ΩΨ.1 ΩΨ.2 := by
  have hΨ : Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => ΩΨ.2ᴴ :=
    (continuous_id.matrix_conjTranspose.measurable).comp measurable_snd
  simp only [generalizedNystrom_def]
  exact (((measurable_const.matrix_mul measurable_fst).matrix_mul
    (measurable_pinv.comp ((hΨ.matrix_mul measurable_const).matrix_mul measurable_fst))).matrix_mul
      hΨ).matrix_mul measurable_const

/-- Nyström $\mathbf{\Omega} \mapsto \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$ is a measurable
function of the test matrix. -/
@[fun_prop]
theorem measurable_nystrom {l : Type*} [Fintype l] (H : Matrix n n 𝕜) :
    Measurable fun Ω : Matrix n l 𝕜 => nystrom H Ω := by
  have h := (measurable_generalizedNystrom (l := l) (p := l) H).comp
    (measurable_id.prodMk measurable_id : Measurable fun Ω : Matrix n l 𝕜 => (Ω, Ω))
  simp only [Function.comp_def] at h
  exact h

/-! ### The chosen SVD and the truncated SVD -/

/-- The chosen SVD, $\mathbf{A} \mapsto (\mathsf{svdU}(\mathbf{A}), \mathsf{svdV}(\mathbf{A}))$, is
Borel measurable: it is the lexicographically least point of the closed set of SVDs of
$\mathbf{A}$, whose sections lie in the compact set of pairs of frames. -/
private theorem measurable_svdU_svdV :
    Measurable fun A : Matrix m n 𝕜 => (svdU A, svdV A) := by
  refine isClosed_setOf_isSVD_singularValues.measurable_of_forall_toLex_equivFun_le
    (Module.finBasis ℝ _) (fun _ => ⟨Set.univ, Filter.univ_mem, _,
      isCompact_setOf_hasOrthonormalCols.prod isCompact_setOf_hasOrthonormalCols,
      fun _ _ y hy => ⟨hy.hasOrthonormalCols_left, hy.hasOrthonormalCols_right⟩⟩)
    fun A => ⟨isSVD_svdU_svdV A, fun y hy => IsSVD.toLex_equivFun_svdU_svdV_le hy⟩

/-- The left factor of the chosen SVD, $\mathbf{A} \mapsto \mathsf{svdU}(\mathbf{A})$, is Borel
measurable (it is not continuous: it jumps where singular values meet). -/
@[fun_prop]
theorem measurable_svdU : Measurable (svdU : Matrix m n 𝕜 → _) :=
  measurable_fst.comp measurable_svdU_svdV

/-- The right factor of the chosen SVD, $\mathbf{A} \mapsto \mathsf{svdV}(\mathbf{A})$, is Borel
measurable. -/
@[fun_prop]
theorem measurable_svdV : Measurable (svdV : Matrix m n 𝕜 → _) :=
  measurable_snd.comp measurable_svdU_svdV

/-- The truncated SVD is Borel measurable: $\mathbf{A} \mapsto \llbracket\mathbf{A}
\rrbracket_k$ is measurable for every $k$, though not continuous (it jumps at ties
$\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$). So the expectation of any error of a truncated
random output is defined, and every theorem stated for a measurable choice of best
approximations applies at `NLAlib.truncatedSVD`. -/
@[fun_prop]
theorem measurable_truncatedSVD (k : ℕ) :
    Measurable fun A : Matrix m n 𝕜 => truncatedSVD A k := by
  have hD : Continuous fun A : Matrix m n 𝕜 =>
      Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) := by
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    split_ifs
    · exact RCLike.continuous_ofReal.comp (continuous_singularValues (i : ℕ))
    · exact continuous_const
  simp only [truncatedSVD_def]
  exact (measurable_svdU.matrix_mul hD.measurable).matrix_mul
    ((continuous_id.matrix_conjTranspose.measurable).comp measurable_svdV)

section EarlyTruncation

variable {l p : Type*} [Fintype l] [Fintype p]

/-- The early-truncated randomized SVD
$\mathbf{\Omega} \mapsto \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ is a
measurable function of the test matrix. -/
@[fun_prop]
theorem measurable_earlyTruncatedRSVD (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun Ω : Matrix n l 𝕜 => earlyTruncatedRSVD A Ω k :=
  (measurable_rangeProjector.comp
    ((measurable_truncatedSVD k).comp
      (measurable_const.matrix_mul measurable_id))).matrix_mul measurable_const

/-- Early-truncated generalized Nyström
$(\mathbf{\Omega}, \mathbf{\Psi}) \mapsto \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)$ is a measurable function of the two test matrices. -/
@[fun_prop]
theorem measurable_earlyTruncatedGeneralizedNystrom (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 =>
      earlyTruncatedGeneralizedNystrom A ΩΨ.1 ΩΨ.2 k := by
  have hΨ : Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => ΩΨ.2ᴴ :=
    (continuous_id.matrix_conjTranspose.measurable).comp measurable_snd
  have hT : Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => truncatedSVD (A * ΩΨ.1) k :=
    (measurable_truncatedSVD k).comp (measurable_const.matrix_mul measurable_fst)
  simp only [earlyTruncatedGeneralizedNystrom, obliqueProjector]
  exact ((hT.matrix_mul (measurable_pinv.comp (hΨ.matrix_mul hT))).matrix_mul hΨ).matrix_mul
    measurable_const

end EarlyTruncation

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Classical in
/-- The absolute value $(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2}$ is a continuous function of the
matrix. -/
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
/-- Each Gram–Schmidt vector of the columns (unnormalised, `InnerProductSpace.gramSchmidt`) is a
measurable function of the matrix. -/
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

/-- The polar factor is measurable. -/
@[fun_prop]
theorem measurable_polarFactor [DecidableEq n] :
    Measurable (polarFactor : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  have h := (continuous_sqrt_gram (𝕜 := 𝕜) (m := m) (n := n)).measurable
  exact measurable_id.matrix_mul (measurable_pinv.comp h)

/-- The Gram–Schmidt orthonormalisation is measurable. -/
@[fun_prop]
theorem measurable_gramSchmidtQ [LinearOrder n] [LocallyFiniteOrderBot n] :
    Measurable (gramSchmidtQ : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  have h := measurable_gramSchmidt (𝕜 := 𝕜) (m := m) j
  have hn : Measurable fun A : Matrix m n 𝕜 =>
      InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j := by
    unfold InnerProductSpace.gramSchmidtNormed
    exact ((RCLike.continuous_ofReal (K := 𝕜)).measurable.comp h.norm).inv.smul h
  exact (PiLp.continuous_apply 2 (fun _ : m => 𝕜) i).measurable.comp hn

/-! ### Deprecated aliases -/

@[deprecated measurable_pseudoConditionNumber (since := "2026-10-14")]
alias measurable_conditionNumber :=
  measurable_pseudoConditionNumber

end NLAlib
