/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import NLAlib.Matrix.Factorizations.QR

/-!
# Gram–Schmidt orthogonalisation of the columns of a matrix

The Gram–Schmidt process applied to the columns of $\mathbf{A}$, in the order of the column
index, gives $\mathbf{Q}$ = `NLAlib.gramSchmidtQ A`, whose nonzero columns are orthonormal, and the
upper triangular $\mathbf{R} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$ = `NLAlib.gramSchmidtR A` with
nonnegative diagonal, with $\mathbf{A} = \mathbf{Q}\mathbf{R}$ always. A column of $\mathbf{Q}$
vanishes exactly when the corresponding column of $\mathbf{A}$ depends on the earlier ones; for
$\mathbf{A}$ of full column rank this is the QR factorization with positive diagonal.

The process is Mathlib's `InnerProductSpace.gramSchmidtNormed` on the columns.

## Main definitions

* `NLAlib.gramSchmidtQ`, `NLAlib.gramSchmidtR`: the two factors.
* `NLAlib.mgsSweep`: the modified Gram–Schmidt sweep of a vector against a sequence.

## Main results

* `NLAlib.gramSchmidtQ_mul_gramSchmidtR`: $\mathbf{Q}\mathbf{R} = \mathbf{A}$.
* `NLAlib.isUpperTriangular_gramSchmidtR`, `NLAlib.gramSchmidtR_apply_self_nonneg`.
* `NLAlib.gramSchmidtR_apply_self_smul_col`: the classical recursion.
* `NLAlib.isQR_gramSchmidt`: the QR factorization of a matrix of full column rank.
* `NLAlib.range_gramSchmidtQ`, `NLAlib.gramSchmidtQ_mul_conjTranspose`: with no rank assumption,
  $\mathbf{Q}$ spans the column space and
  $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}}$.
* `NLAlib.gramSchmidtQ_submatrix`, `NLAlib.gramSchmidtQ_submatrix_castLE`: restriction to an
  initial segment of the columns.
* `NLAlib.gramSchmidtQ_col_eq_zero_iff`, `NLAlib.gramSchmidtQ_col_bot`: zero columns and the first
  column.
* `NLAlib.dotProduct_mgsSweep_gramSchmidtQ_col`, `NLAlib.mgsSweep_gramSchmidtQ_col`: the triangular
  entries and swept columns in the modified process.
* `NLAlib.mgsSweep_eq_sub_sum`: the modified Gram–Schmidt sweep `NLAlib.mgsSweep` equals the
  classical one against pairwise orthogonal vectors.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [LinearOrder n]
  [LocallyFiniteOrderBot n]

/-! ### The Gram–Schmidt process in an inner product space -/

section General

open InnerProductSpace

variable {ι E F : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem inner_gramSchmidt_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 f j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K, Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f (Finset.mem_Iio.mp hi).ne', mul_zero]

private theorem inner_gramSchmidtNormed_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) := by
  rw [gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self, RCLike.conj_inv,
    RCLike.conj_ofReal, sq]
  by_cases h : (‖gramSchmidt 𝕜 f j‖ : 𝕜) = 0
  · rw [h, mul_zero, mul_zero]
  · rw [inv_mul_cancel_left₀ h]

private theorem inner_gramSchmidtNormed_of_ne (f : ι → E) {k l : ι} (hkl : k ≠ l) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f k) (gramSchmidtNormed 𝕜 f l) = 0 := by
  rw [gramSchmidtNormed, gramSchmidtNormed, inner_smul_left, inner_smul_right,
    gramSchmidt_orthogonal 𝕜 f hkl, mul_zero, mul_zero]

private theorem inner_gramSchmidtNormed_self_of_ne_zero (f : ι → E) {k : ι}
    (h : gramSchmidt 𝕜 f k ≠ 0) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f k) (gramSchmidtNormed 𝕜 f k) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, gramSchmidtNormed, norm_smul_inv_norm h, RCLike.ofReal_one,
    one_pow]

/-- The Gram–Schmidt recursion for the normalised vectors. -/
private theorem norm_gramSchmidt_smul_gramSchmidtNormed (f : ι → E) (j : ι) :
    (‖gramSchmidt 𝕜 f j‖ : 𝕜) • gramSchmidtNormed 𝕜 f j =
      f j - ∑ i ∈ Finset.Iio j,
        inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i := by
  have h1 : (‖gramSchmidt 𝕜 f j‖ : 𝕜) • gramSchmidtNormed 𝕜 f j = gramSchmidt 𝕜 f j := by
    by_cases h : gramSchmidt 𝕜 f j = 0
    · rw [gramSchmidtNormed, h, smul_zero, smul_zero]
    · rw [gramSchmidtNormed,
        smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))]
  rw [h1, eq_sub_iff_add_eq]
  conv_rhs => rw [gramSchmidt_def'' 𝕜 f j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gramSchmidtNormed, inner_smul_left, smul_smul, RCLike.conj_inv, RCLike.conj_ofReal]
  congr 1
  ring

private theorem gramSchmidt_eq_zero_iff (f : ι → E) (j : ι) :
    gramSchmidt 𝕜 f j = 0 ↔ f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← span_gramSchmidt_Iio, gramSchmidt_def'' 𝕜 f j, h, zero_add]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  · have hle : Submodule.span 𝕜 (f '' Set.Iio j) ≤ (𝕜 ∙ gramSchmidt 𝕜 f j)ᗮ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (gramSchmidt_inv_triangular 𝕜 f hi)
    have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle h)
    rw [inner_gramSchmidt_self] at h0
    exact norm_eq_zero.mp (RCLike.ofReal_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

/-- The Gram–Schmidt process commutes with a linear isometry. -/
private theorem gramSchmidt_map (T : E →ₗᵢ[𝕜] F) (f : ι → E) (j : ι) :
    gramSchmidt 𝕜 (fun k => T (f k)) j = T (gramSchmidt 𝕜 f j) := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    rw [gramSchmidt_def 𝕜 (fun k => T (f k)) j, gramSchmidt_def 𝕜 f j, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ih i (Finset.mem_Iio.mp hi), Submodule.starProjection_singleton,
      Submodule.starProjection_singleton, map_smul, T.inner_map_map, T.norm_map]

private theorem gramSchmidtNormed_map (T : E →ₗᵢ[𝕜] F) (f : ι → E) (j : ι) :
    gramSchmidtNormed 𝕜 (fun k => T (f k)) j = T (gramSchmidtNormed 𝕜 f j) := by
  rw [gramSchmidtNormed, gramSchmidtNormed, gramSchmidt_map, T.norm_map, map_smul]

end General

/-- Membership in a span of vectors, read in the Euclidean space. -/
private theorem toLp_mem_span_image_iff {ι κ : Type*} (v : ι → κ → 𝕜) (s : Set ι) (x : κ → 𝕜) :
    WithLp.toLp 2 x ∈ Submodule.span 𝕜 ((fun k => WithLp.toLp 2 (v k)) '' s) ↔
      x ∈ Submodule.span 𝕜 (v '' s) := by
  have h : (fun k => WithLp.toLp 2 (v k)) '' s =
      ((WithLp.linearEquiv 2 𝕜 (κ → 𝕜)).symm : (κ → 𝕜) →ₗ[𝕜] WithLp 2 (κ → 𝕜)) '' (v '' s) := by
    rw [Set.image_image]
    rfl
  rw [h, ← Submodule.map_span, Submodule.mem_map_equiv]
  rfl

/-! ### The factors -/

/-- The matrix of Gram–Schmidt vectors of the columns of $\mathbf{A}$: column $j$ is the
normalised component of column $j$ of $\mathbf{A}$ orthogonal to the earlier columns, or zero if
that component is zero.
Algorithm: gram-schmidt -/
noncomputable def gramSchmidtQ (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  Matrix.of fun i j =>
    InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j i

/-- The triangular factor of the Gram–Schmidt process,
$\mathbf{R} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$.
Algorithm: gram-schmidt -/
noncomputable def gramSchmidtR (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (gramSchmidtQ A)ᴴ * A

/-- The columns of $\mathbf{A}$ as vectors of the Euclidean space. -/
private abbrev colVec (A : Matrix m n 𝕜) (k : n) : EuclideanSpace 𝕜 m :=
  WithLp.toLp 2 (A.col k)

private theorem gramSchmidtR_apply (A : Matrix m n 𝕜) (k j : n) :
    gramSchmidtR A k j =
      inner 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) k) (colVec A j) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, gramSchmidtR, Matrix.mul_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, mul_comm]
  rfl

private theorem gramSchmidtR_apply_self (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j = (‖InnerProductSpace.gramSchmidt 𝕜 (colVec A) j‖ : 𝕜) := by
  rw [gramSchmidtR_apply, inner_gramSchmidtNormed_self]

/-- The triangular factor is upper triangular. -/
theorem isUpperTriangular_gramSchmidtR (A : Matrix m n 𝕜) :
    (gramSchmidtR A).IsUpperTriangular := by
  intro k j hjk
  have hjk' : j < k := hjk
  rw [gramSchmidtR_apply, InnerProductSpace.gramSchmidtNormed, inner_smul_left,
    InnerProductSpace.gramSchmidt_inv_triangular 𝕜 _ hjk', mul_zero]

/-- The diagonal of the triangular factor is nonnegative. -/
theorem gramSchmidtR_apply_self_nonneg (A : Matrix m n 𝕜) (j : n) : 0 ≤ gramSchmidtR A j j := by
  rw [gramSchmidtR_apply_self]
  exact RCLike.ofReal_nonneg.mpr (norm_nonneg _)

/-- The classical Gram–Schmidt recursion:
$\mathbf{R}_{j,j} \mathbf{q}_j = \mathbf{a}_j - \sum_{k < j} \mathbf{R}_{k,j} \mathbf{q}_k$, with
$\mathbf{a}_j$, $\mathbf{q}_j$ the columns of $\mathbf{A}$, $\mathbf{Q}$. -/
theorem gramSchmidtR_apply_self_smul_col (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j • (gramSchmidtQ A).col j =
      A.col j - ∑ k ∈ Finset.Iio j, gramSchmidtR A k j • (gramSchmidtQ A).col k := by
  have h := congrArg WithLp.ofLp (norm_gramSchmidt_smul_gramSchmidtNormed (𝕜 := 𝕜) (colVec A) j)
  rw [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_sum] at h
  rw [gramSchmidtR_apply_self]
  simp only [gramSchmidtR_apply]
  exact h

/-- Gram–Schmidt factors the matrix: $\mathbf{Q}\mathbf{R} = \mathbf{A}$, with no rank
assumption. -/
theorem gramSchmidtQ_mul_gramSchmidtR (A : Matrix m n 𝕜) :
    gramSchmidtQ A * gramSchmidtR A = A := by
  ext i j
  have h := congrFun (gramSchmidtR_apply_self_smul_col A j) i
  simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, Matrix.col_apply, smul_eq_mul,
    mul_comm (gramSchmidtR A _ j)] at h
  rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic j)),
    ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, h, sub_add_cancel]
  intro k _ hk
  rw [isUpperTriangular_gramSchmidtR A (not_le.mp (Finset.mem_Iic.not.mp hk)), mul_zero]

/-- The Gram matrix $\mathbf{Q}^{\mathsf{H}}\mathbf{Q}$ of the Gram–Schmidt vectors is diagonal,
with entry $0$ where $\mathbf{R}_{j,j} = 0$ and $1$ elsewhere. -/
theorem conjTranspose_gramSchmidtQ_mul_self [DecidableEq n] (A : Matrix m n 𝕜) :
    (gramSchmidtQ A)ᴴ * gramSchmidtQ A =
      Matrix.diagonal fun j => if gramSchmidtR A j j = 0 then 0 else 1 := by
  ext k l
  have h : ((gramSchmidtQ A)ᴴ * gramSchmidtQ A) k l =
      inner 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) k)
        (InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) l) := by
    rw [conjTranspose_mul_self_apply, dotProduct_comm]
    rfl
  rw [h]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.diagonal_apply_eq, gramSchmidtR_apply_self]
    by_cases h0 : InnerProductSpace.gramSchmidt 𝕜 (colVec A) k = 0
    · rw [if_pos (by rw [h0, norm_zero, RCLike.ofReal_zero]),
        InnerProductSpace.gramSchmidtNormed, h0, smul_zero, inner_zero_left]
    · rw [if_neg (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)),
        inner_gramSchmidtNormed_self_of_ne_zero _ h0]
  · rw [Matrix.diagonal_apply_ne _ hkl, inner_gramSchmidtNormed_of_ne _ hkl]

/-- A diagonal entry $\mathbf{R}_{j,j}$ vanishes exactly when column $j$ of $\mathbf{A}$ lies in
the span of the earlier columns. -/
theorem gramSchmidtR_apply_self_eq_zero_iff (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j = 0 ↔ A.col j ∈ Submodule.span 𝕜 (A.col '' Set.Iio j) := by
  rw [gramSchmidtR_apply_self, RCLike.ofReal_eq_zero, norm_eq_zero, gramSchmidt_eq_zero_iff]
  exact toLp_mem_span_image_iff A.col (Set.Iio j) (A.col j)

/-- The diagonal of $\mathbf{R}$ has no zero exactly when $\mathbf{A}$ has full column rank
($\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ injective). -/
theorem forall_gramSchmidtR_apply_self_ne_zero_iff (A : Matrix m n 𝕜) :
    (∀ j, gramSchmidtR A j j ≠ 0) ↔ Function.Injective A.mulVec := by
  classical
  refine ⟨fun h => ?_, fun h j => ?_⟩
  · have hQ : HasOrthonormalCols (gramSchmidtQ A) := by
      rw [HasOrthonormalCols, conjTranspose_gramSchmidtQ_mul_self, ← Matrix.diagonal_one]
      exact congrArg _ (funext fun j => if_neg (h j))
    exact (IsQR.injective_mulVec_iff ⟨(gramSchmidtQ_mul_gramSchmidtR A).symm, hQ,
      isUpperTriangular_gramSchmidtR A⟩).mpr h
  · rw [gramSchmidtR_apply_self, Ne, RCLike.ofReal_eq_zero, norm_eq_zero]
    exact InnerProductSpace.gramSchmidt_ne_zero j ((Matrix.mulVec_injective_iff.mp h).map'
      (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap (LinearEquiv.ker _))

/-- The first Gram–Schmidt vectors span the same subspace as the first columns of $\mathbf{A}$:
the columns $i \le j$ of $\mathbf{Q}$ and of $\mathbf{A}$ have the same span. -/
theorem span_gramSchmidtQ_col_image_Iic (A : Matrix m n 𝕜) (j : n) :
    Submodule.span 𝕜 ((gramSchmidtQ A).col '' Set.Iic j) =
      Submodule.span 𝕜 (A.col '' Set.Iic j) := by
  have h : Submodule.span 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) '' Set.Iic j) =
      Submodule.span 𝕜 (colVec A '' Set.Iic j) := by
    rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]
  ext x
  refine (toLp_mem_span_image_iff _ _ x).symm.trans
    (Iff.trans ?_ (toLp_mem_span_image_iff _ _ x))
  exact iff_of_eq (congrArg (fun S => WithLp.toLp 2 x ∈ S) h)

/-- For $\mathbf{A}$ of full column rank the Gram–Schmidt vectors are orthonormal. -/
theorem hasOrthonormalCols_gramSchmidtQ [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : HasOrthonormalCols (gramSchmidtQ A) := by
  rw [HasOrthonormalCols, conjTranspose_gramSchmidtQ_mul_self, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun j =>
    if_neg ((forall_gramSchmidtR_apply_self_ne_zero_iff A).mpr hA j))

/-- **Gram–Schmidt computes the QR factorization** of a matrix of full column rank.
[TrefethenBau1997, Lecture 7]. -/
theorem isQR_gramSchmidt [DecidableEq n] {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    IsQR A (gramSchmidtQ A) (gramSchmidtR A) := by
  exact ⟨(gramSchmidtQ_mul_gramSchmidtR A).symm, hasOrthonormalCols_gramSchmidtQ hA,
    isUpperTriangular_gramSchmidtR A⟩

/-- For $\mathbf{A}$ of full column rank the diagonal of the triangular factor is positive. -/
theorem gramSchmidtR_apply_self_pos {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    (j : n) : 0 < gramSchmidtR A j j := by
  exact (gramSchmidtR_apply_self_nonneg A j).lt_of_ne'
    ((forall_gramSchmidtR_apply_self_ne_zero_iff A).mpr hA j)

/-- Gram–Schmidt commutes with a factor $\mathbf{W}$ with orthonormal columns on the left: the
Gram–Schmidt factor of $\mathbf{W}\mathbf{A}$ is $\mathbf{W}\mathbf{Q}$. -/
theorem HasOrthonormalCols.gramSchmidtQ_mul_left {l : Type*} [Fintype l] [DecidableEq m]
    {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) :
    gramSchmidtQ (W * A) = W * gramSchmidtQ A := by
  let T : EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 l :=
    { toLinearMap := Matrix.toEuclideanLin W
      norm_map' := fun x => hW.norm_toLp_mulVec x.ofLp }
  ext i j
  change (InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => T (colVec A k)) j) i = _
  rw [gramSchmidtNormed_map]
  rfl

/-- The triangular factor is unchanged by a factor $\mathbf{W}$ with orthonormal columns on the
left: $\mathbf{W}\mathbf{A}$ and $\mathbf{A}$ have the same triangular factor $\mathbf{R}$. -/
theorem HasOrthonormalCols.gramSchmidtR_mul_left {l : Type*} [Fintype l] [DecidableEq m]
    {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) :
    gramSchmidtR (W * A) = gramSchmidtR A := by
  rw [gramSchmidtR, HasOrthonormalCols.gramSchmidtQ_mul_left hW, hW.conjTranspose_mul_mul,
    gramSchmidtR]

/-- The Gram–Schmidt vectors span the column space: $\operatorname{range}\mathbf{Q} =
\operatorname{range}\mathbf{A}$ for $\mathbf{Q}$ = `gramSchmidtQ A`, with no rank assumption (the
zero columns contribute nothing). -/
theorem range_gramSchmidtQ (A : Matrix m n 𝕜) :
    LinearMap.range (gramSchmidtQ A).mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (gramSchmidtQ A).col j ∈ Submodule.span 𝕜 ((gramSchmidtQ A).col '' Set.Iic j) :=
      Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
    rw [span_gramSchmidtQ_col_image_Iic] at hj
    exact Submodule.span_mono (Set.image_subset_range _ _) hj
  · conv_lhs => rw [← gramSchmidtQ_mul_gramSchmidtR A]
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _

/-- A column of the Gram–Schmidt matrix vanishes exactly when the corresponding diagonal entry
of the triangular factor does. -/
theorem gramSchmidtQ_col_eq_zero_iff (A : Matrix m n 𝕜) (j : n) :
    (gramSchmidtQ A).col j = 0 ↔ gramSchmidtR A j j = 0 := by
  rw [gramSchmidtR_apply_self, RCLike.ofReal_eq_zero, norm_eq_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra h0
    have h1 := inner_gramSchmidtNormed_self_of_ne_zero (𝕜 := 𝕜) (colVec A) h0
    have h2 : InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) j = 0 := by
      ext i
      exact congrFun h i
    rw [h2, inner_zero_left] at h1
    exact zero_ne_one h1
  · ext i
    change InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) j i = 0
    rw [InnerProductSpace.gramSchmidtNormed, h, smul_zero]
    rfl

/-- The first Gram–Schmidt vector is the normalised first column,
$\mathbf{q}_0 = \|\mathbf{a}_0\|^{-1}\mathbf{a}_0$ (zero when $\mathbf{a}_0 = \mathbf{0}$). -/
theorem gramSchmidtQ_col_bot [OrderBot n] (A : Matrix m n 𝕜) :
    (gramSchmidtQ A).col ⊥ = (‖WithLp.toLp 2 (A.col ⊥)‖⁻¹ : 𝕜) • A.col ⊥ := by
  have h : InnerProductSpace.gramSchmidt 𝕜 (colVec A) ⊥ = colVec A ⊥ := by
    rw [InnerProductSpace.gramSchmidt_def, Finset.sum_eq_zero, sub_zero]
    intro i hi
    exact absurd (Finset.mem_Iio.mp hi) not_lt_bot
  ext i
  change InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) ⊥ i = _
  rw [InnerProductSpace.gramSchmidtNormed, h]
  rfl

/-- The Gram–Schmidt matrix is fixed by its Gram matrix:
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$, with no rank assumption, since the
columns on which $\mathbf{Q}^{\mathsf{H}}\mathbf{Q}$ vanishes are zero. -/
theorem gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self (A : Matrix m n 𝕜) :
    gramSchmidtQ A * ((gramSchmidtQ A)ᴴ * gramSchmidtQ A) = gramSchmidtQ A := by
  classical
  rw [conjTranspose_gramSchmidtQ_mul_self]
  ext i j
  rw [Matrix.mul_diagonal]
  split_ifs with h
  · rw [mul_zero]
    exact (congrFun ((gramSchmidtQ_col_eq_zero_iff A j).mpr h) i).symm
  · rw [mul_one]

/-- The Gram–Schmidt matrix is a partial isometry onto the column space:
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}}$ for $\mathbf{Q}$ = `gramSchmidtQ A`,
with no rank assumption. -/
theorem gramSchmidtQ_mul_conjTranspose (A : Matrix m n 𝕜) :
    gramSchmidtQ A * (gramSchmidtQ A)ᴴ = rangeProjector A := by
  have hQ := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self A
  refine IsStarProjection.eq_rangeProjector (Matrix.isStarProjection_iff.mpr ⟨?_, ?_⟩) ?_
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc (gramSchmidtQ A), hQ]
  · exact Matrix.isHermitian_mul_conjTranspose_self _
  · rw [← range_gramSchmidtQ A]
    refine le_antisymm ?_ ?_
    · rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · conv_lhs => rw [← hQ, ← Matrix.mul_assoc, Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _

/-- Gram–Schmidt commutes with restriction to an initial segment of columns: for an order
embedding $e$ whose range is a lower set, the Gram–Schmidt matrix of the columns $e(j)$ of
$\mathbf{A}$ consists of the columns $e(j)$ of the Gram–Schmidt matrix of $\mathbf{A}$. -/
theorem gramSchmidtQ_submatrix {p : Type*} [Fintype p] [LinearOrder p] [LocallyFiniteOrderBot p]
    (A : Matrix m n 𝕜) (e : p ↪o n) (he : IsLowerSet (Set.range e)) :
    gramSchmidtQ (A.submatrix id e) = (gramSchmidtQ A).submatrix id e := by
  have hIio : ∀ j : p, (Finset.Iio j).map e.toEmbedding = Finset.Iio (e j) := by
    intro j
    ext x
    simp only [Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact e.lt_iff_lt.mpr hy
    · obtain ⟨y, rfl⟩ := he hx.le ⟨j, rfl⟩
      exact ⟨y, e.lt_iff_lt.mp hx, rfl⟩
  have hgs : ∀ j : p, InnerProductSpace.gramSchmidt 𝕜 (fun k => colVec A (e k)) j =
      InnerProductSpace.gramSchmidt 𝕜 (colVec A) (e j) := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      rw [InnerProductSpace.gramSchmidt_def, InnerProductSpace.gramSchmidt_def 𝕜 (colVec A),
        ← hIio, Finset.sum_map]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ih i (Finset.mem_Iio.mp hi)]
      rfl
  ext i j
  change InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => colVec A (e k)) j i =
    InnerProductSpace.gramSchmidtNormed 𝕜 (colVec A) (e j) i
  rw [InnerProductSpace.gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed, hgs]

/-- Gram–Schmidt of the first $q$ columns is the first $q$ columns of Gram–Schmidt. -/
theorem gramSchmidtQ_submatrix_castLE {q q' : ℕ} (h : q ≤ q') (A : Matrix m (Fin q') 𝕜) :
    gramSchmidtQ (A.submatrix id (Fin.castLE h)) = (gramSchmidtQ A).submatrix id (Fin.castLE h) :=
  gramSchmidtQ_submatrix A (Fin.castLEOrderEmb h) (by
    rintro a b hba ⟨c, rfl⟩
    exact ⟨⟨b, lt_of_le_of_lt (Fin.le_def.mp hba) c.2⟩, rfl⟩)

/-! ### Modified Gram–Schmidt -/

section Modified

variable {m : Type*} [Fintype m]

/-- The **modified Gram–Schmidt sweep**: $\mathbf{u}_0 = \mathbf{w}$ and
$\mathbf{u}_{i+1} = \mathbf{u}_i - (\mathbf{v}_i^{\mathsf{H}}\mathbf{u}_i)\mathbf{v}_i$; the value
at $k$ is $\mathbf{w}$ reduced against $\mathbf{v}_0, \dots, \mathbf{v}_{k-1}$, one vector at a
time, each coefficient computed from the partially reduced vector. The vectors are not assumed
normalised. It is the inner loop of the Arnoldi process. [GolubVanLoan2013, §5.2.8]. -/
def mgsSweep (V : ℕ → m → 𝕜) (w : m → 𝕜) : ℕ → m → 𝕜
  | 0 => w
  | i + 1 => mgsSweep V w i - (star (V i) ⬝ᵥ mgsSweep V w i) • V i

/-- **Projection coefficients in modified Gram–Schmidt.** A vector orthogonal to the first
$k$ sweep vectors has the same inner product with the partially reduced column
$\mathsf{mgsSweep}(\mathbf{v},\mathbf{w},k)$ as with the original column. In particular, taking
the next orthogonal vector gives the same entry of the triangular factor as classical
Gram–Schmidt, including when an earlier column has vanished. [GolubVanLoan2013, §5.2.8]. -/
theorem dotProduct_mgsSweep_eq {V : ℕ → m → 𝕜} {x : m → 𝕜} {k : ℕ}
    (h : ∀ i < k, star x ⬝ᵥ V i = 0) (w : m → 𝕜) :
    star x ⬝ᵥ mgsSweep V w k = star x ⬝ᵥ w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mgsSweep, dotProduct_sub, dotProduct_smul, h k (Nat.lt_succ_self k), smul_zero, sub_zero]
    exact ih fun i hi => h i (Nat.lt_succ_of_lt hi)

/-- **Modified and classical Gram–Schmidt agree in exact arithmetic**: if
$\mathbf{v}_i^{\mathsf{H}}\mathbf{v}_j = 0$ for $j < i < k$, then
$$\mathsf{mgsSweep}(\mathbf{v}, \mathbf{w}, k) = \mathbf{w} - \sum_{i < k}
(\mathbf{v}_i^{\mathsf{H}}\mathbf{w})\mathbf{v}_i\,.$$
[GolubVanLoan2013, §5.2.8]. -/
theorem mgsSweep_eq_sub_sum {V : ℕ → m → 𝕜} {k : ℕ}
    (h : ∀ i < k, ∀ j < i, star (V i) ⬝ᵥ V j = 0) (w : m → 𝕜) :
    mgsSweep V w k = w - ∑ i ∈ Finset.range k, (star (V i) ⬝ᵥ w) • V i := by
  induction k with
  | zero => simp [mgsSweep]
  | succ k ih =>
    have ih' := ih fun i hi j hj => h i (Nat.lt_succ_of_lt hi) j hj
    have hc := dotProduct_mgsSweep_eq (h k (Nat.lt_succ_self k)) w
    change mgsSweep V w k - (star (V k) ⬝ᵥ mgsSweep V w k) • V k = _
    rw [hc, ih', Finset.sum_range_succ, sub_sub]

/-- The columns of the Gram–Schmidt factor are mutually orthogonal, with squared norm one for a
successful pivot and zero for a breakdown. -/
theorem dotProduct_gramSchmidtQ_col {k : ℕ} (M : Matrix m (Fin k) 𝕜)
    (c c' : Fin k) : star ((gramSchmidtQ M).col c) ⬝ᵥ (gramSchmidtQ M).col c' =
      if c = c' then (if gramSchmidtR M c c = 0 then 0 else 1) else 0 := by
  have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self M) c) c'
  rw [Matrix.mul_apply, Matrix.diagonal_apply] at h
  rw [← h, dotProduct]
  rfl

private theorem star_col_dotProduct_eq_gramSchmidtR {k : ℕ} (M : Matrix m (Fin k) 𝕜)
    (c j : Fin k) : star ((gramSchmidtQ M).col c) ⬝ᵥ M.col j = gramSchmidtR M c j := by
  rw [gramSchmidtR, Matrix.mul_apply, dotProduct]
  rfl

/-- Sweeping column $j$ against the preceding Gram–Schmidt columns gives
$r_{jj}\mathbf{q}_j$, including a zero residual at breakdown. -/
theorem mgsSweep_gramSchmidtQ_col {k : ℕ} (M : Matrix m (Fin k) 𝕜) (u : Fin k) :
    mgsSweep (fun c a => if h : c < k then gramSchmidtQ M a ⟨c, h⟩ else 0) (M.col u) u =
      gramSchmidtR M u u • (gramSchmidtQ M).col u := by
  obtain ⟨j, hj⟩ := u
  set Vc : ℕ → m → 𝕜 := fun c a => if h : c < k then gramSchmidtQ M a ⟨c, h⟩ else 0
  have hV : ∀ c (h : c < k), Vc c = (gramSchmidtQ M).col ⟨c, h⟩ := fun c h => by
    ext a; simp [Vc, h, Matrix.col]
  rw [mgsSweep_eq_sub_sum, gramSchmidtR_apply_self_smul_col]
  · congr 1
    set g : ℕ → m → 𝕜 := fun i => if h : i < k then
      gramSchmidtR M ⟨i, h⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨i, h⟩ else 0
    have hg : ∀ c : Fin k, gramSchmidtR M c ⟨j, hj⟩ • (gramSchmidtQ M).col c = g c := fun c => by
      simp [g, c.2]
    rw [Finset.sum_congr rfl fun c _ => hg c]
    change _ = ∑ c ∈ Finset.Iio (⟨j, hj⟩ : Fin k), g (Fin.valEmbedding c)
    rw [← Finset.sum_map (Finset.Iio ⟨j, hj⟩) Fin.valEmbedding g, Fin.map_valEmbedding_Iio,
      Nat.Iio_eq_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := (Finset.mem_range.mp hi).trans hj
    simp only [g, hik, dif_pos, hV i hik]
    rw [← star_col_dotProduct_eq_gramSchmidtR]
  · intro i hi i' hi'
    rw [hV i (hi.trans hj), hV i' ((hi'.trans hi).trans hj), dotProduct_gramSchmidtQ_col,
      if_neg (fun h => by simp [Fin.ext_iff] at h; omega)]

/-- **Triangular coefficients of modified Gram–Schmidt.** The product of $\mathbf{q}_i$ with
the residual of column $j$ after the first $i$ projections gives $r_{ij}$ of classical
Gram–Schmidt. This holds at every step of $\mathsf{mgsSweep}$, also for dependent columns.
[GolubVanLoan2013, §5.2.8].
Result: gram-schmidt -/
theorem dotProduct_mgsSweep_gramSchmidtQ_col {k : ℕ} (A : Matrix m (Fin k) 𝕜) (i j : Fin k) :
    star ((gramSchmidtQ A).col i) ⬝ᵥ
      mgsSweep (fun l a => if h : l < k then gramSchmidtQ A a ⟨l, h⟩ else 0) (A.col j) i =
        gramSchmidtR A i j := by
  rw [dotProduct_mgsSweep_eq]
  · exact star_col_dotProduct_eq_gramSchmidtR A i j
  · intro l hl
    have hlk := hl.trans i.isLt
    simp only [dif_pos hlk]
    exact (dotProduct_gramSchmidtQ_col A i ⟨l, hlk⟩).trans
      (if_neg (fun h => hl.ne (congrArg Fin.val h).symm))


end Modified

end NLAlib
