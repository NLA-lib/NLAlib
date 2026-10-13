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

The Gram–Schmidt process applied to the columns of `A`, in the order of the column index, gives
`NLAlib.gramSchmidtQ A`, whose nonzero columns are orthonormal, and the upper triangular
`NLAlib.gramSchmidtR A = Qᴴ A` with nonnegative diagonal, with `A = Q R` always. A column of `Q`
vanishes exactly when the corresponding column of `A` depends on the earlier ones; for `A` of full
column rank this is the QR factorization with positive diagonal.

The process is Mathlib's `InnerProductSpace.gramSchmidtNormed` on the columns.

## Main definitions

* `NLAlib.gramSchmidtQ`, `NLAlib.gramSchmidtR`: the two factors.

## Main results

* `NLAlib.gramSchmidtQ_mul_gramSchmidtR`: `Q R = A`.
* `NLAlib.isUpperTriangular_gramSchmidtR`, `NLAlib.gramSchmidtR_apply_self_nonneg`.
* `NLAlib.gramSchmidtR_apply_self_smul_col`: the classical recursion.
* `NLAlib.isQR_gramSchmidt`: the QR factorization of a matrix of full column rank.
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

/-- The matrix of Gram–Schmidt vectors of the columns of `A`: column `j` is the normalised
component of column `j` of `A` orthogonal to the earlier columns, or zero if there is none.
Port of `NLAlib.gramSchmidtQ`, there by an explicit recursion over `ℝ`. -/
noncomputable def gramSchmidtQ (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  Matrix.of fun i j =>
    InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j i

/-- The triangular factor of the Gram–Schmidt process, `R = Qᴴ A`.
Port of `NLAlib.gramSchmidtR`. -/
noncomputable def gramSchmidtR (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (gramSchmidtQ A)ᴴ * A

/-- The columns of `A` as vectors of the Euclidean space. -/
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

/-- The triangular factor is upper triangular. Port of `NLAlib.isUpperTriangular_gramSchmidtR`. -/
theorem isUpperTriangular_gramSchmidtR (A : Matrix m n 𝕜) :
    (gramSchmidtR A).IsUpperTriangular := by
  intro k j hjk
  have hjk' : j < k := hjk
  rw [gramSchmidtR_apply, InnerProductSpace.gramSchmidtNormed, inner_smul_left,
    InnerProductSpace.gramSchmidt_inv_triangular 𝕜 _ hjk', mul_zero]

/-- The diagonal of the triangular factor is nonnegative.
Port of `NLAlib.gramSchmidtR_apply_self_nonneg`. -/
theorem gramSchmidtR_apply_self_nonneg (A : Matrix m n 𝕜) (j : n) : 0 ≤ gramSchmidtR A j j := by
  rw [gramSchmidtR_apply_self]
  exact RCLike.ofReal_nonneg.mpr (norm_nonneg _)

/-- **The classical Gram–Schmidt recursion**: `r_jj q_j = a_j - ∑_{k < j} r_kj q_k`.
Port of `NLAlib.gramSchmidtResidual_eq_sum` and `NLAlib.norm_smul_gramSchmidtCol`. -/
theorem gramSchmidtR_apply_self_smul_col (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j • (gramSchmidtQ A).col j =
      A.col j - ∑ k ∈ Finset.Iio j, gramSchmidtR A k j • (gramSchmidtQ A).col k := by
  have h := congrArg WithLp.ofLp (norm_gramSchmidt_smul_gramSchmidtNormed (𝕜 := 𝕜) (colVec A) j)
  rw [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_sum] at h
  rw [gramSchmidtR_apply_self]
  simp only [gramSchmidtR_apply]
  exact h

/-- **Gram–Schmidt factors the matrix**: `Q R = A`, with no rank assumption.
Port of `NLAlib.gramSchmidtQ_mul_gramSchmidtR`. -/
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

/-- The Gram matrix of the Gram–Schmidt vectors is diagonal with entries zero or one.
Port of `NLAlib.transpose_gramSchmidtQ_mul_self`. -/
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

/-- A diagonal entry of `R` vanishes exactly when the column of `A` depends on the earlier ones.
Port of `NLAlib.gramSchmidtResidual_eq_zero_iff`. -/
theorem gramSchmidtR_apply_self_eq_zero_iff (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j = 0 ↔ A.col j ∈ Submodule.span 𝕜 (A.col '' Set.Iio j) := by
  rw [gramSchmidtR_apply_self, RCLike.ofReal_eq_zero, norm_eq_zero, gramSchmidt_eq_zero_iff]
  exact toLp_mem_span_image_iff A.col (Set.Iio j) (A.col j)

/-- The diagonal of `R` has no zero exactly when `A` has full column rank.
Port of `NLAlib.gramSchmidtSucceeds_iff_linearIndependent`. -/
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

/-- The first Gram–Schmidt vectors span the same subspace as the first columns of `A`.
Port of `NLAlib.span_gramSchmidtCol_image_Iic`. -/
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

/-- For `A` of full column rank the Gram–Schmidt vectors are orthonormal.
Port of `NLAlib.hasOrthonormalCols_gramSchmidtQ`. -/
theorem hasOrthonormalCols_gramSchmidtQ [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : HasOrthonormalCols (gramSchmidtQ A) := by
  rw [HasOrthonormalCols, conjTranspose_gramSchmidtQ_mul_self, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun j =>
    if_neg ((forall_gramSchmidtR_apply_self_ne_zero_iff A).mpr hA j))

/-- **Gram–Schmidt computes the QR factorization** of a matrix of full column rank.
[TrefethenBau1997, Lecture 7]. Port of `NLAlib.isQR_gramSchmidt`. -/
theorem isQR_gramSchmidt [DecidableEq n] {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    IsQR A (gramSchmidtQ A) (gramSchmidtR A) := by
  exact ⟨(gramSchmidtQ_mul_gramSchmidtR A).symm, hasOrthonormalCols_gramSchmidtQ hA,
    isUpperTriangular_gramSchmidtR A⟩

/-- For `A` of full column rank the diagonal of the triangular factor is positive.
Port of `NLAlib.gramSchmidtR_apply_self_pos`. -/
theorem gramSchmidtR_apply_self_pos {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    (j : n) : 0 < gramSchmidtR A j j := by
  exact (gramSchmidtR_apply_self_nonneg A j).lt_of_ne'
    ((forall_gramSchmidtR_apply_self_ne_zero_iff A).mpr hA j)

/-- Gram–Schmidt commutes with a unitary factor on the left: `Q(W A) = W Q(A)`.
Port of `NLAlib.qrNormalizedArray_orthogonal_mul`. -/
theorem gramSchmidtQ_mul_left {l : Type*} [Fintype l] [DecidableEq m] {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) :
    gramSchmidtQ (W * A) = W * gramSchmidtQ A := by
  let T : EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 l :=
    { toLinearMap := Matrix.toEuclideanLin W
      norm_map' := fun x => hW.norm_toLp_mulVec x.ofLp }
  ext i j
  change (InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => T (colVec A k)) j) i = _
  rw [gramSchmidtNormed_map]
  rfl

/-- The triangular factor is unchanged by a unitary factor on the left: `R(W A) = R(A)`.
Port of `NLAlib.canonicalQRUpper_orthogonal_mul`. -/
theorem gramSchmidtR_mul_left {l : Type*} [Fintype l] [DecidableEq m] {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) :
    gramSchmidtR (W * A) = gramSchmidtR A := by
  rw [gramSchmidtR, gramSchmidtQ_mul_left hW, hW.conjTranspose_mul_mul, gramSchmidtR]

end NLAlib
