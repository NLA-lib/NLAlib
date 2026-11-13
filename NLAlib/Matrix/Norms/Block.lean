/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Matrix.Norms.Compare

/-!
# Norms of block matrices and submatrices

The Frobenius norm is additive in squares over blocks; the spectral norm is subadditive in
squares over rows or columns of blocks, and exactly additive in that sense when the summands have
orthogonal ranges. Submatrices have smaller norms.

## Main results

* `NLAlib.frobNorm_fromRows_sq`, `NLAlib.frobNorm_fromCols_sq`, `NLAlib.frobNorm_fromBlocks_sq`.
* `NLAlib.specNorm_fromRows_sq_le`, `NLAlib.specNorm_fromCols_sq_le`.
* `NLAlib.specNorm_submatrix_le`, `NLAlib.frobNorm_submatrix_le`.
* `NLAlib.frobNorm_le_of_row_eq`: selecting distinct rows and padding with zeros is contractive.
* `NLAlib.specNorm_fromBlocks_zero₁₂_zero₂₁`: a block diagonal matrix has the larger of the two
  spectral norms.
* `NLAlib.specNorm_add_sq_le_of_conjTranspose_mul_eq_zero`: summands with orthogonal ranges.
* `NLAlib.specNorm_dilation`: the Hermitian dilation has the spectral norm of the matrix.
* `NLAlib.dilationCLM`, `NLAlib.dilationCLM_apply`: its continuous real-linear map.
* `NLAlib.frobNorm_blockDiagonal_sq`, `NLAlib.specNorm_blockDiagonal_le`,
  `NLAlib.specNorm_blockDiagonal_const`: block diagonal matrices.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p] [Fintype q]

/-! ### Frobenius norm -/

/-- The squared Frobenius norm is additive over stacked rows:
$$\left\|\begin{bmatrix} \mathbf{A} \\ \mathbf{B} \end{bmatrix}\right\|_{\mathsf{F}}^2
  = \|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{B}\|_{\mathsf{F}}^2\,.$$ -/
theorem frobNorm_fromRows_sq (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    frobNorm (Matrix.fromRows A B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  simp only [frobNorm_sq_eq_sum, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr]

/-- The squared Frobenius norm is additive over adjoined columns:
$\|\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}\|_{\mathsf{F}}^2 =
\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{B}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_fromCols_sq (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    frobNorm (Matrix.fromCols A B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  rw [← frobNorm_transpose, Matrix.transpose_fromCols, frobNorm_fromRows_sq, frobNorm_transpose,
    frobNorm_transpose]

/-- The squared Frobenius norm of a block matrix is the sum over the four blocks:
$$\left\|\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{C} & \mathbf{D} \end{bmatrix}
  \right\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{B}\|_{\mathsf{F}}^2 +
  \|\mathbf{C}\|_{\mathsf{F}}^2 + \|\mathbf{D}\|_{\mathsf{F}}^2\,.$$ -/
theorem frobNorm_fromBlocks_sq (A : Matrix m n 𝕜) (B : Matrix m q 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p q 𝕜) :
    frobNorm (Matrix.fromBlocks A B C D) ^ 2 =
      frobNorm A ^ 2 + frobNorm B ^ 2 + frobNorm C ^ 2 + frobNorm D ^ 2 := by
  rw [← Matrix.fromRows_fromCols_eq_fromBlocks, frobNorm_fromRows_sq, frobNorm_fromCols_sq,
    frobNorm_fromCols_sq]
  ring

private theorem sum_comp_le_sum_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] {e : ι → κ}
    (he : Function.Injective e) {f : κ → ℝ} (hf : ∀ k, 0 ≤ f k) : ∑ i, f (e i) ≤ ∑ k, f k := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := f) he.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hf k

/-- A submatrix selected by injective maps of the row and column indices has Frobenius norm at
most that of the matrix. -/
theorem frobNorm_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) :
    frobNorm (A.submatrix r c) ≤ frobNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
  simp only [Matrix.submatrix_apply]
  calc ∑ i, ∑ j, ‖A (r i) (c j)‖ ^ 2
      ≤ ∑ i, ∑ j, ‖A (r i) j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        sum_comp_le_sum_of_injective hc (f := fun j => ‖A (r i) j‖ ^ 2) fun _ => sq_nonneg _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
        sum_comp_le_sum_of_injective hr (f := fun i => ∑ j, ‖A i j‖ ^ 2) fun _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Selecting distinct rows of a matrix and padding with zero rows cannot increase its
Frobenius norm. The row map need only be injective on the selected rows $s$; outside $s$ the
matrix on the left is zero. This includes shifted and truncated stacks of matrix blocks. -/
theorem frobNorm_le_of_row_eq (A : Matrix m n 𝕜) (B : Matrix l n 𝕜) (s : Finset m)
    (f : m → l) (hf : Set.InjOn f (s : Set m))
    (heq : ∀ i ∈ s, ∀ j, A i j = B (f i) j)
    (hzero : ∀ i ∉ s, ∀ j, A i j = 0) : frobNorm A ≤ frobNorm B := by
  classical
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ i ∈ s, ∑ j, ‖A i j‖ ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        simp only [hzero i hi, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, Finset.sum_const_zero]
    _ = ∑ i ∈ s, ∑ j, ‖B (f i) j‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [heq i hi]
    _ = ∑ i ∈ s.image f, ∑ j, ‖B i j‖ ^ 2 :=
        (Finset.sum_image (s := s) (g := f) (f := fun i => ∑ j, ‖B i j‖ ^ 2) hf).symm
    _ ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **Pythagoras for summands with orthogonal ranges**: if
$\mathbf{A}^{\mathsf{H}}\mathbf{B} = \mathbf{0}$ then
$\|\mathbf{A} + \mathbf{B}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{B}\|_{\mathsf{F}}^2$. [HornJohnson2013, §5.1]. -/
theorem frobNorm_add_sq_of_conjTranspose_mul_eq_zero {A B : Matrix m n 𝕜} (h : Aᴴ * B = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  refine frobNorm_add_sq_of_frobInner_eq_zero ?_
  rw [frobInner_eq_re_trace, h, Matrix.trace_zero, map_zero]

/-- Pythagoras for summands with orthogonal row spaces: if
$\mathbf{A}\mathbf{B}^{\mathsf{H}} = \mathbf{0}$ then
$\|\mathbf{A} + \mathbf{B}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{B}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_add_sq_of_mul_conjTranspose_eq_zero {A B : Matrix m n 𝕜} (h : A * Bᴴ = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  refine frobNorm_add_sq_of_frobInner_eq_zero ?_
  rw [frobInner_eq_re_trace_mul_conjTranspose, h, Matrix.trace_zero, map_zero]

/-! ### Spectral norm -/

/-- A submatrix selected by injective maps of the row and column indices has spectral norm at
most that of the matrix. -/
theorem specNorm_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) :
    specNorm (A.submatrix r c) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  have hv : A.submatrix r c *ᵥ x = (A *ᵥ Function.extend c x 0) ∘ r := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
    refine Fintype.sum_of_injective c hc _ _ (fun k hk => ?_) fun j => ?_
    · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply, mul_zero]
    · rw [hc.extend_apply]
  rw [hv, ← EuclideanSpace.norm_toLp_extend_zero hc x]
  exact (EuclideanSpace.norm_toLp_comp_le_of_injective hr _).trans (norm_toLp_mulVec_le A _)

/-- The squared spectral norm of stacked rows is at most the sum of the squares:
$$\left\|\begin{bmatrix} \mathbf{A} \\ \mathbf{B} \end{bmatrix}\right\|_2^2 \le \|\mathbf{A}\|_2^2 +
\|\mathbf{B}\|_2^2\,.$$ -/
theorem specNorm_fromRows_sq_le (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm (Matrix.fromRows A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  rw [← specNorm_conjTranspose_mul_self (Matrix.fromRows A B),
    ← specNorm_conjTranspose_mul_self A, ← specNorm_conjTranspose_mul_self B,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  exact specNorm_add_le _ _

/-- The squared spectral norm of adjoined columns is at most the sum of the squares:
$\|\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}\|_2^2 \le \|\mathbf{A}\|_2^2 +
\|\mathbf{B}\|_2^2$. -/
theorem specNorm_fromCols_sq_le (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm (Matrix.fromCols A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  rw [← specNorm_mul_conjTranspose_self (Matrix.fromCols A B),
    ← specNorm_mul_conjTranspose_self A, ← specNorm_mul_conjTranspose_self B,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
  exact specNorm_add_le _ _

/-- A block of rows has spectral norm at most that of the stacked matrix:
$\|\mathbf{A}\|_2 \le \left\|\begin{bmatrix} \mathbf{A} \\ \mathbf{B} \end{bmatrix}\right\|_2$. -/
theorem specNorm_le_specNorm_fromRows_left (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm A ≤ specNorm (Matrix.fromRows A B) :=
  specNorm_submatrix_le (Matrix.fromRows A B) (r := Sum.inl) (c := id) Sum.inl_injective
    Function.injective_id

/-- A block of rows has spectral norm at most that of the stacked matrix:
$\|\mathbf{B}\|_2 \le \left\|\begin{bmatrix} \mathbf{A} \\ \mathbf{B} \end{bmatrix}\right\|_2$. -/
theorem specNorm_le_specNorm_fromRows_right (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm B ≤ specNorm (Matrix.fromRows A B) :=
  specNorm_submatrix_le (Matrix.fromRows A B) (r := Sum.inr) (c := id) Sum.inr_injective
    Function.injective_id

/-- A block of columns has spectral norm at most that of the adjoined matrix:
$\|\mathbf{A}\|_2 \le \|\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}\|_2$. -/
theorem specNorm_le_specNorm_fromCols_left (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm A ≤ specNorm (Matrix.fromCols A B) :=
  specNorm_submatrix_le (Matrix.fromCols A B) (r := id) (c := Sum.inl) Function.injective_id
    Sum.inl_injective

/-- A block of columns has spectral norm at most that of the adjoined matrix:
$\|\mathbf{B}\|_2 \le \|\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}\|_2$. -/
theorem specNorm_le_specNorm_fromCols_right (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm B ≤ specNorm (Matrix.fromCols A B) :=
  specNorm_submatrix_le (Matrix.fromCols A B) (r := id) (c := Sum.inr) Function.injective_id
    Sum.inr_injective

/-- Stacking zero rows under a matrix does not change its spectral norm:
$\left\|\begin{bmatrix} \mathbf{A} \\ \mathbf{0} \end{bmatrix}\right\|_2 = \|\mathbf{A}\|_2$. -/
@[simp]
theorem specNorm_fromRows_zero (A : Matrix m n 𝕜) :
    specNorm (Matrix.fromRows A (0 : Matrix p n 𝕜)) = specNorm A := by
  refine le_antisymm ?_ (specNorm_le_specNorm_fromRows_left A 0)
  refine (sq_le_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).1 ?_
  have h := specNorm_fromRows_sq_le A (0 : Matrix p n 𝕜)
  rwa [specNorm_zero, zero_pow two_ne_zero, add_zero] at h

/-- Adjoining zero columns to a matrix does not change its spectral norm:
$\|\begin{bmatrix} \mathbf{A} & \mathbf{0} \end{bmatrix}\|_2 = \|\mathbf{A}\|_2$. -/
@[simp]
theorem specNorm_fromCols_zero (A : Matrix m n 𝕜) :
    specNorm (Matrix.fromCols A (0 : Matrix m p 𝕜)) = specNorm A := by
  refine le_antisymm ?_ (specNorm_le_specNorm_fromCols_left A 0)
  refine (sq_le_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).1 ?_
  have h := specNorm_fromCols_sq_le A (0 : Matrix m p 𝕜)
  rwa [specNorm_zero, zero_pow two_ne_zero, add_zero] at h

/-- The spectral norm of a block diagonal matrix is the larger of the spectral norms of the
blocks:
$$\left\|\begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{D} \end{bmatrix}\right\|_2
  = \max\bigl(\|\mathbf{A}\|_2, \|\mathbf{D}\|_2\bigr)\,.$$ -/
theorem specNorm_fromBlocks_zero₁₂_zero₂₁ (A : Matrix m n 𝕜) (D : Matrix p q 𝕜) :
    specNorm (Matrix.fromBlocks A 0 0 D) = max (specNorm A) (specNorm D) := by
  have hM : 0 ≤ max (specNorm A) (specNorm D) := le_max_of_le_left (specNorm_nonneg A)
  refine le_antisymm ((specNorm_le_iff hM).2 fun x => ?_) (max_le ?_ ?_)
  · have hA : ‖WithLp.toLp 2 (A *ᵥ (x ∘ Sum.inl))‖ ≤
        max (specNorm A) (specNorm D) * ‖WithLp.toLp 2 (x ∘ Sum.inl)‖ :=
      (norm_toLp_mulVec_le A _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hD : ‖WithLp.toLp 2 (D *ᵥ (x ∘ Sum.inr))‖ ≤
        max (specNorm A) (specNorm D) * ‖WithLp.toLp 2 (x ∘ Sum.inr)‖ :=
      (norm_toLp_mulVec_le D _).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hx : ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 (x ∘ Sum.inl)‖ ^ 2 + ‖WithLp.toLp 2 (x ∘ Sum.inr)‖ ^ 2 := by
      rw [← EuclideanSpace.norm_toLp_sumElim_sq, Sum.elim_comp_inl_inr]
    refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 ?_
    rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      EuclideanSpace.norm_toLp_sumElim_sq, mul_pow, hx, mul_add, ← mul_pow, ← mul_pow]
    gcongr
  · exact specNorm_submatrix_le (Matrix.fromBlocks A 0 0 D) (r := Sum.inl) (c := Sum.inl)
      Sum.inl_injective Sum.inl_injective
  · exact specNorm_submatrix_le (Matrix.fromBlocks A 0 0 D) (r := Sum.inr) (c := Sum.inr)
      Sum.inr_injective Sum.inr_injective

/-- For summands with orthogonal row spaces ($\mathbf{X}\mathbf{Y}^{\mathsf{H}} = \mathbf{0}$),
the squared spectral norm of the sum is at most the sum of the squares:
$\|\mathbf{X} + \mathbf{Y}\|_2^2 \le \|\mathbf{X}\|_2^2 + \|\mathbf{Y}\|_2^2$. -/
theorem specNorm_add_sq_le_of_mul_conjTranspose_eq_zero {X Y : Matrix m n 𝕜} (h : X * Yᴴ = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  have h' : Y * Xᴴ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Y * Xᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h, Matrix.conjTranspose_zero]
  have hG : (X + Y) * (X + Y)ᴴ = X * Xᴴ + Y * Yᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h',
      add_zero, zero_add]
  rw [← specNorm_mul_conjTranspose_self (X + Y), ← specNorm_mul_conjTranspose_self X,
    ← specNorm_mul_conjTranspose_self Y, hG]
  exact specNorm_add_le _ _

/-- For summands with orthogonal ranges ($\mathbf{X}^{\mathsf{H}}\mathbf{Y} = \mathbf{0}$), the
squared spectral norm of the sum is at most the sum of the squares:
$\|\mathbf{X} + \mathbf{Y}\|_2^2 \le \|\mathbf{X}\|_2^2 + \|\mathbf{Y}\|_2^2$. -/
theorem specNorm_add_sq_le_of_conjTranspose_mul_eq_zero {X Y : Matrix m n 𝕜} (h : Xᴴ * Y = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  have h' : Xᴴ * Yᴴᴴ = 0 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact h
  have h2 := specNorm_add_sq_le_of_mul_conjTranspose_eq_zero h'
  rwa [← Matrix.conjTranspose_add, specNorm_conjTranspose, specNorm_conjTranspose,
    specNorm_conjTranspose] at h2

/-! ### The Hermitian dilation -/

open scoped Matrix.Norms.L2Operator in
/-- The Hermitian dilation as a continuous real-linear map on finite rectangular matrices,
through which integrals, $L^p$ membership and measurability pass to `dilation`. It is only
real-linear: the lower-left block $\mathbf{A}^{\mathsf{H}}$ is conjugate-linear in
$\mathbf{A}$. -/
noncomputable def dilationCLM (m : Type*) [Fintype m] :
    Matrix m n 𝕜 →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := dilation
      map_add' := dilation_add
      map_smul' := dilation_smul_real }

open scoped Matrix.Norms.L2Operator in
/-- The continuous real-linear dilation map applies `dilation` to its matrix argument. -/
@[simp]
theorem dilationCLM_apply (A : Matrix m n 𝕜) : dilationCLM m A = dilation A :=
  rfl

/-- The Hermitian dilation has the spectral norm of the matrix:
$\left\|\begin{bmatrix} \mathbf{0} & \mathbf{A} \\ \mathbf{A}^{\mathsf{H}} & \mathbf{0}
\end{bmatrix}\right\|_2 = \|\mathbf{A}\|_2$. [Tropp2015, (2.1.28)]. -/
@[simp]
theorem specNorm_dilation (A : Matrix m n 𝕜) : specNorm (dilation A) = specNorm A := by
  refine (sq_eq_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).1 ?_
  rw [← specNorm_conjTranspose_mul_self (dilation A), conjTranspose_dilation,
    dilation_mul_dilation, specNorm_fromBlocks_zero₁₂_zero₂₁, specNorm_mul_conjTranspose_self,
    specNorm_conjTranspose_mul_self, max_self]

/-- The squared Frobenius norm of the Hermitian dilation is twice that of the matrix:
$\left\|\begin{bmatrix} \mathbf{0} & \mathbf{A} \\ \mathbf{A}^{\mathsf{H}} & \mathbf{0}
\end{bmatrix}\right\|_{\mathsf{F}}^2 = 2 \|\mathbf{A}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_dilation_sq (A : Matrix m n 𝕜) :
    frobNorm (dilation A) ^ 2 = 2 * frobNorm A ^ 2 := by
  rw [dilation_def, frobNorm_fromBlocks_sq]
  simp only [frobNorm_zero, frobNorm_conjTranspose]
  ring

/-! ### Block diagonal matrices -/

section BlockDiagonal

variable {o : Type*} [Fintype o] [DecidableEq o]

/-- The squared Frobenius norm of a block diagonal matrix is the sum over the blocks:
$\|\operatorname{diag}(\mathbf{M}_1, \dots, \mathbf{M}_k)\|_{\mathsf{F}}^2 =
\sum_i \|\mathbf{M}_i\|_{\mathsf{F}}^2$. -/
theorem frobNorm_blockDiagonal_sq (M : o → Matrix m n 𝕜) :
    frobNorm (Matrix.blockDiagonal M) ^ 2 = ∑ k, frobNorm (M k) ^ 2 := by
  simp only [frobNorm_sq_eq_sum, Fintype.sum_prod_type_right, Matrix.blockDiagonal_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp [apply_ite (fun z : 𝕜 => ‖z‖ ^ 2)]

/-- $k$ copies of one block: $\|\mathbf{I}_k \otimes \mathbf{B}\|_{\mathsf{F}}^2 =
k\,\|\mathbf{B}\|_{\mathsf{F}}^2$, for the block diagonal matrix with every block
$\mathbf{B}$. -/
theorem frobNorm_blockDiagonal_const_sq (B : Matrix m n 𝕜) :
    frobNorm (Matrix.blockDiagonal fun _ : o => B) ^ 2 = Fintype.card o * frobNorm B ^ 2 := by
  rw [frobNorm_blockDiagonal_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Fintype m] in
/-- A block diagonal matrix acts blockwise: the block $k$ of
$\operatorname{diag}(\mathbf{M}_1, \dots)\mathbf{x}$ is $\mathbf{M}_k\mathbf{x}_k$. -/
private theorem blockDiagonal_mulVec_apply (M : o → Matrix m n 𝕜) (x : n × o → 𝕜) (i : m)
    (k : o) : (Matrix.blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun j => x (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.blockDiagonal_apply,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- The spectral norm of a block diagonal matrix is at most any common bound $c \ge 0$ on the
spectral norms of its blocks. -/
theorem specNorm_blockDiagonal_le (M : o → Matrix m n 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k, specNorm (M k) ≤ c) : specNorm (Matrix.blockDiagonal M) ≤ c := by
  refine (specNorm_le_iff hc).2 fun x => ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := pow_le_pow_left₀ (norm_nonneg _)
    ((norm_toLp_mulVec_le (M k) fun j => x (j, k)).trans
      (mul_le_mul_of_nonneg_right (h k) (norm_nonneg _))) 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h1
  simpa only [PiLp.toLp_apply, blockDiagonal_mulVec_apply] using h1

/-- Each block has spectral norm at most that of the block diagonal matrix. -/
theorem specNorm_le_specNorm_blockDiagonal (M : o → Matrix m n 𝕜) (k : o) :
    specNorm (M k) ≤ specNorm (Matrix.blockDiagonal M) := by
  have h := specNorm_submatrix_le (Matrix.blockDiagonal M) (r := fun i : m => (i, k))
    (c := fun j : n => (j, k)) (fun _ _ h => (Prod.mk.inj h).1) (fun _ _ h => (Prod.mk.inj h).1)
  convert h using 2
  ext i j
  simp

/-- $k \ge 1$ copies of one block: $\|\mathbf{I}_k \otimes \mathbf{B}\|_2 = \|\mathbf{B}\|_2$,
for the block diagonal matrix with every block $\mathbf{B}$. -/
theorem specNorm_blockDiagonal_const [Nonempty o] (B : Matrix m n 𝕜) :
    specNorm (Matrix.blockDiagonal fun _ : o => B) = specNorm B :=
  le_antisymm (specNorm_blockDiagonal_le _ (specNorm_nonneg B) fun _ => le_rfl)
    (specNorm_le_specNorm_blockDiagonal (fun _ : o => B) (Classical.arbitrary o))

end BlockDiagonal

end NLAlib
