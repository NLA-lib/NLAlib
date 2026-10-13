/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Inequalities.Determinant
public import NLAlib.Matrix.Norms.Loewner

/-!
# Gaussian elimination

One step of elimination at a diagonal pivot `t` replaces `A` by
`A - (A t t)⁻¹ • (column t of A) (row t of A)`, which clears row and column `t`. This is the
operation behind the LU and Cholesky factorizations and their pivoted and randomly pivoted
variants. The step is defined for any index type over any field; when the pivot is zero it does
nothing. On the complement of the pivot it is the Schur complement of the pivot entry.

Elimination in the natural order, `NLAlib.gaussState`, is in
`NLAlib.Matrix.Factorizations.GaussState`. Elimination of a positive semidefinite matrix along a
list of pivots (the Nyström residual, randomly pivoted Cholesky) is in
`NLAlib.Matrix.Factorizations.Nystrom`.

## Main definitions

* `NLAlib.eliminationStep`: one elimination step at a diagonal pivot.

## Main results

* `NLAlib.rank_eliminationStep_add_one`: a step at a nonzero pivot lowers the rank by one.
* `NLAlib.det_eq_apply_self_mul_det_eliminationStep`: the determinant through a step.
* `Matrix.PosSemidef.eliminationStep`, `Matrix.PosSemidef.eliminationStep_le`.
* `Matrix.IsHermitian.posDef_iff_eliminationStep`: positive definiteness through a step.
* `Matrix.PosSemidef.foldl_eliminationStep`: elimination along a list of pivots keeps a positive
  semidefinite matrix positive semidefinite.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {K : Type*} [Field K] {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-! ### One elimination step -/

/-- **One step of elimination** at the diagonal pivot `t`: subtract from `A` the rank-one matrix
`(A t t)⁻¹ • (column t) (row t)`. If the pivot `A t t` is zero the step returns `A`.
Port of `NLAlib.eliminationStep`. -/
def eliminationStep (A : Matrix n n K) (t : n) : Matrix n n K :=
  Matrix.of fun i j => A i j - (A t t)⁻¹ * (A i t * A t j)

/-- Entries of an elimination step. Port of `NLAlib.eliminationStep_apply`. -/
@[simp]
theorem eliminationStep_apply (A : Matrix n n K) (t i j : n) :
    eliminationStep A t i j = A i j - (A t t)⁻¹ * (A i t * A t j) :=
  rfl

/-- A step on the zero matrix. Port of `NLAlib.eliminationStep_zero`. -/
@[simp]
theorem eliminationStep_zero (t : n) : eliminationStep (0 : Matrix n n K) t = 0 := by
  ext i j
  simp

/-- A step at a zero pivot does nothing.
Port of `NLAlib.eliminationStep_eq_self_of_apply_self_eq_zero`. -/
theorem eliminationStep_eq_self_of_apply_self_eq_zero {A : Matrix n n K} {t : n}
    (ht : A t t = 0) : eliminationStep A t = A := by
  ext i j
  simp [ht]

/-- A step at a nonzero pivot clears the pivot row.
Port of `NLAlib.eliminationStep_apply_pivot_left_of_ne_zero`. -/
theorem eliminationStep_apply_pivot_left {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) (j : n) :
    eliminationStep A t t j = 0 := by
  rw [eliminationStep_apply, ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- A step at a nonzero pivot clears the pivot column.
Port of `NLAlib.eliminationStep_apply_pivot_right_of_ne_zero`. -/
theorem eliminationStep_apply_pivot_right {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) (i : n) :
    eliminationStep A t i t = 0 := by
  rw [eliminationStep_apply, mul_comm (A i t), ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- A zero row stays zero. Port of `NLAlib.eliminationStep_apply_eq_zero_of_row`. -/
theorem eliminationStep_apply_eq_zero_of_row {A : Matrix n n K} {u : n} (hu : ∀ j, A u j = 0)
    (t j : n) : eliminationStep A t u j = 0 := by
  simp [hu]

/-- A zero column stays zero. Port of `NLAlib.eliminationStep_apply_eq_zero_of_col`. -/
theorem eliminationStep_apply_eq_zero_of_col {A : Matrix n n K} {u : n} (hu : ∀ i, A i u = 0)
    (t i : n) : eliminationStep A t i u = 0 := by
  simp [hu]

/-- Elimination commutes with the transpose. -/
theorem eliminationStep_transpose (A : Matrix n n K) (t : n) :
    eliminationStep Aᵀ t = (eliminationStep A t)ᵀ := by
  ext i j
  simp only [eliminationStep_apply, Matrix.transpose_apply, mul_comm (A t i)]

/-- Elimination commutes with relabelling. -/
theorem eliminationStep_submatrix (A : Matrix n n K) (e : m → n) (t : m) :
    eliminationStep (A.submatrix e e) t = (eliminationStep A (e t)).submatrix e e := by
  ext i j
  simp only [eliminationStep_apply, Matrix.submatrix_apply]

/-- **The step as a rank-one update**: `A - (A t t)⁻¹ • (column t) (row t)`, in matrix form. -/
theorem eliminationStep_eq_sub_smul_vecMulVec (A : Matrix n n K) (t : n) :
    eliminationStep A t = A - (A t t)⁻¹ • Matrix.vecMulVec (fun i => A i t) (A t) := by
  ext i j
  simp only [eliminationStep_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]

section Fintype

variable [Fintype n] [DecidableEq n]

/-- The action of an elimination step on a vector.
Port of `NLAlib.eliminationStep_mulVec_eq`. -/
theorem eliminationStep_mulVec (A : Matrix n n K) (t : n) (x : n → K) :
    eliminationStep A t *ᵥ x = A *ᵥ (x - ((A *ᵥ x) t / A t t) • Pi.single t 1) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext j
  simp only [Matrix.mulVec, dotProduct, eliminationStep_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply, sub_mul, Finset.sum_sub_distrib, div_eq_mul_inv]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A step at a nonzero pivot adds the pivot coordinate line to the kernel. -/
private theorem ker_eliminationStep_eq_sup_span_singleton {A : Matrix n n K} {t : n}
    (ht : A t t ≠ 0) :
    LinearMap.ker (eliminationStep A t).mulVecLin =
      LinearMap.ker A.mulVecLin ⊔ Submodule.span K {Pi.single t (1 : K)} := by
  apply le_antisymm
  · intro x hx
    have hy : x - ((A *ᵥ x) t / A t t) • Pi.single t (1 : K) ∈ LinearMap.ker A.mulVecLin := by
      change A *ᵥ (x - ((A *ᵥ x) t / A t t) • Pi.single t (1 : K)) = 0
      rw [← eliminationStep_mulVec]
      exact hx
    have he : ((A *ᵥ x) t / A t t) • Pi.single t (1 : K) ∈
        Submodule.span K {Pi.single t (1 : K)} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.mem_sup.mpr ⟨_, hy, _, he, sub_add_cancel _ _⟩
  · refine sup_le (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    · change A *ᵥ x = 0 at hx
      change eliminationStep A t *ᵥ x = 0
      rw [eliminationStep_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, Pi.zero_apply,
        zero_div, zero_smul, sub_zero]
    · change eliminationStep A t *ᵥ Pi.single t 1 = 0
      rw [Matrix.mulVec_single_one]
      ext j
      exact eliminationStep_apply_pivot_right ht j

omit [DecidableEq n] in
/-- **A step at a nonzero pivot lowers the rank by one** (Wedderburn's rank reduction).
Port of `NLAlib.rank_eliminationStep_add_one_eq`. -/
theorem rank_eliminationStep_add_one {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    (eliminationStep A t).rank + 1 = A.rank := by
  classical
  have he : Pi.single t (1 : K) ∉ LinearMap.ker A.mulVecLin := by
    intro hz
    have hh : (A *ᵥ Pi.single t (1 : K)) t = 0 := congrFun hz t
    rw [Matrix.mulVec_single_one] at hh
    exact ht hh
  have hker := Submodule.finrank_sup_span_singleton he
  rw [← ker_eliminationStep_eq_sup_span_singleton ht] at hker
  have hA := A.finrank_ker_mulVecLin_add_rank
  have hS := (eliminationStep A t).finrank_ker_mulVecLin_add_rank
  omega

/-- **The determinant through an elimination step**: `det A` is the pivot times the determinant
of the Schur complement, which is the eliminated matrix on the complement of the pivot.
Port of `NLAlib.det_eq_mul_det_pivotSchur`, there for the first pivot of a matrix on `Fin`. -/
theorem det_eq_apply_self_mul_det_eliminationStep {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    A.det = A t t *
      ((eliminationStep A t).submatrix (Subtype.val : {i // i ≠ t} → n) Subtype.val).det := by
  let c : n → K := fun i => if i = t then 0 else -((A t t)⁻¹ * A i t)
  let B : Matrix n n K := Matrix.of fun i j => A i j + c i * A t j
  have hB : B.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c t (if_pos rfl) fun i j => rfl
  have hcol : ∀ i, ¬ i = t → ∀ j, j = t → B i j = 0 := by
    intro i hi j hj
    subst hj
    simp only [B, c, Matrix.of_apply, if_neg hi]
    field_simp
    ring
  rw [← hB, Matrix.twoBlockTriangular_det B (fun i => i = t) hcol]
  congr 1
  · convert Matrix.det_eq_elem_of_subsingleton (B.toSquareBlockProp fun i => i = t) ⟨t, rfl⟩
    simp only [B, c, Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.of_apply, if_true,
      zero_mul, add_zero]
  · congr 1
    ext i j
    simp only [B, c, Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.of_apply,
      if_neg i.2, Matrix.submatrix_apply, eliminationStep_apply]
    ring

omit [DecidableEq n] in
/-- The trace after an elimination step. -/
theorem trace_eliminationStep (A : Matrix n n K) (t : n) :
    (eliminationStep A t).trace = A.trace - (A t t)⁻¹ * ∑ i, A i t * A t i := by
  simp only [Matrix.trace, Matrix.diag_apply, eliminationStep_apply, Finset.sum_sub_distrib,
    Finset.mul_sum]

end Fintype

/-! ### Elimination on Hermitian and positive semidefinite matrices -/

/-- Elimination preserves Hermitian matrices. Port of `NLAlib.isHermitian_eliminationStep`. -/
theorem _root_.Matrix.IsHermitian.eliminationStep {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (t : n) : (eliminationStep A t).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [eliminationStep_apply, star_sub, star_mul', star_inv₀, hA.apply]
  ring

/-- For a positive semidefinite matrix a step clears the pivot row, whether or not the pivot is
zero. Port of `NLAlib.eliminationStep_apply_pivot_left`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_apply_pivot_left {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (t j : n) : eliminationStep A t t j = 0 := by
  by_cases h : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero h]
    exact congrFun (hA.row_eq_zero_of_apply_self_eq_zero h) j
  · exact NLAlib.eliminationStep_apply_pivot_left h j

/-- For a positive semidefinite matrix a step clears the pivot column, whether or not the pivot
is zero. Port of `NLAlib.eliminationStep_apply_pivot_right`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_apply_pivot_right {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (t i : n) : eliminationStep A t i t = 0 := by
  by_cases h : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero h]
    exact congrFun (hA.col_eq_zero_of_apply_self_eq_zero h) i
  · exact NLAlib.eliminationStep_apply_pivot_right h i

section Finite

variable [Finite n]

/-- **Elimination preserves positive semidefinite matrices.**
Port of `NLAlib.posSemidef_eliminationStep`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (t : n) : (eliminationStep A t).PosSemidef := by
  classical
  cases nonempty_fintype n
  by_cases ht : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero ht]
    exact hA
  have hS := Matrix.IsHermitian.eliminationStep hA.isHermitian t
  have hAM : A * (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) =
      NLAlib.eliminationStep A t := by
    rw [eliminationStep_eq_sub_smul_vecMulVec, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_vecMulVec, Matrix.mulVec_single_one]
    rfl
  have hMA : (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t))ᴴ * A =
      NLAlib.eliminationStep A t := by
    have h := congrArg Matrix.conjTranspose hAM
    rwa [Matrix.conjTranspose_mul, hA.isHermitian.eq, hS.eq] at h
  have hcol : (NLAlib.eliminationStep A t).col t = 0 :=
    funext fun j => NLAlib.eliminationStep_apply_pivot_right ht j
  have hSM : NLAlib.eliminationStep A t * (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) =
      NLAlib.eliminationStep A t := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
      Matrix.mulVec_single_one, hcol, Matrix.zero_vecMulVec, smul_zero, sub_zero]
  rw [← hSM, ← hMA]
  exact hA.conjTranspose_mul_mul_same _

/-- Elimination decreases a positive semidefinite matrix in the Loewner order.
Port of `NLAlib.eliminationStep_le`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (t : n) : eliminationStep A t ≤ A := by
  rw [Matrix.le_iff]
  have hd0 : 0 ≤ RCLike.re (A t t) := (RCLike.nonneg_iff.mp hA.diag_nonneg).1
  have hinv : 0 ≤ (A t t)⁻¹ := by
    rw [← hA.isHermitian.coe_re_apply_self t, ← RCLike.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hd0)
  have hrow : A t = star fun i => A i t := funext fun j => (hA.isHermitian.apply t j).symm
  have he : A - eliminationStep A t =
      (A t t)⁻¹ • Matrix.vecMulVec (fun i => A i t) (star fun i => A i t) := by
    rw [eliminationStep_eq_sub_smul_vecMulVec, sub_sub_cancel, ← hrow]
  rw [he]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul hinv

/-- **Positive definiteness through an elimination step**: `A` is positive definite exactly when
the pivot is positive and the Schur complement is positive definite.
Port of `NLAlib.posDef_iff_pivotSchur`, there for the first pivot of a matrix on `Fin`. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_eliminationStep
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : n) :
    A.PosDef ↔ 0 < A t t ∧
      ((eliminationStep A t).submatrix (Subtype.val : {i // i ≠ t} → n) Subtype.val).PosDef := by
  classical
  cases nonempty_fintype n
  let e : {i // i = t} ⊕ {i // ¬ i = t} ≃ n := Equiv.sumCompl fun i => i = t
  let A₁ : Matrix {i // i = t} {i // i = t} 𝕜 := A.submatrix Subtype.val Subtype.val
  let B : Matrix {i // i = t} {i // ¬ i = t} 𝕜 := A.submatrix Subtype.val Subtype.val
  let C : Matrix {i // ¬ i = t} {i // ¬ i = t} 𝕜 := A.submatrix Subtype.val Subtype.val
  have hblock : A.submatrix e e = Matrix.fromBlocks A₁ B Bᴴ C := by
    ext (i | i) (j | j) <;> simp [e, A₁, B, C, hA.apply]
  have hiff : A.PosDef ↔ (A.submatrix e e).PosDef :=
    ⟨fun h => h.submatrix e.injective, fun h => by simpa using h.submatrix e.symm.injective⟩
  have hA₁ : A₁ = Matrix.diagonal fun _ => A t t := by
    ext ⟨i, rfl⟩ ⟨j, rfl⟩
    simp [A₁]
  have hA₁pos : A₁.PosDef ↔ 0 < A t t := by
    rw [hA₁, Matrix.posDef_diagonal_iff]
    exact ⟨fun h => h ⟨t, rfl⟩, fun h _ => h⟩
  have hinv : A₁⁻¹ = Matrix.diagonal fun _ => (A t t)⁻¹ := by
    rw [Matrix.inv_subsingleton]
    congr 1
    funext i
    obtain ⟨i, rfl⟩ := i
    exact Ring.inverse_eq_inv _
  have hS : C - Bᴴ * A₁⁻¹ * B =
      (eliminationStep A t).submatrix (Subtype.val : {i // i ≠ t} → n) Subtype.val := by
    ext i j
    rw [hinv, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_diagonal]
    simp only [B, C, Matrix.conjTranspose_apply, Matrix.submatrix_apply, hA.apply,
      eliminationStep_apply]
    change A i j - A i t * (A t t)⁻¹ * A t j = A i j - (A t t)⁻¹ * (A i t * A t j)
    ring
  rw [hiff, hblock, posDef_fromBlocks_iff, hA₁pos, hS]

/-- Elimination along any list of pivots keeps a positive semidefinite matrix positive
semidefinite. -/
theorem _root_.Matrix.PosSemidef.foldl_eliminationStep {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) : (l.foldl eliminationStep A).PosSemidef := by
  induction l generalizing A with
  | nil => exact hA
  | cons t l ih => exact ih (hA.eliminationStep t)

end Finite

end NLAlib
