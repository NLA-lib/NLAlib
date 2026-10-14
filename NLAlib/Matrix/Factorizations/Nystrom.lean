/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Elimination
public import NLAlib.Matrix.Pseudoinverse.GeneralizedSchur

/-!
# The Nyström residual and elimination along pivots

For a positive semidefinite matrix `A` and a selection `e : p → n` of indices, the Nyström
residual `A - A_{:,e} (A_{e,e})⁺ A_{e,:}` is the largest positive semidefinite matrix below `A`
whose columns at the selected indices vanish. Eliminating along a list of pivots
(`l.foldl eliminationStep A`) produces the residual of the pivot set; this is the residual of a
partial pivoted Cholesky factorization. Averaging one step over a pivot drawn with probability
proportional to the diagonal gives the expected step of randomly pivoted Cholesky.

## Main results

* `Matrix.PosSemidef.sub_submatrix_mul_pinv_mul`, `Matrix.PosSemidef.sub_submatrix_mul_pinv_mul_le`,
  `Matrix.PosSemidef.sub_submatrix_mul_pinv_mul_apply`,
  `Matrix.PosSemidef.le_sub_submatrix_mul_pinv_mul`: the Nyström residual is positive
  semidefinite, below `A`, zero on the selected columns, and the largest such matrix.
* `Matrix.PosSemidef.foldl_eliminationStep_eq_sub`: elimination along pivots is the Nyström
  residual.
* `NLAlib.ker_mulVecLin_le_ker_eliminationStep`: an elimination step does not shrink the kernel.
* `Matrix.PosSemidef.sum_smul_eliminationStep`,
  `Matrix.PosSemidef.sum_mul_re_trace_eliminationStep`: the expected step of randomly pivoted
  Cholesky and its trace.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

section Finite

variable [Finite n]

/-! ### The Nyström residual along a selection -/

omit [Finite n] in
/-- A positive semidefinite matrix bordered by a selection of its rows and columns. -/
private theorem posSemidef_fromBlocks_submatrix {p : Type*} {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (e : p → n) :
    (Matrix.fromBlocks (A.submatrix e e) (A.submatrix e id) (A.submatrix e id)ᴴ A).PosSemidef := by
  have hblock : Matrix.fromBlocks (A.submatrix e e) (A.submatrix e id) (A.submatrix e id)ᴴ A =
      A.submatrix (Sum.elim e id) (Sum.elim e id) := by
    rw [Matrix.conjTranspose_submatrix, hA.isHermitian.eq]
    ext (i | i) (j | j) <;> rfl
  rw [hblock]
  exact hA.submatrix _

/-- **The Nyström residual is positive semidefinite**: for positive semidefinite `A` and a
selection `e`, so is `A - A_{:,e} (A_{e,e})⁺ A_{e,:}`. It is a generalized Schur complement. -/
theorem _root_.Matrix.PosSemidef.sub_submatrix_mul_pinv_mul {p : Type*} [Fintype p]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (e : p → n) :
    (A - A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id).PosSemidef := by
  have h := posSemidef_sub_conjTranspose_mul_pinv_mul_of_posSemidef_fromBlocks
    (posSemidef_fromBlocks_submatrix hA e)
  rwa [Matrix.conjTranspose_submatrix, hA.isHermitian.eq] at h

/-- The Nyström residual of a positive semidefinite matrix is below the matrix in the Loewner
order. -/
theorem _root_.Matrix.PosSemidef.sub_submatrix_mul_pinv_mul_le {p : Type*} [Fintype p]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (e : p → n) :
    A - A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id ≤ A := by
  have hB : (A.submatrix e id)ᴴ = A.submatrix id e := by
    rw [Matrix.conjTranspose_submatrix, hA.isHermitian.eq]
  rw [Matrix.le_iff, sub_sub_cancel, ← hB]
  exact (hA.submatrix e).pinv.conjTranspose_mul_mul_same _

/-- The columns of the Nyström residual at the selected indices vanish. -/
theorem _root_.Matrix.PosSemidef.sub_submatrix_mul_pinv_mul_apply {p : Type*} [Fintype p]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (e : p → n) (i : n) (k : p) :
    (A - A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id) i (e k) = 0 := by
  have h := congrArg Matrix.conjTranspose
    (mul_pinv_mul_eq_of_posSemidef_fromBlocks (posSemidef_fromBlocks_submatrix hA e))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_submatrix,
    hA.isHermitian.eq, (hA.submatrix e).pinv.isHermitian.eq, (hA.submatrix e).isHermitian.eq,
    ← Matrix.mul_assoc] at h
  rw [Matrix.sub_apply, sub_eq_zero]
  exact (congrFun (congrFun h i) k).symm

/-- **The Nyström residual is the largest** positive semidefinite matrix below `A` whose columns
at the selected indices vanish. -/
theorem _root_.Matrix.PosSemidef.le_sub_submatrix_mul_pinv_mul {p : Type*} [Fintype p]
    {A M : Matrix n n 𝕜} (hM : M.PosSemidef) (e : p → n) (hMA : M ≤ A)
    (hMe : ∀ i k, M i (e k) = 0) :
    M ≤ A - A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id := by
  have hMe' : ∀ k i, M (e k) i = 0 := fun k i => by
    rw [← hM.isHermitian.apply, hMe, star_zero]
  have h1 : (A - M).submatrix id e = A.submatrix id e := by
    ext i k
    simp [hMe]
  have h2 : (A - M).submatrix e id = A.submatrix e id := by
    ext k i
    simp [hMe']
  have h3 : (A - M).submatrix e e = A.submatrix e e := by
    ext k k'
    simp [hMe]
  have h := Matrix.PosSemidef.sub_submatrix_mul_pinv_mul (Matrix.le_iff.mp hMA) e
  rw [h1, h2, h3] at h
  rw [Matrix.le_iff]
  convert h using 1
  abel

/-! ### Elimination along a list of pivots -/

omit [Finite n] in
/-- One elimination step is the Nyström residual along a single index. -/
private theorem eliminationStep_eq_sub_submatrix_mul_pinv_mul (A : Matrix n n 𝕜) (t : n) :
    eliminationStep A t =
      A - A.submatrix id (fun _ : Unit => t) *
        pinv (A.submatrix (fun _ : Unit => t) fun _ => t) *
          A.submatrix (fun _ : Unit => t) id := by
  have h : A.submatrix (fun _ : Unit => t) (fun _ => t) = Matrix.diagonal fun _ => A t t := by
    ext i j
    simp
  rw [h, pinv_diagonal]
  ext i j
  simp only [eliminationStep_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Finset.univ_unique, Finset.sum_singleton, id_eq, if_true]
  ring

/-- **Elimination along a list of pivots is the Nyström residual.** For a positive semidefinite
`A` and pivots `l`, the eliminated matrix is `A - A_{:,l} (A_{l,l})⁺ A_{l,:}`: it depends only on
the set of pivots, and repeated pivots do nothing. This is the residual of the partial pivoted
Cholesky factorization. [ChenEtAl2025, §2]. -/
theorem _root_.Matrix.PosSemidef.foldl_eliminationStep_eq_sub
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (l : List n) :
    l.foldl eliminationStep A =
      A - A.submatrix id l.get * pinv (A.submatrix l.get l.get) * A.submatrix l.get id := by
  induction l using List.reverseRecOn with
  | nil =>
    ext i j
    simp
  | append_singleton l t ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    have hR := hA.sub_submatrix_mul_pinv_mul l.get
    have hR' := hA.sub_submatrix_mul_pinv_mul (l ++ [t]).get
    have hRcol : ∀ x ∈ l, ∀ i,
        (A - A.submatrix id l.get * pinv (A.submatrix l.get l.get) * A.submatrix l.get id) i x =
          0 := by
      intro x hx i
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hx
      exact hA.sub_submatrix_mul_pinv_mul_apply _ i k
    have hR'col : ∀ x ∈ l ++ [t], ∀ i,
        (A - A.submatrix id (l ++ [t]).get * pinv (A.submatrix (l ++ [t]).get (l ++ [t]).get) *
          A.submatrix (l ++ [t]).get id) i x = 0 := by
      intro x hx i
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hx
      exact hA.sub_submatrix_mul_pinv_mul_apply _ i k
    apply le_antisymm
    · refine (hR.eliminationStep t).le_sub_submatrix_mul_pinv_mul _
        ((hR.eliminationStep_le t).trans (hA.sub_submatrix_mul_pinv_mul_le _)) fun i k => ?_
      rcases List.mem_append.mp (List.get_mem (l ++ [t]) k) with h | h
      · exact eliminationStep_apply_eq_zero_of_col (fun i => hRcol _ h i) t i
      · rw [List.mem_singleton.mp h]
        exact hR.eliminationStep_apply_pivot_right t i
    · rw [eliminationStep_eq_sub_submatrix_mul_pinv_mul]
      refine hR'.le_sub_submatrix_mul_pinv_mul _ ?_ fun i _ =>
        hR'col t (List.mem_append_right _ (List.mem_singleton_self t)) i
      exact hR'.le_sub_submatrix_mul_pinv_mul _ (hA.sub_submatrix_mul_pinv_mul_le _)
        fun i k => hR'col _ (List.mem_append_left _ (List.get_mem l k)) i

end Finite

/-! ### The kernel under elimination -/

/-- **An elimination step does not shrink the kernel**: `ker A ≤ ker (eliminationStep A t)`, for
any square matrix over a field and any pivot, zero or not. For a positive semidefinite matrix
this is the exhaustion of the column space by the pivots of a partial Cholesky factorization.
[ChenEtAl2025, §2]. Port of `NLAlib.ker_mulVecLin_le_ker_eliminationStep`. -/
theorem ker_mulVecLin_le_ker_eliminationStep {K : Type*} [Field K] [Fintype n]
    (A : Matrix n n K) (t : n) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker (eliminationStep A t).mulVecLin := by
  classical
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
  rw [eliminationStep_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, Pi.zero_apply,
    zero_div, zero_smul, sub_zero]

/-! ### Randomly pivoted Cholesky -/

/-- **The expected step of randomly pivoted Cholesky.** Choosing the pivot `i` with probability
`A i i / tr A` gives, on average, `A - A² / tr A`.
[ChenEtAl2025, §5].
Port of `NLAlib.sum_choleskyPivotProbability_smul_eliminationStep_eq`. -/
theorem _root_.Matrix.PosSemidef.sum_smul_eliminationStep [Fintype n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (ht : RCLike.re A.trace ≠ 0) :
    ∑ i, (RCLike.re (A i i) / RCLike.re A.trace) • eliminationStep A i =
      A - (RCLike.re A.trace)⁻¹ • (A * A) := by
  have htr : ∑ i, RCLike.re (A i i) = RCLike.re A.trace := by
    rw [Matrix.trace, map_sum]
    rfl
  have hc : ∀ i j k, (RCLike.re (A i i) / RCLike.re A.trace) •
      ((A i i)⁻¹ * (A j i * A i k)) = (RCLike.re A.trace)⁻¹ • (A j i * A i k) := by
    intro i j k
    by_cases hi : A i i = 0
    · have hji : A j i = 0 := congrFun (hA.col_eq_zero_of_apply_self_eq_zero hi) j
      rw [hji, zero_mul, mul_zero, smul_zero, smul_zero]
    · have ht' : ((RCLike.re A.trace : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr ht
      rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_div,
        RCLike.ofReal_inv, hA.isHermitian.coe_re_apply_self]
      field_simp
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, eliminationStep_apply, smul_sub,
    Finset.sum_sub_distrib, Matrix.sub_apply, hc, ← Finset.smul_sum, Matrix.mul_apply]
  rw [← Finset.sum_smul, ← Finset.sum_div, htr, div_self ht, one_smul]

/-- **The expected trace after a step of randomly pivoted Cholesky**: choosing the pivot `i`
with probability `A i i / tr A` leaves, on average, the trace `tr A - tr A² / tr A`.
[ChenEtAl2025, §5]. -/
theorem _root_.Matrix.PosSemidef.sum_mul_re_trace_eliminationStep [Fintype n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (ht : RCLike.re A.trace ≠ 0) :
    ∑ i, (RCLike.re (A i i) / RCLike.re A.trace) * RCLike.re (eliminationStep A i).trace =
      RCLike.re A.trace - RCLike.re (A * A).trace / RCLike.re A.trace := by
  have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re M.trace) (hA.sum_smul_eliminationStep ht)
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub, map_sum, map_sub,
    RCLike.smul_re] at h
  rw [h, inv_mul_eq_div]

end NLAlib
