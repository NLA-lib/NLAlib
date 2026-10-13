/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Inequalities.Determinant
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# Gaussian elimination

One step of elimination at a diagonal pivot `t` replaces `A` by
`A - (A t t)⁻¹ • (column t of A) (row t of A)`, which clears row and column `t`. This is the
operation behind the LU and Cholesky factorizations and their pivoted and randomly pivoted
variants. The step is defined for any index type over any field; when the pivot is zero it does
nothing. On the complement of the pivot it is the Schur complement of the pivot entry.

`NLAlib.gaussState A k` is the matrix after eliminating the first `k` pivots of a matrix indexed
by `Fin n`, in the natural order. An algorithm is a total recursion; its breakdown is a zero
pivot, and its correctness theorem assumes nonzero pivots.

## Main definitions

* `NLAlib.eliminationStep`: one elimination step at a diagonal pivot.
* `NLAlib.gaussState`: the sequence of matrices produced by elimination in the natural order.

## Main results

* `NLAlib.rank_eliminationStep_add_one`: a step at a nonzero pivot lowers the rank by one.
* `NLAlib.det_eq_apply_self_mul_det_eliminationStep`: the determinant through a step.
* `Matrix.PosSemidef.eliminationStep`, `Matrix.PosSemidef.eliminationStep_le`.
* `Matrix.IsHermitian.posDef_iff_eliminationStep`: positive definiteness through a step.
* `Matrix.PosSemidef.sum_smul_eliminationStep`: the expected step of randomly pivoted Cholesky.
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
  sorry

/-- A step at a zero pivot does nothing.
Port of `NLAlib.eliminationStep_eq_self_of_apply_self_eq_zero`. -/
theorem eliminationStep_eq_self_of_apply_self_eq_zero {A : Matrix n n K} {t : n}
    (ht : A t t = 0) : eliminationStep A t = A := by
  sorry

/-- A step at a nonzero pivot clears the pivot row.
Port of `NLAlib.eliminationStep_apply_pivot_left_of_ne_zero`. -/
theorem eliminationStep_apply_pivot_left {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) (j : n) :
    eliminationStep A t t j = 0 := by
  sorry

/-- A step at a nonzero pivot clears the pivot column.
Port of `NLAlib.eliminationStep_apply_pivot_right_of_ne_zero`. -/
theorem eliminationStep_apply_pivot_right {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) (i : n) :
    eliminationStep A t i t = 0 := by
  sorry

/-- A zero row stays zero. Port of `NLAlib.eliminationStep_apply_eq_zero_of_row`. -/
theorem eliminationStep_apply_eq_zero_of_row {A : Matrix n n K} {u : n} (hu : ∀ j, A u j = 0)
    (t j : n) : eliminationStep A t u j = 0 := by
  sorry

/-- A zero column stays zero. Port of `NLAlib.eliminationStep_apply_eq_zero_of_col`. -/
theorem eliminationStep_apply_eq_zero_of_col {A : Matrix n n K} {u : n} (hu : ∀ i, A i u = 0)
    (t i : n) : eliminationStep A t i u = 0 := by
  sorry

/-- Elimination commutes with the transpose. -/
theorem eliminationStep_transpose (A : Matrix n n K) (t : n) :
    eliminationStep Aᵀ t = (eliminationStep A t)ᵀ := by
  sorry

/-- Elimination commutes with relabelling. -/
theorem eliminationStep_submatrix (A : Matrix n n K) (e : m → n) (t : m) :
    eliminationStep (A.submatrix e e) t = (eliminationStep A (e t)).submatrix e e := by
  sorry

section Fintype

variable [Fintype n] [DecidableEq n]

/-- The action of an elimination step on a vector.
Port of `NLAlib.eliminationStep_mulVec_eq`. -/
theorem eliminationStep_mulVec (A : Matrix n n K) (t : n) (x : n → K) :
    eliminationStep A t *ᵥ x = A *ᵥ (x - ((A *ᵥ x) t / A t t) • Pi.single t 1) := by
  sorry

/-- **A step at a nonzero pivot lowers the rank by one** (Wedderburn's rank reduction).
Port of `NLAlib.rank_eliminationStep_add_one_eq`. -/
theorem rank_eliminationStep_add_one {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    (eliminationStep A t).rank + 1 = A.rank := by
  sorry

/-- **The determinant through an elimination step**: `det A` is the pivot times the determinant
of the Schur complement, which is the eliminated matrix on the complement of the pivot.
Port of `NLAlib.det_eq_mul_det_pivotSchur`, there for the first pivot of a matrix on `Fin`. -/
theorem det_eq_apply_self_mul_det_eliminationStep {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    A.det = A t t *
      ((eliminationStep A t).submatrix (Subtype.val : {i // i ≠ t} → n) Subtype.val).det := by
  sorry

/-- The trace after an elimination step. -/
theorem trace_eliminationStep (A : Matrix n n K) (t : n) :
    (eliminationStep A t).trace = A.trace - (A t t)⁻¹ * ∑ i, A i t * A t i := by
  sorry

end Fintype

/-! ### Elimination on Hermitian and positive semidefinite matrices -/

/-- Elimination preserves Hermitian matrices. Port of `NLAlib.isHermitian_eliminationStep`. -/
theorem _root_.Matrix.IsHermitian.eliminationStep {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (t : n) : (eliminationStep A t).IsHermitian := by
  sorry

section Fintype

variable [Fintype n]

/-- **Elimination preserves positive semidefinite matrices.**
Port of `NLAlib.posSemidef_eliminationStep`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (t : n) : (eliminationStep A t).PosSemidef := by
  sorry

/-- Elimination decreases a positive semidefinite matrix in the Loewner order.
Port of `NLAlib.eliminationStep_le`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_le {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (t : n) : eliminationStep A t ≤ A := by
  sorry

/-- For a positive semidefinite matrix a step clears the pivot row, whether or not the pivot is
zero. Port of `NLAlib.eliminationStep_apply_pivot_left`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_apply_pivot_left {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (t j : n) : eliminationStep A t t j = 0 := by
  sorry

/-- For a positive semidefinite matrix a step clears the pivot column, whether or not the pivot
is zero. Port of `NLAlib.eliminationStep_apply_pivot_right`. -/
theorem _root_.Matrix.PosSemidef.eliminationStep_apply_pivot_right {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (t i : n) : eliminationStep A t i t = 0 := by
  sorry

/-- **Positive definiteness through an elimination step**: `A` is positive definite exactly when
the pivot is positive and the Schur complement is positive definite.
Port of `NLAlib.posDef_iff_pivotSchur`, there for the first pivot of a matrix on `Fin`. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_eliminationStep [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : n) :
    A.PosDef ↔ 0 < A t t ∧
      ((eliminationStep A t).submatrix (Subtype.val : {i // i ≠ t} → n) Subtype.val).PosDef := by
  sorry

/-- Elimination along any list of pivots keeps a positive semidefinite matrix positive
semidefinite. -/
theorem _root_.Matrix.PosSemidef.foldl_eliminationStep {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) : (l.foldl eliminationStep A).PosSemidef := by
  sorry

/-- **Elimination along a list of pivots is the Nyström residual.** For a positive semidefinite
`A` and pivots `l`, the eliminated matrix is `A - A_{:,l} (A_{l,l})⁺ A_{l,:}`: it depends only on
the set of pivots, and repeated pivots do nothing. This is the residual of the partial pivoted
Cholesky factorization. [ChenEtAl2025, §2]. -/
theorem _root_.Matrix.PosSemidef.foldl_eliminationStep_eq_sub [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (l : List n) :
    l.foldl eliminationStep A =
      A - A.submatrix id l.get * pinv (A.submatrix l.get l.get) * A.submatrix l.get id := by
  sorry

/-- **The expected step of randomly pivoted Cholesky.** Choosing the pivot `i` with probability
`A i i / tr A` gives, on average, `A - A² / tr A`.
[ChenEtAl2025, §5].
Port of `NLAlib.sum_choleskyPivotProbability_smul_eliminationStep_eq`. -/
theorem _root_.Matrix.PosSemidef.sum_smul_eliminationStep {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (ht : RCLike.re A.trace ≠ 0) :
    ∑ i, (RCLike.re (A i i) / RCLike.re A.trace) • eliminationStep A i =
      A - (RCLike.re A.trace)⁻¹ • (A * A) := by
  sorry

end Fintype

/-! ### Elimination in the natural order -/

/-- The matrix after eliminating the pivots `0, …, k - 1` of a matrix indexed by `Fin n`, in this
order. Steps beyond `n` do nothing. -/
def gaussState {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then eliminationStep (gaussState A k) ⟨k, h⟩ else gaussState A k

section GaussState

variable {n : ℕ}

/-- Elimination starts from the matrix. -/
@[simp]
theorem gaussState_zero (A : Matrix (Fin n) (Fin n) K) : gaussState A 0 = A :=
  rfl

/-- One more step of elimination. -/
theorem gaussState_succ (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (h : k < n) :
    gaussState A (k + 1) = eliminationStep (gaussState A k) ⟨k, h⟩ := by
  sorry

/-- Elimination in the natural order is elimination along the list `0, …, k - 1`. -/
theorem gaussState_eq_foldl (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    gaussState A k = ((List.finRange n).take k).foldl eliminationStep A := by
  sorry

/-- **The telescoping identity of elimination**: `A` is the current state plus the rank-one
matrices removed so far. It holds with no assumption on the pivots, since a zero pivot removes
nothing. -/
theorem eq_gaussState_add_sum (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    A = gaussState A k +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        (gaussState A j j j)⁻¹ •
          Matrix.vecMulVec (fun i => gaussState A j i j) (gaussState A j j) := by
  sorry

/-- While the pivots are nonzero, the rows already eliminated are zero. -/
theorem gaussState_apply_eq_zero_of_lt_left (A : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) {i : Fin n} (hi : (i : ℕ) < k)
    (j : Fin n) : gaussState A k i j = 0 := by
  sorry

/-- While the pivots are nonzero, the columns already eliminated are zero. -/
theorem gaussState_apply_eq_zero_of_lt_right (A : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) (i : Fin n) {j : Fin n}
    (hj : (j : ℕ) < k) : gaussState A k i j = 0 := by
  sorry

/-- While the pivots are nonzero, each step lowers the rank by one. -/
theorem rank_gaussState_add (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ n)
    (hp : ∀ l : Fin n, (l : ℕ) < k → gaussState A l l l ≠ 0) :
    (gaussState A k).rank + k = A.rank := by
  sorry

/-- **Pivots and leading principal minors.** While the earlier pivots are nonzero, the leading
principal minor of order `i + 1` is the product of the first `i + 1` pivots.
Port of `NLAlib.leadingMinor_succ_eq_mul_leadingMinor_pivotSchur`, in closed form. -/
theorem principalMinor_Iic_eq_prod_gaussState (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (hp : ∀ l : Fin n, l < i → gaussState A l l l ≠ 0) :
    principalMinor A (Finset.Iic i) = ∏ l ∈ Finset.Iic i, gaussState A l l l := by
  sorry

/-- **A pivot is the ratio of consecutive leading principal minors**, while the earlier pivots
are nonzero. -/
theorem gaussState_apply_self_mul_principalMinor_Iio (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (hp : ∀ l : Fin n, l < i → gaussState A l l l ≠ 0) :
    gaussState A i i i * principalMinor A (Finset.Iio i) = principalMinor A (Finset.Iic i) := by
  sorry

/-- **The pivots up to `i` are nonzero exactly when the leading principal minors up to order
`i + 1` are nonzero.** -/
theorem forall_gaussState_ne_zero_iff (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    (∀ l : Fin n, l ≤ i → gaussState A l l l ≠ 0) ↔
      ∀ l : Fin n, l ≤ i → principalMinor A (Finset.Iic l) ≠ 0 := by
  sorry

/-- The pivots of a positive definite matrix are positive. -/
theorem _root_.Matrix.PosDef.gaussState_apply_self_pos {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) (i : Fin n) : 0 < gaussState A i i i := by
  sorry

end GaussState

end NLAlib
