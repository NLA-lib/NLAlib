/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.CGS2.BasisExtension
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Orth

/-!
# Decoding the stored blocks of the column-wise extension

Round $c$ of the column-wise extension reads the basis followed by the new columns before $c$
as one stored block of $k + c$ columns. This file identifies that block, decoded, with the
columns $[\mathbf{Q}, \mathbf{Q}'_{<c}]$ of the pure analysis, indexed by the disjoint union of
the old and the new columns, and decodes the columns of the block and of the coefficients.

## Main definitions

* `NLAlib.CGS2.storedCol`: the stored column $j < k + c$ as an old or a new column.

## Main results

* `NLAlib.CGS2.vec_take`, `NLAlib.CGS2.vec_append_left`, `NLAlib.CGS2.vec_append_right`: entries
  of a prefix and of a concatenation.
* `NLAlib.CGS2.storedCol_injective`, `NLAlib.CGS2.eq_inr_of_notMem_range_storedCol`: the stored
  columns are distinct, and the others are new columns from $c$ on.
* `NLAlib.CGS2.submatrix_fromCols_colsBefore`: the stored block of round $c$, decoded.
* `NLAlib.CGS2.decv_take_drop`, `NLAlib.CGS2.dec_vec_coef`: a column of a block and an entry of
  a coefficient column, decoded.
* `NLAlib.CGS2.col_fromCols_colsBefore_eq_zero`, `NLAlib.CGS2.storedCol_mulVec`,
  `NLAlib.CGS2.transpose_mulVec_storedCol_inl`, `NLAlib.CGS2.transpose_mulVec_storedCol_inr`:
  products with the stored block.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGS2

open Ops

variable {K : Type} [Inhabited K]

/-- An entry of a prefix of a list is the entry of the list. -/
theorem vec_take {xs : List K} {L x : ℕ} (h : x < L) : vec (xs.take L) x = vec xs x := by
  simp [vec, List.getD_eq_getElem?_getD, h]

/-- An entry of a concatenation within the first list. -/
theorem vec_append_left {xs ys : List K} {x : ℕ} (h : x < xs.length) :
    vec (xs ++ ys) x = vec xs x := by
  simp [vec, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- An entry of a concatenation past the first list. -/
theorem vec_append_right {xs ys : List K} {x : ℕ} (h : xs.length ≤ x) :
    vec (xs ++ ys) x = vec ys (x - xs.length) := by
  simp [vec, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **The stored column `j < k + c` of round `c`** as an index of $[\mathbf{Q}, \mathbf{Q}']$:
the old column `j` for `j < k`, and the new column `j - k` otherwise. -/
def storedCol (k b c : ℕ) (hc : c ≤ b) (j : Fin (k + c)) : Fin k ⊕ Fin b :=
  if h : (j : ℕ) < k then Sum.inl ⟨j, h⟩ else Sum.inr ⟨j - k, by have := j.isLt; omega⟩

omit [Inhabited K] in
/-- The stored columns of round `c` are distinct columns of $[\mathbf{Q}, \mathbf{Q}']$. -/
theorem storedCol_injective (k b c : ℕ) (hc : c ≤ b) :
    Function.Injective (storedCol k b c hc) := by
  intro i j hij
  unfold storedCol at hij
  have hi' := i.isLt
  have hj' := j.isLt
  by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k
  · rw [dif_pos hi, dif_pos hj] at hij
    have h : (i : ℕ) = (j : ℕ) := Fin.mk.inj (Sum.inl.inj hij)
    exact Fin.ext h
  · rw [dif_pos hi, dif_neg hj] at hij
    cases hij
  · rw [dif_neg hi, dif_pos hj] at hij
    cases hij
  · rw [dif_neg hi, dif_neg hj] at hij
    have h : (i : ℕ) - k = (j : ℕ) - k := congrArg Fin.val (Sum.inr.inj hij)
    exact Fin.ext (by omega)

omit [Inhabited K] in
/-- A column of $[\mathbf{Q}, \mathbf{Q}']$ that is not stored in round `c` is a new column
$c' \ge c$. -/
theorem eq_inr_of_notMem_range_storedCol {k b c : ℕ} (hc : c ≤ b) {x : Fin k ⊕ Fin b}
    (hx : x ∉ Set.range (storedCol k b c hc)) : ∃ c' : Fin b, x = Sum.inr c' ∧ c ≤ (c' : ℕ) := by
  rcases x with j | c'
  · have hj := j.isLt
    exact absurd ⟨⟨j, by omega⟩, by simp [storedCol, hj]⟩ hx
  · refine ⟨c', rfl, ?_⟩
    by_contra hlt
    exact hx ⟨⟨k + c', by omega⟩, by simp [storedCol]⟩

/-- The stored block of round `c`, decoded. For basis words `qs` of `k` columns of length
`n` and new columns `qn`, the first `k + c` stored columns decode to the stored columns of
$[\mathbf{Q}, \mathbf{Q}'_{<c}]$, where $\mathbf{Q}'_{<c}$ is $\mathbf{Q}'$ with the columns
from $c$ on replaced by zero. -/
theorem submatrix_fromCols_colsBefore {dec : K → ℝ} {n k b : ℕ} {qs qn : List K}
    (hqs : qs.length = k * n) (c : Fin b) :
    (Matrix.fromCols (decodeMatrix dec n k qs)
        (colsBefore (decodeMatrix dec n b qn) c)).submatrix id (storedCol k b c c.isLt.le) =
      decodeMatrix dec n (k + c) ((qs ++ qn).take ((k + c) * n)) := by
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  have hcb := c.isLt
  have hlt : (j : ℕ) * n + i < (k + c) * n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at h
    omega
  rw [decodeMatrix_apply, vec_take hlt]
  simp only [Matrix.submatrix_apply, id_eq]
  unfold storedCol
  by_cases hjk : (j : ℕ) < k
  · have hlt' : (j : ℕ) * n + i < qs.length := by
      rw [hqs]
      have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hjk)
      rw [Nat.succ_mul] at h
      omega
    rw [dif_pos hjk, Matrix.fromCols_apply_inl, decodeMatrix_apply, vec_append_left hlt']
  · have hmul := Nat.mul_le_mul_right n (not_lt.mp hjk)
    have hge : qs.length ≤ (j : ℕ) * n + i := by
      rw [hqs]
      omega
    have hsub : (j : ℕ) * n + i - qs.length = ((j : ℕ) - k) * n + i := by
      rw [hqs, Nat.sub_mul]
      omega
    have hc' : (⟨(j : ℕ) - k, by omega⟩ : Fin b) < c :=
      Fin.lt_def.mpr (show (j : ℕ) - k < c by omega)
    rw [dif_neg hjk, Matrix.fromCols_apply_inr, vec_append_right hge, hsub]
    simp only [colsBefore, Matrix.of_apply, if_pos hc', decodeMatrix_apply]

/-- Column `c` of a stored block of columns of length `n`, decoded, is column `c` of the
decoded block. -/
theorem decv_take_drop {dec : K → ℝ} {n b : ℕ} (ws : List K) (c : Fin b) :
    decv dec n ((ws.drop (c * n)).take n) = (decodeMatrix dec n b ws).col c := by
  funext i
  rw [Matrix.col_apply, decodeMatrix_apply]
  exact congrArg dec (vec_drop_take i.isLt)

/-- Entry `i` of column `c` of a stored coefficient block of `k + b` rows, decoded, is the
entry `(i, c)` of the decoded block. -/
theorem dec_vec_coef {dec : K → ℝ} {k b : ℕ} (cs : List K) (c : Fin b) {i : ℕ}
    (hi : i < k + b) :
    dec (vec ((cs.drop (c * (k + b))).take (k + b)) i) =
      decodeMatrix dec (k + b) b cs ⟨i, hi⟩ c := by
  rw [decodeMatrix_apply, vec_drop_take hi]

omit [Inhabited K] in
/-- The columns of $[\mathbf{Q}, \mathbf{Q}'_{<c}]$ that are not stored in round `c` are zero. -/
theorem col_fromCols_colsBefore_eq_zero {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (Q' : Matrix (Fin n) (Fin b) ℝ) (c : Fin b) {x : Fin k ⊕ Fin b}
    (hx : x ∉ Set.range (storedCol k b c c.isLt.le)) :
    (Matrix.fromCols Q (colsBefore Q' c)).col x = 0 := by
  obtain ⟨c', rfl, hge⟩ := eq_inr_of_notMem_range_storedCol _ hx
  exact col_colsBefore_of_not_lt Q' fun h => by
    have := Fin.lt_def.mp h
    omega

omit [Inhabited K] in
/-- The projection onto the stored columns of round `c` is the projection onto the columns of
$\mathbf{F} = [\mathbf{Q}, \mathbf{Q}'_{<c}]$: with $\mathbf{V}$ the stored columns of
$\mathbf{F}$, $\mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{x} =
\mathbf{F}\mathbf{F}^{\mathsf{T}}\mathbf{x}$, the other columns of $\mathbf{F}$ being zero. -/
theorem storedCol_mulVec {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (Q' : Matrix (Fin n) (Fin b) ℝ) (c : Fin b) (x : Fin n → ℝ) :
    (Matrix.fromCols Q (colsBefore Q' c)).submatrix id (storedCol k b c c.isLt.le) *ᵥ
        (((Matrix.fromCols Q (colsBefore Q' c)).submatrix id (storedCol k b c c.isLt.le))ᵀ *ᵥ
          x) =
      Matrix.fromCols Q (colsBefore Q' c) *ᵥ ((Matrix.fromCols Q (colsBefore Q' c))ᵀ *ᵥ x) := by
  have key : ∀ h : Fin k ⊕ Fin b → ℝ,
      (Matrix.fromCols Q (colsBefore Q' c)).submatrix id (storedCol k b c c.isLt.le) *ᵥ
        (h ∘ storedCol k b c c.isLt.le) = Matrix.fromCols Q (colsBefore Q' c) *ᵥ h := by
    intro h
    funext r
    simp only [Matrix.mulVec, dotProduct]
    refine Fintype.sum_of_injective _ (storedCol_injective k b c c.isLt.le)
      (fun j => (Matrix.fromCols Q (colsBefore Q' c)).submatrix id
        (storedCol k b c c.isLt.le) r j * (h ∘ storedCol k b c c.isLt.le) j)
      (fun i => Matrix.fromCols Q (colsBefore Q' c) r i * h i) (fun i hi => ?_) fun j => rfl
    rw [show Matrix.fromCols Q (colsBefore Q' c) r i = 0 from
      congrFun (col_fromCols_colsBefore_eq_zero Q Q' c hi) r, zero_mul]
  exact key ((Matrix.fromCols Q (colsBefore Q' c))ᵀ *ᵥ x)

omit [Inhabited K] in
/-- The coefficient of a vector against a stored column `i < k` is its coefficient against
column `i` of the old basis. -/
theorem transpose_mulVec_storedCol_inl {n k b c : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (X : Matrix (Fin n) (Fin b) ℝ) (hc : c ≤ b) (x : Fin n → ℝ) {i : ℕ} (hi : i < k) :
    (((Matrix.fromCols Q X).submatrix id (storedCol k b c hc))ᵀ *ᵥ x) ⟨i, by omega⟩ =
      (Qᵀ *ᵥ x) ⟨i, hi⟩ := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
    storedCol, dif_pos hi, Matrix.fromCols_apply_inl]

omit [Inhabited K] in
/-- The coefficient of a vector against the stored column `k + c'`, `c' < c`, of round `c` is
its coefficient against column `c'` of the new block. -/
theorem transpose_mulVec_storedCol_inr {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (Q' : Matrix (Fin n) (Fin b) ℝ) (c : Fin b) (x : Fin n → ℝ) {c' : Fin b} (hc' : c' < c) :
    (((Matrix.fromCols Q (colsBefore Q' c)).submatrix id (storedCol k b c c.isLt.le))ᵀ *ᵥ x)
        ⟨k + c', by have := Fin.lt_def.mp hc'; omega⟩ = (Q'ᵀ *ᵥ x) c' := by
  have h : ¬ k + (c' : ℕ) < k := by omega
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
    storedCol, dif_neg h, Matrix.fromCols_apply_inr, Nat.add_sub_cancel_left, Fin.eta,
    colsBefore, Matrix.of_apply, if_pos hc']

end NLAlib.CGS2
