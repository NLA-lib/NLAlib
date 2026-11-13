/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Concatenated columns in fixed-width storage

Column-major storage concatenates the packed words of adjacent column blocks. The finite
matrix statement uses Mathlib's sum-of-column-types equivalence, so recursive matrix assembly
needs no additional storage representation or padding values.

## Main results

* `NLAlib.Ops.EntryCodec.packFinMatrix_columns` groups packed words by matrix column.
-/

@[expose] public section

namespace NLAlib.Ops.EntryCodec

variable {K E : Type}

/-- Column-major packing is the flattened list of packed entry columns, including empty
row or column dimensions. -/
theorem packFinMatrix_columns (C : EntryCodec K E) {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) :
    C.packFinMatrix A = (List.ofFn fun j : Fin cols =>
      (List.ofFn fun i : Fin rows => List.ofFn (C.words (A i j))).flatten).flatten := by
  simp only [packFinMatrix, List.ofFn_mul]
  simp only [List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext z
  simp [finProdFinEquiv, Fin.divNat, Fin.modNat, Idx.div_add z.isLt,
    Idx.mod_add z.isLt, Idx.div_add i.isLt, Idx.mod_add i.isLt]

/-- Adjacent column blocks are concatenated in packed memory. The column sum is identified
with its ordered finite index using Mathlib's standard equivalence. -/
theorem packFinMatrix_fromCols (C : EntryCodec K E) {rows p q : ℕ}
    (A : Matrix (Fin rows) (Fin p) E) (B : Matrix (Fin rows) (Fin q) E) :
    C.packFinMatrix ((Matrix.fromCols A B).submatrix id finSumFinEquiv.symm) =
      C.packFinMatrix A ++ C.packFinMatrix B := by
  have hleft (i : Fin p) :
      finSumFinEquiv.symm (Fin.castLE (Nat.le_add_right p q) i) = (Sum.inl i : Fin p ⊕ Fin q) := by
    exact finSumFinEquiv_symm_apply_castAdd i
  simp only [packFinMatrix_columns, List.ofFn_add, List.flatten_append,
    Matrix.submatrix_apply, hleft,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    id_eq]

/-- The same column assembly allows a supplied proof of the total column count. -/
theorem packFinMatrix_fromCols_cast (C : EntryCodec K E) {rows n p q : ℕ}
    (h : n = p + q) (A : Matrix (Fin rows) (Fin p) E) (B : Matrix (Fin rows) (Fin q) E) :
    C.packFinMatrix ((Matrix.fromCols A B).submatrix id
      ((finCongr h).trans finSumFinEquiv.symm)) = C.packFinMatrix A ++ C.packFinMatrix B := by
  subst n
  exact C.packFinMatrix_fromCols A B

end NLAlib.Ops.EntryCodec
