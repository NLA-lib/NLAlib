/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Column spaces of a column-partitioned matrix

The column space of `Matrix.fromCols A B`, the matrix
$\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$, contains that of $\mathbf{A}$, and the
column space of $\begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$ contains $\mathbf{y}$.
Mathlib has `Matrix.fromCols_mulVec` (the action of
$\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$ on a split vector) and no range statement.
Upstream candidate for `Mathlib.Data.Matrix.ColumnRowPartitioned` (or
`Mathlib.LinearAlgebra.Matrix.ToLin`, which has `Matrix.mulVecLin`).

## Main results

* `Matrix.range_le_range_fromCols_left`: $\operatorname{range} \mathbf{A} \le
  \operatorname{range} \begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$.
* `Matrix.mem_range_fromCols_replicateCol`: $\mathbf{y} \in
  \operatorname{range} \begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$.
* `Matrix.range_fromCols_eq_sup`: the concatenated column space is the supremum of the two
  column spaces.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommSemiring R] {n q r : Type*} [Fintype q] [Fintype r]

/-- The column space of $\mathbf{A}$ lies in the column space of `Matrix.fromCols A B`, the matrix
$\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$. -/
theorem range_le_range_fromCols_left (A : Matrix n q R) (B : Matrix n r R) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range (fromCols A B).mulVecLin := by
  rintro _ ⟨v, rfl⟩
  refine ⟨Sum.elim v 0, ?_⟩
  simp only [mulVecLin_apply, fromCols_mulVec_sumElim, mulVec_zero, add_zero]

/-- The column space of a column concatenation is the supremum of the two column spaces.
This holds over every commutative semiring. Upstream candidate. -/
theorem range_fromCols_eq_sup (A : Matrix n q R) (B : Matrix n r R) :
    LinearMap.range (fromCols A B).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change (fromCols A B) *ᵥ x ∈ _
    rw [fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · apply sup_le (range_le_range_fromCols_left A B)
    rintro _ ⟨x, rfl⟩
    refine ⟨Sum.elim 0 x, ?_⟩
    simp only [mulVecLin_apply, fromCols_mulVec_sumElim, mulVec_zero, zero_add]

/-- The vector $\mathbf{y}$ lies in the column space of
$\begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$, the matrix $\mathbf{A}$ with
$\mathbf{y}$ appended as one column. -/
theorem mem_range_fromCols_replicateCol (A : Matrix n q R) (y : n → R) :
    y ∈ LinearMap.range (fromCols A (replicateCol Unit y)).mulVecLin := by
  refine ⟨Sum.elim 0 fun _ => 1, ?_⟩
  ext i
  simp [mulVec, dotProduct]

end Matrix
