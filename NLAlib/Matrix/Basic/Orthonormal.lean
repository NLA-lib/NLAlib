/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Matrices with orthonormal columns

`NLAlib.HasOrthonormalCols Q` says `Qᴴ * Q = 1`. It is the library's single spelling of
orthonormality and is always taken as a hypothesis in this form. Orthonormal rows are
`HasOrthonormalCols Qᴴ`; a unitary matrix is a square `Q` with `HasOrthonormalCols Q`.

## Main definitions

* `NLAlib.HasOrthonormalCols`: `Qᴴ * Q = 1`.

## Main results

* `NLAlib.hasOrthonormalCols_iff_orthonormal`: the bridge to Mathlib's `Orthonormal`.
* `NLAlib.hasOrthonormalCols_iff_mem_unitaryGroup`: the bridge to `Matrix.unitaryGroup`.
* `NLAlib.HasOrthonormalCols.norm_toLp_mulVec`: multiplication by `Q` preserves the Euclidean
  norm.
* `NLAlib.HasOrthonormalCols.mulVec_injective`: `Q` has full column rank.
* `NLAlib.HasOrthonormalCols.mul_conjTranspose_self`: for square `Q`, also `Q * Qᴴ = 1`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- `Q` has orthonormal columns: `Qᴴ * Q = 1`. Over `ℝ` this is `Qᵀ * Q = 1`. Orthonormal rows are
expressed by applying the predicate to `Qᴴ`, and a unitary matrix is a square matrix with this
property. -/
def HasOrthonormalCols (Q : Matrix m n 𝕜) : Prop :=
  Qᴴ * Q = 1

/-- `HasOrthonormalCols Q` unfolds to `Qᴴ * Q = 1`. -/
theorem hasOrthonormalCols_iff {Q : Matrix m n 𝕜} : HasOrthonormalCols Q ↔ Qᴴ * Q = 1 :=
  Iff.rfl

namespace HasOrthonormalCols

/-- The defining equation `Qᴴ * Q = 1`, as a rewrite rule. -/
theorem conjTranspose_mul_self {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : Qᴴ * Q = 1 :=
  hQ

end HasOrthonormalCols

/-! ### Bridges to Mathlib -/

/-- `Q` has orthonormal columns exactly when its columns are an orthonormal family in
`EuclideanSpace 𝕜 m`, in the sense of Mathlib's `Orthonormal`.
Port of `NLAlib.hasOrthonormalCols_iff_orthonormal`. -/
theorem hasOrthonormalCols_iff_orthonormal {Q : Matrix m n 𝕜} :
    HasOrthonormalCols Q ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j) := by
  sorry

/-- A square matrix has orthonormal columns exactly when it belongs to Mathlib's
`Matrix.unitaryGroup`. -/
theorem hasOrthonormalCols_iff_mem_unitaryGroup {Q : Matrix n n 𝕜} :
    HasOrthonormalCols Q ↔ Q ∈ Matrix.unitaryGroup n 𝕜 := by
  sorry

/-! ### Constructions -/

/-- The identity matrix has orthonormal columns. -/
theorem hasOrthonormalCols_one : HasOrthonormalCols (1 : Matrix n n 𝕜) := by
  sorry

namespace HasOrthonormalCols

/-- A product of matrices with orthonormal columns has orthonormal columns. -/
protected theorem mul {Q : Matrix l m 𝕜} {W : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (hW : HasOrthonormalCols W) : HasOrthonormalCols (Q * W) := by
  sorry

/-- Relabelling the rows by a bijection and selecting columns by an injective map preserves
orthonormality of the columns. -/
protected theorem submatrix {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (e₁ : l ≃ m)
    {e₂ : p → n} (he₂ : Function.Injective e₂) : HasOrthonormalCols (Q.submatrix e₁ e₂) := by
  sorry

end HasOrthonormalCols

/-- Two blocks of columns placed side by side have orthonormal columns exactly when each block
does and the blocks are mutually orthogonal. -/
theorem hasOrthonormalCols_fromCols_iff {Q₁ : Matrix m n 𝕜} {Q₂ : Matrix m p 𝕜} :
    HasOrthonormalCols (Matrix.fromCols Q₁ Q₂) ↔
      HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Q₂ ∧ Q₁ᴴ * Q₂ = 0 := by
  sorry

namespace HasOrthonormalCols

/-! ### Cancellation -/

/-- `Qᴴ` cancels `Q` on the left of a product: `Qᴴ * (Q * A) = A`. -/
theorem conjTranspose_mul_cancel_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix n p 𝕜) : Qᴴ * (Q * A) = A := by
  sorry

/-- `Q` cancels `Qᴴ` on the right of a product: `A * Qᴴ * Q = A`. -/
theorem mul_conjTranspose_mul_cancel_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : A * Qᴴ * Q = A := by
  sorry

/-- `Q * Qᴴ * Q = Q`: the projector `Q * Qᴴ` fixes the columns of `Q`. -/
theorem mul_conjTranspose_mul_self {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Q * Qᴴ * Q = Q := by
  sorry

/-- Multiplication by `Q` on the left preserves Gram products: `(Q * A)ᴴ * (Q * B) = Aᴴ * B`.
In particular `(Q * A)ᴴ * (Q * A) = Aᴴ * A`. -/
theorem conjTranspose_mul_mul {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜)
    (B : Matrix n l 𝕜) : (Q * A)ᴴ * (Q * B) = Aᴴ * B := by
  sorry

/-- Left multiplication by a matrix with orthonormal columns is injective. -/
theorem mul_right_inj {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) {A B : Matrix n p 𝕜} :
    Q * A = Q * B ↔ A = B := by
  sorry

/-! ### Action on vectors -/

/-- A matrix with orthonormal columns has full column rank: `Q.mulVec` is injective. -/
theorem mulVec_injective {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Function.Injective Q.mulVec := by
  sorry

/-- `Qᴴ` undoes `Q` on vectors: `Qᴴ *ᵥ (Q *ᵥ x) = x`. -/
theorem conjTranspose_mulVec_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    Qᴴ *ᵥ (Q *ᵥ x) = x := by
  sorry

/-- Multiplication by `Q` preserves the pairing `star x ⬝ᵥ y`.
Port of `NLAlib.star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`, there for `x = y`. -/
theorem star_mulVec_dotProduct_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x y : n → 𝕜) : star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = star x ⬝ᵥ y := by
  sorry

/-- Multiplication by a matrix with orthonormal columns preserves the Euclidean norm. -/
theorem norm_toLp_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  sorry

/-- Multiplication by `Qᴴ` does not increase the Euclidean norm (Bessel's inequality).
Port of `NLAlib.sum_norm_sq_conjTranspose_mulVec_le`. -/
theorem norm_toLp_conjTranspose_mulVec_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x : m → 𝕜) : ‖WithLp.toLp 2 (Qᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  sorry

/-! ### Rank and size -/

/-- A matrix with orthonormal columns has at most as many columns as rows.
Port of `NLAlib.card_le_card_of_hasOrthonormalCols`. -/
theorem card_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Fintype.card n ≤ Fintype.card m := by
  sorry

/-- A matrix with orthonormal columns has rank equal to its number of columns. -/
theorem rank_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : Q.rank = Fintype.card n := by
  sorry

/-- Left multiplication by a matrix with orthonormal columns preserves rank. -/
theorem rank_mul {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    (Q * A).rank = A.rank := by
  sorry

/-! ### Square matrices -/

/-- A matrix with orthonormal columns and as many rows as columns also satisfies `Q * Qᴴ = 1`.
The row and column index types may differ. -/
theorem mul_conjTranspose_self_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) : Q * Qᴴ = 1 := by
  sorry

/-- A square matrix with orthonormal columns satisfies `Q * Qᴴ = 1`. -/
theorem mul_conjTranspose_self {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q * Qᴴ = 1 := by
  sorry

/-- If `Q` has orthonormal columns and as many rows as columns, then `Qᴴ` has orthonormal
columns. -/
theorem conjTranspose_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) : HasOrthonormalCols Qᴴ := by
  sorry

/-- The conjugate transpose of a square matrix with orthonormal columns has orthonormal
columns. -/
protected theorem conjTranspose {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) :
    HasOrthonormalCols Qᴴ := by
  sorry

/-- A square matrix with orthonormal columns is invertible. -/
theorem isUnit {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : IsUnit Q := by
  sorry

/-- The inverse of a square matrix with orthonormal columns is its conjugate transpose. -/
theorem inv_eq {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q⁻¹ = Qᴴ := by
  sorry

end HasOrthonormalCols

end NLAlib
