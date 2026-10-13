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
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

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

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype m] [DecidableEq n]

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
  rw [orthonormal_iff_ite, HasOrthonormalCols, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply, Matrix.one_apply, dotProduct]
  simp only [Matrix.conjTranspose_apply, Matrix.col_apply, Pi.star_apply, mul_comm]

/-- A square matrix has orthonormal columns exactly when it belongs to Mathlib's
`Matrix.unitaryGroup`. -/
theorem hasOrthonormalCols_iff_mem_unitaryGroup [Fintype n] {Q : Matrix n n 𝕜} :
    HasOrthonormalCols Q ↔ Q ∈ Matrix.unitaryGroup n 𝕜 :=
  Matrix.mem_unitaryGroup_iff'.symm

/-! ### Constructions -/

/-- The identity matrix has orthonormal columns. -/
theorem hasOrthonormalCols_one [Fintype n] : HasOrthonormalCols (1 : Matrix n n 𝕜) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_one, Matrix.one_mul]

namespace HasOrthonormalCols

/-- A product of matrices with orthonormal columns has orthonormal columns. -/
protected theorem mul [Fintype l] [DecidableEq m] {Q : Matrix l m 𝕜} {W : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (hW : HasOrthonormalCols W) : HasOrthonormalCols (Q * W) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
    hQ.conjTranspose_mul_self, Matrix.one_mul, hW.conjTranspose_mul_self]

/-- Relabelling the rows by a bijection and selecting columns by an injective map preserves
orthonormality of the columns. -/
protected theorem submatrix [Fintype l] [DecidableEq p] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (e₁ : l ≃ m) {e₂ : p → n} (he₂ : Function.Injective e₂) :
    HasOrthonormalCols (Q.submatrix e₁ e₂) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hQ.conjTranspose_mul_self, Matrix.submatrix_one e₂ he₂]

end HasOrthonormalCols

/-- Two blocks of columns placed side by side have orthonormal columns exactly when each block
does and the blocks are mutually orthogonal. -/
theorem hasOrthonormalCols_fromCols_iff [DecidableEq p] {Q₁ : Matrix m n 𝕜}
    {Q₂ : Matrix m p 𝕜} :
    HasOrthonormalCols (Matrix.fromCols Q₁ Q₂) ↔
      HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Q₂ ∧ Q₁ᴴ * Q₂ = 0 := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h₁, h₁₂, -, h₂⟩
    exact ⟨h₁, h₂, h₁₂⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    refine ⟨h₁, h₁₂, ?_, h₂⟩
    rw [← Matrix.conjTranspose_eq_zero, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact h₁₂

namespace HasOrthonormalCols

variable [Fintype n]

/-! ### Cancellation -/

/-- `Qᴴ` cancels `Q` on the left of a product: `Qᴴ * (Q * A) = A`. -/
theorem conjTranspose_mul_cancel_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix n p 𝕜) : Qᴴ * (Q * A) = A := by
  rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]

/-- `Q` cancels `Qᴴ` on the right of a product: `A * Qᴴ * Q = A`. -/
theorem mul_conjTranspose_mul_cancel_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : A * Qᴴ * Q = A := by
  rw [Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.mul_one]

/-- `Q * Qᴴ * Q = Q`: the projector `Q * Qᴴ` fixes the columns of `Q`. -/
theorem mul_conjTranspose_mul_self {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Q * Qᴴ * Q = Q :=
  hQ.mul_conjTranspose_mul_cancel_right Q

/-- Multiplication by `Q` on the left preserves Gram products: `(Q * A)ᴴ * (Q * B) = Aᴴ * B`.
In particular `(Q * A)ᴴ * (Q * A) = Aᴴ * A`. -/
theorem conjTranspose_mul_mul {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜)
    (B : Matrix n l 𝕜) : (Q * A)ᴴ * (Q * B) = Aᴴ * B := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left]

/-- Left multiplication by a matrix with orthonormal columns is injective. -/
theorem mul_right_inj {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) {A B : Matrix n p 𝕜} :
    Q * A = Q * B ↔ A = B := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [← hQ.conjTranspose_mul_cancel_left A, h, hQ.conjTranspose_mul_cancel_left]

/-! ### Action on vectors -/

/-- A matrix with orthonormal columns has full column rank: `Q.mulVec` is injective. -/
theorem mulVec_injective {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Function.Injective Q.mulVec := by
  intro x y h
  have h' := congrArg (Qᴴ *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec] using h'

/-- `Qᴴ` undoes `Q` on vectors: `Qᴴ *ᵥ (Q *ᵥ x) = x`. -/
theorem conjTranspose_mulVec_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    Qᴴ *ᵥ (Q *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]

/-- Multiplication by `Q` preserves the pairing `star x ⬝ᵥ y`.
Port of `NLAlib.star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`, there for `x = y`. -/
theorem star_mulVec_dotProduct_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x y : n → 𝕜) : star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.conjTranspose_mulVec_mulVec]

/-- Multiplication by a matrix with orthonormal columns preserves the Euclidean norm. -/
theorem norm_toLp_mulVec {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct,
    EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, hQ.star_mulVec_dotProduct_mulVec]

/-- Multiplication by `Qᴴ` does not increase the Euclidean norm (Bessel's inequality).
Port of `NLAlib.sum_norm_sq_conjTranspose_mulVec_le`. -/
theorem norm_toLp_conjTranspose_mulVec_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (x : m → 𝕜) : ‖WithLp.toLp 2 (Qᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have h := (hasOrthonormalCols_iff_orthonormal.mp hQ).sum_inner_products_le
    (x := WithLp.toLp 2 x) (s := Finset.univ)
  rw [EuclideanSpace.norm_sq_eq]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) h
  simp only [EuclideanSpace.inner_toLp_toLp, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.col_apply, Pi.star_apply, mul_comm]

/-! ### Rank and size -/

/-- A matrix with orthonormal columns has at most as many columns as rows.
Port of `NLAlib.card_le_card_of_hasOrthonormalCols`. -/
theorem card_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Fintype.card n ≤ Fintype.card m := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := Q.mulVecLin) hQ.mulVec_injective
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h

/-- A matrix with orthonormal columns has rank equal to its number of columns. -/
theorem rank_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : Q.rank = Fintype.card n := by
  refine le_antisymm Q.rank_le_card_width ?_
  have h := Matrix.rank_mul_le_right Qᴴ Q
  rwa [hQ.conjTranspose_mul_self, Matrix.rank_one] at h

/-- Left multiplication by a matrix with orthonormal columns preserves rank. -/
theorem rank_mul [Fintype p] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    (Q * A).rank = A.rank := by
  refine le_antisymm (Matrix.rank_mul_le_right Q A) ?_
  have h := Matrix.rank_mul_le_right Qᴴ (Q * A)
  rwa [hQ.conjTranspose_mul_cancel_left] at h

/-! ### Square matrices -/

/-- A matrix with orthonormal columns and as many rows as columns also satisfies `Q * Qᴴ = 1`.
The row and column index types may differ. -/
theorem mul_conjTranspose_self_of_card_eq [DecidableEq m] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card m = Fintype.card n) : Q * Qᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq m n 𝕜 h).mpr hQ

/-- A square matrix with orthonormal columns satisfies `Q * Qᴴ = 1`. -/
theorem mul_conjTranspose_self {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q * Qᴴ = 1 :=
  hQ.mul_conjTranspose_self_of_card_eq rfl

/-- If `Q` has orthonormal columns and as many rows as columns, then `Qᴴ` has orthonormal
columns. -/
theorem conjTranspose_of_card_eq [DecidableEq m] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card m = Fintype.card n) :
    HasOrthonormalCols Qᴴ := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
  exact hQ.mul_conjTranspose_self_of_card_eq h

/-- The conjugate transpose of a square matrix with orthonormal columns has orthonormal
columns. -/
protected theorem conjTranspose {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) :
    HasOrthonormalCols Qᴴ :=
  hQ.conjTranspose_of_card_eq rfl

/-- A square matrix with orthonormal columns is invertible. -/
theorem isUnit {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : IsUnit Q :=
  isUnit_iff_exists.mpr ⟨Qᴴ, hQ.mul_conjTranspose_self, hQ⟩

/-- The inverse of a square matrix with orthonormal columns is its conjugate transpose. -/
theorem inv_eq {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) : Q⁻¹ = Qᴴ :=
  Matrix.inv_eq_left_inv hQ

end HasOrthonormalCols

end NLAlib
