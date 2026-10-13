/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Gram matrices

The Gram matrix of `A` is `Aᴴ * A`; it has no definition of its own. Mathlib has its positive
semidefiniteness (`Matrix.posSemidef_conjTranspose_mul_self`), rank
(`Matrix.rank_conjTranspose_mul_self`) and kernel (`Matrix.ker_mulVecLin_conjTranspose_mul_self`).
This file adds the characterisations of invertibility.

"Full column rank" is spelled `Function.Injective A.mulVec` throughout the library, the
hypothesis of Mathlib's `Matrix.PosDef.conjTranspose_mul_self`. The equivalent forms
`IsUnit (Aᴴ * A)` and `A.rank = Fintype.card n` are reached through the lemmas here.

## Main results

* `NLAlib.isUnit_conjTranspose_mul_self_iff`: `Aᴴ * A` is invertible iff `A.mulVec` is injective.
* `NLAlib.mulVec_injective_iff_rank_eq`: `A.mulVec` is injective iff `A.rank` is the number of
  columns.
* `NLAlib.posDef_conjTranspose_mul_self_iff`: `Aᴴ * A` is positive definite iff `A.mulVec` is
  injective.
* `NLAlib.conjTranspose_mul_self_eq_gram`: the bridge to Mathlib's `Matrix.gram`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-- An entry of the Gram matrix `Aᴴ * A` is the pairing of two columns of `A`. -/
theorem conjTranspose_mul_self_apply [Fintype m] (A : Matrix m n 𝕜) (i j : n) :
    (Aᴴ * A) i j = star (A.col i) ⬝ᵥ A.col j := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply, Matrix.col_apply,
    Pi.star_apply]

/-- `Aᴴ * A` is Mathlib's `Matrix.gram` of the columns of `A` in `EuclideanSpace 𝕜 m`. -/
theorem conjTranspose_mul_self_eq_gram [Fintype m] (A : Matrix m n 𝕜) :
    Aᴴ * A = Matrix.gram 𝕜 fun j => WithLp.toLp 2 (A.col j) := by
  ext i j
  rw [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, conjTranspose_mul_self_apply,
    dotProduct_comm]

/-- `A.mulVec` is injective exactly when the rank of `A` is its number of columns. -/
theorem mulVec_injective_iff_rank_eq [Fintype n] {A : Matrix m n 𝕜} :
    Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span,
    Matrix.rank_eq_finrank_span_cols, eq_comm, Set.finrank]

/-- The Gram matrix `Aᴴ * A` is invertible exactly when `A` has full column rank.
[HornJohnson2013, Theorem 7.2.10]. -/
theorem isUnit_conjTranspose_mul_self_iff [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} : IsUnit (Aᴴ * A) ↔ Function.Injective A.mulVec := by
  rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin,
    ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_conjTranspose_mul_self]

/-- The Gram matrix `Aᴴ * A` is positive definite exactly when `A` has full column rank.
The reverse direction is Mathlib's `Matrix.PosDef.conjTranspose_mul_self`. -/
theorem posDef_conjTranspose_mul_self_iff [Fintype m] [Fintype n] {A : Matrix m n 𝕜} :
    (Aᴴ * A).PosDef ↔ Function.Injective A.mulVec := by
  classical
  exact ⟨fun h => isUnit_conjTranspose_mul_self_iff.mp h.isUnit,
    Matrix.PosDef.conjTranspose_mul_self A⟩

/-- The Gram matrix `Aᴴ * A` is invertible exactly when the rank of `A` is its number of
columns. Port of `NLAlib.det_ne_zero_of_rank_eq`, there for a square real matrix. -/
theorem isUnit_conjTranspose_mul_self_iff_rank [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} : IsUnit (Aᴴ * A) ↔ A.rank = Fintype.card n := by
  rw [isUnit_conjTranspose_mul_self_iff, mulVec_injective_iff_rank_eq]

/-- With full column rank, `(Aᴴ * A)⁻¹ * Aᴴ` is a left inverse of `A`. -/
theorem inv_conjTranspose_mul_self_mul_conjTranspose_mul [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) : (Aᴴ * A)⁻¹ * Aᴴ * A = 1 := by
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_conjTranspose_mul_self_iff.mpr hA))

/-- Two matrices with a common left factor of full column rank are equal when the products are:
`A * B = A * C ↔ B = C`. -/
theorem mul_right_inj_of_mulVec_injective {p : Type*} [Fintype n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {B C : Matrix n p 𝕜} : A * B = A * C ↔ B = C := by
  refine ⟨fun h => Matrix.ext_col fun j => hA ?_, fun h => by rw [h]⟩
  exact congrArg (fun M : Matrix m p 𝕜 => M.col j) h

end NLAlib
