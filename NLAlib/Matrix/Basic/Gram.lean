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

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- An entry of the Gram matrix `Aᴴ * A` is the pairing of two columns of `A`. -/
theorem conjTranspose_mul_self_apply (A : Matrix m n 𝕜) (i j : n) :
    (Aᴴ * A) i j = star (A.col i) ⬝ᵥ A.col j := by
  sorry

/-- `Aᴴ * A` is Mathlib's `Matrix.gram` of the columns of `A` in `EuclideanSpace 𝕜 m`. -/
theorem conjTranspose_mul_self_eq_gram (A : Matrix m n 𝕜) :
    Aᴴ * A = Matrix.gram 𝕜 fun j => WithLp.toLp 2 (A.col j) := by
  sorry

/-- `A.mulVec` is injective exactly when the rank of `A` is its number of columns. -/
theorem mulVec_injective_iff_rank_eq {A : Matrix m n 𝕜} :
    Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  sorry

/-- The Gram matrix `Aᴴ * A` is positive definite exactly when `A` has full column rank.
The forward direction is Mathlib's `Matrix.PosDef.conjTranspose_mul_self`. -/
theorem posDef_conjTranspose_mul_self_iff {A : Matrix m n 𝕜} :
    (Aᴴ * A).PosDef ↔ Function.Injective A.mulVec := by
  sorry

/-- The Gram matrix `Aᴴ * A` is invertible exactly when `A` has full column rank.
[HornJohnson2013, Theorem 7.2.10]. -/
theorem isUnit_conjTranspose_mul_self_iff [DecidableEq n] {A : Matrix m n 𝕜} :
    IsUnit (Aᴴ * A) ↔ Function.Injective A.mulVec := by
  sorry

/-- The Gram matrix `Aᴴ * A` is invertible exactly when the rank of `A` is its number of
columns. Port of `NLAlib.det_ne_zero_of_rank_eq`, there for a square real matrix. -/
theorem isUnit_conjTranspose_mul_self_iff_rank [DecidableEq n] {A : Matrix m n 𝕜} :
    IsUnit (Aᴴ * A) ↔ A.rank = Fintype.card n := by
  sorry

/-- With full column rank, `(Aᴴ * A)⁻¹ * Aᴴ` is a left inverse of `A`. -/
theorem inv_conjTranspose_mul_self_mul_conjTranspose_mul [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : (Aᴴ * A)⁻¹ * Aᴴ * A = 1 := by
  sorry

/-- Two matrices with a common left factor of full column rank are equal when the products are:
`A * B = A * C ↔ B = C`. -/
theorem mul_right_inj_of_mulVec_injective {p : Type*} [Fintype p] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {B C : Matrix n p 𝕜} : A * B = A * C ↔ B = C := by
  sorry

end NLAlib
