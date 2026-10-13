/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector

/-!
# The Penrose conditions

`NLAlib.IsPinv A B` says that `B` is a Moore–Penrose pseudoinverse of `A`: the four Penrose
identities hold. Such a `B` is unique, so the predicate is the way to identify a pseudoinverse:
to show `pinv A = B` (in `NLAlib.Matrix.Pseudoinverse.Pinv`) one checks the four identities.

## Main definitions

* `NLAlib.IsPinv`: the four Penrose identities.

## Main results

* `NLAlib.IsPinv.unique`: a matrix has at most one pseudoinverse.
* `NLAlib.IsPinv.symm`, `NLAlib.IsPinv.conjTranspose`, `NLAlib.IsPinv.mul_left`: stability.
* `NLAlib.IsPinv.mul_eq_rangeProjector`: `A * B` is the orthogonal projector onto the column
  space of `A`.
* `NLAlib.isPinv_inv`, `NLAlib.HasOrthonormalCols.isPinv`, `NLAlib.isPinv_diagonal`: examples.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- `B` is a **Moore–Penrose pseudoinverse** of `A`: the four Penrose identities
`A B A = A`, `B A B = B`, `(A B)ᴴ = A B`, `(B A)ᴴ = B A`. There is at most one such `B`
(`NLAlib.IsPinv.unique`), and every matrix has one (`NLAlib.exists_isPinv`).
[GolubVanLoan2013, §5.5.2]; [HornJohnson2013, Problem 7.3.P7].
Port of `NLAlib.IsMoorePenroseInverse`. -/
structure IsPinv (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) : Prop where
  /-- `A * B * A = A`. -/
  mul_mul_left : A * B * A = A
  /-- `B * A * B = B`. -/
  mul_mul_right : B * A * B = B
  /-- `A * B` is Hermitian. -/
  isHermitian_left : (A * B).IsHermitian
  /-- `B * A` is Hermitian. -/
  isHermitian_right : (B * A).IsHermitian

namespace IsPinv

variable {A : Matrix m n 𝕜} {B C : Matrix n m 𝕜}

/-- **Uniqueness of the pseudoinverse.** [HornJohnson2013, Problem 7.3.P7].
Port of `NLAlib.IsMoorePenroseInverse.unique`.
Result: moore-penrose-uniqueness -/
theorem unique (hB : IsPinv A B) (hC : IsPinv A C) : B = C := by
  have hBA : B * A = C * A := by
    have h1 : B * A * (C * A) = B * A := by
      rw [Matrix.mul_assoc B A, ← Matrix.mul_assoc A C A, hC.mul_mul_left]
    have h2 : C * A * (B * A) = C * A := by
      rw [Matrix.mul_assoc C A, ← Matrix.mul_assoc A B A, hB.mul_mul_left]
    have h3 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, hB.isHermitian_right.eq, hC.isHermitian_right.eq, h2] at h3
    exact h3.symm
  have hAB : A * B = A * C := by
    have h1 : A * B * (A * C) = A * C := by
      rw [← Matrix.mul_assoc, hB.mul_mul_left]
    have h2 : A * C * (A * B) = A * B := by
      rw [← Matrix.mul_assoc, hC.mul_mul_left]
    have h3 := congrArg Matrix.conjTranspose h1
    rwa [Matrix.conjTranspose_mul, hB.isHermitian_left.eq, hC.isHermitian_left.eq, h2] at h3
  calc B = B * A * B := hB.mul_mul_right.symm
    _ = C * (A * B) := by rw [hBA, Matrix.mul_assoc]
    _ = C * A * C := by rw [hAB, Matrix.mul_assoc]
    _ = C := hC.mul_mul_right

/-- The relation is symmetric: `A` is a pseudoinverse of its pseudoinverse.
Port of `NLAlib.IsMoorePenroseInverse.swap`. -/
protected theorem symm (h : IsPinv A B) : IsPinv B A := by
  exact ⟨h.mul_mul_right, h.mul_mul_left, h.isHermitian_right, h.isHermitian_left⟩

/-- The conjugate transpose of a pseudoinverse is a pseudoinverse of the conjugate transpose.
Port of `NLAlib.IsMoorePenroseInverse.conjTranspose`. -/
protected theorem conjTranspose (h : IsPinv A B) : IsPinv Aᴴ Bᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      h.mul_mul_left]
  · rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      h.mul_mul_right]
  · rw [← Matrix.conjTranspose_mul]
    exact h.isHermitian_right.conjTranspose
  · rw [← Matrix.conjTranspose_mul]
    exact h.isHermitian_left.conjTranspose

/-- Relabelling rows and columns by bijections.
Port of `NLAlib.IsMoorePenroseInverse.submatrix`. -/
protected theorem submatrix (h : IsPinv A B) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    IsPinv (A.submatrix e₁ e₂) (B.submatrix e₂ e₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.mul_mul_left]
  · rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.mul_mul_right]
  · rw [Matrix.submatrix_mul_equiv]
    exact h.isHermitian_left.submatrix e₁
  · rw [Matrix.submatrix_mul_equiv]
    exact h.isHermitian_right.submatrix e₂

/-- Scaling by a nonzero scalar. -/
protected theorem smul (h : IsPinv A B) {c : 𝕜} (hc : c ≠ 0) : IsPinv (c • A) (c⁻¹ • B) := by
  have hAB : c • A * c⁻¹ • B = A * B := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hBA : c⁻¹ • B * c • A = B * A := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hAB, Matrix.mul_smul, h.mul_mul_left]
  · rw [hBA, Matrix.mul_smul, h.mul_mul_right]
  · rw [hAB]
    exact h.isHermitian_left
  · rw [hBA]
    exact h.isHermitian_right

/-- Left multiplication by a matrix with orthonormal columns: `(Q * A)⁺ = A⁺ * Qᴴ`.
Port of `NLAlib.IsMoorePenroseInverse.unitary_transform`. -/
theorem mul_left [DecidableEq m] (h : IsPinv A B) {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) : IsPinv (Q * A) (B * Qᴴ) := by
  have hBA : B * Qᴴ * (Q * A) = B * A := by
    rw [Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left]
  have hAB : Q * A * (B * Qᴴ) = Q * (A * B) * Qᴴ := by
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc (Q * A), hBA, Matrix.mul_assoc Q, ← Matrix.mul_assoc A, h.mul_mul_left]
  · rw [hBA, ← Matrix.mul_assoc, h.mul_mul_right]
  · rw [hAB]
    exact Matrix.isHermitian_mul_mul_conjTranspose Q h.isHermitian_left
  · rw [hBA]
    exact h.isHermitian_right

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns:
`(A * Qᴴ)⁺ = Q * A⁺`. -/
theorem mul_conjTranspose_right [DecidableEq n] (h : IsPinv A B) {Q : Matrix l n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsPinv (A * Qᴴ) (Q * B) := by
  have h' := (h.conjTranspose.mul_left hQ).conjTranspose
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at h'

/-- `A * B` is an orthogonal projector.
Port of `NLAlib.IsMoorePenroseInverse.mul_isIdempotentElem`. -/
theorem isStarProjection_left (h : IsPinv A B) : IsStarProjection (A * B) := by
  rw [Matrix.isStarProjection_iff]
  exact ⟨by rw [← Matrix.mul_assoc, h.mul_mul_left], h.isHermitian_left⟩

/-- `B * A` is an orthogonal projector.
Port of `NLAlib.IsMoorePenroseInverse.inv_mul_isIdempotentElem`. -/
theorem isStarProjection_right (h : IsPinv A B) : IsStarProjection (B * A) := by
  exact h.symm.isStarProjection_left

/-- `A * B` is the orthogonal projector onto the column space of `A`.
Port of `NLAlib.IsMoorePenroseInverse.range_mul_eq`. -/
theorem mul_eq_rangeProjector (h : IsPinv A B) : A * B = rangeProjector A := by
  refine h.isStarProjection_left.eq_rangeProjector (le_antisymm ?_ ?_)
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨B, rfl⟩
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨A, h.mul_mul_left.symm⟩

/-- `B * A` is the orthogonal projector onto the column space of `Aᴴ`, the row space of `A`. -/
theorem mul_eq_rangeProjector_conjTranspose (h : IsPinv A B) : B * A = rangeProjector Aᴴ := by
  rw [← h.conjTranspose.mul_eq_rangeProjector, ← Matrix.conjTranspose_mul,
    h.isHermitian_right.eq]

/-- The column space of a pseudoinverse of `A` is the column space of `Aᴴ`. -/
theorem range_mulVecLin_eq (h : IsPinv A B) :
    LinearMap.range B.mulVecLin = LinearMap.range Aᴴ.mulVecLin := by
  rw [← range_mulVecLin_rangeProjector Aᴴ, ← h.mul_eq_rangeProjector_conjTranspose]
  refine le_antisymm ?_ ?_
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨B, h.mul_mul_right.symm⟩
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨A, rfl⟩

open scoped ComplexOrder in
/-- A pseudoinverse of `A` has the rank of `A`.
Port of the argument of `NLAlib.IsMoorePenroseInverse.range_mul_eq`. -/
theorem rank_eq (h : IsPinv A B) : B.rank = A.rank := by
  rw [Matrix.rank, h.range_mulVecLin_eq, ← Matrix.rank_conjTranspose A, Matrix.rank]

/-- The Gram matrix `Aᴴ * A` has pseudoinverse `B * Bᴴ`.
Port of `NLAlib.IsMoorePenroseInverse.conjTranspose_mul_self`. -/
theorem conjTranspose_mul_self (h : IsPinv A B) : IsPinv (Aᴴ * A) (B * Bᴴ) := by
  have hCG : B * Bᴴ * (Aᴴ * A) = B * A := by
    rw [Matrix.mul_assoc B, ← Matrix.mul_assoc Bᴴ, ← Matrix.conjTranspose_mul,
      h.isHermitian_left.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.mul_mul_right]
  have hGC : Aᴴ * A * (B * Bᴴ) = B * A := by
    have h' := congrArg Matrix.conjTranspose hCG
    rwa [h.isHermitian_right.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose] at h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc (Aᴴ * A), hCG, Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc A,
      h.mul_mul_left]
  · rw [hCG, ← Matrix.mul_assoc, h.mul_mul_right]
  · rw [hGC]
    exact h.isHermitian_right
  · rw [hCG]
    exact h.isHermitian_right

end IsPinv

/-! ### Examples -/

/-- The zero matrix is its own pseudoinverse, up to shape. -/
theorem isPinv_zero : IsPinv (0 : Matrix m n 𝕜) (0 : Matrix n m 𝕜) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_zero]
  · rw [Matrix.mul_zero]
  · rw [Matrix.mul_zero]
    exact Matrix.isHermitian_zero
  · rw [Matrix.mul_zero]
    exact Matrix.isHermitian_zero

/-- The inverse of an invertible matrix is its pseudoinverse. -/
theorem isPinv_inv [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) : IsPinv A A⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  · rw [Matrix.mul_nonsing_inv _ hdet]
    exact Matrix.isHermitian_one
  · rw [Matrix.nonsing_inv_mul _ hdet]
    exact Matrix.isHermitian_one

/-- `a * a⁻¹` is `0` or `1`, hence self-adjoint. -/
private theorem star_mul_inv_self (a : 𝕜) : star (a * a⁻¹) = a * a⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, star_zero]
  · rw [mul_inv_cancel₀ ha, star_one]

/-- The pseudoinverse of a diagonal matrix inverts the nonzero diagonal entries.
Port of `NLAlib.isMoorePenroseInverse_singleton`, there for a `1 × 1` real matrix. -/
theorem isPinv_diagonal [DecidableEq n] (d : n → 𝕜) :
    IsPinv (Matrix.diagonal d) (Matrix.diagonal fun i => (d i)⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_inv_mul_cancel (d i))
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    have h := mul_inv_mul_cancel (d i)⁻¹
    rwa [inv_inv] at h
  · rw [Matrix.diagonal_mul_diagonal]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun i => star_mul_inv_self (d i))
  · rw [Matrix.diagonal_mul_diagonal]
    refine Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun i => ?_)
    change star ((d i)⁻¹ * d i) = (d i)⁻¹ * d i
    rw [mul_comm]
    exact star_mul_inv_self (d i)

/-- A matrix with orthonormal columns has its conjugate transpose as pseudoinverse. -/
theorem HasOrthonormalCols.isPinv [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsPinv Q Qᴴ := by
  refine ⟨hQ.mul_conjTranspose_mul_self, ?_, Matrix.isHermitian_mul_conjTranspose_self Q, ?_⟩
  · rw [hQ.conjTranspose_mul_self, Matrix.one_mul]
  · rw [hQ.conjTranspose_mul_self]
    exact Matrix.isHermitian_one

/-- An orthogonal projector is its own pseudoinverse. -/
theorem _root_.IsStarProjection.isPinv {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    IsPinv P P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP.mul_self, hP.mul_self]
  · rw [hP.mul_self, hP.mul_self]
  · rw [hP.mul_self]
    exact hP.isHermitian
  · rw [hP.mul_self]
    exact hP.isHermitian

/-- With full column rank, `(Aᴴ * A)⁻¹ * Aᴴ` is the pseudoinverse.
Port of `NLAlib.isMoorePenroseInverse_pinvL`. -/
theorem isPinv_inv_mul_conjTranspose [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : IsPinv A ((Aᴴ * A)⁻¹ * Aᴴ) := by
  have hinv := inv_conjTranspose_mul_self_mul_conjTranspose_mul hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  · rw [hinv, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, ← rangeProjector_eq_mul_inv_mul_conjTranspose
      (isUnit_conjTranspose_mul_self_iff.mpr hA)]
    exact (isStarProjection_rangeProjector A).isHermitian
  · rw [hinv]
    exact Matrix.isHermitian_one

/-- With full row rank, `Aᴴ * (A * Aᴴ)⁻¹` is the pseudoinverse.
Port of `NLAlib.isMoorePenroseInverse_pinvR`. -/
theorem isPinv_conjTranspose_mul_inv [DecidableEq m] {A : Matrix m n 𝕜}
    (hA : Function.Injective Aᴴ.mulVec) : IsPinv A (Aᴴ * (A * Aᴴ)⁻¹) := by
  have h := (isPinv_inv_mul_conjTranspose hA).conjTranspose
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] at h

end NLAlib
