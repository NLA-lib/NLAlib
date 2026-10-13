/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# The generalized Schur complement

For a Hermitian block matrix `fromBlocks A B Bᴴ C` whose leading block may be singular, the
generalized Schur complement is `C - Bᴴ * pinv A * B`. It has no definition; this is its
spelling. The criteria here are the pseudoinverse forms of the statements in
`NLAlib.Matrix.Basic.SchurComplement`, which are stated with an arbitrary solution `X` of
`A * X = B`; here `X = pinv A * B`.

## Main results

* `NLAlib.posSemidef_fromBlocks_iff_pinv`: Albert's criterion.
* `NLAlib.isLeast_re_quadForm_fromBlocks`: the generalized Schur complement is the partial
  minimum of the quadratic form.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]

/-- `mul_pinv_mul_eq_of_range_le` in the association `A * X = B` with `X = pinv A * B`, which
the criteria of `NLAlib.Matrix.Basic.SchurComplement` take. -/
private theorem mul_pinv_mul_eq_aux [Fintype n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) : A * (pinv A * B) = B := by
  rw [← Matrix.mul_assoc]
  exact mul_pinv_mul_eq_of_range_le h

/-- In a positive semidefinite block matrix, `A * pinv A * B = B`.
Port of `NLAlib.one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef`. -/
theorem mul_pinv_mul_eq_of_posSemidef_fromBlocks [Finite n] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    A * pinv A * B = B := by
  have := Fintype.ofFinite n
  exact mul_pinv_mul_eq_of_range_le (range_mulVecLin_le_of_posSemidef_fromBlocks h)

/-- For Hermitian `A`, the solution `X = pinv A * B` gives `Xᴴ * A * X = Bᴴ * pinv A * B`. -/
private theorem conjTranspose_pinv_mul_mul_pinv_mul {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    (hA : A.IsHermitian) : (pinv A * B)ᴴ * A * (pinv A * B) = Bᴴ * pinv A * B := by
  rw [Matrix.conjTranspose_mul, hA.pinv.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc (pinv A), ← Matrix.mul_assoc (pinv A),
    pinv_mul_mul_pinv]

/-- **Albert's criterion.** The block matrix `fromBlocks A B Bᴴ C` is positive semidefinite
exactly when `A` is, the columns of `B` lie in the column space of `A`, and the generalized
Schur complement `C - Bᴴ * pinv A * B` is positive semidefinite.
[HornJohnson2013, Theorem 7.7.9]. Port of `NLAlib.posSemidef_fromBlocks_iff`.
Result: schur-complement-psd, albert-theorem -/
theorem posSemidef_fromBlocks_iff_pinv [Fintype n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ∧
        (C - Bᴴ * pinv A * B).PosSemidef := by
  constructor
  · intro h
    have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
    have hr := range_mulVecLin_le_of_posSemidef_fromBlocks h
    have hS := posSemidef_sub_conjTranspose_mul_mul_of_posSemidef_fromBlocks h
      (mul_pinv_mul_eq_aux hr)
    rw [conjTranspose_pinv_mul_mul_pinv_mul hA.isHermitian] at hS
    exact ⟨hA, hr, hS⟩
  · rintro ⟨hA, hr, hS⟩
    refine posSemidef_fromBlocks_iff_exists.mpr
      ⟨hA, pinv A * B, mul_pinv_mul_eq_aux hr, ?_⟩
    rwa [conjTranspose_pinv_mul_mul_pinv_mul hA.isHermitian]

/-- In a positive semidefinite block matrix the generalized Schur complement is positive
semidefinite. Port of `NLAlib.generalizedSchurComplement_nonneg`. -/
theorem posSemidef_sub_conjTranspose_mul_pinv_mul_of_posSemidef_fromBlocks [Finite n]
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) : (C - Bᴴ * pinv A * B).PosSemidef := by
  have := Fintype.ofFinite n
  exact (posSemidef_fromBlocks_iff_pinv.mp h).2.2

/-- **The generalized Schur complement as a partial minimum.** In a positive semidefinite block
matrix, the quadratic form of `C - Bᴴ * pinv A * B` at `x` is the least value of the quadratic
form of the block matrix at `(y, x)` over `y`.
[HornJohnson2013, §7.7].
Port of `NLAlib.isLeast_generalizedSchurComplement_quadratic`.
Result: schur-complement-variational -/
theorem isLeast_re_quadForm_fromBlocks [Fintype n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (x : n → 𝕜) :
    IsLeast
      (Set.range fun y : m → 𝕜 =>
        RCLike.re (quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x)))
      (RCLike.re (quadForm (C - Bᴴ * pinv A * B) x)) := by
  have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
  have hX : A * (pinv A * B) = B :=
    mul_pinv_mul_eq_aux (range_mulVecLin_le_of_posSemidef_fromBlocks h)
  have hS := conjTranspose_pinv_mul_mul_pinv_mul (B := B) hA.isHermitian
  constructor
  · refine ⟨-((pinv A * B) *ᵥ x), ?_⟩
    change RCLike.re (quadForm _ (Sum.elim (-((pinv A * B) *ᵥ x)) x)) = _
    rw [quadForm_fromBlocks_eq_add hA.isHermitian hX, neg_add_cancel, quadForm_zero_right,
      zero_add, hS]
  · rintro _ ⟨y, rfl⟩
    have hle := quadForm_sub_conjTranspose_mul_mul_le h hX y x
    rw [hS] at hle
    exact (RCLike.le_iff_re_im.mp hle).1

end NLAlib
