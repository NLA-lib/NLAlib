/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Basic.QuadForm

/-!
# Positive semidefinite block matrices and Schur complements

Criteria for a Hermitian block matrix `fromBlocks A B Bᴴ C` to be positive semidefinite or
positive definite. The Schur complement has no definition: with `A` invertible it is Mathlib's
`C - Bᴴ * A⁻¹ * B`, and in general it is `C - Xᴴ * A * X` for any solution `X` of `A * X = B`,
which does not depend on the solution. Mathlib has the determinant and inverse of a block matrix
and the semidefinite criterion for positive definite `A` (`Matrix.PosSemidef.fromBlocks₁₁`).

## Main results

* `NLAlib.posSemidef_fromBlocks_iff_exists`: Albert's criterion, without the pseudoinverse.
* `NLAlib.quadForm_fromBlocks_eq_add`: completing the square.
* `NLAlib.posDef_fromBlocks_iff`: the positive definite criterion.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-- **Completing the square** in a Hermitian block matrix. If `A` is Hermitian and `A * X = B`,
the quadratic form of `fromBlocks A B Bᴴ C` at `(y, x)` is the quadratic form of `A` at
`y + X x` plus the quadratic form of `C - Xᴴ * A * X` at `x`.
Port of `NLAlib.dotProduct_fromBlocks_eq_generalizedSchurComplement_square`, there with
`X = A⁺ B`. -/
theorem quadForm_fromBlocks_eq_add [Fintype m] [Fintype n] {A : Matrix m m 𝕜}
    {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hX : A * X = B) (y : m → 𝕜) (x : n → 𝕜) :
    quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x) =
      quadForm A (y + X *ᵥ x) + quadForm (C - Xᴴ * A * X) x := by
  have hAX : A *ᵥ (X *ᵥ x) = B *ᵥ x := by rw [Matrix.mulVec_mulVec, hX]
  have hXA : star (X *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ (Bᴴ *ᵥ y) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hX,
      Matrix.conjTranspose_mul, hA.eq]
  rw [quadForm_sub_left, quadForm_conjTranspose_mul_mul, quadForm_add_right, hAX, hXA]
  simp only [quadForm, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.star_sumElim, sumElim_dotProduct_sumElim, dotProduct_add, hAX]
  ring

/-- For Hermitian `A`, the matrix `Xᴴ * A * X` is the same for every solution `X` of
`A * X = B`. -/
theorem conjTranspose_mul_mul_eq_of_mul_eq [Fintype m] {A : Matrix m m 𝕜} {B X Y : Matrix m n 𝕜}
    (hA : A.IsHermitian) (hX : A * X = B) (hY : A * Y = B) : Xᴴ * A * X = Yᴴ * A * Y := by
  calc Xᴴ * A * X = Xᴴ * (A * Y) := by rw [Matrix.mul_assoc, hX, hY]
    _ = (A * X)ᴴ * Y := by rw [Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]
    _ = Yᴴ * A * Y := by rw [hX, ← hY, Matrix.conjTranspose_mul, hA.eq]

/-- In a positive semidefinite block matrix, the kernel of the leading block `A` is contained in
the kernel of `Bᴴ`. Port of `NLAlib.conjTranspose_mulVec_eq_zero_of_fromBlocks_posSemidef`. -/
theorem conjTranspose_mulVec_eq_zero_of_posSemidef_fromBlocks [Fintype m] [Finite n]
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) {z : m → 𝕜} (hz : A *ᵥ z = 0) :
    Bᴴ *ᵥ z = 0 := by
  have := Fintype.ofFinite n
  have hq : star (Sum.elim z (0 : n → 𝕜)) ⬝ᵥ
      (Matrix.fromBlocks A B Bᴴ C *ᵥ Sum.elim z (0 : n → 𝕜)) = 0 := by
    simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hz,
      Matrix.mulVec_zero, Function.star_sumElim, sumElim_dotProduct_sumElim, star_zero,
      zero_dotProduct, dotProduct_zero, add_zero]
  have hv := (h.dotProduct_mulVec_zero_iff _).mp hq
  have hr := congrArg (fun v : m ⊕ n → 𝕜 => v ∘ Sum.inr) hv
  simpa only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.mulVec_zero, add_zero, Pi.zero_comp] using hr

/-- In a positive semidefinite block matrix, the columns of the off-diagonal block `B` lie in the
column space of the leading block `A`.
Port of `NLAlib.one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef`. -/
theorem range_mulVecLin_le_of_posSemidef_fromBlocks [Fintype m] [Fintype n] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  classical
  have hA : A.IsHermitian := (h.submatrix (Sum.inl : m → m ⊕ n)).isHermitian
  have hAF : A * (1 - rangeProjector A) = 0 := by
    simpa only [hA.eq] using conjTranspose_mul_one_sub_rangeProjector A
  have hBF : Bᴴ * (1 - rangeProjector A) = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    refine conjTranspose_mulVec_eq_zero_of_posSemidef_fromBlocks h ?_
    rw [Matrix.mulVec_mulVec, hAF, Matrix.zero_mulVec]
  have hFB : (1 - rangeProjector A) * B = 0 := by
    have hc := congrArg Matrix.conjTranspose hBF
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (isStarProjection_one_sub_rangeProjector A).conjTranspose_eq,
      Matrix.conjTranspose_zero] at hc
  rw [← rangeProjector_mul_eq_self_iff]
  rw [one_sub_rangeProjector_mul, sub_eq_zero] at hFB
  exact hFB.symm

/-- **Albert's criterion.** The block matrix `fromBlocks A B Bᴴ C` is positive semidefinite
exactly when `A` is, the equation `A * X = B` has a solution, and `C - Xᴴ * A * X` is positive
semidefinite for one such solution (equivalently for all,
`NLAlib.conjTranspose_mul_mul_eq_of_mul_eq`).
[HornJohnson2013, Theorem 7.7.9]; stated there with the pseudoinverse solution `X = A⁺ B` and the
range condition `A A⁺ B = B`, here with any solution, so that no pseudoinverse is needed.
Port of `NLAlib.posSemidef_fromBlocks_iff`.
Result: schur-complement-psd, albert-theorem -/
theorem posSemidef_fromBlocks_iff_exists [Fintype m] [Finite n] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ ∃ X : Matrix m n 𝕜, A * X = B ∧ (C - Xᴴ * A * X).PosSemidef := by
  have := Fintype.ofFinite n
  constructor
  · intro h
    have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
    have hC : C.PosSemidef := h.submatrix (Sum.inr : n → m ⊕ n)
    obtain ⟨X, hX⟩ :=
      range_mulVecLin_le_iff_exists_mul.mp (range_mulVecLin_le_of_posSemidef_fromBlocks h)
    refine ⟨hA, X, hX.symm, posSemidef_iff_quadForm_nonneg.mpr ⟨hC.isHermitian.sub
      (Matrix.isHermitian_conjTranspose_mul_mul X hA.isHermitian), fun x => ?_⟩⟩
    have hx := h.quadForm_nonneg (Sum.elim (-(X *ᵥ x)) x)
    rwa [quadForm_fromBlocks_eq_add hA.isHermitian hX.symm, neg_add_cancel, quadForm_zero_right,
      zero_add] at hx
  · rintro ⟨hA, X, hX, hS⟩
    have hC : C.IsHermitian := by
      simpa only [sub_add_cancel] using
        hS.isHermitian.add (Matrix.isHermitian_conjTranspose_mul_mul X hA.isHermitian)
    refine posSemidef_iff_quadForm_nonneg.mpr ⟨hA.isHermitian.fromBlocks rfl hC, fun z => ?_⟩
    rw [← Sum.elim_comp_inl_inr z, quadForm_fromBlocks_eq_add hA.isHermitian hX]
    exact add_nonneg (hA.quadForm_nonneg _) (hS.quadForm_nonneg _)

/-- If the block matrix is positive semidefinite, then for every solution `X` of `A * X = B` the
Schur complement `C - Xᴴ * A * X` is positive semidefinite.
Port of `NLAlib.generalizedSchurComplement_nonneg`. -/
theorem posSemidef_sub_conjTranspose_mul_mul_of_posSemidef_fromBlocks [Fintype m] [Finite n]
    {A : Matrix m m 𝕜} {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (hX : A * X = B) :
    (C - Xᴴ * A * X).PosSemidef := by
  obtain ⟨hA, Y, hY, hS⟩ := posSemidef_fromBlocks_iff_exists.mp h
  rwa [conjTranspose_mul_mul_eq_of_mul_eq hA.isHermitian hX hY]

/-- **The Schur complement as a partial minimum.** In a positive semidefinite block matrix, with
`A * X = B`, the quadratic form of `C - Xᴴ * A * X` at `x` is a lower bound for the quadratic
form of the block matrix at `(y, x)`, for every `y`. Equality holds at `y = -X x`
(`NLAlib.quadForm_fromBlocks_eq_add`).
Port of `NLAlib.dotProduct_generalizedSchurComplement_mulVec_le`.
Result: schur-complement-variational -/
theorem quadForm_sub_conjTranspose_mul_mul_le [Fintype m] [Fintype n] {A : Matrix m m 𝕜}
    {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (hX : A * X = B) (y : m → 𝕜) (x : n → 𝕜) :
    quadForm (C - Xᴴ * A * X) x ≤ quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x) := by
  have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
  rw [quadForm_fromBlocks_eq_add hA.isHermitian hX]
  exact le_add_of_nonneg_left (hA.quadForm_nonneg _)

/-- The Schur complement of a positive semidefinite leading block is below `C` in the Loewner
order. Port of `NLAlib.generalizedSchurComplement_le`. -/
theorem sub_conjTranspose_mul_mul_le [Fintype m] [Finite n] {A : Matrix m m 𝕜} (hA : A.PosSemidef)
    (X : Matrix m n 𝕜) (C : Matrix n n 𝕜) : C - Xᴴ * A * X ≤ C := by
  rw [Matrix.le_iff, sub_sub_cancel]
  exact hA.conjTranspose_mul_mul_same X

/-- **Positive definite block matrices.** `fromBlocks A B Bᴴ C` is positive definite exactly when
`A` and the Schur complement `C - Bᴴ * A⁻¹ * B` are.
[HornJohnson2013, Theorem 7.7.7].
Result: schur-complement-pd -/
theorem posDef_fromBlocks_iff [Fintype m] [Finite n] [DecidableEq m] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ A.PosDef ∧ (C - Bᴴ * A⁻¹ * B).PosDef := by
  have := Fintype.ofFinite n
  have key : ∀ hA : A.PosDef, A * (A⁻¹ * B) = B ∧ (A⁻¹ * B)ᴴ * A * (A⁻¹ * B) = Bᴴ * A⁻¹ * B := by
    intro hA
    have hAB : A * (A⁻¹ * B) = B :=
      Matrix.mul_nonsing_inv_cancel_left A B ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    refine ⟨hAB, ?_⟩
    rw [Matrix.mul_assoc, hAB, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      hA.isHermitian.eq]
  constructor
  · intro h
    have hA : A.PosDef := h.submatrix (e := (Sum.inl : m → m ⊕ n)) Sum.inl_injective
    have hC : C.PosDef := h.submatrix (e := (Sum.inr : n → m ⊕ n)) Sum.inr_injective
    obtain ⟨hAB, hS⟩ := key hA
    refine ⟨hA, posDef_iff_quadForm_pos.mpr ⟨?_, fun x hx => ?_⟩⟩
    · rw [← hS]
      exact hC.isHermitian.sub (Matrix.isHermitian_conjTranspose_mul_mul _ hA.isHermitian)
    · have hne : Sum.elim (-((A⁻¹ * B) *ᵥ x)) x ≠ 0 := fun h0 =>
        hx (by
          simpa only [Sum.elim_comp_inr, Pi.zero_comp] using
            congrArg (fun v : m ⊕ n → 𝕜 => v ∘ Sum.inr) h0)
      have hpos := h.quadForm_pos hne
      rwa [quadForm_fromBlocks_eq_add hA.isHermitian hAB, neg_add_cancel, quadForm_zero_right,
        zero_add, hS] at hpos
  · rintro ⟨hA, hSd⟩
    obtain ⟨hAB, hS⟩ := key hA
    rw [← hS] at hSd
    have hC : C.IsHermitian := by
      simpa only [sub_add_cancel] using
        hSd.isHermitian.add
          (Matrix.isHermitian_conjTranspose_mul_mul (A⁻¹ * B) hA.isHermitian)
    refine posDef_iff_quadForm_pos.mpr ⟨hA.isHermitian.fromBlocks rfl hC, fun z hz => ?_⟩
    rw [← Sum.elim_comp_inl_inr z, quadForm_fromBlocks_eq_add hA.isHermitian hAB]
    rcases eq_or_ne (z ∘ Sum.inr) 0 with hx | hx
    · have hy : z ∘ Sum.inl ≠ 0 := fun hy => hz (by
        rw [← Sum.elim_comp_inl_inr z, hx, hy]
        exact Sum.elim_zero_zero)
      rw [hx, Matrix.mulVec_zero, add_zero, quadForm_zero_right, add_zero]
      exact hA.quadForm_pos hy
    · exact add_pos_of_nonneg_of_pos (hA.posSemidef.quadForm_nonneg _) (hSd.quadForm_pos hx)

end NLAlib
