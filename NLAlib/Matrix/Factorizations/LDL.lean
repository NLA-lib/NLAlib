/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU

/-!
# Unit lower triangular LDL factorization

Hermitian elimination with nonzero pivots produces a unit lower triangular factor and a
real diagonal. The diagonal is represented as a vector, and may have either sign. This
one-by-one-pivot factorization includes indefinite matrices whose elimination pivots do
not vanish; it makes no pivot-selection or two-by-two-pivot claim.

## Main results

* `NLAlib.IsLDL.isLU`: conversion to an upper factor through the real diagonal.
* `NLAlib.IsLDL.unique`: uniqueness for nonsingular input.
* `Matrix.IsHermitian.isLDL_luLower`: the factors computed by elimination satisfy the LDL identity.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [LinearOrder n] [Fintype n]

/-- `IsLDL A L d` states that a Hermitian matrix is a unit lower triangular factor times a
real diagonal times the factor's conjugate transpose. Diagonal entries may have either
sign or vanish. [GolubVanLoan2013, §4.1]. -/
structure IsLDL (A L : Matrix n n 𝕜) (d : n → 𝕜) : Prop where
  /-- The left factor has unit diagonal and is lower triangular. -/
  isUnitLowerTriangular : IsUnitLowerTriangular L
  /-- The diagonal vector is real. -/
  star_diag : ∀ i, star (d i) = d i
  /-- The original matrix is the product of the three factors. -/
  eq_mul : A = L * Matrix.diagonal d * Lᴴ

/-- An LDL factorization represents a Hermitian matrix. -/
theorem IsLDL.isHermitian {A L : Matrix n n 𝕜} {d : n → 𝕜}
    (h : IsLDL A L d) : A.IsHermitian := by
  rw [h.eq_mul]
  exact Matrix.isHermitian_mul_mul_conjTranspose L
    (Matrix.isHermitian_diagonal_iff.mpr h.star_diag)

/-- An LDL factorization also supplies a unit-lower/upper LU factorization, with upper
factor equal to the diagonal times the conjugate transpose of the lower factor. -/
theorem IsLDL.isLU {A L : Matrix n n 𝕜} {d : n → 𝕜} (h : IsLDL A L d) :
    IsLU A L (Matrix.diagonal d * Lᴴ) := by
  refine ⟨h.isUnitLowerTriangular, ?_, ?_⟩
  · exact (Matrix.blockTriangular_diagonal d).mul
      h.isUnitLowerTriangular.conjTranspose.isUpperTriangular
  · simpa only [Matrix.mul_assoc] using h.eq_mul

/-- The unit lower factor and real diagonal of an LDL factorization are unique when the
input is nonsingular. No definiteness or sign assumption on the diagonal is required. -/
theorem IsLDL.unique {A L L' : Matrix n n 𝕜} {d d' : n → 𝕜}
    (hA : IsUnit A.det) (h : IsLDL A L d) (h' : IsLDL A L' d') : L = L' ∧ d = d' := by
  obtain ⟨hL, hU⟩ := IsLU.unique hA h.isLU h'.isLU
  refine ⟨hL, funext fun i => ?_⟩
  have hd := congrArg (fun U : Matrix n n 𝕜 => U i i) hU
  simpa only [Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    h.isUnitLowerTriangular.apply_self, h'.isUnitLowerTriangular.apply_self,
    star_one, mul_one] using hd

variable {N : ℕ}

/-- For Hermitian elimination with nonzero pivots, the upper factor is the pivot diagonal
multiplied by the lower factor's conjugate transpose. [GolubVanLoan2013, §4.1]. -/
theorem _root_.Matrix.IsHermitian.luUpper_eq_diagonal_mul_conjTranspose_luLower
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hp : ∀ i : Fin N, gaussState A i i i ≠ 0) :
    luUpper A = Matrix.diagonal (fun i : Fin N => gaussState A i i i) * (luLower A)ᴴ := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  simp only [luUpper, luLower, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_pos hij.le, if_pos hij, star_div₀, (hA.gaussState i).apply,
      (hA.gaussState i).apply, mul_div_cancel₀ _ (hp i)]
  · simp only [le_refl, if_true, lt_self_iff_false, if_false, star_one, mul_one]
  · simp only [if_neg hij.not_ge, if_neg hij.not_gt, if_neg hij.ne,
      star_zero, mul_zero]

/-- The actual elimination lower factor and pivot diagonal form an LDL factorization of
any Hermitian input with nonzero elimination pivots. No positive-definiteness assumption
is needed. [GolubVanLoan2013, §4.1]. -/
theorem _root_.Matrix.IsHermitian.isLDL_luLower {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hp : ∀ i : Fin N, gaussState A i i i ≠ 0) :
    IsLDL A (luLower A) (fun i : Fin N => gaussState A i i i) := by
  refine ⟨isUnitLowerTriangular_luLower A, fun i => (hA.gaussState i).apply i i, ?_⟩
  rw [Matrix.mul_assoc, ← hA.luUpper_eq_diagonal_mul_conjTranspose_luLower hp]
  exact (isLU_luLower_luUpper (fun i _ => by simpa only [luUpper_apply_self] using hp i)).eq_mul

end NLAlib
