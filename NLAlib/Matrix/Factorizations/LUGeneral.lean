/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU

/-!
# Elimination with zero pivots, and partial pivoting row by row

Elimination without pivoting, `NLAlib.luLower` and `NLAlib.luUpper`, factors a matrix as soon as
every zero pivot has only zeros below it (`NLAlib.eq_luLower_mul_luUpper`); nonzero pivots are
not needed. This file states that as a realisation theorem for `NLAlib.IsLU`, and specialises it
to partial pivoting, where every pivot is largest in absolute value among the entries below it:
then the multipliers are at most one and row `i` of the upper factor grows by at most `2 ^ i`.

## Main results

* `NLAlib.isLU_luLower_luUpper_of_forall_eq_zero`: elimination computes the LU factorization
  when every zero pivot has zeros below it.
* `NLAlib.isLU_luLower_luUpper_of_forall_norm_le`, `NLAlib.norm_luLower_apply_le_one`,
  `NLAlib.norm_luUpper_apply_le`: the factors computed with pivots of largest absolute value.
* `NLAlib.exists_perm_isLU_luLower_luUpper_norm_le`: partial pivoting with the row-wise growth
  bound `2 ^ i`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {K : Type*} [Field K] {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- **Elimination computes the LU factorization when every zero pivot has zeros below it.**
This covers singular matrices; `NLAlib.isLU_luLower_luUpper` is the case of nonzero pivots. -/
theorem isLU_luLower_luUpper_of_forall_eq_zero {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ j i : Fin n, j < i → gaussState A j j j = 0 → gaussState A j i j = 0) :
    IsLU A (luLower A) (luUpper A) :=
  ⟨isUnitLowerTriangular_luLower A, isUpperTriangular_luUpper A, eq_luLower_mul_luUpper h⟩

/-- Elimination computes the LU factorization when every pivot is largest in absolute value
among the entries below it, as after the row exchanges of partial pivoting. -/
theorem isLU_luLower_luUpper_of_forall_norm_le {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) :
    IsLU B (luLower B) (luUpper B) := by
  refine isLU_luLower_luUpper_of_forall_eq_zero fun j i hji hj => ?_
  have h := hB j i hji.le
  rw [hj, norm_zero] at h
  exact norm_le_zero_iff.mp h

/-- With pivots of largest absolute value, the multipliers are at most one in absolute value.
[GolubVanLoan2013, §3.4.5]. -/
theorem norm_luLower_apply_le_one {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) (i j : Fin n) :
    ‖luLower B i j‖ ≤ 1 := by
  simp only [luLower, Matrix.of_apply]
  split_ifs with h1 h2
  · rw [norm_div]
    exact div_le_one_of_le₀ (hB j i h1.le) (norm_nonneg _)
  · rw [norm_one]
  · rw [norm_zero]
    exact zero_le_one

/-- **Row-wise growth with partial pivoting.** With pivots of largest absolute value, the
entries of row `i` of the upper factor exceed those of the matrix by a factor at most `2 ^ i`.
[Higham2002, §9.3]; there as the growth factor bound `2 ^ (n - 1)`, which is the last row. -/
theorem norm_luUpper_apply_le {B : Matrix (Fin n) (Fin n) 𝕜} {M : ℝ}
    (hM : ∀ i j, ‖B i j‖ ≤ M)
    (hB : ∀ j i : Fin n, j ≤ i → ‖gaussState B j i j‖ ≤ ‖gaussState B j j j‖) (i j : Fin n) :
    ‖luUpper B i j‖ ≤ 2 ^ (i : ℕ) * M := by
  simp only [luUpper, Matrix.of_apply]
  split_ifs with h1
  · exact norm_gaussState_apply_le hM hB i i j le_rfl
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg zero_le_two _) ((norm_nonneg _).trans (hM i j))

/-- **Partial pivoting, row by row.** Every square matrix indexed by `Fin n` has a row
permutation after which elimination computes an LU factorization whose multipliers are at most
one in absolute value and whose upper factor has row `i` bounded by `2 ^ i` times the largest
entry of the matrix. [GolubVanLoan2013, §3.4.5]; [Higham2002, §9.3].
`NLAlib.exists_perm_isLU_norm_le` is the uniform bound on any linearly ordered index type. -/
theorem exists_perm_isLU_luLower_luUpper_norm_le (A : Matrix (Fin n) (Fin n) 𝕜) {M : ℝ}
    (hM : ∀ i j, ‖A i j‖ ≤ M) :
    ∃ σ : Equiv.Perm (Fin n),
      IsLU (A.submatrix σ id) (luLower (A.submatrix σ id)) (luUpper (A.submatrix σ id)) ∧
      (∀ i j, ‖luLower (A.submatrix σ id) i j‖ ≤ 1) ∧
      ∀ i j : Fin n, ‖luUpper (A.submatrix σ id) i j‖ ≤ 2 ^ (i : ℕ) * M := by
  obtain ⟨σ, hσ⟩ := exists_perm_forall_weight_gaussState_le (fun x : 𝕜 => ‖x‖) A
  exact ⟨σ, isLU_luLower_luUpper_of_forall_norm_le hσ, norm_luLower_apply_le_one hσ,
    norm_luUpper_apply_le (fun a b => hM (σ a) b) hσ⟩

end NLAlib
