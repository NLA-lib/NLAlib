/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Elimination

/-!
# The LU factorization

`NLAlib.IsLU A L U` says that `A = L * U` with `L` unit lower triangular and `U` upper
triangular. The factorization of a nonsingular matrix is unique, and exists exactly when the
leading principal minors are nonzero; the pivots are ratios of consecutive leading minors. With a
row permutation it always exists, and partial pivoting bounds the entries of the factors.

Leading principal minors are `principalMinor A (Finset.Iic i)`.

## Main definitions

* `NLAlib.IsLU`: the factorization predicate.
* `NLAlib.luLower`, `NLAlib.luUpper`: the factors computed by elimination without pivoting, for a
  matrix indexed by `Fin n` over a field.

## Main results

* `NLAlib.IsLU.unique`, `NLAlib.IsLU.det_eq_prod`, `NLAlib.IsLU.principalMinor_eq_prod`.
* `NLAlib.exists_isLU_iff_forall_principalMinor_ne_zero`: existence for nonsingular matrices.
* `NLAlib.exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank`: existence from the leading
  minors up to the rank.
* `NLAlib.isLU_luLower_luUpper`: elimination computes the factorization.
* `NLAlib.exists_perm_isLU_norm_le`: partial pivoting, with the growth bound `2 ^ (n - 1)`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R K : Type*} {m n : Type*} [LinearOrder m] [LinearOrder n] [Fintype m] [Fintype n]

/-- `IsLU A L U`: **`A = L * U` is an LU factorization**, with `L` unit lower triangular and `U`
upper triangular. [GolubVanLoan2013, §3.2]; [HornJohnson2013, §3.5].
Port of `NLAlib.IsLU`, there over `ℝ`. -/
structure IsLU [Semiring R] (A L U : Matrix n n R) : Prop where
  /-- The left factor is unit lower triangular. -/
  isUnitLowerTriangular : IsUnitLowerTriangular L
  /-- The right factor is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The matrix is the product of the factors. -/
  eq_mul : A = L * U

section CommRing

variable [CommRing R] [DecidableEq n] {A L U : Matrix n n R}

/-- The determinant is the product of the pivots. Port of `NLAlib.IsLU.det_eq_prod`. -/
theorem IsLU.det_eq_prod (h : IsLU A L U) : A.det = ∏ i, U i i := by
  sorry

/-- A matrix with an LU factorization is nonsingular exactly when its pivots are units. -/
theorem IsLU.isUnit_det_iff (h : IsLU A L U) : IsUnit A.det ↔ ∀ i, IsUnit (U i i) := by
  sorry

/-- **Principal minors on lower sets.** For an LU factorization and a lower set `s` of indices,
the principal minor of `A` on `s` is the product of the pivots in `s`.
Port of `NLAlib.IsLU.leadingMinor_eq_prod`, there for leading blocks of a matrix on `Fin`. -/
theorem IsLU.principalMinor_eq_prod (h : IsLU A L U) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) : principalMinor A s = ∏ i ∈ s, U i i := by
  sorry

/-- The leading blocks of an LU factorization are LU factorizations of the leading blocks.
Port of `NLAlib.IsLU.leadingSubmatrix`. -/
theorem IsLU.submatrix_of_isLowerSet (h : IsLU A L U) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) :
    IsLU (A.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
      (L.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
      (U.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) := by
  sorry

/-- An LU factorization is preserved by an order isomorphism of the index type.
Port of `NLAlib.IsLU.submatrix`. -/
theorem IsLU.submatrix_orderIso (h : IsLU A L U) (e : m ≃o n) :
    IsLU (A.submatrix e e) (L.submatrix e e) (U.submatrix e e) := by
  sorry

/-- **The LU factorization of a nonsingular matrix is unique.**
[HornJohnson2013, Corollary 3.5.6]. Port of `NLAlib.IsLU.unique`. -/
theorem IsLU.unique {L' U' : Matrix n n R} (hA : IsUnit A.det) (h : IsLU A L U)
    (h' : IsLU A L' U') : L = L' ∧ U = U' := by
  sorry

end CommRing

/-! ### Existence -/

section Field

variable [Field K] [DecidableEq n] [LocallyFiniteOrderBot n]

/-- **A nonsingular matrix has an LU factorization exactly when its leading principal minors
are nonzero.** [HornJohnson2013, Corollary 3.5.5].
Port of `NLAlib.exists_isLU_iff_forall_leadingMinor_ne_zero`, there over `ℝ`.
Result: lu-existence -/
theorem exists_isLU_iff_forall_principalMinor_ne_zero {A : Matrix n n K} (hA : IsUnit A.det) :
    (∃ L U, IsLU A L U) ↔ ∀ i, principalMinor A (Finset.Iic i) ≠ 0 := by
  sorry

/-- A matrix whose proper leading principal minors are nonzero has an LU factorization.
Port of `NLAlib.exists_isLU_of_forall_leadingMinor_ne_zero`, there over `ℝ`. -/
theorem exists_isLU_of_forall_principalMinor_ne_zero (A : Matrix n n K)
    (h : ∀ i, principalMinor A (Finset.Iio i) ≠ 0) : ∃ L U, IsLU A L U := by
  sorry

/-- **A matrix whose leading principal minors up to its rank are nonzero has an LU
factorization.** [HornJohnson2013, Theorem 3.5.2].
Port of `NLAlib.exists_unit_triangular_factorizations_of_leading_minors_through_rank`. -/
theorem exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank (A : Matrix n n K)
    (h : ∀ i, (Finset.Iic i).card ≤ A.rank → principalMinor A (Finset.Iic i) ≠ 0) :
    ∃ L U, IsLU A L U := by
  sorry

/-- **Every square matrix has an LU factorization after a row permutation.**
[GolubVanLoan2013, Theorem 3.4.1 context]. Port of `NLAlib.isPLU_luPartialPivot`, as an
existence statement over any field. -/
theorem exists_perm_isLU (A : Matrix n n K) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n K), IsLU (A.submatrix σ id) L U := by
  sorry

end Field

/-- **Partial pivoting.** Every square matrix has a row-permuted LU factorization in which the
entries of `L` are at most one in absolute value and the entries of `U` exceed those of `A` by a
factor at most `2 ^ (n - 1)`. [GolubVanLoan2013, §3.4.5]; [Higham2002, §9.3].
Port of `NLAlib.exists_isPLU_abs_le_one` and `NLAlib.abs_luPartialPivot_upper_le_two_pow`.
Result: partial-pivoting-growth -/
theorem exists_perm_isLU_norm_le {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n] (A : Matrix n n 𝕜)
    {M : ℝ} (hM : ∀ i j, ‖A i j‖ ≤ M) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ id) L U ∧
      (∀ i j, ‖L i j‖ ≤ 1) ∧ ∀ i j, ‖U i j‖ ≤ 2 ^ (Fintype.card n - 1) * M := by
  sorry

/-! ### Elimination without pivoting -/

section Recursion

variable [Field K] {n : ℕ}

/-- The unit lower triangular factor computed by elimination without pivoting: column `j` holds
the multipliers of step `j`. Port of `NLAlib.lu`, first component. -/
def luLower (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if j < i then gaussState A j i j / gaussState A j j j else if i = j then 1 else 0

/-- The upper triangular factor computed by elimination without pivoting: row `i` is the pivot
row of step `i`. Port of `NLAlib.lu`, second component. -/
def luUpper (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i ≤ j then gaussState A i i j else 0

/-- The lower factor of elimination is unit lower triangular.
Port of `NLAlib.isUnitLowerTriangular_lu_fst`. -/
theorem isUnitLowerTriangular_luLower (A : Matrix (Fin n) (Fin n) K) :
    IsUnitLowerTriangular (luLower A) := by
  sorry

/-- The upper factor of elimination is upper triangular.
Port of `NLAlib.isUpperTriangular_lu_snd`. -/
theorem isUpperTriangular_luUpper (A : Matrix (Fin n) (Fin n) K) :
    (luUpper A).IsUpperTriangular := by
  sorry

/-- The diagonal of the upper factor holds the pivots. -/
@[simp]
theorem luUpper_apply_self (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    luUpper A i i = gaussState A i i i := by
  sorry

/-- **Elimination computes the LU factorization** when every pivot but the last is nonzero.
Port of `NLAlib.isLU_lu`. -/
theorem isLU_luLower_luUpper {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i : Fin n, (i : ℕ) + 1 < n → luUpper A i i ≠ 0) :
    IsLU A (luLower A) (luUpper A) := by
  sorry

/-- Elimination computes the LU factorization of a matrix whose proper leading principal minors
are nonzero. Port of `NLAlib.isLU_lu_of_forall_leadingMinor_ne_zero`. -/
theorem isLU_luLower_luUpper_of_forall_principalMinor_ne_zero {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i, principalMinor A (Finset.Iio i) ≠ 0) : IsLU A (luLower A) (luUpper A) := by
  sorry

/-- **Elimination runs without a zero pivot exactly when all leading principal minors are
nonzero.** Port of `NLAlib.luSucceeds_iff_forall_leadingMinor_ne_zero`. -/
theorem forall_luUpper_apply_self_ne_zero_iff (A : Matrix (Fin n) (Fin n) K) :
    (∀ i, luUpper A i i ≠ 0) ↔ ∀ i, principalMinor A (Finset.Iic i) ≠ 0 := by
  sorry

end Recursion

end NLAlib
