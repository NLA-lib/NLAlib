/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Triangular matrices and triangular solves

Triangular matrices are Mathlib's `Matrix.IsUpperTriangular` and `Matrix.IsLowerTriangular` on a
linearly ordered index type. This file adds what the factorizations need: conjugate transposes,
diagonals of products and inverses, principal submatrices, the predicates
`NLAlib.IsUnitLowerTriangular` and `NLAlib.IsUnitUpperTriangular`, the shape predicate
`NLAlib.IsUpperTrapezoidal` for rectangular matrices indexed by `Fin`, and forward and back
substitution.

## Main definitions

* `NLAlib.IsUnitLowerTriangular`, `NLAlib.IsUnitUpperTriangular`: triangular with unit diagonal.
* `NLAlib.IsUpperTrapezoidal`: zero below the main diagonal, for `Matrix (Fin m) (Fin n) R`.
* `NLAlib.forwardSubst`, `NLAlib.backSubst`: the two substitution recursions over a field.

## Main results

* `NLAlib.eq_diagonal_of_isLowerTriangular_of_isUpperTriangular`.
* `Matrix.IsUpperTriangular.inv_apply_self`: the diagonal of the inverse.
* `NLAlib.IsUnitLowerTriangular.mul`, `.inv`, `.det_eq_one`.
* `NLAlib.mulVec_forwardSubst`, `NLAlib.mulVec_backSubst`: the substitutions solve the systems.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R K : Type*} {m n : Type*} [LinearOrder m] [LinearOrder n]

/-! ### Triangular matrices -/

/-- The conjugate transpose of an upper triangular matrix is lower triangular. -/
theorem _root_.Matrix.IsUpperTriangular.conjTranspose [AddMonoid R] [StarAddMonoid R]
    {A : Matrix n n R} (h : A.IsUpperTriangular) : Aᴴ.IsLowerTriangular := by
  sorry

/-- The conjugate transpose of a lower triangular matrix is upper triangular. -/
theorem _root_.Matrix.IsLowerTriangular.conjTranspose [AddMonoid R] [StarAddMonoid R]
    {A : Matrix n n R} (h : A.IsLowerTriangular) : Aᴴ.IsUpperTriangular := by
  sorry

/-- A principal submatrix of an upper triangular matrix along a strictly monotone map is upper
triangular. -/
theorem _root_.Matrix.IsUpperTriangular.submatrix_of_strictMono [Zero R] {A : Matrix n n R}
    (h : A.IsUpperTriangular) {e : m → n} (he : StrictMono e) :
    (A.submatrix e e).IsUpperTriangular := by
  sorry

/-- A principal submatrix of a lower triangular matrix along a strictly monotone map is lower
triangular. -/
theorem _root_.Matrix.IsLowerTriangular.submatrix_of_strictMono [Zero R] {A : Matrix n n R}
    (h : A.IsLowerTriangular) {e : m → n} (he : StrictMono e) :
    (A.submatrix e e).IsLowerTriangular := by
  sorry

/-- A matrix that is both lower and upper triangular is diagonal.
Port of `NLAlib.eq_diagonal_of_isLowerTriangular_of_isUpperTriangular`, there over `ℝ`. -/
theorem eq_diagonal_of_isLowerTriangular_of_isUpperTriangular [Zero R] [DecidableEq n]
    {A : Matrix n n R} (hL : A.IsLowerTriangular) (hU : A.IsUpperTriangular) :
    A = Matrix.diagonal fun i => A i i := by
  sorry

section Fintype

variable [Fintype n]

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem _root_.Matrix.IsUpperTriangular.mul_apply_self [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  sorry

/-- The diagonal of a product of lower triangular matrices is the product of the diagonals. -/
theorem _root_.Matrix.IsLowerTriangular.mul_apply_self [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  sorry

/-- **Leading blocks of a lower-times-upper product.** For `L` lower triangular, `U` upper
triangular and a lower set `s` of indices, the principal submatrix of `L * U` on `s` is the
product of the principal submatrices. -/
theorem submatrix_mul_of_isLowerTriangular_of_isUpperTriangular [NonUnitalNonAssocSemiring R]
    {L U : Matrix n n R} (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) :
    ((L * U).submatrix (Subtype.val : s → n) (Subtype.val : s → n)) =
      L.submatrix (Subtype.val : s → n) (Subtype.val : s → n) *
        U.submatrix (Subtype.val : s → n) (Subtype.val : s → n) := by
  sorry

variable [DecidableEq n]

/-- An upper triangular matrix is invertible exactly when its diagonal entries are units.
Port of `NLAlib.isUnit_det_iff_of_isUpperTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.isUnit_det_iff [CommRing R] {A : Matrix n n R}
    (hA : A.IsUpperTriangular) : IsUnit A.det ↔ ∀ i, IsUnit (A i i) := by
  sorry

/-- A lower triangular matrix is invertible exactly when its diagonal entries are units.
Port of `NLAlib.isUnit_det_iff_of_isLowerTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.isUnit_det_iff [CommRing R] {A : Matrix n n R}
    (hA : A.IsLowerTriangular) : IsUnit A.det ↔ ∀ i, IsUnit (A i i) := by
  sorry

/-- The inverse of an upper triangular matrix is upper triangular.
Port of `NLAlib.isUpperTriangular_inv`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.inv [CommRing R] {A : Matrix n n R}
    (hA : A.IsUpperTriangular) : A⁻¹.IsUpperTriangular := by
  sorry

/-- The inverse of a lower triangular matrix is lower triangular.
Port of `NLAlib.isLowerTriangular_inv`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.inv [CommRing R] {A : Matrix n n R}
    (hA : A.IsLowerTriangular) : A⁻¹.IsLowerTriangular := by
  sorry

/-- The diagonal of the inverse of an invertible upper triangular matrix.
Port of `NLAlib.inv_apply_self_of_isUpperTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.inv_apply_self [Field K] {A : Matrix n n K}
    (hA : A.IsUpperTriangular) (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  sorry

/-- The diagonal of the inverse of an invertible lower triangular matrix.
Port of `NLAlib.inv_apply_self_of_isLowerTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.inv_apply_self [Field K] {A : Matrix n n K}
    (hA : A.IsLowerTriangular) (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  sorry

end Fintype

/-! ### Unit triangular matrices -/

/-- A matrix is **unit lower triangular** if it is lower triangular with ones on the diagonal.
Port of `NLAlib.IsUnitLowerTriangular`, there over `ℝ`. -/
structure IsUnitLowerTriangular [Zero R] [One R] (L : Matrix n n R) : Prop where
  /-- The matrix is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal entries are one. -/
  apply_self : ∀ i, L i i = 1

/-- A matrix is **unit upper triangular** if it is upper triangular with ones on the diagonal.
Port of `NLAlib.IsUnitUpperTriangular`, there over `ℝ`. -/
structure IsUnitUpperTriangular [Zero R] [One R] (U : Matrix n n R) : Prop where
  /-- The matrix is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- The diagonal entries are one. -/
  apply_self : ∀ i, U i i = 1

/-- The identity is unit lower triangular. Port of `NLAlib.isUnitLowerTriangular_one`. -/
theorem isUnitLowerTriangular_one [Zero R] [One R] [DecidableEq n] :
    IsUnitLowerTriangular (1 : Matrix n n R) := by
  sorry

/-- The identity is unit upper triangular. Port of `NLAlib.isUnitUpperTriangular_one`. -/
theorem isUnitUpperTriangular_one [Zero R] [One R] [DecidableEq n] :
    IsUnitUpperTriangular (1 : Matrix n n R) := by
  sorry

/-- The transpose of a unit lower triangular matrix is unit upper triangular.
Port of `NLAlib.isUnitUpperTriangular_transpose_iff`. -/
theorem isUnitUpperTriangular_transpose_iff [Zero R] [One R] {L : Matrix n n R} :
    IsUnitUpperTriangular Lᵀ ↔ IsUnitLowerTriangular L := by
  sorry

/-- The transpose of a unit upper triangular matrix is unit lower triangular.
Port of `NLAlib.isUnitLowerTriangular_transpose_iff`. -/
theorem isUnitLowerTriangular_transpose_iff [Zero R] [One R] {U : Matrix n n R} :
    IsUnitLowerTriangular Uᵀ ↔ IsUnitUpperTriangular U := by
  sorry

/-- The conjugate transpose of a unit lower triangular matrix is unit upper triangular. -/
theorem IsUnitLowerTriangular.conjTranspose [NonAssocSemiring R] [StarRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : IsUnitUpperTriangular Lᴴ := by
  sorry

section Fintype

variable [Fintype n] [DecidableEq n]

/-- A product of unit lower triangular matrices is unit lower triangular.
Port of `NLAlib.IsUnitLowerTriangular.mul`. -/
theorem IsUnitLowerTriangular.mul [NonAssocSemiring R] {A B : Matrix n n R}
    (hA : IsUnitLowerTriangular A) (hB : IsUnitLowerTriangular B) :
    IsUnitLowerTriangular (A * B) := by
  sorry

/-- A product of unit upper triangular matrices is unit upper triangular.
Port of `NLAlib.IsUnitUpperTriangular.mul`. -/
theorem IsUnitUpperTriangular.mul [NonAssocSemiring R] {A B : Matrix n n R}
    (hA : IsUnitUpperTriangular A) (hB : IsUnitUpperTriangular B) :
    IsUnitUpperTriangular (A * B) := by
  sorry

/-- A unit lower triangular matrix has determinant one.
Port of `NLAlib.IsUnitLowerTriangular.det_eq_one`. -/
theorem IsUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : L.det = 1 := by
  sorry

/-- A unit upper triangular matrix has determinant one.
Port of `NLAlib.IsUnitUpperTriangular.det_eq_one`. -/
theorem IsUnitUpperTriangular.det_eq_one [CommRing R] {U : Matrix n n R}
    (hU : IsUnitUpperTriangular U) : U.det = 1 := by
  sorry

/-- The inverse of a unit lower triangular matrix is unit lower triangular.
Port of `NLAlib.IsUnitLowerTriangular.inv`. -/
theorem IsUnitLowerTriangular.inv [CommRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : IsUnitLowerTriangular L⁻¹ := by
  sorry

/-- The inverse of a unit upper triangular matrix is unit upper triangular.
Port of `NLAlib.IsUnitUpperTriangular.inv`. -/
theorem IsUnitUpperTriangular.inv [CommRing R] {U : Matrix n n R}
    (hU : IsUnitUpperTriangular U) : IsUnitUpperTriangular U⁻¹ := by
  sorry

end Fintype

/-- A unit lower triangular matrix that is also upper triangular is the identity.
Port of `NLAlib.eq_one_of_isUnitLowerTriangular_of_isUpperTriangular`. -/
theorem IsUnitLowerTriangular.eq_one_of_isUpperTriangular [Zero R] [One R] [DecidableEq n]
    {A : Matrix n n R} (hL : IsUnitLowerTriangular A) (hU : A.IsUpperTriangular) : A = 1 := by
  sorry

/-! ### Upper trapezoidal matrices -/

/-- A rectangular matrix indexed by `Fin m` and `Fin n` is **upper trapezoidal** if its entries
below the main diagonal vanish. Port of `NLAlib.IsUpperTrapezoidal`. -/
def IsUpperTrapezoidal [Zero R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (j : ℕ) < (i : ℕ) → A i j = 0

/-- For a square matrix, upper trapezoidal means upper triangular.
Port of `NLAlib.isUpperTrapezoidal_iff_isUpperTriangular`. -/
theorem isUpperTrapezoidal_iff_isUpperTriangular [Zero R] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) R} : IsUpperTrapezoidal A ↔ A.IsUpperTriangular := by
  sorry

/-- The leading square block of a tall upper trapezoidal matrix is upper triangular and the rows
below it vanish. -/
theorem IsUpperTrapezoidal.isUpperTriangular_submatrix_castLE [Zero R] {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (hA : IsUpperTrapezoidal A) (h : n ≤ m) :
    (A.submatrix (Fin.castLE h) id).IsUpperTriangular ∧
      ∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → A i j = 0 := by
  sorry

/-! ### Forward and back substitution -/

section Substitution

variable [Field K] {n : ℕ}

/-- The state of forward substitution after `k` steps: the first `k` entries of the solution of
`L x = b` have been computed, the others are zero. -/
def forwardSubstState (L : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : ℕ → Fin n → K
  | 0 => 0
  | k + 1 => fun i =>
      if (i : ℕ) = k then (b i - ∑ j, L i j * forwardSubstState L b k j) / L i i
      else forwardSubstState L b k i

/-- **Forward substitution**: the solution of the lower triangular system `L x = b`, computed
from the first entry down. Port of `NLAlib.forwardSubst`, there over `ℝ`. -/
def forwardSubst (L : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : Fin n → K :=
  forwardSubstState L b n

/-- The state of back substitution after `k` steps: the last `k` entries of the solution of
`U x = b` have been computed, the others are zero. -/
def backSubstState (U : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : ℕ → Fin n → K
  | 0 => 0
  | k + 1 => fun i =>
      if (i : ℕ) + k + 1 = n then (b i - ∑ j, U i j * backSubstState U b k j) / U i i
      else backSubstState U b k i

/-- **Back substitution**: the solution of the upper triangular system `U x = b`, computed from
the last entry up. Port of `NLAlib.backSubst`, there over `ℝ`. -/
def backSubst (U : Matrix (Fin n) (Fin n) K) (b : Fin n → K) : Fin n → K :=
  backSubstState U b n

/-- Forward substitution solves a lower triangular system with nonzero diagonal.
Port of `NLAlib.mulVec_forwardSubst`. -/
theorem mulVec_forwardSubst {L : Matrix (Fin n) (Fin n) K} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → K) : L *ᵥ forwardSubst L b = b := by
  sorry

/-- Back substitution solves an upper triangular system with nonzero diagonal.
Port of `NLAlib.mulVec_backSubst`. -/
theorem mulVec_backSubst {U : Matrix (Fin n) (Fin n) K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → K) : U *ᵥ backSubst U b = b := by
  sorry

/-- Forward substitution computes the action of the inverse. -/
theorem forwardSubst_eq_inv_mulVec {L : Matrix (Fin n) (Fin n) K} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → K) : forwardSubst L b = L⁻¹ *ᵥ b := by
  sorry

/-- Back substitution computes the action of the inverse. -/
theorem backSubst_eq_inv_mulVec {U : Matrix (Fin n) (Fin n) K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → K) : backSubst U b = U⁻¹ *ᵥ b := by
  sorry

end Substitution

end NLAlib
