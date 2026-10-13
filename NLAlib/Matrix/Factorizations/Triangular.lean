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
* `Matrix.IsLowerTriangular.submatrix_mul_of_isLowerSet`,
  `Matrix.IsUpperTriangular.submatrix_mul_of_isLowerSet`: principal blocks of a product on a
  lower set.
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
  intro i j hij
  rw [Matrix.conjTranspose_apply, h (i := j) (j := i) hij, star_zero]

/-- The conjugate transpose of a lower triangular matrix is upper triangular. -/
theorem _root_.Matrix.IsLowerTriangular.conjTranspose [AddMonoid R] [StarAddMonoid R]
    {A : Matrix n n R} (h : A.IsLowerTriangular) : Aᴴ.IsUpperTriangular := by
  intro i j hij
  rw [Matrix.conjTranspose_apply, h (i := j) (j := i) hij, star_zero]

/-- A principal submatrix of an upper triangular matrix along a strictly monotone map is upper
triangular. -/
theorem _root_.Matrix.IsUpperTriangular.submatrix_of_strictMono [Zero R] {A : Matrix n n R}
    (h : A.IsUpperTriangular) {e : m → n} (he : StrictMono e) :
    (A.submatrix e e).IsUpperTriangular := by
  exact fun i j hij => h (he hij)

/-- A principal submatrix of a lower triangular matrix along a strictly monotone map is lower
triangular. -/
theorem _root_.Matrix.IsLowerTriangular.submatrix_of_strictMono [Zero R] {A : Matrix n n R}
    (h : A.IsLowerTriangular) {e : m → n} (he : StrictMono e) :
    (A.submatrix e e).IsLowerTriangular := by
  exact fun i j hij => h (i := e i) (j := e j) (he (OrderDual.toDual_lt_toDual.mp hij))

/-- A matrix that is both lower and upper triangular is diagonal.
Port of `NLAlib.eq_diagonal_of_isLowerTriangular_of_isUpperTriangular`, there over `ℝ`. -/
theorem eq_diagonal_of_isLowerTriangular_of_isUpperTriangular [Zero R] [DecidableEq n]
    {A : Matrix n n R} (hL : A.IsLowerTriangular) (hU : A.IsUpperTriangular) :
    A = Matrix.diagonal fun i => A i i := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hL (i := i) (j := j) h, Matrix.diagonal_apply_ne _ h.ne]
  · rw [Matrix.diagonal_apply_eq]
  · rw [hU (i := i) (j := j) h, Matrix.diagonal_apply_ne _ h.ne']

section Fintype

variable [Fintype n]

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem _root_.Matrix.IsUpperTriangular.mul_apply_self [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hA (i := i) (j := k) h, zero_mul]
    · rw [hB (i := k) (j := i) h, mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

/-- The diagonal of a product of lower triangular matrices is the product of the diagonals. -/
theorem _root_.Matrix.IsLowerTriangular.mul_apply_self [NonUnitalNonAssocSemiring R]
    {A B : Matrix n n R} (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB (i := k) (j := i) h, mul_zero]
    · rw [hA (i := i) (j := k) h, zero_mul]
  · exact fun h => absurd (Finset.mem_univ i) h

/-- **Leading blocks of a product with a lower triangular left factor.** For `L` lower
triangular, any `B`, and a lower set `s` of indices, the principal submatrix of `L * B` on `s` is
the product of the principal submatrices. With `B` upper triangular these are the leading blocks
of an LU factorization. -/
theorem _root_.Matrix.IsLowerTriangular.submatrix_mul_of_isLowerSet [NonUnitalNonAssocSemiring R]
    {L : Matrix n n R} (hL : L.IsLowerTriangular) (B : Matrix n n R) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) :
    ((L * B).submatrix (Subtype.val : s → n) (Subtype.val : s → n)) =
      L.submatrix (Subtype.val : s → n) (Subtype.val : s → n) *
        B.submatrix (Subtype.val : s → n) (Subtype.val : s → n) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Finset.sum_coe_sort s (fun k => L i k * B k j)]
  refine (Finset.sum_subset (Finset.subset_univ s) fun k _ hk => ?_).symm
  have hik : (i : n) < k :=
    lt_of_not_ge fun hki => hk (Finset.mem_coe.mp (hs hki (Finset.mem_coe.mpr i.2)))
  rw [hL (i := (i : n)) (j := k) hik, zero_mul]

/-- **Leading blocks of a product with an upper triangular right factor.** For any `A`, `U`
upper triangular, and a lower set `s` of indices, the principal submatrix of `A * U` on `s` is
the product of the principal submatrices. -/
theorem _root_.Matrix.IsUpperTriangular.submatrix_mul_of_isLowerSet [NonUnitalNonAssocSemiring R]
    {U : Matrix n n R} (hU : U.IsUpperTriangular) (A : Matrix n n R) {s : Finset n}
    (hs : IsLowerSet (s : Set n)) :
    ((A * U).submatrix (Subtype.val : s → n) (Subtype.val : s → n)) =
      A.submatrix (Subtype.val : s → n) (Subtype.val : s → n) *
        U.submatrix (Subtype.val : s → n) (Subtype.val : s → n) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Finset.sum_coe_sort s (fun k => A i k * U k j)]
  refine (Finset.sum_subset (Finset.subset_univ s) fun k _ hk => ?_).symm
  have hjk : (j : n) < k :=
    lt_of_not_ge fun hkj => hk (Finset.mem_coe.mp (hs hkj (Finset.mem_coe.mpr j.2)))
  rw [hU (i := k) (j := (j : n)) hjk, mul_zero]

variable [DecidableEq n]

/-- An upper triangular matrix is invertible exactly when its diagonal entries are units.
Port of `NLAlib.isUnit_det_iff_of_isUpperTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.isUnit_det_iff [CommRing R] {A : Matrix n n R}
    (hA : A.IsUpperTriangular) : IsUnit A.det ↔ ∀ i, IsUnit (A i i) := by
  rw [Matrix.det_of_isUpperTriangular hA, IsUnit.prod_univ_iff]

/-- A lower triangular matrix is invertible exactly when its diagonal entries are units.
Port of `NLAlib.isUnit_det_iff_of_isLowerTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.isUnit_det_iff [CommRing R] {A : Matrix n n R}
    (hA : A.IsLowerTriangular) : IsUnit A.det ↔ ∀ i, IsUnit (A i i) := by
  rw [Matrix.det_of_isLowerTriangular A hA, IsUnit.prod_univ_iff]

/-- The inverse of an upper triangular matrix is upper triangular.
Port of `NLAlib.isUpperTriangular_inv`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.inv [CommRing R] {A : Matrix n n R}
    (hA : A.IsUpperTriangular) : A⁻¹.IsUpperTriangular := by
  by_cases h : IsUnit A.det
  · let := A.invertibleOfIsUnitDet h
    exact Matrix.blockTriangular_inv_of_blockTriangular hA
  · rw [Matrix.nonsing_inv_apply_not_isUnit A h]
    exact Matrix.blockTriangular_zero

/-- The inverse of a lower triangular matrix is lower triangular.
Port of `NLAlib.isLowerTriangular_inv`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.inv [CommRing R] {A : Matrix n n R}
    (hA : A.IsLowerTriangular) : A⁻¹.IsLowerTriangular := by
  by_cases h : IsUnit A.det
  · let := A.invertibleOfIsUnitDet h
    exact Matrix.blockTriangular_inv_of_blockTriangular hA
  · rw [Matrix.nonsing_inv_apply_not_isUnit A h]
    exact Matrix.blockTriangular_zero

/-- The diagonal of the inverse of an invertible upper triangular matrix.
Port of `NLAlib.inv_apply_self_of_isUpperTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsUpperTriangular.inv_apply_self [Field K] {A : Matrix n n K}
    (hA : A.IsUpperTriangular) (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  have hu : IsUnit A.det :=
    (Matrix.IsUpperTriangular.isUnit_det_iff hA).2 fun j => (hd j).isUnit
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i) i
  rw [Matrix.IsUpperTriangular.mul_apply_self hA (Matrix.IsUpperTriangular.inv hA),
    Matrix.one_apply_eq] at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- The diagonal of the inverse of an invertible lower triangular matrix.
Port of `NLAlib.inv_apply_self_of_isLowerTriangular`, there over `ℝ`. -/
theorem _root_.Matrix.IsLowerTriangular.inv_apply_self [Field K] {A : Matrix n n K}
    (hA : A.IsLowerTriangular) (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  have hu : IsUnit A.det :=
    (Matrix.IsLowerTriangular.isUnit_det_iff hA).2 fun j => (hd j).isUnit
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i) i
  rw [Matrix.IsLowerTriangular.mul_apply_self hA (Matrix.IsLowerTriangular.inv hA),
    Matrix.one_apply_eq] at h1
  exact eq_inv_of_mul_eq_one_right h1

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
  exact ⟨Matrix.blockTriangular_one, fun _ => Matrix.one_apply_eq _⟩

/-- The identity is unit upper triangular. Port of `NLAlib.isUnitUpperTriangular_one`. -/
theorem isUnitUpperTriangular_one [Zero R] [One R] [DecidableEq n] :
    IsUnitUpperTriangular (1 : Matrix n n R) := by
  exact ⟨Matrix.blockTriangular_one, fun _ => Matrix.one_apply_eq _⟩

/-- The transpose of a unit lower triangular matrix is unit upper triangular.
Port of `NLAlib.isUnitUpperTriangular_transpose_iff`. -/
theorem isUnitUpperTriangular_transpose_iff [Zero R] [One R] {L : Matrix n n R} :
    IsUnitUpperTriangular Lᵀ ↔ IsUnitLowerTriangular L := by
  exact ⟨fun h => ⟨fun i j hij => h.1 (i := j) (j := i) hij, h.2⟩,
    fun h => ⟨fun i j hij => h.1 (i := j) (j := i) hij, h.2⟩⟩

/-- The conjugate transpose of a unit lower triangular matrix is unit upper triangular. -/
theorem IsUnitLowerTriangular.conjTranspose [NonAssocSemiring R] [StarRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : IsUnitUpperTriangular Lᴴ := by
  exact ⟨Matrix.IsLowerTriangular.conjTranspose hL.1, fun i => by
    rw [Matrix.conjTranspose_apply, hL.2, star_one]⟩

section Fintype

variable [Fintype n]

/-- A product of unit lower triangular matrices is unit lower triangular.
Port of `NLAlib.IsUnitLowerTriangular.mul`. -/
theorem IsUnitLowerTriangular.mul [NonAssocSemiring R] {A B : Matrix n n R}
    (hA : IsUnitLowerTriangular A) (hB : IsUnitLowerTriangular B) :
    IsUnitLowerTriangular (A * B) := by
  exact ⟨Matrix.BlockTriangular.mul hA.1 hB.1, fun i => by
    rw [Matrix.IsLowerTriangular.mul_apply_self hA.1 hB.1, hA.2, hB.2, one_mul]⟩

/-- A product of unit upper triangular matrices is unit upper triangular.
Port of `NLAlib.IsUnitUpperTriangular.mul`. -/
theorem IsUnitUpperTriangular.mul [NonAssocSemiring R] {A B : Matrix n n R}
    (hA : IsUnitUpperTriangular A) (hB : IsUnitUpperTriangular B) :
    IsUnitUpperTriangular (A * B) := by
  exact ⟨Matrix.BlockTriangular.mul hA.1 hB.1, fun i => by
    rw [Matrix.IsUpperTriangular.mul_apply_self hA.1 hB.1, hA.2, hB.2, one_mul]⟩

variable [DecidableEq n]

/-- A unit lower triangular matrix has determinant one.
Port of `NLAlib.IsUnitLowerTriangular.det_eq_one`. -/
theorem IsUnitLowerTriangular.det_eq_one [CommRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L hL.1]
  exact Finset.prod_eq_one fun i _ => hL.2 i

/-- A unit upper triangular matrix has determinant one.
Port of `NLAlib.IsUnitUpperTriangular.det_eq_one`. -/
theorem IsUnitUpperTriangular.det_eq_one [CommRing R] {U : Matrix n n R}
    (hU : IsUnitUpperTriangular U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hU.1]
  exact Finset.prod_eq_one fun i _ => hU.2 i

/-- The inverse of a unit lower triangular matrix is unit lower triangular.
Port of `NLAlib.IsUnitLowerTriangular.inv`. -/
theorem IsUnitLowerTriangular.inv [CommRing R] {L : Matrix n n R}
    (hL : IsUnitLowerTriangular L) : IsUnitLowerTriangular L⁻¹ := by
  have hu : IsUnit L.det := by rw [hL.det_eq_one]; exact isUnit_one
  refine ⟨Matrix.IsLowerTriangular.inv hL.1, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
  rwa [Matrix.IsLowerTriangular.mul_apply_self hL.1 (Matrix.IsLowerTriangular.inv hL.1),
    Matrix.one_apply_eq, hL.2, one_mul] at h1

/-- The inverse of a unit upper triangular matrix is unit upper triangular.
Port of `NLAlib.IsUnitUpperTriangular.inv`. -/
theorem IsUnitUpperTriangular.inv [CommRing R] {U : Matrix n n R}
    (hU : IsUnitUpperTriangular U) : IsUnitUpperTriangular U⁻¹ := by
  have hu : IsUnit U.det := by rw [hU.det_eq_one]; exact isUnit_one
  refine ⟨Matrix.IsUpperTriangular.inv hU.1, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv U hu) i) i
  rwa [Matrix.IsUpperTriangular.mul_apply_self hU.1 (Matrix.IsUpperTriangular.inv hU.1),
    Matrix.one_apply_eq, hU.2, one_mul] at h1

end Fintype

/-- A unit lower triangular matrix that is also upper triangular is the identity.
Port of `NLAlib.eq_one_of_isUnitLowerTriangular_of_isUpperTriangular`. -/
theorem IsUnitLowerTriangular.eq_one_of_isUpperTriangular [Zero R] [One R] [DecidableEq n]
    {A : Matrix n n R} (hL : IsUnitLowerTriangular A) (hU : A.IsUpperTriangular) : A = 1 := by
  calc A = Matrix.diagonal fun i => A i i :=
        eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hL.1 hU
    _ = Matrix.diagonal fun _ => 1 := congrArg _ (funext hL.2)
    _ = 1 := Matrix.diagonal_one

/-! ### Upper trapezoidal matrices -/

/-- A rectangular matrix indexed by `Fin m` and `Fin n` is **upper trapezoidal** if its entries
below the main diagonal vanish. Port of `NLAlib.IsUpperTrapezoidal`. -/
def IsUpperTrapezoidal [Zero R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (j : ℕ) < (i : ℕ) → A i j = 0

/-- For a square matrix, upper trapezoidal means upper triangular.
Port of `NLAlib.isUpperTrapezoidal_iff_isUpperTriangular`. -/
theorem isUpperTrapezoidal_iff_isUpperTriangular [Zero R] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) R} : IsUpperTrapezoidal A ↔ A.IsUpperTriangular := by
  exact ⟨fun h i j hij => h i j (Fin.lt_def.mp hij), fun h i j hij => h (Fin.lt_def.mpr hij)⟩

/-- The leading square block of a tall upper trapezoidal matrix is upper triangular. -/
theorem IsUpperTrapezoidal.isUpperTriangular_submatrix_castLE [Zero R] {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (hA : IsUpperTrapezoidal A) (h : n ≤ m) :
    (A.submatrix (Fin.castLE h) id).IsUpperTriangular := by
  exact fun i j hij => hA (Fin.castLE h i) j (Fin.lt_def.mp hij)

/-- The rows of an upper trapezoidal matrix beyond the number of columns vanish. -/
theorem IsUpperTrapezoidal.apply_eq_zero_of_le [Zero R] {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (hA : IsUpperTrapezoidal A) {i : Fin m} (hi : n ≤ (i : ℕ))
    (j : Fin n) : A i j = 0 := by
  exact hA i j (j.2.trans_le hi)

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

private theorem forwardSubstState_succ (L : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (k : ℕ)
    (i : Fin n) :
    forwardSubstState L b (k + 1) i =
      if (i : ℕ) = k then (b i - ∑ j, L i j * forwardSubstState L b k j) / L i i
      else forwardSubstState L b k i :=
  rfl

private theorem backSubstState_succ (U : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (k : ℕ)
    (i : Fin n) :
    backSubstState U b (k + 1) i =
      if (i : ℕ) + k + 1 = n then (b i - ∑ j, U i j * backSubstState U b k j) / U i i
      else backSubstState U b k i :=
  rfl

/-- The entries not yet computed by forward substitution are zero. -/
private theorem forwardSubstState_apply_of_le (L : Matrix (Fin n) (Fin n) K) (b : Fin n → K)
    {k : ℕ} {i : Fin n} (hi : k ≤ (i : ℕ)) : forwardSubstState L b k i = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [forwardSubstState_succ, if_neg (by omega)]
    exact ih (by omega)

/-- After `k` steps of forward substitution the first `k` equations hold. -/
private theorem mulVec_forwardSubstState {L : Matrix (Fin n) (Fin n) K}
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) (b : Fin n → K) (k : ℕ) (i : Fin n)
    (hi : (i : ℕ) < k) : (L *ᵥ forwardSubstState L b k) i = b i := by
  induction k with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    simp only [Matrix.mulVec, dotProduct] at ih ⊢
    by_cases hik : (i : ℕ) = k
    · have hx : ∀ j, L i j * forwardSubstState L b (k + 1) j =
          L i j * forwardSubstState L b k j +
            if j = i then b i - ∑ j, L i j * forwardSubstState L b k j else 0 := by
        intro j
        rw [forwardSubstState_succ]
        by_cases hji : j = i
        · subst hji
          rw [if_pos hik, if_pos rfl, forwardSubstState_apply_of_le L b hik.ge, mul_zero,
            zero_add, mul_div_cancel₀ _ (hd j)]
        · rw [if_neg (fun h => hji (Fin.ext (h.trans hik.symm))), if_neg hji, add_zero]
      rw [Finset.sum_congr rfl fun j _ => hx j, Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ i), add_sub_cancel]
    · rw [← ih (by omega)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [forwardSubstState_succ]
      by_cases hjk : (j : ℕ) = k
      · rw [hL (i := i) (j := j) (show i < j from Fin.lt_def.mpr (by omega)), zero_mul, zero_mul]
      · rw [if_neg hjk]

/-- Back substitution is forward substitution on the index-reversed system. -/
private theorem backSubstState_eq (U : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (k : ℕ) :
    backSubstState U b k =
      forwardSubstState (U.submatrix Fin.rev Fin.rev) (b ∘ Fin.rev) k ∘ Fin.rev := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    have hiff : ((i : ℕ) + k + 1 = n) ↔ ((Fin.rev i : ℕ) = k) := by
      rw [Fin.val_rev]
      omega
    have hsum : ∑ j, U i j * (forwardSubstState (U.submatrix Fin.rev Fin.rev) (b ∘ Fin.rev) k ∘
          Fin.rev) j =
        ∑ j, U i j.rev * forwardSubstState (U.submatrix Fin.rev Fin.rev) (b ∘ Fin.rev) k j :=
      Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp
    rw [Function.comp_apply, forwardSubstState_succ, backSubstState_succ, ih, hsum]
    simp only [hiff, Matrix.submatrix_apply, Function.comp_apply, Fin.rev_rev]

/-- Forward substitution solves a lower triangular system with nonzero diagonal.
Port of `NLAlib.mulVec_forwardSubst`. -/
theorem mulVec_forwardSubst {L : Matrix (Fin n) (Fin n) K} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → K) : L *ᵥ forwardSubst L b = b := by
  exact funext fun i => mulVec_forwardSubstState hL hd b n i i.2

/-- Back substitution solves an upper triangular system with nonzero diagonal.
Port of `NLAlib.mulVec_backSubst`. -/
theorem mulVec_backSubst {U : Matrix (Fin n) (Fin n) K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → K) : U *ᵥ backSubst U b = b := by
  have hL : (U.submatrix Fin.rev Fin.rev).IsLowerTriangular :=
    fun i j hij => hU (i := i.rev) (j := j.rev) (Fin.rev_lt_rev.2 hij)
  have h := mulVec_forwardSubst hL (fun i => hd i.rev) (b ∘ Fin.rev)
  ext i
  have hi := congrFun h i.rev
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply,
    Fin.rev_rev] at hi
  rw [← hi]
  simp only [backSubst, backSubstState_eq, forwardSubst, Matrix.mulVec, dotProduct,
    Function.comp_apply]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp).symm

/-- Forward substitution computes the action of the inverse. -/
theorem forwardSubst_eq_inv_mulVec {L : Matrix (Fin n) (Fin n) K} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → K) : forwardSubst L b = L⁻¹ *ᵥ b := by
  have hu : IsUnit L.det :=
    (Matrix.IsLowerTriangular.isUnit_det_iff hL).2 fun i => (hd i).isUnit
  calc forwardSubst L b = (L⁻¹ * L) *ᵥ forwardSubst L b := by
        rw [Matrix.nonsing_inv_mul L hu, Matrix.one_mulVec]
    _ = L⁻¹ *ᵥ (L *ᵥ forwardSubst L b) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = L⁻¹ *ᵥ b := by rw [mulVec_forwardSubst hL hd b]

/-- Back substitution computes the action of the inverse. -/
theorem backSubst_eq_inv_mulVec {U : Matrix (Fin n) (Fin n) K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → K) : backSubst U b = U⁻¹ *ᵥ b := by
  have hu : IsUnit U.det :=
    (Matrix.IsUpperTriangular.isUnit_det_iff hU).2 fun i => (hd i).isUnit
  calc backSubst U b = (U⁻¹ * U) *ᵥ backSubst U b := by
        rw [Matrix.nonsing_inv_mul U hu, Matrix.one_mulVec]
    _ = U⁻¹ *ᵥ (U *ᵥ backSubst U b) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = U⁻¹ *ᵥ b := by rw [mulVec_backSubst hU hd b]

end Substitution

end NLAlib
