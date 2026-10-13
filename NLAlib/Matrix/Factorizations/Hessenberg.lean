/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Factorizations.Householder

/-!
# Hessenberg and tridiagonal form

A matrix indexed by `Fin` is upper Hessenberg if it vanishes below the first subdiagonal, and
tridiagonal if it vanishes outside the three central diagonals. Every square matrix is unitarily
similar to an upper Hessenberg matrix, and every Hermitian matrix to a tridiagonal one, by a
unitary matrix that fixes the first coordinate vector. The QR iteration preserves both forms, and
an unreduced Hessenberg form is determined by the first column of the unitary factor up to
unimodular scaling (the implicit Q theorem).

The Hessenberg predicate is stated for rectangular matrices, since the Arnoldi process produces
`(k + 1) × k` Hessenberg matrices.

## Main definitions

* `NLAlib.IsUpperHessenberg`, `NLAlib.IsTridiagonal`.

## Main results

* `NLAlib.exists_isUpperHessenberg_conjTranspose_mul_mul`: reduction to Hessenberg form.
* `Matrix.IsHermitian.exists_isTridiagonal_conjTranspose_mul_mul`: reduction to tridiagonal form.
* `NLAlib.IsUpperHessenberg.exists_isQR`: a Hessenberg matrix has a QR factorization with
  Hessenberg `Q`, so `R Q` is again Hessenberg.
* `NLAlib.exists_eq_mul_diagonal_of_isUpperHessenberg`: the implicit Q theorem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {R : Type*} {m n : ℕ}

/-! ### The predicates -/

/-- A matrix indexed by `Fin m` and `Fin n` is **upper Hessenberg** if its entries below the first
subdiagonal vanish. [GolubVanLoan2013, §7.4]. Port of `NLAlib.IsUpperHessenberg`, there for
square real matrices. -/
def IsUpperHessenberg [Zero R] (H : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < (i : ℕ) → H i j = 0

/-- A square matrix indexed by `Fin n` is **tridiagonal** if its entries outside the main
diagonal and the two adjacent ones vanish. Port of `NLAlib.IsTridiagonal`. -/
def IsTridiagonal [Zero R] (T : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ) → T i j = 0

/-- An upper trapezoidal matrix is upper Hessenberg.
Port of `NLAlib.isUpperHessenberg_of_isUpperTriangular`. -/
theorem IsUpperTrapezoidal.isUpperHessenberg [Zero R] {A : Matrix (Fin m) (Fin n) R}
    (hA : IsUpperTrapezoidal A) : IsUpperHessenberg A := by
  sorry

/-- An upper triangular matrix is upper Hessenberg. -/
theorem _root_.Matrix.IsUpperTriangular.isUpperHessenberg [Zero R]
    {A : Matrix (Fin n) (Fin n) R} (hA : A.IsUpperTriangular) : IsUpperHessenberg A := by
  sorry

/-- A tridiagonal matrix is upper Hessenberg. -/
theorem IsTridiagonal.isUpperHessenberg [Zero R] {T : Matrix (Fin n) (Fin n) R}
    (hT : IsTridiagonal T) : IsUpperHessenberg T := by
  sorry

/-- A matrix is tridiagonal exactly when it and its transpose are upper Hessenberg. -/
theorem isTridiagonal_iff [Zero R] {T : Matrix (Fin n) (Fin n) R} :
    IsTridiagonal T ↔ IsUpperHessenberg T ∧ IsUpperHessenberg Tᵀ := by
  sorry

/-- A Hermitian upper Hessenberg matrix is tridiagonal.
Port of `NLAlib.IsUpperHessenberg.isTridiagonal_of_isHermitian`. -/
theorem IsUpperHessenberg.isTridiagonal {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : IsUpperHessenberg H) (h : H.IsHermitian) : IsTridiagonal H := by
  sorry

/-- An upper Hessenberg matrix times an upper triangular one is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.mul_isUpperTriangular`. -/
theorem IsUpperHessenberg.mul_isUpperTriangular [NonUnitalNonAssocSemiring R]
    {H : Matrix (Fin m) (Fin n) R} {U : Matrix (Fin n) (Fin n) R} (hH : IsUpperHessenberg H)
    (hU : U.IsUpperTriangular) : IsUpperHessenberg (H * U) := by
  sorry

/-- An upper triangular matrix times an upper Hessenberg one is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.isUpperTriangular_mul`. -/
theorem IsUpperHessenberg.isUpperTriangular_mul [NonUnitalNonAssocSemiring R]
    {U : Matrix (Fin m) (Fin m) R} {H : Matrix (Fin m) (Fin n) R} (hU : U.IsUpperTriangular)
    (hH : IsUpperHessenberg H) : IsUpperHessenberg (U * H) := by
  sorry

/-- A shift of an upper Hessenberg matrix is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.sub_smul_one`. -/
theorem IsUpperHessenberg.sub_smul_one [Ring R] {H : Matrix (Fin n) (Fin n) R}
    (hH : IsUpperHessenberg H) (μ : R) : IsUpperHessenberg (H - μ • (1 : Matrix _ _ R)) := by
  sorry

/-! ### Reduction -/

/-- **Reduction to Hessenberg form.** Every square matrix is unitarily similar to an upper
Hessenberg matrix, by a unitary matrix whose first column is the first coordinate vector.
[GolubVanLoan2013, §7.4.3]; [HornJohnson2013, §2.5].
Port of `NLAlib.exists_isHessenbergForm`, which the prototype leaves unproved.
Result: hessenberg-reduction -/
theorem exists_isUpperHessenberg_conjTranspose_mul_mul (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols Q ∧ IsUpperHessenberg (Qᴴ * A * Q) ∧
      ∀ i : Fin n, (i : ℕ) = 0 → Q.col i = Pi.single i 1 := by
  sorry

/-- **Reduction to tridiagonal form.** Every Hermitian matrix is unitarily similar to a
Hermitian tridiagonal matrix. [GolubVanLoan2013, §8.3.1].
Port of `NLAlib.IsHessenbergForm.isTridiagonal`. -/
theorem _root_.Matrix.IsHermitian.exists_isTridiagonal_conjTranspose_mul_mul
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols Q ∧ IsTridiagonal (Qᴴ * A * Q) ∧
      ∀ i : Fin n, (i : ℕ) = 0 → Q.col i = Pi.single i 1 := by
  sorry

/-! ### The QR iteration -/

/-- **A Hessenberg matrix has a QR factorization with a Hessenberg unitary factor.** No rank
assumption is made.
[GolubVanLoan2013, §5.2.5]. Port of `NLAlib.isQR_givensQR` with
`NLAlib.isUpperHessenberg_givensQR_fst`, which the prototype leaves unproved. -/
theorem IsUpperHessenberg.exists_isQR {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : IsUpperHessenberg H) : ∃ Q R, IsQR H Q R ∧ IsUpperHessenberg Q := by
  sorry

/-- A step of the QR iteration with a Hessenberg unitary factor keeps the Hessenberg form.
Port of `NLAlib.isUpperHessenberg_givensQR_snd_mul_fst`. -/
theorem IsQR.isUpperHessenberg_mul {H Q R : Matrix (Fin n) (Fin n) 𝕜} (h : IsQR H Q R)
    (hQ : IsUpperHessenberg Q) : IsUpperHessenberg (R * Q) := by
  sorry

/-- For a nonsingular Hessenberg matrix the unitary factor of any QR factorization is
Hessenberg. Port of `NLAlib.isUpperHessenberg_mul_of_isQR`. -/
theorem IsQR.isUpperHessenberg_of_isUpperHessenberg {H Q R : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsQR H Q R) (hH : IsUpperHessenberg H) (hR : ∀ i, R i i ≠ 0) :
    IsUpperHessenberg Q := by
  sorry

/-- **The QR iteration preserves tridiagonal Hermitian matrices.**
[GolubVanLoan2013, §8.3.3]. Port of `NLAlib.isTridiagonal_mul_of_isQR`. -/
theorem IsQR.isTridiagonal_mul {H Q R : Matrix (Fin n) (Fin n) 𝕜} (h : IsQR H Q R)
    (hH : H.IsHermitian) (hT : IsTridiagonal H) (hQ : IsUpperHessenberg Q) :
    IsTridiagonal (R * Q) := by
  sorry

/-! ### The implicit Q theorem -/

/-- **The implicit Q theorem.** If `Q₁ᴴ A Q₁ = H₁` and `Q₂ᴴ A Q₂ = H₂` are upper Hessenberg with
`Q₁`, `Q₂` unitary with the same first column, and the subdiagonal of `H₁` has no zero, then
`Q₂ = Q₁ D` and `H₂ = Dᴴ H₁ D` for a diagonal `D` of unit modulus with first entry one.
[GolubVanLoan2013, Theorem 7.4.2].
Port of `NLAlib.IsHessenbergForm.exists_sign`, which the prototype leaves unproved.
Result: implicit-q -/
theorem exists_eq_mul_diagonal_of_isUpperHessenberg {A Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hQ₁ : HasOrthonormalCols Q₁) (hQ₂ : HasOrthonormalCols Q₂)
    (hH₁ : IsUpperHessenberg (Q₁ᴴ * A * Q₁)) (hH₂ : IsUpperHessenberg (Q₂ᴴ * A * Q₂))
    (hcol : Q₁.col 0 = Q₂.col 0)
    (hsub : ∀ i j : Fin (n + 1), (i : ℕ) = j + 1 → (Q₁ᴴ * A * Q₁) i j ≠ 0) :
    ∃ d : Fin (n + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ Q₂ = Q₁ * Matrix.diagonal d ∧
      Q₂ᴴ * A * Q₂ = Matrix.diagonal (star d) * (Q₁ᴴ * A * Q₁) * Matrix.diagonal d := by
  sorry

end NLAlib
