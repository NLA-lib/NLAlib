/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Majorization.Schur

/-!
# The Hermitian part and the real parts of the eigenvalues

The Hermitian part of a square matrix is `NLAlib.hermitianPart A = (A + Aᴴ) / 2`, Mathlib's
`selfAdjointPart ℝ A` as a matrix. The real parts of the eigenvalues of a complex matrix are
majorized by the eigenvalues of its Hermitian part (Ky Fan), so they lie between its extreme
eigenvalues (Bendixson).

## Main definitions

* `NLAlib.hermitianPart`: `(2⁻¹ : ℝ) • (A + Aᴴ)`.

## Main results

* `NLAlib.majorized_re_of_isEigenvalueListing`: Ky Fan's majorization.
* `NLAlib.re_le_eigenvalue_zero_hermitianPart`, `NLAlib.eigenvalue_hermitianPart_le_re`:
  Bendixson's bounds.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Hermitian part** of a square matrix, `(A + Aᴴ) / 2`.
[HornJohnson2013, §4.1.2]. -/
noncomputable def hermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : ℝ) • (A + Aᴴ)

/-- The Hermitian part is Mathlib's `selfAdjointPart`. -/
theorem hermitianPart_eq_selfAdjointPart (A : Matrix n n 𝕜) :
    hermitianPart A = (selfAdjointPart ℝ A : Matrix n n 𝕜) := by
  sorry

/-- The Hermitian part is Hermitian. -/
theorem isHermitian_hermitianPart (A : Matrix n n 𝕜) : (hermitianPart A).IsHermitian := by
  sorry

/-- A Hermitian matrix is its own Hermitian part. -/
theorem _root_.Matrix.IsHermitian.hermitianPart_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hermitianPart A = A := by
  sorry

/-- The quadratic form of the Hermitian part is the real part of the quadratic form. -/
theorem re_quadForm_hermitianPart (A : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (hermitianPart A) x) = RCLike.re (quadForm A x) := by
  sorry

/-- The Hermitian part commutes with unitary conjugation.
Port of `NLAlib.selfAdjointPart_mul_mul_conjTranspose`. -/
theorem hermitianPart_mul_mul_conjTranspose (U A : Matrix n n 𝕜) :
    hermitianPart (U * A * Uᴴ) = U * hermitianPart A * Uᴴ := by
  sorry

/-- **The real parts of the eigenvalues are majorized by the eigenvalues of the Hermitian
part** (Ky Fan). [HornJohnson1991, §3.3]; [Bhatia1997, Proposition III.5.3].
Port of `NLAlib.majorized_real_parts_eigenvalues_selfAdjointPart`.
Result: real-part-majorization -/
theorem majorized_re_of_isEigenvalueListing {A : Matrix n n ℂ} {z : n → ℂ} {x : n → ℝ}
    (hz : IsEigenvalueListing A z)
    (hx : IsEigenvalueListing (hermitianPart A) fun i => ((x i : ℝ) : ℂ)) :
    Majorized (fun i => (z i).re) x := by
  sorry

/-- **Bendixson's upper bound**: the real part of every eigenvalue is at most the largest
eigenvalue of the Hermitian part. [HornJohnson2013, §5.6].
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, upper half. -/
theorem re_le_eigenvalue_zero_hermitianPart {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : RCLike.re μ ≤ eigenvalue (hermitianPart A) 0 := by
  sorry

/-- **Bendixson's lower bound**: the real part of every eigenvalue is at least the smallest
eigenvalue of the Hermitian part.
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, lower half. -/
theorem eigenvalue_hermitianPart_le_re {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A)
    {j : ℕ} (hj : j + 1 = Fintype.card n) : eigenvalue (hermitianPart A) j ≤ RCLike.re μ := by
  sorry

end NLAlib
