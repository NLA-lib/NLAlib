/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Majorization.Schur

/-!
# The Hermitian part and the real parts of the eigenvalues

The Hermitian part of a square complex matrix is `(A + Aᴴ) / 2`, written
`(2⁻¹ : ℝ) • (A + Aᴴ)`. The real parts of the eigenvalues of `A` are majorized by the eigenvalues
of its Hermitian part (Ky Fan), so they lie between its extreme eigenvalues (Bendixson), and
every majorization of this kind is realised by a matrix.

## Main results

* `NLAlib.majorized_re_of_charpoly_eq`: Ky Fan's majorization.
* `NLAlib.re_le_eigenvalue_zero_hermitianPart`, `NLAlib.eigenvalue_hermitianPart_le_re`:
  Bendixson's bounds.
* `NLAlib.exists_charpoly_eq_of_majorized_re`: the converse.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian part is Hermitian. -/
theorem isHermitian_smul_add_conjTranspose (A : Matrix n n ℂ) :
    ((2⁻¹ : ℝ) • (A + Aᴴ)).IsHermitian := by
  sorry

/-- **The real parts of the eigenvalues are majorized by the eigenvalues of the Hermitian
part** (Ky Fan). [HornJohnson1991, §3.3]; [Bhatia1997, Proposition III.5.3].
Port of `NLAlib.majorized_real_parts_eigenvalues_selfAdjointPart`.
Result: real-part-majorization -/
theorem majorized_re_of_charpoly_eq (A : Matrix n n ℂ) {z : n → ℂ} {x : n → ℝ}
    (hz : A.charpoly = ∏ i, (X - C (z i)))
    (hx : ((2⁻¹ : ℝ) • (A + Aᴴ)).charpoly = ∏ i, (X - C ((x i : ℝ) : ℂ))) :
    Majorized (fun i => (z i).re) x := by
  sorry

/-- **Bendixson's upper bound**: the real part of every eigenvalue is at most the largest
eigenvalue of the Hermitian part. [HornJohnson2013, §5.6].
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, upper half. -/
theorem re_le_eigenvalue_zero_hermitianPart {A : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A) : μ.re ≤ eigenvalue ((2⁻¹ : ℝ) • (A + Aᴴ)) 0 := by
  sorry

/-- **Bendixson's lower bound**: the real part of every eigenvalue is at least the smallest
eigenvalue of the Hermitian part.
Port of `NLAlib.real_part_eigenvalue_mem_Icc_selfAdjointPart`, lower half. -/
theorem eigenvalue_hermitianPart_le_re {A : Matrix n n ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A)
    {j : ℕ} (hj : j + 1 = Fintype.card n) : eigenvalue ((2⁻¹ : ℝ) • (A + Aᴴ)) j ≤ μ.re := by
  sorry

/-- **Every majorization of real parts is realised**: if `re z` is majorized by `x`, there is a
matrix with eigenvalues `z` whose Hermitian part has eigenvalues `x`.
[HornJohnson1991, §3.3].
Port of `NLAlib.exists_matrix_charpoly_and_selfAdjointPart_charpoly_of_majorized`. -/
theorem exists_charpoly_eq_of_majorized_re {z : n → ℂ} {x : n → ℝ}
    (h : Majorized (fun i => (z i).re) x) :
    ∃ A : Matrix n n ℂ, A.charpoly = ∏ i, (X - C (z i)) ∧
      ((2⁻¹ : ℝ) • (A + Aᴴ)).charpoly = ∏ i, (X - C ((x i : ℝ) : ℂ)) := by
  sorry

end NLAlib
