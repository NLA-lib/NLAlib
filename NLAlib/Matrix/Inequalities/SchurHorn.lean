/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.Schur
public import NLAlib.Matrix.Basic.PlaneRotation
public import NLAlib.Matrix.Subspaces.Frames

/-!
# The Schur–Horn theorem

Schur's theorem says that the diagonal of a Hermitian matrix is majorized by its eigenvalues
(`NLAlib.Matrix.Majorization.Schur`). Horn's converse: every real vector majorized by `λ` is the
diagonal of a real symmetric matrix with eigenvalues `λ`. Together they describe the set of
diagonals of the unitary orbit of a Hermitian matrix.

## Main results

* `NLAlib.exists_hasOrthonormalCols_diag_eq_of_majorized`: Horn's theorem.
* `NLAlib.majorized_iff_exists_hasOrthonormalCols_diag_eq`: the Schur–Horn theorem.
* `Matrix.IsHermitian.majorized_iff_exists_diag_conj_eq`: for the orbit of a Hermitian matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal of `Q * diagonal λ * Qᴴ` is the image of `λ` under the matrix of squared moduli
of the entries of `Q`. Port of `NLAlib.diagonal_conjugation_eq_sq_mulVec`, there over `ℝ`. -/
theorem re_mul_diagonal_mul_conjTranspose_apply_self (Q : Matrix n n 𝕜) (lam : n → ℝ) (i : n) :
    RCLike.re ((Q * Matrix.diagonal (fun j => ((lam j : ℝ) : 𝕜)) * Qᴴ) i i) =
      ((Matrix.of fun i j => ‖Q i j‖ ^ 2) *ᵥ lam) i := by
  sorry

/-- **Horn's theorem.** If `d` is majorized by `λ`, there is a real orthogonal matrix `Q` such
that `Q * diagonal λ * Qᴴ` has diagonal `d`.
[HornJohnson2013, Theorem 4.3.48].
Port of `NLAlib.exists_orthogonal_diagonal_eq_of_majorized`.
Result: schur-horn -/
theorem exists_hasOrthonormalCols_diag_eq_of_majorized {d lam : n → ℝ} (h : Majorized d lam) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ (Q * Matrix.diagonal lam * Qᴴ).diag = d := by
  sorry

/-- **The Schur–Horn theorem.** A real vector `d` is majorized by `λ` exactly when it is the
diagonal of `Q * diagonal λ * Qᴴ` for some real orthogonal `Q`.
[HornJohnson2013, Theorems 4.3.45 and 4.3.48].
Port of `NLAlib.majorized_iff_exists_orthogonal_diagonal_eq`.
Result: schur-horn -/
theorem majorized_iff_exists_hasOrthonormalCols_diag_eq {d lam : n → ℝ} :
    Majorized d lam ↔
      ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ (Q * Matrix.diagonal lam * Qᴴ).diag = d := by
  sorry

/-- **The diagonals of the unitary orbit of a Hermitian matrix** are exactly the vectors
majorized by its eigenvalues.
[HornJohnson2013, Theorems 4.3.45 and 4.3.48].
Result: schur-horn -/
theorem _root_.Matrix.IsHermitian.majorized_iff_exists_diag_conj_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {d : n → ℝ} :
    Majorized d hA.eigenvalues ↔
      ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ ∀ i, (Uᴴ * A * U) i i = ((d i : ℝ) : 𝕜) := by
  sorry

end NLAlib
