/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.DoublyStochastic
public import NLAlib.Matrix.Majorization.KyFan

/-!
# Schur's theorem: the diagonal is majorized by the eigenvalues

The squared moduli of the entries of a unitary matrix form a doubly stochastic matrix, and the
diagonal of a unitarily diagonalised matrix is the image of the diagonal factor under such a
matrix. Hence the diagonal of a Hermitian matrix is majorized by its eigenvalues.

The majorization statement compares two vectors on the index type `n`. It is stated for any
unitary diagonalisation `A * U = U * diagonal d`; the form with Mathlib's `hA.eigenvalues` and
the partial-sum form with `NLAlib.eigenvalue` are corollaries.

## Main results

* `NLAlib.HasOrthonormalCols.norm_sq_mem_doublyStochastic`: orthostochastic matrices.
* `NLAlib.majorized_re_diag_of_mul_eq_mul_diagonal`: Schur's theorem.
* `Matrix.IsHermitian.sumLargest_re_diag_le_sum_eigenvalue`: the same as partial sums.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of a unitary matrix is doubly stochastic.
[HornJohnson2013, §8.7]. Port of
`NLAlib.norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.norm_sq_mem_doublyStochastic {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) :
    (Matrix.of fun i j => ‖U i j‖ ^ 2) ∈ doublyStochastic ℝ n := by
  sorry

/-- **Schur's theorem.** If `A * U = U * diagonal d` for a unitary `U` and real `d`, the diagonal
of `A` is majorized by `d`: the diagonal of a Hermitian matrix is majorized by its eigenvalues,
in any enumeration.
[HornJohnson2013, Theorem 4.3.45].
Port of `NLAlib.majorized_diagonal_eigenvalues`.
Result: schur-majorization -/
theorem majorized_re_diag_of_mul_eq_mul_diagonal {A U : Matrix n n 𝕜} {d : n → ℝ}
    (hU : HasOrthonormalCols U) (h : A * U = U * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) :
    Majorized (fun i => RCLike.re (A i i)) d := by
  sorry

/-- Schur's theorem for Mathlib's enumeration of the eigenvalues.
[HornJohnson2013, Theorem 4.3.45].
Result: schur-majorization -/
theorem _root_.Matrix.IsHermitian.majorized_re_diag_eigenvalues {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Majorized (fun i => RCLike.re (A i i)) hA.eigenvalues := by
  sorry

/-- Schur's theorem as partial sums: the sum of the `k` largest diagonal entries of a Hermitian
matrix is at most the sum of its `k` largest eigenvalues.
[HornJohnson2013, Theorem 4.3.45].
Result: schur-majorization -/
theorem _root_.Matrix.IsHermitian.sumLargest_re_diag_le_sum_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) :
    sumLargest (fun i => RCLike.re (A i i)) k ≤ ∑ i ∈ Finset.range k, eigenvalue A i := by
  sorry

/-- Each diagonal entry of a Hermitian matrix lies between its extreme eigenvalues.
Port of `NLAlib.re_diagonal_mem_Icc_eigenvalues₀`. -/
theorem _root_.Matrix.IsHermitian.re_apply_self_mem_Icc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (i : n) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    RCLike.re (A i i) ∈ Set.Icc (eigenvalue A k) (eigenvalue A 0) := by
  sorry

/-- For a convex function, the sum over the diagonal is at most the sum over the eigenvalues.
[HornJohnson2013, Theorem 4.3.50 with 4.3.45]. -/
theorem _root_.Matrix.IsHermitian.sum_convex_re_diag_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ i, φ (RCLike.re (A i i)) ≤ ∑ k ∈ Finset.range (Fintype.card n), φ (eigenvalue A k) := by
  sorry

end NLAlib
