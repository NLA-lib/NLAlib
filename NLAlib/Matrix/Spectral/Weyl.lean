/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Weyl's inequalities and eigenvalue perturbation

Eigenvalues of Hermitian matrices are monotone in the Loewner order, subadditive in Weyl's sense,
`1`-Lipschitz in the spectral norm, and move by at most `r` positions under a perturbation of
rank `r`.

`NLAlib.eigengap A k` is the gap `eigenvalue A (k - 1) - eigenvalue A k` separating the `k`
largest eigenvalues from the rest; it is the quantity perturbation bounds for eigenspaces divide
by.

## Main definitions

* `NLAlib.eigengap`: the gap below the `k` largest eigenvalues.

## Main results

* `NLAlib.eigenvalue_le_eigenvalue_of_le`: monotonicity in the Loewner order.
* `NLAlib.eigenvalue_add_le`, `NLAlib.le_eigenvalue_add`: Weyl's inequalities.
* `NLAlib.abs_eigenvalue_sub_le`: eigenvalues are `1`-Lipschitz in the spectral norm.
* `NLAlib.eigenvalue_add_le_of_rank_le`, `NLAlib.eigenvalue_le_eigenvalue_add_of_rank_le`:
  interlacing under a low-rank perturbation.
* `NLAlib.abs_eigengap_sub_le`: stability of the gap.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Monotonicity -/

/-- **Monotonicity of eigenvalues.** If `A ≤ B` in the Loewner order and `A` is Hermitian (then
so is `B`), every eigenvalue of `A` is at most the corresponding eigenvalue of `B`.
[HornJohnson2013, Corollary 4.3.12].
Port of `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le`.
Result: eigenvalue-monotonicity -/
theorem eigenvalue_le_eigenvalue_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (hA : A.IsHermitian)
    (k : ℕ) : eigenvalue A k ≤ eigenvalue B k := by
  sorry

/-- Adding a positive semidefinite matrix does not decrease any eigenvalue. -/
theorem eigenvalue_le_eigenvalue_add_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosSemidef) (k : ℕ) : eigenvalue A k ≤ eigenvalue (A + B) k := by
  sorry

/-! ### Weyl's inequalities -/

/-- **Weyl's inequality.** For Hermitian `A`, `B` and `i + j` a valid index,
`λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)`, eigenvalues non-increasing and indexed from `0`.
[HornJohnson2013, Theorem 4.3.1]; stated there over `ℂ` with eigenvalues in increasing order.
Port of `Matrix.IsHermitian.eigenvalues₀_add_le`.
Result: weyl-inequality -/
theorem eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j : ℕ} (hij : i + j < Fintype.card n) :
    eigenvalue (A + B) (i + j) ≤ eigenvalue A i + eigenvalue B j := by
  sorry

/-- **Weyl's inequality, lower form.** For Hermitian `A`, `B` and valid indices with
`i + j + 1 = k + Fintype.card n`, `λ_i(A) + λ_j(B) ≤ λ_k(A + B)`.
[HornJohnson2013, Theorem 4.3.1].
Result: weyl-inequality -/
theorem le_eigenvalue_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j k : ℕ} (hi : i < Fintype.card n) (hj : j < Fintype.card n)
    (h : i + j + 1 = k + Fintype.card n) :
    eigenvalue A i + eigenvalue B j ≤ eigenvalue (A + B) k := by
  sorry

/-- Weyl's inequality with the largest eigenvalue of the perturbation:
`λ_k(A + B) ≤ λ_k(A) + λ_0(B)`. -/
theorem eigenvalue_add_le_add_eigenvalue_zero {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (A + B) k ≤ eigenvalue A k + eigenvalue B 0 := by
  sorry

/-- Weyl's inequality with the smallest eigenvalue of the perturbation:
`λ_k(A) + λ_min(B) ≤ λ_k(A + B)`. -/
theorem eigenvalue_add_eigenvalue_last_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k l : ℕ} (hk : k < Fintype.card n) (hl : l + 1 = Fintype.card n) :
    eigenvalue A k + eigenvalue B l ≤ eigenvalue (A + B) k := by
  sorry

/-- **Eigenvalues are `1`-Lipschitz in the spectral norm.** For Hermitian `A`, `B` and every
`k`, `|λ_k(A) - λ_k(B)| ≤ ‖A - B‖₂`.
[HornJohnson2013, Corollary 4.3.15].
Result: weyl-perturbation -/
theorem abs_eigenvalue_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) : |eigenvalue A k - eigenvalue B k| ≤ specNorm (A - B) := by
  sorry

/-! ### Low-rank perturbations -/

/-- **Interlacing under a low-rank perturbation, upper.** If `B` has rank at most `r` then
`λ_{k+r}(A + B) ≤ λ_k(A)`.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_add_le_of_rank_le`, there over `ℝ`.
Result: low-rank-interlacing -/
theorem eigenvalue_add_le_of_rank_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℕ} (hr : B.rank ≤ r) {k : ℕ} (hk : k + r < Fintype.card n) :
    eigenvalue (A + B) (k + r) ≤ eigenvalue A k := by
  sorry

/-- **Interlacing under a low-rank perturbation, lower.** If `B` has rank at most `r` then
`λ_{k+r}(A) ≤ λ_k(A + B)`.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_le_add_of_rank_le`, there over `ℝ`.
Result: low-rank-interlacing -/
theorem eigenvalue_le_eigenvalue_add_of_rank_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℕ} (hr : B.rank ≤ r) {k : ℕ} (hk : k + r < Fintype.card n) :
    eigenvalue A (k + r) ≤ eigenvalue (A + B) k := by
  sorry

/-- **Rank-one update, upper.** Adding `z zᴴ` moves each eigenvalue up by at most one position:
`λ_{k+1}(A + z zᴴ) ≤ λ_k(A)`. [HornJohnson2013, Corollary 4.3.9].
Port of `NLAlib.eigenvalues₀_rank_one_add_interlacing`, there over `ℝ` as a conjunction. -/
theorem eigenvalue_add_vecMulVec_star_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) (z : n → 𝕜)
    {k : ℕ} (hk : k + 1 < Fintype.card n) :
    eigenvalue (A + Matrix.vecMulVec z (star z)) (k + 1) ≤ eigenvalue A k := by
  sorry

/-- **Rank-one update, lower.** Adding `z zᴴ` does not decrease any eigenvalue.
[HornJohnson2013, Corollary 4.3.9]. -/
theorem eigenvalue_le_eigenvalue_add_vecMulVec_star {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) (k : ℕ) :
    eigenvalue A k ≤ eigenvalue (A + Matrix.vecMulVec z (star z)) k := by
  sorry

/-! ### The eigengap -/

/-- The **eigengap** below the `k` largest eigenvalues: `λ_{k-1}(A) - λ_k(A)` with eigenvalues
indexed from `0`, the gap that separates the leading `k`-dimensional eigenspace from the rest. The
index is the dimension of that eigenspace. With truncated subtraction `eigengap A 0 = 0`, so a
hypothesis `0 < eigengap A k` already excludes `k = 0`. -/
noncomputable def eigengap (A : Matrix n n 𝕜) (k : ℕ) : ℝ :=
  eigenvalue A (k - 1) - eigenvalue A k

/-- The eigengap at dimension zero is zero. -/
@[simp]
theorem eigengap_zero (A : Matrix n n 𝕜) : eigengap A 0 = 0 := by
  sorry

/-- The eigengap at dimension `k + 1` is `λ_k - λ_{k+1}`. This is the form to compute with. -/
theorem eigengap_succ (A : Matrix n n 𝕜) (k : ℕ) :
    eigengap A (k + 1) = eigenvalue A k - eigenvalue A (k + 1) := by
  sorry

/-- The eigengap of a Hermitian matrix is nonnegative at a valid index. -/
theorem _root_.Matrix.IsHermitian.eigengap_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) : 0 ≤ eigengap A k := by
  sorry

/-- **Stability of the eigengap.** A Hermitian perturbation changes the gap by at most twice its
spectral norm. -/
theorem abs_eigengap_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) : |eigengap A k - eigengap B k| ≤ 2 * specNorm (A - B) := by
  sorry

end NLAlib
