/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Majorization.DoublyStochastic
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Horn's product inequality and log-majorization

The singular values of a product are log-majorized by the products of the singular values:
`∏ i < k, σ_i(A B) ≤ ∏ i < k, σ_i(A) σ_i(B)`. Weyl's lemma turns such product inequalities
between non-increasing nonnegative sequences into inequalities between sums of powers, which is
how Hölder's inequality for Schatten norms is obtained.

## Main results

* `NLAlib.prod_range_singularValues_mul_le`: Horn's product inequality.
* `NLAlib.sum_range_rpow_le_of_forall_prod_range_le`: Weyl's lemma, log-majorization implies
  weak majorization of powers.
* `NLAlib.sum_range_singularValues_mul_rpow_le`: power sums of the singular values of a product.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- **Horn's product inequality.** For every `k`,
`∏ i < k, σ_i(A * B) ≤ ∏ i < k, σ_i(A) σ_i(B)`.
[HornJohnson1991, Theorem 3.3.4].
Port of `NLAlib.prod_singularValues_mul_le`, there over `ℝ`.
Result: horn-product-inequality -/
theorem prod_range_singularValues_mul_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (k : ℕ) :
    ∏ i ∈ Finset.range k, singularValues (A * B) i ≤
      ∏ i ∈ Finset.range k, singularValues A i * singularValues B i := by
  sorry

/-- **Weyl's lemma: log-majorization implies weak majorization of powers.** For nonnegative
non-increasing sequences `x`, `y` with `∏ i < k, x i ≤ ∏ i < k, y i` for all `k ≤ N`, and any
`r > 0`, `∑ i < N, x i ^ r ≤ ∑ i < N, y i ^ r`.
[HornJohnson1991, Theorem 3.3.13 and Corollary 3.3.10].
Port of `NLAlib.sum_range_rpow_le_of_nonneg_of_prod_le`. -/
theorem sum_range_rpow_le_of_forall_prod_range_le {x y : ℕ → ℝ} {N : ℕ} (hx0 : ∀ i, 0 ≤ x i)
    (hy0 : ∀ i, 0 ≤ y i) (hx : Antitone x) (hy : Antitone y)
    (h : ∀ k ≤ N, ∏ i ∈ Finset.range k, x i ≤ ∏ i ∈ Finset.range k, y i) {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, x i ^ r ≤ ∑ i ∈ Finset.range N, y i ^ r := by
  sorry

/-- Power sums of the singular values of a product: for `r > 0` and every `N`,
`∑ i < N, σ_i(A B) ^ r ≤ ∑ i < N, (σ_i(A) σ_i(B)) ^ r`.
[HornJohnson1991, Theorem 3.3.14].
Port of `NLAlib.sum_range_singularValues_mul_rpow_le`, there over `ℝ`. -/
theorem sum_range_singularValues_mul_rpow_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, singularValues (A * B) i ^ r ≤
      ∑ i ∈ Finset.range N, (singularValues A i * singularValues B i) ^ r := by
  sorry

end NLAlib
