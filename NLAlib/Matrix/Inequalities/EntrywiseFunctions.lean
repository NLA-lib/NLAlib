/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import NLAlib.Matrix.Inequalities.HadamardProduct

/-!
# Entrywise functions of positive semidefinite matrices

By the Schur product theorem, entrywise powers of a positive semidefinite matrix are positive
semidefinite, hence so is the entrywise image under any power series with nonnegative
coefficients, in particular the entrywise exponential. These are the facts behind positive
definite kernels (polynomial and exponential kernels).

## Main results

* `Matrix.PosSemidef.map_pow`: entrywise powers.
* `Matrix.PosSemidef.map_of_hasSum`: entrywise power series with nonnegative coefficients.
* `Matrix.PosSemidef.map_exp`: the entrywise exponential of a real positive semidefinite matrix.
* `Matrix.PosSemidef.posDef_map_exp_iff`: it is positive definite exactly when the rows are
  distinct.
* `Matrix.PosSemidef.map_pow_le_map_pow_of_le`: monotonicity of entrywise powers.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Entrywise powers -/

/-- **Entrywise powers of a positive semidefinite matrix are positive semidefinite.**
[HornJohnson2013, Theorem 7.5.9]. Port of `NLAlib.posSemidef_map_pow`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.map_pow {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : ℕ) :
    (A.map fun t => t ^ k).PosSemidef := by
  sorry

/-- Entrywise powers are monotone on positive semidefinite matrices: `0 ≤ B ≤ A` gives
`B^{∘k} ≤ A^{∘k}`. [HornJohnson1991, §5.2 context].
Port of `NLAlib.map_pow_le_map_pow_of_posSemidef_le`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.map_pow_le_map_pow_of_le {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B ≤ A) (k : ℕ) : (B.map fun t => t ^ k) ≤ A.map fun t => t ^ k := by
  sorry

/-! ### Power series with nonnegative coefficients -/

/-- **Entrywise power series with nonnegative coefficients preserve positive semidefiniteness.**
If `f t = ∑ c k t ^ k` with `c k ≥ 0` at every entry of the real positive semidefinite matrix
`A`, then `A.map f` is positive semidefinite.
[HornJohnson2013, Theorem 7.5.9]; [HornJohnson1991, Theorem 6.3.6 context].
Port of `NLAlib.posSemidef_map_of_nonneg_powerSeries`.
Result: schur-product-power-series -/
theorem _root_.Matrix.PosSemidef.map_of_hasSum {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {f : ℝ → ℝ}
    (h : ∀ i j, HasSum (fun k => c k * A i j ^ k) (f (A i j))) : (A.map f).PosSemidef := by
  sorry

/-- **The entrywise exponential of a positive semidefinite matrix is positive semidefinite.**
[HornJohnson2013, Theorem 7.5.9]. Port of `NLAlib.posSemidef_map_exp`. -/
theorem _root_.Matrix.PosSemidef.map_exp {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  sorry

/-- The entrywise exponential is monotone on positive semidefinite matrices.
Port of `NLAlib.map_exp_le_map_exp_of_posSemidef_le`. -/
theorem _root_.Matrix.PosSemidef.map_exp_le_map_exp_of_le {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (h : B ≤ A) : B.map Real.exp ≤ A.map Real.exp := by
  sorry

/-- **The entrywise exponential of a positive semidefinite matrix is positive definite exactly
when its rows are distinct.** [HornJohnson2013, Theorem 7.5.9 context].
Port of `NLAlib.posDef_map_exp_iff_rows_injective`.
Result: exponential-kernel -/
theorem _root_.Matrix.PosSemidef.posDef_map_exp_iff {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosDef ↔ Function.Injective A.row := by
  sorry

/-- The Gram matrix `exp (b i * b j)` of distinct real numbers is positive definite.
Port of `NLAlib.posDef_sum_inv_factorial_map_pow_vecMulVec_of_injective`, in the limit. -/
theorem posDef_of_exp_mul {b : n → ℝ} (hb : Function.Injective b) :
    (Matrix.of fun i j => Real.exp (b i * b j)).PosDef := by
  sorry

end NLAlib
