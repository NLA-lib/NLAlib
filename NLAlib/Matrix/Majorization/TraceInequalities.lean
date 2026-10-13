/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.Schur

/-!
# Trace inequalities of von Neumann type

The trace of a product is bounded by the sum of the products of the sorted eigenvalues (for
Hermitian matrices) or singular values (in general). From these follow the Hoffman–Wielandt
inequality for Hermitian matrices and Mirsky's inequality in the Frobenius norm: sorted
eigenvalues and sorted singular values are `1`-Lipschitz in the Frobenius norm, as vectors.

## Main results

* `Matrix.IsHermitian.re_trace_mul_le_sum_eigenvalue_mul`: the Hermitian trace inequality.
* `NLAlib.norm_trace_conjTranspose_mul_le_sum_singularValues_mul`: von Neumann's trace inequality.
* `NLAlib.sum_sq_eigenvalue_sub_le_frobNorm_sub_sq`: Hoffman–Wielandt for Hermitian matrices.
* `NLAlib.sum_sq_singularValues_sub_le_frobNorm_sub_sq`: Mirsky's inequality.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **The trace inequality for Hermitian matrices.** `re tr (A B) ≤ ∑ λ_i(A) λ_i(B)`, the
eigenvalues of each matrix in non-increasing order.
[HornJohnson2013, Theorem 4.3.53].
Port of `NLAlib.trace_mul_le_sum_eigenvalues₀_mul`, there over `ℝ`.
Result: von-neumann-trace-inequality -/
theorem _root_.Matrix.IsHermitian.re_trace_mul_le_sum_eigenvalue_mul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤
      ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i * eigenvalue B i := by
  sorry

/-- The lower trace inequality for Hermitian matrices: `∑ λ_i(A) λ_{n-1-i}(B) ≤ re tr (A B)`,
the eigenvalues of `A` in non-increasing and those of `B` in non-decreasing order.
[HornJohnson2013, Theorem 4.3.53]. -/
theorem _root_.Matrix.IsHermitian.sum_eigenvalue_mul_rev_le_re_trace_mul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ i : Fin (Fintype.card n), eigenvalue A i * eigenvalue B (Fin.rev i) ≤
      RCLike.re (A * B).trace := by
  sorry

/-- **von Neumann's trace inequality.** `|tr (Aᴴ B)| ≤ ∑ σ_i(A) σ_i(B)`.
[HornJohnson2013, Theorem 7.4.1.1].
Port of `NLAlib.frobInner_le_sum_singularValues_mul`, there over `ℝ` and for the real part.
Result: von-neumann-trace-inequality -/
theorem norm_trace_conjTranspose_mul_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  sorry

/-- von Neumann's trace inequality for the Frobenius inner product:
`|⟨A, B⟩_F| ≤ ∑ σ_i(A) σ_i(B)`.
[HornJohnson2013, Theorem 7.4.1.1].
Port of `NLAlib.abs_frobInner_le_sum_singularValues_mul`, there over `ℝ`.
Result: von-neumann-trace-inequality -/
theorem abs_frobInner_le_sum_singularValues_mul (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  sorry

/-- **Hoffman–Wielandt for Hermitian matrices.** The sorted eigenvalues are `1`-Lipschitz in the
Frobenius norm: `∑ (λ_i(A) - λ_i(B))² ≤ ‖A - B‖_F²`, over any set of indices.
[HornJohnson2013, Corollary 6.3.8].
Port of `NLAlib.sum_sq_eigenvalues₀_sub_le_frobSq_sub`, there over `ℝ`.
Result: hoffman-wielandt -/
theorem sum_sq_eigenvalue_sub_le_frobNorm_sub_sq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Finset ℕ) :
    ∑ i ∈ S, (eigenvalue A i - eigenvalue B i) ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  sorry

/-- **Mirsky's inequality** in the Frobenius norm. The sorted singular values are `1`-Lipschitz:
`∑ (σ_i(A) - σ_i(B))² ≤ ‖A - B‖_F²`, over any set of indices.
[HornJohnson2013, Corollary 7.4.1.3].
Port of `NLAlib.sum_sq_singularValues_add_sub_le_frobSq`, there over `ℝ`.
Result: mirsky-inequality -/
theorem sum_sq_singularValues_sub_le_frobNorm_sub_sq (A B : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, (singularValues A i - singularValues B i) ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  sorry

/-- The Frobenius inner product with a matrix of rank at most `r` is bounded through the
spectral norm: `⟨X, E⟩_F ≤ √r ‖X‖_F ‖E‖₂`.
Port of `NLAlib.frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`, there over `ℝ`. -/
theorem frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le {X : Matrix m n 𝕜} {r : ℕ}
    (hX : X.rank ≤ r) (E : Matrix m n 𝕜) :
    frobInner X E ≤ √(r : ℝ) * frobNorm X * specNorm E := by
  sorry

end NLAlib
