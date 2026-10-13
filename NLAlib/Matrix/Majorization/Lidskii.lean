/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.TraceInequalities
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Lidskii's inequalities

For Hermitian `A` and `B`, the vector of eigenvalue differences `λ_i(A + B) - λ_i(A)` is
majorized by the eigenvalues of `B`. For arbitrary matrices, the absolute differences of
singular values `|σ_i(A + E) - σ_i(A)|` are weakly majorized by the singular values of `E`. The
second statement is the general form of Mirsky's theorem: with Fan dominance it gives the
`1`-Lipschitz property of singular values in every unitarily invariant norm.

## Main results

* `NLAlib.sum_eigenvalue_add_sub_le_sum_range`, `NLAlib.majorized_eigenvalue_add_sub`: Lidskii.
* `NLAlib.sum_abs_singularValues_add_sub_le_kyFanNorm`,
  `NLAlib.weaklyMajorized_abs_singularValues_add_sub`: the singular value form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Lidskii's inequality**, sum form. For Hermitian `A`, `B` and any set `J` of valid indices,
`∑ j ∈ J, (λ_j(A + B) - λ_j(A)) ≤ ∑ i < |J|, λ_i(B)`.
[HornJohnson2013, Theorem 4.3.47(b)]; [Bhatia1997, Theorem III.4.1].
Port of `NLAlib.sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix`, there over `ℝ`.
Result: lidskii-inequality -/
theorem sum_eigenvalue_add_sub_le_sum_range {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {J : Finset ℕ} (hJ : ∀ j ∈ J, j < Fintype.card n) :
    ∑ j ∈ J, (eigenvalue (A + B) j - eigenvalue A j) ≤
      ∑ i ∈ Finset.range J.card, eigenvalue B i := by
  sorry

/-- **Lidskii's inequality**, majorization form. For Hermitian `A`, `B`, the eigenvalue
differences `λ_i(A + B) - λ_i(A)` are majorized by the eigenvalues of `B`.
[Bhatia1997, Corollary III.4.2].
Port of `NLAlib.majorized_eigenvalues₀_add_sub`, there over `ℝ`.
Result: lidskii-inequality -/
theorem majorized_eigenvalue_add_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    Majorized (fun i : Fin (Fintype.card n) => eigenvalue (A + B) i - eigenvalue A i)
      (fun i : Fin (Fintype.card n) => eigenvalue B i) := by
  sorry

/-- **Lidskii's inequality for singular values.** For any set `S` of indices,
`∑ i ∈ S, |σ_i(A + E) - σ_i(A)| ≤ ∑ j < |S|, σ_j(E)`.
[HornJohnson1991, Theorem 3.4.5]; [Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.sum_abs_singularValues_add_sub_le_sum_range`, there over `ℝ`.
Result: lidskii-singular-values, mirsky-inequality -/
theorem sum_abs_singularValues_add_sub_le_kyFanNorm (A E : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues (A + E) i - singularValues A i| ≤ kyFanNorm S.card E := by
  sorry

/-- The absolute differences of the first `N` singular values are weakly majorized by the first
`N` singular values of the perturbation, for every `N`.
[Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.weaklyMajorized_abs_singularValues_add_sub_padded`, there over `ℝ`.
Result: lidskii-singular-values -/
theorem weaklyMajorized_abs_singularValues_add_sub (A E : Matrix m n 𝕜) (N : ℕ) :
    WeaklyMajorized (fun i : Fin N => |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin N => singularValues E i) := by
  sorry

end NLAlib
