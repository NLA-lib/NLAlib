/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.EigenvalueTransform

/-!
# The Courant–Fischer variational characterisation of eigenvalues

The `k`-th eigenvalue of a Hermitian matrix is a max–min and a min–max of its quadratic form
over subspaces. The two one-sided subspace statements are the forms proofs use: a lower bound on
the quadratic form over a subspace of dimension `k + 1` bounds `eigenvalue A k` from below, and
an upper bound over a subspace of codimension `k` bounds it from above. Hypotheses are written
homogeneously, `c * ‖x‖ ^ 2 ≤ re (quadForm A x)`, with no restriction to nonzero or unit vectors.

The extreme eigenvalues are also characterised in the Loewner order, which is how bounds on the
largest and smallest eigenvalue of a random matrix are stated and used.

## Main results

* `Matrix.IsHermitian.le_eigenvalue_of_forall_mem`,
  `Matrix.IsHermitian.eigenvalue_le_of_forall_mem`: the one-sided Courant–Fischer bounds.
* `Matrix.IsHermitian.eigenvalue_eq_iSup_iInf`, `Matrix.IsHermitian.eigenvalue_eq_iInf_iSup`:
  the Courant–Fischer theorem as equations.
* `Matrix.IsHermitian.le_smul_one_iff`, `Matrix.IsHermitian.smul_one_le_iff`: the largest and
  smallest eigenvalue in the Loewner order.
* `Matrix.IsHermitian.specNorm_eq_max`, `Matrix.PosSemidef.specNorm_eq_eigenvalue_zero`: the
  spectral norm of a Hermitian matrix.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### One-sided subspace bounds -/

/-- **Courant–Fischer, lower bound.** If the quadratic form of a Hermitian `A` is at least
`c * ‖x‖ ^ 2` on a subspace of dimension at least `k + 1`, then `c ≤ eigenvalue A k`.
[HornJohnson2013, Theorem 4.2.6]; stated there as an equation over `ℂ` with eigenvalues in
increasing order, here as the inequality a proof applies, over any `RCLike` field, non-increasing.
Port of `Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S)
    {c : ℝ} (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x)) :
    c ≤ eigenvalue A k := by
  sorry

/-- **Courant–Fischer, upper bound.** If the quadratic form of a Hermitian `A` is at most
`c * ‖x‖ ^ 2` on a subspace of codimension at most `k`, for a valid index `k`, then
`eigenvalue A k ≤ c`. The index must be valid: beyond the size of `A` the eigenvalue is `0` by
convention while the zero subspace satisfies the hypothesis for negative `c`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ}
    (h : ∀ x ∈ W, RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2) :
    eigenvalue A k ≤ c := by
  sorry

/-- The lower bound is attained: there is a subspace of dimension `k + 1` on which the quadratic
form is at least `eigenvalue A k * ‖x‖ ^ 2` (the span of the first `k + 1` eigenvectors).
Port of `Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_eigenvalue_mul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = k + 1 ∧
      ∀ x ∈ S, eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  sorry

/-- The upper bound is attained: there is a subspace of codimension `k` on which the quadratic
form is at most `eigenvalue A k * ‖x‖ ^ 2` (the span of the eigenvectors from the `k`-th on).
Port of `Matrix.IsHermitian.exists_submodule_le_eigenvalues₀_mul`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_le_eigenvalue_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 W + k = Fintype.card n ∧
      ∀ x ∈ W, RCLike.re (quadForm A x) ≤ eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-! ### The Courant–Fischer equations -/

/-- **Courant–Fischer, max–min form.** `eigenvalue A k` is the supremum, over subspaces `S` of
dimension `k + 1`, of the infimum of the quadratic form over the unit vectors of `S`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iSup_iInf`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iSup_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨆ S : {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1},
        ⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  sorry

/-- **Courant–Fischer, min–max form.** `eigenvalue A k` is the infimum, over subspaces `W` of
codimension `k`, of the supremum of the quadratic form over the unit vectors of `W`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iInf_iSup`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iInf_iSup {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨅ W : {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n},
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  sorry

/-! ### Extreme eigenvalues -/

/-- **Rayleigh bound, upper.** The quadratic form of a Hermitian matrix is at most its largest
eigenvalue times `‖x‖ ^ 2`. [HornJohnson2013, Theorem 4.2.2]. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_le_eigenvalue_zero_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (quadForm A x) ≤ eigenvalue A 0 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- **Rayleigh bound, lower.** The quadratic form of a Hermitian matrix is at least its smallest
eigenvalue times `‖x‖ ^ 2`. The last index is given by the equation `k + 1 = Fintype.card n`.
[HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`, there as an infimum. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_mul_le_re_quadForm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) (x : n → 𝕜) :
    eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  sorry

/-- A Hermitian matrix is below its largest eigenvalue times the identity. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_zero_smul_one [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : A ≤ eigenvalue A 0 • (1 : Matrix n n 𝕜) := by
  sorry

/-- A Hermitian matrix is above its smallest eigenvalue times the identity. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_smul_one_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k • (1 : Matrix n n 𝕜) ≤ A := by
  sorry

/-- **The largest eigenvalue in the Loewner order.** For a Hermitian matrix on a nonempty index
type, `A ≤ c • 1` exactly when the largest eigenvalue is at most `c`. This is the form in which
an upper bound on `λ_max` is used. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_iff [DecidableEq n] [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} :
    A ≤ c • (1 : Matrix n n 𝕜) ↔ eigenvalue A 0 ≤ c := by
  sorry

/-- **The smallest eigenvalue in the Loewner order.** For a Hermitian matrix, `c • 1 ≤ A` exactly
when the smallest eigenvalue is at least `c`. This is the form in which a lower bound on `λ_min`
is used. -/
theorem _root_.Matrix.IsHermitian.smul_one_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ} :
    c • (1 : Matrix n n 𝕜) ≤ A ↔ c ≤ eigenvalue A k := by
  sorry

/-- The largest eigenvalue of a Hermitian matrix is the supremum of its quadratic form over
unit vectors. [HornJohnson2013, Theorem 4.2.2].
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_zero_eq_iSup [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    eigenvalue A 0 = ⨆ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  sorry

/-- The smallest eigenvalue of a Hermitian matrix is the infimum of its quadratic form over
unit vectors. [HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`.
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_eq_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k = ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  sorry

/-! ### The spectral norm of a Hermitian matrix -/

/-- Every eigenvalue of a Hermitian matrix is bounded in absolute value by the spectral norm. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalue_le_specNorm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) : |eigenvalue A k| ≤ specNorm A := by
  sorry

/-- The spectral norm of a Hermitian matrix is the larger of the absolute values of its extreme
eigenvalues. Port of `NLAlib.specNorm_eq_norm_eigenvalue`, there over `ℝ` as a supremum over the
unsorted eigenvalues. -/
theorem _root_.Matrix.IsHermitian.specNorm_eq_max {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    specNorm A = max |eigenvalue A 0| |eigenvalue A k| := by
  sorry

/-- The spectral norm of a positive semidefinite matrix is its largest eigenvalue. -/
theorem _root_.Matrix.PosSemidef.specNorm_eq_eigenvalue_zero {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : specNorm A = eigenvalue A 0 := by
  sorry

/-- A positive semidefinite matrix has a unit eigenvector for its spectral norm.
Port of `NLAlib.exists_unit_mulVec_eq_specNorm_smul`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.exists_norm_eq_one_and_mulVec_eq_specNorm_smul [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ A *ᵥ u = specNorm A • u := by
  sorry

end NLAlib
