/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Spectral.Weyl

/-!
# First-order perturbation of a simple eigenvalue

A simple eigenvalue moves differentiably under a perturbation `A + t • E`, with derivative
`yᴴ E x / yᴴ x` for right and left eigenvectors `x`, `y`. For a Hermitian matrix the sorted
eigenvalue `eigenvalue (A + t • E) k` itself is differentiable at `t = 0` when `eigenvalue A k` is
simple, with derivative `xᴴ E x` for a unit eigenvector: no branch has to be chosen.

## Main results

* `Matrix.IsHermitian.hasDerivAt_eigenvalue_add_smul`: the Hermitian case.
* `NLAlib.exists_eigenvalue_branch_of_rootMultiplicity_eq_one`: a differentiable branch through a
  simple eigenvalue of a complex matrix.
-/

@[expose] public section

open scoped Matrix Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Hermitian matrices -/

/-- **First-order perturbation of a simple eigenvalue of a Hermitian matrix.** If `A` and `E` are
Hermitian, `eigenvalue A k` is a simple eigenvalue of `A` and `x` is a unit eigenvector for it,
then `t ↦ eigenvalue (A + t • E) k` has derivative `re (xᴴ E x)` at `0`.
[StewartSun1990, Theorem IV.2.3]; [Kato1995, §II.6.4]. -/
theorem _root_.Matrix.IsHermitian.hasDerivAt_eigenvalue_add_smul {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ} (hk : k < Fintype.card n)
    (hsimple : ∀ i, i < Fintype.card n → i ≠ k → eigenvalue A i ≠ eigenvalue A k)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = eigenvalue A k • x) :
    HasDerivAt (fun t : ℝ => eigenvalue (A + t • E) k) (RCLike.re (star x ⬝ᵥ E *ᵥ x)) 0 := by
  sorry

/-- The second-order remainder in the Hermitian case: for `t` small,
`|λ_k(A + t E) - λ_k(A) - t xᴴ E x| δ ≤ t² ‖E‖₂²`, where `δ` is half the distance from
`eigenvalue A k` to the rest of the spectrum.
[Parlett1998, Theorem 11.7.1 applied to the Rayleigh quotient of `x`]. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalue_add_smul_sub_mul_le {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i, i < Fintype.card n → i ≠ k → 2 * δ ≤ |eigenvalue A i - eigenvalue A k|)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = eigenvalue A k • x) {t : ℝ}
    (ht : |t| * specNorm E < δ / 2) :
    |eigenvalue (A + t • E) k - eigenvalue A k - t * RCLike.re (star x ⬝ᵥ E *ᵥ x)| * δ ≤
      t ^ 2 * specNorm E ^ 2 := by
  sorry

/-! ### General complex matrices -/

/-- **A differentiable branch through a simple eigenvalue.** Let `μ` be a simple root of the
characteristic polynomial of the complex matrix `A`, with right eigenvector `x` and left
eigenvector `y`. Then there is a function `φ` with `φ 0 = μ`, derivative `yᵀ E x / yᵀ x` at `0`,
such that near `(0, μ)` the eigenvalues of `A + t • E` close to `μ` are exactly `φ t`, and they
remain simple. The left eigenvector enters through the bilinear product `yᵀ x`, with
`y ᵥ* A = μ • y`; for Hermitian `A` take `y = star x` to recover the derivative `xᴴ E x`.
[StewartSun1990, Theorem IV.2.3]; [HornJohnson2013, Theorem 6.3.12].
Port of `NLAlib.exists_eigenvalue_branch_of_simple_with_multiplicity`.
Result: simple-eigenvalue-perturbation -/
theorem exists_eigenvalue_branch_of_rootMultiplicity_eq_one {A : Matrix n n ℂ}
    (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x)
    (hyA : y ᵥ* A = μ • y) (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ HasDerivAt φ (y ⬝ᵥ E *ᵥ x / y ⬝ᵥ x) 0 ∧
      (∀ᶠ t in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (0, μ), p.2 ∈ spectrum ℂ (A + p.1 • E) ↔ φ p.1 = p.2) ∧
      ∀ᶠ t in 𝓝 0, (A + t • E).charpoly.rootMultiplicity (φ t) = 1 := by
  sorry

/-- For a simple eigenvalue the left and right eigenvectors are not orthogonal: `yᵀ x ≠ 0`.
[HornJohnson2013, Lemma 6.3.10]. -/
theorem dotProduct_ne_zero_of_rootMultiplicity_eq_one {A : Matrix n n ℂ} {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) : y ⬝ᵥ x ≠ 0 := by
  sorry

end NLAlib
