/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import NLAlib.Matrix.Spectral.CourantFischer
public import NLAlib.Matrix.Norms.Loewner

/-!
# Functions of a Hermitian matrix

For a Hermitian matrix `A` and `f : ℝ → ℝ`, the matrix `f(A)` is Mathlib's continuous functional
calculus `cfc f A`. This file gives the working API in the vocabulary of this library: `cfc f A`
through any unitary diagonalisation, its trace, eigenvalues, quadratic form and spectral norm,
and its behaviour under unitary conjugation and block diagonal sums.

No definition is introduced. `cfc f A` is the spelling of `f(A)`; the square root is
`CFC.sqrt A`, a real power of a positive semidefinite matrix is `A ^ r`, the absolute value is
`CFC.abs A` and the positive part is `A⁺`, all from Mathlib and all available with
`open scoped MatrixOrder`. They unfold to `cfc` by `CFC.sqrt_eq_real_sqrt`,
`CFC.rpow_eq_cfc_real`, `CFC.abs_eq_cfc_norm` and `CFC.posPart_def`. General facts are Mathlib's:
`cfc_predicate` (`f(A)` is Hermitian), `cfc_commute_cfc`, `cfc_mono` (comparison on the
spectrum), `cfc_nonneg`, `cfc_pow_id`, `cfc_inv_id`, `cfc_polynomial`.

The location of the spectrum is the hypothesis `spectrum ℝ A ⊆ s`, or a Loewner sandwich
`a • 1 ≤ A`, `A ≤ b • 1` for an interval.

## Main results

* `NLAlib.cfc_eq_mul_diagonal_mul_conjTranspose`: `f(U D Uᴴ) = U f(D) Uᴴ`.
* `Matrix.IsHermitian.spectrum_subset_iff`: the spectrum through the sorted eigenvalues.
* `Matrix.IsHermitian.re_trace_cfc`: `tr f(A) = ∑ f(λ_i)`.
* `Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn`: eigenvalues of `f(A)` for monotone `f`.
* `Matrix.IsHermitian.specNorm_cfc_le`: `‖f(A)‖₂ ≤ max |f|` on the spectrum.
* `NLAlib.re_quadForm_cfc_eq_sum`: the quadratic form of `f(A)` as a weighted sum.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisation -/

/-- **`f(A)` through a unitary diagonalisation.** If `A = U * diagonal d * Uᴴ` with `U` unitary
and `d` real, then `cfc f A = U * diagonal (f ∘ d) * Uᴴ`.
Port of `NLAlib.cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose`, there for the chosen
eigenvector matrix. -/
theorem cfc_eq_mul_diagonal_mul_conjTranspose {A U : Matrix n n 𝕜} {d : n → ℝ}
    (hU : HasOrthonormalCols U) (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ)
    (f : ℝ → ℝ) : cfc f A = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ := by
  sorry

/-- `f` of a real diagonal matrix is the diagonal matrix of the values of `f`.
Port of `NLAlib.cfc_diagonal_real`. -/
theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      Matrix.diagonal fun i => ((f (d i) : ℝ) : 𝕜) := by
  sorry

/-- An eigenvector of `A` is an eigenvector of `f(A)`: if `A x = μ x` then `f(A) x = f(μ) x`. -/
theorem _root_.Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) {x : n → 𝕜} {μ : ℝ} (hx : A *ᵥ x = μ • x) :
    cfc f A *ᵥ x = f μ • x := by
  sorry

/-! ### Conjugation, relabelling and block sums -/

/-- **`f` commutes with unitary conjugation**: `f(U A Uᴴ) = U f(A) Uᴴ` for unitary `U`.
Port of `NLAlib.cfc_unitary_conj`, there over `ℂ`. -/
theorem cfc_mul_mul_conjTranspose {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (U * A * Uᴴ) = U * cfc f A * Uᴴ := by
  sorry

/-- `f` commutes with relabelling. Port of `NLAlib.cfc_reindex_of_isHermitian`. -/
theorem cfc_submatrix_equiv {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) (e : m ≃ n) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  sorry

/-- **`f` of a block diagonal matrix** is the block diagonal matrix of `f(A)` and `f(B)`.
Port of `NLAlib.cfc_fromBlocks`, there over `ℂ`. -/
theorem cfc_fromBlocks_diagonal {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  sorry

/-! ### The spectrum -/

/-- The spectrum of a Hermitian matrix lies in `s` exactly when its eigenvalues do. -/
theorem _root_.Matrix.IsHermitian.spectrum_subset_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {s : Set ℝ} : spectrum ℝ A ⊆ s ↔ ∀ i, i < Fintype.card n → eigenvalue A i ∈ s := by
  sorry

/-- A matrix between `a • 1` and `b • 1` has its spectrum in `[a, b]`. -/
theorem spectrum_subset_Icc_of_le {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    spectrum ℝ A ⊆ Set.Icc a b := by
  sorry

/-- The spectrum of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.spectrum_subset_Ici {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    spectrum ℝ A ⊆ Set.Ici 0 := by
  sorry

/-- The spectrum of a positive definite matrix is positive. -/
theorem _root_.Matrix.PosDef.spectrum_subset_Ioi {A : Matrix n n 𝕜} (hA : A.PosDef) :
    spectrum ℝ A ⊆ Set.Ioi 0 := by
  sorry

/-! ### Trace, eigenvalues and quadratic forms -/

/-- **The trace of `f(A)`** is the sum of `f` over the eigenvalues.
Port of `NLAlib.re_trace_cfc_eq_sum_eigenvalues`.
Result: trace-of-matrix-function -/
theorem _root_.Matrix.IsHermitian.re_trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i ∈ Finset.range (Fintype.card n), f (eigenvalue A i) := by
  sorry

/-- **Eigenvalues of `f(A)` for a non-decreasing `f`**: `λ_k(f(A)) = f(λ_k(A))`, when `f` is
monotone on a set containing the spectrum of `A`.
Port of `NLAlib.eigenvalues₀_cfc_of_antitone`, there with the hypothesis on the composite. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A k) := by
  sorry

/-- Eigenvalues of `f(A)` for a non-increasing `f`: `λ_k(f(A)) = f(λ_j(A))` with
`k + j + 1 = card n`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_antitoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k j : ℕ} (hkj : k + j + 1 = Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A j) := by
  sorry

/-- **The quadratic form of `f(A)`** through a unitary diagonalisation `A = U D Uᴴ`:
`xᴴ f(A) x = ∑ f(d_i) |(Uᴴ x)_i|²`. This is the identity behind Gauss quadrature for `xᴴ f(A) x`.
Port of `NLAlib.dotProduct_cfc_mulVec_eq_sum`, there over `ℝ` with the chosen eigenbasis. -/
theorem re_quadForm_cfc_eq_sum {A U : Matrix n n 𝕜} {d : n → ℝ} (hU : HasOrthonormalCols U)
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (f : ℝ → ℝ) (x : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) x) = ∑ i, f (d i) * ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
  sorry

/-- **A nonnegative trace function dominates its value at the largest eigenvalue**: if `φ ≥ 0`
on the spectrum of `A` then `φ(λ_0(A)) ≤ tr φ(A)`. With `φ = exp` this is the first step of the
matrix Laplace transform method; with `φ(t) = max (t - 1) 0` it is the first step of the
intrinsic-dimension bounds. [Tropp2015, Proposition 3.2.1 and §7.5]. -/
theorem _root_.Matrix.IsHermitian.apply_eigenvalue_zero_le_re_trace_cfc [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {φ : ℝ → ℝ} (hφ : ∀ x ∈ spectrum ℝ A, 0 ≤ φ x) :
    φ (eigenvalue A 0) ≤ RCLike.re (cfc φ A).trace := by
  sorry

/-! ### Order and norm bounds -/

/-- Comparison on an interval containing the spectrum: if `a • 1 ≤ A ≤ b • 1` and `f ≤ g` on
`[a, b]`, then `f(A) ≤ g(A)`. The comparison on the spectrum itself is Mathlib's `cfc_mono`. -/
theorem cfc_le_cfc_of_forall_mem_Icc {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) : cfc f A ≤ cfc g A := by
  sorry

/-- **The spectral norm of `f(A)`** is at most the largest `|f|` on the spectrum.
Port of `NLAlib.specNorm_aeval_le`, there for polynomials over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.specNorm_cfc_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) :
    specNorm (cfc f A) ≤ c := by
  sorry

/-- The quadratic form of `f(A)` is bounded by the largest `|f|` on the spectrum.
Port of `NLAlib.abs_dotProduct_cfc_mulVec_le`. -/
theorem _root_.Matrix.IsHermitian.abs_re_quadForm_cfc_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {c : ℝ} (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) (x : n → 𝕜) :
    |RCLike.re (quadForm (cfc f A) x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- A lower bound for the trace of `f(A)` from a lower bound of `f` on the spectrum.
Port of `NLAlib.mul_card_le_re_trace_cfc_of_le`. -/
theorem _root_.Matrix.IsHermitian.mul_card_le_re_trace_cfc {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {b : ℝ} (h : ∀ x ∈ spectrum ℝ A, b ≤ f x) :
    b * Fintype.card n ≤ RCLike.re (cfc f A).trace := by
  sorry

/-! ### The inverse square root -/

/-- The inverse of the square root of a positive definite matrix through the functional
calculus. Port of `NLAlib.cfc_inv_sqrt_mul_sqrt`. -/
theorem _root_.Matrix.PosDef.inv_sqrt_eq_cfc {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ = cfc (fun x : ℝ => (√x)⁻¹) A := by
  sorry

/-- The square root of a positive definite matrix is invertible. -/
theorem _root_.Matrix.PosDef.isUnit_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsUnit (CFC.sqrt A) := by
  sorry

end NLAlib
