/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Spectral.SVD

/-!
# Polynomials in a matrix

Real polynomials evaluated at a matrix, `Polynomial.aeval A p`. For a Hermitian matrix this is
`cfc (p.eval ·) A` (Mathlib's `cfc_polynomial`), so its norm is the largest value of `|p|` on
the eigenvalues: the fact behind every polynomial convergence bound for Krylov methods. For a
rectangular matrix, polynomials in the two Gram matrices intertwine, `p(A Aᴴ) A = A p(Aᴴ A)`,
and act on the singular values.

## Main results

* `Matrix.IsHermitian.exists_cfc_eq_aeval`: every function of `A` is a polynomial in `A`.
* `Matrix.IsHermitian.specNorm_aeval_le`: `‖p(A)‖₂ ≤ max |p(λ_i)|`.
* `NLAlib.specNorm_cfc_sub_aeval_le`: polynomial approximation of `f(A)`.
* `NLAlib.aeval_mul_conjTranspose_self_mul`: intertwining.
* `NLAlib.IsSVD.mul_aeval_conjTranspose_mul_self`: a polynomial filter applied to an SVD.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-! ### Polynomials in a Hermitian matrix -/

/-- A polynomial in a real diagonal matrix. Port of `NLAlib.aeval_diagonal_ofReal`. -/
theorem aeval_diagonal (d : n → ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) p =
      Matrix.diagonal fun i => ((p.eval (d i) : ℝ) : 𝕜) := by
  sorry

/-- A polynomial commutes with unitary conjugation. -/
theorem aeval_mul_mul_conjTranspose {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U)
    (A : Matrix n n 𝕜) (p : ℝ[X]) : aeval (U * A * Uᴴ) p = U * aeval A p * Uᴴ := by
  sorry

/-- A function of a Hermitian matrix is the polynomial that agrees with it on the eigenvalues.
Port of `NLAlib.cfc_eq_aeval_of_forall_eval_eq`. -/
theorem _root_.Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {p : ℝ[X]} (h : ∀ x ∈ spectrum ℝ A, p.eval x = f x) :
    cfc f A = aeval A p := by
  sorry

/-- **Every function of a Hermitian matrix is a polynomial in it** of degree less than the size:
`f(A) b` lies in the Krylov space of `A` and `b`.
Port of `NLAlib.cfc_eq_aeval_interpolate`. -/
theorem _root_.Matrix.IsHermitian.exists_cfc_eq_aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : ∃ p : ℝ[X], p.degree < (Fintype.card n : WithBot ℕ) ∧ cfc f A = aeval A p := by
  sorry

/-- A polynomial in a Hermitian matrix is Hermitian. Port of `NLAlib.transpose_aeval`. -/
theorem _root_.Matrix.IsHermitian.aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : ℝ[X]) :
    (Polynomial.aeval A p).IsHermitian := by
  sorry

/-- **The norm of a polynomial in a Hermitian matrix** is at most the largest value of `|p|` on
its eigenvalues. [Saad2003, §6.11]; [Saad2011, §6.6]. Port of `NLAlib.specNorm_aeval_le`.
Result: polynomial-spectral-bound -/
theorem _root_.Matrix.IsHermitian.specNorm_aeval_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (p : ℝ[X]) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |p.eval x| ≤ c) :
    specNorm (Polynomial.aeval A p) ≤ c := by
  sorry

/-- The norm of a polynomial in a matrix with spectrum in `[a, b]` is at most the largest value
of `|p|` on `[a, b]`. This is the form used with Chebyshev polynomials.
[Saad2003, §6.11.3]. -/
theorem specNorm_aeval_le_of_forall_mem_Icc {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (p : ℝ[X]) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ c) : specNorm (aeval A p) ≤ c := by
  sorry

/-- **The error of a polynomial approximation of `f(A)`** is at most the error of the scalar
approximation on an interval containing the spectrum. This is the bound behind Krylov methods for
`f(A) b`. [Higham2008, §13.2 context]; [Saad2003, §6.11]. -/
theorem specNorm_cfc_sub_aeval_le {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {f : ℝ → ℝ} (p : ℝ[X])
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ Set.Icc a b, |f x - p.eval x| ≤ c) :
    specNorm (cfc f A - aeval A p) ≤ c := by
  sorry

/-- The trace of a polynomial in a Hermitian matrix. -/
theorem _root_.Matrix.IsHermitian.re_trace_aeval {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (p : ℝ[X]) :
    RCLike.re (Polynomial.aeval A p).trace =
      ∑ i ∈ Finset.range (Fintype.card n), p.eval (eigenvalue A i) := by
  sorry

/-- The quadratic form of `p(A)` for positive semidefinite `A` is controlled by `|p|` on an
interval containing the spectrum: the energy-norm bound for a polynomial error.
[Saad2003, Lemma 6.28 context].
Port of `NLAlib.quadForm_aeval_mulVec_le`, there over `ℝ`. -/
theorem re_quadForm_aeval_mulVec_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 ≤ a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (p : ℝ[X]) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ c) (x : n → 𝕜) :
    RCLike.re (quadForm A (aeval A p *ᵥ x)) ≤ c ^ 2 * RCLike.re (quadForm A x) := by
  sorry

/-! ### Intertwining and singular values -/

/-- Powers intertwine: if `B * A = A * C` then `B ^ j * A = A * C ^ j`.
Port of `NLAlib.pow_mul_eq_mul_pow_of_mul_eq`. -/
theorem pow_mul_eq_mul_pow_of_mul_eq_mul {R : Type*} [Semiring R] {B : Matrix m m R}
    {A : Matrix m n R} {C : Matrix n n R} (h : B * A = A * C) (j : ℕ) :
    B ^ j * A = A * C ^ j := by
  sorry

/-- Polynomials intertwine: if `B * A = A * C` then `p(B) * A = A * p(C)`.
Port of `NLAlib.aeval_mul_eq_mul_aeval_of_mul_eq`. -/
theorem aeval_mul_eq_mul_aeval_of_mul_eq_mul {B : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : B * A = A * C) (p : ℝ[X]) : aeval B p * A = A * aeval C p := by
  sorry

/-- **Polynomials in the two Gram matrices intertwine**: `p(A Aᴴ) A = A p(Aᴴ A)`.
Port of `NLAlib.aeval_conjGram_mul_eq_mul_aeval_conjGram`. -/
theorem aeval_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (p : ℝ[X]) :
    aeval (A * Aᴴ) p * A = A * aeval (Aᴴ * A) p := by
  sorry

/-- **A polynomial filter on an SVD.** If `A = U diag(σ) Vᴴ`, then
`A p(Aᴴ A) = U diag(σ_i p(σ_i²)) Vᴴ`, up to the part of `p(Aᴴ A)` outside the row space, which
`A` annihilates. Port of `NLAlib.rectDiag_mul_aeval_gram`, there for a rectangular diagonal. -/
theorem IsSVD.mul_aeval_conjTranspose_mul_self {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V) (p : ℝ[X]) :
    A * aeval (Aᴴ * A) p =
      U * Matrix.diagonal (fun i => ((σ i * p.eval (σ i ^ 2) : ℝ) : 𝕜)) * Vᴴ := by
  sorry

/-- **Singular values of a power-iterated matrix**: `(A Aᴴ)^q A` has singular values
`σ_i ^ (2 q + 1)`. [HalkoMartinssonTropp2011, §4.5].
Port of `NLAlib.singularValues_gram_pow_mul`, there over `ℝ`. -/
theorem singularValues_pow_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (q i : ℕ) :
    singularValues ((A * Aᴴ) ^ q * A) i = singularValues A i ^ (2 * q + 1) := by
  sorry

/-- The rank of a power-iterated matrix is the rank of the matrix.
Port of `NLAlib.rank_gram_pow_mul`. -/
theorem rank_pow_mul_conjTranspose_self_mul (A : Matrix m n 𝕜) (q : ℕ) :
    ((A * Aᴴ) ^ q * A).rank = A.rank := by
  sorry

end NLAlib
