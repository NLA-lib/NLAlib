/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Normed

/-!
# Derivatives of matrix-valued functions of one variable

Derivatives of the product, the powers, the determinant (Jacobi's formula), the inverse and the
trace of powers of a differentiable one-parameter family of matrices. Hypotheses and matrix-valued
conclusions are entrywise, `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t`, so the statements
do not depend on a choice of matrix norm. Upstream candidates for a file
`Mathlib.Analysis.Calculus.Deriv.Matrix`.

## Main results

* `Matrix.hasDerivAt_iff_forall_apply`: the entrywise form of a derivative.
* `Matrix.hasDerivAt_mul_apply`, `Matrix.hasDerivAt_pow_succ_apply`: products and powers.
* `Matrix.hasDerivAt_det`: Jacobi's formula `(det A)' = tr (adj A · A')`.
* `Matrix.hasDerivAt_log_det`: `(log det A)' = tr (A⁻¹ A')`.
* `Matrix.hasDerivAt_inv_apply`: `(A⁻¹)' = -A⁻¹ A' A⁻¹`.
* `Matrix.hasDerivAt_trace_pow_succ`: `(tr Aᵏ⁺¹)' = (k + 1) tr (A' Aᵏ)`.
-/

@[expose] public section

namespace Matrix

variable {𝔽 : Type*} [NontriviallyNormedField 𝔽] {R : Type*} [NormedCommRing R]
  [NormedAlgebra 𝔽 R] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

open scoped Matrix.Norms.Elementwise in
/-- With the entrywise norm, a matrix family is differentiable exactly when its entries are. The
same holds for every norm on matrices, all of which induce the product topology. -/
theorem hasDerivAt_iff_forall_apply {A : 𝔽 → Matrix m n R} {A' : Matrix m n R} {t : 𝔽} :
    HasDerivAt A A' t ↔ ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t := by
  sorry

/-- The derivative of a product of two matrix families, entrywise. -/
theorem hasDerivAt_mul_apply {A : 𝔽 → Matrix l m R} {B : 𝔽 → Matrix m n R} {A' : Matrix l m R}
    {B' : Matrix m n R} {t : 𝔽} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i : l) (j : n) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  sorry

/-- The derivative of the trace of a matrix family. -/
theorem hasDerivAt_trace {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => (A s).trace) A'.trace t := by
  sorry

variable [DecidableEq n]

/-- The derivative of a power of a matrix family, entrywise:
`(Aᵏ⁺¹)' = ∑_{i + j = k} Aⁱ A' Aʲ`. -/
theorem hasDerivAt_pow_succ_apply {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (k : ℕ) (i j : n) :
    HasDerivAt (fun s => (A s ^ (k + 1)) i j)
      ((∑ p ∈ Finset.antidiagonal k, A t ^ p.1 * A' * A t ^ p.2) i j) t := by
  sorry

/-- **The derivative of the trace of a power**: `(tr Aᵏ⁺¹)' = (k + 1) tr (A' Aᵏ)`.
Port of `NLAlib.hasDerivAt_matrix_trace_pow`, there over `ℝ` in the operator norm. -/
theorem hasDerivAt_trace_pow_succ {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (k : ℕ) :
    HasDerivAt (fun s => (A s ^ (k + 1)).trace) ((k + 1) * (A' * A t ^ k).trace) t := by
  sorry

/-- The sum over rows of the determinants with one row replaced is the trace against the
adjugate. Port of `NLAlib.sum_det_updateRow_eq_trace_adjugate_mul`, there over `ℝ`. -/
theorem sum_det_updateRow {S : Type*} [CommRing S] (A H : Matrix n n S) :
    ∑ i, (A.updateRow i (H i)).det = (A.adjugate * H).trace := by
  sorry

/-- **Jacobi's formula**: `(det A)' = tr (adj A · A')`.
Port of `NLAlib.hasDerivAt_det`, there over `ℝ` in the entrywise norm. -/
theorem hasDerivAt_det {A : 𝔽 → Matrix n n R} {A' : Matrix n n R} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * A').trace t := by
  sorry

/-- **The derivative of the inverse**, entrywise: `(A⁻¹)' = -A⁻¹ A' A⁻¹` where `A t` is
invertible. Port of `NLAlib.hasDerivAt_matrix_inv`, there over `ℝ` in the operator norm. -/
theorem hasDerivAt_inv_apply {A : 𝔽 → Matrix n n 𝔽} {A' : Matrix n n 𝔽} {t : 𝔽}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (ht : IsUnit (A t).det) (i j : n) :
    HasDerivAt (fun s => (A s)⁻¹ i j) ((-((A t)⁻¹ * A' * (A t)⁻¹)) i j) t := by
  sorry

/-- **The derivative of the logarithm of the determinant**: `(log det A)' = tr (A⁻¹ A')` where
`A t` is invertible. Port of `NLAlib.hasDerivAt_log_det`. -/
theorem hasDerivAt_log_det {A : ℝ → Matrix n n ℝ} {A' : Matrix n n ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (ht : (A t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (A s).det) ((A t)⁻¹ * A').trace t := by
  sorry

end Matrix
