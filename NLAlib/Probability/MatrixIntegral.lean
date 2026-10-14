/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.ForMathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Probability.Isotropic

/-!
# Integrals of matrix-valued functions

The expectation of a random matrix `X : Ω → Matrix m n 𝕜` is Mathlib's Bochner integral
`∫ ω, X ω ∂μ`, which needs a normed-space structure on matrices. NLAlib uses one scope for it,
library-wide: `open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md`
entry 13), with the real normed-space instance of
`NLAlib/ForMathlib/Analysis/CStarAlgebra/Matrix.lean`. The value of the integral does not depend
on the norm, and the statements here mention none: integrability and the integral are entrywise,
and the integral commutes with the conjugate transpose, reindexing, submatrices, the trace,
products with fixed matrices and quadratic forms. An almost surely Hermitian (positive
semidefinite) random matrix has a Hermitian (positive semidefinite) mean, with no integrability
hypothesis, because a non-integrable function integrates to `0`. Loewner monotonicity is Mathlib's
`MeasureTheory.integral_mono_ae`, through `Matrix.instClosedIciTopology`.

## Main results

* `Matrix.integrable_iff`, `Matrix.memLp_iff`, `Matrix.integral_apply`: entrywise.
* `Matrix.integral_conjTranspose`, `Matrix.integral_reindex`, `Matrix.integral_submatrix`,
  `Matrix.integral_trace`, `Matrix.integral_const_mul`, `Matrix.integral_mul_const`,
  `Matrix.integral_quadForm`.
* `Matrix.isHermitian_integral`, `Matrix.posSemidef_integral`, `Matrix.posDef_integral`.
* `NLAlib.IsIsotropic.integral_vecMulVec`: `E [X Xᴴ] = 1`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l m n k : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq k]

section Entrywise

variable {X : Ω → Matrix m n 𝕜}

/-- A random matrix is integrable exactly when its entries are. -/
theorem _root_.Matrix.integrable_iff :
    Integrable X μ ↔ ∀ i j, Integrable (fun ω => X ω i j) μ := by
  sorry

/-- A random matrix is in `Lᵖ` exactly when its entries are. -/
theorem _root_.Matrix.memLp_iff {p : ℝ≥0∞} :
    MemLp X p μ ↔ ∀ i j, MemLp (fun ω => X ω i j) p μ := by
  sorry

/-- The entries of the mean of a random matrix are the means of its entries. Integrability of
the entries is needed: if one entry is not integrable, the integral is `0` while the other
entries may have nonzero means. -/
theorem _root_.Matrix.integral_apply (hX : ∀ i j, Integrable (fun ω => X ω i j) μ) (i : m)
    (j : n) : (∫ ω, X ω ∂μ) i j = ∫ ω, X ω i j ∂μ := by
  sorry

end Entrywise

section Linear

variable {X : Ω → Matrix m n 𝕜}

/-- The conjugate transpose commutes with the integral; no integrability is needed, since the
conjugate transpose is a real-linear isometric equivalence. -/
theorem _root_.Matrix.integral_conjTranspose (X : Ω → Matrix m n 𝕜) :
    ∫ ω, (X ω)ᴴ ∂μ = (∫ ω, X ω ∂μ)ᴴ := by
  sorry

/-- Reindexing commutes with the integral; no integrability is needed. -/
theorem _root_.Matrix.integral_reindex {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (e : m ≃ m') (f : n ≃ n') (X : Ω → Matrix m n 𝕜) :
    ∫ ω, Matrix.reindex e f (X ω) ∂μ = Matrix.reindex e f (∫ ω, X ω ∂μ) := by
  sorry

/-- A submatrix of the mean is the mean of the submatrix. -/
theorem _root_.Matrix.integral_submatrix (hX : Integrable X μ) (r : l → m) (c : k → n) :
    ∫ ω, (X ω).submatrix r c ∂μ = (∫ ω, X ω ∂μ).submatrix r c := by
  sorry

/-- The trace commutes with the integral. -/
theorem _root_.Matrix.integral_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    ∫ ω, (X ω).trace ∂μ = (∫ ω, X ω ∂μ).trace := by
  sorry

/-- A fixed left factor comes out of the integral. Integrability is needed: `A * X` may be
integrable when `X` is not. -/
theorem _root_.Matrix.integral_const_mul (A : Matrix l m 𝕜) (hX : Integrable X μ) :
    ∫ ω, A * X ω ∂μ = A * ∫ ω, X ω ∂μ := by
  sorry

/-- A fixed right factor comes out of the integral. -/
theorem _root_.Matrix.integral_mul_const (hX : Integrable X μ) (B : Matrix n k 𝕜) :
    ∫ ω, X ω * B ∂μ = (∫ ω, X ω ∂μ) * B := by
  sorry

/-- The quadratic form of the mean is the mean of the quadratic form. -/
theorem _root_.Matrix.integral_quadForm {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ)
    (z : n → 𝕜) : ∫ ω, quadForm (X ω) z ∂μ = quadForm (∫ ω, X ω ∂μ) z := by
  sorry

end Linear

section Order

variable {X : Ω → Matrix n n 𝕜}

/-- An almost surely Hermitian random matrix has a Hermitian mean. No integrability is needed:
a non-integrable function integrates to `0`. -/
theorem _root_.Matrix.isHermitian_integral (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    (∫ ω, X ω ∂μ).IsHermitian := by
  sorry

/-- An almost surely positive semidefinite random matrix has a positive semidefinite mean. No
integrability is needed. -/
theorem _root_.Matrix.posSemidef_integral (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    (∫ ω, X ω ∂μ).PosSemidef := by
  sorry

/-- An integrable, almost surely positive definite random matrix has a positive definite mean,
for a nonzero measure. -/
theorem _root_.Matrix.posDef_integral [NeZero μ] (hX : Integrable X μ)
    (h : ∀ᵐ ω ∂μ, (X ω).PosDef) : (∫ ω, X ω ∂μ).PosDef := by
  sorry

end Order

/-- The second-moment matrix of an isotropic vector is the identity: `E [X Xᴴ] = 1`. -/
theorem IsIsotropic.integral_vecMulVec {X : Ω → n → 𝕜} (hX : IsIsotropic X μ) :
    ∫ ω, Matrix.vecMulVec (X ω) (star (X ω)) ∂μ = 1 := by
  sorry

end NLAlib
