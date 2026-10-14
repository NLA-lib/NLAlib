/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# The rank of a Gaussian matrix

A nonzero polynomial in independent real coordinates with an atomless law is almost surely
nonzero. Minors are polynomials in the entries, so a standard Gaussian matrix has full rank almost
surely, and so does every Gaussian sketch `A G` up to the rank of `A`:
`rank (A G) = min (rank A) (card n)` almost surely. In particular `(A G)ᴴ (A G)` is almost surely
invertible when `card n ≤ rank A`.

## Main results

* `NLAlib.ae_eval_ne_zero_of_ne_zero`.
* `NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- A nonzero polynomial in independent coordinates with an atomless law is almost surely
nonzero. -/
theorem ae_eval_ne_zero_of_ne_zero {ι : Type*} [Fintype ι] {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {f : MvPolynomial ι ℝ} (hf : f ≠ 0) :
    ∀ᵐ x ∂Measure.pi fun _ : ι => ν, MvPolynomial.eval x f ≠ 0 := by
  sorry

/-- A standard Gaussian matrix has full rank almost surely. -/
theorem ae_rank_eq_min_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (X ω).rank = min (Fintype.card m) (Fintype.card n) := by
  sorry

/-- **The rank of a Gaussian sketch**: `rank (A G) = min (rank A) (card n)` almost surely. -/
theorem ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix {l : Type*} [Fintype l] (A : Matrix l m ℝ)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card n) := by
  sorry

/-- The Gram matrix of a Gaussian sketch is almost surely invertible when the sketch is no wider
than the rank of `A`. -/
theorem ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix [DecidableEq n] {l : Type*}
    [Fintype l] {A : Matrix l m ℝ} (hA : Fintype.card n ≤ A.rank)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, IsUnit ((A * X ω)ᴴ * (A * X ω)) := by
  sorry

end NLAlib
