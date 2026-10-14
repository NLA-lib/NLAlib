/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Law

/-!
# Gaussian matrices

`NLAlib.gaussianMatrix m n` is the law of an `m × n` real matrix with independent standard
Gaussian entries, written as independent rows, each a standard Gaussian vector:
`Measure.pi fun _ : m => gaussianVector n`. It is an `abbrev`, so P0's product-law lemmas apply
directly: the rows are `ProbabilityTheory.HasLaw.eval`, their independence
`ProbabilityTheory.HasLaw.iIndepFun_eval`, the entries `ProbabilityTheory.HasLaw.entry` and
`ProbabilityTheory.HasLaw.iIndepFun_entry`. Since `Matrix` is a `def`, Mathlib's instances about
`Measure.pi` are not found at `Measure (Matrix m n ℝ)`; the ones the library needs are stated here.

A Gaussian matrix read as a vector indexed by `m × n` (`Function.uncurry`) is a standard Gaussian
vector, and its Frobenius norm is that vector's Euclidean norm; this is how the vector results of
the probability layer apply to it. The law is real; a complex Gaussian matrix will be a separate
law (`docs/design/Probability-P2.md` §7).

## Main definitions

* `NLAlib.gaussianMatrix m n`.

## Main results

* `NLAlib.hasLaw_uncurry_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_gaussianMatrix_of_hasLaw_uncurry`.
* `NLAlib.hasLaw_col_of_hasLaw_gaussianMatrix`, `NLAlib.iIndepFun_col_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- The law of a matrix with independent standard Gaussian entries: independent rows, each a
standard Gaussian vector. -/
noncomputable abbrev gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℝ) :=
  Measure.pi fun _ : m => gaussianVector n

instance isProbabilityMeasure_gaussianMatrix : IsProbabilityMeasure (gaussianMatrix m n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : m => gaussianVector n))

instance isGaussian_gaussianMatrix : IsGaussian (gaussianMatrix m n) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    { toFun := fun v => Matrix.of (Function.curry v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  have h : gaussianMatrix m n = (gaussianVector (m × n)).map L :=
    (measurePreserving_curry_pi (ν := fun _ _ => gaussianReal 0 1)).map_eq.symm
  rw [h]
  exact isGaussian_map_of_measurable (MeasurableEquiv.curry m n ℝ).measurable

/-- A Gaussian matrix read as a vector indexed by `m × n` is a standard Gaussian vector. -/
theorem hasLaw_uncurry_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω => Function.uncurry (X ω)) (gaussianVector (m × n)) μ :=
  (measurePreserving_curry_pi (ν := fun _ _ => gaussianReal 0 1)).symm.fun_comp_hasLaw hX

/-- A random matrix whose entries, as a vector indexed by `m × n`, form a standard Gaussian vector
is a Gaussian matrix. -/
theorem hasLaw_gaussianMatrix_of_hasLaw_uncurry
    (hX : HasLaw (fun ω => Function.uncurry (X ω)) (gaussianVector (m × n)) μ) :
    HasLaw X (gaussianMatrix m n) μ :=
  (measurePreserving_curry_pi (ν := fun _ _ => gaussianReal 0 1)).fun_comp_hasLaw hX

/-- The transpose of a Gaussian matrix is Gaussian: transposition permutes the coordinates of
the flattened standard Gaussian vector. -/
private theorem hasLaw_transpose (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω j i => X ω i j) (Measure.pi fun _ : n => gaussianVector m) μ := by
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry (X := fun ω => (X ω)ᵀ) ?_
  exact (measurePreserving_arrowCongr' (fun _ : m × n => gaussianReal 0 1)
    (fun _ : n × m => gaussianReal 0 1) (Equiv.prodComm m n) (MeasurableEquiv.refl ℝ)
    fun _ => MeasurePreserving.id _).fun_comp_hasLaw (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)

/-- The columns of a Gaussian matrix are standard Gaussian vectors. -/
theorem hasLaw_col_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) (j : n) :
    HasLaw (fun ω i => X ω i j) (gaussianVector m) μ :=
  (hasLaw_transpose hX).eval j

/-- The columns of a Gaussian matrix are independent. -/
theorem iIndepFun_col_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    iIndepFun (fun j ω i => X ω i j) μ :=
  (hasLaw_transpose hX).iIndepFun_eval

end NLAlib
