/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Matrix.Perturbation.Continuity
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.GramSchmidt

/-!
# Measurability of spectral quantities

For random matrices, the quantities of this library must be measurable functions of the matrix.
Norms, singular values and eigenvalues are continuous, hence measurable. The rank, the
pseudoinverse, the range projector, the condition number, the polar factor and the Gram–Schmidt
factors are not continuous but are Borel measurable.

Matrices carry the product σ-algebra `Matrix.instMeasurableSpace`.

## Main results

* `NLAlib.measurable_specNorm`, `NLAlib.measurable_frobNorm`, `NLAlib.measurable_matrixNorm`.
* `NLAlib.measurable_singularValues`, `NLAlib.measurable_eigenvalue`.
* `NLAlib.measurable_rank`, `NLAlib.measurable_pinv`, `NLAlib.measurable_rangeProjector`,
  `NLAlib.measurable_conditionNumber`.
* `NLAlib.measurable_polarFactor`, `NLAlib.measurable_gramSchmidtQ`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Continuous quantities -/

/-- The spectral norm is measurable. Port of `NLAlib.measurable_specNorm_of_entries`. -/
theorem measurable_specNorm : Measurable (specNorm : Matrix m n 𝕜 → ℝ) := by
  sorry

/-- The Frobenius norm is measurable. Port of `NLAlib.measurable_frobSq_of_entries`. -/
theorem measurable_frobNorm : Measurable (frobNorm : Matrix m n 𝕜 → ℝ) := by
  sorry

/-- Every unitarily invariant norm is measurable. -/
theorem SymmetricGauge.measurable_matrixNorm (Φ : SymmetricGauge) :
    Measurable (Φ.matrixNorm : Matrix m n 𝕜 → ℝ) := by
  sorry

/-- Each singular value is measurable. -/
theorem measurable_singularValues (k : ℕ) :
    Measurable fun A : Matrix m n 𝕜 => singularValues A k := by
  sorry

/-- Each sorted eigenvalue is measurable (it is continuous on the closed set of Hermitian
matrices and zero elsewhere). -/
theorem measurable_eigenvalue [DecidableEq n] (k : ℕ) :
    Measurable fun A : Matrix n n 𝕜 => eigenvalue A k := by
  sorry

/-! ### Quantities that are not continuous -/

/-- The rank is measurable. -/
theorem measurable_rank : Measurable fun A : Matrix m n 𝕜 => A.rank := by
  sorry

/-- **The pseudoinverse is measurable.** Port of `NLAlib.measurable_pinvL_entry_of` and
`NLAlib.measurable_pinvR_entry`. -/
theorem measurable_pinv [DecidableEq m] [DecidableEq n] :
    Measurable (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  sorry

/-- The orthogonal projector onto the range is measurable. -/
theorem measurable_rangeProjector [DecidableEq m] [DecidableEq n] :
    Measurable (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) := by
  sorry

/-- The condition number is measurable. -/
theorem measurable_conditionNumber [DecidableEq m] [DecidableEq n] :
    Measurable (conditionNumber : Matrix m n 𝕜 → ℝ) := by
  sorry

/-- The polar factor is measurable. Port of `NLAlib.measurable_polarFrame_entry`. -/
theorem measurable_polarFactor [DecidableEq m] [DecidableEq n] :
    Measurable (polarFactor : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  sorry

/-- The Gram–Schmidt orthonormalisation is measurable.
Port of `NLAlib.measurable_qrNormalizedArray`. -/
theorem measurable_gramSchmidtQ [LinearOrder n] [LocallyFiniteOrderBot n] [DecidableEq n] :
    Measurable (gramSchmidtQ : Matrix m n 𝕜 → Matrix m n 𝕜) := by
  sorry

end NLAlib
