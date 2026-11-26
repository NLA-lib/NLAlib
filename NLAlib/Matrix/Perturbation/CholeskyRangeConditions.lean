/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.CholeskyMixedSchurError

/-!
# Numerical input conditions for finite-range Cholesky

Every field is a scalar inequality depending only on matrix dimension, error allowances,
input spectral scale and margin, and backend finite range. There is no execution, trace,
store or computed-pivot hypothesis.

## Main definitions

* `NLAlib.Computation.CholeskyRangeConditions`: the explicit numerical input range conditions.

## Main results

The stored finite-range Cholesky theorem consumes these conditions together with the input's
spectral band and the backend's arithmetic, square-root and literal laws.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Sufficient input numerical conditions for the existing saved-pivot Cholesky driver.
The full-residual recurrence controls every entry, including retired rows and columns.
The remaining inequalities bound the exact literal, reciprocal, row product, rank-one
product, addition, square root and normalized quotient before each instruction executes.
These are conservative sufficient conditions, not necessary representability conditions. -/
structure CholeskyRangeConditions (N : ℕ) (u τ B μ Ω : ℝ) : Prop where
  /-- The relative error allowance is nonnegative. -/
  roundoff_nonneg : 0 ≤ u
  /-- The relative error allowance is less than one. -/
  roundoff_lt_one : u < 1
  /-- The absolute underflow allowance is nonnegative. -/
  underflow_nonneg : 0 ≤ τ
  /-- The input lower spectral margin is positive. -/
  margin_pos : 0 < μ
  /-- The input lower margin is no larger than the input upper spectral scale. -/
  margin_le_scale : μ ≤ B
  /-- The full-residual propagated error is less than half the input lower margin. -/
  residual_error_lt : choleskyMixedSchurErrorBound u τ B μ N < μ / 2
  /-- The actual rounded diagonal square root stays bounded away from zero. -/
  root_margin_pos : 0 < (1 - u) * Real.sqrt (μ / 2) - τ
  /-- The exact minus-one literal is inside the backend's accepted range. -/
  literal_le : 1 ≤ Ω
  /-- The exact reciprocal coefficient quotient is inside the accepted range. -/
  coefficient_le : (1 + u + τ) / (μ / 2) ≤ Ω
  /-- The coefficient times each saved row entry is inside the accepted range. -/
  row_product_le : ((1 + u) * (1 + u + τ) / (μ / 2) + τ) * (2 * B) ≤ Ω
  /-- Each saved column entry times its rounded scaled row entry is in range. -/
  cell_product_le : (2 * B) *
    ((1 + u) * ((1 + u) * (1 + u + τ) / (μ / 2) + τ) * (2 * B) + τ) ≤ Ω
  /-- Each original residual entry plus its rounded rank-one term is in range. -/
  sum_le : 2 * B + ((1 + u) * (2 * B) *
    ((1 + u) * ((1 + u) * (1 + u + τ) / (μ / 2) + τ) * (2 * B) + τ) + τ) ≤ Ω
  /-- Each exact diagonal square root is inside the accepted range. -/
  root_le : Real.sqrt (2 * B) ≤ Ω
  /-- Every exact suffix normalization quotient is inside the accepted range. -/
  quotient_le : (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - τ) ≤ Ω

end NLAlib.Computation
