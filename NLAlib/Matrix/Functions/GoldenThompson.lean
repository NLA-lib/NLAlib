/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Matrix.Functions.Complexification

/-!
# The Golden–Thompson inequality

For Hermitian `H` and `K`, `tr exp (H + K) ≤ tr (exp H · exp K)`. It replaces the scalar identity
`e^{h + k} = e^h e^k` in the Ahlswede–Winter approach to matrix concentration.

## Main results

* `NLAlib.re_trace_exp_add_le`: the Golden–Thompson inequality.
* `Matrix.PosDef.re_trace_exp_add_cfc_log_le`: the form `tr exp (H + log X) ≤ tr (exp H · X)`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a product of two positive semidefinite matrices is real and nonnegative. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace := by
  sorry

/-- **The Golden–Thompson inequality.** For Hermitian `H` and `K`,
`tr exp (H + K) ≤ tr (exp H · exp K)`.
[Bhatia1997, §IX.3]; [Tropp2015, §3.1 notes].
Port of `NLAlib.golden_thompson`, there over `ℂ`.
Result: golden-thompson -/
theorem re_trace_exp_add_le {H K : Matrix n n 𝕜} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    RCLike.re (exp (H + K)).trace ≤ RCLike.re (exp H * exp K).trace := by
  sorry

/-- The Golden–Thompson inequality with a logarithm: for Hermitian `H` and positive definite
`X`, `tr exp (H + log X) ≤ tr (exp H · X)`.
Port of `NLAlib.traceExp_add_matrixLog_le`, there over `ℂ`. -/
theorem _root_.Matrix.PosDef.re_trace_exp_add_cfc_log_le {H X : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hX : X.PosDef) :
    RCLike.re (exp (H + cfc Real.log X)).trace ≤ RCLike.re (exp H * X).trace := by
  sorry

end NLAlib
