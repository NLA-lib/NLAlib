/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.GoldenThompson
public import NLAlib.Matrix.Functions.OperatorMonotone

/-!
# Lieb's concavity theorem

For a fixed Hermitian `H`, the function `A ↦ tr exp (H + log A)` is concave on positive definite
matrices. This is the theorem behind Tropp's master inequality for sums of independent random
matrices. The proof follows Tropp: the relative entropy
`D(A; H) = tr (A (log A - log H) - (A - H))` is nonnegative (Klein) and jointly convex (through
the operator convexity of the matrix perspective), and `tr exp (H + log A)` is a partial maximum
of an affine function minus a relative entropy.

## Main definitions

* `NLAlib.relativeEntropy`: the matrix relative entropy `tr (A (log A - log H) - (A - H))`.

## Main results

* `NLAlib.relativeEntropy_nonneg`: nonnegativity.
* `NLAlib.convexOn_relativeEntropy`: joint convexity.
* `NLAlib.isGreatest_re_trace_exp_add_cfc_log`: the variational formula.
* `NLAlib.concaveOn_re_trace_exp_add_cfc_log`: Lieb's theorem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **matrix relative entropy** of two positive definite matrices,
`D(A; H) = tr (A (log A - log H) - (A - H))`: the Bregman divergence of `A ↦ tr (A log A - A)`.
[Tropp2015, Definition 8.3.1]. Port of `NLAlib.relativeEntropy`. -/
noncomputable def relativeEntropy (A H : Matrix n n 𝕜) : ℝ :=
  RCLike.re (A * (cfc Real.log A - cfc Real.log H) - (A - H)).trace

/-- The relative entropy of a matrix with itself vanishes. -/
@[simp]
theorem relativeEntropy_self (A : Matrix n n 𝕜) : relativeEntropy A A = 0 := by
  sorry

/-- **The matrix relative entropy is nonnegative** (Klein's inequality).
[Tropp2015, Proposition 8.3.5]. Port of `NLAlib.relativeEntropy_nonneg`, there over `ℂ`.
Result: relative-entropy -/
theorem relativeEntropy_nonneg {A H : Matrix n n 𝕜} (hA : A.PosDef) (hH : H.PosDef) :
    0 ≤ relativeEntropy A H := by
  sorry

/-- **The matrix relative entropy is jointly convex** (Lindblad).
[Tropp2015, §8.3 and §8.8]; [Lindblad1974].
Port of `NLAlib.convexOn_relativeEntropy`, there over `ℂ` on `Fin d`.
Result: relative-entropy -/
theorem convexOn_relativeEntropy :
    ConvexOn ℝ {P : Matrix n n 𝕜 × Matrix n n 𝕜 | P.1.PosDef ∧ P.2.PosDef}
      fun P => relativeEntropy P.1 P.2 := by
  sorry

/-- **A variational formula for the trace.** For positive definite `M`,
`tr M = max_T tr (T log M - T log T + T)` over positive definite `T`.
[Tropp2015, §8.3]. Port of `NLAlib.isGreatest_variational_trace`. -/
theorem isGreatest_re_trace_mul_cfc_log_sub {M : Matrix n n 𝕜} (hM : M.PosDef) :
    IsGreatest
      ((fun T : Matrix n n 𝕜 =>
        RCLike.re (T * cfc Real.log M - T * cfc Real.log T + T).trace) '' {T | T.PosDef})
      (RCLike.re M.trace) := by
  sorry

/-- **The variational formula behind Lieb's theorem**: for Hermitian `H` and positive definite
`A`, `tr exp (H + log A) = max_T [tr (T H) + tr A - D(T; A)]` over positive definite `T`.
[Tropp2015, §8.3].
Port of `NLAlib.isGreatest_variational_traceExp`, there over `ℂ` on `Fin d`. -/
theorem isGreatest_re_trace_exp_add_cfc_log {H A : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hA : A.PosDef) :
    IsGreatest
      ((fun T : Matrix n n 𝕜 =>
        RCLike.re (T * H).trace + RCLike.re A.trace - relativeEntropy T A) '' {T | T.PosDef})
      (RCLike.re (exp (H + cfc Real.log A)).trace) := by
  sorry

/-- **Lieb's concavity theorem.** For a fixed Hermitian `H`, `A ↦ tr exp (H + log A)` is concave
on the positive definite matrices.
[Lieb1973]; [Tropp2015, Theorem 8.1.1].
Port of `NLAlib.lieb_concavity`, there over `ℂ`.
Result: lieb-concavity -/
theorem concaveOn_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      fun A => RCLike.re (exp (H + cfc Real.log A)).trace := by
  sorry

end NLAlib
