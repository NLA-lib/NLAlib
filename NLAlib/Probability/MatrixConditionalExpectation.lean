/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Probability.MatrixIntegral

/-!
# Conditional expectations of matrix-valued functions

The conditional expectation of a random matrix `X : Ω → Matrix m n 𝕜` given a σ-algebra `m` is
Mathlib's `μ[X | m]`, under the same normed structure as the integral:
`open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md` entry 13;
`NLAlib/Probability/MatrixIntegral.lean`). It is entrywise, commutes with the conjugate
transpose, the trace and the Hermitian dilation, and preserves almost sure Hermitian, positive
semidefinite and positive definite values. The conjugate transpose, Hermitian and positive
semidefinite statements need no integrability, because a non-integrable function has conditional
expectation `0`. Loewner monotonicity is Mathlib's `MeasureTheory.condExp_mono`, through
`Matrix.instOrderClosedTopology` (`NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean`), and is
not restated.

The conditional sibling of `NLAlib/Probability/MatrixIntegral.lean`
(`docs/design/Probability-P5d.md` §3.1).

## Main results

* `Matrix.condExp_apply`, `Matrix.condExp_conjTranspose`, `Matrix.condExp_trace`.
* `Matrix.ae_isHermitian_condExp`, `Matrix.ae_posSemidef_condExp`, `Matrix.ae_posDef_condExp`.
* `Matrix.condExp_dilation`, `Matrix.condExp_dilation_sq`: for the rectangular Freedman
  inequality.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l n : Type*} [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]

omit [DecidableEq l] in
/-- The conditional expectation of a random matrix is entrywise.
Proof: `ContinuousLinearMap.comp_condExp_comm` with the entry `(i, j)` as a real continuous
linear map. Easy. -/
theorem _root_.Matrix.condExp_apply {X : Ω → Matrix l n 𝕜} (hX : Integrable X μ) (i : l)
    (j : n) : (fun ω => μ[X | m] ω i j) =ᵐ[μ] μ[fun ω => X ω i j | m] := by
  sorry

/-- The conditional expectation commutes with the conjugate transpose. No integrability
hypothesis.
Proof: case split on `Integrable X μ`. If integrable, `ContinuousLinearMap.comp_condExp_comm`
with the conjugate transpose as a real continuous linear map; if not, neither is
`fun ω => (X ω)ᴴ` (the conjugate transpose is an isometric real linear equivalence), and both
sides are `0` by `condExp_of_not_integrable`. Easy. -/
theorem _root_.Matrix.condExp_conjTranspose (X : Ω → Matrix l n 𝕜) :
    μ[fun ω => (X ω)ᴴ | m] =ᵐ[μ] fun ω => (μ[X | m] ω)ᴴ := by
  sorry

/-- The conditional expectation commutes with the trace.
Proof: `ContinuousLinearMap.comp_condExp_comm` with `Matrix.traceLinearMap`. Easy. -/
theorem _root_.Matrix.condExp_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    (fun ω => (μ[X | m] ω).trace) =ᵐ[μ] μ[fun ω => (X ω).trace | m] := by
  sorry

/-- An almost surely Hermitian random matrix has an almost surely Hermitian conditional
expectation. No integrability hypothesis.
Proof: `Matrix.condExp_conjTranspose` and `condExp_congr_ae`. Easy. -/
theorem _root_.Matrix.ae_isHermitian_condExp {X : Ω → Matrix n n 𝕜}
    (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) : ∀ᵐ ω ∂μ, (μ[X | m] ω).IsHermitian := by
  sorry

/-- An almost surely positive semidefinite random matrix has an almost surely positive
semidefinite conditional expectation. No integrability hypothesis.
Proof: Mathlib's `condExp_nonneg` in the Loewner order, with `Matrix.nonneg_iff_posSemidef`.
Easy. -/
theorem _root_.Matrix.ae_posSemidef_condExp {X : Ω → Matrix n n 𝕜}
    (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) : ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef := by
  sorry

/-- An integrable, almost surely positive definite random matrix has an almost surely positive
definite conditional expectation, under a finite measure. This removes the hypothesis
`(μ[exp X | m] ω).PosDef` from conditional Lieb.
Proof: with `f = min (λ_min X) 1`, integrable and almost surely positive, `X ≥ f • 1`, so
`μ[X | m] ≥ μ[f | m] • 1` by `condExp_mono`, and `μ[f | m] > 0` almost surely (the
conditional expectation of an almost surely positive integrable function, on the set where it
is `≤ 0`, integrates to a nonpositive number, so that set is null). Medium. -/
theorem _root_.Matrix.ae_posDef_condExp (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) (h : ∀ᵐ ω ∂μ, (X ω).PosDef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosDef := by
  sorry

/-- The conditional expectation of the Hermitian dilation of an integrable random matrix is the
dilation of its conditional expectation. The conditional form of `NLAlib.integral_dilation`.
Proof: `ContinuousLinearMap.comp_condExp_comm` with the dilation as a real continuous linear map.
Easy. -/
theorem _root_.Matrix.condExp_dilation {S : Ω → Matrix l n 𝕜} (hS : Integrable S μ) :
    μ[fun ω => dilation (S ω) | m] =ᵐ[μ] fun ω => dilation (μ[S | m] ω) := by
  sorry

/-- The conditional expectation of the square of a dilation is block diagonal, with the
conditional expectations of `S Sᴴ` and `Sᴴ S` on the diagonal. The conditional form of the
`integral_dilation_sq` step of `NLAlib/Probability/MatrixConcentration/Bernstein.lean`.
Proof: `dilation_mul_dilation`, then `ContinuousLinearMap.comp_condExp_comm` with the block
diagonal embedding of `Matrix l l 𝕜 × Matrix n n 𝕜` and Mathlib's conditional expectation of a
pair (`condExp` of `Prod.fst`, `Prod.snd` through `comp_condExp_comm`); `S Sᴴ` and `Sᴴ S` are
integrable by Hölder from `MemLp S 2 μ`. Easy to medium. -/
theorem _root_.Matrix.condExp_dilation_sq {S : Ω → Matrix l n 𝕜}
    (hS : MemLp S 2 μ) :
    μ[fun ω => dilation (S ω) ^ 2 | m] =ᵐ[μ] fun ω =>
      Matrix.fromBlocks (μ[fun ω' => S ω' * (S ω')ᴴ | m] ω) 0 0
        (μ[fun ω' => (S ω')ᴴ * S ω' | m] ω) := by
  sorry

end NLAlib
