/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Laplace

/-!
# The generalised matrix Laplace transform bound

For a random Hermitian matrix `Y` and a nonnegative function `ψ`, nondecreasing on `[0, ∞)`,
`P(t ≤ λ_max Y) ≤ E tr ψ(Y) / ψ(t)` for `t ≥ 0` with `ψ t > 0` (Tropp 2015, Proposition 7.4.1).
The exponential `ψ a = e^{θ a}` gives the matrix Laplace transform bound of
`NLAlib/Probability/MatrixConcentration/Laplace.lean`; the intrinsic-dimension tails
(`NLAlib/Probability/MatrixConcentration/IntrinsicDimension.lean`) use `ψ a = e^{θ a} - θ a - 1`
and `ψ a = max (e^{θ a} - 1) 0`, which vanish at `0` and so let the intrinsic dimension replace
the ambient dimension.

This skeleton file is to be merged into `Laplace.lean`, which owns the subject (P5b, D6 and §8).

## Main results

* `NLAlib.measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div`: the generalised bound.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §7.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {Y : Ω → Matrix n n 𝕜}

/-- **The generalised matrix Laplace transform bound**: for `ψ ≥ 0` nondecreasing on `[0, ∞)`,
`t ≥ 0` and `ψ t > 0`, `P(t ≤ λ_max Y) ≤ E tr ψ(Y) / ψ(t)`.
[Tropp2015, Proposition 7.4.1]; here for any measure (the proof is Markov's inequality,
`mul_meas_ge_le_integral_of_nonneg`, which needs no finiteness), over any `RCLike` field. No
continuity of `ψ` is assumed: the spectrum of a Hermitian matrix is finite, so `cfc ψ` is never
its junk value at a Hermitian argument. `[Nonempty n]` is needed: for empty `n` and `t = 0` the
event is everything and the right side `0`. The integrability hypothesis `hint` excludes the junk
value `0` of the integral.
Result: generalized-matrix-laplace -/
theorem measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {ψ : ℝ → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ : MonotoneOn ψ (Set.Ici 0))
    (hint : Integrable (fun ω => RCLike.re (cfc ψ (Y ω)).trace) μ) {t : ℝ} (ht : 0 ≤ t)
    (hψt : 0 < ψ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤ (∫ ω, RCLike.re (cfc ψ (Y ω)).trace ∂μ) / ψ t := by
  set f : Ω → ℝ := fun ω => RCLike.re (cfc ψ (Y ω)).trace with hf
  have hf0 : 0 ≤ᵐ[μ] f := by
    filter_upwards [hY] with ω hω
    simp only [hf, Pi.zero_apply, hω.re_trace_cfc]
    exact Finset.sum_nonneg fun i _ => hψ0 _
  have hfin : μ {ω | ψ t ≤ f ω} ≠ ⊤ := by
    refine (lt_of_le_of_lt (measure_mono fun ω (h : ψ t ≤ f ω) => ?_)
      (hint.measure_norm_ge_lt_top hψt)).ne
    exact h.trans (Real.le_norm_self _)
  have hsub : μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤ μ.real {ω | ψ t ≤ f ω} := by
    refine ENNReal.toReal_mono hfin (measure_mono_ae ?_)
    filter_upwards [hY] with ω hω (h : t ≤ eigenvalue (Y ω) 0)
    exact (hψ ht (ht.trans h) h).trans
      (hω.apply_eigenvalue_zero_le_re_trace_cfc fun x _ => hψ0 x)
  rw [le_div_iff₀ hψt, mul_comm]
  exact (mul_le_mul_of_nonneg_left hsub hψt.le).trans
    (mul_meas_ge_le_integral_of_nonneg hf0 hint _)

end NLAlib
