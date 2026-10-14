/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TracePowers
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.GaussianIntegrationByPartsGrowth
public import NLAlib.Probability.Distributions.RademacherSymmetry
public import NLAlib.Probability.MatrixIntegral

/-!
# Trace moments of matrix series and the noncommutative Khintchine inequality

For a matrix series `Y = ∑ i, g i • A i` with real coefficients `g` and Hermitian `A i`, the even
trace moments satisfy `E tr Y^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p` when `g` is a standard Gaussian
vector or a vector of independent random signs: the noncommutative Khintchine inequality in trace
form. Both follow from one law-free step, which closes the moment recursion
`E tr Y^{2q+2} ≤ (2q + 1) E tr (V Y^{2q})` by trace Young; the two laws enter only through their
recursions, by Stein's identity coordinate by coordinate (Gaussian) or by flipping one sign at a
time (Rademacher). The second moment `E Y² = ∑ A i²` holds for any isotropic coefficient vector,
with no Hermitian hypothesis.

The spectral-norm moments `E ‖Y‖^{2p} ≤ (2p - 1)^p d ‖∑ A i²‖^p` compose the headline with
`specNorm_pow_le_re_trace_pow` and `re_trace_pow_le_card_mul_specNorm_pow` and are not stated.

## Main results

* `NLAlib.IsIsotropic.integral_sum_smul_sq`: `E (∑ ε i • A i)² = ∑ A i²`.
* `NLAlib.integral_re_trace_pow_le_of_recursion`: the law-free absorption step.
* `NLAlib.integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector`,
  `NLAlib.integral_re_trace_sum_smul_pow_le_of_hasLaw_rademacherVector`: noncommutative
  Khintchine.

## References

* [L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration
  inequalities via the method of exchangeable pairs*][MackeyEtAl2014], §7.
* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
  {A : ι → Matrix n n 𝕜}

/-! ### The second moment -/

/-- A matrix series with isotropic real coefficients has second moment `E [Y²] = ∑ A i²`. No
Hermitian hypothesis, no independence and no probability measure: isotropy is all that is used.
[Tropp2015, chapter 4] (there for Gaussian and Rademacher coefficients). -/
theorem IsIsotropic.integral_sum_smul_sq [DecidableEq ι] {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : ∫ ω, (∑ i, ε ω i • A i) ^ 2 ∂μ = ∑ i, A i ^ 2 := by
  sorry

/-- The square of a matrix series with isotropic real coefficients is integrable, so
`IsIsotropic.integral_sum_smul_sq` is not between junk values. -/
theorem IsIsotropic.integrable_sum_smul_sq [DecidableEq ι] {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : Integrable (fun ω => (∑ i, ε ω i • A i) ^ 2) μ := by
  sorry

/-! ### The law-free step -/

/-- **The moment recursion closes.** If `E tr Y^{2q+2} ≤ (2q + 1) E tr (V Y^{2q})` for an almost
surely Hermitian `Y` and a positive semidefinite `V`, then
`E tr Y^{2q+2} ≤ (2q + 1)^{q+1} tr V^{q+1}`. Law-free: the Gaussian and Rademacher series satisfy
the recursion with `V = ∑ A i²`, and any other law with the recursion (exchangeable pairs) gets
the bound. [MackeyEtAl2014, Theorem 7.1] (the absorption step of its proof).
No integrability hypothesis is needed, by a case split: if `tr (V Y^{2q})` is not integrable its
integral is `0`, so `hrec` makes the left side at most `0`; if `tr Y^{2q+2}` is not integrable the
left side is `0`; in both cases the right side is nonnegative
(`Matrix.PosSemidef.re_trace_pow_nonneg`). Otherwise integrate trace Young
(`re_trace_mul_pow_le_add`),
`(q + 1)(2q + 1) tr (V Y^{2q}) ≤ (2q + 1)^{q+1} tr V^{q+1} + q tr Y^{2q+2}`, and combine with
`hrec`. -/
theorem integral_re_trace_pow_le_of_recursion [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {V : Matrix n n 𝕜} (hV : V.PosSemidef) (q : ℕ)
    (hrec : ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (V * Y ω ^ (2 * q)).trace ∂μ) :
    ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace := by
  sorry

/-! ### Gaussian series -/

/-- The polynomial trace moments of a Gaussian matrix series are integrable. Proof: Gaussian
moments of every order (`HasGaussianLaw.memLp`). -/
theorem integrable_re_trace_sum_smul_pow_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, g ω i • A i) ^ r).trace) μ := by
  sorry

/-- **The Gaussian moment recursion**: for a standard Gaussian vector `g` and Hermitian `A i`,
`E tr Y^{2q+2} ≤ (2q + 1) E tr ((∑ A i²) Y^{2q})` with `Y = ∑ g i • A i`.
[MackeyEtAl2014, Theorem 7.1] (there by exchangeable pairs). Proof:
`tr Y^{2q+2} = ∑ i, g i tr (A i Y^{2q+1})`; Stein's identity for derivatives of polynomial growth
(`integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow`)
in each coordinate gives `∑_{l ≤ 2q} E tr (A i Y^l A i Y^{2q-l})`, each term at most
`E tr (A i² Y^{2q})` (`re_trace_mul_pow_mul_pow_le`). -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, g ω i • A i) ^ (2 * q)).trace ∂μ := by
  sorry

/-- **Noncommutative Khintchine inequality**, Gaussian series: for a standard Gaussian vector `g`
and Hermitian `A i`, `E tr (∑ g i • A i)^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p`.
[MackeyEtAl2014, Theorem 7.1]; [Tropp2015, chapter 4]; here over any `RCLike` field and any
finite index types, every `p` (at `p = 0` both sides are `card n`). Buchholz's `(2p - 1)!!` is a
sharper constant of another shape, not stated.
Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace := by
  sorry

/-! ### Rademacher series -/

/-- The polynomial trace moments of a Rademacher matrix series are integrable. Proof: the
coordinates are almost surely bounded. -/
theorem integrable_re_trace_sum_smul_pow_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, ε ω i • A i) ^ r).trace) μ := by
  sorry

/-- **The Rademacher moment recursion**: for a vector `ε` of independent random signs and
Hermitian `A i`, `E tr Y^{2q+2} ≤ (2q + 1) E tr ((∑ A i²) Y^{2q})` with `Y = ∑ ε i • A i`.
[MackeyEtAl2014, Theorem 7.1] (there by exchangeable pairs). Proof: with `Y⁽ⁱ⁾` the series with
the `i`-th sign flipped (same law, `measurePreserving_update_neg_rademacherVector`),
`E [ε i tr (A i Y^{2q+1})] = ¼ E tr ((Y - Y⁽ⁱ⁾)(Y^{2q+1} - Y⁽ⁱ⁾^{2q+1}))`; the mean value trace
inequality (`re_trace_sub_mul_pow_sub_pow_le`) with `Y - Y⁽ⁱ⁾ = 2 ε i • A i` and `ε i² = 1`, and a
second flip. -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, ε ω i • A i) ^ (2 * q)).trace ∂μ := by
  sorry

/-- **Noncommutative Khintchine inequality**, Rademacher series: for a vector `ε` of independent
random signs and Hermitian `A i`, `E tr (∑ ε i • A i)^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p`.
[MackeyEtAl2014, Theorem 7.1]; [Tropp2015, chapter 4]; here over any `RCLike` field and any
finite index types, every `p`.
Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace := by
  sorry

end NLAlib
