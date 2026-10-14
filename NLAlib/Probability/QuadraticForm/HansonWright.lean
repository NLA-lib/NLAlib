/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square

/-!
# The Hanson–Wright inequality

For a real random vector `X` with independent coordinates, each sub-Gaussian with proxy `c`, and
any real matrix `A`, the quadratic form `Xᵀ A X` concentrates about its mean:

`P(t ≤ |Xᵀ A X - E Xᵀ A X|) ≤ 2 exp (-C min (t² / (c² ‖A‖_F²), t / (c ‖A‖)))`,

with the universal constant `C = NLAlib.hansonWrightConstant`, which the sources leave
unspecified. The diagonal part is Bernstein's inequality for the centred squares; the
off-diagonal part is bounded by decoupling and comparison with a Gaussian chaos.

## Main definitions

* `NLAlib.hansonWrightConstant`.

## Main results

* `NLAlib.measureReal_quadForm_sub_integral_ge_le`,
  `NLAlib.measureReal_quadForm_sub_integral_le_le`: the upper and lower tails.
* `NLAlib.measureReal_abs_quadForm_sub_integral_ge_le`: **the Hanson–Wright inequality**.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Theorem 6.2.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {c : ℝ≥0}

/-- The Hanson–Wright constant: the universal constant in the exponent of the Hanson–Wright
inequality, which the sources ([Vershynin2018], Theorem 6.2.1; Rudelson and Vershynin 2013,
Theorem 1.1) leave unspecified. The value is what the proof here reaches; a larger value is a
better bound. Use only `hansonWrightConstant_pos` and `le_hansonWrightConstant`. -/
noncomputable irreducible_def hansonWrightConstant : ℝ := 1 / (256 * rexp 2)

theorem hansonWrightConstant_pos : 0 < hansonWrightConstant := by
  sorry

/-- An explicit lower bound on `hansonWrightConstant`. -/
theorem le_hansonWrightConstant : 1 / (256 * rexp 2) ≤ hansonWrightConstant := by
  sorry

/-- The upper tail of a quadratic form in independent sub-Gaussian coordinates. -/
theorem measureReal_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) := by
  sorry

/-- The lower tail of a quadratic form in independent sub-Gaussian coordinates. -/
theorem measureReal_quadForm_sub_integral_le_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ ≤ -t} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) := by
  sorry

/-- **The Hanson–Wright inequality** ([Vershynin2018], Theorem 6.2.1). -/
theorem measureReal_abs_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ|} ≤
      2 * rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) := by
  sorry

end NLAlib
