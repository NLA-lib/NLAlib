/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Norms.Net
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Probability.Isotropic
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic

/-!
# Extreme singular values of matrices with independent sub-Gaussian rows

For a random matrix `X : m × n` (`N = card m` rows, `n = card n` columns) whose rows are
independent, isotropic and sub-Gaussian with proxy `c`, and `w = C c (√n + t)` with
`C = subgaussianRowsConstant`: outside probability `2 e^{-t²}`,
`(√N - w)² • 1 ≤ Xᴴ X ≤ (√N + w)² • 1`, hence `√N - w < σ_min(X)` and `‖X‖ < √N + w`. Also the
fixed-vector bound: for a unit `x`, `‖X x‖² - N` is sub-exponential with parameters `32 c² N`,
`4 c`.

**Naming.** The suffix `_of_isSubgaussianVector` stands for the three row hypotheses, always taken
together and in this order: `hind : iIndepFun (fun i ω => X ω i) μ` (independent rows),
`hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ` and
`hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ`. No `1 ≤ c` hypothesis is stated: with rows and
columns present, isotropy and `HasSubgaussianMGF.integral_sq_le` give it.

A standard Gaussian matrix satisfies the hypotheses with `c = 1`, but there the bounds of
`NLAlib/RandomMatrix/Gaussian/ExtremeSingularValues.lean` are better in every regime
(`√N ± (√n + √2 t)` outside `2 e^{-t²}`).

## Main definitions

* `NLAlib.subgaussianRowsConstant`: the constant `C` of the bounds.

## Main results

* `NLAlib.hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector`: the fixed-vector bound.
* The two-sided Gram bound (in namespace `NLAlib`):
  `measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector`.
* Its one-sided forms and the singular-value tails
  `NLAlib.measureReal_singularValues_le_le_of_isSubgaussianVector`,
  `NLAlib.measureReal_specNorm_ge_le_of_isSubgaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal

namespace NLAlib

/-- The constant `C` of the sub-Gaussian rows theorem: `√N ± C c (√n + t)` outside `2 e^{-t²}`.
[Vershynin2018, Theorem 4.6.1] leaves it unspecified (`C K²` there). The value proved is `24`:
the net argument needs `C² / 256 ≥ max 1 (log 9)`, that is `C ≥ 16 √(log 9) ≈ 23.72`, so the margin
is thin and the proof uses `(√n + t)² ≥ n + t²` and a `1/4`-net exactly. Smaller is better; the
API is the upper bound `subgaussianRowsConstant_le`. -/
noncomputable irreducible_def subgaussianRowsConstant : ℝ := 24

/-- The sub-Gaussian rows constant is positive. -/
theorem subgaussianRowsConstant_pos : 0 < subgaussianRowsConstant := by
  sorry

/-- An explicit upper bound on `subgaussianRowsConstant`. -/
theorem subgaussianRowsConstant_le : subgaussianRowsConstant ≤ 24 := by
  sorry

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] [DecidableEq n] {X : Ω → Matrix m n ℝ} {c : ℝ≥0}

/-- **The fixed-vector bound**: for independent isotropic sub-Gaussian rows with proxy `c` and a
unit vector `x`, `‖X x‖² - N` is sub-exponential with parameters `32 c² N` and `4 c`: each
`⟨Xᵢ, x⟩² - 1` is sub-exponential with parameters `32 c²`, `4 c`
(`HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`), and the rows are independent.
[Vershynin2018, proof of Theorem 4.6.1], with the constants of the squared sub-Gaussian. -/
theorem hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasSubexponentialMGF (fun ω => ‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - Fintype.card m)
      (32 * c ^ 2 * Fintype.card m) (4 * c) μ := by
  sorry

/-- **Independent isotropic sub-Gaussian rows**, the Gram sandwich: with
`w = subgaussianRowsConstant * c * (√n + t)` and `0 ≤ t`, `w ≤ √N`,
`(√N - w)² • 1 ≤ Xᴴ X ≤ (√N + w)² • 1` outside probability `2 e^{-t²}`.
[Vershynin2018, Theorem 4.6.1], there for the singular values with an unspecified constant
`C K²`; here in Loewner form with the named constant `subgaussianRowsConstant`. For a standard
Gaussian matrix the Gram sandwich of `NLAlib/RandomMatrix/Gaussian/ExtremeSingularValues.lean`
is better in every regime.
Result: subgaussian-matrix-norm -/
theorem
measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t)
    (hw : subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ √(Fintype.card m : ℝ)) :
    μ.real {ω | ¬ ((√(Fintype.card m : ℝ) -
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ) ≤
      (X ω)ᴴ * X ω ∧ (X ω)ᴴ * X ω ≤ (√(Fintype.card m : ℝ) +
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ))} ≤
      2 * Real.exp (-t ^ 2) := by
  sorry

/-- The lower Gram bound for independent isotropic sub-Gaussian rows: `(√N - w)² • 1 ≤ Xᴴ X`
outside probability `2 e^{-t²}`, with `w = subgaussianRowsConstant * c * (√n + t)`, `0 ≤ t` and
`w ≤ √N` (the base must be nonnegative). [Vershynin2018, Theorem 4.6.1], in Loewner form. For a
standard Gaussian matrix
`NLAlib.measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix` is better
in every regime. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t)
    (hw : subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ √(Fintype.card m : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) -
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ) ≤
      (X ω)ᴴ * X ω} ≤ 2 * Real.exp (-t ^ 2) := by
  sorry

/-- The upper Gram bound for independent isotropic sub-Gaussian rows: `Xᴴ X ≤ (√N + w)² • 1`
outside probability `2 e^{-t²}`, with `w = subgaussianRowsConstant * c * (√n + t)` and `0 ≤ t`.
[Vershynin2018, Theorem 4.6.1], in Loewner form. For a standard Gaussian matrix
`NLAlib.measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix` is better
in every regime. -/
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤ (√(Fintype.card m : ℝ) +
      subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ)} ≤
      2 * Real.exp (-t ^ 2) := by
  sorry

/-- The lower tail of the smallest singular value for independent isotropic sub-Gaussian rows:
`P(σ_min(X) ≤ √N - w) ≤ 2 e^{-t²}`, with `w = subgaussianRowsConstant * c * (√n + t)` and
`0 ≤ t`; `σ_min` is the singular value of index `k` with `k + 1 = n`. The rows must exist
(`[Nonempty m]`): with no rows the hypotheses leave `c` free, and for `c = 0` the event is
everything. [Vershynin2018, Theorem 4.6.1]. For a standard Gaussian matrix
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix` is better in every regime. -/
theorem measureReal_singularValues_le_le_of_isSubgaussianVector [Nonempty m]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤
      √(Fintype.card m : ℝ) - subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)} ≤
      2 * Real.exp (-t ^ 2) := by
  sorry

/-- The upper tail of the spectral norm for independent isotropic sub-Gaussian rows:
`P(√N + w ≤ ‖X‖) ≤ 2 e^{-t²}`, with `w = subgaussianRowsConstant * c * (√n + t)` and `0 ≤ t`.
The rows must exist (`[Nonempty m]`), as in
`NLAlib.measureReal_singularValues_le_le_of_isSubgaussianVector`. [Vershynin2018, Theorem 4.6.1].
For a standard Gaussian matrix `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` is
better in every regime. -/
theorem measureReal_specNorm_ge_le_of_isSubgaussianVector [Nonempty m]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(Fintype.card m : ℝ) +
      subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ specNorm (X ω)} ≤
      2 * Real.exp (-t ^ 2) := by
  sorry

end NLAlib
