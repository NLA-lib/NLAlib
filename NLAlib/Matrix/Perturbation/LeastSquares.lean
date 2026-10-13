/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Pseudoinverse
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Perturbation of least-squares problems

How the solution and the residual of `min ‖b - A x‖` move when `A` and `b` are perturbed, for `A`
of full column rank. The bounds are stated for least-squares solutions `x` of `(A, b)` and `y` of
`(A + E, b + f)`; under the hypotheses both are unique.

## Main results

* `NLAlib.IsLeastSquaresSolution.norm_sub_le`: the absolute bound for the solutions.
* `NLAlib.IsLeastSquaresSolution.norm_sub_le_of_le`: the relative bound, with the condition
  number.
* `NLAlib.norm_one_sub_rangeProjector_mulVec_sub_le`: the bound for the residuals.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- The least-squares solution of a full-column-rank problem is bounded by the data:
`‖x‖ ≤ ‖A⁺‖₂ ‖b‖`. -/
theorem IsLeastSquaresSolution.norm_le_specNorm_pinv_mul {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {b : m → 𝕜} {x : n → 𝕜}
    (hx : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 x‖ ≤ specNorm (pinv A) * ‖WithLp.toLp 2 b‖ := by
  sorry

/-- **Perturbation of a least-squares solution.** Let `A` have full column rank and
`‖A⁺‖₂ ‖E‖₂ < 1`. If `x` solves the problem `(A, b)` and `y` solves `(A + E, b + f)`, then
`‖y - x‖ ≤ ‖(A + E)⁺‖₂ (‖f‖ + ‖E‖₂ ‖x‖ + ‖A⁺‖₂ ‖E‖₂ ‖b - A x‖)`.
[GolubVanLoan2013, Theorem 5.3.1]; [Wedin1973]; [Higham2002, Theorem 20.1].
Port of `NLAlib.norm_least_squares_sub_le_pinv`, there over `ℝ`.
Result: least-squares-perturbation -/
theorem IsLeastSquaresSolution.norm_sub_le {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1)
    {b f : m → 𝕜} {x y : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hy : IsLeastSquaresSolution (A + E) (b + f) y) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      specNorm (pinv (A + E)) *
        (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖ +
          specNorm (pinv A) * specNorm E * ‖WithLp.toLp 2 (b - A *ᵥ x)‖) := by
  sorry

/-- **Relative perturbation of a least-squares solution.** Let `A` have full column rank,
`‖E‖₂ ≤ ε ‖A‖₂`, `‖f‖ ≤ ε ‖b‖` and `κ(A) ε < 1`. Then
`‖y - x‖ ≤ ‖A⁺‖₂ / (1 - κ ε) · (ε ‖b‖ + ε ‖A‖₂ ‖x‖ + ‖A⁺‖₂ ε ‖A‖₂ ‖b - A x‖)`.
The last term carries `κ²` when the residual is not small.
[GolubVanLoan2013, Theorem 5.3.1].
Port of `NLAlib.norm_least_squares_sub_le_relative_data`, there over `ℝ`.
Result: least-squares-perturbation -/
theorem IsLeastSquaresSolution.norm_sub_le_of_le {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A)
    (hε : conditionNumber A * ε < 1) {b f : m → 𝕜} {x y : n → 𝕜}
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) (hx : IsLeastSquaresSolution A b x)
    (hy : IsLeastSquaresSolution (A + E) (b + f) y) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      specNorm (pinv A) / (1 - conditionNumber A * ε) *
        (ε * ‖WithLp.toLp 2 b‖ + ε * specNorm A * ‖WithLp.toLp 2 x‖ +
          specNorm (pinv A) * ε * specNorm A * ‖WithLp.toLp 2 (b - A *ᵥ x)‖) := by
  sorry

/-- **Perturbation of the least-squares residual.** For matrices `A`, `B` of equal rank, the
residuals `(1 - P_A) b` and `(1 - P_B) (b + f)` differ by at most
`‖A⁺‖₂ ‖B - A‖₂ ‖b‖ + ‖f‖`.
[GolubVanLoan2013, Theorem 5.3.1].
Port of `NLAlib.norm_least_squares_residual_sub_le`, there over `ℝ`. -/
theorem norm_one_sub_rangeProjector_mulVec_sub_le {A B : Matrix m n 𝕜} (h : A.rank = B.rank)
    (b f : m → 𝕜) :
    ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b - (1 - rangeProjector B) *ᵥ (b + f))‖ ≤
      specNorm (pinv A) * specNorm (B - A) * ‖WithLp.toLp 2 b‖ + ‖WithLp.toLp 2 f‖ := by
  sorry

/-- Relative perturbation of the least-squares residual: for `A` of full column rank,
`‖E‖₂ ≤ ε ‖A‖₂`, `‖f‖ ≤ ε ‖b‖` and `κ(A) ε < 1`, the residuals differ by at most
`(1 + κ(A)) ε ‖b‖`.
[GolubVanLoan2013, Theorem 5.3.1].
Port of `NLAlib.norm_least_squares_residual_sub_le_relative_data`, there over `ℝ`. -/
theorem norm_one_sub_rangeProjector_mulVec_sub_le_of_le {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A)
    (hε : conditionNumber A * ε < 1) {b f : m → 𝕜}
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) :
    ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b - (1 - rangeProjector (A + E)) *ᵥ (b + f))‖ ≤
      (1 + conditionNumber A) * ε * ‖WithLp.toLp 2 b‖ := by
  sorry

end NLAlib
