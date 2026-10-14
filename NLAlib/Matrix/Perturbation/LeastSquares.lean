/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
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

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The least-squares solution of a full-column-rank problem is bounded by the data:
`‖x‖ ≤ ‖A⁺‖₂ ‖b‖`. -/
theorem IsLeastSquaresSolution.norm_le_specNorm_pinv_mul {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {b : m → 𝕜} {x : n → 𝕜}
    (hx : IsLeastSquaresSolution A b x) :
    ‖WithLp.toLp 2 x‖ ≤ specNorm (pinv A) * ‖WithLp.toLp 2 b‖ := by
  rw [(isLeastSquaresSolution_iff_eq_pinv_mulVec hA).mp hx]
  exact norm_toLp_mulVec_le (pinv A) b

/-- The pseudoinverse of `B` on a residual of `A`, for matrices of equal rank: the residual is
orthogonal to the range of `A`, so only the difference of the range projectors acts. -/
private theorem norm_pinv_mulVec_one_sub_rangeProjector_mulVec_le [DecidableEq m]
    {A B : Matrix m n 𝕜} (h : A.rank = B.rank) (b : m → 𝕜) :
    ‖WithLp.toLp 2 (pinv B *ᵥ ((1 - rangeProjector A) *ᵥ b))‖ ≤
      specNorm (pinv B) * (specNorm (pinv A) * specNorm (B - A) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖) := by
  have hmat : pinv B * (1 - rangeProjector A) =
      pinv B * ((rangeProjector B - rangeProjector A) * (1 - rangeProjector A)) := by
    have h1 : pinv B * rangeProjector B = pinv B := by
      rw [← mul_pinv, ← Matrix.mul_assoc, pinv_mul_mul_pinv]
    have h2 : rangeProjector A * (1 - rangeProjector A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one,
        (isStarProjection_rangeProjector A).isIdempotentElem.eq, sub_self]
    rw [Matrix.sub_mul, h2, sub_zero, ← Matrix.mul_assoc, h1]
  have hvec : pinv B *ᵥ ((1 - rangeProjector A) *ᵥ b) =
      pinv B *ᵥ ((rangeProjector B - rangeProjector A) *ᵥ ((1 - rangeProjector A) *ᵥ b)) := by
    have h3 := congrArg (· *ᵥ b) hmat
    simpa only [← Matrix.mulVec_mulVec] using h3
  rw [hvec]
  refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg _))
  refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [specNorm_sub_comm]
  exact (specNorm_rangeProjector_sub_rangeProjector_le h).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (specNorm_nonneg _))

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
  classical
  have hB := injective_mulVec_add_of_specNorm_pinv_mul_lt_one hA hE
  have hrank : A.rank = (A + E).rank := by
    rw [mulVec_injective_iff_rank_eq.mp hA, mulVec_injective_iff_rank_eq.mp hB]
  have hy' := (isLeastSquaresSolution_iff_eq_pinv_mulVec hB).mp hy
  have hsum : b + f = (A + E) *ᵥ x + (f - E *ᵥ x) + (b - A *ᵥ x) := by
    rw [Matrix.add_mulVec]
    abel
  have he : y - x = pinv (A + E) *ᵥ (f - E *ᵥ x) + pinv (A + E) *ᵥ (b - A *ᵥ x) := by
    rw [hy', hsum, Matrix.mulVec_add, Matrix.mulVec_add, pinv_mulVec_mulVec_of_injective hB]
    abel
  have h1 : ‖WithLp.toLp 2 (pinv (A + E) *ᵥ (f - E *ᵥ x))‖ ≤
      specNorm (pinv (A + E)) * (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) := by
    refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg _))
    rw [WithLp.toLp_sub]
    exact (_root_.norm_sub_le _ _).trans (add_le_add le_rfl (norm_toLp_mulVec_le E x))
  have h2 := norm_pinv_mulVec_one_sub_rangeProjector_mulVec_le hrank b
  rw [← hx.sub_mulVec_eq, add_sub_cancel_left] at h2
  rw [he, WithLp.toLp_add]
  calc ‖WithLp.toLp 2 (pinv (A + E) *ᵥ (f - E *ᵥ x)) +
        WithLp.toLp 2 (pinv (A + E) *ᵥ (b - A *ᵥ x))‖
      ≤ specNorm (pinv (A + E)) * (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) +
        specNorm (pinv (A + E)) *
          (specNorm (pinv A) * specNorm E * ‖WithLp.toLp 2 (b - A *ᵥ x)‖) :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

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
  have hκ : specNorm (pinv A) * specNorm E ≤ conditionNumber A * ε := by
    calc specNorm (pinv A) * specNorm E
        ≤ specNorm (pinv A) * (ε * specNorm A) :=
          mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
      _ = conditionNumber A * ε := by rw [conditionNumber_def]; ring
  have hp := hκ.trans_lt hε
  have hpinv : specNorm (pinv (A + E)) ≤ specNorm (pinv A) / (1 - conditionNumber A * ε) :=
    (specNorm_pinv_add_le_of_injective hA hp).trans
      (div_le_div_of_nonneg_left (specNorm_nonneg _) (sub_pos.mpr hε) (sub_le_sub_left hκ 1))
  have ht : ‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖ +
        specNorm (pinv A) * specNorm E * ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤
      ε * ‖WithLp.toLp 2 b‖ + ε * specNorm A * ‖WithLp.toLp 2 x‖ +
        specNorm (pinv A) * ε * specNorm A * ‖WithLp.toLp 2 (b - A *ᵥ x)‖ := by
    have h1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (WithLp.toLp 2 x))
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hE (specNorm_nonneg (pinv A)))
      (norm_nonneg (WithLp.toLp 2 (b - A *ᵥ x)))
    rw [← mul_assoc] at h2
    exact add_le_add (add_le_add hf h1) h2
  refine (hx.norm_sub_le hA hp hy).trans (mul_le_mul hpinv ht ?_
    (div_nonneg (specNorm_nonneg _) (sub_pos.mpr hε).le))
  exact add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (specNorm_nonneg E) (norm_nonneg _)))
    (mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg E)) (norm_nonneg _))

/-- **Perturbation of the least-squares residual.** For matrices `A`, `B` of equal rank, the
residuals `(1 - P_A) b` and `(1 - P_B) (b + f)` differ by at most
`‖A⁺‖₂ ‖B - A‖₂ ‖b‖ + ‖f‖`.
[GolubVanLoan2013, Theorem 5.3.1].
Port of `NLAlib.norm_least_squares_residual_sub_le`, there over `ℝ`. -/
theorem norm_one_sub_rangeProjector_mulVec_sub_le [DecidableEq m] {A B : Matrix m n 𝕜}
    (h : A.rank = B.rank) (b f : m → 𝕜) :
    ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b - (1 - rangeProjector B) *ᵥ (b + f))‖ ≤
      specNorm (pinv A) * specNorm (B - A) * ‖WithLp.toLp 2 b‖ + ‖WithLp.toLp 2 f‖ := by
  have he : (1 - rangeProjector A) *ᵥ b - (1 - rangeProjector B) *ᵥ (b + f) =
      (rangeProjector B - rangeProjector A) *ᵥ b - (1 - rangeProjector B) *ᵥ f := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add]
    abel
  rw [he, WithLp.toLp_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_
    ((isStarProjection_one_sub_rangeProjector B).norm_toLp_mulVec_le f))
  refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [specNorm_sub_comm]
  exact (specNorm_rangeProjector_sub_rangeProjector_le h).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (specNorm_nonneg _))

/-- Relative perturbation of the least-squares residual: for `A` of full column rank,
`‖E‖₂ ≤ ε ‖A‖₂`, `‖f‖ ≤ ε ‖b‖` and `κ(A) ε < 1`, the residuals differ by at most
`(1 + κ(A)) ε ‖b‖`.
[GolubVanLoan2013, Theorem 5.3.1].
Port of `NLAlib.norm_least_squares_residual_sub_le_relative_data`, there over `ℝ`. -/
theorem norm_one_sub_rangeProjector_mulVec_sub_le_of_le [DecidableEq m] {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A)
    (hε : conditionNumber A * ε < 1) {b f : m → 𝕜}
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) :
    ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b - (1 - rangeProjector (A + E)) *ᵥ (b + f))‖ ≤
      (1 + conditionNumber A) * ε * ‖WithLp.toLp 2 b‖ := by
  have hκ : specNorm (pinv A) * specNorm E ≤ conditionNumber A * ε := by
    calc specNorm (pinv A) * specNorm E
        ≤ specNorm (pinv A) * (ε * specNorm A) :=
          mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
      _ = conditionNumber A * ε := by rw [conditionNumber_def]; ring
  have hB := injective_mulVec_add_of_specNorm_pinv_mul_lt_one hA (hκ.trans_lt hε)
  have hrank : A.rank = (A + E).rank := by
    rw [mulVec_injective_iff_rank_eq.mp hA, mulVec_injective_iff_rank_eq.mp hB]
  have h := norm_one_sub_rangeProjector_mulVec_sub_le hrank b f
  rw [add_sub_cancel_left] at h
  have h1 := mul_le_mul_of_nonneg_right hκ (norm_nonneg (WithLp.toLp 2 b))
  refine h.trans ?_
  calc specNorm (pinv A) * specNorm E * ‖WithLp.toLp 2 b‖ + ‖WithLp.toLp 2 f‖
      ≤ conditionNumber A * ε * ‖WithLp.toLp 2 b‖ + ε * ‖WithLp.toLp 2 b‖ := add_le_add h1 hf
    _ = _ := by ring

end NLAlib
