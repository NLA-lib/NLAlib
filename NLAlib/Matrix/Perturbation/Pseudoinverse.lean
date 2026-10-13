/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Pseudoinverse.NormBounds

/-!
# Perturbation of the pseudoinverse

The pseudoinverse is not continuous: the rank can jump. Wedin's decomposition of
`pinv B - pinv A` into three terms gives bounds in terms of `‖pinv A‖₂` and `‖pinv B‖₂`, with the
constant `(1 + √5) / 2` in the spectral norm and `√2` in the Frobenius norm. When the ranks agree
and the perturbation is small, `‖pinv B‖₂` is controlled by `‖pinv A‖₂`, and the bound closes.

## Main results

* `NLAlib.pinv_sub_pinv`: Wedin's decomposition.
* `NLAlib.SymmetricGauge.matrixNorm_pinv_sub_pinv_le`: the bound in every unitarily invariant
  norm.
* `NLAlib.specNorm_pinv_sub_pinv_le_goldenRatio_mul_max`: the spectral norm constant.
* `NLAlib.specNorm_pinv_le_div_of_rank_eq`: control of `‖pinv B‖₂` for equal ranks.
* `NLAlib.specNorm_rangeProjector_sub_rangeProjector_le`: perturbation of the range projector.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Wedin's decomposition -/

/-- **Wedin's decomposition** of the difference of two pseudoinverses:
`B⁺ - A⁺ = -B⁺ (B - A) A⁺ + B⁺ B⁺ᴴ (B - A)ᴴ (1 - A A⁺) + (1 - B⁺ B) (B - A)ᴴ A⁺ᴴ A⁺`.
[Wedin1973, Theorem 4.1]; [StewartSun1990, Theorem III.3.10].
Port of `NLAlib.moorePenroseInverse_sub_eq`, there over `ℝ`.
Result: pseudoinverse-perturbation -/
theorem pinv_sub_pinv (A B : Matrix m n 𝕜) :
    pinv B - pinv A =
      -(pinv B * (B - A) * pinv A) + pinv B * (pinv B)ᴴ * (B - A)ᴴ * (1 - A * pinv A) +
        (1 - pinv B * B) * (B - A)ᴴ * (pinv A)ᴴ * pinv A := by
  sorry

/-- **Perturbation of the pseudoinverse in every unitarily invariant norm**:
`‖B⁺ - A⁺‖ ≤ (‖B⁺‖₂ ‖A⁺‖₂ + ‖B⁺‖₂² + ‖A⁺‖₂²) ‖B - A‖`.
[Wedin1973]; [StewartSun1990, Theorem III.3.8].
Port of `NLAlib.specNorm_moorePenroseInverse_add_sub_le`, there over `ℝ` in the spectral norm.
Result: pseudoinverse-perturbation -/
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      (specNorm (pinv B) * specNorm (pinv A) + specNorm (pinv B) ^ 2 + specNorm (pinv A) ^ 2) *
        Φ.matrixNorm (B - A) := by
  sorry

/-- `‖B⁺ - A⁺‖ ≤ 3 max (‖A⁺‖₂², ‖B⁺‖₂²) ‖B - A‖` in every unitarily invariant norm.
Port of `NLAlib.specNorm_moorePenroseInverse_add_sub_le_three_mul_max`. -/
theorem SymmetricGauge.matrixNorm_pinv_sub_pinv_le_three_mul_max (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (pinv B - pinv A) ≤
      3 * max (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2) * Φ.matrixNorm (B - A) := by
  sorry

/-- **Wedin's bound in the spectral norm**, with the golden ratio:
`‖B⁺ - A⁺‖₂ ≤ (1 + √5)/2 · max (‖A⁺‖₂², ‖B⁺‖₂²) ‖B - A‖₂`.
[Wedin1973, Theorem 4.1]; [StewartSun1990, Theorem III.3.8].
Port of `NLAlib.specNorm_moorePenroseInverse_sub_le_goldenRatio_max_sq`, there over `ℝ`.
Result: pseudoinverse-perturbation -/
theorem specNorm_pinv_sub_pinv_le_goldenRatio_mul_max (A B : Matrix m n 𝕜) :
    specNorm (pinv B - pinv A) ≤
      Real.goldenRatio * max (specNorm (pinv A) ^ 2) (specNorm (pinv B) ^ 2) *
        specNorm (B - A) := by
  sorry

/-- A matrix with three blocks of norm at most `d` and a vanishing fourth block, relative to two
orthogonal projectors, has spectral norm at most `(1 + √5)/2 · d`.
Port of `NLAlib.specNorm_le_goldenRatio_mul_of_zero_complement_block`. -/
theorem specNorm_le_goldenRatio_mul_of_one_sub_mul_mul_one_sub_eq_zero {Z : Matrix m n 𝕜}
    {P : Matrix n n 𝕜} {Q : Matrix m m 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {d : ℝ} (h00 : (1 - Q) * Z * (1 - P) = 0) (h11 : specNorm (Q * Z * P) ≤ d)
    (h12 : specNorm (Q * Z * (1 - P)) ≤ d) (h21 : specNorm ((1 - Q) * Z * P) ≤ d) :
    specNorm Z ≤ Real.goldenRatio * d := by
  sorry

/-! ### Equal ranks -/

/-- For matrices of equal rank, `‖B⁺ - A⁺‖₂ ≤ (1 + √5)/2 · ‖A⁺‖₂ ‖B⁺‖₂ ‖B - A‖₂`.
[Wedin1973]; [StewartSun1990, Theorem III.3.9].
Port of `NLAlib.specNorm_moorePenroseInverse_sub_le_goldenRatio_mul_of_rank_eq`. -/
theorem specNorm_pinv_sub_pinv_le_goldenRatio_mul_of_rank_eq {A B : Matrix m n 𝕜}
    (h : A.rank = B.rank) :
    specNorm (pinv B - pinv A) ≤
      Real.goldenRatio * specNorm (pinv A) * specNorm (pinv B) * specNorm (B - A) := by
  sorry

/-- For matrices of equal rank, `‖B⁺ - A⁺‖_F ≤ √2 ‖A⁺‖₂ ‖B⁺‖₂ ‖B - A‖_F`.
[Wedin1973]; [StewartSun1990, Theorem III.3.9].
Port of `NLAlib.frobNorm_moorePenroseInverse_sub_le_sqrt_two_mul_of_rank_eq`. -/
theorem frobNorm_pinv_sub_pinv_le_sqrt_two_mul_of_rank_eq {A B : Matrix m n 𝕜}
    (h : A.rank = B.rank) :
    frobNorm (pinv B - pinv A) ≤ √2 * specNorm (pinv A) * specNorm (pinv B) * frobNorm (B - A) := by
  sorry

/-- **Control of the perturbed pseudoinverse.** For matrices of equal rank with
`‖A⁺‖₂ ‖B - A‖₂ < 1`, `‖B⁺‖₂ ≤ ‖A⁺‖₂ / (1 - ‖A⁺‖₂ ‖B - A‖₂)`.
[Wedin1973]; [StewartSun1990, Theorem III.3.8].
Port of `NLAlib.specNorm_moorePenroseInverse_le_div_of_rank_eq`. -/
theorem specNorm_pinv_le_div_of_rank_eq {A B : Matrix m n 𝕜} (h : A.rank = B.rank)
    (hsmall : specNorm (pinv A) * specNorm (B - A) < 1) :
    specNorm (pinv B) ≤ specNorm (pinv A) / (1 - specNorm (pinv A) * specNorm (B - A)) := by
  sorry

/-- A small perturbation of a matrix of full column rank has full column rank.
Port of `NLAlib.rank_add_eq_card_of_pinv_mul_specNorm_lt_one`. -/
theorem injective_mulVec_add_of_specNorm_pinv_mul_lt_one {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1) :
    Function.Injective (A + E).mulVec := by
  sorry

/-- For `A` of full column rank and `‖A⁺‖₂ ‖E‖₂ < 1`,
`‖(A + E)⁺‖₂ ≤ ‖A⁺‖₂ / (1 - ‖A⁺‖₂ ‖E‖₂)`.
Port of `NLAlib.specNorm_pinv_add_le_of_rank_eq_card`. -/
theorem specNorm_pinv_add_le_of_injective {A E : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hE : specNorm (pinv A) * specNorm E < 1) :
    specNorm (pinv (A + E)) ≤ specNorm (pinv A) / (1 - specNorm (pinv A) * specNorm E) := by
  sorry

/-! ### The range projector -/

/-- The part of the range of `A` outside the range of `B` is controlled by `B - A`, in every
unitarily invariant norm: `‖(1 - P_B) P_A‖ ≤ ‖A⁺‖₂ ‖(1 - P_B) (A - B)‖`.
Port of `NLAlib.complement_columnProjector_mul_columnProjector_eq`. -/
theorem SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_rangeProjector_le
    (Φ : SymmetricGauge) (A B : Matrix m n 𝕜) :
    Φ.matrixNorm ((1 - rangeProjector B) * rangeProjector A) ≤
      specNorm (pinv A) * Φ.matrixNorm ((1 - rangeProjector B) * (A - B)) := by
  sorry

/-- **Perturbation of the range projector.** For matrices of equal rank,
`‖P_A - P_B‖₂ ≤ min (‖A⁺‖₂, ‖B⁺‖₂) ‖B - A‖₂`.
[StewartSun1990, §III.3]; [Wedin1973].
Port of `NLAlib.specNorm_sub_columnProjector_le_min_pinv_mul_specNorm`. -/
theorem specNorm_rangeProjector_sub_rangeProjector_le {A B : Matrix m n 𝕜} (h : A.rank = B.rank) :
    specNorm (rangeProjector A - rangeProjector B) ≤
      min (specNorm (pinv A)) (specNorm (pinv B)) * specNorm (B - A) := by
  sorry

end NLAlib
