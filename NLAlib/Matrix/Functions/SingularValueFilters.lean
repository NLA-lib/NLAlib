/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Polynomial

/-!
# Polynomial filters on fixed singular directions

Polar updates can change the signs and ordering of their diagonal coefficients.

## Main results

* `NLAlib.HasOrthonormalCols.mul_aeval_conjTranspose_mul_self`: signed polynomial filtering.
* `NLAlib.HasOrthonormalCols.specNorm_sub_mul_diagonal_mul_conjTranspose`: exact error.

-/

@[expose] public section

open Matrix Polynomial
open scoped Matrix
namespace NLAlib.HasOrthonormalCols

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
variable {U : Matrix m r 𝕜} {V : Matrix n r 𝕜}

/-- The norm of a real diagonal between two orthonormal frames is the supremum of the
absolute diagonal entries, including negative entries and the empty diagonal. -/
theorem specNorm_mul_diagonal_mul_conjTranspose (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (f : r → ℝ) :
    specNorm (U * diagonal (fun i => (f i : 𝕜)) * Vᴴ) = ‖f‖ := by
  rw [hV.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left, specNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [RCLike.norm_ofReal]
    exact norm_le_pi_norm f i
  · rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜)]
    exact norm_le_pi_norm (fun i => (f i : 𝕜)) i

/-- Changing the diagonal coefficients of fixed singular frames has spectral-norm error
equal to the largest absolute coefficient difference. -/
theorem specNorm_sub_mul_diagonal_mul_conjTranspose (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (f g : r → ℝ) :
    specNorm (U * diagonal (fun i => (f i : 𝕜)) * Vᴴ -
      U * diagonal (fun i => (g i : 𝕜)) * Vᴴ) = ‖f - g‖ := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  simp only [← RCLike.ofReal_sub]
  exact hU.specNorm_mul_diagonal_mul_conjTranspose hV _

/-- A Gram-polynomial update multiplies each signed frame coefficient by the polynomial
evaluated at its square. Signed coefficients allow repeated updates with no ordering or
positivity assumptions on intermediate values. -/
theorem mul_aeval_conjTranspose_mul_self [DecidableEq n] (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (f : r → ℝ) (p : ℝ[X]) :
    let A := U * diagonal (fun i => (f i : 𝕜)) * Vᴴ
    A * Polynomial.aeval (Aᴴ * A) p =
      U * diagonal (fun i => ((f i * p.eval (f i ^ 2) : ℝ) : 𝕜)) * Vᴴ := by
  intro A
  have hgram : Aᴴ * A = V * diagonal (fun i => ((f i ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
    dsimp [A]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_diagonal_ofReal,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal]
    simp only [sq, RCLike.ofReal_mul]
  have hint : diagonal (fun i => ((f i ^ 2 : ℝ) : 𝕜)) * Vᴴ = Vᴴ * (Aᴴ * A) := by
    rw [hgram, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  have hp := aeval_mul_eq_mul_aeval_of_mul_eq_mul hint p
  change U * diagonal (fun i => (f i : 𝕜)) * Vᴴ * _ = _
  rw [Matrix.mul_assoc _ Vᴴ, ← hp, aeval_diagonal, ← Matrix.mul_assoc,
    Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
  simp only [RCLike.ofReal_mul]


end NLAlib.HasOrthonormalCols
