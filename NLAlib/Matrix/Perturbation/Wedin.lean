/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Sylvester
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Wedin's theorem for singular subspaces

The analogue of the `sin Θ` theorem for the singular subspaces of a rectangular matrix. The left
and right subspaces are coupled, so the Sylvester equation is replaced by a coupled pair.

The basic statement is in residual form. Let `U`, `V` be frames of left and right singular
vectors of `A` for its `j + 1` largest singular values, and let `(U', V', S)` be any approximate
singular triple with `S` bounded below by `α`. Then
`(α - σ_{j+1}(A)) max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖A V' - U' S‖, ‖Aᴴ U' - V' Sᴴ‖)`.
The perturbation theorem is the case where `(U', V', S)` is exact for `A + E`.

## Main results

* `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_le_max`: the coupled separation bound.
* `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_one_sub_mul_le_max`: Wedin's theorem in residual
  form, every unitarily invariant norm.
* `NLAlib.SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub`: the leading
  singular subspaces of `A` and `A + E`.
* `NLAlib.sq_mul_frobNorm_one_sub_mul_sq_add_le_of_singularValues_sub`: the Frobenius form.
* `NLAlib.max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap`: the bound with the gap of
  the unperturbed matrix only.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### Coupled separation bounds -/

/-- **Coupled separation bound.** If the square matrix `T` is bounded below by `α ≥ 0`
(`α² • 1 ≤ Tᴴ T`) and `‖D‖₂ ≤ β`, then for every pair `X`, `Y`, in every unitarily invariant
norm, `(α - β) max (‖X‖, ‖Y‖) ≤ max (‖D Y - X T‖, ‖Dᴴ X - Y Tᴴ‖)`.
[Wedin1972]; [StewartSun1990, §V.4].
Port of `NLAlib.sub_mul_max_specNorm_le_max_coupled_residual`, there over `ℝ` in the spectral
norm with diagonal `T`. -/
theorem SymmetricGauge.sub_mul_max_matrixNorm_le_max (Φ : SymmetricGauge) {D : Matrix m n 𝕜}
    {T : Matrix p p 𝕜} {α β : ℝ} (hα : 0 ≤ α) (hT : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Tᴴ * T)
    (hD : specNorm D ≤ β) (X : Matrix m p 𝕜) (Y : Matrix n p 𝕜) :
    (α - β) * max (Φ.matrixNorm X) (Φ.matrixNorm Y) ≤
      max (Φ.matrixNorm (D * Y - X * T)) (Φ.matrixNorm (Dᴴ * X - Y * Tᴴ)) := by
  sorry

/-- The coupled separation bound in the Frobenius norm, for the sum of squares:
`(α - β)² (‖X‖_F² + ‖Y‖_F²) ≤ ‖D Y - X T‖_F² + ‖Dᴴ X - Y Tᴴ‖_F²` when `β ≤ α`.
[Wedin1972].
Port of `NLAlib.sub_sq_mul_add_sq_frobNorm_le_add_sq_coupled_residual`. -/
theorem sub_sq_mul_frobNorm_sq_add_frobNorm_sq_le {D : Matrix m n 𝕜} {T : Matrix p p 𝕜}
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : β ≤ α) (hT : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Tᴴ * T)
    (hD : specNorm D ≤ β) (X : Matrix m p 𝕜) (Y : Matrix n p 𝕜) :
    (α - β) ^ 2 * (frobNorm X ^ 2 + frobNorm Y ^ 2) ≤
      frobNorm (D * Y - X * T) ^ 2 + frobNorm (Dᴴ * X - Y * Tᴴ) ^ 2 := by
  sorry

/-! ### The part of a matrix outside its leading singular subspaces -/

/-- If `A * V = U * Σ` and `Aᴴ * U = V * Σ` for frames `U`, `V` and `Σ` the diagonal matrix of
the `j + 1` largest singular values, then the remainder is the compression of `A` to the
complements: `A - U Σ Vᴴ = (1 - U Uᴴ) A (1 - V Vᴴ)`. -/
theorem sub_mul_diagonal_mul_conjTranspose_eq {A : Matrix m n 𝕜} {j : ℕ}
    {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) :
    A - U * (Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) * Vᴴ =
      (1 - U * Uᴴ) * A * (1 - V * Vᴴ) := by
  sorry

/-- **The complement of leading singular frames.** Under the same hypotheses the compression of
`A` to the complements has spectral norm `σ_{j+1}(A)`. This holds with repeated singular
values. -/
theorem specNorm_one_sub_mul_mul_one_sub_of_mul_eq_mul_diagonal {A : Matrix m n 𝕜} {j : ℕ}
    {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) :
    specNorm ((1 - U * Uᴴ) * A * (1 - V * Vᴴ)) = singularValues A (j + 1) := by
  sorry

/-! ### Wedin's theorem -/

/-- **Wedin's `sin Θ` theorem, residual form.** Let `U`, `V` be frames of left and right
singular vectors of `A` for its `j + 1` largest singular values. For any triple `(U', V', S)`
with `S` bounded below by `α ≥ 0`, in every unitarily invariant norm
`(α - σ_{j+1}(A)) max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖A V' - U' S‖, ‖Aᴴ U' - V' Sᴴ‖)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_max_residual_div`, there over `ℝ` in the
spectral norm with square SVD factors.
Result: wedin -/
theorem SymmetricGauge.sub_mul_max_matrixNorm_one_sub_mul_le_max (Φ : SymmetricGauge)
    {A : Matrix m n 𝕜} {j : ℕ} {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    {S : Matrix p p 𝕜} {α : ℝ} (hα : 0 ≤ α) (hS : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Sᴴ * S)
    (U' : Matrix m p 𝕜) (V' : Matrix n p 𝕜) :
    (α - singularValues A (j + 1)) *
        max (Φ.matrixNorm ((1 - U * Uᴴ) * U')) (Φ.matrixNorm ((1 - V * Vᴴ) * V')) ≤
      max (Φ.matrixNorm (A * V' - U' * S)) (Φ.matrixNorm (Aᴴ * U' - V' * Sᴴ)) := by
  sorry

/-- **Wedin's `sin Θ` theorem.** Let `U`, `V` be frames of left and right singular vectors of `A`
for its `j + 1` largest singular values, and `U'`, `V'` the same for `A + E`. If
`δ ≤ σ_j(A + E) - σ_{j+1}(A)`, then in every unitarily invariant norm
`δ max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖E V'‖, ‖Eᴴ U'‖)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_max_perturbation_frame_div`, there over `ℝ`
in the spectral norm with square SVD factors.
Result: wedin -/
theorem SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub
    (Φ : SymmetricGauge) {A E : Matrix m n 𝕜} {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜}
    {V V' : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ : δ ≤ singularValues (A + E) j - singularValues A (j + 1)) :
    δ * max (Φ.matrixNorm ((1 - U * Uᴴ) * U')) (Φ.matrixNorm ((1 - V * Vᴴ) * V')) ≤
      max (Φ.matrixNorm (E * V')) (Φ.matrixNorm (Eᴴ * U')) := by
  sorry

/-- **Wedin's theorem in the Frobenius norm**:
`δ² (‖(1 - U Uᴴ) U'‖_F² + ‖(1 - V Vᴴ) V'‖_F²) ≤ ‖E V'‖_F² + ‖Eᴴ U'‖_F²` for
`0 ≤ δ ≤ σ_j(A + E) - σ_{j+1}(A)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_perturbation_frame_div`.
Result: wedin -/
theorem sq_mul_frobNorm_one_sub_mul_sq_add_le_of_singularValues_sub {A E : Matrix m n 𝕜}
    {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜} {V V' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ singularValues (A + E) j - singularValues A (j + 1)) :
    δ ^ 2 * (frobNorm ((1 - U * Uᴴ) * U') ^ 2 + frobNorm ((1 - V * Vᴴ) * V') ^ 2) ≤
      frobNorm (E * V') ^ 2 + frobNorm (Eᴴ * U') ^ 2 := by
  sorry

/-- **Wedin's theorem with the gap of the unperturbed matrix**, spectral norm:
`max (‖(1 - U Uᴴ) U'‖₂, ‖(1 - V Vᴴ) V'‖₂) ≤ 2 ‖E‖₂ / (σ_j(A) - σ_{j+1}(A))`, for frames with
orthonormal columns on both sides.
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap`.
Result: wedin -/
theorem max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap {A E : Matrix m n 𝕜}
    {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜} {V V' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (hU' : HasOrthonormalCols U')
    (hV' : HasOrthonormalCols V')
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hgap : 0 < singularGap A (j + 1)) :
    max (specNorm ((1 - U * Uᴴ) * U')) (specNorm ((1 - V * Vᴴ) * V')) ≤
      2 * specNorm E / singularGap A (j + 1) := by
  sorry

end NLAlib
