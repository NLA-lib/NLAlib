/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.PrincipalAngles

/-!
# Oblique projections

An idempotent matrix `P` projects onto its range along its kernel. It is an orthogonal projector
exactly when its spectral norm is at most one; otherwise its norm is the secant of the largest
principal angle between its range and the orthogonal complement of its kernel, and `P` and
`1 - P` have the same norm. The oblique projector onto the column space of `X` along the
orthogonal complement of the column space of `Y` is `X * (Yᴴ * X)⁻¹ * Yᴴ`.

## Main results

* `IsIdempotentElem.trace_eq_rank`: the trace of an idempotent matrix is its rank.
* `IsIdempotentElem.one_le_specNorm`, `IsIdempotentElem.isStarProjection_iff_specNorm_le_one`.
* `IsIdempotentElem.specNorm_one_sub`: `‖1 - P‖₂ = ‖P‖₂` for a nontrivial idempotent.
* `IsIdempotentElem.specNorm_mul_cos_principalAngle`: the secant formula.
* `NLAlib.HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose`: the norm of an oblique
  projector given by two frames.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n]
  [DecidableEq p]

/-! ### Idempotent matrices -/

/-- The trace of an idempotent matrix is its rank.
[HornJohnson2013, §3.1.P25 context]. Port of `NLAlib.trace_eq_rank_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.trace_eq_rank {K : Type*} [Field K] {P : Matrix n n K}
    (hP : IsIdempotentElem P) : P.trace = P.rank := by
  sorry

/-- An idempotent matrix fixes the column space of any matrix inside its range.
Port of `NLAlib.mul_eq_of_range_le_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.mul_eq_of_range_le {K : Type*} [Field K] {P : Matrix n n K}
    (hP : IsIdempotentElem P) {X : Matrix n p K}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range P.mulVecLin) : P * X = X := by
  sorry

/-- A nonzero idempotent has spectral norm at least one.
Port of `NLAlib.one_le_specNorm_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.one_le_specNorm {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h : P ≠ 0) : 1 ≤ specNorm P := by
  sorry

/-- **An idempotent is an orthogonal projector exactly when it is a contraction.**
[HornJohnson2013, §3.1.P25 context]; [Kato1995, §I.6.7]. -/
theorem _root_.IsIdempotentElem.isStarProjection_iff_specNorm_le_one {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) : IsStarProjection P ↔ specNorm P ≤ 1 := by
  sorry

/-- **An idempotent and its complement have the same norm**, when neither is zero.
[Kato1995, §I.6.7]; [Szyld2006]; [HornJohnson2013, Corollary 3.4.3.3].
Port of `NLAlib.specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt`, there over `ℝ`.
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_one_sub {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) (h1 : P ≠ 1) : specNorm (1 - P) = specNorm P := by
  sorry

/-- **The secant formula.** The spectral norm of a nonzero idempotent `P` is the secant of the
largest principal angle between its range and the range of `Pᴴ` (the orthogonal complement of its
kernel): `‖P‖₂ cos θ = 1`, and `θ < π / 2`.
[HornJohnson2013, Corollary 3.4.3.3]; [Szyld2006].
Port of `NLAlib.specNorm_idempotent_eq_secant_of_range_frames`, there over `ℝ` with frames.
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_mul_cos_principalAngle {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    specNorm P * Real.cos (principalAngle P Pᴴ j) = 1 := by
  sorry

/-- The largest principal angle between the range of a nonzero idempotent and the complement of
its kernel is acute. -/
theorem _root_.IsIdempotentElem.principalAngle_conjTranspose_lt {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    principalAngle P Pᴴ j < Real.pi / 2 := by
  sorry

/-! ### The oblique projector of two bases -/

/-- `X * (Yᴴ * X)⁻¹ * Yᴴ` is idempotent when `Yᴴ * X` is invertible: it is the projector onto the
column space of `X` along the orthogonal complement of the column space of `Y`. -/
theorem isIdempotentElem_mul_inv_mul_conjTranspose {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    IsIdempotentElem (X * (Yᴴ * X)⁻¹ * Yᴴ) := by
  sorry

/-- The oblique projector `X * (Yᴴ * X)⁻¹ * Yᴴ` fixes `X`. -/
theorem mul_inv_mul_conjTranspose_mul_self {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    X * (Yᴴ * X)⁻¹ * Yᴴ * X = X := by
  sorry

/-- The oblique projector `X * (Yᴴ * X)⁻¹ * Yᴴ` annihilates the orthogonal complement of the
column space of `Y`. -/
theorem mul_inv_mul_conjTranspose_mulVec_eq_zero (X Y : Matrix n p 𝕜) {v : n → 𝕜}
    (hv : Yᴴ *ᵥ v = 0) : (X * (Yᴴ * X)⁻¹ * Yᴴ) *ᵥ v = 0 := by
  sorry

/-- **The norm of an oblique projector between two frames**: for `U`, `V` with orthonormal
columns and `Vᴴ * U` invertible, `‖U (Vᴴ U)⁻¹ Vᴴ‖₂ = ‖(Vᴴ U)⁻¹‖₂`, the reciprocal of the smallest
singular value of `Vᴴ * U`, that is, the secant of the largest principal angle.
[Szyld2006]. -/
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) = specNorm (Vᴴ * U)⁻¹ := by
  sorry

/-- The norm of an oblique projector between two frames, through the principal angle. -/
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose_mul_cos {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (h : IsUnit (Vᴴ * U)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) * Real.cos (principalAngle U V j) = 1 := by
  sorry

end NLAlib
