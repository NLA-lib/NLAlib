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

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [Fintype p]

/-! ### Idempotent matrices -/

/-- The trace of an idempotent matrix is its rank.
[HornJohnson2013, §3.1.P25 context]. Port of `NLAlib.trace_eq_rank_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.trace_eq_rank {K : Type*} [Field K] {P : Matrix n n K}
    (hP : IsIdempotentElem P) : P.trace = P.rank := by
  classical
  have hf : IsIdempotentElem P.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hP.eq]
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply']
  exact ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hf).trace

/-- An idempotent matrix fixes the column space of any matrix inside its range.
Port of `NLAlib.mul_eq_of_range_le_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.mul_eq_of_range_le {K : Type*} [Field K] {P : Matrix n n K}
    (hP : IsIdempotentElem P) {X : Matrix n p K}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range P.mulVecLin) : P * X = X := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := h (show X *ᵥ x ∈ LinearMap.range X.mulVecLin from ⟨x, rfl⟩)
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP.eq]

/-- For a nonzero orthogonal projector `R` and `M` with columns in the range of `R`,
`‖R + M Mᴴ‖₂ = 1 + ‖M‖₂²`. -/
private theorem specNorm_add_mul_conjTranspose_self {R : Matrix n n 𝕜} (hR : IsStarProjection R)
    (h0 : R ≠ 0) {M : Matrix n p 𝕜} (hM : R * M = M) :
    specNorm (R + M * Mᴴ) = 1 + specNorm M ^ 2 := by
  classical
  have hn : 0 < Fintype.card n := by
    rw [Fintype.card_pos_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (Subsingleton.elim _ _)
  have hG : specNorm (M * Mᴴ + (1 : ℝ) • (1 : Matrix n n 𝕜)) = specNorm M ^ 2 + 1 := by
    have hps : (M * Mᴴ + (1 : ℝ) • (1 : Matrix n n 𝕜)).PosSemidef := by
      rw [one_smul]
      exact (Matrix.posSemidef_self_mul_conjTranspose M).add Matrix.PosSemidef.one
    rw [← singularValues_zero_eq_specNorm, hps.singularValues_eq_eigenvalue,
      (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalue_add_smul_one 1 hn,
      ← sq_singularValues_eq_eigenvalue_mul_conjTranspose_self, singularValues_zero_eq_specNorm]
  refine le_antisymm ?_ ?_
  · have h1 := specNorm_add_le R (M * Mᴴ)
    rw [specNorm_mul_conjTranspose_self] at h1
    linarith [hR.specNorm_le_one]
  · have hMR : Mᴴ * R = Mᴴ := by
      have h := congrArg Matrix.conjTranspose hM
      rwa [Matrix.conjTranspose_mul, hR.conjTranspose_eq] at h
    have hGR : (R + M * Mᴴ) * R = R + M * Mᴴ := by
      rw [Matrix.add_mul, hR.mul_self, Matrix.mul_assoc, hMR]
    have hGH : (R + M * Mᴴ)ᴴ = R + M * Mᴴ := by
      rw [Matrix.conjTranspose_add, hR.conjTranspose_eq, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hmax := hR.specNorm_add_le_max (X := R + M * Mᴴ) (Y := 1 - R) hGR hR.one_sub.mul_self
      (by rw [hGH, Matrix.mul_sub, Matrix.mul_one, hGR, sub_self])
    have hsplit : M * Mᴴ + (1 : ℝ) • (1 : Matrix n n 𝕜) = R + M * Mᴴ + (1 - R) := by
      rw [one_smul]
      abel
    have h1 : 1 ≤ specNorm (R + M * Mᴴ) := by
      have hle : R ≤ R + M * Mᴴ := by
        rw [Matrix.le_iff, add_sub_cancel_left]
        exact Matrix.posSemidef_self_mul_conjTranspose M
      have h := hR.posSemidef.specNorm_le_specNorm_of_le hle
      rwa [hR.specNorm_eq_one h0] at h
    rw [hsplit] at hG
    have h2 : specNorm (1 - R) ≤ 1 := hR.one_sub.specNorm_le_one
    linarith [hmax.trans (max_le le_rfl (h2.trans h1))]

/-- The off-diagonal block `N = P - rangeProjector P` of an idempotent `P` carries the norms of
`P` and of `1 - P`, and `P` is an orthogonal projector when it vanishes. -/
private theorem exists_specNorm_sq_eq [DecidableEq n] {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) :
    ∃ N : Matrix n n 𝕜, (P ≠ 0 → specNorm P ^ 2 = 1 + specNorm N ^ 2) ∧
      (P ≠ 1 → specNorm (1 - P) ^ 2 = 1 + specNorm N ^ 2) ∧ (N = 0 → IsStarProjection P) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n 𝕜, Q = rangeProjector P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix n n 𝕜, N = P - Q := ⟨_, rfl⟩
  have hQ : IsStarProjection Q := hQdef ▸ isStarProjection_rangeProjector P
  have hQP : Q * P = P := by rw [hQdef, rangeProjector_mul_self]
  have hPQ : P * Q = Q := by
    rw [hQdef]
    exact hP.mul_eq_of_range_le (range_mulVecLin_rangeProjector P).le
  have hPeq : P = Q + N := by rw [hN]; abel
  have hQN : Q * N = N := by rw [hN, Matrix.mul_sub, hQP, hQ.mul_self]
  have hNQ : N * Q = 0 := by rw [hN, Matrix.sub_mul, hPQ, hQ.mul_self, sub_self]
  have hQNH : Q * Nᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hNQ
    rwa [Matrix.conjTranspose_mul, hQ.conjTranspose_eq, Matrix.conjTranspose_zero] at h
  have hNHQ : Nᴴ * Q = Nᴴ := by
    have h := congrArg Matrix.conjTranspose hQN
    rwa [Matrix.conjTranspose_mul, hQ.conjTranspose_eq] at h
  refine ⟨N, fun h0 => ?_, fun h1 => ?_, fun h => ?_⟩
  · have hgram : P * Pᴴ = Q + N * Nᴴ := by
      rw [hPeq, Matrix.conjTranspose_add, hQ.conjTranspose_eq, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add, hQ.mul_self, hQNH, hNQ, add_zero, zero_add]
    rw [← specNorm_mul_conjTranspose_self, hgram]
    refine specNorm_add_mul_conjTranspose_self hQ (fun hQ0 => h0 ?_) hQN
    rw [← hQP, hQ0, Matrix.zero_mul]
  · obtain ⟨R, hRdef⟩ : ∃ R : Matrix n n 𝕜, R = 1 - Q := ⟨_, rfl⟩
    have hR : IsStarProjection R := hRdef ▸ hQ.one_sub
    have hRN : R * Nᴴ = Nᴴ := by rw [hRdef, Matrix.sub_mul, Matrix.one_mul, hQNH, sub_zero]
    have hgram : (1 - P)ᴴ * (1 - P) = R + Nᴴ * Nᴴᴴ := by
      have e1 : (1 : Matrix n n 𝕜) - P = R - N := by rw [hPeq, hRdef]; abel
      have e2 : R * N = 0 := by rw [hRdef, Matrix.sub_mul, Matrix.one_mul, hQN, sub_self]
      have e3 : Nᴴ * R = 0 := by rw [hRdef, Matrix.mul_sub, Matrix.mul_one, hNHQ, sub_self]
      rw [e1, Matrix.conjTranspose_sub, hR.conjTranspose_eq, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, hR.mul_self, e2, e3, Matrix.conjTranspose_conjTranspose]
      abel
    rw [← specNorm_conjTranspose_mul_self, hgram, ← specNorm_conjTranspose N]
    refine specNorm_add_mul_conjTranspose_self hR (fun hR0 => h1 ?_) hRN
    have hQ1 : Q = 1 := (sub_eq_zero.mp (hRdef ▸ hR0)).symm
    rw [← Matrix.mul_one P, ← hQ1]
    exact hPQ
  · rw [hPeq, h, add_zero]
    exact hQ

/-- A nonzero idempotent has spectral norm at least one.
Port of `NLAlib.one_le_specNorm_of_isIdempotentElem`. -/
theorem _root_.IsIdempotentElem.one_le_specNorm {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h : P ≠ 0) : 1 ≤ specNorm P := by
  have hpos : 0 < specNorm P :=
    lt_of_le_of_ne (specNorm_nonneg P) fun h0 => h (specNorm_eq_zero_iff.mp h0.symm)
  have hle : specNorm P ≤ specNorm P * specNorm P := by
    conv_lhs => rw [← hP.eq]
    exact specNorm_mul_le P P
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

/-- **An idempotent is an orthogonal projector exactly when it is a contraction.**
[HornJohnson2013, §3.1.P25 context]; [Kato1995, §I.6.7]. -/
theorem _root_.IsIdempotentElem.isStarProjection_iff_specNorm_le_one {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) : IsStarProjection P ↔ specNorm P ≤ 1 := by
  classical
  refine ⟨fun h => h.specNorm_le_one, fun h => ?_⟩
  obtain ⟨N, h0, -, hN⟩ := exists_specNorm_sq_eq hP
  by_cases hP0 : P = 0
  · rw [hP0, ← rangeProjector_zero (m := n) (n := n)]
    exact isStarProjection_rangeProjector _
  · refine hN (specNorm_eq_zero_iff.mp ?_)
    have h1 := h0 hP0
    have h2 := specNorm_nonneg P
    have h3 := specNorm_nonneg N
    nlinarith

/-- **An idempotent and its complement have the same norm**, when neither is zero.
[Kato1995, §I.6.7]; [Szyld2006]; [HornJohnson2013, Corollary 3.4.3.3].
Port of `NLAlib.specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt`, there over `ℝ`.
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_one_sub [DecidableEq n] {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : specNorm (1 - P) = specNorm P := by
  obtain ⟨N, hN0, hN1, -⟩ := exists_specNorm_sq_eq hP
  refine (sq_eq_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).mp ?_
  rw [hN0 h0, hN1 h1]

/-- **The secant formula.** The spectral norm of a nonzero idempotent `P` is the secant of the
largest principal angle between its range and the range of `Pᴴ` (the orthogonal complement of its
kernel): `‖P‖₂ cos θ = 1`, and `θ < π / 2`.
[HornJohnson2013, Corollary 3.4.3.3]; [Szyld2006].
Port of `NLAlib.specNorm_idempotent_eq_secant_of_range_frames`, there over `ℝ` with frames.
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_mul_cos_principalAngle {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    specNorm P * Real.cos (principalAngle P Pᴴ j) = 1 := by
  have hpinv : pinv P = rangeProjector Pᴴ * rangeProjector P := by
    rw [← pinv_mul, ← mul_pinv, Matrix.mul_assoc, ← Matrix.mul_assoc P, hP.eq,
      ← Matrix.mul_assoc, pinv_mul_mul_pinv]
  have hcos : Real.cos (principalAngle P Pᴴ j) = (specNorm P)⁻¹ := by
    rw [cos_principalAngle, ← singularValues_conjTranspose, Matrix.conjTranspose_mul,
      conjTranspose_rangeProjector, conjTranspose_rangeProjector, ← hpinv,
      singularValues_pinv P (i := j) (j := 0) (by omega), singularValues_zero_eq_specNorm]
  have hne : specNorm P ≠ 0 := by
    rw [Ne, specNorm_eq_zero_iff]
    rintro rfl
    rw [Matrix.rank_zero] at hj
    omega
  rw [hcos, mul_inv_cancel₀ hne]

/-- The largest principal angle between the range of a nonzero idempotent and the complement of
its kernel is acute. -/
theorem _root_.IsIdempotentElem.principalAngle_conjTranspose_lt {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    principalAngle P Pᴴ j < Real.pi / 2 := by
  have h := hP.specNorm_mul_cos_principalAngle hj
  rw [cos_principalAngle] at h
  rw [principalAngle, Real.arccos_lt_pi_div_two]
  refine lt_of_le_of_ne (singularValues_nonneg _ _) fun h0 => ?_
  rw [← h0, mul_zero] at h
  exact zero_ne_one h

/-! ### The oblique projector of two bases -/

variable [DecidableEq p]

/-- `X * (Yᴴ * X)⁻¹ * Yᴴ` is idempotent when `Yᴴ * X` is invertible: it is the projector onto the
column space of `X` along the orthogonal complement of the column space of `Y`. -/
theorem isIdempotentElem_mul_inv_mul_conjTranspose {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    IsIdempotentElem (X * (Yᴴ * X)⁻¹ * Yᴴ) := by
  have key : X * (Yᴴ * X)⁻¹ * Yᴴ * X = X := by
    rw [Matrix.mul_assoc (X * (Yᴴ * X)⁻¹), Matrix.mul_assoc X,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one]
  rw [IsIdempotentElem, ← Matrix.mul_assoc, ← Matrix.mul_assoc, key]

/-- The oblique projector `X * (Yᴴ * X)⁻¹ * Yᴴ` fixes `X`. -/
theorem mul_inv_mul_conjTranspose_mul_self {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    X * (Yᴴ * X)⁻¹ * Yᴴ * X = X := by
  rw [Matrix.mul_assoc (X * (Yᴴ * X)⁻¹), Matrix.mul_assoc X,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one]

/-- The oblique projector `X * (Yᴴ * X)⁻¹ * Yᴴ` annihilates the orthogonal complement of the
column space of `Y`. -/
theorem mul_inv_mul_conjTranspose_mulVec_eq_zero (X Y : Matrix n p 𝕜) {v : n → 𝕜}
    (hv : Yᴴ *ᵥ v = 0) : (X * (Yᴴ * X)⁻¹ * Yᴴ) *ᵥ v = 0 := by
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- **The norm of an oblique projector between two frames**: for `U`, `V` with orthonormal
columns and `Vᴴ * U` invertible, `‖U (Vᴴ U)⁻¹ Vᴴ‖₂ = ‖(Vᴴ U)⁻¹‖₂`, the reciprocal of the smallest
singular value of `Vᴴ * U`, that is, the secant of the largest principal angle.
[Szyld2006]. -/
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) = specNorm (Vᴴ * U)⁻¹ := by
  rw [Matrix.mul_assoc, hU.specNorm_mul_left, hV.specNorm_mul_conjTranspose_right]

/-- The norm of an oblique projector between two frames, through the principal angle. -/
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose_mul_cos {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (h : IsUnit (Vᴴ * U)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) * Real.cos (principalAngle U V j) = 1 := by
  have hr : (Vᴴ * U).rank = Fintype.card p := Matrix.rank_of_isUnit _ h
  rw [hU.specNorm_mul_inv_mul_conjTranspose hV, ← pinv_of_isUnit h,
    specNorm_pinv _ (k := j) (by rw [hr, hj]), hU.cos_principalAngle hV,
    ← singularValues_conjTranspose (Uᴴ * V), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  exact inv_mul_cancel₀ (ne_of_gt ((singularValues_pos_iff _).mpr (by omega)))

end NLAlib
