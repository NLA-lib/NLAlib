/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Subspaces.PrincipalAngles

/-!
# Oblique projections

An idempotent matrix $\mathbf{P}$ projects onto its range along its kernel. It is an orthogonal
projector exactly when its spectral norm is at most one. For a nonzero projection the norm is the
secant of the largest principal angle between its range and the orthogonal complement of its
kernel. If $\mathbf{P}$ is neither zero nor the identity, then $\mathbf{P}$ and
$\mathbf{I} - \mathbf{P}$ have the same norm. The oblique projector onto the
column space of $\mathbf{X}$ along the orthogonal complement of the column space of $\mathbf{Y}$
is $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$.

## Main results

* `IsIdempotentElem.trace_eq_rank`: the trace of an idempotent matrix is its rank.
* `IsIdempotentElem.one_le_specNorm`, `IsIdempotentElem.isStarProjection_iff_specNorm_le_one`.
* `IsIdempotentElem.specNorm_sq`: $\|\mathbf{P}\|_2^2 = 1 + \|\mathbf{P} -
  \mathbf{P}_{\mathbf{P}}\|_2^2$ for a nonzero idempotent.
* `IsIdempotentElem.specNorm_one_sub`: $\|\mathbf{I} - \mathbf{P}\|_2 = \|\mathbf{P}\|_2$ for a
  nontrivial idempotent.
* `IsIdempotentElem.pinv_eq_rangeProjector_conjTranspose_mul_rangeProjector`: the pseudoinverse
  of an idempotent.
* `IsIdempotentElem.specNorm_mul_cos_principalAngle`: the secant formula.
* `IsIdempotentElem.isUnit_conjTranspose_mul_of_range_le`: the overlap of two bases adapted to an
  idempotent is invertible.

The two-bases spelling $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$
is `NLAlib.obliqueProjector X Yᴴ` (`NLAlib.Matrix.Subspaces.ObliqueProjector`), every rank; the six
lemmas stated with it here are deprecated since 2026-10-15 for their restatements in
`NLAlib.Matrix.Subspaces.ObliqueProjector` and `NLAlib.Matrix.Subspaces.ObliqueBases`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [Fintype p]

/-! ### Idempotent matrices -/

/-- The trace of an idempotent matrix over a field is its rank:
$\operatorname{tr} \mathbf{P} = \operatorname{rank} \mathbf{P}$.
[HornJohnson2013, §3.1.P25 context]. -/
theorem _root_.IsIdempotentElem.trace_eq_rank {K : Type*} [Field K] {P : Matrix n n K}
    (hP : IsIdempotentElem P) : P.trace = P.rank := by
  classical
  have hf : IsIdempotentElem P.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hP.eq]
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply']
  exact ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hf).trace

/-- An idempotent matrix fixes the column space of any matrix inside its range:
$\mathbf{P}\mathbf{X} = \mathbf{X}$ when the column space of $\mathbf{X}$ lies in the range of
$\mathbf{P}$. -/
theorem _root_.IsIdempotentElem.mul_eq_of_range_le {R : Type*} [CommSemiring R]
    {P : Matrix n n R} (hP : IsIdempotentElem P) {X : Matrix n p R}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range P.mulVecLin) : P * X = X := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := h (show X *ᵥ x ∈ LinearMap.range X.mulVecLin from ⟨x, rfl⟩)
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP.eq]

/-- For a nonzero orthogonal projector $\mathbf{R}$ and $\mathbf{M}$ with columns in the range of
$\mathbf{R}$, $\|\mathbf{R} + \mathbf{M}\mathbf{M}^{\mathsf{H}}\|_2 = 1 + \|\mathbf{M}\|_2^2$. -/
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
      ← singularValues_sq_eq_eigenvalue_mul_conjTranspose_self, singularValues_zero_eq_specNorm]
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

/-- The off-diagonal block $\mathbf{P} - \mathbf{P}_{\mathbf{P}}$ of an idempotent $\mathbf{P}$
carries the norms of $\mathbf{P}$ and of $\mathbf{I} - \mathbf{P}$, and $\mathbf{P}$ is an
orthogonal projector when it vanishes. -/
private theorem specNorm_sq_eq_and [DecidableEq n] {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) :
    (P ≠ 0 → specNorm P ^ 2 = 1 + specNorm (P - rangeProjector P) ^ 2) ∧
      (P ≠ 1 → specNorm (1 - P) ^ 2 = 1 + specNorm (P - rangeProjector P) ^ 2) ∧
      (P - rangeProjector P = 0 → IsStarProjection P) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n 𝕜, Q = rangeProjector P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix n n 𝕜, N = P - Q := ⟨_, rfl⟩
  rw [← hQdef, ← hN]
  have hQ : IsStarProjection Q := hQdef ▸ isStarProjection_rangeProjector P
  have hQP : Q * P = P := by rw [hQdef, rangeProjector_mul_self]
  have hPQ : P * Q = Q := by
    rw [hQdef]
    exact hP.mul_eq_of_range_le (range_rangeProjector P).le
  have hPeq : P = Q + N := by rw [hN]; abel
  have hQN : Q * N = N := by rw [hN, Matrix.mul_sub, hQP, hQ.mul_self]
  have hNQ : N * Q = 0 := by rw [hN, Matrix.sub_mul, hPQ, hQ.mul_self, sub_self]
  have hQNH : Q * Nᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hNQ
    rwa [Matrix.conjTranspose_mul, hQ.conjTranspose_eq, Matrix.conjTranspose_zero] at h
  have hNHQ : Nᴴ * Q = Nᴴ := by
    have h := congrArg Matrix.conjTranspose hQN
    rwa [Matrix.conjTranspose_mul, hQ.conjTranspose_eq] at h
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h => ?_⟩
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

/-- **The norm of an idempotent from its off-diagonal part.** A nonzero idempotent $\mathbf{P}$
is its range projector $\mathbf{P}_{\mathbf{P}}$ plus the part
$\mathbf{P} - \mathbf{P}_{\mathbf{P}}$ that maps the orthogonal complement of the range into the
range, and $\|\mathbf{P}\|_2^2 = 1 + \|\mathbf{P} - \mathbf{P}_{\mathbf{P}}\|_2^2$.
[Szyld2006]. -/
theorem _root_.IsIdempotentElem.specNorm_sq {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : specNorm P ^ 2 = 1 + specNorm (P - rangeProjector P) ^ 2 := by
  classical
  exact (specNorm_sq_eq_and hP).1 h0

/-- A nonzero idempotent has spectral norm at least one: $1 \le \|\mathbf{P}\|_2$. -/
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

/-- **An idempotent is an orthogonal projector exactly when it is a contraction**,
$\|\mathbf{P}\|_2 \le 1$.
[HornJohnson2013, §3.1.P25 context]; [Kato1995, §I.6.7]. -/
theorem _root_.IsIdempotentElem.isStarProjection_iff_specNorm_le_one {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) : IsStarProjection P ↔ specNorm P ≤ 1 := by
  classical
  refine ⟨fun h => h.specNorm_le_one, fun h => ?_⟩
  by_cases hP0 : P = 0
  · rw [hP0, ← rangeProjector_zero (m := n) (n := n)]
    exact isStarProjection_rangeProjector _
  · refine (specNorm_sq_eq_and hP).2.2 (specNorm_eq_zero_iff.mp ?_)
    have h1 := hP.specNorm_sq hP0
    have h2 := specNorm_nonneg P
    have h3 := specNorm_nonneg (P - rangeProjector P)
    nlinarith

/-- **An idempotent and its complement have the same norm**, when neither is zero:
$\|\mathbf{I} - \mathbf{P}\|_2 = \|\mathbf{P}\|_2$ for $\mathbf{P} \ne \mathbf{0}, \mathbf{I}$.
[Kato1995, §I.6.7]; [Szyld2006]; [HornJohnson2013, Corollary 3.4.3.3].
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_one_sub [DecidableEq n] {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : specNorm (1 - P) = specNorm P := by
  refine (sq_eq_sq₀ (specNorm_nonneg _) (specNorm_nonneg _)).mp ?_
  rw [hP.specNorm_sq h0, (specNorm_sq_eq_and hP).2.1 h1]

/-- The pseudoinverse of an idempotent $\mathbf{P}$ is the product of the orthogonal projectors
onto the range of $\mathbf{P}^{\mathsf{H}}$ and onto the range of $\mathbf{P}$:
$\mathbf{P}^{+} = \mathbf{P}_{\mathbf{P}^{\mathsf{H}}}\mathbf{P}_{\mathbf{P}}$. This is how the norm
of an oblique projector is read off the principal angles between those two ranges. -/
theorem _root_.IsIdempotentElem.pinv_eq_rangeProjector_conjTranspose_mul_rangeProjector
    {P : Matrix n n 𝕜} (hP : IsIdempotentElem P) :
    pinv P = rangeProjector Pᴴ * rangeProjector P := by
  rw [← pinv_mul, ← mul_pinv, Matrix.mul_assoc, ← Matrix.mul_assoc P, hP.eq,
    ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- **The secant formula.** The spectral norm of a nonzero idempotent $\mathbf{P}$ is the secant
of the largest principal angle between its range and the range of $\mathbf{P}^{\mathsf{H}}$ (the
orthogonal complement of its kernel): $\|\mathbf{P}\|_2 \cos \theta_j = 1$ with
$\theta_j = \theta_j(\mathbf{P}, \mathbf{P}^{\mathsf{H}})$ and
$j + 1 = \operatorname{rank} \mathbf{P}$; that $\theta_j < \pi / 2$ is
`IsIdempotentElem.principalAngle_conjTranspose_lt`.
[HornJohnson2013, Corollary 3.4.3.3]; [Szyld2006].
Result: oblique-projection-norm -/
theorem _root_.IsIdempotentElem.specNorm_mul_cos_principalAngle {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    specNorm P * Real.cos (principalAngle P Pᴴ j) = 1 := by
  have hpinv := hP.pinv_eq_rangeProjector_conjTranspose_mul_rangeProjector
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
its kernel is acute: $\theta_j(\mathbf{P}, \mathbf{P}^{\mathsf{H}}) < \pi / 2$ for
$j + 1 = \operatorname{rank} \mathbf{P}$. -/
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

/-- $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$ is idempotent when
$\mathbf{Y}^{\mathsf{H}}\mathbf{X}$ is invertible: it is the projector onto the column space of
$\mathbf{X}$ along the orthogonal complement of the column space of $\mathbf{Y}$. -/
@[deprecated "Use `isIdempotentElem_obliqueProjector` and `obliqueProjector_of_isUnit`."
  (since := "2026-10-15")]
theorem isIdempotentElem_mul_inv_mul_conjTranspose {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    IsIdempotentElem (X * (Yᴴ * X)⁻¹ * Yᴴ) := by
  have key : X * (Yᴴ * X)⁻¹ * Yᴴ * X = X := by
    rw [Matrix.mul_assoc (X * (Yᴴ * X)⁻¹), Matrix.mul_assoc X,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one]
  rw [IsIdempotentElem, ← Matrix.mul_assoc, ← Matrix.mul_assoc, key]

/-- The oblique projector fixes $\mathbf{X}$:
$\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}\mathbf{X} = \mathbf{X}$
when $\mathbf{Y}^{\mathsf{H}}\mathbf{X}$ is invertible. -/
@[deprecated "Use `obliqueProjector_mul_self_iff` and `obliqueProjector_of_isUnit`."
  (since := "2026-10-15")]
theorem mul_inv_mul_conjTranspose_mul_self {X Y : Matrix n p 𝕜} (h : IsUnit (Yᴴ * X)) :
    X * (Yᴴ * X)⁻¹ * Yᴴ * X = X := by
  rw [Matrix.mul_assoc (X * (Yᴴ * X)⁻¹), Matrix.mul_assoc X,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one]

/-- The oblique projector
$\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$ annihilates the
orthogonal complement of the column space of $\mathbf{Y}$: it sends $\mathbf{v}$ with
$\mathbf{Y}^{\mathsf{H}}\mathbf{v} = \mathbf{0}$ to $\mathbf{0}$. -/
@[deprecated "Use `Matrix.mulVec_mulVec` and the hypothesis, or
  `obliqueProjector_mul_eq_zero_of_mul_eq_zero` at one column." (since := "2026-10-15")]
theorem mul_inv_mul_conjTranspose_mulVec_eq_zero (X Y : Matrix n p 𝕜) {v : n → 𝕜}
    (hv : Yᴴ *ᵥ v = 0) : (X * (Yᴴ * X)⁻¹ * Yᴴ) *ᵥ v = 0 := by
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- **The overlap of two bases adapted to an idempotent is invertible.** If the columns of
$\mathbf{X}$ are independent and lie in the range of an idempotent $\mathbf{P}$, and the column
space of $\mathbf{Y}$ contains the range of $\mathbf{P}^{\mathsf{H}}$ (the orthogonal complement of
the kernel of $\mathbf{P}$), then $\mathbf{Y}^{\mathsf{H}}\mathbf{X}$ is invertible.
Matrices with orthonormal columns are the case `HasOrthonormalCols.mulVec_injective`; no
independence of the columns of $\mathbf{Y}$ is assumed, it follows.
[HornJohnson2013, Corollary 3.4.3.3 context]. -/
theorem _root_.IsIdempotentElem.isUnit_conjTranspose_mul_of_range_le {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {X Y : Matrix n p 𝕜} (hX : Function.Injective X.mulVec)
    (hXP : LinearMap.range X.mulVecLin ≤ LinearMap.range P.mulVecLin)
    (hYP : LinearMap.range Pᴴ.mulVecLin ≤ LinearMap.range Y.mulVecLin) : IsUnit (Yᴴ * X) := by
  obtain ⟨D, hD⟩ := range_le_iff_exists_mul.mp hYP
  have hPX : Dᴴ * (Yᴴ * X) = X := by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← hD, Matrix.conjTranspose_conjTranspose]
    exact hP.mul_eq_of_range_le hXP
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w h
  have h' := congrArg Dᴴ.mulVec h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPX] at h'
  exact hX h'

/-- **Every idempotent is an oblique projector of two bases.** If the columns of $\mathbf{X}$ are
a basis of the range of an idempotent $\mathbf{P}$ and the columns of $\mathbf{Y}$ span the range
of $\mathbf{P}^{\mathsf{H}}$ (the orthogonal complement of the kernel of $\mathbf{P}$), then
$\mathbf{P} = \mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$, with
$\mathbf{Y}^{\mathsf{H}}\mathbf{X}$ invertible by
`IsIdempotentElem.isUnit_conjTranspose_mul_of_range_le`. This is the converse of
`NLAlib.isIdempotentElem_mul_inv_mul_conjTranspose`. Matrices with orthonormal columns are the case
`HasOrthonormalCols.mulVec_injective`; for $\mathbf{P} = \mathbf{0}$ the bases have no columns.
[HornJohnson2013, Corollary 3.4.3.3 context]. -/
@[deprecated "Use `IsIdempotentElem.obliqueProjector_eq` and `obliqueProjector_of_isUnit`."
  (since := "2026-10-15")]
theorem _root_.IsIdempotentElem.eq_mul_inv_mul_conjTranspose {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {X Y : Matrix n p 𝕜} (hX : Function.Injective X.mulVec)
    (hXP : LinearMap.range X.mulVecLin = LinearMap.range P.mulVecLin)
    (hYP : LinearMap.range Y.mulVecLin = LinearMap.range Pᴴ.mulVecLin) :
    P = X * (Yᴴ * X)⁻¹ * Yᴴ := by
  have hu := hP.isUnit_conjTranspose_mul_of_range_le hX hXP.le hYP.ge
  obtain ⟨C, hC⟩ := range_le_iff_exists_mul.mp hXP.ge
  have hPH : IsIdempotentElem Pᴴ := by
    rw [IsIdempotentElem, ← Matrix.conjTranspose_mul, hP.eq]
  have hYP' : Yᴴ * P = Yᴴ := by
    have h := congrArg Matrix.conjTranspose (hPH.mul_eq_of_range_le hYP.le)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  calc P = X * ((Yᴴ * X)⁻¹ * (Yᴴ * X)) * C := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one, hC]
    _ = X * (Yᴴ * X)⁻¹ * (Yᴴ * (X * C)) := by simp only [Matrix.mul_assoc]
    _ = X * (Yᴴ * X)⁻¹ * Yᴴ := by rw [← hC, hYP']

/-- **The norm of an oblique projector between two frames**: for $\mathbf{U}$, $\mathbf{V}$ with
orthonormal columns,
$$\|\mathbf{U}(\mathbf{V}^{\mathsf{H}}\mathbf{U})^{-1}\mathbf{V}^{\mathsf{H}}\|_2
  = \|(\mathbf{V}^{\mathsf{H}}\mathbf{U})^{-1}\|_2\,.$$
No invertibility is assumed (Mathlib's inverse of a singular matrix is $\mathbf{0}$). When
$\mathbf{V}^{\mathsf{H}}\mathbf{U}$ is invertible this is the reciprocal of its smallest singular
value, that is, the secant of the largest principal angle
(`HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose_mul_cos`).
Deprecated for `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector`, which agrees
with this lemma where $\mathbf{V}^{\mathsf{H}}\mathbf{U}$ is invertible; where it is singular
both sides here are $0$ (Mathlib's inverse), a case the replacement states with the
pseudoinverse instead, for frames of any widths.
[Szyld2006]. -/
@[deprecated "Use `HasOrthonormalCols.specNorm_obliqueProjector`." (since := "2026-10-15")]
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) = specNorm (Vᴴ * U)⁻¹ := by
  rw [Matrix.mul_assoc, hU.specNorm_mul_left, hV.specNorm_mul_conjTranspose_right]

/-- The norm of an oblique projector between two frames, through the principal angle: for
$\mathbf{U}$, $\mathbf{V}$ with orthonormal columns indexed by $p$ and
$\mathbf{V}^{\mathsf{H}}\mathbf{U}$ invertible,
$\|\mathbf{U}(\mathbf{V}^{\mathsf{H}}\mathbf{U})^{-1}\mathbf{V}^{\mathsf{H}}\|_2
\cos \theta_j(\mathbf{U}, \mathbf{V}) = 1$ for $j + 1 = \lvert p \rvert$. Deprecated
for `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos`, the same statement. -/
@[deprecated "Use `HasOrthonormalCols.specNorm_obliqueProjector_mul_cos`."
  (since := "2026-10-15")]
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose_mul_cos {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (h : IsUnit (Vᴴ * U)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) * Real.cos (principalAngle U V j) = 1 := by
  have hr : (Vᴴ * U).rank = Fintype.card p := Matrix.rank_of_isUnit _ h
  rw [Matrix.mul_assoc, hU.specNorm_mul_left, hV.specNorm_mul_conjTranspose_right,
    ← pinv_of_isUnit h,
    specNorm_pinv _ (k := j) (by rw [hr, hj]), hU.cos_principalAngle hV,
    ← singularValues_conjTranspose (Uᴴ * V), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  exact inv_mul_cancel₀ (ne_of_gt ((singularValues_pos_iff _).mpr (by omega)))

end NLAlib
