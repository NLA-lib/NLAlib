/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Multiplicative perturbations

Bounds for the singular values, the pseudoinverse and the condition number of `S * A` in terms of
those of `A`, when the Gram matrices are comparable:
`a • Aᴴ A ≤ (S A)ᴴ (S A) ≤ b • Aᴴ A`. This two-sided bound is what a subspace embedding
guarantees, and the consequences here are what sketch-and-precondition and sketched least squares
consume.

## Main results

* `NLAlib.mul_sq_singularValues_le_of_smul_le`, `NLAlib.sq_singularValues_le_mul_of_le_smul`:
  singular values under comparable Gram matrices.
* `NLAlib.rank_eq_of_smul_le_of_le_smul`: the rank is preserved.
* `NLAlib.conditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul`: the condition number.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- **Singular values under a lower Gram bound.** If `a • Aᴴ A ≤ Bᴴ B` with `0 ≤ a`, then
`a σ_i(A)² ≤ σ_i(B)²` for every `i`. With `B = S * A` this is the lower half of a subspace
embedding. [HornJohnson2013, Corollary 7.7.4 for the Gram matrices]. -/
theorem mul_sq_singularValues_le_of_smul_le {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a : ℝ}
    (ha : 0 ≤ a) (h : a • (Aᴴ * A) ≤ Bᴴ * B) (i : ℕ) :
    a * singularValues A i ^ 2 ≤ singularValues B i ^ 2 := by
  have hk := eigenvalue_le_eigenvalue_of_le h
    ((Matrix.isHermitian_conjTranspose_mul_self A).smul (IsSelfAdjoint.all a)) i
  rwa [eigenvalue_real_smul _ ha, ← sq_singularValues, ← sq_singularValues] at hk

/-- **Singular values under an upper Gram bound.** If `Bᴴ B ≤ b • Aᴴ A` then
`σ_i(B)² ≤ b σ_i(A)²` for every `i`. -/
theorem sq_singularValues_le_mul_of_le_smul {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {b : ℝ}
    (h : Bᴴ * B ≤ b • (Aᴴ * A)) (i : ℕ) :
    singularValues B i ^ 2 ≤ b * singularValues A i ^ 2 := by
  rcases le_or_gt 0 b with hb | hb
  · have hk := eigenvalue_le_eigenvalue_of_le h (Matrix.isHermitian_conjTranspose_mul_self B) i
    rwa [eigenvalue_real_smul _ hb, ← sq_singularValues, ← sq_singularValues] at hk
  · have hB : 0 ≤ Bᴴ * B := (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
    have hA : 0 ≤ (-b) • (Aᴴ * A) :=
      ((Matrix.posSemidef_conjTranspose_mul_self A).smul (neg_nonneg.mpr hb.le)).nonneg
    rw [neg_smul, neg_nonneg] at hA
    have hB0 : Bᴴ * B = 0 := le_antisymm (h.trans hA) hB
    have hA0 : Aᴴ * A = 0 :=
      (smul_eq_zero.mp (le_antisymm hA (hB.trans h))).resolve_left hb.ne
    rw [Matrix.conjTranspose_mul_self_eq_zero.mp hB0, Matrix.conjTranspose_mul_self_eq_zero.mp hA0,
      singularValues_zero, singularValues_zero, Pi.zero_apply, zero_pow two_ne_zero, mul_zero]

/-- Comparable Gram matrices have the same rank. -/
theorem rank_eq_of_smul_le_of_le_smul {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (Aᴴ * A) ≤ Bᴴ * B) (h₂ : Bᴴ * B ≤ b • (Aᴴ * A)) :
    B.rank = A.rank := by
  refine le_antisymm (Nat.le_of_not_gt fun hlt => ?_) (Nat.le_of_not_gt fun hlt => ?_)
  · have hB := (singularValues_pos_iff B).mpr hlt
    have hA := (singularValues_eq_zero_iff A).mpr le_rfl
    have h := sq_singularValues_le_mul_of_le_smul h₂ A.rank
    rw [hA, zero_pow two_ne_zero, mul_zero] at h
    exact absurd h (not_le.mpr (pow_pos hB 2))
  · have hA := (singularValues_pos_iff A).mpr hlt
    have hB := (singularValues_eq_zero_iff B).mpr le_rfl
    have h := mul_sq_singularValues_le_of_smul_le ha.le h₁ B.rank
    rw [hB, zero_pow two_ne_zero] at h
    exact absurd h (not_le.mpr (mul_pos ha (pow_pos hA 2)))

/-- Under a lower Gram bound the pseudoinverse is controlled:
`‖B⁺‖₂² ≤ a⁻¹ ‖A⁺‖₂²` when `a • Aᴴ A ≤ Bᴴ B`, `0 < a`, and the ranks agree. -/
theorem specNorm_pinv_sq_le_of_smul_le {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a : ℝ}
    (ha : 0 < a) (h : a • (Aᴴ * A) ≤ Bᴴ * B) (hr : B.rank = A.rank) :
    specNorm (pinv B) ^ 2 ≤ a⁻¹ * specNorm (pinv A) ^ 2 := by
  rcases Nat.eq_zero_or_pos A.rank with h0 | h0
  · rw [Matrix.rank_eq_zero.mp h0, Matrix.rank_eq_zero.mp (hr.trans h0), pinv_zero, pinv_zero,
      specNorm_zero, specNorm_zero, zero_pow two_ne_zero, mul_zero]
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = A.rank := ⟨A.rank - 1, by omega⟩
    have hA := (singularValues_pos_iff A).mpr (by omega : k < A.rank)
    have hle := mul_sq_singularValues_le_of_smul_le ha.le h k
    rw [specNorm_pinv A hk, specNorm_pinv B (hk.trans hr.symm), inv_pow, inv_pow, ← mul_inv]
    exact inv_anti₀ (mul_pos ha (pow_pos hA 2)) hle

/-- **The condition number under comparable Gram matrices**: if
`a • Aᴴ A ≤ Bᴴ B ≤ b • Aᴴ A` with `0 < a`, then `κ(B) ≤ √(b / a) κ(A)`.
With `B = S * A` this is the conditioning of a sketched matrix. -/
theorem conditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul {A : Matrix m n 𝕜}
    {B : Matrix l n 𝕜} {a b : ℝ} (ha : 0 < a) (h₁ : a • (Aᴴ * A) ≤ Bᴴ * B)
    (h₂ : Bᴴ * B ≤ b • (Aᴴ * A)) : conditionNumber B ≤ √(b / a) * conditionNumber A := by
  rcases Nat.eq_zero_or_pos A.rank with h0 | h0
  · rw [Matrix.rank_eq_zero.mp ((rank_eq_of_smul_le_of_le_smul ha h₁ h₂).trans h0),
      conditionNumber_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (conditionNumber_nonneg A)
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = A.rank := ⟨A.rank - 1, by omega⟩
    have hr := rank_eq_of_smul_le_of_le_smul ha h₁ h₂
    have hA := (singularValues_pos_iff A).mpr (by omega : k < A.rank)
    have hB := (singularValues_pos_iff B).mpr (by omega : k < B.rank)
    have hlo := mul_sq_singularValues_le_of_smul_le ha.le h₁ k
    have hhi := sq_singularValues_le_mul_of_le_smul h₂ 0
    rw [conditionNumber_eq_singularValues_div A hk,
      conditionNumber_eq_singularValues_div B (hk.trans hr.symm)]
    rw [← Real.sqrt_sq (div_nonneg (singularValues_nonneg A 0) hA.le),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_pow, div_mul_div_comm,
      div_le_div_iff₀ (pow_pos hB 2) (mul_pos ha (pow_pos hA 2))]
    exact mul_le_mul hhi hlo (mul_pos ha (pow_pos hA 2)).le ((sq_nonneg _).trans hhi)

/-- **Ostrowski's theorem for Gram matrices.** For any `S`, the singular values of `S * A`
satisfy `σ_i(S A) ≤ ‖S‖₂ σ_i(A)`; if `S` is bounded below on the range of `A`, in the form
`a • Aᴴ A ≤ (S A)ᴴ (S A)`, then also `√a σ_i(A) ≤ σ_i(S A)`.
[HornJohnson2013, Theorem 4.5.9 (Ostrowski) for the congruence `Aᴴ Sᴴ S A`]. -/
theorem sqrt_mul_singularValues_le_singularValues_mul {S : Matrix l m 𝕜} {A : Matrix m n 𝕜}
    {a : ℝ} (ha : 0 ≤ a) (h : a • (Aᴴ * A) ≤ (S * A)ᴴ * (S * A)) (i : ℕ) :
    √a * singularValues A i ≤ singularValues (S * A) i := by
  have hle := mul_sq_singularValues_le_of_smul_le ha h i
  rw [← Real.sq_sqrt ha, ← mul_pow] at hle
  exact (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg a) (singularValues_nonneg A i))
    (singularValues_nonneg _ i) two_ne_zero).mp hle

end NLAlib
