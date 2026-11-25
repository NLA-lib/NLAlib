/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Norms.Loewner

/-!
# Quantitative margins for Cholesky elimination

The lower spectral margin of an input controls every exact active Schur pivot. These
estimates provide input conditions for rounded elimination without assuming a successful run.

## Main results

* `Matrix.IsHermitian.quadForm_eliminationStep_eq`: elimination is a quadratic-form compression.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- At a nonzero pivot, elimination is congruence by a matrix changing only its pivot row. -/
theorem _root_.Matrix.IsHermitian.eliminationStep_eq_conjTranspose_mul_mul {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {t : n} (ht : A t t ≠ 0) :
    eliminationStep A t =
      (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t))ᴴ * A *
        (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) := by
  have hAM : A * (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) =
      eliminationStep A t := by
    rw [eliminationStep_eq_sub_smul_vecMulVec, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.mulVec_single_one]
    rfl
  have hMA : (1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t))ᴴ * A =
      eliminationStep A t := by
    have h := congrArg Matrix.conjTranspose hAM
    rwa [Matrix.conjTranspose_mul, hA.eq, (hA.eliminationStep t).eq] at h
  rw [hMA, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
    Matrix.mulVec_single_one]
  have hz : (eliminationStep A t).col t = 0 :=
    funext fun i => eliminationStep_apply_pivot_right ht i
  rw [hz, Matrix.zero_vecMulVec, smul_zero, sub_zero]

/-- The quadratic form after elimination is the original form on a vector changed only at
the pivot coordinate. -/
theorem _root_.Matrix.IsHermitian.quadForm_eliminationStep_eq {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {t : n} (ht : A t t ≠ 0) (x : n → 𝕜) :
    quadForm (eliminationStep A t) x =
      quadForm A ((1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) *ᵥ x) := by
  rw [hA.eliminationStep_eq_conjTranspose_mul_mul ht, quadForm_conjTranspose_mul_mul]

private theorem elimination_compression_apply_ne {A : Matrix n n ℝ} {t i : n}
    (hi : i ≠ t) (x : n → ℝ) :
    ((1 - (A t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (A t)) *ᵥ x) i = x i := by
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Pi.single_eq_of_ne hi]

private theorem le_quadForm_gaussState_of_le_smul_one {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) :
    ∀ k ≤ N, ∀ x : Fin N → ℝ, (∀ i, i.val < k → x i = 0) →
      μ * ∑ i, (x i) ^ 2 ≤ quadForm (gaussState A k) x := by
  have hA : A.PosDef := by
    have h := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hlo)
    simpa only [add_sub_cancel] using h
  intro k
  induction k with
  | zero =>
    intro _ x _
    have h := re_quadForm_le_re_quadForm_of_le hlo x
    simpa [quadForm, Matrix.smul_mulVec, dotProduct, Finset.mul_sum, pow_two, mul_left_comm] using h
  | succ k ih =>
    intro hk x hx
    have hkN : k < N := by omega
    let t : Fin N := ⟨k, hkN⟩
    let S := gaussState A k
    let W := 1 - (S t t)⁻¹ • Matrix.vecMulVec (Pi.single t 1) (S t)
    have hp : S t t ≠ 0 := (hA.gaussState_apply_self_pos t).ne'
    have hz : ∀ i : Fin N, i.val < k → (W *ᵥ x) i = 0 := by
      intro i hi
      have hit : i ≠ t := by intro h; subst i; simp [t] at hi
      rw [elimination_compression_apply_ne hit]
      exact hx i (by omega)
    have hs : ∑ i, (x i) ^ 2 ≤ ∑ i, ((W *ᵥ x) i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hit : i = t
      · subst i
        rw [hx t (by simp [t])]
        simpa using sq_nonneg ((W *ᵥ x) t)
      · rw [elimination_compression_apply_ne hit]
    rw [gaussState_succ A hkN, (hA.isHermitian.gaussState k).quadForm_eliminationStep_eq hp]
    exact (mul_le_mul_of_nonneg_left hs hμ.le).trans (ih (by omega) (W *ᵥ x) hz)

/-- A positive lower spectral input margin is a lower bound for each exact Schur pivot. -/
theorem le_gaussState_apply_self_of_smul_one_le {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (i : Fin N) :
    μ ≤ gaussState A i i i := by
  have h := le_quadForm_gaussState_of_le_smul_one hμ hlo i.val (by omega)
    (Pi.single i 1) (by
      intro j hj
      simp [show j ≠ i from fun he => by subst j; omega])
  simpa [quadForm, dotProduct, Matrix.mulVec_single_one, Pi.single_apply,
    apply_ite, ite_mul] using h

/-- Exact Schur states of a positive semidefinite input decrease in the Loewner order. -/
theorem _root_.Matrix.PosSemidef.gaussState_le {N : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosSemidef) (k : ℕ) :
    gaussState A k ≤ A := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hk : k < N
    · rw [gaussState_succ A hk]
      exact ((hA.gaussState k).eliminationStep_le _).trans ih
    · simpa only [gaussState, dif_neg hk] using ih

/-- Every exact Schur entry of a positive semidefinite input is at most its input spectral
norm bound in magnitude. -/
theorem _root_.Matrix.PosSemidef.norm_gaussState_apply_le {N : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosSemidef) {B : ℝ} (hB : specNorm A ≤ B)
    (k : ℕ) (i j : Fin N) : ‖gaussState A k i j‖ ≤ B := by
  exact (norm_apply_le_specNorm _ i j).trans
    (((hA.gaussState k).specNorm_le_specNorm_of_le (hA.gaussState_le k)).trans hB)

end NLAlib
