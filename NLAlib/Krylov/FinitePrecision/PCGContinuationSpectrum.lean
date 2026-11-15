/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.PCGContinuation

/-!
# Spectral bounds for rounded PCG continuation

Positive spectral windows control the computed pairings through their actual recorded
operator and dot errors. The bounds use the raw input matrices and common precision.

## Main results

* `NLAlib.PCGRun.mul_norm_sq_le_ν`: coercivity of the computed numerator.
* `NLAlib.PCGRun.mul_norm_sq_le_μ`: coercivity of the computed curvature.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.PCGRun

private theorem pairing_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {a a' e : ℝ} (hA : Aᵀ = A) (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (he : 0 ≤ e) (he1 : e ≤ 1)
    (hprec : 6 * e * a' ≤ a) {v w : Fin n → ℝ} {d : ℝ} (hv : v ≠ 0)
    (hw : ‖WithLp.toLp 2 (A *ᵥ v - w)‖ ≤ e * specNorm A * ‖WithLp.toLp 2 v‖)
    (hd : |d| ≤ e * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖) :
    a / 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ w + d := by
  obtain ⟨haa, hN, hq⟩ := specNorm_le_and_le_dotProduct hA ha.le hs hv
  have hV := norm_nonneg (WithLp.toLp 2 v)
  have hN0 := specNorm_nonneg A
  have hE : ‖WithLp.toLp 2 (w - A *ᵥ v)‖ ≤ e * a' * ‖WithLp.toLp 2 v‖ := by
    rw [show w - A *ᵥ v = -(A *ᵥ v - w) by abel, WithLp.toLp_neg, norm_neg]
    exact hw.trans (by gcongr)
  have hW : ‖WithLp.toLp 2 w‖ ≤ 2 * a' * ‖WithLp.toLp 2 v‖ := by
    have ht := EuclideanSpace.norm_toLp_add_le (A *ᵥ v) (w - A *ᵥ v)
    rw [show A *ᵥ v + (w - A *ᵥ v) = w by abel] at ht
    have hm := norm_toLp_mulVec_le A v
    have hNe : specNorm A * ‖WithLp.toLp 2 v‖ ≤ a' * ‖WithLp.toLp 2 v‖ := by gcongr
    have hEe : e * a' * ‖WithLp.toLp 2 v‖ ≤ a' * ‖WithLp.toLp 2 v‖ := by
      have ha'0 : 0 ≤ a' := ha.le.trans haa
      nlinarith [mul_le_mul_of_nonneg_right he1 (mul_nonneg ha'0 hV)]
    linarith
  have hdot := EuclideanSpace.abs_dotProduct_le_norm v (w - A *ᵥ v)
  have hdot' : |v ⬝ᵥ w - v ⬝ᵥ (A *ᵥ v)| ≤ e * a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [← dotProduct_sub]
    exact hdot.trans (by nlinarith [mul_le_mul_of_nonneg_left hE hV])
  have hd' : |d| ≤ 2 * e * a' * ‖WithLp.toLp 2 v‖ ^ 2 :=
    hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hW (mul_nonneg he hV)])
  have hbudget := mul_le_mul_of_nonneg_right hprec (sq_nonneg ‖WithLp.toLp 2 v‖)
  nlinarith [(abs_le.mp hdot').1, (abs_le.mp hd').1]

variable {n k : ℕ} (P : PCGRun n k)

/-- Every direction used by a recorded successful step is nonzero. -/
theorem p_ne_zero {j : ℕ} (hj : j < k) : P.p j ≠ 0 := by
  intro hp
  have he := P.abs_eμ_le j hj
  rw [hp, WithLp.toLp_zero, norm_zero, mul_zero, zero_mul] at he
  have hz := abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
  have hm := P.μ_pos j hj
  rw [P.μ_eq j hj, hp, zero_dotProduct, hz, add_zero] at hm
  exact lt_irrefl _ hm

/-- A positive spectral window for the inverse preconditioner and the input precision
window give a quantitative lower bound on every nonzero residual's computed numerator. -/
theorem mul_norm_sq_le_ν {m m' : ℝ} (hm : 0 < m)
    (hs : spectrum ℝ P.M ⊆ Set.Icc m m') (hprec : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε) {j : ℕ} (hj : j ≤ k) (hr : P.r j ≠ 0) :
    m / 2 * ‖WithLp.toLp 2 (P.r j)‖ ^ 2 ≤ P.ν j := by
  rw [P.ν_eq j hj]
  apply pairing_ge (by simpa only [Matrix.IsHermitian,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    P.posDef_M.isHermitian) hm hs P.ε_nonneg (P.ε_le.trans (by norm_num)) hprec hr
  · exact (P.norm_mulVec_sub_z_le j hj).trans (by gcongr)
  · exact P.abs_eν_le j hj

/-- The system spectral window and common precision give a quantitative lower bound on
each computed curvature in the prefix. -/
theorem mul_norm_sq_le_μ {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ P.A ⊆ Set.Icc a a') (hprec : 6 * P.ε * a' ≤ a)
    {j : ℕ} (hj : j < k) :
    a / 2 * ‖WithLp.toLp 2 (P.p j)‖ ^ 2 ≤ P.μ j := by
  rw [P.μ_eq j hj]
  apply pairing_ge (by simpa only [Matrix.IsHermitian,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    P.isHermitian_A) ha hs P.ε_nonneg (P.ε_le.trans (by norm_num)) hprec (P.p_ne_zero hj)
  · rw [P.s_eq j hj, show P.A *ᵥ P.p j - (P.A *ᵥ P.p j + P.es j) = -P.es j by abel,
      WithLp.toLp_neg, norm_neg]
    exact P.norm_es_le j hj
  · exact P.abs_eμ_le j hj

/-- The step-length weighted product term is bounded by the computed numerator, with
the system spectral ratio as the only geometric factor. -/
theorem γ_mul_norm_p_mul_norm_s_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ P.A ⊆ Set.Icc a a') (hprec : 6 * P.ε * a' ≤ a)
    {j : ℕ} (hj : j < k) :
    P.γ j * ‖WithLp.toLp 2 (P.p j)‖ * ‖WithLp.toLp 2 (P.s j)‖ ≤
      8 * (a' / a) * P.ν j := by
  obtain ⟨haa, hN, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      P.isHermitian_A) ha.le hs (P.p_ne_zero hj)
  have ha'0 : 0 ≤ a' := ha.le.trans haa
  have hν := (P.ν_pos j hj).le
  have hQ := norm_nonneg (WithLp.toLp 2 (P.p j))
  have hγ := (P.γ_pos hj).le
  have hε := P.ε_le
  have hε0 := P.ε_nonneg
  have hS : ‖WithLp.toLp 2 (P.s j)‖ ≤ 2 * a' * ‖WithLp.toLp 2 (P.p j)‖ := by
    have h₁ := P.norm_s_le hj
    have h₂ : (1 + P.ε) * specNorm P.A ≤ 2 * a' := by
      nlinarith [specNorm_nonneg P.A]
    exact h₁.trans (mul_le_mul_of_nonneg_right h₂ hQ)
  have hμ := P.mul_norm_sq_le_μ ha hs hprec hj
  have hγμ := P.γ_mul_μ hj
  have heγ := (abs_le.mp (P.abs_eγ_le j hj)).2
  have hγμ' : P.γ j * P.μ j ≤ 2 * P.ν j := by
    nlinarith [mul_le_mul_of_nonneg_left heγ (P.ν_pos j hj).le]
  have hcurv : a * P.γ j * ‖WithLp.toLp 2 (P.p j)‖ ^ 2 ≤ 4 * P.ν j := by
    nlinarith [mul_le_mul_of_nonneg_left hμ hγ]
  calc
    _ ≤ P.γ j * ‖WithLp.toLp 2 (P.p j)‖ *
        (2 * a' * ‖WithLp.toLp 2 (P.p j)‖) := by gcongr
    _ = (2 * a' / a) * (a * P.γ j * ‖WithLp.toLp 2 (P.p j)‖ ^ 2) := by
      field_simp
    _ ≤ (2 * a' / a) * (4 * P.ν j) := by gcongr
    _ = _ := by ring

/-- If the incoming relative pairing defect is at most one half, residual norm growth
in one rounded PCG step is at most sixty-four times the system spectral ratio. -/
theorem norm_r_succ_le_mul_norm_r {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ P.A ⊆ Set.Icc a a') (hprec : 6 * P.ε * a' ≤ a)
    {j : ℕ} (hj : j < k)
    (hd : |P.r j ⬝ᵥ P.p j - P.ν j| ≤ P.ν j / 2) :
    ‖WithLp.toLp 2 (P.r (j + 1))‖ ≤
      64 * (a' / a) * ‖WithLp.toLp 2 (P.r j)‖ := by
  have hq : 0 < ‖WithLp.toLp 2 (P.p j)‖ := by
    rw [norm_pos_iff]
    exact fun h => P.p_ne_zero hj ((WithLp.toLp_eq_zero 2).mp h)
  obtain ⟨haa, -, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      P.isHermitian_A) ha.le hs (P.p_ne_zero hj)
  have hκ : 1 ≤ a' / a := (one_le_div ha).2 haa
  have hdot := (le_abs_self _).trans
    (EuclideanSpace.abs_dotProduct_le_norm (P.r j) (P.p j))
  have hν : P.ν j ≤ 2 * ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ := by
    linarith [(abs_le.mp hd).1]
  have hline := P.γ_mul_norm_p_mul_norm_s_le ha hs hprec hj
  have hline' : P.γ j * ‖WithLp.toLp 2 (P.s j)‖ ≤
      16 * (a' / a) * ‖WithLp.toLp 2 (P.r j)‖ := by
    have hh := mul_le_mul_of_nonneg_left hν (by positivity : 0 ≤ 8 * (a' / a))
    nlinarith
  have hstep := P.norm_r_succ_le hj
  have hε := P.ε_le
  have hR := norm_nonneg (WithLp.toLp 2 (P.r j))
  have hstep' := mul_le_mul_of_nonneg_left hline' (by have := P.ε_nonneg; positivity : 0 ≤ 1 + P.ε)
  have hκR : ‖WithLp.toLp 2 (P.r j)‖ ≤ (a' / a) * ‖WithLp.toLp 2 (P.r j)‖ := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hε (by positivity :
    0 ≤ 17 * (a' / a) * ‖WithLp.toLp 2 (P.r j)‖)]

/-- The residual times its preconditioner-output norm is controlled by the computed
numerator and the reference inverse-preconditioner's spectral ratio. -/
theorem norm_r_mul_norm_z_le {m m' : ℝ} (hm : 0 < m)
    (hs : spectrum ℝ P.M ⊆ Set.Icc m m') (hprec : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.z j)‖ ≤
      4 * (m' / m) * P.ν j := by
  by_cases hr : P.r j = 0
  · rw [hr, WithLp.toLp_zero, norm_zero, zero_mul, P.ν_eq_zero_of_r_eq_zero hj hr,
      mul_zero]
  obtain ⟨hmm, hN, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      P.posDef_M.isHermitian) hm.le hs hr
  have hm'0 : 0 ≤ m' := hm.le.trans hmm
  have hR := norm_nonneg (WithLp.toLp 2 (P.r j))
  have hZ : ‖WithLp.toLp 2 (P.z j)‖ ≤ 2 * m' * ‖WithLp.toLp 2 (P.r j)‖ := by
    have h₁ := P.norm_z_le hj
    have h₂ : (1 + P.preconditioner.ε) * specNorm P.M ≤ 2 * m' := by
      have hε := P.ε_le
      have hO0 := P.preconditioner.ε_nonneg
      nlinarith [specNorm_nonneg P.M]
    exact h₁.trans (mul_le_mul_of_nonneg_right h₂ hR)
  have hν := P.mul_norm_sq_le_ν hm hs hprec hO hj hr
  calc
    _ ≤ ‖WithLp.toLp 2 (P.r j)‖ * (2 * m' * ‖WithLp.toLp 2 (P.r j)‖) := by gcongr
    _ = (4 * m' / m) * (m / 2 * ‖WithLp.toLp 2 (P.r j)‖ ^ 2) := by
      field_simp; ring
    _ ≤ (4 * m' / m) * P.ν j := by gcongr
    _ = _ := by ring

/-- A nonnegative new numerator bounds the computed direction coefficient times the
old numerator, uniformly over every prefix step. -/
theorem δ_mul_ν_le {j : ℕ} (hj : j < k) : P.δ j * P.ν j ≤ 2 * P.ν (j + 1) := by
  rw [P.δ_mul_ν hj]
  have he := (abs_le.mp (P.abs_eδ_le j hj)).2
  have hε := P.ε_le
  have hν := P.ν_nonneg (j := j + 1) (by omega)
  nlinarith [mul_le_mul_of_nonneg_left he hν]

/-- The propagated old direction term, normalized by the new computed numerator. -/
theorem δ_mul_norm_r_succ_mul_norm_p_le {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    {j : ℕ} (hj : j < k)
    (hR : ‖WithLp.toLp 2 (P.r (j + 1))‖ ≤ B * ‖WithLp.toLp 2 (P.r j)‖)
    (hQ : ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤ L * P.ν j) :
    P.δ j * ‖WithLp.toLp 2 (P.r (j + 1))‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤
      2 * B * L * P.ν (j + 1) := by
  have hδ := P.δ_nonneg hj
  calc
    _ ≤ P.δ j * (B * ‖WithLp.toLp 2 (P.r j)‖) * ‖WithLp.toLp 2 (P.p j)‖ := by gcongr
    _ = B * P.δ j * (‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖) := by ring
    _ ≤ B * P.δ j * (L * P.ν j) := by gcongr
    _ = B * L * (P.δ j * P.ν j) := by ring
    _ ≤ B * L * (2 * P.ν (j + 1)) :=
      mul_le_mul_of_nonneg_left (P.δ_mul_ν_le hj) (mul_nonneg hB hL)
    _ = _ := by ring

/-- A one-step recurrence for the dimensionless residual/direction norm product. -/
theorem norm_r_succ_mul_norm_p_succ_le {m m' B L : ℝ} (hm : 0 < m)
    (hs : spectrum ℝ P.M ⊆ Set.Icc m m') (hprec : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {j : ℕ} (hj : j < k)
    (hR : ‖WithLp.toLp 2 (P.r (j + 1))‖ ≤ B * ‖WithLp.toLp 2 (P.r j)‖)
    (hQ : ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤ L * P.ν j) :
    ‖WithLp.toLp 2 (P.r (j + 1))‖ * ‖WithLp.toLp 2 (P.p (j + 1))‖ ≤
      (8 * (m' / m) + 4 * B * L) * P.ν (j + 1) := by
  have hp := mul_le_mul_of_nonneg_left (P.norm_p_succ_le hj)
    (norm_nonneg (WithLp.toLp 2 (P.r (j + 1))))
  have hz := P.norm_r_mul_norm_z_le hm hs hprec hO (j := j + 1) (by omega)
  have hδ := P.δ_mul_norm_r_succ_mul_norm_p_le hB hL hj hR hQ
  have hε := P.ε_le
  have hε0 := P.ε_nonneg
  have hsum : 0 ≤ ‖WithLp.toLp 2 (P.r (j + 1))‖ *
      (‖WithLp.toLp 2 (P.z (j + 1))‖ + P.δ j * ‖WithLp.toLp 2 (P.p j)‖) := by
    exact mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _)
      (mul_nonneg (P.δ_nonneg hj) (norm_nonneg _)))
  nlinarith [mul_le_mul_of_nonneg_right hε hsum]

/-- The old direction/new residual cross-pairing is bounded by the current defect and
the dimensionless residual/direction norm product. -/
theorem abs_dotProduct_p_r_succ_le_mul_ν {a a' L d : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ P.A ⊆ Set.Icc a a') (hprec : 6 * P.ε * a' ≤ a)
    {j : ℕ} (hj : j < k)
    (hD : |P.r j ⬝ᵥ P.p j - P.ν j| ≤ d * P.ν j)
    (hQ : ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤ L * P.ν j) :
    |P.p j ⬝ᵥ P.r (j + 1)| ≤ (d + P.ε * (1 + 16 * (a' / a) + L)) * P.ν j := by
  have hγ := (P.γ_pos hj).le
  have hε := P.ε_nonneg
  have hQ0 := norm_nonneg (WithLp.toLp 2 (P.p j))
  have hline := P.γ_mul_norm_p_mul_norm_s_le ha hs hprec hj
  have hμ : P.γ j * |P.eμ j| ≤ 8 * P.ε * (a' / a) * P.ν j := by
    calc
      _ ≤ P.γ j * (P.ε * ‖WithLp.toLp 2 (P.p j)‖ * ‖WithLp.toLp 2 (P.s j)‖) :=
        mul_le_mul_of_nonneg_left (P.abs_eμ_le j hj) hγ
      _ = P.ε * (P.γ j * ‖WithLp.toLp 2 (P.p j)‖ * ‖WithLp.toLp 2 (P.s j)‖) := by ring
      _ ≤ P.ε * (8 * (a' / a) * P.ν j) := mul_le_mul_of_nonneg_left hline hε
      _ = _ := by ring
  have her := P.norm_er_le j hj
  rw [abs_of_pos (P.γ_pos hj)] at her
  have her' : ‖WithLp.toLp 2 (P.p j)‖ * ‖WithLp.toLp 2 (P.er j)‖ ≤
      P.ε * (L + 8 * (a' / a)) * P.ν j := by
    have h₁ := mul_le_mul_of_nonneg_left her hQ0
    have h₂ := mul_le_mul_of_nonneg_left hQ hε
    have h₃ := mul_le_mul_of_nonneg_left hline hε
    nlinarith
  have hd := P.abs_dotProduct_p_r_succ_le hj
  nlinarith

/-- A one-step recurrence for the relative residual/direction pairing defect. -/
theorem abs_dotProduct_r_p_sub_ν_succ_le_mul_ν {a a' m m' B L d : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hAp : 6 * P.ε * a' ≤ a) (hm : 0 < m)
    (hMs : spectrum ℝ P.M ⊆ Set.Icc m m') (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε) (hB : 0 ≤ B) (hL : 0 ≤ L) (hd : 0 ≤ d)
    {j : ℕ} (hj : j < k)
    (hR : ‖WithLp.toLp 2 (P.r (j + 1))‖ ≤ B * ‖WithLp.toLp 2 (P.r j)‖)
    (hD : |P.r j ⬝ᵥ P.p j - P.ν j| ≤ d * P.ν j)
    (hQ : ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤ L * P.ν j) :
    |P.r (j + 1) ⬝ᵥ P.p (j + 1) - P.ν (j + 1)| ≤
      (2 * d + P.ε * (2 + 32 * (a' / a) + 2 * L + 8 * (m' / m) + 2 * B * L)) *
        P.ν (j + 1) := by
  have hδ := P.δ_nonneg hj
  have hε := P.ε_nonneg
  have hν := P.ν_nonneg (j := j + 1) (by omega)
  have hQ0 := norm_nonneg (WithLp.toLp 2 (P.r (j + 1)))
  have hκ : 0 ≤ a' / a := by
    obtain ⟨haa, -, -⟩ := specNorm_le_and_le_dotProduct
      (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
        using P.isHermitian_A) ha.le hAs (P.p_ne_zero hj)
    exact div_nonneg (ha.le.trans haa) ha.le
  have hcoef : 0 ≤ d + P.ε * (1 + 16 * (a' / a) + L) := by positivity
  have ht := P.abs_dotProduct_p_r_succ_le_mul_ν ha hAs hAp hj hD hQ
  have ht' : P.δ j * |P.p j ⬝ᵥ P.r (j + 1)| ≤
      2 * (d + P.ε * (1 + 16 * (a' / a) + L)) * P.ν (j + 1) := by
    calc
      _ ≤ P.δ j * ((d + P.ε * (1 + 16 * (a' / a) + L)) * P.ν j) := by gcongr
      _ = (d + P.ε * (1 + 16 * (a' / a) + L)) * (P.δ j * P.ν j) := by ring
      _ ≤ (d + P.ε * (1 + 16 * (a' / a) + L)) * (2 * P.ν (j + 1)) := by
        exact mul_le_mul_of_nonneg_left (P.δ_mul_ν_le hj) hcoef
      _ = _ := by ring
  have hz := P.norm_r_mul_norm_z_le hm hMs hMp hO (j := j + 1) (by omega)
  have hδq := P.δ_mul_norm_r_succ_mul_norm_p_le hB hL hj hR hQ
  have hep := P.norm_ep_le j hj
  rw [abs_of_nonneg hδ] at hep
  have hep' := mul_le_mul_of_nonneg_left hep hQ0
  have hνerr := P.abs_eν_le (j + 1) (by omega)
  have hzε := mul_le_mul_of_nonneg_left hz hε
  have hδε := mul_le_mul_of_nonneg_left hδq hε
  have hdef := P.abs_dotProduct_r_p_sub_ν_succ_le hj
  nlinarith

end NLAlib.PCGRun
