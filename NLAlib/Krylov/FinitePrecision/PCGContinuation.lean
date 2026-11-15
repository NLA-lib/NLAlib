/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.PCGRun

/-!
# Pairing defects in rounded PCG

The search direction is controlled through its pairing with the residual. The exact
defect recurrences retain all the rounded scalar and vector errors, including the
computed numerator error. No linearity of the preconditioner action is used.

## Main results

* `NLAlib.PCGRun.dotProduct_p_r_succ`: the rounded line-search identity.
* `NLAlib.PCGRun.dotProduct_r_p_sub_ν_succ`: the pairing-defect recurrence.
* `NLAlib.PCGRun.p_ne_zero_of_abs_dotProduct_r_p_sub_ν_le`: a local direction certificate.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.PCGRun

variable {n k : ℕ} (P : PCGRun n k)

/-- The computed step length multiplied by its computed denominator. -/
theorem γ_mul_μ {j : ℕ} (hj : j < k) :
    P.γ j * P.μ j = P.ν j * (1 + P.eγ j) := by
  rw [P.γ_eq j hj]
  field_simp [(P.μ_pos j hj).ne']

/-- The computed direction coefficient multiplied by the incoming numerator. -/
theorem δ_mul_ν {j : ℕ} (hj : j < k) :
    P.δ j * P.ν j = P.ν (j + 1) * (1 + P.eδ j) := by
  rw [P.δ_eq j hj]
  field_simp [(P.ν_pos j hj).ne']

/-- At initialization the residual/direction pairing differs from the computed numerator
only by the recorded dot-product error. -/
theorem dotProduct_r_p_sub_ν_zero :
    P.r 0 ⬝ᵥ P.p 0 - P.ν 0 = -P.eν 0 := by
  rw [P.p_zero, P.ν_eq 0 (Nat.zero_le _)]
  ring

/-- The old direction paired with the new residual retains the incoming pairing defect,
the scalar line-search defects, and the residual-update error. -/
theorem dotProduct_p_r_succ {j : ℕ} (hj : j < k) :
    P.p j ⬝ᵥ P.r (j + 1) = (P.r j ⬝ᵥ P.p j - P.ν j) -
      P.ν j * P.eγ j + P.γ j * P.eμ j + P.p j ⬝ᵥ P.er j := by
  rw [P.r_succ j hj, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hμ := P.μ_eq j hj
  have hγ := P.γ_mul_μ hj
  rw [hμ] at hγ
  rw [dotProduct_comm (P.r j) (P.p j)]
  nlinarith

/-- The new pairing defect is the old line-search cross-pairing propagated by the
computed direction coefficient, plus the new vector-update and dot-product errors. -/
theorem dotProduct_r_p_sub_ν_succ {j : ℕ} (hj : j < k) :
    P.r (j + 1) ⬝ᵥ P.p (j + 1) - P.ν (j + 1) =
      P.δ j * (P.p j ⬝ᵥ P.r (j + 1)) +
        P.r (j + 1) ⬝ᵥ P.ep j - P.eν (j + 1) := by
  rw [P.p_succ j hj, P.ν_eq (j + 1) (by omega), dotProduct_add, dotProduct_add,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (P.p j) (P.r (j + 1))]
  ring

/-- A positive computed numerator and a relative pairing defect at most one half imply
that the direction is nonzero. This is the endpoint of the quantitative bootstrap. -/
theorem p_ne_zero_of_abs_dotProduct_r_p_sub_ν_le {j : ℕ} (hν : 0 < P.ν j)
    (hd : |P.r j ⬝ᵥ P.p j - P.ν j| ≤ P.ν j / 2) : P.p j ≠ 0 := by
  intro hp
  rw [hp, dotProduct_zero, zero_sub, abs_neg, abs_of_pos hν] at hd
  linarith

/-- The computed system product has the standard normwise growth bound. -/
theorem norm_s_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (P.s j)‖ ≤
      (1 + P.ε) * specNorm P.A * ‖WithLp.toLp 2 (P.p j)‖ := by
  rw [P.s_eq j hj]
  have h₁ := EuclideanSpace.norm_toLp_add_le (P.A *ᵥ P.p j) (P.es j)
  have h₂ := norm_toLp_mulVec_le P.A (P.p j)
  have h₃ := P.norm_es_le j hj
  nlinarith

/-- The actual nonlinear preconditioner output has the norm growth supplied by its oracle. -/
theorem norm_z_le {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (P.z j)‖ ≤
      (1 + P.preconditioner.ε) * specNorm P.M * ‖WithLp.toLp 2 (P.r j)‖ := by
  have h₁ := EuclideanSpace.norm_toLp_add_le
    (P.M *ᵥ P.r j) (P.z j - P.M *ᵥ P.r j)
  have h₂ := norm_toLp_mulVec_le P.M (P.r j)
  have h₃ := P.norm_mulVec_sub_z_le j hj
  rw [show P.M *ᵥ P.r j + (P.z j - P.M *ᵥ P.r j) = P.z j by abel] at h₁
  rw [show P.z j - P.M *ᵥ P.r j = -(P.M *ᵥ P.r j - P.z j) by abel,
    WithLp.toLp_neg, norm_neg] at h₁
  nlinarith

/-- Every computed numerator in the recorded prefix is nonnegative. -/
theorem ν_nonneg {j : ℕ} (hj : j ≤ k) : 0 ≤ P.ν j := by
  rcases hj.lt_or_eq with h | rfl
  · exact (P.ν_pos j h).le
  · exact P.ν_last_nonneg

/-- The computed step length is positive at each recorded active step. -/
theorem γ_pos {j : ℕ} (hj : j < k) : 0 < P.γ j := by
  rw [P.γ_eq j hj]
  have he := (abs_le.mp (P.abs_eγ_le j hj)).1
  have hε := P.ε_le
  exact mul_pos (div_pos (P.ν_pos j hj) (P.μ_pos j hj)) (by linarith)

/-- The computed direction coefficient is nonnegative, including a zero terminal numerator. -/
theorem δ_nonneg {j : ℕ} (hj : j < k) : 0 ≤ P.δ j := by
  rw [P.δ_eq j hj]
  have he := (abs_le.mp (P.abs_eδ_le j hj)).1
  have hε := P.ε_le
  exact mul_nonneg (div_nonneg (P.ν_nonneg (by omega)) (P.ν_pos j hj).le) (by linarith)

/-- The residual norm after an active step, before any spectral estimates. -/
theorem norm_r_succ_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (P.r (j + 1))‖ ≤ (1 + P.ε) *
      (‖WithLp.toLp 2 (P.r j)‖ + P.γ j * ‖WithLp.toLp 2 (P.s j)‖) := by
  rw [P.r_succ j hj]
  have h₁ := EuclideanSpace.norm_toLp_add_le (P.r j - P.γ j • P.s j) (P.er j)
  have h₂ := EuclideanSpace.norm_toLp_sub_le (P.r j) (P.γ j • P.s j)
  have h₃ := P.norm_er_le j hj
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (P.γ_pos hj)] at h₂
  rw [abs_of_pos (P.γ_pos hj)] at h₃
  nlinarith

/-- The search-direction norm after an active step, before any spectral estimates. -/
theorem norm_p_succ_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (P.p (j + 1))‖ ≤ (1 + P.ε) *
      (‖WithLp.toLp 2 (P.z (j + 1))‖ + P.δ j * ‖WithLp.toLp 2 (P.p j)‖) := by
  rw [P.p_succ j hj]
  have h₁ := EuclideanSpace.norm_toLp_add_le
    (P.z (j + 1) + P.δ j • P.p j) (P.ep j)
  have h₂ := EuclideanSpace.norm_toLp_add_le (P.z (j + 1)) (P.δ j • P.p j)
  have h₃ := P.norm_ep_le j hj
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (P.δ_nonneg hj)] at h₂
  rw [abs_of_nonneg (P.δ_nonneg hj)] at h₃
  nlinarith

/-- Absolute line-search cross-pairing, with all its local error contributions. -/
theorem abs_dotProduct_p_r_succ_le {j : ℕ} (hj : j < k) :
    |P.p j ⬝ᵥ P.r (j + 1)| ≤ |P.r j ⬝ᵥ P.p j - P.ν j| + P.ν j * P.ε +
      P.γ j * |P.eμ j| + ‖WithLp.toLp 2 (P.p j)‖ * ‖WithLp.toLp 2 (P.er j)‖ := by
  rw [P.dotProduct_p_r_succ hj]
  have h₁ := abs_add_le
    ((P.r j ⬝ᵥ P.p j - P.ν j) - P.ν j * P.eγ j + P.γ j * P.eμ j)
    (P.p j ⬝ᵥ P.er j)
  have h₂ := abs_add_le ((P.r j ⬝ᵥ P.p j - P.ν j) - P.ν j * P.eγ j)
    (P.γ j * P.eμ j)
  have h₃ : |(P.r j ⬝ᵥ P.p j - P.ν j) - P.ν j * P.eγ j| ≤
      |P.r j ⬝ᵥ P.p j - P.ν j| + |P.ν j * P.eγ j| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (P.r j ⬝ᵥ P.p j - P.ν j) (-(P.ν j * P.eγ j))
  rw [abs_mul, abs_of_pos (P.γ_pos hj)] at h₂
  rw [abs_mul, abs_of_pos (P.ν_pos j hj)] at h₃
  have h₄ := mul_le_mul_of_nonneg_left (P.abs_eγ_le j hj) (P.ν_pos j hj).le
  have h₅ := EuclideanSpace.abs_dotProduct_le_norm (P.p j) (P.er j)
  linarith

/-- The pairing-defect recurrence with absolute values and actual vector errors. -/
theorem abs_dotProduct_r_p_sub_ν_succ_le {j : ℕ} (hj : j < k) :
    |P.r (j + 1) ⬝ᵥ P.p (j + 1) - P.ν (j + 1)| ≤
      P.δ j * |P.p j ⬝ᵥ P.r (j + 1)| +
        ‖WithLp.toLp 2 (P.r (j + 1))‖ * ‖WithLp.toLp 2 (P.ep j)‖ + |P.eν (j + 1)| := by
  rw [P.dotProduct_r_p_sub_ν_succ hj]
  have h₁ : |P.δ j * (P.p j ⬝ᵥ P.r (j + 1)) + P.r (j + 1) ⬝ᵥ P.ep j - P.eν (j + 1)| ≤
      |P.δ j * (P.p j ⬝ᵥ P.r (j + 1)) + P.r (j + 1) ⬝ᵥ P.ep j| + |P.eν (j + 1)| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (P.δ j * (P.p j ⬝ᵥ P.r (j + 1)) + P.r (j + 1) ⬝ᵥ P.ep j) (-P.eν (j + 1))
  have h₂ := abs_add_le (P.δ j * (P.p j ⬝ᵥ P.r (j + 1)))
    (P.r (j + 1) ⬝ᵥ P.ep j)
  rw [abs_mul, abs_of_nonneg (P.δ_nonneg hj)] at h₂
  have h₃ := EuclideanSpace.abs_dotProduct_le_norm (P.r (j + 1)) (P.ep j)
  linarith

end NLAlib.PCGRun
