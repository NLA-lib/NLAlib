/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedOutput
public import NLAlib.Krylov.FinitePrecision.BackwardBounds

/-!
# Backward error of the actual rounded Lanczos output

A nonzero input and positive cap yield a positive-length run. Its vectors and coefficients
are the same archived values read from the packed output, including zero padding after early
breakdown. The existing backward-error theorem then applies without repeating execution.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Output.exists_run`: positive run tied to actual output.
* `NLAlib.Krylov.Lanczos.Rounded.Output.exists_run_backward`: the same run's backward bound.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {E : ℝ} {vs cs : List K}

/-- Positive cap and nonzero actual input exclude the zero-step alternative. The resulting
existing run retains all physical ties and the actual initial normalization error. -/
theorem Output.exists_run (h : Output dec A rhs E cap vs cs) (hcap : 0 < cap)
    (hrhs : rhs ≠ 0) :
    ∃ done ≤ cap, ∃ z : Values n, ∃ R : LanczosRun n done,
      Outcome A rhs E done z ∧ PackedOutput dec cap z vs cs ∧
      R.H = A ∧ R.ε = E ∧ R.v = z.v ∧ R.α = z.alpha ∧ R.β = z.beta ∧
      (done < cap → z.beta done = 0) := by
  obtain ⟨done, hd, z, ho, hp, hs⟩ := h
  have hdone : done ≠ 0 := by
    intro he
    subst done
    have hz : z.initialNorm = 0 := by simpa using hs hcap
    exact hrhs (ho.norm_zero.mp hz)
  rcases ho.run with hzero | ⟨R, hH, hE, hv, ha, hb⟩
  · exact (hdone hzero.1).elim
  · exact ⟨done, hd, z, R, ho, hp, hH, hE, hv, ha, hb,
      fun hlt => by simpa [hdone] using hs hlt⟩

/-- Under the input cap's quadratic small-roundoff condition, the same physically identified
run satisfies the existing Frobenius backward bound, even if it stopped before the cap. -/
theorem Output.exists_run_backward (h : Output dec A rhs E cap vs cs) (hcap : 0 < cap)
    (hrhs : rhs ≠ 0) (hsmall : (cap : ℝ) ^ 2 * E ≤ 1 / 1000) :
    ∃ done ≤ cap, ∃ z : Values n, ∃ R : LanczosRun n done,
      Outcome A rhs E done z ∧ PackedOutput dec cap z vs cs ∧
      R.H = A ∧ R.ε = E ∧ R.v = z.v ∧ R.α = z.alpha ∧ R.β = z.beta ∧
      (done < cap → z.beta done = 0) ∧
      frobNorm (R.backwardH - R.dilatedH) ≤
        lanczosSmallRoundoffBackwardFactor done * E * specNorm A := by
  obtain ⟨done, hd, z, R, ho, hp, hH, hE, hv, ha, hb, hs⟩ := h.exists_run hcap hrhs
  have he : 0 ≤ E := by simpa only [hE] using R.ε_nonneg
  have hm : (done : ℝ) ^ 2 ≤ (cap : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg done) (Nat.cast_le.mpr hd) 2
  have hbound := R.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le
    (show (done : ℝ) ^ 2 * R.ε ≤ 1 / 1000 by
      rw [hE]
      exact (mul_le_mul_of_nonneg_right hm he).trans hsmall)
  exact ⟨done, hd, z, R, ho, hp, hH, hE, hv, ha, hb, hs, by simpa [hH, hE] using hbound⟩

end NLAlib.Krylov.Lanczos.Rounded
