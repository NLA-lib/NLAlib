/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Rounding
public import NLAlib.Krylov.FinitePrecision.CGRun

/-!
# Precision budget for stored CG arithmetic

Scalar comparisons for the input-only budget used by rounded stored CG execution.
These pure inequalities relate ordered arithmetic factors to dimension-dependent budgets.
They introduce no program execution or successful-run premise.

## Main results

* `NLAlib.cgImplementationRoundoffBound_nonneg`: nonnegative precision budget.
* `NLAlib.roundingFactor_mul_sqrt_le_cgImplementationRoundoffBound`: product-error allowance.
* `NLAlib.roundingFactor_two_le_cgImplementationRoundoffBound`: vector-update allowance.
-/

@[expose] public section

namespace NLAlib

/-- The implementation roundoff budget for stored CG, with current value
shown by <!-- value cgImplementationRoundoffBound N u -->
$$4N^2u.$$
For positive matrix dimension, the input-only small-roundoff window ensures this controls
every actual kernel error of the canonical stored CG implementation. -/
noncomputable irreducible_def cgImplementationRoundoffBound (N : ℕ) (u : ℝ) : ℝ :=
  4 * (N : ℝ) ^ 2 * u

/-- The dimension-dependent roundoff bound is nonnegative at nonnegative roundoff. -/
theorem cgImplementationRoundoffBound_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cgImplementationRoundoffBound N u := by
  rw [cgImplementationRoundoffBound_def]
  positivity

/-- In positive dimension the proposed implementation bound dominates four times unit
roundoff; this also covers zero unit roundoff. -/
theorem four_mul_le_cgImplementationRoundoffBound {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) : 4 * u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [cgImplementationRoundoffBound_def]
  nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - 1 by nlinarith) hu]

private theorem cg_implementation_mul_le {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u) :
    4 * (N : ℝ) * u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [cgImplementationRoundoffBound_def]
  nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - N by nlinarith) hu]

/-- The dot-product rounding factor is bounded by twice dimension times unit roundoff when
the implementation precision budget is at most one hundredth. -/
theorem roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor N u ≤ 2 * N * u := by
  have hNu := (cg_implementation_mul_le hN hu).trans hsmall
  have hNu0 : 0 ≤ (N : ℝ) * u := by positivity
  have hden : 0 < 1 - (N : ℝ) * u := by linarith
  refine (Computation.roundingFactor_le hu (by linarith : (N : ℝ) * u < 1)).trans ?_
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg hNu0 (show 0 ≤ 1 / 2 - (N : ℝ) * u by linarith)]

/-- The dense matvec spectral-error multiplier is bounded by the input-only proposed
implementation budget, including zero unit roundoff. -/
theorem roundingFactor_mul_sqrt_le_cgImplementationRoundoffBound {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor N u * Real.sqrt N ≤
      cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : Real.sqrt N ≤ (N : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith⟩
  have hγ := roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le hN hu hsmall
  calc
    Computation.roundingFactor N u * Real.sqrt N ≤ (2 * N * u) * N :=
      mul_le_mul hγ hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ ≤ cgImplementationRoundoffBound N u := by
      rw [cgImplementationRoundoffBound_def]
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hu]

/-- The two-operation vector-update factor is bounded by the input-only
implementation budget. -/
theorem roundingFactor_two_le_cgImplementationRoundoffBound {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    Computation.roundingFactor 2 u ≤ cgImplementationRoundoffBound N u := by
  have h4u := four_mul_le_cgImplementationRoundoffBound hN hu
  have hden : 0 < 1 - (2 : ℝ) * u := by linarith
  have hγ : Computation.roundingFactor 2 u ≤ 4 * u := by
    calc
      Computation.roundingFactor 2 u ≤ 2 * u / (1 - 2 * u) :=
        Computation.roundingFactor_le hu (by norm_num; linarith)
      _ ≤ 4 * u := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg hu (show 0 ≤ 1 / 4 - u by linarith)]
  exact hγ.trans h4u

/-- The input-only CG horizon window implies the local implementation budget is at most
one hundred-thousandth. No measured trajectory or successful-run premise is needed. -/
theorem cgImplementationRoundoffBound_le_of_mul_le {N q : ℕ} (hq : 0 < q)
    {u κ : ℝ} (hu : 0 ≤ u) (hκ : 1 ≤ κ)
    (hsmall : (q : ℝ) ^ 2 * Real.sqrt q * cgImplementationRoundoffBound N u * κ ^ 2 ≤
      1 / 10 ^ 5) : cgImplementationRoundoffBound N u ≤ 1 / 10 ^ 5 := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : 1 ≤ (q : ℝ) ^ 2 := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hqr
  have hκ2 : 1 ≤ κ ^ 2 := by nlinarith
  have hprod : 1 ≤ (q : ℝ) ^ 2 * Real.sqrt q := by
    simpa only [one_mul] using mul_le_mul hq2 hsqrt (by norm_num) (by positivity)
  have hprod' : 1 ≤ ((q : ℝ) ^ 2 * Real.sqrt q) * κ ^ 2 := by
    simpa only [one_mul] using mul_le_mul hprod hκ2 (by norm_num) (by positivity)
  have h := mul_le_mul_of_nonneg_right hprod' (cgImplementationRoundoffBound_nonneg N hu)
  nlinarith

/-- The input-only implementation budget supplies the primitive dot/division windows and
dominates the self-dot rounding factor. No measured execution quantity occurs here. -/
theorem cgImplementationRoundoffBound_kernel_bounds {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    (N : ℝ) * u < 1 ∧ 2 * u < 1 ∧
      Computation.roundingFactor N u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNu0 : 0 ≤ (N : ℝ) * u := by positivity
  have h4Nu : 4 * N * u ≤ cgImplementationRoundoffBound N u := by
    rw [cgImplementationRoundoffBound_def]
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - N by nlinarith) hu]
  have h4u := four_mul_le_cgImplementationRoundoffBound hN hu
  refine ⟨by linarith, by linarith, ?_⟩
  exact (roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le hN hu hsmall).trans
    (by linarith)

end NLAlib
