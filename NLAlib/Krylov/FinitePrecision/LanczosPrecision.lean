/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Normalization

/-!
# Precision budget for rounded stored Lanczos execution

The implementation budget controls the actual dense matvec, dot, axpy, norm and component
division errors. Normalization requires a separate squared norm defect allowance; the CG
budget is not substituted for that condition. Empty dimension is included.

## Main results

* `NLAlib.normalizationRoundingFactor_le_lanczosImplementationRoundoffBound`:
  the squared unit-vector defect fits the implementation budget.
* `NLAlib.lanczosImplementationRoundoffBound_kernel_bounds`: primitive execution windows.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The input-only stored Lanczos budget,
shown by <!-- value lanczosImplementationRoundoffBound N u -->
$$16(N+1)^2u.$$
The normalization defect and every actual kernel defect fit this budget under its stated
small-roundoff window. No computed trajectory quantity appears in the budget. -/
noncomputable irreducible_def lanczosImplementationRoundoffBound (N : ℕ) (u : ℝ) : ℝ :=
  16 * ((N : ℝ) + 1) ^ 2 * u

/-- The implementation precision budget is nonnegative at nonnegative unit roundoff. -/
theorem lanczosImplementationRoundoffBound_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ lanczosImplementationRoundoffBound N u := by
  rw [lanczosImplementationRoundoffBound_def]
  positivity

private theorem mul_succ_le_budget (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    16 * ((N : ℝ) + 1) * u ≤ lanczosImplementationRoundoffBound N u := by
  rw [lanczosImplementationRoundoffBound_def]
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hu, mul_nonneg hN hu]

/-- Every ordered product factor needed by the implementation is controlled by dimension
and input precision, including zero-length products. -/
theorem roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le {N m : ℕ}
    (hm : m ≤ 2 * (N + 1)) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor m u ≤ 2 * m * u := by
  have hMu := (mul_succ_le_budget N hu).trans hsmall
  have hmr : (m : ℝ) ≤ 2 * ((N : ℝ) + 1) := by exact_mod_cast hm
  have hmu : (m : ℝ) * u ≤ 2 * ((N : ℝ) + 1) * u :=
    mul_le_mul_of_nonneg_right hmr hu
  have hmu0 : 0 ≤ (m : ℝ) * u := by positivity
  apply (roundingFactor_le hu (by linarith : (m : ℝ) * u < 1)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - (m : ℝ) * u)).mpr
  nlinarith [mul_nonneg hmu0 (show 0 ≤ 1 - 2 * ((m : ℝ) * u) by linarith)]

/-- The actual ordered dot-product error fits the implementation budget in every dimension. -/
theorem roundingFactor_le_lanczosImplementationRoundoffBound (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor N u ≤ lanczosImplementationRoundoffBound N u := by
  have hγ := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N) (by omega) hu hsmall
  have hMu := mul_succ_le_budget N hu
  have hNu : 0 ≤ (N : ℝ) * u := by positivity
  nlinarith

/-- The Frobenius-to-spectral multiplier of the actual dense matrix kernel fits the
input-only implementation budget, also in empty dimension. -/
theorem roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor N u * Real.sqrt N ≤ lanczosImplementationRoundoffBound N u := by
  have hγ := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N) (by omega) hu hsmall
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsqrt : Real.sqrt N ≤ (N : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  calc
    _ ≤ (2 * N * u) * (N + 1) := mul_le_mul hγ hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ ≤ 16 * ((N : ℝ) + 1) ^ 2 * u := by
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hu, mul_nonneg hN hu]
    _ = _ := (lanczosImplementationRoundoffBound_def N u).symm

/-- Squared near-unit error after the actual rounded norm and divisions is bounded by the
implementation budget. The full normalization factor retains its product terms. -/
theorem normalizationRoundingFactor_le_lanczosImplementationRoundoffBound (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    normalizationRoundingFactor N u ≤ lanczosImplementationRoundoffBound N u := by
  have hMu := mul_succ_le_budget N hu
  have hn : (N + 1 : ℕ) * u ≤ 1 / 100 := by
    push_cast
    have : 0 ≤ ((N : ℝ) + 1) * u := by positivity
    linarith
  refine (normalizationRoundingFactor_le hu hn).trans ?_
  push_cast
  have : 0 ≤ ((N : ℝ) + 1) * u := by positivity
  linarith

/-- The input precision budget supplies the actual nrm2, rscl and axpy execution windows,
and dominates component division errors and two-operation vector-update errors. -/
theorem lanczosImplementationRoundoffBound_kernel_bounds (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    (N + 1 : ℕ) * u < 1 ∧ 2 * u < 1 ∧ roundingFactor (N + 1) u < 1 ∧
      roundingFactor 2 u ≤ lanczosImplementationRoundoffBound N u ∧
      u ≤ lanczosImplementationRoundoffBound N u := by
  have hMu := mul_succ_le_budget N hu
  have hM0 : 0 ≤ ((N : ℝ) + 1) * u := by positivity
  have huM : u ≤ ((N : ℝ) + 1) * u := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hu]
  have hγM := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N + 1) (by omega) hu hsmall
  have hγ2 := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := 2) (by omega) hu hsmall
  push_cast at hγM ⊢
  refine ⟨by linarith, by linarith, by linarith, ?_, by linarith⟩
  norm_num at hγ2
  linarith

/-- The rounding factor $\gamma_{N+1}(u)$ of a norm of length $N$ is at most the Lanczos
implementation budget `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, which
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$, when $u \ge 0$ and the
budget is at most $1/100$. -/
theorem roundingFactor_succ_le_lanczosImplementationRoundoffBound (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor (N + 1) u ≤ lanczosImplementationRoundoffBound N u := by
  have hγ := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N + 1) (by omega) hu hsmall
  rw [lanczosImplementationRoundoffBound_def] at hsmall ⊢
  push_cast at hγ
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_nonneg (mul_nonneg hN hN) hu, mul_nonneg hN hu]

end NLAlib
