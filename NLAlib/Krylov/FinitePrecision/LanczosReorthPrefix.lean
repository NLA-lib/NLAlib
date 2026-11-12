/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun
public import Mathlib.Data.List.TakeWhile

/-!
# The first inadmissible reorthogonalized Lanczos step

The existing prefix selector reads the actual saved raw norms and coupling coefficients.
It always yields a length at most the number of executed rounds, with strict admissibility
before that length and a quantitative failed test at the next step when one exists.
This selection is a mathematical analysis of stored output, not a change to runtime stopping.

## Main results

* `NLAlib.reorthSteps_le`: the selected prefix is bounded by the executed horizon.
* `NLAlib.mul_lt_beta_of_lt_reorthSteps`: every selected step is strictly admissible.
* `NLAlib.beta_le_of_reorthSteps_lt`: the first excluded step fails the strict test.
-/

@[expose] public section

namespace NLAlib

/-- The stored-output prefix length is the first index failing its strict test, or the cap. -/
theorem reorthSteps_eq_findIdx (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ) :
    reorthSteps τ ν β q =
      (List.range q).findIdx (fun j => !(τ * ν j < β (j + 1))) := by
  classical
  rw [reorthSteps, List.takeWhile_eq_take_findIdx_not, List.length_take]
  exact Nat.min_eq_left (by simpa only [List.length_range] using
    (List.findIdx_le_length (xs := List.range q)
      (p := fun j => !(τ * ν j < β (j + 1)))))

/-- The longest leading admissible prefix never exceeds the actual executed horizon. -/
theorem reorthSteps_le (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ) : reorthSteps τ ν β q ≤ q := by
  rw [reorthSteps_eq_findIdx]
  simpa only [List.length_range] using
    (List.findIdx_le_length (xs := List.range q)
      (p := fun j => !(τ * ν j < β (j + 1))))

/-- Every step strictly before the first excluded step satisfies the actual coefficient test. -/
theorem mul_lt_beta_of_lt_reorthSteps (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ) {j : ℕ}
    (hj : j < reorthSteps τ ν β q) : τ * ν j < β (j + 1) := by
  classical
  rw [reorthSteps_eq_findIdx] at hj
  have h := List.not_of_lt_findIdx hj
  simpa using h

/-- If a step is excluded before the executed horizon, its actual coupling is at most tau
 times its saved raw norm. Zero coupling and an immediately inadmissible first step are included. -/
theorem beta_le_of_reorthSteps_lt (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ)
    (h : reorthSteps τ ν β q < q) :
    β (reorthSteps τ ν β q + 1) ≤ τ * ν (reorthSteps τ ν β q) := by
  classical
  rw [reorthSteps_eq_findIdx] at h ⊢
  have hf := List.findIdx_getElem
    (xs := List.range q) (p := fun j => !(τ * ν j < β (j + 1)))
    (w := by simpa only [List.length_range] using h)
  simpa using hf

end NLAlib
