/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The zero tail of the Lanczos recurrence

A zero current vector coupled by zero beta has zero future basis vectors and coefficients.
This fact justifies successful early exit with preinitialized zero output tails, without an
execution-success or nonbreakdown premise.

## Main results

* `NLAlib.Krylov.Lanczos.lanczosStep_cur_beta_zero` propagates a stopped state.
* `NLAlib.Krylov.Lanczos.lanczosState_cur_beta_zero_of_le` propagates it to every later index.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- A zero current vector and zero coupling remain zero after a Lanczos step, independently
of the previous vector and matrix. [Paige1972, §2]. -/
theorem lanczosStep_cur_beta_zero (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n)
    (hc : s.cur = 0) (hb : s.beta = 0) :
    (lanczosStep A s).cur = 0 ∧ (lanczosStep A s).beta = 0 := by
  simp [lanczosStep, lanczosAlpha, hc, hb]

/-- After a zero-current, zero-beta state, all later current vectors and coupling coefficients
are zero. This supports stopping before further square roots and divisions. [Paige1972, §2]. -/
theorem lanczosState_cur_beta_zero_of_le (A : Matrix n n 𝕜) (b : n → 𝕜) {i j : ℕ}
    (hij : i ≤ j) (hc : (lanczosState A b i).cur = 0)
    (hb : (lanczosState A b i).beta = 0) :
    (lanczosState A b j).cur = 0 ∧ (lanczosState A b j).beta = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simpa using And.intro hc hb
  | succ k ih =>
    exact lanczosStep_cur_beta_zero A (lanczosState A b (i + k)) ih.1 ih.2

/-- A zero current vector makes the diagonal coefficient zero. [Paige1972, §2]. -/
theorem lanczosAlpha_eq_zero_of_cur_eq_zero (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n)
    (hc : s.cur = 0) : lanczosAlpha A s = 0 := by
  simp [lanczosAlpha, hc]

end NLAlib.Krylov.Lanczos
