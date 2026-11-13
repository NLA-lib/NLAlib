/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Spec
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence

/-!
# Exact packed output of fully reorthogonalized Lanczos

The output refers to the old pure recurrence for every real matrix. For Hermitian matrices,
its ordinary coefficient prefix and basis agree with the existing canonical Lanczos output.
The final segment stores the norm before each pair of classical passes.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Output` specifies the complete packed output.
* `NLAlib.Krylov.Lanczos.Reorth.Output.toOrdinary` gives canonical Hermitian output.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

/-- The full exact output, including preorthogonalization norms in the coefficient suffix. -/
structure Output {K : Type} [Inhabited K] (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (cap : ℕ) (vs cs : List K) : Prop where
  /-- Current vectors through the cap, including zero tails after breakdown. -/
  basis : ∀ j ≤ cap, ∀ i : Fin n,
    dec (vec vs (j * n + i)) = (lanczosReorthState A b j).cur i
  /-- The diagonal coefficients are computed before the two classical passes. -/
  alpha : ∀ j < cap,
    dec (vec cs j) = lanczosAlpha A (lanczosReorthState A b j).toLanczosState
  /-- Coupling coefficients include the initial zero. -/
  beta : ∀ j ≤ cap, dec (vec cs (cap + j)) = (lanczosReorthState A b j).beta
  /-- Initial normalization uses the Euclidean input norm. -/
  inputNorm : dec (vec cs (2 * cap + 1)) = ‖WithLp.toLp 2 b‖
  /-- Extra coefficients are the raw residual norms before orthogonalization. -/
  nu : ∀ j < cap, dec (vec cs (2 * cap + 2 + j)) = (lanczosReorthState A b (j+1)).nu

/-- Hermitian exact full reorthogonalization preserves the ordinary Lanczos output, at every
cap and including early breakdown. -/
theorem Output.toOrdinary {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) :
    Lanczos.Output dec A b cap vs cs := by
  refine ⟨?_, ?_, ?_, h.inputNorm⟩
  · intro j hj i
    exact (h.basis j hj i).trans (congrFun (congrArg LanczosState.cur
      (hA.lanczosReorthState_toLanczosState b j).1) i)
  · intro j hj
    rw [h.alpha j hj, (hA.lanczosReorthState_toLanczosState b j).1]
  · intro j hj
    exact (h.beta j hj).trans (congrArg LanczosState.beta
      (hA.lanczosReorthState_toLanczosState b j).1)

/-- Zero current vector and zero coupling propagate through the full classical sweeps. -/
theorem step_cur_beta_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : ℕ) (s : LanczosReorthState ℝ (Fin n)) (hc : s.cur = 0) (hb : s.beta = 0) :
    (lanczosReorthStep A j s).cur = 0 ∧ (lanczosReorthStep A j s).beta = 0 := by
  simp [lanczosReorthStep, lanczosAlpha, LanczosReorthState.toLanczosState, hc, hb,
    cgsProject]

/-- Once breakdown occurs, every later basis vector and coupling is zero. No Hermitian or
nonbreakdown premise is needed to justify preinitialized zero tails. -/
theorem state_cur_beta_zero_of_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    {i j : ℕ} (hij : i ≤ j) (hc : (lanczosReorthState A b i).cur = 0)
    (hb : (lanczosReorthState A b i).beta = 0) :
    (lanczosReorthState A b j).cur = 0 ∧ (lanczosReorthState A b j).beta = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simpa using And.intro hc hb
  | succ k ih => exact step_cur_beta_zero A (i+k) _ ih.1 ih.2

end NLAlib.Krylov.Lanczos.Reorth
