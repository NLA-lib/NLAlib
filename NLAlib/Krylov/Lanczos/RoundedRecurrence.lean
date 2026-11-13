/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedState
public import NLAlib.Krylov.Processes.LanczosProgramRoundedRun

/-!
# Extending the same numerical run from rounded local defects

The existing pure one-step and append constructors consume the defects derived from actual
operations. Matvec, dot, both axpy updates and normalization are all included in the common
local error allowance. Only an active old coefficient permits extending a positive run.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.State.exists_run_next`: extend the archived numerical run.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

/-- Actual local defects extend the existing run while preserving its archived values.
The new last coefficient may be zero; an old terminal run cannot be extended. -/
theorem State.exists_run_next {K : Type} [Inhabited K] {dec : K → ℝ}
    {n cap done L : ℕ} {V C : ℕ × ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {rhs : Fin n → ℝ} {em u E : ℝ} {e : Blas1Err} {z : Values n} {s : Store K}
    (h : State dec A rhs E cap done V C L z s) (hAT : Aᵀ = A)
    (hp : Precision em u E e n)
    (hactive : (if done = 0 then z.initialNorm else z.beta done) ≠ 0)
    {first raw next : Fin n → ℝ} {a b : ℝ}
    (hb : UpdateBounds em (e.dot n) e.axpy A (z.v done) (z.v (done + 1)) first raw
      (z.beta done) a)
    (hn : ‖WithLp.toLp 2 (raw - b • next)‖ ≤ E * ‖WithLp.toLp 2 raw‖)
    (hbn : 0 ≤ b) (hunit : b ≠ 0 → |‖WithLp.toLp 2 next‖ ^ 2 - 1| ≤ E) :
    ∃ R : LanczosRun n (done + 1), R.H = A ∧ R.ε = E ∧
      R.v = (z.next done next a b).v ∧ R.α = (z.next done next a b).alpha ∧
      R.β = (z.next done next a b).beta := by
  obtain ⟨mv, hmv, hw, ha, hz⟩ := hb.normwise hp
  have hcur := h.abs_norm_sq_sub_one_le hactive
  rcases h.run with ⟨rfl, hv0, ha0, hb0⟩ | ⟨R, hH, hE, hv, hα, hβ⟩
  · have hw' : ‖WithLp.toLp 2 (mv - first)‖ ≤ E * ‖WithLp.toLp 2 mv‖ := by
      simpa only [hb0, Pi.zero_apply, zero_smul, sub_zero, abs_zero, zero_mul, add_zero] using hw
    obtain ⟨R, hH, hE, hv, hα, hβ⟩ := LanczosImplementation.exists_lanczosRun_one A hAT E
      hp.nonneg hp.small (z.v 1) mv first raw next a b hcur hmv hw' ha hz hn hbn hunit
    refine ⟨R, hH, hE, ?_, ?_, ?_⟩
    · exact hv.trans (congrArg (fun f => Function.update f 2 next) hv0).symm
    · exact hα.trans (congrArg (fun f => Function.update f 1 a) ha0).symm
    · exact hβ.trans (congrArg (fun f => Function.update f 1 b) hb0).symm
  · have hk : R.β done ≠ 0 := by
      rw [hβ]
      simpa only [if_neg (Nat.ne_of_gt R.k_pos)] using hactive
    obtain ⟨S, hH', hE', hv', hα', hβ'⟩ := LanczosImplementation.exists_lanczosRun_succ R
      mv first raw next a b hk
      (by simpa only [hH, hE, hv] using hmv)
      (by simpa only [hE, hv, hβ] using hw)
      (by simpa only [hE, hv] using ha)
      (by simpa only [hE, hv] using hz)
      (by simpa only [hE] using hn) hbn (by simpa only [hE] using hunit)
    refine ⟨S, hH'.trans hH, hE'.trans hE, ?_, ?_, ?_⟩
    · simpa only [Values.next, hv] using hv'
    · simpa only [Values.next, hα] using hα'
    · simpa only [Values.next, hβ] using hβ'

end NLAlib.Krylov.Lanczos.Rounded
