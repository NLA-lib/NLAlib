/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.SweepExact
public import NLAlib.Krylov.Lanczos.Normalization

/-!
# Exact classical sweeps and the existing reorthogonalized step

The program's two pass witnesses and its guarded normalization relation identify the next
pure recurrence state. This bridge uses actual decoded words, including the zero-residual
case, and does not require a Hermitian matrix or a nonbreakdown premise.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.TwoPassOut.next_eq`: the normalized result is the old step.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

private theorem cgsProject_congr_basis {n k : ℕ} {Q Q' : ℕ → Fin n → ℝ}
    (hQ : ∀ j < k, Q j = Q' j) (w : Fin n → ℝ) : cgsProject Q k w = cgsProject Q' k w := by
  unfold cgsProject
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [hQ j (Finset.mem_range.mp hj)]

/-- A pair of exact classical pass witnesses followed by the certified guarded normalization
computes the current vector and coupling coefficient of the old pure reorthogonalized step. -/
theorem TwoPassOut.next_eq {K : Type} [Inhabited K] {dec : K → ℝ} {n j : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {s : LanczosReorthState ℝ (Fin n)}
    {qs raw reduced initial out : List K} {σ β₀ β : K}
    (hQ : ∀ l < j + 1, (fun i : Fin n => dec (vec qs (l * n + i))) = s.vecs l)
    (hraw : decv dec n raw = A *ᵥ s.cur - s.beta • s.prev -
      lanczosAlpha A s.toLanczosState • s.cur)
    (hp : TwoPassOut dec 0 0 n (j + 1) qs raw reduced)
    (hn : (normalizeRel dec n).rel [n] [reduced,[σ],initial,[β₀]] [] [out,[β]]) :
    decv dec n out = (lanczosReorthStep A j s).cur ∧
      dec β = (lanczosReorthStep A j s).beta := by
  have hred : decv dec n reduced = cgsProject s.vecs (j + 1)
      (cgsProject s.vecs (j + 1) (decv dec n raw)) := by
    rw [hp.project_eq, cgsProject_congr_basis hQ, cgsProject_congr_basis hQ]
  change decv dec n out = _ ∧ dec β = _ at hn
  simpa [lanczosReorthStep, hred, hraw] using hn

end NLAlib.Krylov.Lanczos.Reorth
