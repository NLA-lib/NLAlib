/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Solve
public import NLAlib.Ops.Profiles.ContextLinear
public import NLAlib.Ops.Logic.ContextLink

/-!
# Stored dense Reorth execution

The uniform context transformation forwards actual raw matrix data to scalar matvec loops.
The existing numerical recurrence proof supplies totality; no execution callback is assumed.

## Main results

* `NLAlib.Krylov.CG.Reorth.stored_solve_wp`: the total stored dense solver.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

/-- The transformed solver returns the existing exact recurrence at convergence or the cap.
Positive definiteness is an explicit property of the decoded raw matrix. -/
theorem stored_solve_wp
    {I : Interp RCLikeBlas.Operation CmpTst ℝ} {n cap cutoff : ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ} {B X R P : ℕ × ℕ} {bs xs : List ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, X, R, P], cutoff ≤ z.1)
    (hPos : (StoredOperator.denseMatrix n n raw).PosDef)
    (hBX : B.1 ≠ X.1) (hBR : B.1 ≠ R.1) (hBP : B.1 ≠ P.1)
    (hXR : X.1 ≠ R.1) (hXP : X.1 ≠ P.1) (hRP : R.1 ≠ P.1)
    (hl : μ.Live [B, X, R, P]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hx : μ.store.readBlock X.1 X.2 n = some xs) (hz : μ.Room [X, R, P] [n, n, n]) :
    Wp .total I τ
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext context.length 2
        (ContextLinear.table context.length index))
      ((Env.frame [n, cap] [B, X, X, R, P]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧ HSCG.StoresState id n X R P
        (cgState (StoredOperator.denseMatrix n n raw) (decv id n bs) (decv id n xs)
          (min cap (krylovGrade (StoredOperator.denseMatrix n n raw)
            (decv id n bs - StoredOperator.denseMatrix n n raw *ᵥ decv id n xs)))) μ') μ := by
  obtain ⟨hs, hb', ha, hc⟩ := ContextLinear.guarded_laws hS hB hCmp
    context index μ.store raw hContext hData
  apply Wp.linkContext_of_guarded I _ context (ContextLinear.relation _)
    (ContextLinear.admissible n) _ cutoff μ.store
    (ContextLinear.guarded_meets hS hB context index μ.store raw hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame (by
      intro z hz
      apply hAbove z
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
      tauto) _) hContext
  exact (solve_writes hs RCLikeBlas.exactModel_real hb' ha hc hPos
    hBX hBR hBP hXR hXP hRP hl hb hx hz).wp (fun _ _ h => h)

end NLAlib.Krylov.CG.Reorth
