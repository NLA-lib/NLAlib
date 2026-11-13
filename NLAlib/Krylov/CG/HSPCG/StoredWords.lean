/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Solve
public import NLAlib.Krylov.CG.HSPCG.StoredContext
public import NLAlib.Ops.Logic.ContextLink

/-!
# Stored dense preconditioned conjugate gradient

The uniform context transformation supplies both the system and inverse preconditioner as
explicit raw operands to scalar dense loops. The existing exact PCG recurrence proof applies
to the globally realized proof-side contracts without an execution assumption.

## Main results

* `NLAlib.Krylov.CG.HSPCG.stored_solve_wp`: total stored dense PCG execution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

/-- Positive-definite decoded system and inverse preconditioner matrices and an admitted
Krylov horizon ensure that the transformed program stores its exact PCG recurrence. -/
theorem stored_solve_wp
    {I : Interp RCLikeBlas.Operation CmpTst ℝ} {n cap cutoff : ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ} {B X R Z P : ℕ × ℕ} {bs xs : List ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    (rawA rawP : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) = some rawA)
    (hPrec : μ.store.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some rawP)
    (hAbove : ∀ z ∈ [B, X, R, Z, P], cutoff ≤ z.1)
    (hPos : (StoredOperator.denseMatrix n n rawA).PosDef)
    (hPPos : (StoredOperator.denseMatrix n n rawP).PosDef)
    (hBX : B.1 ≠ X.1) (hBR : B.1 ≠ R.1) (hBZ : B.1 ≠ Z.1) (hBP : B.1 ≠ P.1)
    (hXR : X.1 ≠ R.1) (hXZ : X.1 ≠ Z.1) (hXP : X.1 ≠ P.1)
    (hRZ : R.1 ≠ Z.1) (hRP : R.1 ≠ P.1) (hZP : Z.1 ≠ P.1)
    (hl : μ.Live [B, X, R, Z, P]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hx : μ.store.readBlock X.1 X.2 n = some xs)
    (hHorizon : cap ≤ krylovGrade
      (StoredOperator.denseMatrix n n rawP * StoredOperator.denseMatrix n n rawA)
      (StoredOperator.denseMatrix n n rawP *ᵥ
        (decv id n bs - StoredOperator.denseMatrix n n rawA *ᵥ decv id n xs)))
    (hz : μ.Room [X, R, Z, P] [n, n, n, n]) :
    Wp .total I τ
      ((solve (Op := Signature) (Tst := CmpTst)).linkContext context.length 2
        (StoredContext.table context.length systemIndex preconditionerIndex))
      ((Env.frame [n, cap] [B, X, X, R, Z, P]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧ StoresState id n X R Z P
        (pcgState (StoredOperator.denseMatrix n n rawA) (StoredOperator.denseMatrix n n rawP)
          (decv id n bs) (decv id n xs) cap) μ') μ := by
  obtain ⟨hs, hb', ha, hp⟩ := StoredContext.guarded_laws hS hB context
    systemIndex preconditionerIndex μ.store rawA rawP hContext hData hPrec
  apply Wp.linkContext_of_guarded I _ context (StoredContext.relation _ _)
    (StoredContext.admissible n) _ cutoff μ.store
    (StoredContext.guarded_meets hS hB context systemIndex preconditionerIndex
      μ.store rawA rawP hContext hData hPrec)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame (by
      intro z hz
      apply hAbove z
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
      tauto) _) hContext
  exact (solve_writes hs RCLikeBlas.exactModel_real hb' ha hp hPos hPPos
    hBX hBR hBZ hBP hXR hXZ hXP hRZ hRP hZP hl hb hx hHorizon hz).wp (fun _ _ h => h)

end NLAlib.Krylov.CG.HSPCG
