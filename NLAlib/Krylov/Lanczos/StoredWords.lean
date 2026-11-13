/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Exact
public import NLAlib.Krylov.Lanczos.Reorth.Exact
public import NLAlib.Ops.Profiles.ContextLinear
public import NLAlib.Ops.Logic.ContextLink

/-!
# Lanczos with an explicit stored dense matrix

The fixed context transformation exposes the matrix operand to every scalar matvec leaf.
Exact scalar and vector contracts suffice for total execution of the transformed ordinary
and reorthogonalized programs. Their mathematical outputs are the existing pure recurrences;
no source execution or simulation law is assumed by these word theorems.

## Main results

* `NLAlib.Krylov.Lanczos.stored_solve_wp`: ordinary stored dense Lanczos.
* `NLAlib.Krylov.Lanczos.Reorth.stored_solve_wp`: stored full reorthogonalization.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ} {n cap cutoff : ℕ}
  {τ : Tape ℝ} {μ : Mem ℝ} {B V C : ℕ × ℕ} {bs : List ℝ}

/-- The actual context-forwarded ordinary tree returns its exact pure recurrence on the
matrix decoded from declared raw words, including zero input, zero dimension and breakdown. -/
theorem stored_solve_wp
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, V, C], cutoff ≤ z.1)
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    Wp .total I τ
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext context.length 2
        (ContextLinear.table context.length index))
      ((Env.frame [n, cap] [B, V, C]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.length = μ.store.length ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output id (StoredOperator.denseMatrix n n raw) (decv id n bs) cap vs cs) μ := by
  obtain ⟨hs, hb', ha, hc⟩ := ContextLinear.guarded_laws hS hB hCmp
    context index μ.store raw hContext hData
  apply Wp.linkContext_of_guarded I _ context (ContextLinear.relation _)
    (ContextLinear.admissible n) _ cutoff μ.store
    (ContextLinear.guarded_meets hS hB context index μ.store raw hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame hAbove _) hContext
  exact (solve_writes hs RCLikeBlas.exactModel_real hb' trivial ha hc
    hBV hBC hVC hl hb hz).wp (fun _ hfr h => ⟨h.1, hfr.length_eq, h.2⟩)

namespace Reorth

/-- The actual stored reorthogonalized tree returns the exact two-pass recurrence. Matrix
symmetry is explicit; no full-rank or successful-execution assumption is needed. -/
theorem stored_solve_wp
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, V, C], cutoff ≤ z.1)
    (hAT : (StoredOperator.denseMatrix n n raw).IsHermitian)
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    Wp .total I τ
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext context.length 2
        (ContextLinear.table context.length index))
      ((Env.frame [n, cap] [B, V, C]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.length = μ.store.length ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output id (StoredOperator.denseMatrix n n raw) (decv id n bs) cap vs cs) μ := by
  obtain ⟨hs, hb', ha, hc⟩ := ContextLinear.guarded_laws hS hB hCmp
    context index μ.store raw hContext hData
  apply Wp.linkContext_of_guarded I _ context (ContextLinear.relation _)
    (ContextLinear.admissible n) _ cutoff μ.store
    (ContextLinear.guarded_meets hS hB context index μ.store raw hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame hAbove _) hContext
  exact (solve_writes hs RCLikeBlas.exactModel_real hb' trivial ha hc hAT
    hBV hBC hVC hl hb hz).wp (fun _ hfr h => ⟨h.1, hfr.length_eq, h.2⟩)

end Reorth
end NLAlib.Krylov.Lanczos
