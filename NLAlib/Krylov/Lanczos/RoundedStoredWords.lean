/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedSolve
public import NLAlib.Krylov.Lanczos.Reorth.RoundedSolve
public import NLAlib.Ops.Profiles.ContextLinearRounded
public import NLAlib.Ops.Logic.ContextLink

/-!
# Rounded Lanczos with an explicit stored dense matrix

The actual context-forwarded tree executes scalar dense matrix products on the raw supplied
matrix. Total numerical word proofs transfer through local rounded kernel contracts, preserving
the actual packed basis and coefficient outputs. No successful source execution is assumed.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.stored_solve_wp`: ordinary rounded stored execution.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.stored_solve_wp`: rounded reorthogonalized execution.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.Lanczos

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ} {n cap cutoff : ℕ}
  {M : Machine ℝ} {u em E : ℝ} {e : Blas1Err} {ok : ℕ → Prop}
  {τ : Tape ℝ} {μ : Mem ℝ} {B V C : ℕ × ℕ} {bs : List ℝ}

namespace Rounded

/-- Local scalar/vector contracts and the actual dense word-kernel error imply total
ordinary rounded execution, including zero input, zero dimension and early breakdown. -/
theorem stored_solve_wp
    (hS : IsScalar M I) (hM : StdModel u id M) (hB : IsBlas1 id e ok I) (hok : ok n)
    (hCmp : IsCmp id I) (hprec : Precision em u E e n)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (herror : 0 ≤ em * specNorm (StoredOperator.denseMatrix n n raw))
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          em * specNorm (StoredOperator.denseMatrix n n raw) * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, V, C], cutoff ≤ z.1)
    (hAT : (StoredOperator.denseMatrix n n raw)ᵀ = StoredOperator.denseMatrix n n raw)
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
        Output id (StoredOperator.denseMatrix n n raw) (decv id n bs) E cap vs cs) μ := by
  obtain ⟨hs, hb', ha, hc⟩ := ContextLinearRounded.guarded_laws hS hB hCmp
    context index μ.store raw herror hError hContext hData
  apply Wp.linkContext_of_guarded I _ context
    (ContextLinearRounded.relation M e _ (em * specNorm _))
    (ContextLinearRounded.admissible ok n) _ cutoff μ.store
    (ContextLinearRounded.meets_guarded hS hB context index μ.store raw
      herror hError hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame hAbove _) hContext
  exact (solve_writes hs hM hb' hok ha hc hAT hprec hBV hBC hVC hl hb hz).wp
    (fun _ hfr h => ⟨h.1, hfr.length_eq, h.2⟩)

end Rounded

namespace Reorth.Rounded

/-- The same local rounded contracts imply total stored full reorthogonalization and its
actual packed history. No global orthogonality or future nonbreakdown premise is required. -/
theorem stored_solve_wp
    (hS : IsScalar M I) (hM : StdModel u id M) (hB : IsBlas1 id e ok I) (hok : ok n)
    (hCmp : IsCmp id I) (hprec : Lanczos.Rounded.Precision em u E e n)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (herror : 0 ≤ em * specNorm (StoredOperator.denseMatrix n n raw))
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          em * specNorm (StoredOperator.denseMatrix n n raw) * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, V, C], cutoff ≤ z.1)
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
        Output id (StoredOperator.denseMatrix n n raw) (decv id n bs)
          em u E e cap vs cs) μ := by
  obtain ⟨hs, hb', ha, hc⟩ := ContextLinearRounded.guarded_laws hS hB hCmp
    context index μ.store raw herror hError hContext hData
  apply Wp.linkContext_of_guarded I _ context
    (ContextLinearRounded.relation M e _ (em * specNorm _))
    (ContextLinearRounded.admissible ok n) _ cutoff μ.store
    (ContextLinearRounded.meets_guarded hS hB context index μ.store raw
      herror hError hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame hAbove _) hContext
  exact (solve_writes hs hM hb' hok ha hc hprec hBV hBC hVC hl hb hz).wp
    (fun _ hfr h => ⟨h.1, hfr.length_eq, h.2⟩)

end Reorth.Rounded
end NLAlib.Krylov.Lanczos
