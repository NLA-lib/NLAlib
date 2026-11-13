/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.ContextTransfer

/-!
# Total word proofs for explicitly contextualized programs

Global source laws are supplied by primitive contracts and a proof-side guarded
interpretation. Every successful source call in the protected context regime is its
actual delegated call. A total source word proof therefore certifies the explicitly
forwarded target program, with the identical final memory and no runtime guard or fallback.

## Main results

* `NLAlib.Ops.eval_guardContext`: guarded proofs transfer to their delegated interpretation.
* `NLAlib.Ops.Wp.linkContext_of_guarded`: reuse a total numerical word proof after forwarding.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Lo Tst : Type}

/-- A successful guarded source run delegates every executed primitive and preserves the
raw context snapshot. Its premises are local block contracts, not a whole-run simulation law. -/
theorem eval_guardContext (active fallback : Interp Op Tst K)
    (relations : Op → BlockRel K)
    (adm : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (cutoff : ℕ) (reference : Store K)
    (hMeets : ∀ o, (active.guardContext (fun o => (relations o).spec (adm o))
      (Mem.ContextSnapshot cutoff reference) cutoff fallback).Meets .total o
        ((relations o).spec (adm o)))
    {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m m' : Mem K}
    (hSnapshot : m.ContextSnapshot cutoff reference) (hEnv : ρ.Above cutoff)
    (hr : eval (active.guardContext (fun o => (relations o).spec (adm o))
      (Mem.ContextSnapshot cutoff reference) cutoff fallback) τ s ρ m = some m') :
    eval active τ s ρ m = some m' ∧ m'.ContextSnapshot cutoff reference := by
  refine eval_sim_of_contextSnapshot
    (source := active.guardContext (fun o => (relations o).spec (adm o))
      (Mem.ContextSnapshot cutoff reference) cutoff fallback)
    (target := active) ?_ rfl rfl hSnapshot hEnv hr
  intro o d ins outs tape mem mem' hGood hOut hRun
  have hActive := Interp.callS_guardContext_of_good hGood hOut hRun
  obtain ⟨v, hv, hPost⟩ := hMeets o d ins outs tape mem hActive.1
  rw [hRun] at hv
  cases hv
  exact ⟨hActive.2, BlockRel.contextSnapshot_of_post hGood hOut hPost⟩

/-- A total source word proof certifies the actual context-forwarded tree. Public stored
algorithm constructors instantiate the source laws from raw data and primitive contracts;
no desired output, successful execution or simulation callback is an input assumption. -/
theorem Wp.linkContext_of_guarded (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (relations : Op → BlockRel K)
    (adm : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (fallback : Interp Op Tst K) (cutoff : ℕ) (reference : Store K)
    (hMeets : ∀ o, ((I.linkContext T context).guardContext
      (fun o => (relations o).spec (adm o)) (Mem.ContextSnapshot cutoff reference)
      cutoff fallback).Meets .total o ((relations o).spec (adm o)))
    {slot : ℕ} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {Q : Mem K → Prop}
    (hslot : slot ≤ ρ.idx.length) (hSnapshot : m.ContextSnapshot cutoff reference)
    (hEnv : ρ.Above cutoff) (hContext : ∀ z ∈ context, z.1 < cutoff)
    (hWord : Wp .total ((I.linkContext T context).guardContext
      (fun o => (relations o).spec (adm o)) (Mem.ContextSnapshot cutoff reference)
      cutoff fallback) τ s ρ Q m) :
    Wp .total I τ (s.linkContext context.length slot T) (ρ.withContext context slot) Q m := by
  obtain ⟨out, hr, hQ⟩ := hWord
  have hActual := eval_guardContext (I.linkContext T context) fallback relations adm
    cutoff reference hMeets hSnapshot hEnv hr
  exact ⟨out, (run_linkContext I T context slot τ s ρ m hslot
    (hSnapshot.live hContext)).trans hActual.1, hQ⟩

end NLAlib.Ops
