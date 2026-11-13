/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ContextSemantics
public import NLAlib.Ops.ContextIteration
public import NLAlib.Ops.Frame

/-!
# Whole-program semantics of context forwarding

Explicit context forwarding preserves the exact memory result of the induced source
interpretation. The result includes failure and every allocation, frame, bounded loop and
early-exit loop. Only live context handles and a valid index insertion slot are required.
No read-only data assumption or numerical algorithm property enters this language theorem.

## Main results

* `NLAlib.Ops.run_linkContext`: exact fixed-tree context linking.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Lo Tst K : Type}

/-- Handles live before a successful statement remain live afterwards. -/
theorem Mem.Live.of_eval {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst}
    {ρ : Env} {m m' : Mem K} {as : List (ℕ × ℕ)} (h : m.Live as)
    (hr : eval I τ s ρ m = some m') : m'.Live as :=
  h.congr (Store.length_eq_of_shape (shape_store_of_run hr))

private def ContextRunEq (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (τ : Tape K) (s : Stmt Op Tst) : Prop :=
  ∀ slot ρ m, slot ≤ ρ.idx.length → m.Live context →
    eval I τ (s.linkContext context.length slot T) (ρ.withContext context slot) m =
      eval (I.linkContext T context) τ s ρ m

private theorem context_frame (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (τ : Tape K) {ds : List IExp} {args : List Operand}
    {body : Stmt Op Tst} (hbody : ContextRunEq I T context τ body) :
    ContextRunEq I T context τ (.frame ds args body) := by
  intro slot ρ m hslot hLive
  simp only [Stmt.linkContext, eval, IExp.evalList_withContext ds context slot ρ hslot,
    Operand.evalList_append, evalList_contextOperands context slot ρ hslot,
    Operand.evalList_liftContext context slot ρ args hslot, Option.bind_some]
  cases hd : IExp.evalList ρ.idx ds with
  | none => rfl
  | some d =>
    simp only [Option.bind_some]
    cases ha : Operand.evalList ρ args with
    | none => rfl
    | some a =>
      simp only [Option.map_some, Option.bind_some]
      by_cases hl : m.Live a
      · rw [if_pos ((Mem.live_append m context a).mpr ⟨hLive, hl⟩), if_pos hl]
        have he := hbody d.length (Env.frame d a) m (by simp [Env.frame]) hLive
        rw [Env.withContext_frame] at he
        simpa only [IExp.length_of_evalList hd] using he
      · rw [if_neg (fun h => hl ((Mem.live_append m context a).mp h).2), if_neg hl]

private theorem context_loop (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (τ : Tape K) {n : IExp} {body : Stmt Op Tst}
    (hbody : ContextRunEq I T context τ body) :
    ContextRunEq I T context τ (.loop n body) := by
  intro slot ρ m hslot hLive
  simp only [Stmt.linkContext, eval, IExp.eval_withContext n context slot ρ hslot]
  cases hn : n.eval ρ.idx with
  | none => rfl
  | some N =>
    refine iter_congr_of_invariant (fun μ : Mem K => μ.Live context) _ _ ?_ ?_ N m hLive
    · intro i μ hμ
      have hs : slot ≤ (ρ.pushIdx i).idx.length := by simp [Env.pushIdx]; omega
      simpa only [Env.withContext_pushIdx context slot ρ i hslot] using
        hbody slot (ρ.pushIdx i) μ hs hμ
    · intro i a b ha hr
      exact ha.of_eval hr

private theorem context_while (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (τ : Tape K) {fuel : IExp} {q : Tst}
    {ds : List IExp} {ins : List Operand} {body k : Stmt Op Tst}
    (hbody : ContextRunEq I T context τ body) (hk : ContextRunEq I T context τ k) :
    ContextRunEq I T context τ (.whileFuel fuel q ds ins body k) := by
  intro slot ρ m hslot hLive
  let J := I.linkContext T context
  let ts := fun i μ => (J.testAt q ds ins (ρ.pushIdx i) μ).map fun b => (b, μ)
  let tt := fun i μ => (I.testAt q (ds.map (IExp.liftContext context.length slot))
    (ins.map (Operand.liftContext context.length slot))
    ((ρ.withContext context slot).pushIdx i) μ).map fun b => (b, μ)
  let bs := fun i => eval J τ body (ρ.pushIdx i)
  let bt := fun i => eval I τ (body.linkContext context.length slot T)
    ((ρ.withContext context slot).pushIdx i)
  have hs i : slot ≤ (ρ.pushIdx i).idx.length := by simp [Env.pushIdx]; omega
  have ht i μ : tt i μ = ts i μ := by
    dsimp only [tt, ts, J]
    rw [← Env.withContext_pushIdx context slot ρ i hslot,
      Interp.testAt_linkContext I T context slot q ds ins (ρ.pushIdx i) μ (hs i)]
  have hb i μ (hμ : μ.Live context) : bt i μ = bs i μ := by
    simpa only [bt, bs, J, Env.withContext_pushIdx context slot ρ i hslot] using
      hbody slot (ρ.pushIdx i) μ (hs i) hμ
  have hkt i a b (ha : a.Live context) (hr : ts i a = some b) : b.2.Live context := by
    obtain ⟨flag, _, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ha
  have hkb i a b (ha : a.Live context) (hr : bs i a = some b) : b.Live context := ha.of_eval hr
  have hw N := whileIter_congr_of_invariant (fun μ : Mem K => μ.Live context)
    tt ts bt bs (fun i μ _ => ht i μ) hb hkt hkb N 0 m hLive
  simp only [Stmt.linkContext, eval, IExp.eval_withContext fuel context slot ρ hslot]
  cases hf : fuel.eval ρ.idx with
  | none => rfl
  | some N =>
    simp only [Option.bind_some]
    rw [hw N]
    cases hr : whileIter ts bs N 0 m with
    | none => rfl
    | some result =>
      have hl := whileIter_preserves hkt hkb hLive hr
      simpa only [Option.bind_some, Env.withContext_pushIdx context slot ρ result.1 hslot] using
        hk slot (ρ.pushIdx result.1) result.2 (hs result.1) hl

/-- Exact semantics of context forwarding for every statement, including failure.
The additional operands are explicit in the target tree and cannot be used by shifted queries. -/
theorem run_linkContext (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (slot : ℕ) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (m : Mem K)
    (hslot : slot ≤ ρ.idx.length) (hLive : m.Live context) :
    eval I τ (s.linkContext context.length slot T) (ρ.withContext context slot) m =
      eval (I.linkContext T context) τ s ρ m := by
  suffices h : ContextRunEq I T context τ s from h slot ρ m hslot hLive
  clear hslot hLive ρ m slot
  induction s with
  | skip => intro _ _ _ _ _; rfl
  | abort => intro _ _ _ _ _; rfl
  | call o ds ins outs => exact fun slot ρ m hs hl =>
      run_linkContext_call I T context slot τ o ds ins outs ρ m hs hl
  | seq s t ihs iht =>
    intro slot ρ m hs hl
    simp only [Stmt.linkContext, eval, ihs slot ρ m hs hl]
    cases hr : eval (I.linkContext T context) τ s ρ m with
    | none => rfl
    | some a => exact iht slot ρ a hs (hl.of_eval hr)
  | ite q ds ins t e iht ihe =>
    intro slot ρ m hs hl
    simp only [Stmt.linkContext, eval, IExp.evalList_withContext ds context slot ρ hs,
      Operand.evalList_liftContext context slot ρ ins hs, Interp.linkContext,
      iht slot ρ m hs hl, ihe slot ρ m hs hl]
  | frame ds args body ih => exact context_frame I T context τ ih
  | loop n body ih => exact context_loop I T context τ ih
  | whileFuel fuel q ds ins body k ih ihk => exact context_while I T context τ ih ihk
  | bindIdx q ins bound body ih =>
    intro slot ρ m hs hl
    have hb v : slot ≤ (ρ.pushIdx v).idx.length := by simp [Env.pushIdx]; omega
    have he v := ih slot (ρ.pushIdx v) m (hb v) hl
    simp only [Env.withContext_pushIdx context slot ρ _ hs] at he
    simp only [Stmt.linkContext, eval, IExp.eval_withContext bound context slot ρ hs,
      Operand.evalList_liftContext context slot ρ ins hs, Interp.linkContext, he]
  | allocAs fmt len body ih =>
    intro slot ρ m hs hl
    simp only [Stmt.linkContext, eval, IExp.eval_withContext len context slot ρ hs]
    cases hn : len.eval ρ.idx with
    | none => rfl
    | some n =>
      simp only [Option.bind_some]
      have hl' : (Mem.mk (m.store.push n) m.pos).Live context := by
        intro z hz
        have := hl z hz
        simpa only [Store.length_push] using Nat.lt_succ_of_lt this
      have he := ih slot (ρ.pushBuf m.store.length) ⟨m.store.push n, m.pos⟩ hs hl'
      simp only [Env.withContext_pushBuf] at he
      rw [he]

end NLAlib.Ops
