/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Isolated

/-!
# Linking a stored operand in any isolated buffer

A total word proof for a source tree transfers to the tree with forwarded context operands. The
isolated buffers are those satisfying a predicate `C`. The context operands are in isolated
buffers; the ordinary capabilities of the source tree avoid them. No order between the buffers
is assumed.

## Main results

* `NLAlib.Ops.eval_sim_of_isolated`: same-memory interpreter refinement.
* `NLAlib.Ops.eval_guardIsolated`: guarded proofs transfer to their delegated interpretation.
* `NLAlib.Ops.Wp.linkContext_of_isolated`: reuse a total word proof after forwarding.
-/

@[expose] public section

namespace NLAlib.Ops

section Transfer

variable {K Op Tst : Type} {source target : Interp Op Tst K}
  {C : ℕ → Prop} {reference : Store K} {τ : Tape K}

private def IsolatedTransfer (source target : Interp Op Tst K) (C : ℕ → Prop)
    (reference : Store K) (τ : Tape K) (s : Stmt Op Tst) : Prop :=
  ∀ ρ m m', m.Isolated C reference → ρ.Avoids C →
    eval source τ s ρ m = some m' →
      eval target τ s ρ m = some m' ∧ m'.Isolated C reference

private theorem isolated_while {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} (hTest : source.test = target.test)
    (hbody : IsolatedTransfer source target C reference τ body)
    (hk : IsolatedTransfer source target C reference τ k) :
    IsolatedTransfer source target C reference τ (.whileFuel fuel q ds ins body k) := by
  intro ρ m m' hSnapshot hEnv hr
  obtain ⟨N, hN, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨loopResult, hLoop, hr⟩ := Option.bind_eq_some_iff.mp hr
  let ts := fun i μ => (source.testAt q ds ins (ρ.pushIdx i) μ).map fun b => (b, μ)
  let tt := fun i μ => (target.testAt q ds ins (ρ.pushIdx i) μ).map fun b => (b, μ)
  let bs := fun i => eval source τ body (ρ.pushIdx i)
  let bt := fun i => eval target τ body (ρ.pushIdx i)
  have ht i a b (ha : a.Isolated C reference) (htest : ts i a = some b) :
      tt i a = some b ∧ b.2.Isolated C reference := by
    have he : tt i a = ts i a := by simp only [tt, ts, Interp.testAt, hTest]
    obtain ⟨flag, _, rfl⟩ := Option.map_eq_some_iff.mp htest
    exact ⟨he.trans htest, ha⟩
  have hb i a b (ha : a.Isolated C reference) (hbodyRun : bs i a = some b) :
      bt i a = some b ∧ b.Isolated C reference :=
    hbody _ _ _ ha (hEnv.pushIdx i) hbodyRun
  obtain ⟨hTarget, hSnapshot'⟩ := whileIter_sim_of_invariant
    (fun μ : Mem K => μ.Isolated C reference) tt ts bt bs ht hb hSnapshot hLoop
  obtain ⟨hkTarget, hFinal⟩ := hk _ _ _ hSnapshot' (hEnv.pushIdx loopResult.1) hr
  dsimp only [tt, bt] at hTarget
  exact ⟨by simp only [eval, hN, Option.bind_some, hTarget, hkTarget], hFinal⟩

/-- Successful source execution transfers through local call refinement. The callback is
one primitive-call law, not a whole-program correctness or success assumption. Public stored
algorithm certificates derive it from their declared block contracts and raw data. The
isolated buffers are those satisfying `C`; no buffer order is assumed. -/
theorem eval_sim_of_isolated
    (hCall : ∀ o d ins outs τ m m', m.Isolated C reference →
      (∀ z ∈ outs, ¬ C z.1) → source.callS o d ins outs τ m = some m' →
      target.callS o d ins outs τ m = some m' ∧ m'.Isolated C reference)
    (hTest : source.test = target.test) (hIndex : source.index = target.index)
    {s : Stmt Op Tst} {ρ : Env} {m m' : Mem K}
    (hSnapshot : m.Isolated C reference) (hEnv : ρ.Avoids C)
    (hr : eval source τ s ρ m = some m') :
    eval target τ s ρ m = some m' ∧ m'.Isolated C reference := by
  suffices h : IsolatedTransfer source target C reference τ s from h ρ m m' hSnapshot hEnv hr
  clear hSnapshot hEnv hr ρ m m'
  induction s with
  | skip => intro ρ m m' hp _ hr; cases hr; exact ⟨rfl, hp⟩
  | abort => intro ρ m m' _ _ hr; cases hr
  | call o ds ins outs =>
    intro ρ m m' hp hEnv hr
    obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨ht, hp'⟩ := hCall o d a b τ m m' hp (Operand.avoids_of_evalList hEnv hb) hr
    exact ⟨by simp only [eval, hd, ha, hb, Option.bind_some, ht], hp'⟩
  | seq s t ihs iht =>
    intro ρ m m' hp he hr
    obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hvt, hpv⟩ := ihs _ _ _ hp he hv
    obtain ⟨hrt, hpr⟩ := iht _ _ _ hpv he hr
    exact ⟨by simp only [eval, hvt, Option.bind_some, hrt], hpr⟩
  | ite q ds ins t e iht ihe =>
    intro ρ m m' hp he hr
    obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨flag, hq, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hqt : target.test q d a m = some flag := by rw [← hTest]; exact hq
    cases flag with
    | false =>
      obtain ⟨hrt, hpr⟩ := ihe _ _ _ hp he hr
      exact ⟨by simpa only [eval, hd, ha, hqt, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte] using hrt, hpr⟩
    | true =>
      obtain ⟨hrt, hpr⟩ := iht _ _ _ hp he hr
      exact ⟨by simpa only [eval, hd, ha, hqt, Option.bind_some, ↓reduceIte] using hrt, hpr⟩
  | frame ds args body ih =>
    intro ρ m m' hp he hr
    obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    split_ifs at hr with hl
    obtain ⟨ht, hp'⟩ := ih _ _ _ hp (Env.Avoids.frame (Operand.avoids_of_evalList he ha) d) hr
    exact ⟨by simp only [eval, hd, ha, Option.bind_some, if_pos hl, ht], hp'⟩
  | note _ _ ih => intro ρ m m' hp he hr; exact ih ρ m m' hp he hr
  | loop n body ih =>
    intro ρ m m' hp he hr
    obtain ⟨N, hN, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hs i a b (ha : a.Isolated C reference) (hr : eval source τ body
        (ρ.pushIdx i) a = some b) := ih _ _ _ ha (he.pushIdx i) hr
    obtain ⟨ht, hp'⟩ := iter_sim_of_invariant
      (fun μ : Mem K => μ.Isolated C reference) _ _ hs hp hr
    exact ⟨by simp only [eval, hN, Option.bind_some, ht], hp'⟩
  | whileFuel fuel q ds ins body k ih ihk => exact isolated_while hTest ih ihk
  | bindIdx q ins bound body ih =>
    intro ρ m m' hp he hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨B, hB, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
    split_ifs at hr with hBound
    obtain ⟨ht, hp'⟩ := ih _ _ _ hp (he.pushIdx v) hr
    have hvt : target.index q a m = some v := by rw [← hIndex]; exact hv
    exact ⟨by simp only [eval, ha, hB, hvt, Option.bind_some, if_pos hBound, ht], hp'⟩
  | allocAs fmt len body ih =>
    intro ρ m m' hp he hr
    obtain ⟨n, hn, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨ht, hpv⟩ := ih _ _ _ (hp.push n) (he.pushBuf fun hc => Nat.lt_irrefl _ (hp.1 _ hc)) hv
    have hlen : v.store.length = m.store.length + 1 := by
      rw [Store.length_eq_of_shape (shape_store_of_run hv), Store.length_push]
    exact ⟨by simp only [eval, hn, Option.bind_some, ht, Option.map_some],
      hpv.pop hp.1 hlen⟩

end Transfer

section Link

variable {K Op Lo Tst : Type}

/-- A successful guarded source run delegates every executed primitive and preserves the
isolated buffers. Its premises are local block contracts, not a whole-run simulation law. -/
theorem eval_guardIsolated (active fallback : Interp Op Tst K)
    (relations : Op → BlockRel K)
    (adm : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (C : ℕ → Prop) (reference : Store K)
    (hSat : ∀ o, (active.guardIsolated (fun o => (relations o).spec (adm o))
      (Mem.Isolated C reference) C fallback).Satisfies .total o
        ((relations o).spec (adm o)))
    {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m m' : Mem K}
    (hSnapshot : m.Isolated C reference) (hEnv : ρ.Avoids C)
    (hr : eval (active.guardIsolated (fun o => (relations o).spec (adm o))
      (Mem.Isolated C reference) C fallback) τ s ρ m = some m') :
    eval active τ s ρ m = some m' ∧ m'.Isolated C reference := by
  refine eval_sim_of_isolated
    (source := active.guardIsolated (fun o => (relations o).spec (adm o))
      (Mem.Isolated C reference) C fallback)
    (target := active) ?_ rfl rfl hSnapshot hEnv hr
  intro o d ins outs tape mem mem' hGood hOut hRun
  have hActive := Interp.callS_guardIsolated_of_good hGood hOut hRun
  obtain ⟨v, hv, hPost⟩ := (hSat o).callS d ins outs tape mem hActive.1
  rw [hRun] at hv
  cases hv
  exact ⟨hActive.2, BlockRel.isolated_of_post hGood hOut hPost⟩

/-- A total source word proof certifies the actual context-forwarded tree. Public stored
algorithm constructors instantiate the source laws from raw data and primitive contracts;
no desired output, successful execution or simulation callback is an input assumption. -/
theorem Wp.linkContext_of_isolated (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (relations : Op → BlockRel K)
    (adm : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (fallback : Interp Op Tst K) (C : ℕ → Prop) (reference : Store K)
    (hSat : ∀ o, ((I.linkContext T context).guardIsolated
      (fun o => (relations o).spec (adm o)) (Mem.Isolated C reference) C
      fallback).Satisfies .total o ((relations o).spec (adm o)))
    {slot : ℕ} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {Q : Mem K → Prop}
    (hslot : slot ≤ ρ.idx.length) (hSnapshot : m.Isolated C reference)
    (hEnv : ρ.Avoids C) (hContext : ∀ z ∈ context, C z.1)
    (hWord : Wp .total ((I.linkContext T context).guardIsolated
      (fun o => (relations o).spec (adm o)) (Mem.Isolated C reference) C
      fallback) τ s ρ Q m) :
    Wp .total I τ (s.linkContext context.length slot T) (ρ.withContext context slot) Q m := by
  obtain ⟨out, hr, hQ⟩ := hWord
  have hActual := eval_guardIsolated (I.linkContext T context) fallback relations adm
    C reference hSat hSnapshot hEnv hr
  exact ⟨out, (run_linkContext I T context slot τ s ρ m hslot
    (hSnapshot.live hContext)).trans hActual.1, hQ⟩

end Link

end NLAlib.Ops
