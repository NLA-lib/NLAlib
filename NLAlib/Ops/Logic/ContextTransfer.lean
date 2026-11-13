/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.ContextSnapshot

/-!
# Transferring guarded context proofs to actual execution

The reusable language rule transfers successful source steps through local primitive
contracts while protecting a raw context prefix. The guarded source is only a proof
device. Actual target execution contains no added precondition tests or fallback calls.

## Main results

* `NLAlib.Ops.eval_sim_of_contextSnapshot`: same-memory interpreter refinement.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} {source target : Interp Op Tst K}
  {cutoff : ℕ} {reference : Store K} {τ : Tape K}

private def SnapshotTransfer (source target : Interp Op Tst K) (cutoff : ℕ)
    (reference : Store K) (τ : Tape K) (s : Stmt Op Tst) : Prop :=
  ∀ ρ m m', m.ContextSnapshot cutoff reference → ρ.Above cutoff →
    eval source τ s ρ m = some m' →
      eval target τ s ρ m = some m' ∧ m'.ContextSnapshot cutoff reference

private theorem snapshot_while {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} (hTest : source.test = target.test)
    (hbody : SnapshotTransfer source target cutoff reference τ body)
    (hk : SnapshotTransfer source target cutoff reference τ k) :
    SnapshotTransfer source target cutoff reference τ (.whileFuel fuel q ds ins body k) := by
  intro ρ m m' hSnapshot hEnv hr
  obtain ⟨N, hN, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨loopResult, hLoop, hr⟩ := Option.bind_eq_some_iff.mp hr
  let ts := fun i μ => (source.testAt q ds ins (ρ.pushIdx i) μ).map fun b => (b, μ)
  let tt := fun i μ => (target.testAt q ds ins (ρ.pushIdx i) μ).map fun b => (b, μ)
  let bs := fun i => eval source τ body (ρ.pushIdx i)
  let bt := fun i => eval target τ body (ρ.pushIdx i)
  have ht i a b (ha : a.ContextSnapshot cutoff reference) (htest : ts i a = some b) :
      tt i a = some b ∧ b.2.ContextSnapshot cutoff reference := by
    have he : tt i a = ts i a := by simp only [tt, ts, Interp.testAt, hTest]
    obtain ⟨flag, _, rfl⟩ := Option.map_eq_some_iff.mp htest
    exact ⟨he.trans htest, ha⟩
  have hb i a b (ha : a.ContextSnapshot cutoff reference) (hbodyRun : bs i a = some b) :
      bt i a = some b ∧ b.ContextSnapshot cutoff reference :=
    hbody _ _ _ ha (hEnv.pushIdx i) hbodyRun
  obtain ⟨hTarget, hSnapshot'⟩ := whileIter_sim_of_invariant
    (fun μ : Mem K => μ.ContextSnapshot cutoff reference) tt ts bt bs ht hb hSnapshot hLoop
  obtain ⟨hkTarget, hFinal⟩ := hk _ _ _ hSnapshot' (hEnv.pushIdx loopResult.1) hr
  dsimp only [tt, bt] at hTarget
  exact ⟨by simp only [eval, hN, Option.bind_some, hTarget, hkTarget], hFinal⟩

/-- Successful source execution transfers through local call refinement. The callback is
one primitive-call law, not a whole-program correctness or success assumption. Public stored
algorithm certificates derive it from their declared block contracts and raw data. -/
theorem eval_sim_of_contextSnapshot
    (hCall : ∀ o d ins outs τ m m', m.ContextSnapshot cutoff reference →
      (∀ z ∈ outs, cutoff ≤ z.1) → source.callS o d ins outs τ m = some m' →
      target.callS o d ins outs τ m = some m' ∧ m'.ContextSnapshot cutoff reference)
    (hTest : source.test = target.test) (hIndex : source.index = target.index)
    {s : Stmt Op Tst} {ρ : Env} {m m' : Mem K}
    (hSnapshot : m.ContextSnapshot cutoff reference) (hEnv : ρ.Above cutoff)
    (hr : eval source τ s ρ m = some m') :
    eval target τ s ρ m = some m' ∧ m'.ContextSnapshot cutoff reference := by
  suffices h : SnapshotTransfer source target cutoff reference τ s from h ρ m m' hSnapshot hEnv hr
  clear hSnapshot hEnv hr ρ m m'
  induction s with
  | skip => intro ρ m m' hp _ hr; cases hr; exact ⟨rfl, hp⟩
  | abort => intro ρ m m' _ _ hr; cases hr
  | call o ds ins outs =>
    intro ρ m m' hp hEnv hr
    obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨ht, hp'⟩ := hCall o d a b τ m m' hp (Operand.above_of_evalList hEnv hb) hr
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
    obtain ⟨ht, hp'⟩ := ih _ _ _ hp (Env.Above.frame (Operand.above_of_evalList he ha) d) hr
    exact ⟨by simp only [eval, hd, ha, Option.bind_some, if_pos hl, ht], hp'⟩
  | loop n body ih =>
    intro ρ m m' hp he hr
    obtain ⟨N, hN, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hs i a b (ha : a.ContextSnapshot cutoff reference) (hr : eval source τ body
        (ρ.pushIdx i) a = some b) := ih _ _ _ ha (he.pushIdx i) hr
    obtain ⟨ht, hp'⟩ := iter_sim_of_invariant
      (fun μ : Mem K => μ.ContextSnapshot cutoff reference) _ _ hs hp hr
    exact ⟨by simp only [eval, hN, Option.bind_some, ht], hp'⟩
  | whileFuel fuel q ds ins body k ih ihk => exact snapshot_while hTest ih ihk
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
    obtain ⟨ht, hpv⟩ := ih _ _ _ (hp.push n) (he.pushBuf hp.1) hv
    have hlen : v.store.length = m.store.length + 1 := by
      rw [Store.length_eq_of_shape (shape_store_of_run hv), Store.length_push]
    exact ⟨by simp only [eval, hn, Option.bind_some, ht, Option.map_some],
      hpv.pop (by have := hp.1; omega)⟩

end NLAlib.Ops
