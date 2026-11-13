/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.WeightedCost

/-!
# Weighted accounting on ordinary loop invariants

The word-level step uses the same footprint and mathematical invariant as `writes_loop`.
A separate per-round estimate bounds actual counted instructions. The shared rule combines
them on one execution, retaining the word proof's total correctness and frame.

## Main results

* `NLAlib.Ops.writes_loop_weighted`: total loop execution with invariant-sensitive weights.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- An ordinary total WP applies to the memory of any actual counted execution of that
same statement. This observation lets resource proofs reuse mathematical word invariants. -/
theorem Wp.post_of_evalCounted {I : Interp Op Tst K} {τ : Tape K} {W : Op → List ℕ → ℕ}
    {s : Stmt Op Tst} {ρ : Env} {Q : Mem K → Prop} {a b : St Op Tst K}
    (h : Wp .total I τ s ρ Q a.mem) (hr : evalCounted I W τ s ρ a = some b) : Q b.mem := by
  obtain ⟨m', hm', hQ⟩ := h
  have he := Option.some.inj (hm'.symm.trans (run_of_exec hr))
  exact he ▸ hQ

/-- The weighted invariant rule on an existing counted loop, starting from any prior count,
live scratch and peak. Its frame and mathematical state use the ordinary word-level proof;
only the weighted count increment is accumulated. -/
theorem evalCounted_loop_weight_of_writes {I : Interp Op Tst K} {τ : Tape K}
    {W : Op → List ℕ → ℕ} {ρ : Env} {a b : St Op Tst K}
    {n : IExp} {N : ℕ} {body : Stmt Op Tst}
    (hn : n.eval ρ.idx = some N) (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1))
    (P : ℕ → Mem K → Prop) (h0 : P 0 a.mem)
    (hstep : ∀ i < N, ∀ m', a.mem.store.EqOff (F i) m'.store → P i m' →
      Writes .total I τ body (ρ.pushIdx i) (F (i + 1)) (P (i + 1)) m')
    (weight : Count Op Tst →+ ℕ) (w : ℕ → ℕ)
    (hweight : ∀ i < N, ∀ x y : St Op Tst K,
      a.mem.store.EqOff (F i) x.mem.store → P i x.mem →
      evalCounted I W τ body (ρ.pushIdx i) x = some y →
        weight y.cost ≤ weight x.cost + w i)
    (hr : evalCounted I W τ (.loop n body) ρ a = some b) :
    weight b.cost ≤ weight a.cost + ∑ i ∈ Finset.range N, w i ∧
      a.mem.store.EqOff (F N) b.mem.store ∧ P N b.mem := by
  have hi : iter (fun i => evalCounted I W τ body (ρ.pushIdx i)) N a = some b := by
    simpa only [evalCounted, hn, Option.bind_some] using hr
  have hb := iter_weight_le_of_invariant_upto
    (P := fun i x => a.mem.store.EqOff (F i) x.mem.store ∧ P i x.mem)
    (weight := weight) (w := w) (fun i hiN x y hx hxy => ?_)
    ⟨Store.EqOff.refl _ _, h0⟩ hi
  · exact ⟨hb.2, hb.1⟩
  · have hpost := (hstep i hiN x.mem hx.1 hx.2).post_of_evalCounted hxy
    exact ⟨⟨(hx.1.mono (hF i hiN)).trans hpost.1, hpost.2⟩,
      hweight i hiN x y hx.1 hx.2 hxy⟩

/-- The same footprint and mathematical invariant as the ordinary total loop rule,
augmented with bounds on actual per-round weighted counts. The result guarantees execution,
its final word invariant/frame, and the sum of the per-round costs on that execution. -/
theorem writes_loop_weighted {I : Interp Op Tst K} {τ : Tape K} {W : Op → List ℕ → ℕ}
    {ρ : Env} {m : Mem K} {n : IExp} {N : ℕ} {body : Stmt Op Tst}
    (hn : n.eval ρ.idx = some N) (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1))
    (P : ℕ → Mem K → Prop) (h0 : P 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → P i m' →
      Writes .total I τ body (ρ.pushIdx i) (F (i + 1)) (P (i + 1)) m')
    (weight : Count Op Tst →+ ℕ) (w : ℕ → ℕ)
    (hweight : ∀ i < N, ∀ a b : St Op Tst K, m.store.EqOff (F i) a.mem.store → P i a.mem →
      evalCounted I W τ body (ρ.pushIdx i) a = some b →
        weight b.cost ≤ weight a.cost + w i) :
    ConditionalRunsW I W τ (.loop n body) ρ m (stmtPeak W (.loop n body) ρ.idx)
      (fun c m' => weight c ≤ ∑ i ∈ Finset.range N, w i ∧
        m.store.EqOff (F N) m'.store ∧ P N m') := by
  have ht := writes_loop (md := .total) hn F hF P h0 hstep
  obtain ⟨m', hr, hpost⟩ := ht
  obtain ⟨st, he, _, hp, _⟩ := ConditionalRuns.of_run
    (Q := fun m' => m.store.EqOff (F N) m'.store ∧ P N m') hr hpost W
  have hb := evalCounted_loop_weight_of_writes hn F hF P h0 hstep weight w hweight he
  refine ⟨st, he, hp, ?_, hb.2⟩
  simpa only [St.init, map_zero, Nat.zero_add] using hb.1

end NLAlib.Ops
