/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public import NLAlib.Ops.Static

/-!
# The transfer theorems of linking

A theorem about an algorithm under every interpretation meeting contracts becomes a theorem about
the linked program, with no new proof about the algorithm.

* **Counts.** `NLAlib.Ops.Count.push κ` is the additive map sending one call of `o` at the
  dimensions `d` to `κ o d`; with `κ` the cost of each implementation it is the push-forward of
  the counts of the algorithm to the counts of the lower operations, and with a weight it is a
  weighted count (`NLAlib.Ops.Count.push_comp`: push-forwards compose, so towers and weights are
  evaluated).
* **The certificate** `NLAlib.Ops.Table.Accounts`: each implementation runs within the cost `κ`
  and the workspace declared for its operation. It follows from the static cost and workspace of
  the trees (`NLAlib.Ops.Table.accounts_of_static`) and says nothing of values.
* `NLAlib.Ops.exec_link`: the simulation. `NLAlib.Ops.Runs.link`, `NLAlib.Ops.link_total`: total
  correctness with counts pushed forward and the same workspace. `NLAlib.Ops.RunsL.link`,
  `NLAlib.Ops.link_liberal`: partial correctness, through the induced interpretation only.
  `NLAlib.Ops.exec_link_weight`: a weighted, data-dependent bound on the counts of one run.
  `NLAlib.Ops.fail_subset`: failure events, sample by sample.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ K : Type}

namespace Count

/-- **The push-forward of counts**: the additive map sending one use of `o` at `d` to `κ o d`. -/
noncomputable def push {A : Type} [AddCommMonoid A] (κ : Op → List ℕ → A) : Count Op →+ A :=
  Finsupp.liftAddHom fun k => (smulAddHom ℕ A).flip (κ k.1 k.2)

@[simp] theorem push_one {A : Type} [AddCommMonoid A] (κ : Op → List ℕ → A) (o : Op)
    (d : List ℕ) : push κ (Count.one o d) = κ o d := by
  simp [push, Count.one]

theorem push_single {A : Type} [AddCommMonoid A] (κ : Op → List ℕ → A) (k : Op × List ℕ)
    (n : ℕ) : push κ (Finsupp.single k n) = n • κ k.1 k.2 := by
  simp [push]

theorem push_mono {A : Type} [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A]
    (κ : Op → List ℕ → A) : Monotone (push κ) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := exists_add_of_le hab
  rw [map_add]
  exact le_self_add

/-- Push-forwards compose: the push-forward through a tower, or a weight of a push-forward, is
the push-forward of the composed cost of single calls. -/
theorem push_comp {A : Type} [AddCommMonoid A] (κ₁ : Op₁ → List ℕ → Count Op₂)
    (κ₂ : Op₂ → List ℕ → A) (c : Count Op₁) :
    push κ₂ (push κ₁ c) = push (fun o d => push κ₂ (κ₁ o d)) c := by
  have h : (push κ₂).comp (push κ₁) = push fun o d => push κ₂ (κ₁ o d) :=
    Finsupp.addHom_ext fun k n => by
      simp only [AddMonoidHom.comp_apply, push_single, map_nsmul]
  exact DFunLike.congr_fun h c

/-- A weighted count: one use of `o` at `d` weighs `w o d`. -/
noncomputable abbrev weight (w : Op → List ℕ → ℕ) : Count Op →+ ℕ := push w

end Count

/-- **The accounting certificate of a table**, for the lower interpretation `I` and workspaces
`W₂`: every successful run of an implementation, at dimensions and operands that fit, costs at
most `κ o d` and stays within the workspace `W₁ o d` declared for its operation; a kept operation
costs itself and has at most the same workspace. Nothing about values. -/
structure Table.Accounts (T : Table Op₁ Op₂) (I : Interp Op₂ K) (W₂ : Op₂ → List ℕ → ℕ)
    (κ : Op₁ → List ℕ → Count Op₂) (W₁ : Op₁ → List ℕ → ℕ) : Prop where
  /-- Implemented operations. -/
  impl : ∀ o R, T o = .inl R → ∀ (τ : ℕ → K) (d : List ℕ) (a : List (ℕ × ℕ)) (st st' : St Op₂ K),
    d.length = R.nd → a.length = R.nin + R.nout →
    exec I W₂ τ R.body (Env.frame d a) st = some st' → St.Within st st' (κ o d) (W₁ o d)
  /-- Kept operations. -/
  kept : ∀ o o', T o = .inr o' → ∀ d, Count.one o' d ≤ κ o d ∧ W₂ o' d ≤ W₁ o d

/-- **The certificate follows from the static cost and workspace of the trees**, for every
interpretation. -/
theorem Table.accounts_of_static {T : Table Op₁ Op₂} {W₂ : Op₂ → List ℕ → ℕ}
    {κ : Op₁ → List ℕ → Count Op₂} {W₁ : Op₁ → List ℕ → ℕ}
    (himpl : ∀ o R, T o = .inl R → ∀ d offs : List ℕ, d.length = R.nd →
      offs.length = R.nin + R.nout →
      staticCost R.body (d ++ offs) ≤ κ o d ∧ staticPeak W₂ R.body (d ++ offs) ≤ W₁ o d)
    (hkept : ∀ o o', T o = .inr o' → ∀ d, Count.one o' d ≤ κ o d ∧ W₂ o' d ≤ W₁ o d)
    (I : Interp Op₂ K) : T.Accounts I W₂ κ W₁ where
  impl o R hT τ d a st st' hd ha h := by
    obtain ⟨h1, h2⟩ := himpl o R hT d (a.map Prod.snd) hd (by simpa using ha)
    exact (exec_within h).mono h1 h2
  kept := hkept

/-- The simulation relation between a run of the algorithm under the induced interpretation and
the run of the linked program: same memory and live cells; lower counts within the push-forward
of the upper counts; lower peak within the upper peak. -/
structure Sim (κ : Op₁ → List ℕ → Count Op₂) (a : St Op₁ K) (c : St Op₂ K) : Prop where
  /-- Same memory. -/
  mem : c.mem = a.mem
  /-- Same live scratch cells. -/
  cur : c.cur = a.cur
  /-- Counts within the push-forward. -/
  cost : c.cost ≤ Count.push κ a.cost
  /-- Peak within the peak. -/
  peak : c.peak ≤ a.peak

theorem Sim.tick {T : Table Op₁ Op₂} {I : Interp Op₂ K} {W₂ : Op₂ → List ℕ → ℕ}
    {κ : Op₁ → List ℕ → Count Op₂} {W₁ : Op₁ → List ℕ → ℕ} (hacc : T.Accounts I W₂ κ W₁)
    {a : St Op₁ K} {c : St Op₂ K} (hs : Sim κ a c) {o : Op₁} {o' : Op₂} (hT : T o = .inr o')
    (d : List ℕ) : Sim κ (a.tick o d) (c.tick o' d) :=
  ⟨hs.mem, hs.cur, by
    simp only [St.tick, map_add, Count.push_one]
    exact add_le_add hs.cost (hacc.kept o o' hT d).1, hs.peak⟩

theorem iter_sim {σ σ' : Type} (R : σ → σ' → Prop) {f : ℕ → σ → Option σ}
    {f' : ℕ → σ' → Option σ'}
    (hf : ∀ i s s₁ s', R s s' → f i s = some s₁ → ∃ s₁', f' i s' = some s₁' ∧ R s₁ s₁') :
    ∀ n s s₁ s', R s s' → iter f n s = some s₁ → ∃ s₁', iter f' n s' = some s₁' ∧ R s₁ s₁' := by
  intro n
  induction n with
  | zero =>
    intro s s₁ s' hR hr
    cases hr
    exact ⟨s', rfl, hR⟩
  | succ k ih =>
    intro s s₁ s' hR hr
    obtain ⟨sm, h1, h2⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨sm', h1', hR'⟩ := ih s sm s' hR h1
    obtain ⟨s₁', h2', hR₁⟩ := hf k sm s₁ sm' hR' h2
    exact ⟨s₁', by simp only [iter, h1', Option.bind_some, h2'], hR₁⟩

theorem whileIter_sim {σ σ' : Type} (R : σ → σ' → Prop) {test : σ → Option Bool} {tick : σ → σ}
    {body : σ → Option σ} {test' : σ' → Option Bool} {tick' : σ' → σ'} {body' : σ' → Option σ'}
    (ht : ∀ s s', R s s' → test' s' = test s) (hk : ∀ s s', R s s' → R (tick s) (tick' s'))
    (hb : ∀ s s₁ s', R s s' → body s = some s₁ → ∃ s₁', body' s' = some s₁' ∧ R s₁ s₁') :
    ∀ n s s₁ s', R s s' → whileIter test tick body n s = some s₁ →
      ∃ s₁', whileIter test' tick' body' n s' = some s₁' ∧ R s₁ s₁' := by
  intro n
  induction n with
  | zero =>
    intro s s₁ s' hR hr
    obtain ⟨b, hb', hr⟩ := Option.bind_eq_some_iff.mp hr
    cases b with
    | true => simp at hr
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hr
      exact ⟨tick' s', by simp [whileIter, ht s s' hR, hb'], hr ▸ hk s s' hR⟩
  | succ k ih =>
    intro s s₁ s' hR hr
    obtain ⟨b, hb', hr⟩ := Option.bind_eq_some_iff.mp hr
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hr
      exact ⟨tick' s', by simp [whileIter, ht s s' hR, hb'], hr ▸ hk s s' hR⟩
    | true =>
      simp only [if_true] at hr
      obtain ⟨sm, h1, h2⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨sm', h1', hR'⟩ := hb _ sm _ (hk s s' hR) h1
      obtain ⟨s₁', h2', hR₁⟩ := ih sm s₁ sm' hR' h2
      exact ⟨s₁', by simp [whileIter, ht s s' hR, hb', h1', h2'], hR₁⟩

section Link

variable {T : Table Op₁ Op₂} {I : Interp Op₂ K} {W₂ : Op₂ → List ℕ → ℕ}
  {κ : Op₁ → List ℕ → Count Op₂} {W₁ : Op₁ → List ℕ → ℕ}

/-- The simulation of one call: a kept operation by itself, an implemented one by the certificate
of its implementation. -/
theorem exec_link_call (hacc : T.Accounts I W₂ κ W₁) (τ : ℕ → K) {o : Op₁} {ds : List IExp}
    {ins outs : List Operand} {ρ : Env} {a a₁ : St Op₁ K} {c : St Op₂ K} (hs : Sim κ a c)
    (h : exec (I.link T) W₁ τ (.call o ds ins outs) ρ a = some a₁) :
    ∃ c₁, exec I W₂ τ ((Stmt.call o ds ins outs).link T) ρ c = some c₁ ∧ Sim κ a₁ c₁ := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m', hcall, rfl⟩ := Option.map_eq_some_iff.mp h
  cases hT : T o with
  | inr o' =>
    rw [Interp.link_callS_inr I hT, ← hs.mem] at hcall
    refine ⟨⟨m', c.cost + Count.one o' d, c.cur, max c.peak (c.cur + W₂ o' d)⟩, by
      simp [Stmt.link, hT, exec, hd, hi, hb, hcall], rfl, hs.cur, ?_, ?_⟩
    · simp only [map_add, Count.push_one]
      exact add_le_add hs.cost (hacc.kept o o' hT d).1
    · rw [hs.cur]
      exact max_le_max hs.peak (Nat.add_le_add_left (hacc.kept o o' hT d).2 _)
  | inl R =>
    rw [Interp.link_callS_inl I hT] at hcall
    split_ifs at hcall with hfit
    have h1 := IExp.length_of_evalList hd
    have h2 := Operand.length_of_evalList hi
    have h3 := Operand.length_of_evalList hb
    obtain ⟨c₁, hc, hm⟩ := exec_eq_some_of_run hcall W₂ c hs.mem
    obtain ⟨w1, w2, w3⟩ := hacc.impl o R hT τ d (i ++ b) c c₁ hfit.1
      (by rw [List.length_append, hfit.2.1, hfit.2.2]) hc
    refine ⟨c₁, ?_, hm, w1.trans hs.cur, ?_, ?_⟩
    · have hfit' : R.Fits ds.length ins.length outs.length := by
        rw [← h1, ← h2, ← h3]
        exact hfit
      have hl : (Stmt.call o ds ins outs).link T = .frame ds (ins ++ outs) R.body := by
        simp only [Stmt.link, hT]
        exact if_pos hfit'
      simp [hl, exec, hd, hi, hb, Operand.evalList_append, hc]
    · simp only [map_add, Count.push_one]
      exact w2.trans (add_le_add hs.cost le_rfl)
    · rw [hs.cur] at w3
      exact w3.trans (max_le_max hs.peak le_rfl)

/-- **The simulation theorem**: a successful counted run of the algorithm under the induced
interpretation is matched by a counted run of the linked program under the lower interpretation,
with the same memory, counts within the push-forward and peak within the peak. -/
theorem exec_link (hacc : T.Accounts I W₂ κ W₁) (τ : ℕ → K) (s : Stmt Op₁) :
    ∀ (ρ : Env) (a a₁ : St Op₁ K) (c : St Op₂ K), Sim κ a c →
      exec (I.link T) W₁ τ s ρ a = some a₁ →
      ∃ c₁, exec I W₂ τ (s.link T) ρ c = some c₁ ∧ Sim κ a₁ c₁ := by
  induction s with
  | skip => intro ρ a a₁ c hs h; cases h; exact ⟨c, rfl, hs⟩
  | abort => intro ρ a a₁ c hs h; cases h
  | seq s t ihs iht =>
    intro ρ a a₁ c hs h
    obtain ⟨am, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cm, hc1, hsm⟩ := ihs ρ a am c hs h1
    obtain ⟨c₁, hc2, hs₁⟩ := iht ρ am a₁ cm hsm h2
    exact ⟨c₁, by simp only [Stmt.link, exec, hc1, Option.bind_some, hc2], hs₁⟩
  | call o ds ins outs => exact fun ρ a a₁ c hs h => exec_link_call hacc τ hs h
  | ite o ds ins t e iht ihe =>
    intro ρ a a₁ c hs h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    cases hT : T o with
    | inl R => rw [Interp.link_test_inl I hT] at hb; cases hb
    | inr o' =>
      rw [Interp.link_test_inr I hT, ← hs.mem] at hb
      have hs' := hs.tick hacc hT d
      cases b with
      | false =>
        obtain ⟨c₁, hc, hs₁⟩ := ihe ρ _ a₁ _ hs' (by simpa using h)
        exact ⟨c₁, by simp [Stmt.link, hT, exec, hd, hi, hb, hc], hs₁⟩
      | true =>
        obtain ⟨c₁, hc, hs₁⟩ := iht ρ _ a₁ _ hs' (by simpa using h)
        exact ⟨c₁, by simp [Stmt.link, hT, exec, hd, hi, hb, hc], hs₁⟩
  | whileFuel fuel o ds ins body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    cases hT : T o with
    | inl R => cases k <;> simp [whileIter, Interp.link_test_inl I hT] at h
    | inr o' =>
      obtain ⟨c₁, hc, hs₁⟩ := whileIter_sim (Sim κ) (test' := fun s => I.test o' d i s.mem)
        (tick' := fun s => s.tick o' d) (body' := exec I W₂ τ (body.link T) ρ)
        (fun s s' hR => by rw [Interp.link_test_inr I hT, hR.mem])
        (fun s s' hR => hR.tick hacc hT d) (fun s s₁ s' hR hb => ih ρ s s₁ s' hR hb) k a a₁ c hs h
      exact ⟨c₁, by simp [Stmt.link, hT, exec, hk, hd, hi, hc], hs₁⟩
  | bindIdx o ins bound body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases hT : T o with
    | inl R => rw [Interp.link_index_inl I hT] at hv; cases hv
    | inr o' =>
      rw [Interp.link_index_inr I hT, ← hs.mem] at hv
      split_ifs at h with hle
      obtain ⟨c₁, hc, hs₁⟩ := ih _ _ a₁ _ (hs.tick hacc hT []) h
      exact ⟨c₁, by simp [Stmt.link, hT, exec, hi, hB, hv, hle, hc], hs₁⟩
  | alloc len body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨cm, cc, ccur, cpk⟩ := c
    obtain ⟨e1, e2, hcost, hpeak⟩ := hs
    dsimp only at e1 e2 hcost hpeak
    subst e1 e2
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c₂, hc, hs₂⟩ := ih _
      ⟨⟨a.mem.store.push n, a.mem.pos⟩, a.cost, a.cur + n, max a.peak (a.cur + n)⟩ a₂
      ⟨⟨a.mem.store.push n, a.mem.pos⟩, cc, a.cur + n, max cpk (a.cur + n)⟩
      ⟨rfl, rfl, hcost, max_le_max hpeak le_rfl⟩ h₂
    exact ⟨⟨⟨c₂.mem.store.pop, c₂.mem.pos⟩, c₂.cost, a.cur, c₂.peak⟩,
      by simp only [Stmt.link, exec, hn, Option.bind_some, hc, Option.map_some],
      ⟨by simp only [hs₂.mem], rfl, hs₂.cost, hs₂.peak⟩⟩
  | loop n body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c₁, hc, hs₁⟩ := iter_sim (Sim κ)
      (f' := fun i st => exec I W₂ τ (body.link T) (ρ.pushIdx i) st)
      (fun i s s₁ s' hR hb => ih _ s s₁ s' hR hb) k a a₁ c hs h
    exact ⟨c₁, by simp only [Stmt.link, exec, hk, Option.bind_some, hc], hs₁⟩
  | frame ds args body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c₁, hc, hs₁⟩ := ih _ a a₁ c hs h
    exact ⟨c₁, by simp only [Stmt.link, exec, hd, hi, Option.bind_some, hc], hs₁⟩

/-- **Linking, total correctness with accounting.** If the algorithm runs within `B`, `M` under
the induced interpretation, the linked program runs under the lower interpretation within the
pushed-forward counts and the same workspace, with the same postcondition. -/
theorem Runs.link (hacc : T.Accounts I W₂ κ W₁) {τ : ℕ → K} {s : Stmt Op₁} {ρ : Env} {m : Mem K}
    {B : Count Op₁} {M : ℕ} {Q : Mem K → Prop} (h : Runs (I.link T) W₁ τ s ρ m B M Q) :
    Runs I W₂ τ (s.link T) ρ m (Count.push κ B) M Q := by
  obtain ⟨a₁, hrun, hcost, hpeak, hQ⟩ := h
  obtain ⟨c₁, hc, hs₁⟩ := exec_link hacc τ s ρ (St.init m) a₁ (St.init m)
    ⟨rfl, rfl, by simp [St.init], le_rfl⟩ hrun
  exact ⟨c₁, hc, hs₁.cost.trans (Count.push_mono κ hcost), hs₁.peak.trans hpeak, hs₁.mem ▸ hQ⟩

/-- **Linking a theorem proved for every interpretation meeting contracts** `Ck`: it holds for
the linked program as soon as the induced interpretation meets `Ck`, that is, the implementations
meet their specifications. -/
theorem link_total {Ck : Interp Op₁ K → Prop} {τ : ℕ → K} {s : Stmt Op₁} {ρ : Env} {m : Mem K}
    {B : Count Op₁} {M : ℕ} {Q : Mem K → Prop} (hT : ∀ J, Ck J → Runs J W₁ τ s ρ m B M Q)
    (hk : Ck (I.link T)) (hacc : T.Accounts I W₂ κ W₁) :
    Runs I W₂ τ (s.link T) ρ m (Count.push κ B) M Q :=
  (hT _ hk).link hacc

/-- **Weighted, data-dependent counts.** A bound `w₁ cost ≤ t` on the final count of one run of
the algorithm becomes `w₂ cost ≤ t` for the linked run, for every monotone `w₂` with
`w₂ ∘ push κ ≤ w₁`. -/
theorem exec_link_weight (hacc : T.Accounts I W₂ κ W₁) {τ : ℕ → K} {s : Stmt Op₁} {ρ : Env}
    {m : Mem K} {a₁ : St Op₁ K} {w₁ : Count Op₁ → ℕ} {w₂ : Count Op₂ → ℕ} (hw₂ : Monotone w₂)
    (hww : ∀ x, w₂ (Count.push κ x) ≤ w₁ x)
    (hrun : exec (I.link T) W₁ τ s ρ (St.init m) = some a₁) {t : ℕ} (ht : w₁ a₁.cost ≤ t) :
    ∃ c₁, exec I W₂ τ (s.link T) ρ (St.init m) = some c₁ ∧ c₁.mem = a₁.mem ∧ w₂ c₁.cost ≤ t := by
  obtain ⟨c₁, hc, hs₁⟩ := exec_link hacc τ s ρ (St.init m) a₁ (St.init m)
    ⟨rfl, rfl, by simp [St.init], le_rfl⟩ hrun
  exact ⟨c₁, hc, hs₁.mem, (hw₂ hs₁.cost).trans ((hww _).trans ht)⟩

/-- **Probability.** The interpretation is fixed before the sample `ω`; the tape, the start and
the postcondition may depend on it. The failure event of the linked program is inside the failure
event of the algorithm under the induced interpretation, so a bound on the probability of the
latter bounds the former. -/
theorem fail_subset (hacc : T.Accounts I W₂ κ W₁) {Ω : Type} {τ : Ω → ℕ → K} {s : Stmt Op₁}
    {ρ : Env} {m : Ω → Mem K} {B : Count Op₁} {M : ℕ} {Q : Ω → Mem K → Prop} :
    {ω | ¬ Runs I W₂ (τ ω) (s.link T) ρ (m ω) (Count.push κ B) M (Q ω)} ⊆
      {ω | ¬ Runs (I.link T) W₁ (τ ω) s ρ (m ω) B M (Q ω)} :=
  fun _ hω hR => hω (hR.link hacc)

end Link

/-- **Linking, partial correctness.** A refinement statement under the induced interpretation is
one about the linked program. No certificate. -/
theorem RunsL.link {T : Table Op₁ Op₂} {I : Interp Op₂ K} {τ : ℕ → K} {s : Stmt Op₁} {ρ : Env}
    {m : Mem K} {Q : Mem K → Prop} (h : RunsL (I.link T) τ s ρ m Q) :
    RunsL I τ (s.link T) ρ m Q := by
  intro m' hm
  rw [run_link] at hm
  exact h m' hm

/-- **Linking a refinement theorem proved for every interpretation meeting contracts** `Ck`:
only through the induced interpretation. -/
theorem link_liberal {T : Table Op₁ Op₂} {I : Interp Op₂ K} {Ck : Interp Op₁ K → Prop}
    {τ : ℕ → K} {s : Stmt Op₁} {ρ : Env} {m : Mem K} {Q : Mem K → Prop}
    (hT : ∀ J, Ck J → RunsL J τ s ρ m Q) (hk : Ck (I.link T)) : RunsL I τ (s.link T) ρ m Q :=
  (hT _ hk).link

end NLAlib.Ops
