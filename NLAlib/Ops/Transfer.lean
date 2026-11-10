/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Module.End
public import NLAlib.Ops.Link
public import NLAlib.Ops.Static

/-!
# The transfer theorems of linking

A theorem about an algorithm under every interpretation meeting contracts becomes a theorem about
the linked program, with no new proof about the algorithm.

## Main results

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
  `NLAlib.Ops.fail_subset`: failure events, sample by sample.
* **Weighted, data-dependent counts.** `NLAlib.Ops.Table.AccountsW`: each implementation adds at
  most `t o d` to a weight of the lower counts; its counts need not be uniform in the data.
  `NLAlib.Ops.RunsW.link`, `NLAlib.Ops.exec_link_weight`: a bound on the weight of the counts of
  one run of the algorithm, which may depend on the final memory, is the same bound for the
  linked program. The simulation is one induction for the counts and for every weight
  (`NLAlib.Ops.Table.Accounts.toW`).
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Op₃ Tst K : Type}

namespace Count

/-- The additive map sending one use of the name `k` at `d` to `f k d`. -/
noncomputable def lift {A : Type} [AddCommMonoid A] (f : Op ⊕ Tst → List ℕ → A) :
    Count Op Tst →+ A :=
  Finsupp.liftAddHom fun k => (smulAddHom ℕ A).flip (f k.1 k.2)

theorem lift_single {A : Type} [AddCommMonoid A] (f : Op ⊕ Tst → List ℕ → A)
    (k : (Op ⊕ Tst) × List ℕ) (n : ℕ) : lift f (Finsupp.single k n) = n • f k.1 k.2 := by
  simp [lift]

theorem lift_mono {A : Type} [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A]
    (f : Op ⊕ Tst → List ℕ → A) : Monotone (lift f) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := exists_add_of_le hab
  rw [map_add]
  exact le_self_add

/-- **The push-forward of counts**: the additive map sending one call of `o` at `d` to `κ o d`
and keeping the uses of queries. -/
noncomputable def push (κ : Op₁ → List ℕ → Count Op₂ Tst) : Count Op₁ Tst →+ Count Op₂ Tst :=
  lift (Sum.elim κ Count.test)

@[simp] theorem push_one (κ : Op₁ → List ℕ → Count Op₂ Tst) (o : Op₁) (d : List ℕ) :
    push κ (Count.one o d) = κ o d := by
  simp [push, lift, Count.one]

@[simp] theorem push_test (κ : Op₁ → List ℕ → Count Op₂ Tst) (q : Tst) (d : List ℕ) :
    push κ (Count.test q d) = Count.test q d := by
  simp [push, lift, Count.test]

theorem push_mono (κ : Op₁ → List ℕ → Count Op₂ Tst) : Monotone (push κ) := lift_mono _

/-- Push-forwards compose: the push-forward through a tower is the push-forward of the composed
cost of single calls. -/
theorem push_comp (κ₁ : Op₁ → List ℕ → Count Op₂ Tst) (κ₂ : Op₂ → List ℕ → Count Op₃ Tst)
    (c : Count Op₁ Tst) : push κ₂ (push κ₁ c) = push (fun o d => push κ₂ (κ₁ o d)) c := by
  have h : (push κ₂).comp (push κ₁) = push fun o d => push κ₂ (κ₁ o d) :=
    Finsupp.addHom_ext fun k n => by
      obtain ⟨k | q, d⟩ := k
      · simp only [AddMonoidHom.comp_apply, push, lift_single, map_nsmul, Sum.elim_inl]
      · have := push_test κ₂ q d
        simp only [AddMonoidHom.comp_apply, push, lift_single, map_nsmul, Sum.elim_inr] at this ⊢
        rw [this]
  exact DFunLike.congr_fun h c

/-- The push-forward that keeps every operation is the identity. -/
@[simp] theorem push_one_eq (c : Count Op Tst) : push Count.one c = c := by
  have h : push (Op₁ := Op) (Tst := Tst) Count.one = AddMonoidHom.id _ :=
    Finsupp.addHom_ext fun k n => by
      obtain ⟨k | q, d⟩ := k <;>
        simp [push, lift_single, Count.one, Count.test, Finsupp.smul_single]
  exact DFunLike.congr_fun h c

/-- A weighted count: one call of `o` at `d` weighs `w o d`, one use of a query `wt q d`. -/
noncomputable abbrev weight (w : Op → List ℕ → ℕ) (wt : Tst → List ℕ → ℕ := fun _ _ => 0) :
    Count Op Tst →+ ℕ := lift (Sum.elim w wt)

@[simp] theorem weight_one (w : Op → List ℕ → ℕ) (wt : Tst → List ℕ → ℕ) (o : Op) (d : List ℕ) :
    weight w wt (Count.one o d) = w o d := by
  simp [lift, Count.one]

@[simp] theorem weight_test (w : Op → List ℕ → ℕ) (wt : Tst → List ℕ → ℕ) (q : Tst)
    (d : List ℕ) : weight w wt (Count.test (Op := Op) q d) = wt q d := by
  simp [lift, Count.test]

end Count

/-- **The accounting certificate of a table**, for the lower interpretation `I` and workspaces
`W₂`: every successful run of an implementation, at dimensions and operands that fit, costs at
most `κ o d` and stays within the workspace `W₁ o d` declared for its operation; a kept operation
costs itself and has at most the same workspace. Nothing about values. -/
structure Table.Accounts (T : Table Op₁ Op₂ Tst) (I : Interp Op₂ Tst K) (W₂ : Op₂ → List ℕ → ℕ)
    (κ : Op₁ → List ℕ → Count Op₂ Tst) (W₁ : Op₁ → List ℕ → ℕ) : Prop where
  /-- Implemented operations. -/
  impl : ∀ o R, T o = .inl R → ∀ (τ : Tape K) (d : List ℕ) (a : List (ℕ × ℕ)) (st st'
      : St Op₂ Tst K),
    d.length = R.nd → a.length = R.nin + R.nout →
    exec I W₂ τ R.body (Env.frame d a) st = some st' → St.Within st st' (κ o d) (W₁ o d)
  /-- Kept operations. -/
  kept : ∀ o o', T o = .inr o' → ∀ d, Count.one o' d ≤ κ o d ∧ W₂ o' d ≤ W₁ o d

/-- **The certificate follows from the static cost and workspace of the trees**, for every
interpretation. -/
theorem Table.accounts_of_static {T : Table Op₁ Op₂ Tst} {W₂ : Op₂ → List ℕ → ℕ}
    {κ : Op₁ → List ℕ → Count Op₂ Tst} {W₁ : Op₁ → List ℕ → ℕ}
    (himpl : ∀ o R, T o = .inl R → ∀ d offs : List ℕ, d.length = R.nd →
      offs.length = R.nin + R.nout →
      staticCost R.body (d ++ offs) ≤ κ o d ∧ staticPeak W₂ R.body (d ++ offs) ≤ W₁ o d)
    (hkept : ∀ o o', T o = .inr o' → ∀ d, Count.one o' d ≤ κ o d ∧ W₂ o' d ≤ W₁ o d)
    (I : Interp Op₂ Tst K) : T.Accounts I W₂ κ W₁ where
  impl o R hT τ d a st st' hd ha h := by
    obtain ⟨h1, h2⟩ := himpl o R hT d (a.map Prod.snd) hd (by simpa using ha)
    exact (exec_within h).mono h1 h2
  kept := hkept

/-- **The weighted accounting certificate of a table.** `w₂` is a weight of the lower counts
(an additive map to an ordered monoid `A`: flops, kernel work `T(k)`, the counts themselves) and
`t o d` bounds the weight of one call of `o` at the dimensions `d`. Every successful run of an
implementation adds at most `t o d` to the weight and stays within the workspace of its
operation. The counts of a run of an implementation may depend on the data (a split read from
the store, a loop with early exit); only their weight is bounded. Nothing about values. -/
structure Table.AccountsW {A : Type} [AddCommMonoid A] [PartialOrder A] (T : Table Op₁ Op₂ Tst)
    (I : Interp Op₂ Tst K) (W₂ : Op₂ → List ℕ → ℕ) (w₂ : Count Op₂ Tst →+ A)
    (t : Op₁ → List ℕ → A) (W₁ : Op₁ → List ℕ → ℕ) : Prop where
  /-- Implemented operations. -/
  impl : ∀ o R, T o = .inl R → ∀ (τ : Tape K) (d : List ℕ) (a : List (ℕ × ℕ)) (st st'
      : St Op₂ Tst K),
    d.length = R.nd → a.length = R.nin + R.nout →
    exec I W₂ τ R.body (Env.frame d a) st = some st' →
      st'.cur = st.cur ∧ w₂ st'.cost ≤ w₂ st.cost + t o d ∧
        st'.peak ≤ max st.peak (st.cur + W₁ o d)
  /-- Kept operations. -/
  kept : ∀ o o', T o = .inr o' → ∀ d, w₂ (Count.one o' d) ≤ t o d ∧ W₂ o' d ≤ W₁ o d

/-- The weight of the upper counts that a weighted certificate compares with: one call of `o` at
`d` weighs `t o d`, one use of a query what it weighs below. -/
noncomputable def Count.upper {A : Type} [AddCommMonoid A] (w₂ : Count Op₂ Tst →+ A)
    (t : Op₁ → List ℕ → A) : Count Op₁ Tst →+ A :=
  Count.lift (Sum.elim t fun q d => w₂ (Count.test q d))

@[simp] theorem Count.upper_one {A : Type} [AddCommMonoid A] (w₂ : Count Op₂ Tst →+ A)
    (t : Op₁ → List ℕ → A) (o : Op₁) (d : List ℕ) : Count.upper w₂ t (Count.one o d) = t o d := by
  simp [Count.upper, Count.lift, Count.one]

@[simp] theorem Count.upper_test {A : Type} [AddCommMonoid A] (w₂ : Count Op₂ Tst →+ A)
    (t : Op₁ → List ℕ → A) (q : Tst) (d : List ℕ) :
    Count.upper w₂ t (Count.test q d) = w₂ (Count.test q d) := by
  simp [Count.upper, Count.lift, Count.test]

/-- With the counts themselves as weight, the upper weight is the push-forward. -/
theorem Count.upper_id (κ : Op₁ → List ℕ → Count Op₂ Tst) :
    Count.upper (AddMonoidHom.id (Count Op₂ Tst)) κ = Count.push κ := rfl

/-- The accounting certificate is the weighted one for the counts themselves. -/
theorem Table.Accounts.toW {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K}
    {W₂ : Op₂ → List ℕ → ℕ} {κ : Op₁ → List ℕ → Count Op₂ Tst} {W₁ : Op₁ → List ℕ → ℕ}
    (h : T.Accounts I W₂ κ W₁) : T.AccountsW I W₂ (AddMonoidHom.id _) κ W₁ where
  impl o R hT τ d a st st' hd ha hrun := h.impl o R hT τ d a st st' hd ha hrun
  kept := h.kept

/-- The simulation relation between a run of the algorithm under the induced interpretation and
the run of the linked program: same memory and live cells; the weight of the lower counts within
the weight of the upper counts; lower peak within the upper peak. -/
structure Sim {A : Type} [AddCommMonoid A] [PartialOrder A] (w₂ : Count Op₂ Tst →+ A)
    (t : Op₁ → List ℕ → A) (a : St Op₁ Tst K) (c : St Op₂ Tst K) : Prop where
  /-- Same memory. -/
  mem : c.mem = a.mem
  /-- Same live scratch cells. -/
  cur : c.cur = a.cur
  /-- Weight within the weight. -/
  cost : w₂ c.cost ≤ Count.upper w₂ t a.cost
  /-- Peak within the peak. -/
  peak : c.peak ≤ a.peak

section Link

variable {A : Type} [AddCommMonoid A] [PartialOrder A] [IsOrderedAddMonoid A]
  {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {W₂ : Op₂ → List ℕ → ℕ}
  {w₂ : Count Op₂ Tst →+ A} {t : Op₁ → List ℕ → A} {W₁ : Op₁ → List ℕ → ℕ}

theorem Sim.tick {a : St Op₁ Tst K} {c : St Op₂ Tst K} (hs : Sim w₂ t a c) (q : Tst)
    (d : List ℕ) : Sim w₂ t (a.tick q d) (c.tick q d) :=
  ⟨hs.mem, hs.cur, by
    simp only [St.tick, map_add, Count.upper_test]
    exact add_le_add hs.cost le_rfl, hs.peak⟩

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

theorem whileIter_sim {σ σ' : Type} (R : σ → σ' → Prop) {test : ℕ → σ → Option (Bool × σ)}
    {body : ℕ → σ → Option σ} {test' : ℕ → σ' → Option (Bool × σ')}
    {body' : ℕ → σ' → Option σ'}
    (ht : ∀ i s bs s', R s s' → test i s = some bs →
      ∃ s₁', test' i s' = some (bs.1, s₁') ∧ R bs.2 s₁')
    (hb : ∀ i s s₁ s', R s s' → body i s = some s₁ → ∃ s₁', body' i s' = some s₁' ∧ R s₁ s₁') :
    ∀ n i s js s', R s s' → whileIter test body n i s = some js →
      ∃ s₁', whileIter test' body' n i s' = some (js.1, s₁') ∧ R js.2 s₁' := by
  intro n
  induction n with
  | zero =>
    intro i s js s' hR hr
    cases hr
    exact ⟨s', rfl, hR⟩
  | succ k ih =>
    intro i s js s' hR hr
    obtain ⟨bs, hbs, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨st', ht', hR'⟩ := ht i s bs s' hR hbs
    split_ifs at hr with hc
    · obtain ⟨sm, h1, h2⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨sm', h1', hRm⟩ := hb i _ sm _ hR' h1
      obtain ⟨s₁', h2', hR₁⟩ := ih (i + 1) sm js sm' hRm h2
      exact ⟨s₁', by simp [whileIter, ht', hc, h1', h2'], hR₁⟩
    · cases hr
      exact ⟨st', by simp [whileIter, ht', hc], hR'⟩

/-- The simulation of one call: a kept operation by itself, an implemented one by the certificate
of its implementation. -/
theorem exec_link_call (hacc : T.AccountsW I W₂ w₂ t W₁) (τ : Tape K) {o : Op₁} {ds : List IExp}
    {ins outs : List Operand} {ρ : Env} {a a₁ : St Op₁ Tst K} {c : St Op₂ Tst K}
    (hs : Sim w₂ t a c) (h : exec (I.link T) W₁ τ (.call o ds ins outs) ρ a = some a₁) :
    ∃ c₁, exec I W₂ τ ((Stmt.call o ds ins outs).link T) ρ c = some c₁ ∧ Sim w₂ t a₁ c₁ := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m', hcall, rfl⟩ := Option.map_eq_some_iff.mp h
  cases hT : T o with
  | inr o' =>
    rw [Interp.link_callS_inr I hT, ← hs.mem] at hcall
    refine ⟨⟨m', c.cost + Count.one o' d, c.cur, max c.peak (c.cur + W₂ o' d)⟩, by
      simp [Stmt.link, hT, exec, hd, hi, hb, hcall], rfl, hs.cur, ?_, ?_⟩
    · simp only [map_add, Count.upper_one]
      exact add_le_add hs.cost (hacc.kept o o' hT d).1
    · rw [hs.cur]
      exact max_le_max hs.peak (Nat.add_le_add_left (hacc.kept o o' hT d).2 _)
  | inl R =>
    rw [Interp.link_callS_inl I hT] at hcall
    split_ifs at hcall with hl hfit
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
      have hl' : (Stmt.call o ds ins outs).link T = .frame ds (ins ++ outs) R.body := by
        simp only [Stmt.link, hT]
        exact if_pos hfit'
      simp [hl', exec, hd, hi, hb, Operand.evalList_append, hc, hs.mem, hl]
    · simp only [map_add, Count.upper_one]
      exact w2.trans (add_le_add hs.cost le_rfl)
    · rw [hs.cur] at w3
      exact w3.trans (max_le_max hs.peak le_rfl)

/-- **The simulation theorem**: a successful counted run of the algorithm under the induced
interpretation is matched by a counted run of the linked program under the lower interpretation,
with the same memory, the weight of its counts within the weight of the upper counts and its
peak within the peak. One induction serves the counts themselves and every weight. -/
theorem exec_link (hacc : T.AccountsW I W₂ w₂ t W₁) (τ : Tape K) (s : Stmt Op₁ Tst) :
    ∀ (ρ : Env) (a a₁ : St Op₁ Tst K) (c : St Op₂ Tst K), Sim w₂ t a c →
      exec (I.link T) W₁ τ s ρ a = some a₁ →
      ∃ c₁, exec I W₂ τ (s.link T) ρ c = some c₁ ∧ Sim w₂ t a₁ c₁ := by
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
  | ite q ds ins t e iht ihe =>
    intro ρ a a₁ c hs h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    have hb' : I.test q d i c.mem = some b := by rw [hs.mem]; exact hb
    have hs' := hs.tick q d
    cases b with
    | false =>
      obtain ⟨c₁, hc, hs₁⟩ := ihe ρ _ a₁ _ hs' (by simpa using h)
      exact ⟨c₁, by simp [Stmt.link, exec, hd, hi, hb', hc], hs₁⟩
    | true =>
      obtain ⟨c₁, hc, hs₁⟩ := iht ρ _ a₁ _ hs' (by simpa using h)
      exact ⟨c₁, by simp [Stmt.link, exec, hd, hi, hb', hc], hs₁⟩
  | whileFuel fuel q ds ins body k ih ihk =>
    intro ρ a a₁ c hs h
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨jst, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cm, hc, hsm⟩ := whileIter_sim (Sim w₂ t)
      (test' := fun i st => I.testSt q ds ins (ρ.pushIdx i) st)
      (body' := fun i => exec I W₂ τ (body.link T) (ρ.pushIdx i))
      (fun i s bs s' hR hbs => by
        obtain ⟨d, hd, hbs⟩ := Option.bind_eq_some_iff.mp hbs
        obtain ⟨x, hx, hbs⟩ := Option.bind_eq_some_iff.mp hbs
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hbs
        have hb' : I.test q d x s'.mem = some b := by rw [hR.mem]; exact hb
        exact ⟨s'.tick q d, by rw [Interp.testSt_eq hd hx, hb']; rfl, hR.tick q d⟩)
      (fun i s s₁ s' hR hb => ih _ s s₁ s' hR hb) n 0 a jst c hs hw
    obtain ⟨c₁, hc₁, hs₁⟩ := ihk _ _ a₁ _ hsm h
    exact ⟨c₁, by simp [Stmt.link, exec, hn, hc, hc₁], hs₁⟩
  | bindIdx q ins bound body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    have hv' : I.index q i c.mem = some v := by rw [hs.mem]; exact hv
    split_ifs at h with hle
    obtain ⟨c₁, hc, hs₁⟩ := ih _ _ a₁ _ (hs.tick q []) h
    exact ⟨c₁, by simp [Stmt.link, exec, hi, hB, hv', hle, hc], hs₁⟩
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
    obtain ⟨c₁, hc, hs₁⟩ := iter_sim (Sim w₂ t)
      (f' := fun i st => exec I W₂ τ (body.link T) (ρ.pushIdx i) st)
      (fun i s s₁ s' hR hb => ih _ s s₁ s' hR hb) k a a₁ c hs h
    exact ⟨c₁, by simp only [Stmt.link, exec, hk, Option.bind_some, hc], hs₁⟩
  | frame ds args body ih =>
    intro ρ a a₁ c hs h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hl
    obtain ⟨c₁, hc, hs₁⟩ := ih _ a a₁ c hs h
    exact ⟨c₁, by simp [Stmt.link, exec, hd, hi, hc, hs.mem, hl], hs₁⟩

/-- **Linking a run whose postcondition sees the counts.** Under a weighted certificate, the
linked program runs within the same workspace, and the weight of its counts is at most the
weight of counts `c₁` of the algorithm that satisfy the postcondition. A bound on the weight of
the algorithm's counts, whatever it depends on, is a bound on the weight of the program's. -/
theorem RunsW.link (hacc : T.AccountsW I W₂ w₂ t W₁) {τ : Tape K} {s : Stmt Op₁ Tst} {ρ : Env}
    {m : Mem K} {M : ℕ} {Q : Count Op₁ Tst → Mem K → Prop}
    (h : RunsW (I.link T) W₁ τ s ρ m M Q) :
    RunsW I W₂ τ (s.link T) ρ m M fun c m' => ∃ c₁, w₂ c ≤ Count.upper w₂ t c₁ ∧ Q c₁ m' := by
  obtain ⟨a₁, hrun, hpeak, hQ⟩ := h
  obtain ⟨c₁, hc, hs₁⟩ := exec_link hacc τ s ρ (St.init m) a₁ (St.init m)
    ⟨rfl, rfl, by simp [St.init], le_rfl⟩ hrun
  exact ⟨c₁, hc, hs₁.peak.trans hpeak, a₁.cost, hs₁.cost, hs₁.mem ▸ hQ⟩

end Link

section Link

variable {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {W₂ : Op₂ → List ℕ → ℕ}
  {κ : Op₁ → List ℕ → Count Op₂ Tst} {W₁ : Op₁ → List ℕ → ℕ}

/-- **Linking, total correctness with accounting.** If the algorithm runs within `B`, `M` under
the induced interpretation, the linked program runs under the lower interpretation within the
pushed-forward counts and the same workspace, with the same postcondition. -/
theorem Runs.link (hacc : T.Accounts I W₂ κ W₁) {τ : Tape K} {s : Stmt Op₁ Tst} {ρ : Env}
    {m : Mem K} {B : Count Op₁ Tst} {M : ℕ} {Q : Mem K → Prop}
    (h : Runs (I.link T) W₁ τ s ρ m B M Q) :
    Runs I W₂ τ (s.link T) ρ m (Count.push κ B) M Q := by
  obtain ⟨a₁, hrun, hcost, hpeak, hQ⟩ := h
  obtain ⟨c₁, hc, hs₁⟩ := exec_link hacc.toW τ s ρ (St.init m) a₁ (St.init m)
    ⟨rfl, rfl, by simp [St.init], le_rfl⟩ hrun
  exact ⟨c₁, hc, (show c₁.cost ≤ Count.push κ a₁.cost from hs₁.cost).trans
    (Count.push_mono κ hcost), hs₁.peak.trans hpeak, hs₁.mem ▸ hQ⟩

/-- **Linking a theorem proved for every interpretation meeting contracts** `Ck`: it holds for
the linked program as soon as the induced interpretation meets `Ck`, that is, the implementations
meet their specifications. -/
theorem link_total {Ck : Interp Op₁ Tst K → Prop} {τ : Tape K} {s : Stmt Op₁ Tst} {ρ : Env}
    {m : Mem K}
    {B : Count Op₁ Tst} {M : ℕ} {Q : Mem K → Prop} (hT : ∀ J, Ck J → Runs J W₁ τ s ρ m B M Q)
    (hk : Ck (I.link T)) (hacc : T.Accounts I W₂ κ W₁) :
    Runs I W₂ τ (s.link T) ρ m (Count.push κ B) M Q :=
  (hT _ hk).link hacc

/-- **Probability.** The interpretation is fixed before the sample `ω`; the tape, the start and
the postcondition may depend on it. The failure event of the linked program is inside the failure
event of the algorithm under the induced interpretation, so a bound on the probability of the
latter bounds the former. -/
theorem fail_subset (hacc : T.Accounts I W₂ κ W₁) {Ω : Type} {τ : Ω → Tape K} {s : Stmt Op₁ Tst}
    {ρ : Env} {m : Ω → Mem K} {B : Count Op₁ Tst} {M : ℕ} {Q : Ω → Mem K → Prop} :
    {ω | ¬ Runs I W₂ (τ ω) (s.link T) ρ (m ω) (Count.push κ B) M (Q ω)} ⊆
      {ω | ¬ Runs (I.link T) W₁ (τ ω) s ρ (m ω) B M (Q ω)} :=
  fun _ hω hR => hω (hR.link hacc)

end Link

/-- **Weighted, data-dependent counts.** A bound `t`, which may depend on the final memory, on
the weight of the counts of one run of the algorithm becomes the same bound on the weight of the
counts of the linked run. The weight below is `w₂`; one call of `o` at `d` weighs `u o d` above,
and the weighted certificate says that this covers its implementation. -/
theorem exec_link_weight {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {W₂ : Op₂ → List ℕ → ℕ}
    {W₁ : Op₁ → List ℕ → ℕ} {w₂ : Count Op₂ Tst →+ ℕ} {u : Op₁ → List ℕ → ℕ}
    (hacc : T.AccountsW I W₂ w₂ u W₁) {τ : Tape K} {s : Stmt Op₁ Tst} {ρ : Env} {m : Mem K}
    {M : ℕ} {t : Mem K → ℕ} {Q : Mem K → Prop}
    (h : RunsW (I.link T) W₁ τ s ρ m M fun c m' => Count.upper w₂ u c ≤ t m' ∧ Q m') :
    RunsW I W₂ τ (s.link T) ρ m M fun c m' => w₂ c ≤ t m' ∧ Q m' :=
  (h.link hacc).mono le_rfl fun _ _ ⟨_, h1, h2, h3⟩ => ⟨h1.trans h2, h3⟩

/-- **Linking, partial correctness.** A refinement statement under the induced interpretation is
one about the linked program. No certificate. -/
theorem RunsL.link {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {τ : Tape K} {s : Stmt Op₁ Tst}
    {ρ : Env}
    {m : Mem K} {Q : Mem K → Prop} (h : RunsL (I.link T) τ s ρ m Q) :
    RunsL I τ (s.link T) ρ m Q := by
  intro m' hm
  rw [run_link] at hm
  exact h m' hm

/-- **Linking a refinement theorem proved for every interpretation meeting contracts** `Ck`:
only through the induced interpretation. -/
theorem link_liberal {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {Ck : Interp Op₁ Tst K → Prop}
    {τ : Tape K} {s : Stmt Op₁ Tst} {ρ : Env} {m : Mem K} {Q : Mem K → Prop}
    (hT : ∀ J, Ck J → RunsL J τ s ρ m Q) (hk : Ck (I.link T)) : RunsL I τ (s.link T) ρ m Q :=
  (hT _ hk).link

end NLAlib.Ops
