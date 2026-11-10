/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import NLAlib.Ops.Stream
public import NLAlib.Ops.Syntax

/-!
# Interpretations and the evaluator

An interpretation `NLAlib.Ops.Interp Op Tst K` gives the meaning of every operation: the effect of a
call on the memory (it is given the tape), the Boolean of a test, the number of an index use.

## Main results

Two evaluators:

* `NLAlib.Ops.run`: the memory after a run. This is the meaning of a program.
* `NLAlib.Ops.exec`: the same run with its accounting. The evaluator, not the interpretation,
  fixes the accounting: every use of an operation counts one at the key
  `(operation, dimensions)` (`NLAlib.Ops.Count`), a call raises the peak by the workspace that
  the access model declares for it, and `alloc` by its length. `NLAlib.Ops.map_mem_exec`: the two
  agree on the memory, failures included.

A call that changes the shape of the store fails (`NLAlib.Ops.Interp.callS`).

`NLAlib.Ops.cost_le_of_exec`: a counted run only adds counts.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **An interpretation**: the meaning of every operation. `call` is the effect of a call at its
dimensions, input and output operands on the memory, given the tape; `test` and `index` are the
Boolean and the number an operation returns when it is used as a test or as an index. -/
structure Interp (Op Tst K : Type) where
  /-- The effect of a call. -/
  call : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Tape K → Mem K → Option (Mem K)
  /-- The Boolean of a test. -/
  test : Tst → List ℕ → List (ℕ × ℕ) → Mem K → Option Bool
  /-- The number of an index use. -/
  index : Tst → List (ℕ × ℕ) → Mem K → Option ℕ

/-- The call of the evaluator: the call of the interpretation, failing if an operand handle is
not a buffer of the store, or if the call changes the shape of the store. -/
def Interp.callS (I : Interp Op Tst K) (o : Op) (d : List ℕ) (ins outs : List (ℕ × ℕ))
    (τ : Tape K) (m : Mem K) : Option (Mem K) :=
  if m.Live (ins ++ outs) then
    (I.call o d ins outs τ m).bind fun m' =>
      if m'.store.shape = m.store.shape then some m' else none
  else none

theorem Interp.callS_of_live {I : Interp Op Tst K} {o : Op} {d : List ℕ}
    {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m : Mem K} (h : m.Live (ins ++ outs)) :
    I.callS o d ins outs τ m = (I.call o d ins outs τ m).bind fun m' =>
      if m'.store.shape = m.store.shape then some m' else none := if_pos h

theorem Interp.live_of_callS {I : Interp Op Tst K} {o : Op} {d : List ℕ}
    {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K}
    (h : I.callS o d ins outs τ m = some m') : m.Live (ins ++ outs) := by
  unfold Interp.callS at h
  split_ifs at h with hl
  exact hl

theorem Interp.shape_of_callS {I : Interp Op Tst K} {o : Op} {d : List ℕ}
    {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K}
    (h : I.callS o d ins outs τ m = some m') : m'.store.shape = m.store.shape := by
  rw [Interp.callS_of_live (Interp.live_of_callS h)] at h
  obtain ⟨m₁, -, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with hs
  cases h
  exact hs

/-- Bounded iteration. -/
def iter {σ : Type} (f : ℕ → σ → Option σ) : ℕ → σ → Option σ
  | 0, s => some s
  | k + 1, s => (iter f k s).bind (f k)

/-- **The loop with early exit**: at most `r` more rounds, from the round `i`. A round applies
`test` (which returns the Boolean and the state after the test); if it holds the round runs
`body` and the loop goes on, otherwise the loop ends. The result is the number of rounds done and
the state. At the cap the loop ends without a test. -/
def whileIter {σ : Type} (test : ℕ → σ → Option (Bool × σ)) (body : ℕ → σ → Option σ) :
    ℕ → ℕ → σ → Option (ℕ × σ)
  | 0, i, s => some (i, s)
  | r + 1, i, s => (test i s).bind fun bs =>
      if bs.1 then (body i bs.2).bind (whileIter test body r (i + 1)) else some (i, bs.2)

/-- The Boolean of the test `q` at the dimensions `ds` and the operands `ins`, in the
environment `ρ`. -/
def Interp.testAt (I : Interp Op Tst K) (q : Tst) (ds : List IExp) (ins : List Operand) (ρ : Env)
    (m : Mem K) : Option Bool :=
  (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a => I.test q d a m

theorem Interp.testAt_eq {I : Interp Op Tst K} {q : Tst} {ds : List IExp} {ins : List Operand}
    {ρ : Env} {m : Mem K} {d : List ℕ} {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) : I.testAt q ds ins ρ m = I.test q d a m := by
  simp [Interp.testAt, hd, ha]

/-- **The run**: the memory after a program, in the environment `ρ`, under the interpretation `I`
and the tape `τ`; `none` is failure. -/
def run (I : Interp Op Tst K) (τ : Tape K) :
    Stmt Op Tst → Env → Mem K → Option (Mem K)
  | .skip, _, m => some m
  | .abort, _, _ => none
  | .seq s t, ρ, m => (run I τ s ρ m).bind (run I τ t ρ)
  | .call o ds ins outs, ρ, m =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (Operand.evalList ρ outs).bind fun b => I.callS o d a b τ m
  | .ite q ds ins t e, ρ, m =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (I.test q d a m).bind fun c => if c then run I τ t ρ m else run I τ e ρ m
  | .whileFuel fuel q ds ins body k, ρ, m =>
      (fuel.eval ρ.idx).bind fun n =>
        (whileIter (fun i m => (I.testAt q ds ins (ρ.pushIdx i) m).map fun b => (b, m))
          (fun i => run I τ body (ρ.pushIdx i)) n 0 m).bind fun jm =>
            run I τ k (ρ.pushIdx jm.1) jm.2
  | .bindIdx q ins bound body, ρ, m =>
      (Operand.evalList ρ ins).bind fun a => (bound.eval ρ.idx).bind fun B =>
        (I.index q a m).bind fun v => if v ≤ B then run I τ body (ρ.pushIdx v) m else none
  | .alloc len body, ρ, m =>
      (len.eval ρ.idx).bind fun n =>
        (run I τ body (ρ.pushBuf m.store.length) ⟨m.store.push n, m.pos⟩).map fun m' =>
          ⟨m'.store.pop, m'.pos⟩
  | .loop n body, ρ, m =>
      (n.eval ρ.idx).bind fun k => iter (fun i m => run I τ body (ρ.pushIdx i) m) k m
  | .frame ds args body, ρ, m =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ args).bind fun a =>
        if m.Live a then run I τ body (Env.frame d a) m else none

/-- **Counts**: the number of uses of each operation and of each query at each list of
dimensions. -/
abbrev Count (Op Tst : Type) := (Op ⊕ Tst) × List ℕ →₀ ℕ

/-- One call of the operation `o` at the dimensions `d`. -/
noncomputable def Count.one (o : Op) (d : List ℕ) : Count Op Tst := Finsupp.single (.inl o, d) 1

/-- One use of the query `q` at the dimensions `d`. -/
noncomputable def Count.test (q : Tst) (d : List ℕ) : Count Op Tst :=
  Finsupp.single (.inr q, d) 1

/-- The state of a counted run: the memory, the counts, the live scratch cells and their peak. -/
structure St (Op Tst K : Type) where
  /-- The memory. -/
  mem : Mem K
  /-- The counts so far. -/
  cost : Count Op Tst
  /-- The scratch cells now allocated. -/
  cur : ℕ
  /-- The peak of scratch cells, workspaces of operations included. -/
  peak : ℕ

/-- The state at the start of a run: no counts, no scratch. -/
def St.init (m : Mem K) : St Op Tst K := ⟨m, 0, 0, 0⟩

/-- Count one use of the query `q` at `d`. -/
noncomputable def St.tick (st : St Op Tst K) (q : Tst) (d : List ℕ) : St Op Tst K :=
  ⟨st.mem, st.cost + Count.test q d, st.cur, st.peak⟩

/-- The counted test of a loop round: the Boolean of the test `q` and the state with one more
use of `q` at its dimensions. -/
noncomputable def Interp.testSt (I : Interp Op Tst K) (q : Tst) (ds : List IExp)
    (ins : List Operand) (ρ : Env) (st : St Op Tst K) : Option (Bool × St Op Tst K) :=
  (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
    (I.test q d a st.mem).map fun b => (b, st.tick q d)

theorem Interp.testSt_eq {I : Interp Op Tst K} {q : Tst} {ds : List IExp} {ins : List Operand}
    {ρ : Env} {st : St Op Tst K} {d : List ℕ} {a : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a) :
    I.testSt q ds ins ρ st = (I.test q d a st.mem).map fun b => (b, st.tick q d) := by
  simp [Interp.testSt, hd, ha]

/-- A counted test that succeeds: the dimensions, the Boolean and the state. -/
theorem Interp.testSt_eq_some {I : Interp Op Tst K} {q : Tst} {ds : List IExp}
    {ins : List Operand} {ρ : Env} {st : St Op Tst K} {bs : Bool × St Op Tst K}
    (h : I.testSt q ds ins ρ st = some bs) :
    ∃ d, IExp.evalList ρ.idx ds = some d ∧ I.testAt q ds ins ρ st.mem = some bs.1 ∧
      bs.2 = st.tick q d := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨d, hd, by simp [Interp.testAt, hd, ha, hb], rfl⟩

/-- **The counted run.** `W o d` is the workspace, in cells, that the access model declares for a
call of `o` at the dimensions `d`. -/
noncomputable def exec (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) :
    Stmt Op Tst → Env → St Op Tst K → Option (St Op Tst K)
  | .skip, _, st => some st
  | .abort, _, _ => none
  | .seq s t, ρ, st => (exec I W τ s ρ st).bind (exec I W τ t ρ)
  | .call o ds ins outs, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (Operand.evalList ρ outs).bind fun b => (I.callS o d a b τ st.mem).map fun m' =>
          ⟨m', st.cost + Count.one o d, st.cur, max st.peak (st.cur + W o d)⟩
  | .ite q ds ins t e, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (I.test q d a st.mem).bind fun c =>
          if c then exec I W τ t ρ (st.tick q d) else exec I W τ e ρ (st.tick q d)
  | .whileFuel fuel q ds ins body k, ρ, st =>
      (fuel.eval ρ.idx).bind fun n =>
        (whileIter (fun i st => I.testSt q ds ins (ρ.pushIdx i) st)
          (fun i => exec I W τ body (ρ.pushIdx i)) n 0 st).bind fun jst =>
            exec I W τ k (ρ.pushIdx jst.1) jst.2
  | .bindIdx q ins bound body, ρ, st =>
      (Operand.evalList ρ ins).bind fun a => (bound.eval ρ.idx).bind fun B =>
        (I.index q a st.mem).bind fun v =>
          if v ≤ B then exec I W τ body (ρ.pushIdx v) (st.tick q []) else none
  | .alloc len body, ρ, st =>
      (len.eval ρ.idx).bind fun n =>
        (exec I W τ body (ρ.pushBuf st.mem.store.length)
          ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.cost, st.cur + n,
            max st.peak (st.cur + n)⟩).map fun st' =>
          ⟨⟨st'.mem.store.pop, st'.mem.pos⟩, st'.cost, st.cur, st'.peak⟩
  | .loop n body, ρ, st =>
      (n.eval ρ.idx).bind fun k => iter (fun i st => exec I W τ body (ρ.pushIdx i) st) k st
  | .frame ds args body, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ args).bind fun a =>
        if st.mem.Live a then exec I W τ body (Env.frame d a) st else none

/-! ### The counted run and the run agree on the memory -/

theorem Option.map_bind_of_comm {α β α' β' : Type} {g : α → α'} {g' : β → β'}
    {f : α → Option β} {f' : α' → Option β'} (x : Option α)
    (h : ∀ a, (f a).map g' = f' (g a)) : (x.bind f).map g' = (x.map g).bind f' := by
  cases x with
  | none => rfl
  | some a => exact h a

theorem map_iter {σ σ' : Type} {g : σ → σ'} {f : ℕ → σ → Option σ} {f' : ℕ → σ' → Option σ'}
    (h : ∀ i a, (f i a).map g = f' i (g a)) (k : ℕ) (s : σ) :
    (iter f k s).map g = iter f' k (g s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iter]
    rw [Option.map_bind_of_comm _ (h k), ih]

theorem map_whileIter {σ σ' : Type} {g : σ → σ'} {test : ℕ → σ → Option (Bool × σ)}
    {body : ℕ → σ → Option σ} {test' : ℕ → σ' → Option (Bool × σ')}
    {body' : ℕ → σ' → Option σ'}
    (ht : ∀ i a, (test i a).map (Prod.map id g) = test' i (g a))
    (hb : ∀ i a, (body i a).map g = body' i (g a)) (r i : ℕ) (s : σ) :
    (whileIter test body r i s).map (Prod.map id g) = whileIter test' body' r i (g s) := by
  induction r generalizing i s with
  | zero => rfl
  | succ r ih =>
    simp only [whileIter, ← ht]
    cases test i s with
    | none => rfl
    | some bs =>
      obtain ⟨b, s₁⟩ := bs
      cases b with
      | false => rfl
      | true =>
        simp only [Option.bind_some, if_true, Option.map_some, Prod.map_apply, id]
        rw [Option.map_bind_of_comm _ (fun a => ih (i + 1) a), hb]

/-- **The counted run and the run end in the same memory, or both fail.** -/
theorem map_mem_exec (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst)
    (ρ : Env)
    (st : St Op Tst K) : (exec I W τ s ρ st).map (·.mem) = run I τ s ρ st.mem := by
  induction s generalizing ρ st with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht =>
    simp only [exec, run]
    rw [Option.map_bind_of_comm _ (fun a => iht ρ a), ihs]
  | call o ds ins outs =>
    simp only [exec, run]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;>
      cases Operand.evalList ρ outs <;> simp [Option.map_map, Function.comp_def]
  | ite q ds ins t e iht ihe =>
    simp only [exec, run]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;> try rfl
    rename_i d a
    simp only [Option.bind_some]
    cases I.test q d a st.mem with
    | none => rfl
    | some c => cases c <;> simp [iht, ihe, St.tick]
  | whileFuel fuel q ds ins body k ih ihk =>
    simp only [exec, run]
    cases fuel.eval ρ.idx with
    | none => rfl
    | some n =>
      simp only [Option.bind_some]
      rw [Option.map_bind_of_comm (g := Prod.map id fun x : St Op Tst K => x.mem)
        (f' := fun jm : ℕ × Mem K => run I τ k (ρ.pushIdx jm.1) jm.2) _
        (fun a => ihk (ρ.pushIdx a.1) a.2)]
      rw [map_whileIter (g := fun x : St Op Tst K => x.mem)
        (test' := fun i m => (I.testAt q ds ins (ρ.pushIdx i) m).map fun b => (b, m))
        (body' := fun i => run I τ body (ρ.pushIdx i)) (fun i a => ?_)
        (fun i a => ih (ρ.pushIdx i) a)]
      · simp only [Interp.testSt, Interp.testAt]
        cases IExp.evalList (ρ.pushIdx i).idx ds <;>
          cases Operand.evalList (ρ.pushIdx i) ins <;> try rfl
        rename_i d a'
        simp only [Option.bind_some]
        cases I.test q d a' a.mem <;> rfl
  | bindIdx q ins bound body ih =>
    simp only [exec, run]
    cases Operand.evalList ρ ins <;> cases bound.eval ρ.idx <;> try rfl
    rename_i a B
    simp only [Option.bind_some]
    cases I.index q a st.mem with
    | none => rfl
    | some v => by_cases hv : v ≤ B <;> simp [hv, ih, St.tick]
  | alloc len body ih =>
    simp only [exec, run]
    cases len.eval ρ.idx with
    | none => rfl
    | some n =>
      have h := ih (ρ.pushBuf st.mem.store.length)
        ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.cost, st.cur + n, max st.peak (st.cur + n)⟩
      simp only [Option.bind_some, ← h, Option.map_map]
      rfl
  | loop n body ih =>
    simp only [exec, run]
    cases n.eval ρ.idx with
    | none => rfl
    | some k => exact map_iter (fun i a => ih (ρ.pushIdx i) a) _ _
  | frame ds args body ih =>
    simp only [exec, run]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ args <;> try rfl
    simp only [Option.bind_some]
    split_ifs
    · exact ih _ _
    · rfl

/-- A counted run succeeds exactly when the run does. -/
theorem exec_eq_some_of_run {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env}
    {m m' : Mem K}
    (h : run I τ s ρ m = some m') (W : Op → List ℕ → ℕ) (st : St Op Tst K) (hm : st.mem = m) :
    ∃ st', exec I W τ s ρ st = some st' ∧ st'.mem = m' := by
  have e := map_mem_exec I W τ s ρ st
  rw [hm, h] at e
  obtain ⟨st', h1, h2⟩ := Option.map_eq_some_iff.mp e
  exact ⟨st', h1, h2⟩

theorem run_of_exec {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {s : Stmt Op Tst}
    {ρ : Env}
    {st st' : St Op Tst K} (h : exec I W τ s ρ st = some st') :
    run I τ s ρ st.mem = some st'.mem := by
  rw [← map_mem_exec I W τ s ρ st, h]
  rfl

/-! ### A run keeps the shape of the store -/

theorem iter_rel {σ : Type} {R : σ → σ → Prop} (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) {f : ℕ → σ → Option σ}
    (h : ∀ i a b, f i a = some b → R a b) {k : ℕ} {s s' : σ} (hk : iter f k s = some s') :
    R s s' := by
  induction k generalizing s' with
  | zero => cases hk; exact hrefl _
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    exact htrans _ _ _ (ih ha) (h k a s' hb)

/-- A relation that every test and every body keeps holds between the start and the end of a loop
with early exit, which does at most the rounds it is given. -/
theorem whileIter_rel {σ : Type} {R : σ → σ → Prop} (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) {test : ℕ → σ → Option (Bool × σ)}
    {body : ℕ → σ → Option σ} (ht : ∀ i a bs, test i a = some bs → R a bs.2)
    (h : ∀ i a b, body i a = some b → R a b) {r i : ℕ} {s : σ} {js : ℕ × σ}
    (hk : whileIter test body r i s = some js) : R s js.2 ∧ i ≤ js.1 ∧ js.1 ≤ i + r := by
  induction r generalizing i s with
  | zero => cases hk; exact ⟨hrefl _, le_rfl, le_rfl⟩
  | succ r ih =>
    obtain ⟨bs, hbs, hb⟩ := Option.bind_eq_some_iff.mp hk
    split_ifs at hb with hc
    · obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨h1, h2, h3⟩ := ih hb
      exact ⟨htrans _ _ _ (ht i s bs hbs) (htrans _ _ _ (h _ _ _ ha) h1), by omega, by omega⟩
    · cases hb
      exact ⟨ht i s bs hbs, le_rfl, by omega⟩

/-- **A run keeps the shape of the store**: buffers are neither created, resized nor freed behind
the program's back. -/
theorem shape_store_of_run {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env}
    {m m' : Mem K}
    (h : run I τ s ρ m = some m') : m'.store.shape = m.store.shape := by
  induction s generalizing ρ m m' with
  | skip => cases h; rfl
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    exact (iht hb).trans (ihs ha)
  | call o ds ins outs =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact Interp.shape_of_callS h
  | ite q ds ins t e iht ihe =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases c
    · exact ihe h
    · exact iht h
  | whileFuel fuel q ds ins body k ih ihk =>
    obtain ⟨n, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨jm, hw, h⟩ := Option.bind_eq_some_iff.mp h
    refine (ihk h).trans (whileIter_rel (R := fun a b : Mem K => b.store.shape = a.store.shape)
      (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) (fun i a bs hbs => ?_)
      (fun _ _ _ hb => ih hb) hw).1
    obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hbs
    rfl
  | bindIdx q ins bound body ih =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    exact ih h
  | alloc len body ih =>
    obtain ⟨n, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    have := ih h₂
    simp only [Store.push, Store.shape_append] at this
    change m₂.store.pop.shape = m.store.shape
    rw [Store.shape_pop, this]
    simp [Store.shape]
  | loop n body ih =>
    obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact iter_rel (R := fun a b : Mem K => b.store.shape = a.store.shape) (fun _ => rfl)
      (fun _ _ _ h1 h2 => h2.trans h1) (fun _ _ _ hb => ih hb) h
  | frame ds args body ih =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    exact ih h

/-! ### A counted run only adds counts -/

/-- **A counted run only adds counts**, so the counts of a run from a state are those of the
state plus an increment. -/
theorem cost_le_of_exec {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {st st' : St Op Tst K} (h : exec I W τ s ρ st = some st') :
    st.cost ≤ st'.cost := by
  induction s generalizing ρ st st' with
  | skip => cases h; exact le_rfl
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    exact (ihs ha).trans (iht hb)
  | call o ds ins outs =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact le_self_add
  | ite q ds ins t e iht ihe =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    have ht : st.cost ≤ (st.tick q d).cost := le_self_add
    cases c
    · exact ht.trans (ihe h)
    · exact ht.trans (iht h)
  | whileFuel fuel q ds ins body k ih ihk =>
    obtain ⟨n, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨jst, hw, h⟩ := Option.bind_eq_some_iff.mp h
    refine (whileIter_rel (R := fun a b : St Op Tst K => a.cost ≤ b.cost) (fun _ => le_rfl)
      (fun _ _ _ h1 h2 => h1.trans h2) (fun i a bs hbs => ?_) (fun _ _ _ hb => ih hb) hw).1.trans
      (ihk h)
    obtain ⟨d, -, -, e⟩ := Interp.testSt_eq_some hbs
    rw [e]
    exact le_self_add
  | bindIdx q ins bound body ih =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    exact (le_self_add : st.cost ≤ (st.tick q []).cost).trans (ih h)
  | alloc len body ih =>
    obtain ⟨n, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    have h₃ := ih h₂
    exact h₃
  | loop n body ih =>
    obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact iter_rel (R := fun a b : St Op Tst K => a.cost ≤ b.cost) (fun _ => le_rfl)
      (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ hb => ih hb) h
  | frame ds args body ih =>
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    exact ih h

end NLAlib.Ops
