/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Rules
public import NLAlib.Ops.Transfer

/-!
# Counts in the logic, where they depend on the data

The counts of a program are its static cost (`NLAlib.Ops.Runs.of_run`), and the logic `Wp` does
not carry them. The static cost is only a bound where the counts depend on the data: a size read
from the store (`bindIdx` is charged at every value up to its bound), a branch, a loop with early
exit. `NLAlib.Ops.RunsFromW` is the judgment that carries the counts exactly: a counted run from
a state, whose postcondition is given **the counts that the run added** and the final memory.
So a bound may depend on the data, the bound of a continuation may depend on the state it starts
from, and a weighted bound (`∀ T` monotone and superadditive, …) is a postcondition like any
other.

One rule per constructor: `skip`, `seq` (the continuation is proved from the state and the
counts reached), `call` (one call, at its dimensions), `ite`, `bindIdx` (charged at the value
read), `alloc`, `loop` (an invariant on the counts so far and the memory), `whileFuel`, `frame`;
and `NLAlib.Ops.RunsFromW.of_wp` takes everything whose counts do not depend on the data from
`Wp` with its static cost. A `RunsFromW` from the initial state is a `NLAlib.Ops.RunsW`
(`NLAlib.Ops.RunsFromW.runsW`) or a `NLAlib.Ops.Runs` (`NLAlib.Ops.RunsFromW.runs`), which
linking transfers (`NLAlib.Ops.RunsW.link`, `NLAlib.Ops.exec_link_weight`).

`NLAlib.Ops.RunsFromWL` is the same judgment for **partial correctness**: if the counted run
from the state succeeds, it stays within the workspace and the postcondition holds of the counts
added and the final memory. It has the same rules, read in parallel: where the total rule is
given the Boolean of a test, the value of a conversion or a live frame, the liberal rule is
proved for every Boolean the test may return, every value within the bound, and under the
hypothesis that the frame is live; `abort` is vacuous. `NLAlib.Ops.RunsFromWL.of_static` is the
static count with no hypothesis at all (`NLAlib.Ops.exec_within`). It says nothing of success, so
a target never rests on it alone; what it is for is the accounting certificate of an
implementation, which speaks of every successful run
(`NLAlib.Ops.Table.AccountsW.of_runsFromWL`).

## Main results

* `NLAlib.Ops.RunsFromW`: the judgment.
* `NLAlib.Ops.RunsFromW.seq`, `NLAlib.Ops.RunsFromW.bindIdx`, `NLAlib.Ops.RunsFromW.loop`,
  `NLAlib.Ops.RunsFromW.whileFuel` and the other rules.
* `NLAlib.Ops.RunsFromW.of_wp`, `NLAlib.Ops.RunsFromW.runsW`, `NLAlib.Ops.RunsFromW.runs`.
* `NLAlib.Ops.RunsFromWL`: the liberal judgment, with `skip`, `abort`, `seq`, `call`, `ite`,
  `bindIdx`, `alloc`, `frame`, `loop`, `whileFuel`, `mono`, `and`, `of_static`, `of_wp`.
* `NLAlib.Ops.RunsFromWL.of_runsFromW`, `NLAlib.Ops.RunsFromWL.runsFromW`: total and liberal.
* `NLAlib.Ops.RunsFromWL.link_from`, `NLAlib.Ops.RunsFromWL.link`: linking from counted
  states and from the initial state.
* `NLAlib.Ops.Table.AccountsW.of_runsFromWL`, `NLAlib.Ops.RunsFromWL.runsL`,
  `NLAlib.Ops.RunsFromWL.exec_init`: the table certificate and the forms from the initial state.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- The state `b` is reached from `a` with exactly the counts `c` added, the same live cells and
a peak at most `p` above them. -/
def St.Reach (a b : St Op Tst K) (c : Count Op Tst) (p : ℕ) : Prop :=
  b.cost = a.cost + c ∧ b.cur = a.cur ∧ b.peak ≤ max a.peak (a.cur + p)

namespace St.Reach

theorem refl (a : St Op Tst K) (p : ℕ) : St.Reach a a 0 p := ⟨by simp, rfl, by simp⟩

theorem trans {a b d : St Op Tst K} {c c' : Count Op Tst} {p p' : ℕ} (h : St.Reach a b c p)
    (h' : St.Reach b d c' p') : St.Reach a d (c + c') (max p p') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨by rw [h1', h1, add_assoc], h2'.trans h2, ?_⟩
  rw [h2] at h3'
  omega

theorem tick (a : St Op Tst K) (q : Tst) (d : List ℕ) (p : ℕ) :
    St.Reach a (a.tick q d) (Count.test q d) p := ⟨rfl, rfl, by simp [St.tick]⟩

end St.Reach

/-- **A counted run from a state, whose postcondition sees the counts**: the counted run of `s`
from `st` succeeds, stays within the workspace `p` above the live cells, and `Q` holds of the
counts that the run added and of the final memory. -/
def RunsFromW (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst)
    (ρ : Env) (st : St Op Tst K) (p : ℕ) (Q : Count Op Tst → Mem K → Prop) : Prop :=
  ∃ st' c, exec I W τ s ρ st = some st' ∧ St.Reach st st' c p ∧ Q c st'.mem

namespace RunsFromW

variable {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {ρ : Env} {st : St Op Tst K}
  {p p' : ℕ} {Q Q' : Count Op Tst → Mem K → Prop}

/-- Everything whose counts do not depend on the data: a total `Wp` and the static cost. -/
theorem of_wp {s : Stmt Op Tst} {P : Mem K → Prop} (h : Wp .total I τ s ρ P st.mem) :
    RunsFromW I W τ s ρ st (staticPeak W s ρ.idx) fun c m => c ≤ staticCost s ρ.idx ∧ P m := by
  obtain ⟨m', hrun, hQ⟩ := h
  obtain ⟨st', hst, hm⟩ := exec_eq_some_of_run hrun W st rfl
  obtain ⟨h1, h2, h3⟩ := exec_within hst
  obtain ⟨c, hc⟩ := exists_add_of_le (cost_le_of_exec hst)
  exact ⟨st', c, hst, ⟨hc, h1, h3⟩, by rwa [hc, add_le_add_iff_left] at h2, hm ▸ hQ⟩

theorem mono {s : Stmt Op Tst} (h : RunsFromW I W τ s ρ st p Q) (hp : p ≤ p')
    (hQ : ∀ c m, Q c m → Q' c m) : RunsFromW I W τ s ρ st p' Q' := by
  obtain ⟨st', c, h1, ⟨h2, h3, h4⟩, h5⟩ := h
  exact ⟨st', c, h1, ⟨h2, h3, by omega⟩, hQ _ _ h5⟩

theorem skip (h : Q 0 st.mem) : RunsFromW I W τ .skip ρ st p Q :=
  ⟨st, 0, rfl, St.Reach.refl st p, h⟩

/-- **Sequence**: the continuation is proved from the state reached, with the counts so far; its
bound may depend on both. The workspaces take their maximum. -/
theorem seq {s t : Stmt Op Tst} (h : RunsFromW I W τ s ρ st p Q')
    (h' : ∀ st' c, Q' c st'.mem → RunsFromW I W τ t ρ st' p' fun c' m => Q (c + c') m) :
    RunsFromW I W τ (.seq s t) ρ st (max p p') Q := by
  obtain ⟨st₁, c₁, h1, h2, h3⟩ := h
  obtain ⟨st₂, c₂, h4, h5, h6⟩ := h' st₁ c₁ h3
  exact ⟨st₂, c₁ + c₂, by simp only [exec, h1, Option.bind_some, h4], h2.trans h5, h6⟩

/-- **A call**: one call at its dimensions, and the workspace of the operation. The memory is
taken from `Wp`, by any call rule. -/
theorem call {o : Op} {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {P : Mem K → Prop} (hd : IExp.evalList ρ.idx ds = some d)
    (h : Wp .total I τ (.call o ds ins outs) ρ P st.mem) :
    RunsFromW I W τ (.call o ds ins outs) ρ st (W o d) fun c m => c = Count.one o d ∧ P m := by
  obtain ⟨m', hrun, hP⟩ := h
  simp only [run, hd, Option.bind_some] at hrun
  obtain ⟨a, ha, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  exact ⟨⟨m', st.cost + Count.one o d, st.cur, max st.peak (st.cur + W o d)⟩, Count.one o d,
    by simp [exec, hd, ha, hb, hrun], ⟨rfl, rfl, le_rfl⟩, rfl, hP⟩

/-- **Branch**: one use of the test, then the branch taken. -/
theorem ite {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} {b : Bool} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : I.test q d a st.mem = some b)
    (h : RunsFromW I W τ (if b then t else e) ρ (st.tick q d) p
      fun c m => Q (Count.test q d + c) m) : RunsFromW I W τ (.ite q ds ins t e) ρ st p Q := by
  obtain ⟨st', c, h1, h2, h3⟩ := h
  refine ⟨st', Count.test q d + c, ?_, by simpa using (St.Reach.tick st q d p).trans h2, h3⟩
  cases b <;> simpa [exec, hd, ha, hb] using h1

/-- **Index binder**: one use of the query, then the body **at the value read**, which is
charged for that value only. -/
theorem bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B v : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B) (hv : I.index q a st.mem = some v) (hle : v ≤ B)
    (h : RunsFromW I W τ body (ρ.pushIdx v) (st.tick q []) p
      fun c m => Q (Count.test q [] + c) m) :
    RunsFromW I W τ (.bindIdx q ins bound body) ρ st p Q := by
  obtain ⟨st', c, h1, h2, h3⟩ := h
  exact ⟨st', Count.test q [] + c, by simpa [exec, ha, hB, hv, hle] using h1,
    by simpa using (St.Reach.tick st q [] p).trans h2, h3⟩

/-- **Scratch buffer**: the body runs with the new buffer on top, which is then popped; the
workspace is that of the body above the buffer. -/
theorem alloc {len : IExp} {body : Stmt Op Tst} {n : ℕ} (hn : len.eval ρ.idx = some n)
    (h : RunsFromW I W τ body (ρ.pushBuf st.mem.store.length)
      ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.cost, st.cur + n, max st.peak (st.cur + n)⟩ p
      fun c m' => Q c ⟨m'.store.pop, m'.pos⟩) :
    RunsFromW I W τ (.alloc len body) ρ st (n + p) Q := by
  obtain ⟨st', c, h1, ⟨h2, h3, h4⟩, h5⟩ := h
  refine ⟨⟨⟨st'.mem.store.pop, st'.mem.pos⟩, st'.cost, st.cur, st'.peak⟩, c,
    by simp only [exec, hn, Option.bind_some, h1, Option.map_some], ⟨h2, rfl, ?_⟩, h5⟩
  simp only at h4 ⊢
  omega

/-- Procedure instance. -/
theorem frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a) (hl : st.mem.Live a)
    (h : RunsFromW I W τ body (Env.frame d a) st p Q) :
    RunsFromW I W τ (.frame ds args body) ρ st p Q := by
  obtain ⟨st', c, h1, h2, h3⟩ := h
  exact ⟨st', c, by simpa only [exec, hd, ha, Option.bind_some, if_pos hl] using h1, h2, h3⟩

/-- **Loop**, with an invariant on the counts added so far and the memory, indexed by the number
of rounds done: the bound of a round comes from the invariant. -/
theorem loop {n : IExp} {body : Stmt Op Tst} {k : ℕ} (hn : n.eval ρ.idx = some k)
    (Inv : ℕ → Count Op Tst → Mem K → Prop) (h0 : Inv 0 0 st.mem)
    (hstep : ∀ i < k, ∀ st' c, Inv i c st'.mem →
      RunsFromW I W τ body (ρ.pushIdx i) st' p fun c' m => Inv (i + 1) (c + c') m) :
    RunsFromW I W τ (.loop n body) ρ st p (Inv k) := by
  have key : ∀ j ≤ k, ∃ st' c, iter (fun i st => exec I W τ body (ρ.pushIdx i) st) j st =
      some st' ∧ St.Reach st st' c p ∧ Inv j c st'.mem := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨st, 0, rfl, St.Reach.refl st p, h0⟩
    | succ j ih =>
      intro hj
      obtain ⟨st₁, c₁, h1, h2, h3⟩ := ih (by omega)
      obtain ⟨st₂, c₂, h4, h5, h6⟩ := hstep j (by omega) st₁ c₁ h3
      exact ⟨st₂, c₁ + c₂, by simp only [iter, h1, Option.bind_some, h4],
        by simpa using h2.trans h5, h6⟩
  obtain ⟨st', c, h1, h2, h3⟩ := key k le_rfl
  exact ⟨st', c, by simp only [exec, hn, Option.bind_some, h1], h2, h3⟩

/-- **The loop with early exit**, with an invariant on the counts added so far and the memory.
At a round below the cap the test is used once: if it holds the body keeps the invariant,
otherwise the continuation runs with the round index. At the cap the continuation runs without a
test. The counts are those of the rounds that were done. -/
theorem whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} {n : ℕ} (hn : fuel.eval ρ.idx = some n)
    (Inv : ℕ → Count Op Tst → Mem K → Prop) (h0 : Inv 0 0 st.mem)
    (hstep : ∀ i < n, ∀ (st' : St Op Tst K) c, Inv i c st'.mem → ∃ d a b,
      IExp.evalList (ρ.pushIdx i).idx ds = some d ∧ Operand.evalList (ρ.pushIdx i) ins = some a ∧
      I.test q d a st'.mem = some b ∧
      if b then RunsFromW I W τ body (ρ.pushIdx i) (st'.tick q d) p
          fun c' m => Inv (i + 1) (c + (Count.test q d + c')) m
        else RunsFromW I W τ k (ρ.pushIdx i) (st'.tick q d) p
          fun c' m => Q (c + (Count.test q d + c')) m)
    (hcap : ∀ (st' : St Op Tst K) c, Inv n c st'.mem →
      RunsFromW I W τ k (ρ.pushIdx n) st' p fun c' m => Q (c + c') m) :
    RunsFromW I W τ (.whileFuel fuel q ds ins body k) ρ st p Q := by
  have key : ∀ (r i : ℕ) (st₁ : St Op Tst K) (c₁ : Count Op Tst), i + r = n →
      St.Reach st st₁ c₁ p → Inv i c₁ st₁.mem → ∃ st' c,
        ((whileIter (fun i st => I.testSt q ds ins (ρ.pushIdx i) st)
          (fun i => exec I W τ body (ρ.pushIdx i)) r i st₁).bind fun jst =>
            exec I W τ k (ρ.pushIdx jst.1) jst.2) = some st' ∧
        St.Reach st st' c p ∧ Q c st'.mem := by
    intro r
    induction r with
    | zero =>
      intro i st₁ c₁ hi hr hinv
      obtain rfl : i = n := by omega
      obtain ⟨st₂, c₂, h1, h2, h3⟩ := hcap st₁ c₁ hinv
      exact ⟨st₂, c₁ + c₂, by simpa [whileIter] using h1, by simpa using hr.trans h2, h3⟩
    | succ r ih =>
      intro i st₁ c₁ hi hr hinv
      obtain ⟨d, a, b, hd, ha, hb, hrun⟩ := hstep i (by omega) st₁ c₁ hinv
      have ht : I.testSt q ds ins (ρ.pushIdx i) st₁ = some (b, st₁.tick q d) := by
        rw [Interp.testSt_eq hd ha, hb]
        rfl
      have hr' := hr.trans (St.Reach.tick st₁ q d p)
      cases b with
      | false =>
        obtain ⟨st₂, c₂, h1, h2, h3⟩ := hrun
        exact ⟨st₂, c₁ + Count.test q d + c₂, by simpa [whileIter, ht] using h1,
          by simpa using hr'.trans h2, by simpa [add_assoc] using h3⟩
      | true =>
        obtain ⟨st₂, c₂, h1, h2, h3⟩ := hrun
        obtain ⟨st₃, c₃, h4, h5, h6⟩ := ih (i + 1) st₂ (c₁ + Count.test q d + c₂) (by omega)
          (by simpa using hr'.trans h2) (by simpa [add_assoc] using h3)
        exact ⟨st₃, c₃, by simpa [whileIter, ht, h1, Option.bind_assoc] using h4, h5, h6⟩
  obtain ⟨st', c, h1, h2, h3⟩ := key n 0 st 0 (by omega) (St.Reach.refl st p) h0
  exact ⟨st', c, by simp only [exec, hn, Option.bind_some, h1], h2, h3⟩

/-- A counted run from the initial state is a run whose postcondition sees the counts. -/
theorem runsW {s : Stmt Op Tst} {m : Mem K} (h : RunsFromW I W τ s ρ (St.init m) p Q) :
    RunsW I W τ s ρ m p Q := by
  obtain ⟨st', c, h1, ⟨h2, -, h3⟩, h4⟩ := h
  refine ⟨st', h1, by simpa [St.init] using h3, ?_⟩
  have e : st'.cost = c := by simpa [St.init] using h2
  exact e ▸ h4

/-- A counted run from the initial state whose counts are within `B` is a run within the
budget. -/
theorem runs {s : Stmt Op Tst} {m : Mem K} {B : Count Op Tst} {P : Mem K → Prop}
    (h : RunsFromW I W τ s ρ (St.init m) p fun c m' => c ≤ B ∧ P m') : Runs I W τ s ρ m B p P :=
  runs_iff_runsW.mpr h.runsW

end RunsFromW

/-- **A counted run from a state, partial correctness**: if the counted run of `s` from `st`
succeeds, it stays within the workspace `p` above the live cells, and `Q` holds of the counts
that the run added and of the final memory. It says nothing of success: a target never rests on
it alone. -/
def RunsFromWL (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst)
    (ρ : Env) (st : St Op Tst K) (p : ℕ) (Q : Count Op Tst → Mem K → Prop) : Prop :=
  ∀ st', exec I W τ s ρ st = some st' → ∃ c, St.Reach st st' c p ∧ Q c st'.mem

namespace RunsFromWL

variable {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {ρ : Env} {st : St Op Tst K}
  {p p' : ℕ} {Q Q' : Count Op Tst → Mem K → Prop}

/-- A total counted run is a liberal one. -/
theorem of_runsFromW {s : Stmt Op Tst} (h : RunsFromW I W τ s ρ st p Q) :
    RunsFromWL I W τ s ρ st p Q := by
  obtain ⟨st', c, h1, h2, h3⟩ := h
  intro st'' hst
  obtain rfl : st' = st'' := Option.some.inj (h1.symm.trans hst)
  exact ⟨c, h2, h3⟩

/-- A liberal counted run of a program that succeeds (a total `Wp`, with any postcondition) is a
total one. -/
theorem runsFromW {s : Stmt Op Tst} {P : Mem K → Prop} (h : RunsFromWL I W τ s ρ st p Q)
    (hs : Wp .total I τ s ρ P st.mem) :
    RunsFromW I W τ s ρ st p fun c m => Q c m ∧ P m := by
  obtain ⟨m', hrun, hP⟩ := hs
  obtain ⟨st', hst, hm⟩ := exec_eq_some_of_run hrun W st rfl
  obtain ⟨c, h1, h2⟩ := h st' hst
  exact ⟨st', c, hst, h1, h2, hm ▸ hP⟩

/-- **The static count and workspace, with no hypothesis**: every successful counted run is
within them (`NLAlib.Ops.exec_within`). -/
theorem of_static (s : Stmt Op Tst) :
    RunsFromWL I W τ s ρ st (staticPeak W s ρ.idx) fun c _ => c ≤ staticCost s ρ.idx := by
  intro st' hst
  obtain ⟨h1, h2, h3⟩ := exec_within hst
  obtain ⟨c, hc⟩ := exists_add_of_le (cost_le_of_exec hst)
  exact ⟨c, ⟨hc, h1, h3⟩, by rwa [hc, add_le_add_iff_left] at h2⟩

/-- Everything whose counts do not depend on the data: a liberal `Wp` and the static cost. -/
theorem of_wp {s : Stmt Op Tst} {P : Mem K → Prop} (h : Wp .liberal I τ s ρ P st.mem) :
    RunsFromWL I W τ s ρ st (staticPeak W s ρ.idx) fun c m => c ≤ staticCost s ρ.idx ∧ P m := by
  intro st' hst
  obtain ⟨c, h1, h2⟩ := of_static s st' hst
  exact ⟨c, h1, h2, h _ (run_of_exec hst)⟩

theorem mono {s : Stmt Op Tst} (h : RunsFromWL I W τ s ρ st p Q) (hp : p ≤ p')
    (hQ : ∀ c m, Q c m → Q' c m) : RunsFromWL I W τ s ρ st p' Q' := by
  intro st' hst
  obtain ⟨c, ⟨h2, h3, h4⟩, h5⟩ := h st' hst
  exact ⟨c, ⟨h2, h3, by omega⟩, hQ _ _ h5⟩

/-- Two postconditions of the same run hold together: the counts added are determined by the
run. -/
theorem and {s : Stmt Op Tst} (h : RunsFromWL I W τ s ρ st p Q)
    (h' : RunsFromWL I W τ s ρ st p' Q') :
    RunsFromWL I W τ s ρ st (min p p') fun c m => Q c m ∧ Q' c m := by
  intro st' hst
  obtain ⟨c, ⟨h2, h3, h4⟩, h5⟩ := h st' hst
  obtain ⟨c', ⟨h2', -, h4'⟩, h5'⟩ := h' st' hst
  obtain rfl : c = c' := add_left_cancel (h2.symm.trans h2')
  exact ⟨c, ⟨h2, h3, by omega⟩, h5, h5'⟩

theorem skip (h : Q 0 st.mem) : RunsFromWL I W τ .skip ρ st p Q :=
  of_runsFromW (RunsFromW.skip h)

/-- **Failure**: nothing to prove. An implementation that fails outside its shape is accounted
for at no cost. -/
theorem abort : RunsFromWL I W τ .abort ρ st p Q := fun _ h => by cases h

/-- **Sequence**: the continuation is proved from every state the first part may reach, with
the counts so far; its bound may depend on both. The workspaces take their maximum. -/
theorem seq {s t : Stmt Op Tst} (h : RunsFromWL I W τ s ρ st p Q')
    (h' : ∀ st' c, Q' c st'.mem → RunsFromWL I W τ t ρ st' p' fun c' m => Q (c + c') m) :
    RunsFromWL I W τ (.seq s t) ρ st (max p p') Q := by
  intro st₂ hst
  obtain ⟨st₁, h1, h4⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨c₁, h2, h3⟩ := h st₁ h1
  obtain ⟨c₂, h5, h6⟩ := h' st₁ c₁ h3 st₂ h4
  exact ⟨c₁ + c₂, h2.trans h5, h6⟩

/-- **A call**: one call at its dimensions, and the workspace of the operation. The memory is
taken from a liberal `Wp`, by any call rule (`fun _ _ => trivial` when only the counts
matter). -/
theorem call {o : Op} {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {P : Mem K → Prop} (hd : IExp.evalList ρ.idx ds = some d)
    (h : Wp .liberal I τ (.call o ds ins outs) ρ P st.mem) :
    RunsFromWL I W τ (.call o ds ins outs) ρ st (W o d) fun c m => c = Count.one o d ∧ P m := by
  intro st' hst
  have hP := h _ (run_of_exec hst)
  simp only [exec, hd, Option.bind_some] at hst
  obtain ⟨a, -, hst⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨b, -, hst⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨m', -, rfl⟩ := Option.map_eq_some_iff.mp hst
  exact ⟨Count.one o d, ⟨rfl, rfl, le_rfl⟩, rfl, hP⟩

/-- **Branch**: one use of the test, then the branch taken, for every Boolean that the test may
return. -/
theorem ite {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a)
    (h : ∀ b, I.test q d a st.mem = some b →
      RunsFromWL I W τ (if b then t else e) ρ (st.tick q d) p
        fun c m => Q (Count.test q d + c) m) : RunsFromWL I W τ (.ite q ds ins t e) ρ st p Q := by
  intro st' hst
  simp only [exec, hd, ha, Option.bind_some] at hst
  obtain ⟨b, hb, hst⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨c, h2, h3⟩ := h b hb st' (by cases b <;> simpa using hst)
  exact ⟨Count.test q d + c, by simpa using (St.Reach.tick st q d p).trans h2, h3⟩

/-- **Index binder**: one use of the query, then the body at every value within the bound that
the query may return; the body **receives the value read** and is charged for that value
only. -/
theorem bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B)
    (h : ∀ v ≤ B, I.index q a st.mem = some v →
      RunsFromWL I W τ body (ρ.pushIdx v) (st.tick q []) p
        fun c m => Q (Count.test q [] + c) m) :
    RunsFromWL I W τ (.bindIdx q ins bound body) ρ st p Q := by
  intro st' hst
  simp only [exec, ha, hB, Option.bind_some] at hst
  obtain ⟨v, hv, hst⟩ := Option.bind_eq_some_iff.mp hst
  split_ifs at hst with hle
  obtain ⟨c, h2, h3⟩ := h v hle hv st' hst
  exact ⟨Count.test q [] + c, by simpa using (St.Reach.tick st q [] p).trans h2, h3⟩

/-- **Scratch buffer**: the body runs with the new buffer on top, which is then popped; the
workspace is that of the body above the buffer. -/
theorem alloc {len : IExp} {body : Stmt Op Tst} {n : ℕ} (hn : len.eval ρ.idx = some n)
    (h : RunsFromWL I W τ body (ρ.pushBuf st.mem.store.length)
      ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.cost, st.cur + n, max st.peak (st.cur + n)⟩ p
      fun c m' => Q c ⟨m'.store.pop, m'.pos⟩) :
    RunsFromWL I W τ (.alloc len body) ρ st (n + p) Q := by
  intro st' hst
  simp only [exec, hn, Option.bind_some] at hst
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hst
  obtain ⟨c, ⟨h2, h3, h4⟩, h5⟩ := h st₂ h₂
  refine ⟨c, ⟨h2, rfl, ?_⟩, h5⟩
  simp only at h4 ⊢
  omega

/-- Procedure instance: the body, when the arguments are live. -/
theorem frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a)
    (h : st.mem.Live a → RunsFromWL I W τ body (Env.frame d a) st p Q) :
    RunsFromWL I W τ (.frame ds args body) ρ st p Q := by
  intro st' hst
  simp only [exec, hd, ha, Option.bind_some] at hst
  split_ifs at hst with hl
  exact h hl st' hst

/-- **Loop**, with an invariant on the counts added so far and the memory, indexed by the number
of rounds done: the bound of a round comes from the invariant. -/
theorem loop {n : IExp} {body : Stmt Op Tst} {k : ℕ} (hn : n.eval ρ.idx = some k)
    (Inv : ℕ → Count Op Tst → Mem K → Prop) (h0 : Inv 0 0 st.mem)
    (hstep : ∀ i < k, ∀ st' c, Inv i c st'.mem →
      RunsFromWL I W τ body (ρ.pushIdx i) st' p fun c' m => Inv (i + 1) (c + c') m) :
    RunsFromWL I W τ (.loop n body) ρ st p (Inv k) := by
  have key : ∀ j ≤ k, ∀ st', iter (fun i st => exec I W τ body (ρ.pushIdx i) st) j st =
      some st' → ∃ c, St.Reach st st' c p ∧ Inv j c st'.mem := by
    intro j
    induction j with
    | zero =>
      rintro - st' ⟨⟩
      exact ⟨0, St.Reach.refl st p, h0⟩
    | succ j ih =>
      intro hj st₂ hst
      obtain ⟨st₁, h1, h4⟩ := Option.bind_eq_some_iff.mp hst
      obtain ⟨c₁, h2, h3⟩ := ih (by omega) st₁ h1
      obtain ⟨c₂, h5, h6⟩ := hstep j (by omega) st₁ c₁ h3 st₂ h4
      exact ⟨c₁ + c₂, by simpa using h2.trans h5, h6⟩
  intro st' hst
  simp only [exec, hn, Option.bind_some] at hst
  exact key k le_rfl st' hst

/-- **The loop with early exit**, with an invariant on the counts added so far and the memory.
At a round below the cap the test is used once, and for every Boolean it may return: if it holds
the body keeps the invariant, otherwise the continuation runs with the round index. At the cap
the continuation runs without a test. The counts are those of the rounds that were done. -/
theorem whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} {n : ℕ} (hn : fuel.eval ρ.idx = some n)
    (Inv : ℕ → Count Op Tst → Mem K → Prop) (h0 : Inv 0 0 st.mem)
    (hstep : ∀ i < n, ∀ (st' : St Op Tst K) c, Inv i c st'.mem → ∃ d a,
      IExp.evalList (ρ.pushIdx i).idx ds = some d ∧ Operand.evalList (ρ.pushIdx i) ins = some a ∧
      ∀ b, I.test q d a st'.mem = some b →
        if b then RunsFromWL I W τ body (ρ.pushIdx i) (st'.tick q d) p
            fun c' m => Inv (i + 1) (c + (Count.test q d + c')) m
          else RunsFromWL I W τ k (ρ.pushIdx i) (st'.tick q d) p
            fun c' m => Q (c + (Count.test q d + c')) m)
    (hcap : ∀ (st' : St Op Tst K) c, Inv n c st'.mem →
      RunsFromWL I W τ k (ρ.pushIdx n) st' p fun c' m => Q (c + c') m) :
    RunsFromWL I W τ (.whileFuel fuel q ds ins body k) ρ st p Q := by
  have key : ∀ (r i : ℕ) (st₁ : St Op Tst K) (c₁ : Count Op Tst), i + r = n →
      St.Reach st st₁ c₁ p → Inv i c₁ st₁.mem → ∀ st',
        ((whileIter (fun i st => I.testSt q ds ins (ρ.pushIdx i) st)
          (fun i => exec I W τ body (ρ.pushIdx i)) r i st₁).bind fun jst =>
            exec I W τ k (ρ.pushIdx jst.1) jst.2) = some st' →
        ∃ c, St.Reach st st' c p ∧ Q c st'.mem := by
    intro r
    induction r with
    | zero =>
      intro i st₁ c₁ hi hr hinv st' hst
      obtain rfl : i = n := by omega
      obtain ⟨c₂, h2, h3⟩ := hcap st₁ c₁ hinv st' (by simpa [whileIter] using hst)
      exact ⟨c₁ + c₂, by simpa using hr.trans h2, h3⟩
    | succ r ih =>
      intro i st₁ c₁ hi hr hinv st' hst
      obtain ⟨d, a, hd, ha, hrun⟩ := hstep i (by omega) st₁ c₁ hinv
      have hr' := hr.trans (St.Reach.tick st₁ q d p)
      simp only [whileIter, Interp.testSt_eq hd ha, Option.bind_assoc] at hst
      obtain ⟨bs, hbs, hst⟩ := Option.bind_eq_some_iff.mp hst
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hbs
      have hrun := hrun b hb
      cases b with
      | false =>
        obtain ⟨c₂, h2, h3⟩ := hrun st' (by simpa using hst)
        exact ⟨c₁ + Count.test q d + c₂, by simpa using hr'.trans h2,
          by simpa [add_assoc] using h3⟩
      | true =>
        simp only [if_true, Option.bind_assoc] at hst hrun
        obtain ⟨st₂, h1, hst⟩ := Option.bind_eq_some_iff.mp hst
        obtain ⟨c₂, h2, h3⟩ := hrun st₂ h1
        exact ih (i + 1) st₂ (c₁ + Count.test q d + c₂) (by omega)
          (by simpa using hr'.trans h2) (by simpa [add_assoc] using h3) st' hst
  intro st' hst
  simp only [exec, hn, Option.bind_some] at hst
  exact key n 0 st 0 (by omega) (St.Reach.refl st p) h0 st' hst

/-- From the initial state: every successful counted run is within the workspace, and the
postcondition holds of its counts and its memory. -/
theorem exec_init {s : Stmt Op Tst} {m : Mem K} (h : RunsFromWL I W τ s ρ (St.init m) p Q)
    {st' : St Op Tst K} (hst : exec I W τ s ρ (St.init m) = some st') :
    st'.peak ≤ p ∧ Q st'.cost st'.mem := by
  obtain ⟨c, ⟨h2, -, h3⟩, h4⟩ := h st' hst
  have e : st'.cost = c := by simpa [St.init] using h2
  exact ⟨by simpa [St.init] using h3, e ▸ h4⟩

/-- A liberal counted run is a refinement statement, for the part of the postcondition that
every count satisfies. -/
theorem runsL {s : Stmt Op Tst} {m : Mem K} {P : Mem K → Prop}
    (h : RunsFromWL I W τ s ρ (St.init m) p fun _ m' => P m') : RunsL I τ s ρ m P := by
  intro m' hrun
  obtain ⟨st', hst, rfl⟩ := exec_eq_some_of_run hrun W (St.init m) rfl
  exact (h.exec_init hst).2

end RunsFromWL

section Link

variable {Op₁ Op₂ A : Type} [AddCommMonoid A] [PartialOrder A] [IsOrderedAddMonoid A]
  {T : Table Op₁ Op₂ Tst} {I : Interp Op₂ Tst K} {W₂ : Op₂ → List ℕ → ℕ}
  {w₂ : Count Op₂ Tst →+ A} {t : Op₁ → List ℕ → A} {W₁ : Op₁ → List ℕ → ℕ}

/-- **The weighted accounting certificate from the liberal judgment**: the body of every
implementation, in its frame and from every state, adds counts of weight at most `t o d` within
the workspace of its operation. This is what the rules of `RunsFromWL` prove. -/
theorem Table.AccountsW.of_runsFromWL
    (himpl : ∀ o R, T o = .inl R → ∀ (τ : Tape K) (d : List ℕ) (a : List (ℕ × ℕ))
      (st : St Op₂ Tst K), d.length = R.nd → a.length = R.nin + R.nout →
      RunsFromWL I W₂ τ R.body (Env.frame d a) st (W₁ o d) fun c _ => w₂ c ≤ t o d)
    (hkept : ∀ o o', T o = .inr o' → ∀ d, w₂ (Count.one o' d) ≤ t o d ∧ W₂ o' d ≤ W₁ o d) :
    T.AccountsW I W₂ w₂ t W₁ where
  kept := hkept
  impl o R hT τ d a st st' hd ha h := by
    obtain ⟨c, ⟨h1, h2, h3⟩, hc⟩ := himpl o R hT τ d a st hd ha st' h
    exact ⟨h2, by rw [h1, map_add]; exact add_le_add le_rfl hc, h3⟩

/-- Link a liberal counted segment from states with the same memory and live cells. The upper
starting peak must fit within the lower segment's peak bound. If the linked segment succeeds,
its added counts have weight at most the upper weight of the counts added by the algorithm
segment, which satisfy its postcondition. -/
theorem RunsFromWL.link_from (hacc : T.AccountsW I W₂ w₂ t W₁) {τ : Tape K} {s : Stmt Op₁ Tst}
    {ρ : Env} {a : St Op₁ Tst K} {c : St Op₂ Tst K} {p : ℕ} {Q : Count Op₁ Tst → Mem K → Prop}
    (h : RunsFromWL (I.link T) W₁ τ s ρ a p Q) (hmem : c.mem = a.mem) (hcur : c.cur = a.cur)
    (hpeak : a.peak ≤ max c.peak (c.cur + p)) :
    RunsFromWL I W₂ τ (s.link T) ρ c p
      fun dc m' => ∃ da, w₂ dc ≤ Count.upper w₂ t da ∧ Q da m' := by
  intro result hresult
  have hrun : run (I.link T) τ s ρ a.mem = some result.mem := by
    rw [← hmem, ← run_link]
    exact run_of_exec hresult
  let a₀ : St Op₁ Tst K := ⟨a.mem, 0, a.cur, 0⟩
  let c₀ : St Op₂ Tst K := ⟨c.mem, 0, c.cur, 0⟩
  obtain ⟨a₁, ha, -⟩ := exec_eq_some_of_run hrun W₁ a₀ rfl
  obtain ⟨c₁, hc, hsim⟩ := exec_link hacc τ s ρ a₀ a₁ c₀
    ⟨hmem, hcur, by simp [a₀, c₀], le_rfl⟩ ha
  have ha' := map_addHistory_exec (I.link T) W₁ τ s ρ a₀ a.cost a.peak
  have hc' := map_addHistory_exec I W₂ τ (s.link T) ρ c₀ c.cost c.peak
  have hstartA : St.addHistory a.cost a.peak a₀ = a := by simp [a₀, St.addHistory]
  have hstartC : St.addHistory c.cost c.peak c₀ = c := by simp [c₀, St.addHistory]
  rw [ha, Option.map_some, hstartA] at ha'
  rw [hc, Option.map_some, hstartC] at hc'
  have hEq := Option.some.inj (hresult.symm.trans hc'.symm)
  subst result
  obtain ⟨da, ⟨hcost, hcur', hpeak'⟩, hQ⟩ := h _ ha'.symm
  have hda : a₁.cost = da := add_left_cancel hcost
  subst da
  refine ⟨c₁.cost, ⟨rfl, hsim.cur.trans (hcur'.trans hcur.symm), ?_⟩,
    a₁.cost, hsim.cost, hsim.mem ▸ hQ⟩
  change max a.peak a₁.peak ≤ max a.peak (a.cur + p) at hpeak'
  change max c.peak c₁.peak ≤ max c.peak (c.cur + p)
  rw [hcur] at hpeak ⊢
  apply max_le (Nat.le_max_left ..)
  calc
    c₁.peak ≤ a₁.peak := hsim.peak
    _ ≤ max a.peak a₁.peak := Nat.le_max_right ..
    _ ≤ max a.peak (a.cur + p) := hpeak'
    _ ≤ max c.peak (a.cur + p) := max_le hpeak (Nat.le_max_right ..)

/-- Linking a liberal counted run from the initial state. -/
theorem RunsFromWL.link (hacc : T.AccountsW I W₂ w₂ t W₁) {τ : Tape K} {s : Stmt Op₁ Tst}
    {ρ : Env} {m : Mem K} {p : ℕ} {Q : Count Op₁ Tst → Mem K → Prop}
    (h : RunsFromWL (I.link T) W₁ τ s ρ (St.init m) p Q) :
    RunsFromWL I W₂ τ (s.link T) ρ (St.init m) p
      fun c m' => ∃ c₁, w₂ c ≤ Count.upper w₂ t c₁ ∧ Q c₁ m' :=
  h.link_from hacc rfl rfl (Nat.zero_le _)

end Link

end NLAlib.Ops
