/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Rules

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

## Main results

* `NLAlib.Ops.RunsFromW`: the judgment.
* `NLAlib.Ops.RunsFromW.seq`, `NLAlib.Ops.RunsFromW.bindIdx`, `NLAlib.Ops.RunsFromW.loop`,
  `NLAlib.Ops.RunsFromW.whileFuel` and the other rules.
* `NLAlib.Ops.RunsFromW.of_wp`, `NLAlib.Ops.RunsFromW.runsW`, `NLAlib.Ops.RunsFromW.runs`.
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

end NLAlib.Ops
