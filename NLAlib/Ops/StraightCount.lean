/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tape
public import NLAlib.Ops.Reference.Equivalence

/-!
# The static count and scratch are exact for trees without tests

`NLAlib.Ops.exec_static` bounds the count and the scratch of every successful run by the static
count and the static scratch of the tree. For a tree with no test, no loop with early exit and
no index query (`NLAlib.Ops.Stmt.Straight`) the control flow does not depend on the data, and the
bound is an equality: every successful run makes exactly the calls and structural instructions
the tree contains, and its peak scratch is exactly the static scratch.

## Main results

* `NLAlib.Ops.evalCounted_exactly_of_straight`: the statement for a tree, from any state.
* `NLAlib.Ops.Stmt.straight_of_isStraight`: a Boolean check the kernel evaluates.
* `NLAlib.Ops.exec_eq_static_of_straight`: the statement for the evaluator of a program.
* `NLAlib.Ops.Reference.Execution.eq_static_of_straight`: the statement for the execution
  rules.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- The state `b` is reached from `a` with exactly the counts `c` added and the peak raised to
exactly `p` above the live payload bytes, which are unchanged. -/
def St.Exactly (a b : St Op Tst K) (c : Count Op Tst) (p : ℕ) : Prop :=
  b.cur = a.cur ∧ b.cost = a.cost + c ∧ b.peak = max a.peak (a.cur + p)

namespace St.Exactly

/-- A state is reached from itself with no count and no workspace, when its live bytes are within
its peak. -/
theorem refl {a : St Op Tst K} (ha : a.cur ≤ a.peak) : St.Exactly a a 0 0 :=
  ⟨rfl, by simp, by simp [ha]⟩

/-- The end state has its live bytes within its peak when the start state has. -/
theorem consistent {a b : St Op Tst K} {c : Count Op Tst} {p : ℕ} (h : St.Exactly a b c p) :
    b.cur ≤ b.peak := by
  obtain ⟨h1, -, h3⟩ := h
  omega

/-- Exact counts add and exact workspaces take the larger, in sequence. -/
theorem trans {a b d : St Op Tst K} {c c' : Count Op Tst} {p p' : ℕ}
    (h : St.Exactly a b c p) (h' : St.Exactly b d c' p') :
    St.Exactly a d (c + c') (max p p') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1'.trans h1, by rw [h2', h2, add_assoc], ?_⟩
  rw [h3', h3, h1]
  omega

end St.Exactly

/-- The rounds of a counted loop add their exact counts and take the largest workspace. -/
theorem iter_exactly {f : ℕ → St Op Tst K → Option (St Op Tst K)} {c : ℕ → Count Op Tst}
    {p : ℕ → ℕ}
    (h : ∀ i a b, a.cur ≤ a.peak → f i a = some b → St.Exactly a b (c i) (p i)) {k : ℕ}
    {s s' : St Op Tst K} (hs : s.cur ≤ s.peak) (hk : iter f k s = some s') :
    St.Exactly s s' (∑ i ∈ Finset.range k, c i) ((Finset.range k).sup p) := by
  induction k generalizing s' with
  | zero => cases hk; simpa using St.Exactly.refl hs
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    have h₁ := ih ha
    have h₂ := h k a s' h₁.consistent hb
    have h₃ := h₁.trans h₂
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.sup_insert, max_comm]
    exact h₃

/-- The static count and workspace are exact without tests: a successful counted run of a
tree with no test, no loop with early exit and no index query adds exactly the static count and
raises the peak to exactly the static workspace above the live bytes. -/
theorem evalCounted_exactly_of_straight {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s : Stmt Op Tst} (hs : s.Straight) {ρ : Env} {st st' : St Op Tst K}
    (hst : st.cur ≤ st.peak) (h : evalCounted I W τ s ρ st = some st') :
    St.Exactly st st' (stmtCost s ρ.idx) (stmtPeak W s ρ.idx) := by
  induction s generalizing ρ st st' with
  | skip => cases h; exact St.Exactly.refl hst
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    have h₁ := ihs hs.1 hst ha
    exact h₁.trans (iht hs.2 h₁.consistent hb)
  | call o ds ins outs =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, by simp [stmtCost, useCost, hd], by simp [stmtPeak, hd]⟩
  | ite q ds ins t e iht ihe => exact hs.elim
  | whileFuel fuel q ds ins body k ih ihk => exact hs.elim
  | bindIdx q ins bound body ih => exact hs.elim
  | allocAs fmt len body ih =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, h2, h3⟩ := ih hs (ρ := ρ.pushBuf st.mem.store.length)
      (st := ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.cost, st.cur + fmt.bytes * n,
        max st.peak (st.cur + fmt.bytes * n)⟩) (by simp) h₂
    refine ⟨rfl, h2, ?_⟩
    simp only [stmtPeak, hn, Option.getD_some, Env.idx_pushBuf] at h3 ⊢
    omega
  | loop n body ih =>
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [stmtCost, stmtPeak, hk] using
      iter_exactly (fun i _ _ ha hb => ih hs ha hb) hst h
  | frame ds args body ih =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    simpa [stmtCost, stmtPeak, hd, Operand.evalList_off_of_evalList ha] using ih hs hst h
  | note _ _ ih => exact ih hs hst h

/-- A list of structural instructions is a tree without tests. -/
theorem straight_tally (ks : List Bookkeeping) :
    (tally (Op := Op) (Tst := Tst) ks).Straight := by
  induction ks with
  | nil => trivial
  | cons k ks ih => exact ⟨trivial, ih⟩

/-- Structural accounting adds no test to a tree without tests. -/
theorem Stmt.Straight.instrument {s : Stmt Op Tst} (hs : s.Straight) : s.instrument.Straight := by
  induction s with
  | skip => exact straight_tally _
  | abort => trivial
  | seq s t ihs iht => exact ⟨straight_tally _, ihs hs.1, iht hs.2⟩
  | call o ds ins outs => exact ⟨straight_tally _, trivial⟩
  | ite q ds ins t e iht ihe => exact hs.elim
  | whileFuel fuel q ds ins body k ih ihk => exact hs.elim
  | bindIdx q ins bound body ih => exact hs.elim
  | allocAs fmt len body ih => exact ⟨straight_tally _, trivial, ih hs, trivial⟩
  | loop n body ih => exact ⟨straight_tally _, straight_tally _, ih hs⟩
  | frame ds args body ih => exact ⟨straight_tally _, ih hs⟩
  | note _ _ ih => exact ih hs

/-- The Boolean form of `NLAlib.Ops.Stmt.Straight`, which the kernel evaluates on a closed
tree. -/
def Stmt.isStraight : Stmt Op Tst → Bool
  | .skip => true
  | .abort => true
  | .seq s t => s.isStraight && t.isStraight
  | .call _ _ _ _ => true
  | .ite _ _ _ _ _ => false
  | .whileFuel _ _ _ _ _ _ => false
  | .bindIdx _ _ _ _ => false
  | .allocAs _ _ body => body.isStraight
  | .loop _ body => body.isStraight
  | .frame _ _ body => body.isStraight
  | .note _ s => s.isStraight

/-- A tree the Boolean check accepts has no test. -/
theorem Stmt.straight_of_isStraight {s : Stmt Op Tst} (h : s.isStraight = true) : s.Straight := by
  induction s with
  | skip => trivial
  | abort => trivial
  | seq s t ihs iht =>
    simp only [Stmt.isStraight, Bool.and_eq_true] at h
    exact ⟨ihs h.1, iht h.2⟩
  | call o ds ins outs => trivial
  | ite q ds ins t e iht ihe => cases h
  | whileFuel fuel q ds ins body k ih ihk => cases h
  | bindIdx q ins bound body ih => cases h
  | allocAs fmt len body ih => exact ih h
  | loop n body ih => exact ih h
  | frame ds args body ih => exact ih h
  | note _ _ ih => exact ih h

/-- Exact resources of a program without tests: every successful run of the evaluator has
exactly the static count of the tree and exactly its static scratch. -/
theorem exec_eq_static_of_straight {r b : ℕ} {p : Program Op Tst r b} (hs : p.body.Straight)
    {I : Interp Op Tst K} {R : ResourceModel Op Tst} {formats : Fin b → StorageFormat}
    {τ : Tape K} {d : Fin r → ℕ} {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (h : exec p I R formats τ d m = some st) :
    st.cost = staticCost p d ∧ st.peak = staticPeak R p d := by
  unfold exec at h
  split_ifs at h
  obtain ⟨raw, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, hc, hp⟩ := evalCounted_exactly_of_straight hs.instrument (by simp [St.init]) hr
  have hc' : raw.cost = staticCost p d := by simpa [St.init, staticCost] using hc
  refine ⟨hc', ?_⟩
  have hp' : raw.peak = stmtPeak (instrumentWorkspace R.workspace) p.body.instrument
      (Program.environment (b := b) d).idx := by simpa [St.init] using hp
  simp [St.reserveQueries, staticPeak, hp', hc']

/-- Exact resources under the execution rules: an outcome the rules derive for a program
without tests has exactly the static count of the tree and exactly its static scratch. -/
theorem Reference.Execution.eq_static_of_straight {r b : ℕ} {p : Program Op Tst r b}
    (hs : p.body.Straight) {I : Interp Op Tst K} {R : ResourceModel Op Tst}
    {formats : Fin b → StorageFormat} {τ : Tape K} {d : Fin r → ℕ} {m : Mem K}
    {st : Reference.State Op Tst K} (h : Reference.Execution p I R formats τ d m st) :
    st.cost = staticCost p d ∧ st.peak = staticPeak R p d :=
  exec_eq_static_of_straight hs ((Reference.execution_iff_exec I R τ p formats d m st).mp h)

end NLAlib.Ops
