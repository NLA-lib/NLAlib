/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Counted
public import NLAlib.Ops.Logic.Writes

/-!
# Counts in the logic layer

Two things a program proof does with counts:

* **Static counts in closed form.** `staticCost` of a tree is a sum over its loops; the abstract
  theorem states it in closed form (`m p • dot [n]`, `(p (p - 1) / 2) • (neg + axpy) + …`). The
  tactic `count_eval` unfolds `staticCost` on the tree, evaluates the index expressions and
  rewrites the sums of `NLAlib.Ops.Count.sum_range_nsmul` and `sum_range_id_nsmul` (phase B).
* **Counts that depend on the data**, by `RunsFromW` (`NLAlib.Ops.Counted`). What is missing is
  the partial-correctness form: `NLAlib.Ops.RunsFromWL` ("if the counted run succeeds, `Q` holds
  of the counts added and the memory"), with one rule per constructor, so that
  `Table.AccountsW` is proved for a large implementation without unfolding `exec`. And the bridge
  from a block specification: `NLAlib.Ops.RunsFromW.of_writes`.

**Phase A**: statements only (`sorry`).

## Main results

* `NLAlib.Ops.RunsFromW.of_writes`: a block specification with its static counts.
* `NLAlib.Ops.RunsFromWL` and its rules `skip`, `seq`, `call`, `loop`, `bindIdx`, `of_runsFromW`.
* `NLAlib.Ops.Count.sum_range_nsmul`, `NLAlib.Ops.Count.sum_range_id_nsmul`: closed forms.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {ρ : Env}

/-- A block specification, counted at its static cost: the bridge from `Writes` to the counted
judgment for the parts whose counts do not depend on the data. -/
theorem RunsFromW.of_writes {s : Stmt Op Tst} {st : St Op Tst K} {F : Fp} {P : Mem K → Prop}
    (h : Writes .total I τ s ρ F P st.mem) :
    RunsFromW I W τ s ρ st (staticPeak W s ρ.idx) fun c m' =>
      c ≤ staticCost s ρ.idx ∧ st.mem.store.EqOff F m'.store ∧ P m' := by sorry

/-- **The counted judgment, partial correctness**: if the counted run of `s` from `st` succeeds,
it stays within the workspace `p` above the live cells, and `Q` holds of the counts added and of
the final memory. It says nothing of success: a target never rests on it alone. -/
def RunsFromWL (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst)
    (ρ : Env) (st : St Op Tst K) (p : ℕ) (Q : Count Op Tst → Mem K → Prop) : Prop :=
  ∀ st', exec I W τ s ρ st = some st' → ∃ c, St.Reach st st' c p ∧ Q c st'.mem

namespace RunsFromWL

variable {st : St Op Tst K} {p p' : ℕ} {Q Q' : Count Op Tst → Mem K → Prop}

theorem skip (h : Q 0 st.mem) : RunsFromWL I W τ .skip ρ st p Q := by sorry

/-- Sequence: the continuation from every state the first part may reach. -/
theorem seq {s t : Stmt Op Tst} (h : RunsFromWL I W τ s ρ st p Q')
    (h' : ∀ st' c, Q' c st'.mem → RunsFromWL I W τ t ρ st' p' fun c' m => Q (c + c') m) :
    RunsFromWL I W τ (.seq s t) ρ st (max p p') Q := by sorry

/-- A call: one count at its dimensions, and the workspace of the operation; the memory from any
liberal `Wp` of the call. -/
theorem call {o : Op} {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {P : Mem K → Prop}
    (hd : IExp.evalList ρ.idx ds = some d)
    (h : Wp .liberal I τ (.call o ds ins outs) ρ P st.mem) :
    RunsFromWL I W τ (.call o ds ins outs) ρ st (W o d) fun c m => c = Count.one o d ∧ P m := by
  sorry

/-- A loop, with an invariant on the counts added so far and the memory. -/
theorem loop {n : IExp} {body : Stmt Op Tst} {k : ℕ} (hn : n.eval ρ.idx = some k)
    (Inv : ℕ → Count Op Tst → Mem K → Prop) (h0 : Inv 0 0 st.mem)
    (hstep : ∀ i < k, ∀ st' c, Inv i c st'.mem →
      RunsFromWL I W τ body (ρ.pushIdx i) st' p fun c' m => Inv (i + 1) (c + c') m) :
    RunsFromWL I W τ (.loop n body) ρ st p (Inv k) := by sorry

/-- An index binder: one use of the query, then the body at **every** value the query may
return within the bound (the value is not known in partial correctness). -/
theorem bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst} {B : ℕ}
    (hB : bound.eval ρ.idx = some B)
    (h : ∀ v ≤ B, RunsFromWL I W τ body (ρ.pushIdx v) (st.tick q []) p
      fun c m => Q (Count.test q [] + c) m) :
    RunsFromWL I W τ (.bindIdx q ins bound body) ρ st p Q := by sorry

/-- A total counted run is a liberal one. -/
theorem of_runsFromW {s : Stmt Op Tst} (h : RunsFromW I W τ s ρ st p Q) :
    RunsFromWL I W τ s ρ st p Q := by sorry

end RunsFromWL

/-! ### Closed forms -/

namespace Count

/-- A constant count over a range. -/
theorem sum_range_nsmul (p : ℕ) (c : Count Op Tst) : ∑ _j ∈ Finset.range p, c = p • c := by
  simp

/-- A count proportional to the round over a range: `Σ_{j < p} j c = (p (p - 1) / 2) c`, the
triangle of classical Gram–Schmidt. -/
theorem sum_range_id_nsmul (p : ℕ) (c : Count Op Tst) :
    ∑ j ∈ Finset.range p, j • c = (p * (p - 1) / 2) • c := by sorry

end Count

/-- **`count_eval`**: a goal `staticCost s idx = C` or `≤ C`, or `Count.push T c = C`, with `C` in
closed form. Unfolds `staticCost` and `useCost` on the tree, evaluates the index expressions,
distributes `•` and `Count.push` over the sums (`map_add`, `map_nsmul`, the cost lemmas of the
profile), rewrites `Count.sum_range_nsmul`, `Count.sum_range_id_nsmul`, and closes by `abel`
(with `ring_nf` on the coefficients). Fails with the remaining goal. Phase B; provisional
implementation. -/
macro "count_eval" : tactic => `(tactic| first
  | (simp [staticCost, useCost, Count.sum_range_nsmul, Count.sum_range_id_nsmul]; done)
  | fail "count_eval: the count is not put in the closed form of the goal")

end NLAlib.Ops
