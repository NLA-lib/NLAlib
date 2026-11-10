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
* **Counts that depend on the data**, by `RunsFromW` (`NLAlib.Ops.Counted`), and
  the partial-correctness form: `NLAlib.Ops.RunsFromWL` ("if the counted run succeeds, `Q` holds
  of the counts added and the memory"), with one rule per constructor: it is the core's
  (`NLAlib.Ops.Counted`, decision D12). Here: the bridge from a block specification,
  `NLAlib.Ops.RunsFromW.of_writes`.

## Main results

* `NLAlib.Ops.RunsFromW.of_writes`: a block specification with its static counts.
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
      c ≤ staticCost s ρ.idx ∧ st.mem.store.EqOff F m'.store ∧ P m' :=
  RunsFromW.of_wp h

/-! ### Closed forms -/

namespace Count

/-- A constant count over a range. -/
theorem sum_range_nsmul (p : ℕ) (c : Count Op Tst) : ∑ _j ∈ Finset.range p, c = p • c := by
  simp

/-- A count proportional to the round over a range: `Σ_{j < p} j c = (p (p - 1) / 2) c`, the
triangle of classical Gram–Schmidt. -/
theorem sum_range_id_nsmul (p : ℕ) (c : Count Op Tst) :
    ∑ j ∈ Finset.range p, j • c = (p * (p - 1) / 2) • c := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, ← add_nsmul]
    congr 1
    rcases p with _ | q
    · rfl
    · have : (q + 1 + 1) * (q + 1 + 1 - 1) = (q + 1) * (q + 1 - 1) + 2 * (q + 1) := by
        simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      omega

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
