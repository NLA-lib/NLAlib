/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Static

/-!
# Counted loops with state invariants

A stored size query can select one operation shape rather than every syntactically possible
shape. The loop invariant justifies the selected per-iteration count. Accumulation then uses
the sum of those counts and the maximum per-iteration workspace, without a supremum over
unreachable stored sizes.

## Main results

* `NLAlib.Ops.iter_within_of_invariant`: accumulate actual shape-specific iteration budgets.
* `NLAlib.Ops.iter_weight_le_of_invariant`: accumulate weighted actual counts directly.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- Iteration preserves a state invariant and accumulates its per-round resource bounds.
The step premise is needed only on states satisfying the invariant. This lemma concerns an
actual counted iteration; total program correctness supplies its execution separately. -/
theorem iter_within_of_invariant
    {f : ℕ → St Op Tst K → Option (St Op Tst K)} {P : ℕ → St Op Tst K → Prop}
    {c : ℕ → Count Op Tst} {p : ℕ → ℕ}
    (hstep : ∀ i a b, P i a → f i a = some b →
      P (i + 1) b ∧ St.Within a b (c i) (p i))
    {k : ℕ} {s s' : St Op Tst K} (hs : P 0 s) (hk : iter f k s = some s') :
    P k s' ∧ St.Within s s' (∑ i ∈ Finset.range k, c i) ((Finset.range k).sup p) := by
  induction k generalizing s' with
  | zero => cases hk; exact ⟨hs, St.Within.refl s⟩
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨hpa, hsa⟩ := ih ha
    obtain ⟨hpb, hab⟩ := hstep k a s' hpa hb
    refine ⟨hpb, (hsa.trans hab).mono ?_ ?_⟩
    · rw [Finset.sum_range_succ]
    · rw [Finset.range_add_one, Finset.sup_insert]
      exact le_of_eq (max_comm _ _)

/-- A loop's actual weighted count is bounded by the sum of the selected per-round weights.
This does not first bound the complete count vector by its syntactic manifest. Thus an
invariant can exploit a stored partition when bounding matrix-kernel work or span.
The weight may be any function on counts; its algebraic laws belong to the step proof. -/
theorem iter_weight_le_of_invariant
    {f : ℕ → St Op Tst K → Option (St Op Tst K)} {P : ℕ → St Op Tst K → Prop}
    {weight : Count Op Tst → ℕ} {w : ℕ → ℕ}
    (hstep : ∀ i a b, P i a → f i a = some b →
      P (i + 1) b ∧ weight b.cost ≤ weight a.cost + w i)
    {k : ℕ} {s s' : St Op Tst K} (hs : P 0 s) (hk : iter f k s = some s') :
    P k s' ∧ weight s'.cost ≤ weight s.cost + ∑ i ∈ Finset.range k, w i := by
  induction k generalizing s' with
  | zero => cases hk; exact ⟨hs, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨hpa, hsa⟩ := ih ha
    obtain ⟨hpb, hab⟩ := hstep k a s' hpa hb
    refine ⟨hpb, ?_⟩
    rw [Finset.sum_range_succ]
    omega

/-- The invariant-sensitive weighted rule needs its step proof only for the rounds actually
reserved by this iteration count. This is the usual bounded loop-invariant interface. -/
theorem iter_weight_le_of_invariant_upto
    {f : ℕ → St Op Tst K → Option (St Op Tst K)} {P : ℕ → St Op Tst K → Prop}
    {weight : Count Op Tst → ℕ} {w : ℕ → ℕ} {k : ℕ}
    (hstep : ∀ i < k, ∀ a b, P i a → f i a = some b →
      P (i + 1) b ∧ weight b.cost ≤ weight a.cost + w i)
    {s s' : St Op Tst K} (hs : P 0 s) (hk : iter f k s = some s') :
    P k s' ∧ weight s'.cost ≤ weight s.cost + ∑ i ∈ Finset.range k, w i := by
  have hgen : ∀ j ≤ k, ∀ b, iter f j s = some b →
      P j b ∧ weight b.cost ≤ weight s.cost + ∑ i ∈ Finset.range j, w i := by
    intro j
    induction j with
    | zero => intro hj b hb; cases hb; exact ⟨hs, by simp⟩
    | succ j ih =>
      intro hj b hb
      obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨hpa, hwa⟩ := ih (by omega) a ha
      obtain ⟨hpb, hwb⟩ := hstep j (by omega) a b hpa hb
      refine ⟨hpb, ?_⟩
      rw [Finset.sum_range_succ]
      omega
  exact hgen k le_rfl s' hk

end NLAlib.Ops
