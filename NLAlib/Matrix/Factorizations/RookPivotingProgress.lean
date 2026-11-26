/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.RookPivoting
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite progress of strict rook pivoting

Only strict column-magnitude growth causes a continuation. The visited columns below are
mathematical witnesses in the execution proof, not a runtime array. Each continuation inserts
a fresh active column. Exhausting the active columns therefore rules out a further strict
improvement, including ties and zero active columns.

## Main results

* `NLAlib.HasRookVisitedColumns.insert`: a strict improvement visits a fresh column.
* `NLAlib.HasRookVisitedColumns.rookColumnMagnitude_le_of_card`:
  exhausted active columns bound every score.
-/

@[expose] public section

namespace NLAlib

/-- The visited active columns are all bounded by the incumbent column's magnitude. Exactly
one column is present initially and every strict continuation adds one fresh column. This is
proof-only finite progress information, independent of the representation of stored words. -/
structure HasRookVisitedColumns {𝕜 : Type*} [Norm 𝕜] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) 𝕜) (k : Fin N) (rounds : ℕ)
    (current : Fin N) (visited : Finset (Fin N)) : Prop where
  /-- Every visited column belongs to the active suffix. -/
  active : ∀ c ∈ visited, k ≤ c
  /-- The incumbent column has been visited. -/
  current_mem : current ∈ visited
  /-- Each strict continuation has added one column. -/
  card : visited.card = rounds + 1
  /-- No previously visited column has larger magnitude than the incumbent. -/
  le_current : ∀ c ∈ visited, rookColumnMagnitude M k c ≤ rookColumnMagnitude M k current

namespace HasRookVisitedColumns

/-- The initial pivot column is the only visited column before any continuation. -/
theorem initial {𝕜 : Type*} [Norm 𝕜] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) 𝕜) (k : Fin N) :
    HasRookVisitedColumns M k 0 k {k} := by
  refine ⟨?_, by simp, by simp, ?_⟩
  · intro c hc
    have he : c = k := Finset.mem_singleton.mp hc
    subst c
    exact le_rfl
  · intro c hc
    have he : c = k := Finset.mem_singleton.mp hc
    subst c
    exact le_rfl

/-- A strict column-magnitude increase cannot return to a visited column. Inserting the new
active column advances the round count and preserves all visited-column bounds. -/
theorem insert {𝕜 : Type*} [Norm 𝕜] {N rounds : ℕ}
    {M : Matrix (Fin N) (Fin N) 𝕜} {k c d : Fin N} {visited : Finset (Fin N)}
    (h : HasRookVisitedColumns M k rounds c visited) (hd : k ≤ d)
    (hgrowth : rookColumnMagnitude M k c < rookColumnMagnitude M k d) :
    HasRookVisitedColumns M k (rounds + 1) d (insert d visited) := by
  have hnew : d ∉ visited := by
    intro hmem
    exact (not_lt_of_ge (h.le_current d hmem)) hgrowth
  refine ⟨?_, by simp, by rw [Finset.card_insert_of_notMem hnew, h.card], ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hd
    · exact h.active e he
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact le_rfl
    · exact (h.le_current e he).trans hgrowth.le

/-- Once enough distinct columns have been visited, the visited set is the whole active
suffix. Thus every active column magnitude is bounded by the current one. -/
theorem rookColumnMagnitude_le_of_card {𝕜 : Type*} [Norm 𝕜] {N rounds : ℕ}
    {M : Matrix (Fin N) (Fin N) 𝕜} {k c : Fin N} {visited : Finset (Fin N)}
    (h : HasRookVisitedColumns M k rounds c visited) (hcount : N - k.val ≤ rounds + 1)
    (d : Fin N) (hd : k ≤ d) :
    rookColumnMagnitude M k d ≤ rookColumnMagnitude M k c := by
  have hsub : visited ⊆ Finset.Ici k := fun e he => Finset.mem_Ici.mpr (h.active e he)
  have heq : visited = Finset.Ici k := Finset.eq_of_subset_of_card_le hsub (by
    rw [Fin.card_Ici, h.card]
    exact hcount)
  apply h.le_current d
  rw [heq]
  exact Finset.mem_Ici.mpr hd

end HasRookVisitedColumns

end NLAlib
