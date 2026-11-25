/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Order.Fin.Basic

/-!
# Stable finite prefix maxima

A strict score improvement advances a prefix maximizer while retaining the first index on
equality. Upstream candidate for `Mathlib.Order.Fin.Basic`.

## Main results

* `Fin.max_eq_score_choose_of_prefix`: one stable update of a finite prefix maximum.
-/

@[expose] public section

namespace Fin

/-- Retaining an incumbent on equal scores preserves prefix maximality and strict dominance
over all earlier indices. The score takes values in any linear order. -/
theorem max_eq_score_choose_of_prefix {α : Type*} [LinearOrder α]
    {N k : ℕ} (score : Fin N → α) (i j : Fin N)
    (hj : j.val = k) (hdom : ∀ l : Fin N, l.val < k → score l ≤ score i)
    (hfirst : ∀ l : Fin N, l < i → score l < score i) :
    let chosen := if score i < score j then j else i
    max (score i) (score j) = score chosen ∧
      (∀ l : Fin N, l.val < k + 1 → score l ≤ score chosen) ∧
      (∀ l : Fin N, l < chosen → score l < score chosen) := by
  dsimp only
  split_ifs with hlt
  · refine ⟨max_eq_right hlt.le, ?_, ?_⟩
    · intro l hl
      by_cases hlk : l.val < k
      · exact (hdom l hlk).trans hlt.le
      · have : l = j := Fin.ext (by omega)
        subst l
        exact le_rfl
    · intro l hl
      exact (hdom l (by simpa [← hj] using hl)).trans_lt hlt
  · refine ⟨max_eq_left (le_of_not_gt hlt), ?_, hfirst⟩
    intro l hl
    by_cases hlk : l.val < k
    · exact hdom l hlk
    · have : l = j := Fin.ext (by omega)
      subst l
      exact le_of_not_gt hlt

end Fin
