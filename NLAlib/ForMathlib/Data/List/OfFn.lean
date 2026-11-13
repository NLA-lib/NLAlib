/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lists from finite sum functions

Upstream candidates for `Mathlib.Data.List.OfFn`. Functions on a finite sum enumerate their
left and right parts consecutively, including when the total dimension is written by an equal
natural-number expression.

## Main results

* `List.ofFn_sumElim_cast`: finite sum enumeration as list concatenation.
-/

@[expose] public section

namespace List

/-- Enumerating a sum function in the standard finite order concatenates its two lists. -/
theorem ofFn_sumElim_cast {α : Type*} {n p q : ℕ} (h : n = p + q)
    (a : Fin p → α) (b : Fin q → α) :
    List.ofFn (fun i => Sum.elim a b (((finCongr h).trans finSumFinEquiv.symm) i)) =
      List.ofFn a ++ List.ofFn b := by
  subst n
  have hf : (fun i => Sum.elim a b (finSumFinEquiv.symm i)) = Fin.append a b := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp
  simpa only [Equiv.trans_apply, finCongr_refl, Equiv.refl_apply, hf] using
    List.ofFn_fin_append a b

end List
