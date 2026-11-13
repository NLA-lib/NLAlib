/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.Range

/-!
# Monadic folds over natural ranges

Upstream candidate: a successor rule for monadic folds over `List.range`, shared by
execution and weakest-precondition loop proofs. An optional traversal rule also exposes
pointwise success as a successful mapped list.

## Main results

* `List.foldlM_range_succ`: fold below the successor, then execute the last step.
* `List.mapM_eq_some_map`: a pointwise successful optional traversal.
-/

@[expose] public section

universe u v

namespace List

/-- A monadic fold below $i+1$ first folds below $i$, then executes step $i$.
This is `List.range_succ` and `List.foldlM_append` with the singleton fold simplified. -/
theorem foldlM_range_succ {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type u} (f : α → ℕ → m α) (a : α) (i : ℕ) :
    (range (i + 1)).foldlM f a = ((range i).foldlM f a) >>= fun b => f b i := by
  rw [range_succ, foldlM_append]
  simp only [foldlM_cons, foldlM_nil, bind_pure]

/-- If every optional call in a list succeeds with the value of a fixed function,
the optional traversal succeeds with the mapped list. -/
theorem mapM_eq_some_map {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_eq_some_map l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

end List
