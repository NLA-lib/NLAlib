/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop

/-!
# Capped loops as stopped mathematical iteration

A client represents a mathematical state in memory, identifies the actual Boolean query, and
proves one transition under the active guard. The shared rule constructs the loop invariant
and handles early exit: once inactive, the mathematical transition is the identity. No
successful-execution hypothesis is required, and reaching the cap asserts no convergence.

## Main results

* `NLAlib.Ops.writes_whileFuel_iterate`: total capped execution returns the stopped iterate.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K S : Type} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-- A capped loop implements the iterate of the transition that acts while active and is the
identity afterwards. The step proof supplies only the mathematical state transition and its
footprint. The actual query must return the state predicate at every reachable represented
state; early termination is handled by the generic rule. -/
theorem writes_whileFuel_iterate {fuel : IExp} {q : Tst} {ds : List IExp}
    {ins : List Operand} {body : Stmt Op Tst} {N : ℕ} {F : Fp}
    (State : S → Mem K → Prop) (active : S → Bool) (next : S → S) {s : S}
    (hn : fuel.eval ρ.idx = some N) (hs : State s m)
    (htest : ∀ i < N, ∀ m', m.store.EqOff F m'.store →
      State ((fun s => if active s then next s else s)^[i] s) m' →
      I.testAt q ds ins (ρ.pushIdx i) m' =
        some (active ((fun s => if active s then next s else s)^[i] s)))
    (hstep : ∀ i < N, ∀ m', m.store.EqOff F m'.store →
      State ((fun s => if active s then next s else s)^[i] s) m' →
      active ((fun s => if active s then next s else s)^[i] s) = true →
      Writes .total I τ body (ρ.pushIdx i) F
        (State (next ((fun s => if active s then next s else s)^[i] s))) m') :
    Writes .total I τ (.whileFuel fuel q ds ins body .skip) ρ F
      (State ((fun s => if active s then next s else s)^[N] s)) m := by
  let advance : S → S := fun s => if active s then next s else s
  change Writes .total I τ _ _ _ (State (advance^[N] s)) _
  refine (writes_whileFuel hn (fun _ => F) (fun _ _ => le_rfl) ⊥
    (fun i => State (advance^[i] s)) (State (advance^[N] s)) hs ?_ ?_).mono
    (by simp) (fun _ _ h => h)
  · intro i hi m' hfr hstate
    rw [htest i hi m' hfr hstate]
    apply Mode.holds_some
    cases hc : active (advance^[i] s) with
    | true =>
      simp only [ite_true]
      refine (hstep i hi m' hfr hstate hc).mono le_rfl ?_
      intro m'' _ hnext
      simpa only [Function.iterate_succ_apply', advance, hc, ite_true] using hnext
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hfix : advance (advance^[i] s) = advance^[i] s := by simp [advance, hc]
      have hremain : advance^[N - i] (advance^[i] s) = advance^[i] s :=
        Function.iterate_fixed hfix _
      have heq : advance^[N] s = advance^[i] s := by
        rw [← Nat.sub_add_cancel (Nat.le_of_lt hi), Function.iterate_add_apply, hremain]
      exact Writes.skip (heq.symm ▸ hstate)
  · intro m' _ hstate
    exact Writes.skip hstate

end NLAlib.Ops
