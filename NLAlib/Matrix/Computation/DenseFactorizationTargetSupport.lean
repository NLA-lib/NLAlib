/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.InputState
public import NLAlib.Computation.ClosedCountBudget
public import NLAlib.Computation.Model
public import NLAlib.Computation.StaticCost

/-!
# Declared-buffer budgets for dense factorization targets

Successful runs supply the postcondition; the existing static tree analysis supplies counts
and additional workspace. The shared bridge adds the declared caller storage once and compares
these bounds with the independent closed target budget. The target proofs derive both success
and the numerical postcondition from their input domains.

## Main results

* `NLAlib.Computation.DenseFactorizationTarget.runsWithin_of_exec`: the shared budget bridge.
-/

@[expose] public section

namespace NLAlib.Computation.DenseFactorizationTarget

/-- Actual success, a numerical postcondition and structural space bounds prove the budget. -/
theorem runsWithin_of_exec {r b : ℕ} (prog : Prog Unit Empty r b) (N : ℕ)
    (n : Fin r → ℕ) (bufs : Fin b → Array (Option ℝ)) (vals : ℕ → ℝ)
    (ξ : Dist → ℕ → ℝ) (caller scratch : ℕ)
    (hcaller : ((List.ofFn bufs).map Array.size).sum ≤ caller)
    (hspace : (prog.staticCost (fun k => Finsupp.single k 1) (fun _ => 0) N n).cells () ≤
      scratch)
    (hcount : (prog.staticCost (fun k => Finsupp.single k 1) (fun _ => 0) N n).count ≤
      closedCountBudget N) {out : St Unit ℝ (OpCount Unit Empty)}
    (hr : prog.exec (storedInterp 0 vals ξ ()) N n
      (inputState (C := OpCount Unit Empty) () (List.ofFn bufs)) = some out)
    {post : St Unit ℝ (OpCount Unit Empty) → Prop} (hp : post out) :
    prog.RunsWithin (storedInterp 0 vals ξ ()) N n
      (inputState (C := OpCount Unit Empty) () (List.ofFn bufs)) (closedCountBudget N)
      (fun _ => caller + scratch) post := by
  have hb := prog.bounds_staticCost_of_exec_eq_some (storedInterp 0 vals ξ ()) N n hr
  refine ⟨by simp, out, hr, ?_, ?_, hp⟩
  · exact hb.count.trans (add_le_add le_rfl hcount)
  · intro q
    cases q
    have hcur : (inputState (C := OpCount Unit Empty) () (List.ofFn bufs)).cur () ≤ caller := by
      simpa [inputState] using hcaller
    have hpeak : (inputState (C := OpCount Unit Empty) () (List.ofFn bufs)).peak () ≤ caller := by
      simpa [inputState] using hcaller
    change out.peak () + 0 ≤ caller + scratch
    rw [Nat.add_zero]
    exact (hb.peak ()).trans (max_le (hpeak.trans (Nat.le_add_right _ _))
      (Nat.add_le_add hcur hspace))


end NLAlib.Computation.DenseFactorizationTarget
