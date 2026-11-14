/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Backward

/-!
# Example: the backward errors of loops

A round of three programs `c₁`, `c₂`, `c₃`, each a backward step with errors $u$, $v$, $w$ for a
backward-error relation, repeated $N$ times, is a backward step with error $N(u + v + w)$. The
proof is the composition rules and nothing else: no error invariant is written by hand.

The steps are abstract; the backward-error relation may be a perturbed unitary similarity
(`NLAlib.isBackwardErrorRel_isPerturbedUnitarySimilar`), as in the rounded shifted QR algorithm,
where one round is a sweep of rotations, a perturbation by rounding and a deflation.

## Main results

* `NLAlib.Ops.Examples.backwardStep_loop_seq`: the backward error of the loop.
* `NLAlib.Ops.Examples.backwardStep_loop_ite`: a loop of conditional rounds whose skipped arm uses
  the outcome of the test (the decoupling loop of shifted QR).
* `NLAlib.Ops.Examples.backwardStep_whileFuel_skip`: a loop with early exit whose exit uses the
  outcome of the test (the deflation worklist).
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {Op Tst K : Type} {α : Type*} {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env}
  {F : Fp} {R : ℝ → α → α → Prop} {S : α → Mem K → Prop}

/-- The backward error of a loop of three steps: if `c₁`, `c₂`, `c₃` are backward steps that
keep the predicate `S`, with errors $u$, $v$, $w$ and footprint `F` at every round, then the loop
of $N$ rounds of the three is a backward step with error $N(u + v + w)$ and footprint `F`. -/
theorem backwardStep_loop_seq (hR : IsBackwardErrorRel R) {n : IExp} {N : ℕ}
    (hn : n.eval ρ.idx = some N) {c₁ c₂ c₃ : Stmt Op Tst} {u v w : ℝ}
    (h₁ : ∀ i, BackwardStep md I τ c₁ (ρ.pushIdx i) F R S S u)
    (h₂ : ∀ i, BackwardStep md I τ c₂ (ρ.pushIdx i) F R S S v)
    (h₃ : ∀ i, BackwardStep md I τ c₃ (ρ.pushIdx i) F R S S w) :
    BackwardStep md I τ (.loop n (.seq c₁ (.seq c₂ c₃))) ρ F R S S (N * (u + v + w)) := by
  have h := BackwardStep.loop (F := F) hR hn (fun _ => S) (fun _ => u + (v + w)) fun i _ =>
    ((h₁ i).seq hR ((h₂ i).seq hR (h₃ i))).mono hR (by simp) le_rfl fun _ _ h => h
  simpa [add_assoc, mul_add] using h

/-- A loop of conditional rounds, in the shape of the decoupling loop of shifted QR ("iterate
unless the scan says the matrix is decoupled"): the test at round $i$ has an outcome described by
`T i`; on a true outcome the round runs `c`, a backward step with error $u \ge 0$ from `S i` to
`S (i + 1)`; on a false outcome nothing runs, and the outcome alone gives `S (i + 1)`. The loop of
$N$ rounds is a backward step with error $N u$. -/
theorem backwardStep_loop_ite (hR : IsBackwardErrorRel R) {n : IExp} {N : ℕ}
    (hn : n.eval ρ.idx = some N) {q : Tst} {ds : List IExp} {ins : List Operand}
    {c : Stmt Op Tst} {u : ℝ} (hu : 0 ≤ u) (S : ℕ → α → Mem K → Prop)
    (T : ℕ → Bool → α → Mem K → Prop)
    (htest : ∀ i < N, ∀ a m, S i a m →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m) fun b => T i b a m)
    (hc : ∀ i < N, BackwardStep md I τ c (ρ.pushIdx i) F R
      (fun a m => S i a m ∧ T i true a m) (S (i + 1)) u)
    (hstop : ∀ i < N, ∀ a m, S i a m → T i false a m → S (i + 1) a m) :
    BackwardStep md I τ (.loop n (.ite q ds ins c .skip)) ρ F R (S 0) (S N) (N * u) := by
  have h := BackwardStep.loop (F := F) hR hn S (fun _ => u) fun i hi =>
    BackwardStep.ite (T i) (htest i hi) (hc i hi)
      ((BackwardStep.skip hR fun a m h => hstop i hi a m h.1 h.2).mono hR bot_le hu
        fun _ _ h => h)
  simpa using h

/-- A loop with early exit, in the shape of the deflation worklist ("while the stack is not
empty"): the test at round $i$ has an outcome described by `T i`; on a true outcome the round runs
`c`, a backward step with error $u \ge 0$ from `S i` to `S (i + 1)`; on a false outcome the loop
stops, and the outcome gives `S'` (the stack is empty); after $N$ rounds `S N` gives `S'`. The loop
is a backward step with error $N u$. -/
theorem backwardStep_whileFuel_skip (hR : IsBackwardErrorRel R) {fuel : IExp} {N : ℕ}
    (hn : fuel.eval ρ.idx = some N) {q : Tst} {ds : List IExp} {ins : List Operand}
    {c : Stmt Op Tst} {u : ℝ} (hu : 0 ≤ u) (S : ℕ → α → Mem K → Prop) {S' : α → Mem K → Prop}
    (T : ℕ → Bool → α → Mem K → Prop)
    (htest : ∀ i < N, ∀ a m, S i a m →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m) fun b => T i b a m)
    (hc : ∀ i < N, BackwardStep md I τ c (ρ.pushIdx i) F R
      (fun a m => S i a m ∧ T i true a m) (S (i + 1)) u)
    (hexit : ∀ i < N, ∀ a m, S i a m → T i false a m → S' a m)
    (hcap : ∀ a m, S N a m → S' a m) :
    BackwardStep md I τ (.whileFuel fuel q ds ins c .skip) ρ F R (S 0) S' (N * u) := by
  have h := BackwardStep.whileFuel (F := F) (G := ⊥) hR hn S T (fun _ => u) (fun _ _ => hu)
    htest hc (fun i hi => BackwardStep.skip hR fun a m h => hexit i hi a m h.1 h.2)
    (BackwardStep.skip hR hcap)
  simpa using h

end NLAlib.Ops.Examples
