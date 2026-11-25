/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames
public import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Empty-dimensional complete-pivot LU execution

At dimension zero, initialization and every pivoted elimination loop are empty. The body
returns the original state without requiring valid buffer handles or initialized cells.

## Main results

* `NLAlib.Computation.PLUQ.exec_emptyBody`: the complete-pivot body makes no changes at zero.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQ

open Builder

variable {P ι : Type} [DecidableEq P]

/-- Every chooser-based factorization body executes only empty loops at dimension zero,
independently of the chooser and scalar interpretation; no buffer handle is read. -/
theorem exec_emptyBody_choice {K C : Type} [AddMonoid C] (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (A S L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ)
    (choose : IExp ℕ → IExp ℕ → ℕ → IExp ℕ → Cell ℕ ℕ → Cell ℕ ℕ →
      Builder P ι ℕ ℕ Unit) (hn : n.eval = 0) : exec I (do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)).run st = some st := by
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop (n * n) _) (.seq (.loop n _) .skip)))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]


/-- The full complete-pivot factorization body executes only empty loops at dimension zero.
No matrix, factor or log handle is read, independently of the scalar interpretation. -/
theorem exec_emptyBody {K C : Type} [AddMonoid C] (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (A S L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ)
    (hn : n.eval = 0) : exec I (do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        completePivotChoice tag n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)).run st = some st := by
  exact exec_emptyBody_choice I tag st n A S L U Hr Hc ao lo uo hro hco
    (completePivotChoice tag) hn

end NLAlib.Computation.PLUQ
