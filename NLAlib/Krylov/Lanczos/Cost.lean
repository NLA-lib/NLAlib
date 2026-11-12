/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg

/-!
# Counts and workspace of guarded Lanczos

The evaluator counts all initialized output cells, the input normalization, and at most cap
active rounds. Comparison queries are counted separately from arithmetic calls. The basis and
coefficient arrays are caller outputs; scoped scratch consists of two vectors and two cells.

## Main results

* `NLAlib.Krylov.Lanczos.stmtCost_solve` evaluates the complete operation budget.
* `NLAlib.Krylov.Lanczos.stmtPeak_solve_le` bounds workspace independently of the cap.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Largest workspace of a primitive used by initialization or a Lanczos round. -/
def callPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (W (Has.inj (ScalarOp.lit 0)) [])
    (max (W (Has.inj OperatorOp.matvec) [n, n])
      (max (W (Has.inj ScalarOp.neg) [])
        (max (W (Has.inj Blas1Op.dot) [n])
          (max (W (Has.inj Blas1Op.axpy) [n])
            (max (W (Has.inj ScalarOp.sqrt) [])
              (max (W (Has.inj Blas1Op.copy) [n]) (W (Has.inj Blas1Op.scal) [n])))))))

/-- The raw recurrence borrows caller scratch and requires only a call workspace. -/
theorem stmtPeak_update_le (W : Op → List ℕ → ℕ) (n p q b w a t w' a' : ℕ) :
    stmtPeak W (update (Op := Op) (Tst := Tst)) [n, p, q, b, w, a, t, w', a'] ≤
      callPeak W n := by
  simp [update, stmtPeak, callPeak]
  omega

variable [Has CmpTst Tst]

/-- The guarded normalizer borrows caller outputs and introduces no allocated storage. -/
theorem stmtPeak_normalize_le (W : Op → List ℕ → ℕ) (n w s q b q' b' : ℕ) :
    stmtPeak W (normalize (Op := Op) (Tst := Tst)) [n, w, s, q, b, q', b'] ≤
      callPeak W n := by
  simp [normalize, stmtPeak, callPeak]

/-- Static evaluation of one active iteration, including its normalization branch. -/
theorem stmtCost_advance (n cap b v c j : ℕ) :
    stmtCost (advance (Op := Op) (Tst := Tst)) [n, cap, b, v, c, j] = advanceCount n := by
  simp [advance, stmtCost, useCost, stmtCost_update, stmtCost_normalize, advanceCount]
  module

/-- An active iteration introduces no additional allocation beyond the enclosing solve. -/
theorem stmtPeak_advance_le (W : Op → List ℕ → ℕ) (n cap b v c j : ℕ) :
    stmtPeak W (advance (Op := Op) (Tst := Tst)) [n, cap, b, v, c, j] ≤ callPeak W n := by
  have hu := stmtPeak_update_le (Tst := Tst) W n 0 (v + j * n) (c + cap + j) 0 (c + j) 0 0 (c + j)
  have hn := stmtPeak_normalize_le (Tst := Tst) W n 0 0 (v + (j + 1) * n) (c + cap + j + 1)
    (v + (j + 1) * n) (c + cap + j + 1)
  simp [advance, stmtPeak]
  simp only [callPeak] at hu hn ⊢
  omega

omit [Has OperatorOp Op] in
/-- Initialization counts all requested coefficient cells, including any extra suffix. -/
theorem stmtCost_initialize (n cap len b v c p t : ℕ) :
    stmtCost (initializeState (Op := Op) (Tst := Tst)) [n, cap, len, b, v, c, p, t] =
      zeroCount ((cap + 1) * n) + zeroCount len + zeroCount n +
        Count.one (Has.inj Blas1Op.dot) [n] + normalizeCount n := by
  simp [initializeState, stmtCost, useCost, stmtCost_zero, stmtCost_normalize]
  module

/-- The borrowed initializer requires only a call workspace regardless of output lengths. -/
theorem stmtPeak_initialize_le (W : Op → List ℕ → ℕ) (n cap len b v c p t : ℕ) :
    stmtPeak W (initializeState (Op := Op) (Tst := Tst)) [n, cap, len, b, v, c, p, t] ≤
      callPeak W n := by
  have hzV := stmtPeak_zero_le (Op := Op) (Tst := Tst) W ((cap + 1) * n) v
  have hzC := stmtPeak_zero_le (Op := Op) (Tst := Tst) W len c
  have hzP := stmtPeak_zero_le (Op := Op) (Tst := Tst) W n p
  have hn := stmtPeak_normalize_le (Tst := Tst) W n b t v (c + 2 * cap + 1) v
    (c + 2 * cap + 1)
  simp [initializeState, stmtPeak]
  simp only [callPeak] at hn ⊢
  omega

/-- Static accounting includes every initialized cell, input normalization and tested round. -/
theorem stmtCost_solve (n cap b v c : ℕ) :
    stmtCost (solve (Op := Op) (Tst := Tst)) [n, cap, b, v, c] = solveCount n cap := by
  have hsup : (Finset.range (cap + 1)).sup (fun _ => (0 : Count Op Tst)) = 0 :=
    le_antisymm (Finset.sup_le fun _ _ => le_rfl) zero_le
  simp [solve, rounds, stmtCost, testCost, stmtCost_initialize,
    stmtCost_advance, solveCount, hsup]

/-- Two scoped vectors, two cells and one call workspace suffice for the complete solver. -/
def solvePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ := 2 * n + 2 + callPeak W n

/-- The peak workspace does not grow with the iteration cap. -/
theorem stmtPeak_solve_le (W : Op → List ℕ → ℕ) (n cap b v c : ℕ) :
    stmtPeak W (solve (Op := Op) (Tst := Tst)) [n, cap, b, v, c] ≤ solvePeak W n := by
  have hi := stmtPeak_initialize_le (Tst := Tst) W n cap (2 * cap + 2) b v c 0 0
  have hb : (Finset.range cap).sup
      (fun j => stmtPeak W (advance (Op := Op) (Tst := Tst)) [n, cap, b, v, c, j]) ≤
      callPeak W n := Finset.sup_le fun j _ => stmtPeak_advance_le (Tst := Tst) W n cap b v c j
  simp [solve, rounds, stmtPeak, solvePeak]
  omega

end NLAlib.Krylov.Lanczos
