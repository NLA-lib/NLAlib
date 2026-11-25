/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledAlg
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of fixed-original-scale LU

The actual scalar tree computes each original row norm once, scans active column/scale pairs
by division-free comparisons, transports the cached scales and runs total elimination. Its
closed cubic charges all structural instructions. Caller storage comprises the source, two
square factors and one row log; the packed residual/scale arena and temporaries are extra.

## Main results

* `NLAlib.LU.ScaledCertification.countPoly_program`: actual literal instruction polynomial.
* `NLAlib.LU.ScaledCertification.staticPeak_program_le`: packed extra storage at every order.
-/

@[expose] public section

namespace NLAlib.LU.ScaledCertification

open Ops

/-- The fixed stored-scale program, before dimensions, matrix, interpreter and tape. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 4 :=
  (factorScaled (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 4

/-- Full instruction work and sequential span, including original-scale computation. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 479 * d 0 ^ 2 + 707 * d 0 + 109

/-- Extra packed residual/scales, selected-index word, saved Schur vectors and scalar scratch. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 3 * d 0 + 5

/-- The kernel computes the literal polynomial from the actual guarded scalar tree. -/
theorem countPoly_program :
    program.countPoly = [(22, [0, 0, 0]), (479, [0, 0]), (707, [0]), (109, [])] := by
  kernel_rfl

/-- The actual instruction polynomial has the declared closed cubic value at every order. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- Every actual branch fits the packed residual/scale arena and `2n+5` further cells. The
outer dimension guard also covers order zero, without a matrix or execution premise. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (factorScaled (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    [n, 0, 0, 0, 0] ≤ n * n + 3 * n + 5
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  suffices hh : ∀ b < 1 - (1 - n), n * n + n + (1 + max
      ((Finset.range (1 - (1 - n))).sup fun _ : ℕ =>
        (Finset.range (1 - (1 - n))).sup fun _ : ℕ => (Finset.range n).sup fun _ : ℕ => 1)
      ((Finset.range n).sup fun i => max
        (1 + (1 + (1 + (Finset.range (n - i - 1)).sup fun _ : ℕ => 3)))
        ((Finset.range (n - 1 + 1)).sup fun v =>
          max ((Finset.range (1 - (1 - (v - i)))).sup fun _ : ℕ => 1)
            (n + (n + (1 + (Finset.range n).sup fun _ : ℕ => 2)))))) ≤
      n * n + 3 * n + 5 by
    simpa [factorScaled, scaledLoop, scaledStep, scaledChoice, argmaxScaledAbs,
      advanceScaled, considerScaled, acceptScaled, rowScales, maxAbsValue, absolute,
      initializeFactors, pivotSwaps, swapRows, swapColumns, swapScales,
      Examples.Strided.swapMatrixRows, Examples.Strided.swapRows, step, materializeColumn,
      materializeUpper, normalizeColumn, schurStepTotal, schurStep, pivotSaved, rankOne,
      schurColumn, copyLoopRoutine, copyLoop, scalLoopRoutine, scalLoop, axpyLoopRoutine,
      axpyLoop, fillRoutine, fillMap, copyStridedRoutine, stmtPeak, ScalarIndex.resources,
      Stmt.ifPos, Stmt.alloc, IExp.eval, IExp.evalList, h0] using hh
  intro b hb
  have hn : 0 < n := by omega
  have hinit : (Finset.range (1 - (1 - n))).sup (fun _ : ℕ =>
      (Finset.range (1 - (1 - n))).sup fun _ : ℕ =>
        (Finset.range n).sup fun _ : ℕ => 1) ≤ 1 :=
    Finset.sup_le (fun _ _ => Finset.sup_le (fun _ _ => Finset.sup_le (fun _ _ => le_rfl)))
  have h2 : (Finset.range n).sup (fun _ : ℕ => 2) ≤ 2 :=
    Finset.sup_le (fun _ _ => le_rfl)
  have hloop : (Finset.range n).sup (fun i => max
      (1 + (1 + (1 + (Finset.range (n - i - 1)).sup fun _ : ℕ => 3)))
      ((Finset.range (n - 1 + 1)).sup fun v =>
        max ((Finset.range (1 - (1 - (v - i)))).sup fun _ : ℕ => 1)
          (n + (n + (1 + (Finset.range n).sup fun _ : ℕ => 2))))) ≤ 2 * n + 4 := by
    apply Finset.sup_le
    intro i _
    have h3 : (Finset.range (n - i - 1)).sup (fun _ : ℕ => 3) ≤ 3 :=
      Finset.sup_le (fun _ _ => le_rfl)
    refine max_le (by omega) ?_
    apply Finset.sup_le
    intro v _
    have h1 : (Finset.range (1 - (1 - (v - i)))).sup (fun _ : ℕ => 1) ≤ 1 :=
      Finset.sup_le (fun _ _ => le_rfl)
    omega
  omega

end NLAlib.LU.ScaledCertification
