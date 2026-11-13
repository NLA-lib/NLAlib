/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Cost
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Scalar counts for sequential Lanczos

Sequential BLAS implements the vector operations with scalar loops and keeps matrix-vector
products primitive. The count includes every initialized output cell and every normalization
and continuation test. The two vectors and two cells of solve scratch share the dot workspace.

## Main results

* `NLAlib.Krylov.Lanczos.push_solveCount_seq` evaluates the linked scalar budget.
* `NLAlib.Krylov.Lanczos.solvePeak_seq_le` bounds linked scratch by three vectors and three cells.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- Sequential dot uses a zero literal, one copy when nonempty, and the scalar reduction. -/
noncomputable def seqDotCount (n : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj ScalarOp.mul) [] +
    (n - 1) • Count.one (Has.inj ScalarOp.add) [] +
    Count.one (Has.inj (ScalarOp.lit 0)) [] +
    (1 - (1 - n)) • Count.one (Has.inj ScalarOp.copy) []

/-- The sequential raw update contains two axpy loops and its diagonal dot product. -/
noncomputable def seqUpdateCount (n : ℕ) : Count Op Tst :=
  Count.one (Has.inj OperatorOp.matvec) [n, n] +
    2 • Count.one (Has.inj ScalarOp.neg) [] +
    (2 * n) • Count.one (Has.inj ScalarOp.mul) [] +
    (2 * n) • Count.one (Has.inj ScalarOp.add) [] + seqDotCount n

omit [Has OperatorOp Op] [Apart Blas1Op OperatorOp Op] in
/-- A dot call expands to scalar arithmetic, including its empty-vector zero literal. -/
theorem push_dot_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost
      (Count.one (Has.inj Blas1Op.dot) [n]) = seqDotCount n := by
  count_eval [seqDotCount]

/-- Pushing the raw update keeps matvec and expands both vector updates and the dot. -/
theorem push_updateCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (updateCount n) =
      seqUpdateCount n := by
  have hm : (Blas.seq (Op := Op) (Tst := Tst)).cost
      (Has.inj OperatorOp.matvec) [n, n] = Count.one (Has.inj OperatorOp.matvec) [n, n] := by
    simp [Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq, Blas.sumSeqCost]
  count_eval [updateCount, seqUpdateCount, seqDotCount, hm]

variable [Has CmpTst Tst]

/-- Guarded normalization counts the test, square root, copy loop and division loop. -/
noncomputable def seqNormalizeCount (n : ℕ) : Count Op Tst :=
  Count.test (Has.inj CmpTst.isPos) [] + Count.one (Has.inj ScalarOp.sqrt) [] +
    n • Count.one (Has.inj ScalarOp.copy) [] + n • Count.one (Has.inj ScalarOp.div) []

/-- The active round adds the residual self-dot and previous-vector copy to normalization. -/
noncomputable def seqAdvanceCount (n : ℕ) : Count Op Tst :=
  seqUpdateCount n + seqDotCount n + n • Count.one (Has.inj ScalarOp.copy) [] +
    seqNormalizeCount n

/-- Initialization includes all basis and coefficient cells, the previous vector, and the
input self-dot and normalization. -/
noncomputable def seqInitializeCount (n cap : ℕ) : Count Op Tst :=
  ((cap + 1) * n + 2 * cap + 2 + n) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
    seqDotCount n + seqNormalizeCount n

/-- The full scalar budget is initialization plus at most cap tested active rounds. -/
noncomputable def seqSolveCount (n cap : ℕ) : Count Op Tst :=
  seqInitializeCount n cap +
    cap • (Count.test (Has.inj CmpTst.isPos) [] + seqAdvanceCount n)

omit [Has OperatorOp Op] [Apart Blas1Op OperatorOp Op] in
/-- Linking sequential BLAS expands normalization into scalar calls and preserves its test. -/
theorem push_normalizeCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (normalizeCount n) =
      seqNormalizeCount n := by
  count_eval [normalizeCount, seqNormalizeCount, Count.push_test]

/-- Linking expands every operation of one active round to the scalar round budget. -/
theorem push_advanceCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (advanceCount n) =
      seqAdvanceCount n := by
  simp only [advanceCount, map_add, push_updateCount_seq, push_dot_seq,
    push_normalizeCount_seq, seqAdvanceCount]
  count_eval

/-- The complete static budget transfers to the closed scalar count, including zero fills. -/
theorem push_solveCount_seq (n cap : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n cap) =
      seqSolveCount n cap := by
  simp only [solveCount, map_add, map_nsmul, push_advanceCount_seq,
    push_normalizeCount_seq, push_dot_seq, zeroCount, seqSolveCount, seqInitializeCount,
    Count.push_test]
  count_eval

/-- Dot scratch, the two solver vectors and two cells fit in three vectors and three cells,
including for zero dimension. -/
theorem solvePeak_seq_le (n : ℕ) : solvePeak (Blas.ws (Op := Op) 0) n ≤ 3 * n + 3 := by
  simp [solvePeak, callPeak, Blas.ws]
  omega

end NLAlib.Krylov.Lanczos
