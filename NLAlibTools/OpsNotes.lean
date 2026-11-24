/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Krylov.CG.HSCG.Alg
import NLAlib.Krylov.CG.HSPCG.Alg
import NLAlib.Matrix.Factorizations.MGS.Alg
import NLAlib.Estimation.Trace.HutchPlusPlus.Alg
import NLAlib.Ops.Profiles.ExactLinear
import NLAlib.Ops.Notes

/-!
# Library routines read as pseudocode

Every tree written with `ops%` or `routine%` has a noted copy `foo._noted`: the same tree with
the names of its source (`NLAlib/Ops/Logic/Builder.lean`). `noted_of% foo` is that copy, and
`NLAlib.Ops.Stmt.pretty` / `NLAlib.Ops.Routine.pretty` read it as pseudocode. The checks below
fix the output on routines of three shapes: a loop of routine calls, a factorization with
scratch and nested loops, and a randomized estimator.

This is a reading aid for people and tools. It is not a code emitter, and nothing is proved
about its output; the certified trees are the declarations themselves, which carry no note.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Ops

deriving instance Repr for ScalarOp
deriving instance Repr for Blas1Op
deriving instance Repr for OperatorOp
deriving instance Repr for StoredOperatorOp
deriving instance Repr for SampleOp
deriving instance Repr for IndexOp
deriving instance Repr for CmpTst
deriving instance Repr for Krylov.CG.HSPCG.Signature

/-- info: for i < k {
  run NLAlib.Krylov.CG.HSCG.stepRoutine [n] (X, R, P)
} -/
#guard_msgs in
#eval IO.println
  (noted_of% Krylov.CG.HSCG.roundsRoutine : Routine Krylov.CG.HSPCG.Signature Empty).pretty

/-- info: let Q ← alloc n
let Z ← alloc n
let t ← alloc 4
call blas (NLAlib.Ops.Blas1Op.dot) [n] (R, R) → (t)
call operator [n, n] (P) → (Q)
call blas (NLAlib.Ops.Blas1Op.dot) [n] (P, Q) → (t@(1))
call scalar (NLAlib.Ops.ScalarOp.div) [] (t, t@(1)) → (t@(2))
call blas (NLAlib.Ops.Blas1Op.axpy) [n] (t@(2), P, X) → (X)
call scalar (NLAlib.Ops.ScalarOp.neg) [] (t@(2)) → (t@(2))
call blas (NLAlib.Ops.Blas1Op.axpy) [n] (t@(2), Q, R) → (R)
call blas (NLAlib.Ops.Blas1Op.dot) [n] (R, R) → (t@(3))
call scalar (NLAlib.Ops.ScalarOp.div) [] (t@(3), t) → (t@(3))
call blas (NLAlib.Ops.Blas1Op.copy) [n] (R) → (Z)
call blas (NLAlib.Ops.Blas1Op.axpy) [n] (t@(3), P, Z) → (Z)
call blas (NLAlib.Ops.Blas1Op.copy) [n] (Z) → (P) -/
#guard_msgs in
#eval IO.println
  (noted_of% Krylov.CG.HSCG.stepRoutine : Routine Krylov.CG.HSPCG.Signature Empty).pretty

/-- info: let t ← alloc 2
run NLAlib.MGS.factorWithScratch [n, k] (Y, t) -/
#guard_msgs in
#eval IO.println (noted_of% MGS.factorRoutine : Routine RCLikeBlas.Operation CmpTst).pretty

/-- info: let B ← alloc n * (k + ell)
run NLAlib.HutchPlusPlus.prepare [n, k, ell] (data, B)
run NLAlib.HutchPlusPlus.finish [n, k, ell] (data, B, out) -/
#guard_msgs in
#eval IO.println
  (noted_of% HutchPlusPlus.estimateRoutine Stream.gauss (fun n _ => n * n) :
    Routine ExactLinear.Operation CmpTst).pretty
