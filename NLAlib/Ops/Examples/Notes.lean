/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Integrator
public import NLAlib.Ops.Examples.Routine
public import NLAlib.Ops.Notes
meta import NLAlib.Ops.Examples.Integrator
meta import NLAlib.Ops.Examples.Routine
meta import NLAlib.Ops.Notes

/-!
# Example: trees with notes, read as pseudocode

A tree written with `ops%` or `routine%` has no note, and its declaration `foo` has a noted copy
beside it: the same tree with the names of the source as notes (`NLAlib.Ops.Stmt.note`).
`noted_of% foo` is that copy and `NLAlib.Ops.Routine.pretty` reads it as pseudocode. It is a
reading aid, not a code emitter. The checks below fix its output on `Routines.double` and
`NLAlib.Ops.sumSeqRoutine` (whose `ifPos n` is a loop of at most one round, with an unnamed
variable), and show that erasing the notes of the copy gives the tree of the declaration.
The same checks on routines of the algorithm directories are in `NLAlibTools/OpsNotes.lean`,
because no file under `NLAlib/Ops` imports an algorithm.

The routines `NLAlib.Ops.Examples.Routines.sum2`, `NLAlib.Ops.Examples.Integrator.myStep` and
`NLAlib.Ops.Examples.Integrator.myIntegrate` are written with `noted%`, which puts the notes in
the value itself. Their judgments, certificates and counts are proved on the noted trees, by the
same proofs as without notes; the library does not write its trees this way.

## Main results

* The output of `NLAlib.Ops.Routine.pretty` on the noted copies of two routines, and of
  `NLAlib.Ops.Stmt.pretty` on three trees written with `noted%`, checked when the file is built.
* The tree of a routine is its noted copy with the notes erased.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Notes

deriving instance Repr for ScalarOp
deriving instance Repr for Integrator.MyOperation

/-- info: call add [] (x, x) → (x) -/
#guard_msgs in
#eval IO.println (noted_of% Routines.double : Routine ScalarOp Empty).pretty

/-- info: call lit 0 [] () → (z)
for i3 < 1 - (1 - n) {
  call copy [] (x) → (z)
}
for i < n - 1 {
  call add [] (z, x[1 + i]) → (z)
} -/
#guard_msgs in
#eval IO.println (noted_of% sumSeqRoutine : Routine ScalarOp Empty).pretty

/-- The tree of a routine is its noted copy with the notes erased. -/
example : (sumSeqRoutine : Routine ScalarOp Empty).body =
    (noted_of% sumSeqRoutine : Routine ScalarOp Empty).body.erase := rfl

/-- info: let Y ← alloc n
call matvec [n, n] (X) → (Y)
call axpy [n] (h, Y, X) → (X) -/
#guard_msgs in
#eval IO.println Integrator.myStep.body.pretty

/-- info: for t < N {
  run NLAlib.Ops.Examples.Integrator.myStep [n] (h, X)
} -/
#guard_msgs in
#eval IO.println Integrator.myIntegrate.body.pretty

/-- info: run NLAlib.Ops.Examples.Routines.sum [n] (x, z)
run NLAlib.Ops.Examples.Routines.sum [n] (y, w)
call add [] (z, w) → (z) -/
#guard_msgs in
#eval IO.println (Routines.sum2 (Op := ScalarOp) (Tst := Empty)).body.pretty

/-- Erasing the notes of a noted tree gives a tree with the same static count. -/
example (idx : List ℕ) :
    stmtCost Integrator.myIntegrate.body.erase idx = stmtCost Integrator.myIntegrate.body idx :=
  congrFun (stmtCost_erase _) idx

end NLAlib.Ops.Examples.Notes
