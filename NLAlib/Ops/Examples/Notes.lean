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

The routines `NLAlib.Ops.Examples.Routines.sum2`, `NLAlib.Ops.Examples.Integrator.myStep` and
`NLAlib.Ops.Examples.Integrator.myIntegrate` are written with `noted%`, so their trees carry the
names of the source as notes (`NLAlib.Ops.Stmt.note`). The judgments, the certificates and the
counts of those routines are proved on the noted trees, by the same proofs as without notes.

`NLAlib.Ops.Stmt.pretty` reads a tree back as pseudocode. It is a reading aid, not a code
emitter. The checks below fix its output on the three trees.

## Main results

* The output of `NLAlib.Ops.Stmt.pretty` on the three noted trees, checked when the file is built.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Notes

deriving instance Repr for ScalarOp
deriving instance Repr for Integrator.MyOperation

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
