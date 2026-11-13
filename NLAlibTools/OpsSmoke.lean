/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Profiles.StoredDense
import NLAlib.Ops.Examples.Certification
import NLAlib.Ops.Tools.ProgramFixtures
import NLAlib.Ops.Tools.Run

/-!
# Running scalar dense arithmetic through canonical Ops execution

The diagnostic runs the actual column-major dense matrix-vector implementation, including its
scoped temporary and every scalar operation. Canonical execution validates formats and counts
addressing, index arithmetic, control, allocation and release as well as arithmetic. The report
is a computation, not a numerical certificate or a claim about physical memory/time.

The matrix is [[1,2],[3,4]], the vector is [5,6], and the expected output is [17,39].
Imported kernel-checked ProgramFixtures cover format/arity failure and full resource accounting.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.OpsSmoke

/-- One fixed scalar-only dense matvec tree; dimensions are supplied at execution. -/
def denseProgram : Program ScalarOp Empty 2 3 :=
  ⟨.frame [.var 0, .var 1] [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩]
    (StoredDense.impl (Op := ScalarOp) (Tst := Empty)).body⟩

/-- Actual raw column-major words and initially uninitialized output slots. -/
def input : Mem ℚ := ⟨[[some 1, some 3, some 2, some 4], [some 5, some 6], [none, none]], 0⟩

/-- Full canonical execution on an abstract-cell unit-cost scalar model. -/
def report : ProgramReport ScalarOp Empty ℚ :=
  profileProgram denseProgram (Interp.ofFns ratMachine.fn)
    NLAlib.Ops.Examples.Certification.repeatResources (fun _ => .cell) (fun _ _ => 0)
    ![2, 2] input

#guard (report.result.map (fun st => st.mem.store.readBlock 2 0 2)) == some (some [17, 39])
#guard (report.result.map (fun st => st.mem.store.length)) == some 3
#eval report
#eval report.result.map (fun st => st.mem.store.readBlock 2 0 2)

end NLAlibTools.OpsSmoke
