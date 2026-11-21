/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Exact
public import NLAlib.Krylov.Lanczos.Reorth.Exact
public import NLAlib.Ops.Profiles.ContextLinear
public import NLAlib.Ops.RoutineData

/-!
# Fixed stored dense Lanczos programs

Both programs declare four raw buffers: matrix entries, right-hand side, basis capacity and
coefficient capacity. Every matrix application is a scalar dense leaf. The program is fixed
before matrix dimension, iteration cap and raw input words; its remaining vector names are
those of the explicitly chosen exact BLAS operation model.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.solveRoutine`, `NLAlib.Krylov.Lanczos.Stored.program`: the
  stored routine and its program.
* `NLAlib.Krylov.Lanczos.Reorth.Stored.solveRoutine`,
  `NLAlib.Krylov.Lanczos.Reorth.Stored.program`: the reorthogonalized ones.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Stored

open Ops

/-- Lanczos on a stored dense matrix: the matrix-free Lanczos routine with the matrix words, `n * n`
of them, a new isolated leading operand forwarded to every product. -/
def solveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (Lanczos.solveRoutine (Op := Standard.Operation) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0] (ContextLinear.table 1 0)

/-- The fixed ordinary program: the stored routine on the four supplied buffers, the dense matrix
first. -/
def program : Program RCLikeBlas.Operation CmpTst 2 4 := solveRoutine.close 2 4

/-- The canonical four-buffer environment forwards matrix data to every procedure. -/
theorem environment_eq (d : Fin 2 → ℕ) :
    Program.environment (b := 4) d =
      (Env.frame [d 0, d 1] [(1, 0), (2, 0), (3, 0)]).withContext [(0, 0)] 2 := by
  rfl

end NLAlib.Krylov.Lanczos.Stored

namespace NLAlib.Krylov.Lanczos.Reorth.Stored

open Ops

/-- Reorthogonalized Lanczos on a stored dense matrix: the matrix-free routine with the matrix
words, `n * n` of them, a new isolated leading operand forwarded to every product. -/
def solveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (Lanczos.Reorth.solveRoutine (Op := Standard.Operation) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0] (ContextLinear.table 1 0)

/-- The fixed reorthogonalized program: the stored routine on the four supplied buffers. -/
def program : Program RCLikeBlas.Operation CmpTst 2 4 := solveRoutine.close 2 4

end NLAlib.Krylov.Lanczos.Reorth.Stored
