/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.SolveAlias
import NLAlib.Matrix.Factorizations.Cholesky.SolveAlias
import NLAlib.Ops.Profiles.ScalarIndex
import NLAlib.Ops.Tools.Machines

/-!
# Actual closed in-place solve interfaces

These checks execute the closed programs of the four in-place interfaces, so the repeated
operand layout is exercised in addition to the shared raw instruction bodies. The known
system is solved independently of the program's reported postcondition.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.SolveInPlaceOpsSmoke

private def check (r : Routine ScalarIndex.Operation ScalarIndex.Queries)
    (buffers : Store Float) (output : ℕ) : Bool := Id.run do
  let program := r.close 1 buffers.length
  let initial : Mem Float := ⟨buffers, 47⟩
  let interp : Interp ScalarIndex.Operation ScalarIndex.Queries Float :=
    withQueries (ScalarIndex.functions floatMachine)
  let some final := NLAlib.Ops.eval interp (fun _ _ => 0) program.body
    (Program.environment (b := buffers.length) (fun _ : Fin 1 => 2)) initial | return false
  let some xs := final.store.readBlock output 0 2 | return false
  return xs.length == 2 && (xs.getD 0 0 - 1).abs < 1e-12 &&
    (xs.getD 1 0 - 2).abs < 1e-12 && final.pos == 47 &&
    final.store.shape == initial.store.shape && (List.range buffers.length).all fun b =>
      b == output || final.store[b]? == initial.store[b]?

#guard check NLAlib.LU.solveInPlace [vals [2, 1, 1, 3], vals [4, 7]] 1
#guard check NLAlib.Cholesky.solveInPlace [vals [2, 1, 1, 3], vals [4, 7]] 1
#guard check NLAlib.TriangularSolve.solveFactorsInPlace
  [vals [1, 0.5, 0, 1], vals [2, 0, 1, 2.5], vals [4, 7]] 2
#guard check NLAlib.TriangularSolve.solveCholeskyInPlace
  [vals [(2 : Float).sqrt, 1 / (2 : Float).sqrt, 0, (2.5 : Float).sqrt], vals [4, 7]] 1

end NLAlibTools.SolveInPlaceOpsSmoke
