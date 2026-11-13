/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownMatrixShapes
public import NLAlib.Eigensolvers.SpectralBisection.UpMatrixShapes

/-!
# Matrix-call support of the complete fixed solver

Initial input buffers perform no matrix primitive. The actual initialization, downward pass,
bottom boundary, reconstruction and final copies compose to one root-bounded support theorem.

## Main results

* `NLAlib.SpectralBisection.program_matrixShapes`: exact static matrix shapes of the fixed program.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem reconstruct_shape (n L : ℕ) (offs : List ℕ) :
    (stmtCost (reconstructResult (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, L] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame_of_length (d := [n, L]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os hos => upwardPass_matrixShapes n L os hos
  · exact matrixShapes_of_allOps n _ (by rfl) _

private theorem solveBody_shape (n L cap : ℕ) (offs : List ℕ) :
    (stmtCost (solveBody (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      ([n, L, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame_of_length (d := [n, L, cap])
      (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os hos => downwardPass_matrixShapes n L cap os hos
  · refine callsSatisfy_stmtCost_frame (d := [n, L]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => reconstruct_shape n L os

/-- Persistent allocations and caller offsets preserve the complete solver's matrix shapes. -/
theorem solve_matrixShapes (n L cap : ℕ) (offs : List ℕ) :
    (stmtCost (solve (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      ([n, L, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => solveBody_shape n L cap os

/-- Every matrix operation in the fixed program's static support has its declared arity
and logical dimensions bounded by the root. This includes invalid or unreachable data
branches admitted by conservative static analysis, without execution or accuracy assumptions. -/
theorem program_matrixShapes (d : Fin 3 → ℕ) :
    (stmtCost (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      (Program.environment (b := 4) d).idx).CallsSatisfy (MatrixShape (d 0)) := by
  have hd : List.ofFn d = [d 0, d 1, d 2] := by
    simp [List.ofFn_succ, Fin.succ]
  simpa only [program, Program.environment, hd] using
    solve_matrixShapes (d 0) (d 1) (d 2) (List.replicate 4 0)

end NLAlib.SpectralBisection
