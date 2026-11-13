/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.SolverWorkspace
public import NLAlib.Eigensolvers.SpectralBisection.Resources
public import NLAlib.Eigensolvers.SpectralBisection.ProgramMatrixShapes
public import NLAlib.Ops.Workspace

/-!
# Complete abstract-cell storage polynomial

The polynomial is independent of the operation-count manifest and the iteration cap.
It bounds the complete instrumented solver when the selected dense model assigns zero
additional workspace to its matrix primitives. Structural instructions and queries have
zero workspace in that model. Arbitrary matrix workspace adds one finite maximum over
the proved root-bounded call shapes. Supplied resident capacity is included separately below.

## Main results

* `NLAlib.SpectralBisection.staticPeak_zeroWorkspace_le`: independent scratch polynomial.
* `NLAlib.SpectralBisection.staticPeak_workspaceEnvelope_le`: arbitrary finite matrix workspace.
* `NLAlib.SpectralBisection.initialBytes_add_staticPeak_zeroWorkspace_le`: resident plus scratch.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- In the abstract-cell dense profile with zero additional primitive workspace, the full
instrumented solver satisfies the independent arena-and-nesting scratch polynomial.
The root dimension is at least two; no numerical or execution-success premise is needed. -/
theorem staticPeak_zeroWorkspace_le (matrixWork : MatrixOp → List ℕ → ℕ)
    (d : Fin 3 → ℕ) (hn : 2 ≤ d 0) :
    staticPeak (Dense.resources matrixWork (fun _ _ => 0))
      (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤
      6 * (d 0 * d 0) * d 1 + 32 * (d 0 * d 0) + 4 * d 0 * d 1 +
        7 * d 0 + 2 * d 1 + 24 := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  have hw : (Dense.resources matrixWork (fun _ _ => 0)).workspace = fun _ _ => 0 := by
    funext o ds
    cases o <;> rfl
  rw [hw]
  have hd : List.ofFn d = [d 0, d 1, d 2] := by
    simp [List.ofFn_succ, Fin.succ]
  simpa only [program, Program.environment, hd] using
    stmtPeak_solve_zero_le (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (d 0) (d 1) (d 2) (List.replicate 4 0) hn

/-- A globally bounded matrix-workspace function adds its ceiling once to the independent
scratch polynomial. This premise covers every dimension list; replacing it by the finite
root-size envelope requires proving that every called matrix shape stays within that root. -/
theorem staticPeak_workspace_le (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (w : ℕ) (hW : ∀ o ds, matrixWorkspace o ds ≤ w) (d : Fin 3 → ℕ) (hn : 2 ≤ d 0) :
    staticPeak (Dense.resources matrixWork matrixWorkspace)
      (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤
      6 * (d 0 * d 0) * d 1 + 32 * (d 0 * d 0) + 4 * d 0 * d 1 +
        7 * d 0 + 2 * d 1 + 24 + w := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  have hAll : ∀ o ds, (Dense.resources matrixWork matrixWorkspace).workspace o ds ≤ w := by
    intro o ds
    cases o with
    | scalar o => exact Nat.zero_le _
    | index o => exact Nat.zero_le _
    | matrix o => exact hW o ds
    | sample o => exact Nat.zero_le _
  apply (stmtPeak_le_zero_add _ w hAll _ _).trans
  apply Nat.add_le_add_right
  have hd : List.ofFn d = [d 0, d 1, d 2] := by
    simp [List.ofFn_succ, Fin.succ]
  simpa only [program, Program.environment, hd] using
    stmtPeak_solve_zero_le (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (d 0) (d 1) (d 2) (List.replicate 4 0) hn

/-- An arbitrary matrix-workspace function contributes only its finite maximum on legal
root-bounded multiplication and QR shapes. No global or monotone workspace bound is assumed. -/
theorem staticPeak_workspaceEnvelope_le (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (d : Fin 3 → ℕ) (hn : 2 ≤ d 0) :
    staticPeak (Dense.resources matrixWork matrixWorkspace)
      (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤
      6 * (d 0 * d 0) * d 1 + 32 * (d 0 * d 0) + 4 * d 0 * d 1 +
        7 * d 0 + 2 * d 1 + 24 + MatrixOp.workspaceEnvelope matrixWorkspace (d 0) := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  have hSupport :
      (stmtCost (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
        (Program.environment (b := 4) d).idx).BoundsWorkspace
          (Dense.resources matrixWork matrixWorkspace).workspace
          (MatrixOp.workspaceEnvelope matrixWorkspace (d 0)) := by
    intro o ds ho
    have h := workspace_le_envelope_of_matrixShape matrixWorkspace
      (program_matrixShapes d o ds ho)
    cases o <;> exact h
  apply (stmtPeak_le_zero_add_on_support _ _ _ _ hSupport).trans
  apply Nat.add_le_add_right
  have hd : List.ofFn d = [d 0, d 1, d 2] := by
    simp [List.ofFn_succ, Fin.succ]
  simpa only [program, Program.environment, hd] using
    stmtPeak_solve_zero_le (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (d 0) (d 1) (d 2) (List.replicate 4 0) hn

/-- The same solver's complete resident memory includes its supplied matrix, parameter
block and output capacities, together with its proven scratch polynomial. The matrix
primitives have zero additional workspace in the selected abstract-cell resource profile. -/
theorem initialBytes_add_staticPeak_zeroWorkspace_le {K : Type} [Inhabited K]
    {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}
    (matrixWork : MatrixOp → List ℕ → ℕ) (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) (hn : 2 ≤ d 0) :
    (problem (K := K) domain admitted).initialBytes d x +
      staticPeak (Dense.resources matrixWork (fun _ _ => 0))
        (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤
      6 * (d 0 * d 0) * d 1 + 36 * (d 0 * d 0) + 4 * d 0 * d 1 +
        8 * d 0 + 2 * d 1 + 27 := by
  rw [initialBytes_problem]
  have h := staticPeak_zeroWorkspace_le matrixWork d hn
  omega

/-- The independent resident-memory polynomial plus one finite matrix-workspace envelope.
The supplied raw inputs and output capacities are included in the same bound. -/
theorem initialBytes_add_staticPeak_workspaceEnvelope_le {K : Type} [Inhabited K]
    {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) (hn : 2 ≤ d 0) :
    (problem (K := K) domain admitted).initialBytes d x +
      staticPeak (Dense.resources matrixWork matrixWorkspace)
        (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤
      6 * (d 0 * d 0) * d 1 + 36 * (d 0 * d 0) + 4 * d 0 * d 1 +
        8 * d 0 + 2 * d 1 + 27 + MatrixOp.workspaceEnvelope matrixWorkspace (d 0) := by
  rw [initialBytes_problem]
  have h := staticPeak_workspaceEnvelope_le matrixWork matrixWorkspace d hn
  omega

end NLAlib.SpectralBisection
