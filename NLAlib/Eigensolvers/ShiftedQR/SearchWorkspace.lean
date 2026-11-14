/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Kernels
public import NLAlib.Eigensolvers.ShiftedQR.GridSearch
public import NLAlib.Eigensolvers.ShiftedQR.Workspace

/-!
# Workspace of the streaming exceptional-shift search

The actual two-dimensional grid loop stores one candidate at a time. Its scratch bound is
independent of grid resolution and of the number of repeated shifted QR steps per trial.
Caller-owned candidate and output views are excluded from stored workspace here.

## Main results

* `NLAlib.ShiftedQR.searchGridWithScratch_storedWorkspace_le`: two matrices plus fourteen words.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

omit [Has IndexOp Op] [Has CmpTst Tst] in
/-- The product loop allocates three scratch words once for the entire subdiagonal. -/
theorem subdiagProduct_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (subdiagProduct (Tst := Tst)).body idx ≤ 3 := by
  change 3 + _ ≤ 3 + 0
  exact Nat.add_le_add_left (stmtPeak_frame_le_uniform
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le) _ _ idx) _

/-- Acceptance uses the caller-owned scan and product buffers and three transient words. -/
theorem acceptTrialWithScratch_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (acceptTrialWithScratch (Tst := Tst)).body idx ≤ 3 := by
  change max _ (max _ _) ≤ 3
  refine max_le ?_ (max_le ?_ ?_)
  · exact (stmtPeak_zero_of_allocationFree (by rfl) idx).le.trans (Nat.zero_le _)
  · exact stmtPeak_frame_le_uniform subdiagProduct_storedWorkspace_le _ _ idx
  · exact (stmtPeak_zero_of_allocationFree (by rfl) idx).le.trans (Nat.zero_le _)

/-- The six retained scan/product words coexist with at most three transient words. -/
theorem acceptTrial_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (acceptTrial (Tst := Tst)).body idx ≤ 9 := by
  change 5 + (1 + _) ≤ 5 + (1 + 3)
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (stmtPeak_frame_le_uniform acceptTrialWithScratch_storedWorkspace_le _ _ idx) 1) 5

/-- A trial shares its QR and acceptance arenas sequentially, for any repetition count. -/
theorem trial_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (trial (Tst := Tst)).body (n :: k :: offs) ≤
      4 * (n * n) + 14 := by
  change max _ (max _ _) ≤ _
  refine max_le ?_ (max_le ?_ ?_)
  · exact (stmtPeak_zero_of_allocationFree (by rfl) (n :: k :: offs)).le.trans
      (Nat.zero_le _)
  · exact stmtPeak_frame_le (by rfl)
      (fun os => repeatedStep_storedWorkspace_le n k os)
  · exact (stmtPeak_frame_le_uniform acceptTrial_storedWorkspace_le _ _
      (n :: k :: offs)).trans (by omega)

/-- Guarding a candidate with the persistent acceptance flag adds no stored workspace. -/
theorem tryCandidate_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (tryCandidate (Tst := Tst)).body (n :: k :: offs) ≤
      4 * (n * n) + 14 := by
  change max _ 0 ≤ _
  exact max_le (stmtPeak_frame_le (by rfl)
    (fun os => trial_storedWorkspace_le n k os)) (Nat.zero_le _)

omit [Has CmpTst Tst] in
/-- Forming one complex grid point uses nine transient real words. -/
theorem gridPoint_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (gridPoint (Tst := Tst)).body idx ≤ 9 := by
  change 9 + _ ≤ 9 + 0
  exact Nat.add_le_add_left (stmtPeak_frame_le_uniform
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le) _ _ idx) _

/-- Coordinate formation and trial computation reuse their transient storage. -/
theorem gridCandidate_storedWorkspace_le (n k D i j : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (gridCandidate (Tst := Tst)).body
      (n :: k :: D :: i :: j :: offs) ≤ 4 * (n * n) + 14 := by
  change max _ _ ≤ _
  refine max_le ?_ ?_
  · exact (stmtPeak_frame_le_uniform gridPoint_storedWorkspace_le _ _
      (n :: k :: D :: i :: j :: offs)).trans (by omega)
  · exact stmtPeak_frame_le (by rfl)
      (fun os => tryCandidate_storedWorkspace_le n k os)

/-- Streaming the entire grid requires two matrix arenas and fourteen transient words,
independently of its `(D+1)^2` candidates and of the repetition count `k`. -/
theorem searchGridWithScratch_storedWorkspace_le (n k D : ℕ) (offs : List ℕ)
    (hOffsets : offs.length = 9) :
    stmtPeak (fun (_ : Op) _ => 0) (searchGridWithScratch (Tst := Tst)).body
      (n :: k :: D :: offs) ≤ 4 * (n * n) + 14 := by
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro j _
  apply stmtPeak_frame_le
    (d := [n, k, D, i, j])
  · simp [IExp.evalList, IExp.eval, hOffsets]
  · intro os
    exact gridCandidate_storedWorkspace_le n k D i j os

/-- Under the declared QR resource model, supported primitive workspace is added only once.
The premise bounds actual call shapes rather than assuming that spectral kernels are free. -/
theorem searchGridWithScratch_workspace_le
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    (n k D primitiveWorkspace : ℕ) (offs : List ℕ) (hOffsets : offs.length = 9)
    (hPrimitive : (stmtCost (searchGridWithScratch
      (Op := NLAlib.ShiftedQR.Op) (Tst := NLAlib.ShiftedQR.Tst)).body
      (n :: k :: D :: offs)).BoundsWorkspace
      (resources kernelWork kernelWorkspace).workspace primitiveWorkspace) :
    stmtPeak (resources kernelWork kernelWorkspace).workspace
      (searchGridWithScratch (Op := NLAlib.ShiftedQR.Op) (Tst := NLAlib.ShiftedQR.Tst)).body
      (n :: k :: D :: offs) ≤ 4 * (n * n) + 14 + primitiveWorkspace := by
  exact (stmtPeak_le_zero_add_on_support _ primitiveWorkspace _ _ hPrimitive).trans
    (Nat.add_le_add_right (searchGridWithScratch_storedWorkspace_le n k D offs hOffsets) _)

end NLAlib.ShiftedQR
