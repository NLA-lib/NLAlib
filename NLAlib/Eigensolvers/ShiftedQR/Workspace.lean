/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.MultiStep
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Workspace

/-!
# Dimension bounds for exact shifted QR workspace

Stored workspace counts real-word cells allocated by the actual scalar programs. Matrix
inputs and caller-owned outputs are excluded. Loop iterations reuse their scoped scratch.
Primitive workspace can be added separately with the shared support-restricted bound.

## Main results

* `NLAlib.ShiftedQR.shiftedStep_storedWorkspace_le`: one matrix plus fourteen words.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- The seven coefficient scratch words are reused across every scalar branch. -/
theorem coefficients_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (coefficients (Tst := Tst)).body idx ≤ 7 := by
  change 7 + _ ≤ 7
  have h := stmtPeak_frame_le_uniform (W := fun (_ : Op) _ => 0)
    (p := 0) (body := (coefficientsWithScratch (Tst := Tst)).body)
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le)
  change _ + _ ≤ _ + 0
  exact Nat.add_le_add_left (h _ _ idx) _

omit [Has CmpTst Tst] in
/-- One row-rotation sweep reserves ten scalar scratch words, independently of its length. -/
theorem rotateRows_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (rotateRows (Tst := Tst)).body idx ≤ 10 := by
  change 10 + _ ≤ 10
  have h := stmtPeak_frame_le_uniform (W := fun (_ : Op) _ => 0)
    (p := 0) (body := (rotateRowsWithScratch (Tst := Tst)).body)
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le)
  change _ + _ ≤ _ + 0
  exact Nat.add_le_add_left (h _ _ idx) _

omit [Has CmpTst Tst] in
/-- Column rotations use the same ten-word arena as row rotations. -/
theorem rotateColumns_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (rotateColumns (Tst := Tst)).body idx ≤ 10 := by
  change 10 + _ ≤ 10
  have h := stmtPeak_frame_le_uniform (W := fun (_ : Op) _ => 0)
    (p := 0) (body := (rotateColumnsWithScratch (Tst := Tst)).body)
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le)
  change _ + _ ≤ _ + 0
  exact Nat.add_le_add_left (h _ _ idx) _

/-- Coefficient formation and three matrix rotations share their arenas sequentially. -/
theorem round_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (round (Tst := Tst)).body idx ≤ 10 := by
  change max _ (max _ (max _ _)) ≤ 10
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · exact (stmtPeak_frame_le_uniform coefficients_storedWorkspace_le _ _ idx).trans
      (by omega)
  · exact stmtPeak_frame_le_uniform rotateRows_storedWorkspace_le _ _ idx
  · exact stmtPeak_frame_le_uniform rotateRows_storedWorkspace_le _ _ idx
  · exact stmtPeak_frame_le_uniform rotateColumns_storedWorkspace_le _ _ idx

/-- Reusing each round's arenas makes the bound independent of the number of rotations. -/
theorem sweep_storedWorkspace_le (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (sweep (Tst := Tst)).body idx ≤ 10 := by
  apply Finset.sup_le
  intro i _
  exact stmtPeak_frame_le_uniform round_storedWorkspace_le _ _ (idx ++ [i])

/-- One actual shifted QR step allocates one complex matrix and fourteen real words.
The estimate includes the four retained coefficients and the largest ten-word rotation arena. -/
theorem shiftedStep_storedWorkspace_le (n : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (shiftedStep (Tst := Tst)).body (n :: offs) ≤
      2 * (n * n) + 14 := by
  simp only [shiftedStep, stmtPeak_alloc, IExp.eval, List.getElem?_cons_zero,
    Option.getD_some]
  change 2 * (n * n) + (4 + max _ _) ≤ _
  have hi := stmtPeak_frame_le_uniform (W := fun (_ : Op) _ => 0)
    (p := 0) (body := (initializeState (Tst := Tst)).body)
    (fun i => (stmtPeak_zero_of_allocationFree (by rfl) i).le)
  have hs := stmtPeak_frame_le_uniform (sweep_storedWorkspace_le (Op := Op) (Tst := Tst))
  apply Nat.add_le_add_left
  change 4 + _ ≤ 4 + 10
  apply Nat.add_le_add_left
  exact max_le ((hi _ _ (n :: offs)).trans (by omega)) (hs _ _ (n :: offs))

/-- The scalar copy-back does not require a second arena while one shifted step runs. -/
theorem stepInPlaceWithScratch_storedWorkspace_le (n : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (stepInPlaceWithScratch (Tst := Tst)).body
      (n :: offs) ≤ 2 * (n * n) + 14 := by
  change max _ _ ≤ _
  refine max_le ?_ ?_
  · exact stmtPeak_frame_le (by rfl)
      (fun os => shiftedStep_storedWorkspace_le n os)
  · exact (stmtPeak_zero_of_allocationFree (by rfl) (n :: offs)).le.trans
      (Nat.zero_le _)

/-- Repetition reuses the caller-owned temporary matrix regardless of the iteration count. -/
theorem repeatedStepWithScratch_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (repeatedStepWithScratch (Tst := Tst)).body
      (n :: k :: offs) ≤ 2 * (n * n) + 14 := by
  apply Finset.sup_le
  intro i _
  exact stmtPeak_frame_le (by rfl)
    (fun os => stepInPlaceWithScratch_storedWorkspace_le n os)

/-- The complete repeated-shift implementation uses two complex matrices plus fourteen words.
The number of repeated steps does not appear in this bound. -/
theorem repeatedStep_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (repeatedStep (Tst := Tst)).body
      (n :: k :: offs) ≤ 4 * (n * n) + 14 := by
  simp only [repeatedStep, stmtPeak_alloc, IExp.eval, List.getElem?_cons_zero,
    Option.getD_some]
  calc
    _ ≤ 2 * (n * n) + (2 * (n * n) + 14) := Nat.add_le_add_left
      (stmtPeak_frame_le (by rfl)
        (fun os => repeatedStepWithScratch_storedWorkspace_le n k os)) _
    _ ≤ _ := by omega

/-- Stored distinct shifts reuse the same matrix arena as repeated identical shifts. -/
theorem multiStepWithScratch_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (multiStepWithScratch (Tst := Tst)).body
      (n :: k :: offs) ≤ 2 * (n * n) + 14 := by
  apply Finset.sup_le
  intro i _
  exact stmtPeak_frame_le (by rfl)
    (fun os => stepInPlaceWithScratch_storedWorkspace_le n os)

/-- Distinct shift lists also require two matrices and fourteen words, independent of length. -/
theorem multiStep_storedWorkspace_le (n k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (multiStep (Tst := Tst)).body
      (n :: k :: offs) ≤ 4 * (n * n) + 14 := by
  simp only [multiStep, stmtPeak_alloc, IExp.eval, List.getElem?_cons_zero,
    Option.getD_some]
  calc
    _ ≤ 2 * (n * n) + (2 * (n * n) + 14) := Nat.add_le_add_left
      (stmtPeak_frame_le (by rfl)
        (fun os => multiStepWithScratch_storedWorkspace_le n k os)) _
    _ ≤ _ := by omega

end NLAlib.ShiftedQR
