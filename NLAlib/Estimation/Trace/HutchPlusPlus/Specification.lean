/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Resources
public import NLAlib.Estimation.Trace.HutchPlusPlus.Samples
public import NLAlib.Estimation.Trace.HutchPlusPlus.Math
public import NLAlib.Ops.Profiles.ExactLinear
public import NLAlib.Ops.RoutineProblem

/-!
# Canonical raw-input Hutch++ specification

A raw operator-data block and one uninitialized output cell are the entire supplied
interface. The operator representation is a model choice; no host matrix preprocessing
is executed. The actual adjacent sample windows determine the mathematical estimator.
The complete instrumented budget and an independent workspace polynomial refer to the
same output execution, including all sampling and scoped cleanup.

## Main results

* `NLAlib.HutchPlusPlus.Certification.problem`: raw operator and output buffers.
* `NLAlib.HutchPlusPlus.Certification.specification`: numerical readback and full resources.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus.Certification

open Ops

variable {𝕜 : Type} [RCLike 𝕜]

/-- Zero supplies packed-entry defaults and an explicit raw-data witness. -/
local instance instInhabitedSpecification : Inhabited 𝕜 := ⟨0⟩

/-- The admitted inputs of Hutch++: for a positive probe count, the operator's data, a block of
`dataLength n n` words held by the first operand; the output cell is blank. The words are raw:
how they represent a matrix is chosen by the model (`matrix`). The sketch rank, the row count and
the sketch width are unrestricted. The domain does not depend on the stream. -/
def inputs (dataLength : ℕ → ℕ → ℕ) :
    (estimateRoutine (Op := ExactLinear.Operation) (Tst := CmpTst) 0 dataLength).Domain 𝕜 3 2
    where
  valid d := 0 < d 2
  In d := { ws : List 𝕜 // ws.length = dataLength (d 0) (d 0) }
  accepts _ _ := True
  slot d := ![.stored (Codec.words (dataLength (d 0) (d 0))) id, .blank 1]
  fits := by domain_fits
  faithful d x y h := (Codec.words (dataLength (d 0) (d 0))).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := ⟨![0, 0, 1], Nat.zero_lt_one⟩
  inhabited d _ := ⟨⟨List.replicate (dataLength (d 0) (d 0)) 0, List.length_replicate ..⟩,
    trivial⟩

/-- The operator's words and one blank output cell: the problem of Hutch++. -/
abbrev problem (dataLength : ℕ → ℕ → ℕ) : Problem 𝕜 3 2 := (inputs (𝕜 := 𝕜) dataLength).problem

/-- All raw operator-data payload and the output capacity count as resident cells. -/
theorem initialBytes_problem (dataLength : ℕ → ℕ → ℕ) (d : Fin 3 → ℕ)
    (x : (problem (𝕜 := 𝕜) dataLength).Input d) :
    (problem dataLength).initialBytes d x = dataLength (d 0) (d 0) + 1 := by
  refine ((inputs (𝕜 := 𝕜) dataLength).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.words, List.ofFn_succ]

/-- The canonical manifest retains original calls, comparisons and structural instructions. -/
noncomputable def staticBudget (stream : ℕ) (d : Fin 3 → ℕ) :
    Count (ExactLinear.Operation ⊕ Bookkeeping) CmpTst := staticCost (estimateProgram stream) d

/-- The entire fixed estimator is well typed for the standardized exact-linear signatures. -/
theorem wellTyped_estimateProgram (work workspace : ExactLinear.Operation → List ℕ → ℕ)
    (stream : ℕ) :
    (estimateProgram stream).wellTyped (ExactLinear.resources work workspace)
      (fun _ => .cell) = true := by
  rfl

/-- Primitive workspace is added once to the independent stored-matrix/scalar polynomial. -/
theorem staticPeak_estimateProgram_le (work workspace : ExactLinear.Operation → List ℕ → ℕ)
    (w : ℕ) (hW : ∀ o d, workspace o d ≤ w) (stream : ℕ) (d : Fin 3 → ℕ) :
    staticPeak (ExactLinear.resources work workspace) (estimateProgram stream) d ≤
      2 * d 0 * (d 1 + d 2) + 2 + w := by
  rw [staticPeak_eq,
    (ExactLinear.resources work workspace).queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]
  change stmtPeak workspace (estimate stream) [d 0, d 1, d 2, 0, 0] ≤ _
  exact estimate_peak_le workspace w hW stream (d 0) (d 1) (d 2) 0 0

/-- Actual sample windows, exact estimator readback, and full execution resources.
Complex entries are abstract scalar cells; physical storage encodings require another model. -/
noncomputable def specification (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) (w stream : ℕ) :
    Specification ExactLinear.Operation CmpTst (problem (𝕜 := 𝕜) dataLength) where
  budget := staticBudget stream
  scratch d := 2 * d 0 * (d 1 + d 2) + 2 + w
  work d := (ExactLinear.resources work workspace).work (staticBudget stream d)
  span d := (ExactLinear.resources work workspace).span (staticBudget stream d)
  memory d := dataLength (d 0) (d 0) + 1 + (2 * d 0 * (d 1 + d 2) + 2 + w)
  good d x tape _ m := m.pos = d 0 * (d 1 + d 2) ∧ m.store.length = 2 ∧
    m.store.readBlock 1 0 1 = some [hutchpp (matrix (d 0) (d 0) x.val.1.val)
      (sampleMatrices stream (d 0) (d 1) (d 2) tape).1
      (sampleMatrices stream (d 0) (d 1) (d 2) tape).2]

end NLAlib.HutchPlusPlus.Certification
