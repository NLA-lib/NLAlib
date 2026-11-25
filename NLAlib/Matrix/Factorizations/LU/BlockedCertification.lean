/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRoutine
public import NLAlib.Matrix.Factorizations.LU.BlockedResources
public import NLAlib.Matrix.Factorizations.DenseBlockedInputs
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.RoutineFramed

/-!
# Declared stored-entry blocked LU problem

The fixed blocked scalar LU routine receives one real square matrix and two blank square output
buffers. Its admitted matrices have nonzero canonical elimination pivots, including the empty
matrix. The dimensions also supply a positive block size and its exact ceiling block count.
All data are in the declared source; the model has only local scalar arithmetic,
dimension literals, comparisons and stored-index queries.

## Main results

* `NLAlib.LU.BlockedCertification.inputs`: the input-only domain of the actual factor routine.
* The fixed program and closed resources are in the companion resource module.
* `NLAlib.LU.BlockedCertification.bytes_inputs`: source and output capacity are all charged.
-/

@[expose] public section

namespace NLAlib.LU.BlockedCertification

open Ops

/-- The original matrix-only canonical-pivot domain with positive block size and exact
ceiling count, matched to the actual routine interface. -/
def inputs :
    (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain ℝ 3 3 where
  toInputs := DenseFactorization.blockedLuInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.blockedLuInputs, DenseFactorization.blockedMatrixInputs,
      DenseFactorization.matrixInputs, Codec.matrix, EntryCodec.scalar]

/-- The problem derived from its source and blank output slots, with no unstored data. -/
abbrev problem : Problem ℝ 3 3 := inputs.problem

/-- Joint local scalar and query contracts on the same real-word machine. Exactness is a
separate `ExactModel id M` hypothesis of a numerical certificate. -/
noncomputable def model (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries problem :=
  ScalarIndex.model problem M id

/-- The source block read by the routine, supplied by the domain's matrix codec. -/
def inputBlocks (d : Fin 3 → ℕ) (x : problem.Input d) : List (List ℝ) :=
  inputs.blocks d x.val.1

/-- Every admitted input is charged for its source and both blank square outputs. -/
theorem bytes_inputs (d : Fin 3 → ℕ) : inputs.bytes d = 3 * d 0 * d 0 :=
  DenseFactorization.bytes_blockedLuInputs d

/-- The source uses the declared column-major matrix codec; the blank factors contribute no
input words to the routine. -/
theorem blocks_inputs (d : Fin 3 → ℕ) (A : inputs.In d) :
    inputs.blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- Reported canonical factors, the complete off-output source and shape frame, and closed
work, span and memory bounds for the fixed real-word LU program. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => factorBlockedSpec id) (model M).resources inputBlocks inputs.bytes work scratch

/-- The actual scalar LU routine certifies the declared matrix-only problem. Numerical
exactness is a law of the arithmetic machine; every admitted interpreter is obtained from the
same local scalar, comparison and index contracts. Success is proved from those laws and the
input's nonzero canonical pivots, rather than assumed for a computed trace. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => factorBlockedSpec id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, _, hc, _⟩ := ScalarIndex.laws hI
    exact factorBlocked_meets hs hc hM
  · intro d hd A hA τ
    rw [blocks_inputs]
    change Matrix (Fin (d 0)) (Fin (d 0)) ℝ at A
    change (∀ i : Fin (d 0), gaussState A i.val i i ≠ 0) at hA
    change 0 < d 1 ∧ d 2 = (d 0 + d 1 - 1) / d 1 ∧
      ∀ i : Fin (d 0), gaussState
        (decodeMatrix id (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix A)) i.val i i ≠ 0
    refine ⟨hd.1, hd.2, ?_⟩
    unfold decodeMatrix
    rw [EntryCodec.matrix_packFinMatrix]
    simpa only [Matrix.map_id] using hA
  · intro d hd
    exact staticPeak_program_le d
  · intro o d
    exact le_rfl
  · intro k d
    exact le_rfl
  · intro q d
    exact le_rfl
  · intro d hd
    exact (eval_countPoly_program d).le

/-- Every admitted matrix is factored under every interpreter satisfying the declared local
contracts and every tape. The same fixed scalar tree returns canonical factors, retains its
source and buffer shape, and obeys closed instruction/span and caller-plus-scratch bounds.
The matrix hypothesis refers only to original Gaussian pivots; the block controls include
nondividing, oversized and empty-order choices. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.LU.BlockedCertification
