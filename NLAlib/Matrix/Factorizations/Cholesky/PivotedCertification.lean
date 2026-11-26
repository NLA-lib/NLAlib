/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotedResources
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.RoutineFramed

/-!
# Declared diagonal-pivoted PSD Cholesky problem

The source is a real positive-semidefinite square matrix. A blank square factor and blank
absolute pivot log are the only other caller slots. The actual fixed scalar routine certifies
the first-maximum diagonal log, canonical permuted factor, semidefinite Gram identity and
complete off-output frame. The domain includes singular matrices and every order, including
zero. All resident input and output capacities, structural work and scoped scratch are charged.

## Main results

* `NLAlib.Cholesky.PivotedCertification.inputs`: the matrix-only PSD source and blank slots.
* `NLAlib.Cholesky.PivotedCertification.algorithm_checked`: the full checked construction.
-/

@[expose] public section

namespace NLAlib.Cholesky.PivotedCertification

open Ops

/-- One PSD matrix source and two blank outputs: a square factor and its absolute pivot log.
This is distinct from the all-matrix LU domain, which has another square output factor. -/
def inputs :
    (pivotedRightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain
      ℝ 1 3 where
  toInputs := DenseFactorization.matrixInputs [fun n => n * n, id]
    (fun _ A => A.PosSemidef) (fun _ => ⟨1, Matrix.PosSemidef.one⟩)
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.matrixInputs, Codec.matrix, EntryCodec.scalar]

/-- The stored matrix and blank factor/log capacities determine the entire problem. -/
abbrev problem : Problem ℝ 1 3 := inputs.problem

/-- The shared local scalar, comparison, dimension-literal and stored-index profile. Exact
arithmetic is a separate law of the machine used by the numerical certificate. -/
noncomputable def model (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries problem := ScalarIndex.model problem M id

/-- The routine receives exactly the stored source matrix, with no unstored input data. -/
def inputBlocks (d : Fin 1 → ℕ) (x : problem.Input d) : List (List ℝ) :=
  inputs.blocks d x.val.1

/-- The scalar codec supplies the original column-major matrix words; blank outputs supply
capacity but contribute no words to the input relation. -/
theorem blocks_inputs (d : Fin 1 → ℕ) (A : inputs.In d) :
    inputs.blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- The resident caller allocation charges the source matrix, factor matrix and scalar log,
including every initially uninitialized output cell. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 2 * d 0 * d 0 + d 0 := by
  simp [inputs, DenseFactorization.matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- Actual stored log/factor outputs and full source/shape retention, with closed instruction
work, sequential span and caller-plus-scratch cell bounds. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (pivotedRightLooking
    (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => pivotedRightLookingSpec M id) (model M).resources
      inputBlocks inputs.bytes work scratch

/-- The fixed scalar tree certifies every admitted PSD source using local model laws.
The selected indices come from executed scans and stored-index queries; no successful run,
computed factor or host-selected pivot is assumed. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => pivotedRightLookingSpec M id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, hl, hc, hq⟩ := ScalarIndex.laws hI
    exact pivotedRightLooking_meets hs hl hc hq hM
  · intro d hd A hA τ
    rw [blocks_inputs]
    change Matrix (Fin (d 0)) (Fin (d 0)) ℝ at A
    change A.PosSemidef at hA
    change (decodeMatrix id (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix A)).PosSemidef
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

/-- Every real PSD matrix, including singular and empty inputs, is handled by the same fixed
scalar program under every locally admitted interpreter and tape. The actual first-maximum
log determines the symmetric permutation and canonical Gram factor. Source words and all
extents are retained, and the closed work, span and fully charged resident memory bounds hold. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.Cholesky.PivotedCertification
