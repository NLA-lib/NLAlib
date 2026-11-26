/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.Resources
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.RoutineFramed

/-!
# Declared stored-entry Cholesky certificates

The source is one real square matrix; the only other caller slot is a blank square factor.
Both certificates use the same confined local scalar/index/compare profile and retain the
complete off-output frame, including the source and every buffer extent. The strict input
domain gives the ordinary positive-diagonal Cholesky predicate. The semidefinite domain
includes singular matrices and states nonnegative diagonal and the exact Gram identity.

## Main results

* `NLAlib.Cholesky.Certification.algorithm_checked`: positive-definite exact factorization.
* `NLAlib.Cholesky.SemidefiniteCertification.algorithm_checked`: singular-inclusive exact
  factorization with guarded zero pivots.
-/

@[expose] public section

namespace NLAlib.Cholesky.Certification

open Ops

/-- The matrix-only positive-definite domain fitted to the actual scalar routine interface. -/
def inputs :
    (rightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain ℝ 1 2 where
  toInputs := DenseFactorization.spdInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.spdInputs, DenseFactorization.matrixInputs, Codec.matrix,
      EntryCodec.scalar]

/-- The declared source and blank factor slots determine the entire problem. -/
abbrev problem : Problem ℝ 1 2 := inputs.problem

/-- Only local scalar, comparison, literal and stored-index contracts; numerical exactness
is a separate arithmetic-machine hypothesis of the certificate. -/
noncomputable def model (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries problem :=
  ScalarIndex.model problem M id

/-- The routine's input words are exactly the column-major source matrix. -/
def inputBlocks (d : Fin 1 → ℕ) (x : problem.Input d) : List (List ℝ) :=
  inputs.blocks d x.val.1

/-- The declared source codec supplies one matrix block and no words from blank outputs. -/
theorem blocks_inputs (d : Fin 1 → ℕ) (A : inputs.In d) :
    inputs.blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- Both source and blank factor capacity are charged, including uninitialized cells. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 2 * d 0 * d 0 :=
  DenseFactorization.bytes_spdInputs d

/-- Actual numerical outputs and full source/shape retention, with closed total instruction
work, sequential span, and caller-plus-scratch memory. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (rightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => rightLookingSpec M id) (model M).resources inputBlocks inputs.bytes work scratch

/-- The actual routine constructs its exact factor from the original mathematical input
condition. No run, computed-pivot or output-factor premise is supplied. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => rightLookingSpec M id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, _, hc, _⟩ := ScalarIndex.laws hI
    exact rightLooking_meets hs hM
  · intro d hd A hA τ
    rw [blocks_inputs]
    change Matrix (Fin (d 0)) (Fin (d 0)) ℝ at A
    change A.PosDef at hA
    change (decodeMatrix id (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix A)).PosDef
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

/-- Every admitted positive-definite real matrix, including order zero, is factored by the
same fixed scalar program under every locally admitted interpreter and tape. The stored factor
is canonical and its upper words are literal zeros; the numerical postcondition gives the
appropriate diagonal sign and exact Gram identity. The source and all extents are retained.
Work and sequential span satisfy the closed instruction cubic, and resident memory charges
the two caller matrices plus the square residual, two saved vectors and three scalar cells. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.Cholesky.Certification

namespace NLAlib.Cholesky.SemidefiniteCertification

open Ops

/-- The matrix-only positive-semidefinite domain fitted to the actual scalar routine interface. -/
def inputs :
    (semidefiniteRightLooking
      (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain ℝ 1 2 where
  toInputs := DenseFactorization.psdInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.psdInputs, DenseFactorization.matrixInputs, Codec.matrix,
      EntryCodec.scalar]

/-- The declared source and blank factor slots determine the entire problem. -/
abbrev problem : Problem ℝ 1 2 := inputs.problem

/-- Only local scalar, comparison, literal and stored-index contracts; numerical exactness
is a separate arithmetic-machine hypothesis of the certificate. -/
noncomputable def model (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries problem :=
  ScalarIndex.model problem M id

/-- The routine's input words are exactly the column-major source matrix. -/
def inputBlocks (d : Fin 1 → ℕ) (x : problem.Input d) : List (List ℝ) :=
  inputs.blocks d x.val.1

/-- The declared source codec supplies one matrix block and no words from blank outputs. -/
theorem blocks_inputs (d : Fin 1 → ℕ) (A : inputs.In d) :
    inputs.blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- Both source and blank factor capacity are charged, including uninitialized cells. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 2 * d 0 * d 0 :=
  DenseFactorization.bytes_psdInputs d

/-- Actual numerical outputs and full source/shape retention, with closed total instruction
work, sequential span, and caller-plus-scratch memory. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (semidefiniteRightLooking
    (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => semidefiniteRightLookingSpec M id) (model M).resources
      inputBlocks inputs.bytes work scratch

/-- The actual routine constructs its exact factor from the original mathematical input
condition. No run, computed-pivot or output-factor premise is supplied. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => semidefiniteRightLookingSpec M id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, _, hc, _⟩ := ScalarIndex.laws hI
    exact semidefiniteRightLooking_meets hs hM hc
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

/-- Every admitted positive-semidefinite real matrix, including order zero, is factored by the
same fixed scalar program under every locally admitted interpreter and tape. The stored factor
is canonical and its upper words are literal zeros; the numerical postcondition gives the
appropriate diagonal sign and exact Gram identity. The source and all extents are retained.
Work and sequential span satisfy the closed instruction cubic, and resident memory charges
the two caller matrices plus the square residual, two saved vectors and three scalar cells. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.Cholesky.SemidefiniteCertification

