/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LDL.Routine
public import NLAlib.Matrix.Factorizations.LDL.Resources
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.RoutineFramed

/-!
# Declared stored-entry LDL problem

The fixed scalar LDL routine receives one real square matrix and blank square lower-factor and
diagonal-vector output
buffers. Its admitted matrices have Hermitian symmetry and nonzero canonical elimination
pivots, including the empty
matrix. All data are in the declared source; the model has only local scalar arithmetic,
dimension literals, comparisons and stored-index queries.

## Main results

* `NLAlib.LDL.Certification.inputs`: the input-only domain of the actual factor routine.
* The fixed program and closed resources are in the companion resource module.
* `NLAlib.LDL.Certification.bytes_inputs`: source and output capacity are all charged.
-/

@[expose] public section

namespace NLAlib.LDL.Certification

open Ops

/-- The approved matrix-only canonical-pivot domain, matched to the actual routine interface. -/
def inputs : (factor (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain ℝ 1 3 where
  toInputs := DenseFactorization.ldlInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.ldlInputs, DenseFactorization.matrixInputs, Codec.matrix,
      EntryCodec.scalar]

/-- The problem derived from its source and blank output slots, with no unstored data. -/
abbrev problem : Problem ℝ 1 3 := inputs.problem

/-- Joint local scalar and query contracts on the same real-word machine. Exactness is a
separate `ExactModel id M` hypothesis of a numerical certificate. -/
noncomputable def model (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries problem :=
  ScalarIndex.model problem M id

/-- The source block read by the routine, supplied by the domain's matrix codec. -/
def inputBlocks (d : Fin 1 → ℕ) (x : problem.Input d) : List (List ℝ) :=
  inputs.blocks d x.val.1

/-- Every admitted input is charged for its source, blank square factor and blank pivot vector. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 2 * d 0 * d 0 + d 0 :=
  DenseFactorization.bytes_ldlInputs d

/-- The source uses the declared column-major matrix codec; the blank factors contribute no
input words to the routine. -/
theorem blocks_inputs (d : Fin 1 → ℕ) (A : inputs.In d) :
    inputs.blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- Reported canonical factors, the complete off-output source and shape frame, and closed
work, span and memory bounds for the fixed real-word LU program. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (factor (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => factorSpec id) (model M).resources inputBlocks inputs.bytes work scratch

/-- The actual scalar LDL routine certifies the declared matrix-only problem. Numerical
exactness is a law of the arithmetic machine; every admitted interpreter is obtained from the
same local scalar, comparison and index contracts. Success is proved from those laws and the
input's nonzero canonical pivots, rather than assumed for a computed trace. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => factorSpec id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, _, hc, _⟩ := ScalarIndex.laws hI
    exact factor_meets hs hc hM
  · intro d hd A hA τ
    rw [blocks_inputs]
    change Matrix (Fin (d 0)) (Fin (d 0)) ℝ at A
    change A.IsHermitian ∧ (∀ i : Fin (d 0), gaussState A i.val i i ≠ 0) at hA
    change (decodeMatrix id (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix A)).IsHermitian ∧
      (∀ i : Fin (d 0), gaussState
        (decodeMatrix id (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix A)) i.val i i ≠ 0)
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

/-- At every order, including zero, every real matrix with nonzero canonical elimination
pivots is factored by the same fixed program under every admitted local interpreter and tape.
The decoded outputs are its canonical unit lower factor and pivot diagonal, satisfying IsLDL.
The source and all buffer
extents are retained. Work and sequential span are bounded by the displayed closed cubic;
resident memory includes the source, lower factor and pivot vector and the additional upper
factor, residual, two saved
vectors and three scalar cells. No execution or hardware-performance hypothesis is supplied. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.LDL.Certification
