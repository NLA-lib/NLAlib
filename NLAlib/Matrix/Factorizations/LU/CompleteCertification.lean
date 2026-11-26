/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.CompleteResources
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.RoutineFramed

/-!
# Declared complete-pivot LU problem

Every real square matrix is admitted. Two blank square factor buffers and two blank scalar
history vectors are the only other caller slots. Actual scans and stored-index queries
produce both current-position logs; independent replay gives canonical factors of the
permuted source. Singular matrices and order zero are included. Full caller capacities and
additional scoped storage are charged, together with structural work and sequential span.

## Main results

* `NLAlib.LU.CompleteCertification.inputs`: the all-matrix source and four blank outputs.
* `NLAlib.LU.CompleteCertification.algorithm_checked`: the full checked construction.
-/

@[expose] public section

namespace NLAlib.LU.CompleteCertification

open Ops

/-- Every real square matrix and four blank outputs: two square factors and two actual
current-position swap histories. No nonsingularity or host-selected pivot is admitted. -/
def inputs :
    (factorComplete (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain
      ℝ 1 5 where
  toInputs := DenseFactorization.completePivotInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.completePivotInputs, DenseFactorization.matrixInputs,
      Codec.matrix, EntryCodec.scalar]

/-- The stored matrix and blank factor/history capacities determine the entire problem. -/
abbrev problem : Problem ℝ 1 5 := inputs.problem

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

/-- The resident caller allocation charges the source, two factors and both scalar logs,
including every initially uninitialized output cell. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 3 * d 0 * d 0 + 2 * d 0 :=
  DenseFactorization.bytes_completePivotInputs d

/-- Actual stored factors and independent logs, with full source/shape retention and closed
instruction work, sequential span and caller-plus-scratch cell bounds. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (factorComplete
    (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => factorCompleteSpec id) (model M).resources
      inputBlocks inputs.bytes work scratch

/-- The fixed scalar tree certifies every real input using local model laws. Both selected
indices come from executed scans and stored-index queries. Success and canonical factors
are proved from the source, without a run premise, pivot input or nonsingularity condition. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => factorCompleteSpec id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, hl, hc, hq⟩ := ScalarIndex.laws hI
    exact factorComplete_meets hs hc hl hq hM
  · intro d hd A hA τ
    trivial
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

/-- Every real square matrix, including singular and empty inputs, is handled by the same
fixed complete-pivot program under every locally admitted interpreter and tape. The two
actual histories determine independent permutations and canonical LU factors. Source words,
all extents and off-output cells are retained; closed work, span and fully charged resident
memory bounds hold for the actual instruction tree. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.LU.CompleteCertification
