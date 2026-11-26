/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledResources
public import NLAlib.Matrix.Factorizations.LU.ScaledRoutine
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.RoutineFramed

/-!
# Declared fixed-original-scale LU problem

Every real square matrix is admitted. Two blank square factors and a blank row-history
vector are the only other caller slots. Original row norms are computed once from the copied
source, transported by actual row exchanges and used by the executed weighted selector.
Singular matrices, zero original rows and order zero are included. No unweighted bound on
lower multipliers or native floating-point accuracy claim is part of this exact certificate.

## Main results

* `NLAlib.LU.ScaledCertification.inputs`: the all-matrix source and three blank outputs.
* `NLAlib.LU.ScaledCertification.algorithm_checked`: the full fixed-scale construction.
-/

@[expose] public section

namespace NLAlib.LU.ScaledCertification

open Ops

/-- Every real matrix and three blank outputs: two square factors and the actual current-row
swap history. Scales are computed inside the program and are not undeclared input data. -/
def inputs :
    (factorScaled (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).Domain
      ℝ 1 4 where
  toInputs := DenseFactorization.rowPivotInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.rowPivotInputs, DenseFactorization.matrixInputs,
      Codec.matrix, EntryCodec.scalar]

/-- The stored matrix and blank factor/history capacities determine the entire problem. -/
abbrev problem : Problem ℝ 1 4 := inputs.problem

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

/-- The resident caller allocation charges the source, two factors and the row log,
including every initially uninitialized output cell. -/
theorem bytes_inputs (d : Fin 1 → ℕ) : inputs.bytes d = 3 * d 0 * d 0 + d 0 :=
  DenseFactorization.bytes_rowPivotInputs d

/-- Actual stored factors and row history, with full source/shape retention and closed
instruction work, sequential span and caller-plus-scratch cell bounds. -/
noncomputable def specification (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries problem :=
  (factorScaled
    (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).framedSpecification
    (fun _ _ => factorScaledSpec id) (model M).resources
      inputBlocks inputs.bytes work scratch

/-- The fixed scalar tree certifies every real input using local model laws. The selected
rows come from executed weighted scans and stored-index queries. Success and canonical factors
are proved from the source, without a run premise, pivot input or nonsingularity condition. -/
noncomputable def algorithm (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model M) (specification M) := by
  apply inputs.certifyFramed (fun _ _ => factorScaledSpec id) work scratch
  · intro d hd X I hI
    obtain ⟨hs, hl, hc, hq⟩ := ScalarIndex.laws hI
    exact factorScaled_meets hs hc hl hq hM
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
fixed original-scale program under every locally admitted interpreter and tape. The actual
row history determines the source permutation and canonical LU factors; the existing
weighted-pivot prefix is reported without a uniform multiplier bound. Source words,
all extents and off-output cells are retained; closed work, span and fully charged resident
memory bounds hold for the actual instruction tree. -/
theorem algorithm_checked (M : Machine ℝ) (hM : ExactModel id M) :
    inputs.Checked (algorithm M hM) := inputs.checked_all _

end NLAlib.LU.ScaledCertification
