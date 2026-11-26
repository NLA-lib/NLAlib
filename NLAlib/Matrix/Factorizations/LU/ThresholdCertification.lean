/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ThresholdResources
public import NLAlib.Matrix.Factorizations.DenseInputs
public import NLAlib.Ops.RoutineFramed

/-!
# Declared threshold-pivot LU problem

Every real square matrix is admitted. Two blank square factor buffers and one blank scalar
history vector are the only other caller slots. Actual scans and stored-index queries
produce the current-position row log; replay gives canonical factors of the
permuted source. Singular matrices and order zero are included. Full caller capacities and
additional scoped storage are charged, together with structural work and sequential span.
The rational threshold is fixed before the matrix data, lies in `(0, 1]`, and its literal is
exact under the numerical model. Equality in the threshold test accepts the diagonal.

## Main results

* `NLAlib.LU.ThresholdCertification.inputs`: the all-matrix source and three blank outputs.
* `NLAlib.LU.ThresholdCertification.algorithm_checked`: the full checked construction.
-/

@[expose] public section

namespace NLAlib.LU.ThresholdCertification

open Ops

/-- Every real square matrix and three blank outputs: two square factors and one actual
current-position row-swap history. No nonsingularity or host-selected pivot is admitted. -/
def inputs (threshold : ℚ) :
    (factorThreshold (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).Domain
      ℝ 1 4 where
  toInputs := DenseFactorization.rowPivotInputs
  fits := by
    domain_fits
    all_goals simp [DenseFactorization.rowPivotInputs, DenseFactorization.matrixInputs,
      Codec.matrix, EntryCodec.scalar]

/-- The stored matrix and blank factor/history capacities determine the entire problem. -/
abbrev problem (threshold : ℚ) : Problem ℝ 1 4 := (inputs threshold).problem

/-- The shared local scalar, comparison, dimension-literal and stored-index profile. Exact
arithmetic is a separate law of the machine used by the numerical certificate. -/
noncomputable def model (threshold : ℚ) (M : Machine ℝ) :
    AccessModel ScalarIndex.Operation ScalarIndex.Queries (problem threshold) :=
  ScalarIndex.model (problem threshold) M id

/-- The routine receives exactly the stored source matrix, with no unstored input data. -/
def inputBlocks (threshold : ℚ) (d : Fin 1 → ℕ) (x : (problem threshold).Input d) : List (List ℝ) :=
  (inputs threshold).blocks d x.val.1

/-- The scalar codec supplies the original column-major matrix words; blank outputs supply
capacity but contribute no words to the input relation. -/
theorem blocks_inputs (threshold : ℚ) (d : Fin 1 → ℕ) (A : (inputs threshold).In d) :
    (inputs threshold).blocks d A = [(EntryCodec.scalar ℝ).packFinMatrix A] := rfl

/-- The resident caller allocation charges the source, two factors and the scalar row log,
including every initially uninitialized output cell. -/
theorem bytes_inputs (threshold : ℚ) (d : Fin 1 → ℕ) :
    (inputs threshold).bytes d = 3 * d 0 * d 0 + d 0 :=
  DenseFactorization.bytes_rowPivotInputs d

/-- Actual stored factors and the row log, with full source/shape retention and closed
instruction work, sequential span and caller-plus-scratch cell bounds. -/
noncomputable def specification (threshold : ℚ) (M : Machine ℝ) :
    Specification ScalarIndex.Operation ScalarIndex.Queries (problem threshold) :=
  (factorThreshold
    (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).framedSpecification
    (fun _ _ => factorThresholdSpec id threshold) (model threshold M).resources
      (inputBlocks threshold) (inputs threshold).bytes work scratch

/-- The fixed scalar tree certifies every real input using local model laws. Every selected
row comes from executed scans and stored-index queries. Success and canonical factors
are proved from the source, without a run premise, pivot input or nonsingularity condition. -/
noncomputable def algorithm (threshold : ℚ) (hτ : 0 < threshold) (hτ₁ : threshold ≤ 1)
    (M : Machine ℝ) (hM : ExactModel id M) :
    Algorithm (model threshold M) (specification threshold M) := by
  apply (inputs threshold).certifyFramed (fun _ _ => factorThresholdSpec id threshold) work scratch
  · intro d hd X I hI
    obtain ⟨hs, hl, hc, hq⟩ := ScalarIndex.laws hI
    exact factorThreshold_meets threshold hτ hτ₁ hs hc hl hq hM
  · intro d hd A hA τ
    trivial
  · intro d hd
    exact staticPeak_program_le threshold d
  · intro o d
    exact le_rfl
  · intro k d
    exact le_rfl
  · intro q d
    exact le_rfl
  · intro d hd
    exact (eval_countPoly_program threshold d).le

/-- Every real square matrix, including singular and empty inputs, is handled by the same
fixed threshold-pivot program under every locally admitted interpreter and tape. The
actual row history determines a permutation and canonical LU factors. Source words,
all extents and off-output cells are retained; closed work, span and fully charged resident
memory bounds hold for the actual instruction tree. -/
theorem algorithm_checked (threshold : ℚ) (hτ : 0 < threshold) (hτ₁ : threshold ≤ 1)
    (M : Machine ℝ) (hM : ExactModel id M) :
    (inputs threshold).Checked (algorithm threshold hτ hτ₁ M hM) :=
  (inputs threshold).checked_all _

end NLAlib.LU.ThresholdCertification
