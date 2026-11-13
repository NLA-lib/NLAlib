/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Certification
public import NLAlib.Estimation.Trace.HutchPlusPlusTail
public import NLAlib.Ops.Probability

/-!
# Gaussian accuracy of the actual Hutch++ output

Independent real Gaussian sketch and probe matrices determine an explicit packed tape. Its
actual adjacent windows are the same matrices appearing in the pure Hutch++ tail theorem.
A total certificate transfers that bound to the stored estimate, retaining the word output,
sample advance, cleanup and every resource bound on the same counted run.

The input matrix is read through the chosen stored-operator representation. It is fixed before
the random sample; no positive-semidefinite assumption or preprocessing of its words is used.

## Main results

* `NLAlib.HutchPlusPlus.StoresApproxTrace`: actual scalar output near the input trace.
* `NLAlib.HutchPlusPlus.measureReal_not_accepts_le_of_hasLaw_gaussianMatrix`: concrete Gaussian
  accuracy and complete resource failure bound for a certificate of the actual word specification.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops MeasureTheory ProbabilityTheory Certification
open scoped Matrix

/-- The output block contains an actual estimate within the stated absolute trace tolerance. -/
def StoresApproxTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (tolerance : ℝ)
    (out : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ∃ estimate : ℝ, m.store.readBlock out.1 out.2 1 = some [estimate] ∧
    |A.trace - estimate| < tolerance

/-- Gaussian matrix laws and independence give the existing explicit Hutch++ tail bound
for the actual stored output, with all same-run resource and word guarantees retained.
The positive sketch width and embedding dimension are numerical assumptions; the word
certificate itself admits rank deficiency and unrestricted sketch width. No execution-success
hypothesis or unknown reference failure estimate is supplied.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]. -/
theorem measureReal_not_accepts_le_of_hasLaw_gaussianMatrix
    (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List ℝ → Matrix (Fin m) (Fin n) ℝ)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) (w stream : ℕ)
    (algorithm : Algorithm
      (ExactLinear.model (problem (𝕜 := ℝ) dataLength) dataLength matrix work workspace)
      (specification dataLength matrix work workspace w stream))
    {d : Fin 3 → ℕ} (hProbes : 0 < d 2) (hSketch : 0 < d 1)
    (input : (problem (𝕜 := ℝ) dataLength).Input d)
    (I : Interp ExactLinear.Operation CmpTst ℝ)
    (hI : (ExactLinear.model (problem (𝕜 := ℝ) dataLength)
      dataLength matrix work workspace).contracts d input I)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (S : Omega → Matrix (Fin (d 0)) (Fin (d 1)) ℝ)
    (G : Omega → Matrix (Fin (d 0)) (Fin (d 2)) ℝ)
    (hS : HasLaw S (gaussianMatrix (Fin (d 0)) (Fin (d 1))) P)
    (hG : HasLaw G (gaussianMatrix (Fin (d 0)) (Fin (d 2))) P)
    (hSG : IndepFun S G P) {rank : ℕ} {delta tolerance : ℝ} (hDelta : 0 < delta)
    (hSize : subgaussianEmbeddingDim 1 rank (1 / 2) (delta / 2) ≤ d 1)
    (hTolerance : 0 ≤ tolerance) :
    P.real {omega | ¬ (specification dataLength matrix work workspace w stream).Accepts
      (ExactLinear.resources work workspace) d input
        (exec algorithm.program I (ExactLinear.resources work workspace)
          (problem (𝕜 := ℝ) dataLength).formats (packedSampleTape stream (S omega) (G omega))
          d ((problem (𝕜 := ℝ) dataLength).initial d input))
        (fun c m => (specification dataLength matrix work workspace w stream).good
            d input (packedSampleTape stream (S omega) (G omega)) c m ∧
          StoresApproxTrace (matrix (d 0) (d 0) input.val.1) tolerance (1, 0) m)} ≤
      delta + 2 * Real.exp (-(hansonWrightConstant *
        min ((d 2 : ℝ) * tolerance ^ 2 / (subgaussianRangeFinderFactor 1 *
          frobNorm (matrix (d 0) (d 0) input.val.1 -
            truncatedSVD (matrix (d 0) (d 0) input.val.1) rank) ^ 2))
          ((d 2 : ℝ) * tolerance / (√(subgaussianRangeFinderFactor 1) *
            frobNorm (matrix (d 0) (d 0) input.val.1 -
              truncatedSVD (matrix (d 0) (d 0) input.val.1) rank))))) := by
  have : Nonempty (Fin (d 1)) := ⟨⟨0, hSketch⟩⟩
  have : IsProbabilityMeasure P := hS.isProbabilityMeasure
  let A := matrix (d 0) (d 0) input.val.1
  have hTail := measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix A
    hS hG hSG hDelta (by simpa using hSize) hTolerance
  have hReference : P.real {omega | ¬ |A.trace - hutchpp A (S omega) (G omega)| < tolerance} ≤
      delta + 2 * Real.exp (-(hansonWrightConstant *
        min ((d 2 : ℝ) * tolerance ^ 2 /
          (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A rank) ^ 2))
          ((d 2 : ℝ) * tolerance /
            (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A rank))))) := by
    simpa only [not_lt, Fintype.card_fin] using hTail
  refine algorithm.measureReal_failure_le hProbes input I hI
    (fun omega => packedSampleTape stream (S omega) (G omega)) _ _ ?_ P hReference
  intro omega count m hgood hreference
  refine ⟨hgood, hutchpp A (S omega) (G omega), ?_, hreference⟩
  simpa only [sampleMatrices_packedSampleTape] using hgood.2.2

/-- The fixed canonical Hutch++ program has the concrete Gaussian trace-error bound,
including every counted resource bound and exact word/cleanup guarantee on that same run.
The only additional resource premise is the declared common primitive workspace ceiling.
All Gaussian independence and numerical size hypotheses remain explicit.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]. -/
theorem Certification.measureReal_not_accepts_le_of_hasLaw_gaussianMatrix
    (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List ℝ → Matrix (Fin m) (Fin n) ℝ)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) (w stream : ℕ)
    (hWorkspace : ∀ o d, workspace o d ≤ w)
    {d : Fin 3 → ℕ} (hProbes : 0 < d 2) (hSketch : 0 < d 1)
    (input : (problem (𝕜 := ℝ) dataLength).Input d)
    (I : Interp ExactLinear.Operation CmpTst ℝ)
    (hI : (ExactLinear.model (problem (𝕜 := ℝ) dataLength)
      dataLength matrix work workspace).contracts d input I)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (S : Omega → Matrix (Fin (d 0)) (Fin (d 1)) ℝ)
    (G : Omega → Matrix (Fin (d 0)) (Fin (d 2)) ℝ)
    (hS : HasLaw S (gaussianMatrix (Fin (d 0)) (Fin (d 1))) P)
    (hG : HasLaw G (gaussianMatrix (Fin (d 0)) (Fin (d 2))) P)
    (hSG : IndepFun S G P) {rank : ℕ} {delta tolerance : ℝ} (hDelta : 0 < delta)
    (hSize : subgaussianEmbeddingDim 1 rank (1 / 2) (delta / 2) ≤ d 1)
    (hTolerance : 0 ≤ tolerance) :
    P.real {omega | ¬ (specification dataLength matrix work workspace w stream).Accepts
      (ExactLinear.resources work workspace) d input
        (exec (Certification.algorithm dataLength matrix work workspace w hWorkspace stream).program
          I (ExactLinear.resources work workspace)
          (problem (𝕜 := ℝ) dataLength).formats (packedSampleTape stream (S omega) (G omega))
          d ((problem (𝕜 := ℝ) dataLength).initial d input))
        (fun c m => (specification dataLength matrix work workspace w stream).good
            d input (packedSampleTape stream (S omega) (G omega)) c m ∧
          StoresApproxTrace (matrix (d 0) (d 0) input.val.1) tolerance (1, 0) m)} ≤
      delta + 2 * Real.exp (-(hansonWrightConstant *
        min ((d 2 : ℝ) * tolerance ^ 2 / (subgaussianRangeFinderFactor 1 *
          frobNorm (matrix (d 0) (d 0) input.val.1 -
            truncatedSVD (matrix (d 0) (d 0) input.val.1) rank) ^ 2))
          ((d 2 : ℝ) * tolerance / (√(subgaussianRangeFinderFactor 1) *
            frobNorm (matrix (d 0) (d 0) input.val.1 -
              truncatedSVD (matrix (d 0) (d 0) input.val.1) rank))))) := by
  exact HutchPlusPlus.measureReal_not_accepts_le_of_hasLaw_gaussianMatrix
    dataLength matrix work workspace w stream
    (Certification.algorithm dataLength matrix work workspace w hWorkspace stream)
    hProbes hSketch input I hI P S G hS hG hSG hDelta hSize hTolerance

end NLAlib.HutchPlusPlus
