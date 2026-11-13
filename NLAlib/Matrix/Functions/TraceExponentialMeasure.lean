/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Complexification
public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Spectral.SimpleSpectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import NLAlib.Matrix.Functions.TraceExponentialApproximation
public import NLAlib.Matrix.Functions.TraceExponentialDensity

/-!
# Positive measure representation of the trace exponential

For arbitrary Hermitian data, the trace exponential of the affine pencil is the Laplace
transform of a finite positive measure on the spectral interval of the direction. No commutation
or simple-spectrum assumption is imposed.

## Main results

* `NLAlib.exists_isCompactExpRepresentation_re_trace_exp`.
-/
@[expose] public section

section
open Complex MeasureTheory

open scoped Matrix

namespace NLAlib

private theorem complex_trace_representation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (A + t • H)).trace.re)
          (sInf (spectrum ℝ H)) (sSup (spectrum ℝ H)) := by
  apply exists_isCompactExpRepresentation_re_trace_exp_of_diagonal_simple A H hA hH
  intro C hC b hb l u hlu hbu
  have heq (t : ℝ) : C + t • Matrix.diagonal (fun i => (b i : ℂ)) =
      C + (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)) := by
    congr 1
  simpa only [heq] using
    hC.exists_isCompactExpRepresentation_re_trace_exp_of_injective b hb hlu hbu

/-- **Stahl's trace-exponential representation.** For real or complex Hermitian matrices
$\mathbf{A},\mathbf{H}$, the real trace of $\exp(\mathbf{A}+t\mathbf{H})$ is the Laplace transform
of a finite positive measure supported between the spectral extremes of $\mathbf{H}$,
for every real $t$. This includes repeated eigenvalues and the empty matrix. The mass,
tilted moments and even-derivative bounds follow from the scalar measure API.
[Stahl2013, Theorems 1 and 2].
Result: trace-exponential-stahl -/
theorem exists_isCompactExpRepresentation_re_trace_exp
    {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (A H : Matrix n n 𝕜) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => RCLike.re (NormedSpace.exp (A + t • H)).trace)
      (sInf (spectrum ℝ H)) (sSup (spectrum ℝ H)) := by
  have hHC := isHermitian_complexify_iff.mpr hH
  have hs : spectrum ℝ (complexify H) = spectrum ℝ H := by
    rw [hHC.spectrum_eq_image_eigenvalue, hH.spectrum_eq_image_eigenvalue]
    simp only [eigenvalue_complexify]
  obtain ⟨ν, hν⟩ := complex_trace_representation (complexify A) (complexify H)
    (isHermitian_complexify_iff.mpr hA) hHC
  refine ⟨ν, ?_⟩
  simpa only [hs, ← complexify_real_smul, ← complexify_add, ← complexify_exp,
    re_trace_complexify] using hν

end NLAlib
end
