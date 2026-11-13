/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.StoredSamples

/-!
# Rounded word tapes for spectral bisection

The external word tape is a streamwise rounding of an ideal real tape. Its stream laws are
exact pushforwards, with joint independence preserved. The program accesses these words through
its counted sampling primitives; this construction describes their mathematical law.

## Main results

* `NLAlib.SpectralBisection.roundTape_unif`, `roundTape_gauss`: actual component coupling.
* `NLAlib.SpectralBisection.isTapeLaw_roundTape`: the joint law of rounded word streams.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops MeasureTheory

/-- Round uniform words with the uniform rounding map and all other streams with the Gaussian
rounding map. Spectral bisection uses only the uniform and Gaussian stream labels. -/
def roundTape {K : Type} (roundUnif roundGaussian : ℝ → K) (ideal : Tape ℝ) : Tape K :=
  ideal.mapStreams fun s => if s = Stream.unif then roundUnif else roundGaussian

/-- Uniform tape words are exactly their declared rounded ideal words at every position. -/
@[simp] theorem roundTape_unif {K : Type} (roundUnif roundGaussian : ℝ → K)
    (ideal : Tape ℝ) (p : ℕ) :
    roundTape roundUnif roundGaussian ideal p Stream.unif = roundUnif (ideal p Stream.unif) := by
  simp [roundTape, Tape.mapStreams]

/-- Gaussian component words are exactly their declared rounded ideal words at every position. -/
@[simp] theorem roundTape_gauss {K : Type} (roundUnif roundGaussian : ℝ → K)
    (ideal : Tape ℝ) (p : ℕ) :
    roundTape roundUnif roundGaussian ideal p Stream.gauss =
      roundGaussian (ideal p Stream.gauss) := by
  simp [roundTape, Tape.mapStreams, Stream.gauss, Stream.unif]

/-- Measurable rounding gives the joint independent word-stream law. Each stream distribution
is the pushforward of its ideal real distribution through that stream's fixed rounding map. -/
theorem isTapeLaw_roundTape {K Ω : Type} [MeasurableSpace K] [MeasurableSpace Ω]
    {law : ℕ → Measure ℝ} {P : Measure Ω} {ideal : Ω → Tape ℝ}
    (h : IsTapeLaw law P ideal) {roundUnif roundGaussian : ℝ → K}
    (hU : Measurable roundUnif) (hG : Measurable roundGaussian) :
    IsTapeLaw (fun s => (law s).map (if s = Stream.unif then roundUnif else roundGaussian))
      P (fun ω => roundTape roundUnif roundGaussian (ideal ω)) := by
  exact h.map_streams _ fun s => by
    by_cases hs : s = Stream.unif
    · simpa only [hs, ite_true] using hU
    · simpa only [hs, ite_false] using hG

end NLAlib.SpectralBisection
