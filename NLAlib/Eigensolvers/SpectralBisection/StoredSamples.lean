/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Samples
public import NLAlib.Matrix.FinitePrecision.OpsSampling

/-!
# Actual stored words and ideal bisection samples

The ideal coordinate embedding preserves the raw sample law. These equalities identify the
machine's concrete sampler functions with the program's actual stored tape words, provided
those words are the declared position-independent roundings of the ideal real streams.
The Gaussian normalization is explicit: the ideal complex sample divides by the exact square
root of two, while the program uses the rounded square root of its rounded one half.

## Main results

* `NLAlib.SpectralBisection.uniformSample_idealTape`: the actual stored uniform multiplication.
* `NLAlib.SpectralBisection.normalSample_eighIdealComplex`: the actual two stored Gaussian words
  scaled by the normalization word computed by the scalar machine.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The ideal uniform sampler is exactly multiplication of the actual stored sample word.
The rounding is fixed across positions, and the slot lies in the level's uniform batch. -/
theorem uniformSample_idealTape {K : Type} (M : Machine K) (roundUnif : ℝ → K)
    (ideal : Tape ℝ) (stored : Tape K)
    (hround : ∀ p, stored p Stream.unif = roundUnif (ideal p Stream.unif))
    (base n d lo : ℕ) (hlo : lo < n) (scale : K) :
    M.uniformSample roundUnif scale (idealTape n (ideal.shift base) .uniform (n * d + lo)) =
      M.mul scale (stored (base + (d * levelSampleSize n + lo)) Stream.unif) := by
  simp only [Machine.uniformSample, idealTape, idealCoordinate, uniformPosition_mul_add n d lo hlo]
  simp only [Tape.shift_apply]
  rw [hround]

/-- The ideal complex Gaussian sampler is exactly the two actual scalar products performed
on stored Gaussian words at the node's component addresses. The square-root word belongs to the
same scalar machine. No arbitrary normal sampler is assumed to implement these operations. -/
theorem normalSample_eighIdealComplex {K : Type} (M : Machine K) (roundGaussian : ℝ → K)
    (ideal : Tape ℝ) (stored : Tape K)
    (hround : ∀ p, stored p Stream.gauss = roundGaussian (ideal p Stream.gauss))
    (base n d lo j side i : ℕ) (hcol : lo + j < n) (hside : side < 2) (hrow : i < n) :
    M.normalSample roundGaussian (eighIdealComplex (idealTape n (ideal.shift base))
      (2 * (n * n) * d + n * (2 * (lo + j) + side) + i)) =
      M.normalWords
        (stored (base + (d * levelSampleSize n + n + gaussianWord n lo j side i 0))
          Stream.gauss)
        (stored (base + (d * levelSampleSize n + n + gaussianWord n lo j side i 1))
          Stream.gauss) := by
  rw [eighIdealComplex, Machine.normalSample_div_sqrt_two]
  simp only [idealTape, idealCoordinate]
  have hzero := gaussianPosition_gaussianWord n d lo j side i 0 hcol hside hrow (by omega)
  have hone := gaussianPosition_gaussianWord n d lo j side i 1 hcol hside hrow (by omega)
  simp only [Nat.add_zero] at hzero
  rw [hzero, hone]
  simp only [Tape.shift_apply]
  rw [hround, hround]

end NLAlib.SpectralBisection
