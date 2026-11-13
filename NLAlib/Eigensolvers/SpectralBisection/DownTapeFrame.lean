/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownFrame
public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine

/-!
# Indexed-tape outcome footprints

The exact coupling of stored sample words with the indexed mathematical tape also identifies
the output locations. Mathematical outcomes therefore obey the same checked arena bounds.

## Main results

* `NLAlib.SpectralBisection.stepFp_tapeMachine_le_downLevel`: indexed outcomes fit their level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Every actual indexed-tape outcome of a positive bounded node lies in its output level. -/
theorem stepFp_tapeMachine_le_downLevel {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base : ℕ) (τ : Tape K) (d lo fuel : ℕ) (R0 beta R eps : K) (ell : ℕ) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (K × K)) (hslot : lo + k ≤ n) (hpos : 0 < k)
    (ma ua qa ea sz kd kp : ℕ × ℕ) :
    let outcome := eighStep (tapeMachine M dec mm qr n base τ) n fuel R0 beta A R eps ell
      (eighTapeSample n d lo)
    Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp outcome) (stepOutputLengths outcome) ≤
      downLevelRegion n d ma ua qa ea sz kd kp := by
  dsimp only
  rw [eighStep_tapeMachine M dec mm qr n base τ d lo fuel R0 beta R eps ell A hslot]
  exact (stepFp_le_downRegion M dec mm qr (d := d) (fuel := fuel) (ell := ell) hslot hpos
    R0 beta R eps (vec (levelUniformWords n base τ d) lo) (levelGaussianMatrix n base τ d) A
    ma ua qa ea sz kd kp).trans (downRegion_le_level hslot ma ua qa ea sz kd kp)

end NLAlib.SpectralBisection
