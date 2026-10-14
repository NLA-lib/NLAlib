/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Compactness of the unitary group

The unitary group `Matrix.unitaryGroup n 𝕜` (over `ℝ`, the orthogonal group
`Matrix.orthogonalGroup n ℝ`) is a compact space: it is closed, and its entries are bounded by
`1`. With it, Mathlib's `MeasureTheory.Measure.haarMeasure` on the group is a finite measure.
Upstream candidate for `Mathlib.LinearAlgebra.UnitaryGroup` (or the topology file that would
import it).

## Main results

* `Matrix.compactSpace_unitaryGroup`.
-/

@[expose] public section

namespace Matrix

/-- The unitary group `Matrix.unitaryGroup n 𝕜` (over `ℝ`, the orthogonal group) is compact, in
every dimension including `0`. Port of the prototype's `orthogonalGroupCompactSpace`, there for
`Fin n` over `ℝ`. -/
instance compactSpace_unitaryGroup {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    CompactSpace (Matrix.unitaryGroup n 𝕜) := by
  have hb : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1 : Set (Matrix n n 𝕜)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc : IsClosed (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := isClosed_unitary
  refine isCompact_iff_compactSpace.mp (hb.of_isClosed_subset hc fun U hU => ?_)
  simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_norm_bound_of_unitary hU i j

end Matrix
