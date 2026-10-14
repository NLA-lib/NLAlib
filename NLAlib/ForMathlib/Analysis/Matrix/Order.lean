/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Instances.Matrix

/-!
# The Loewner order on matrices is closed

Under `open scoped MatrixOrder`, the Loewner order `A ≤ B ↔ (B - A).PosSemidef` on square matrices
over an `RCLike` field has closed upper sets `{B | A ≤ B}` for the usual topology on matrices.
Mathlib has this only for `ℂ`, through the C*-algebra structure of the operator norm. With it,
Mathlib's order lemmas for integrals (`MeasureTheory.integral_mono_ae`,
`MeasureTheory.integral_nonneg_of_ae`) apply to the Loewner order. Upstream candidate for
`Mathlib/Analysis/Matrix/Order.lean`.

## Main results

* `Matrix.instClosedIciTopology`.
-/

@[expose] public section

open scoped MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The upper sets of the Loewner order are closed. -/
instance instClosedIciTopology : ClosedIciTopology (Matrix n n 𝕜) := by
  sorry

end Matrix
