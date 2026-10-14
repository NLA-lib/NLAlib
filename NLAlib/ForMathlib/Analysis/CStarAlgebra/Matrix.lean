/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The real normed space of matrices under the operator norm

Under `open scoped Matrix.Norms.L2Operator`, Mathlib makes `Matrix m n 𝕜` a normed space over `𝕜`
but not over `ℝ`, which the Bochner integral and conditional expectation need; over `ℂ` the real
structure comes from `NormedSpace.complexToReal`, over a general `RCLike` field from nothing. This
file adds it, on the existing `Module ℝ` structure of matrices (no new data); at `𝕜 = ℂ` it agrees
with `NormedSpace.complexToReal` up to reducible defeq. Upstream candidate for
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`.

## Main definitions

* `Matrix.instL2OpNormedSpaceReal`, scoped to `Matrix.Norms.L2Operator`.
-/

@[expose] public section

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Matrices with the operator norm form a real normed space. Not a global instance: it is
scoped with the norm, `open scoped Matrix.Norms.L2Operator`. -/
@[instance_reducible]
noncomputable def instL2OpNormedSpaceReal : NormedSpace ℝ (Matrix m n 𝕜) where
  norm_smul_le r A := by
    rw [← algebraMap_smul 𝕜 r A, norm_smul, norm_algebraMap']

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedSpaceReal

end Matrix
