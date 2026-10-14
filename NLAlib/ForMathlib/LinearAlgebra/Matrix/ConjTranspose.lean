/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Conjugate transposes of real diagonal matrices

A diagonal matrix over an `RCLike` field whose diagonal entries are real is its own conjugate
transpose. Upstream candidate for `Mathlib.Analysis.RCLike.Basic` or a file on Hermitian
matrices.

## Main results

* `Matrix.conjTranspose_diagonal_ofReal`: `(diagonal fun i => (d i : 𝕜))ᴴ` is itself.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n]

/-- A diagonal matrix with real entries, over an `RCLike` field, is its own conjugate
transpose. -/
theorem conjTranspose_diagonal_ofReal (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : 𝕜))ᴴ = diagonal fun i => ((d i : ℝ) : 𝕜) := by
  rw [diagonal_conjTranspose]
  exact congrArg diagonal (funext fun i => RCLike.conj_ofReal (d i))

end Matrix
