/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.ComponentwiseBackward

/-!
# Approximate eigenvectors of a triangular matrix

The eigenvectors of an upper triangular $\mathbf{T}$ are computed by back substitution in the
shifted systems $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}_j = \mathbf{0}$ with
$(\mathbf{y}_j)_j = 1$ (LAPACK `xTREVC`). A computed basis whose columns are componentwise backward
solutions of these systems and have norm near $1$ has a small column residual, with no hypothesis
on the gaps of the diagonal and none on the structure of $\mathbf{T}$.

## Main definitions

* `NLAlib.IsTriangularEigenbasisApprox`: an approximate eigenbasis by back substitution.

## Main results

* `NLAlib.IsTriangularEigenbasisApprox.norm_mulVec_col_le`: the gap-free column residual.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **An approximate eigenbasis of `T` by back substitution**: each column $\mathbf{y}_j$ of `Y`
has norm within $\eta$ of $1$ and is a componentwise backward solution of
$(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with $(\varepsilon, \sigma)$
(`NLAlib.IsComponentwiseBackwardSolution`). -/
def IsTriangularEigenbasisApprox (ε σ η : ℝ) (T Y : Matrix n n 𝕜) : Prop :=
  ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ η ∧
    IsComponentwiseBackwardSolution ε σ (T - T j j • 1) 0 (Y.col j)

/-- **The column residual of an approximate triangular eigenbasis** is gap-free: for
$\varepsilon, \sigma \ge 0$ and every column, $\|(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}_j\| \le
(\varepsilon(1 + \sqrt N)\|\mathbf{T}\|_{\mathsf F} + \sigma)\|\mathbf{y}_j\|$, $N$ the order. -/
theorem IsTriangularEigenbasisApprox.norm_mulVec_col_le {ε σ η : ℝ} {T Y : Matrix n n 𝕜}
    (h : IsTriangularEigenbasisApprox ε σ η T Y) (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (j : n) :
    ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤
      (ε * (1 + √(Fintype.card n : ℝ)) * frobNorm T + σ) * ‖WithLp.toLp 2 (Y.col j)‖ := by
  sorry

end NLAlib
