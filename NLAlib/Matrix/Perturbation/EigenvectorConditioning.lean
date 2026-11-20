/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.EigenvalueBackward

/-!
# Conditioning of approximate eigenvectors

Let $\mathbf{M}$ be diagonalizable by $\mathbf{W}$ with $\kappa(\mathbf{W}) \le B$ and eigenvalues
at mutual distance at least $\Gamma > 0$ (`NLAlib.IsConditionedDiagonalizable`). If the columns of
$\mathbf{V}$ have norms in $[m, m']$, column residuals
$\|(\mathbf{M} - \mathrm{ev}_j\mathbf{I})\mathbf{v}_j\| \le \eta\|\mathbf{v}_j\|$ with
$8\sqrt N B\eta \le \Gamma$, and the values $\mathrm{ev}_j$ are $\Gamma/2$-separated, then
$\mathbf{V}$ is invertible with $\kappa(\mathbf{V}) \le \tfrac75\sqrt N B\, m'/m$. Each
$\mathrm{ev}_j$ is matched to its own eigenvalue by Bauer–Fike; in the eigenbasis each column is
one entry plus a small rest, and a Neumann series inverts the matrix of the rests. No hypothesis on
a gap of a triangular form is needed: a gap of $\mathbf{T}$ alone does not bound the conditioning.

## Main results

* `NLAlib.IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual`: the condition number
  of approximate eigenvectors of a matrix of the class.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Approximate eigenvectors of a matrix of the class $(B, \Gamma)$ are well conditioned**: let
$\mathbf{M}$ be of the class $(B, \Gamma)$ with $\Gamma > 0$, $\eta \ge 0$,
$8\sqrt N B\eta \le \Gamma$ ($N$ the order), and let the columns of $\mathbf{V}$ have norms in
$[m, m']$ with $m > 0$ and residuals
$\|(\mathbf{M} - \mathrm{ev}_j\mathbf{I})\mathbf{v}_j\| \le \eta\|\mathbf{v}_j\|$, the
$\mathrm{ev}_j$ at mutual distance at least $\Gamma/2$. Then $\mathbf{V}$ is invertible,
$m\|\mathbf{V}^{-1}\|_2 \le \tfrac75 B$ and $\kappa(\mathbf{V}) \le \tfrac75\sqrt N B\,m'/m$.
No printed source. -/
theorem IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual
    {B Γ η m m' : ℝ} {M V : Matrix n n ℂ} {ev : n → ℂ}
    (hM : IsConditionedDiagonalizable B Γ M) (hΓ : 0 < Γ) (hη : 0 ≤ η)
    (hsmall : 8 * √(Fintype.card n : ℝ) * B * η ≤ Γ) (hm : 0 < m)
    (hcol : ∀ j, m ≤ ‖WithLp.toLp 2 (V.col j)‖ ∧ ‖WithLp.toLp 2 (V.col j)‖ ≤ m')
    (hres : ∀ j, ‖WithLp.toLp 2 ((M - ev j • 1) *ᵥ V.col j)‖ ≤ η * ‖WithLp.toLp 2 (V.col j)‖)
    (hsep : ∀ i j, i ≠ j → Γ / 2 ≤ ‖ev i - ev j‖) :
    IsUnit V ∧ m * specNorm V⁻¹ ≤ 7 / 5 * B ∧
      pseudoConditionNumber V ≤ 7 / 5 * √(Fintype.card n : ℝ) * B * (m' / m) := by
  sorry

end NLAlib
