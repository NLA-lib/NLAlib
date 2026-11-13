/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic

/-!
# Mathematical tape sample layouts

## Main results

* Tape sample definitions use ordinary matrices and real sequences.
-/

@[expose] public section

namespace NLAlib.Computation

/-- The distributions a program draws from; each has its own tape. -/
inductive Dist where
  /-- Standard Gaussian. -/
  | gaussian
  /-- Rademacher (random signs). -/
  | rademacher
  /-- Uniform on $[-1, 1]$. -/
  | uniform
  deriving DecidableEq

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The $N \times k$ matrix drawn from the tape `x` from position `off`, column-major: entry
$(i, j)$ is the tape value at $\mathit{off} + i + Nj$. -/
def tapeMatrix (x : ℕ → ℝ) (off N k : ℕ) : Matrix (Fin N) (Fin k) 𝕜 :=
  Matrix.of fun i j => (x (off + i + N * j) : 𝕜)

/-- **The ideal complex Gaussian matrix of a tape** of real draws $x$: entry $(i, j)$ of the
$N \times N$ matrix is $(x_{2(i + Nj)} + i\,x_{2(i + Nj) + 1})/\sqrt2$, column-major. -/
noncomputable def tapeComplexMatrix (x : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ⟨x (2 * (i + N * j)) / √2, x (2 * (i + N * j) + 1) / √2⟩

/-- **The sample positions** of an $N \times N$ matrix drawn column-major: entry $(i, j)$ is
sample $i + Nj$ (its two real draws at tape positions $2(i + Nj)$ and $2(i + Nj) + 1$). -/
def tapeIndexMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℕ :=
  Matrix.of fun i j => i + N * j


end NLAlib.Computation
