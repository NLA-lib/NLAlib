/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.BlockKrylov

/-!
# Block Krylov iteration cannot resolve multiplicities above the block size

Randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$ with a block
$\mathbf{\Omega}$ of $b$ columns sees each eigenspace of
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ only through the $b$ projected columns of
$\mathbf{\Omega}$: the projection of $\mathbf{H}^j\mathbf{\Omega}$ onto the eigenspace of
$\lambda$ is $\lambda^j$ times that of $\mathbf{\Omega}$. So if a singular value $\sigma$ of
$\mathbf{A}$ has multiplicity $b + k + 1$, a subspace of dimension $k + 1$ of its right singular
vectors is orthogonal to the block Krylov space for every depth $q$ and every block, and
$\sigma_k(\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)) \ge \sigma$. In particular a
singular value $\sigma_i > \sigma_r$ of multiplicity above $b$ keeps the spectral error at
$\sigma_i$, above the optimum $\sigma_r$ of rank $r$, at every depth: for a block size below the
target rank some gap hypothesis among the leading singular values is necessary. The bound says
nothing about suboptimality when $\sigma_i = \sigma_r$ (for $\mathbf{A} = \mathbf{I}$ the error
of every method of rank below $\lvert n \rvert$ is $1$).

## Main results

* `NLAlib.singularValues_le_singularValues_sub_rbki_of_singularValues_eq`: every singular value.
* `NLAlib.singularValues_le_specNorm_sub_rbki_of_singularValues_eq`: the spectral norm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq n]

/-- Necessity of a gap for block Krylov iteration, every singular value: for a matrix
$\mathbf{A}$ over $\Bbbk$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, any block
$\mathbf{\Omega}$ with $b$ columns, and indices $i$, $k$ with $\sigma_i = \sigma_{i+b+k}$, for
every depth $q$,
$$\sigma_i(\mathbf{A}) \le
\sigma_k\bigl(\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)\,.$$
The block is arbitrary (no law, no rank condition) and $\sigma_i = 0$ is allowed, where the bound
is trivial. The eigenspace of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ for $\sigma_i^2 > 0$ has
dimension at least $b + k + 1$ and meets the orthogonal complement of the block Krylov space in
dimension at least $k + 1$; there $\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$
acts as $\mathbf{A}$, which scales norms by $\sigma_i$. -/
theorem singularValues_le_singularValues_sub_rbki_of_singularValues_eq (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (q : ℕ) {i k : ℕ}
    (h : singularValues A i = singularValues A (i + Fintype.card l + k)) :
    singularValues A i ≤ singularValues (A - rbki A Ω q) k := by
  -- If `singularValues A i = 0` use `singularValues_nonneg`. Otherwise all of
  -- `singularValues A j`, `i ≤ j ≤ i + card l + k`, equal `σ := singularValues A i`
  -- (`singularValues_antitone`), so the eigenspace `E` of `Aᴴ * A` for `σ ^ 2` has finrank at
  -- least `card l + k + 1` (right singular vectors of an SVD of `A`). For `w ∈ E` and a column
  -- `(Aᴴ * A) ^ j * Ω` of `blockKrylovMatrix (Aᴴ * A) Ω q`, the inner product with `w` is
  -- `σ ^ (2 * j)` times that of the column of `Ω` (`Aᴴ * A` is Hermitian). So
  -- `S := E ⊓ (range Ω.mulVecLin)ᗮ` has finrank at least `k + 1` (rank–nullity,
  -- `rank Ω ≤ card l`) and is orthogonal to the block Krylov space; for `w ∈ S`, `A *ᵥ w` is
  -- orthogonal to the range of `A * blockKrylovMatrix (Aᴴ * A) Ω q` (inner product
  -- `σ ^ 2 * ⟪w, K y⟫ = 0`), so `(A - rbki A Ω q) *ᵥ w = A *ᵥ w` (`rbki_eq_rangeProjector`) with
  -- norm `σ * ‖w‖`. Conclude by `le_singularValues_of_forall_mem`.
  sorry

/-- Necessity of a gap for block Krylov iteration, spectral norm: for a matrix $\mathbf{A}$ over
$\Bbbk$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, any block $\mathbf{\Omega}$ with
$b$ columns, and an index $i$ with $\sigma_i = \sigma_{i+b}$ (the singular value $\sigma_i$ has
multiplicity above the block size), for every depth $q$,
$$\sigma_i(\mathbf{A}) \le \|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\|_2\,.$$
When $\sigma_i > \sigma_r$ the error stays above the optimal rank-$r$ error $\sigma_r$ at every
depth. -/
theorem singularValues_le_specNorm_sub_rbki_of_singularValues_eq (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (q : ℕ) {i : ℕ}
    (h : singularValues A i = singularValues A (i + Fintype.card l)) :
    singularValues A i ≤ specNorm (A - rbki A Ω q) := by
  rw [← singularValues_zero_eq_specNorm]
  exact singularValues_le_singularValues_sub_rbki_of_singularValues_eq A Ω q (k := 0) h

end NLAlib
