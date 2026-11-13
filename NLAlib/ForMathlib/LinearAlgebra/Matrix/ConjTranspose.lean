/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Conjugate transposes: real diagonal matrices and cross-Gram matrices

A diagonal matrix over an `RCLike` field whose diagonal entries are real is its own conjugate
transpose; upstream candidate for `Mathlib.Analysis.RCLike.Basic` or a file on Hermitian
matrices. The cross-Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{B}$ is the sum of the rank-one
products of the rows; upstream candidate for `Mathlib.LinearAlgebra.Matrix.ConjTranspose`, beside
`Matrix.conjTranspose_vecMulVec`. A congruence by a scaled product of Hermitian matrices is
written out, and so is the residual of a congruent linear system; upstream candidates for the
same file.

## Main results

* `Matrix.conjTranspose_diagonal_ofReal`:
  $\operatorname{diag}(\mathbf{d})^{\mathsf{H}} = \operatorname{diag}(\mathbf{d})$ for real
  $\mathbf{d}$.
* `Matrix.conjTranspose_mul_eq_sum_vecMulVec`:
  $\mathbf{A}^{\mathsf{H}}\mathbf{B} = \sum_i \mathbf{a}_i^{\mathsf{H}} \mathbf{b}_i$ over the rows
  $\mathbf{a}_i$, $\mathbf{b}_i$.
* `Matrix.conjTranspose_smul_mul_mul_smul`: a congruence by
  $\sqrt{c}\,\mathbf{S}\mathbf{R}$ for Hermitian $\mathbf{S}$, $\mathbf{R}$.
* `Matrix.conjTranspose_mulVec_sub_mulVec_mulVec`: the residual of the congruent system,
  $\mathbf{C}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{C}\mathbf{y})
  = \mathbf{C}^{\mathsf{H}}\mathbf{b} - \mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}\mathbf{y}$.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

section Diagonal

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n]

/-- A diagonal matrix with real entries, over an `RCLike` field, is its own conjugate
transpose: $\operatorname{diag}(\mathbf{d})^{\mathsf{H}} = \operatorname{diag}(\mathbf{d})$ for
$\mathbf{d}$ real. -/
theorem conjTranspose_diagonal_ofReal (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : 𝕜))ᴴ = diagonal fun i => ((d i : ℝ) : 𝕜) := by
  rw [diagonal_conjTranspose]
  exact congrArg diagonal (funext fun i => RCLike.conj_ofReal (d i))

end Diagonal

section Gram

variable {α : Type*} [Mul α] [AddCommMonoid α] [Star α] {n q r : Type*} [Fintype n]

/-- The cross-Gram matrix is the sum of the rank-one products of the rows:
$\mathbf{A}^{\mathsf{H}}\mathbf{B} = \sum_i \mathbf{a}_i^{\mathsf{H}} \mathbf{b}_i$, where
$\mathbf{a}_i$, $\mathbf{b}_i$ are row $i$ of $\mathbf{A}$ and $\mathbf{B}$ and the summand is
`vecMulVec (star (A i)) (B i)`. At $\mathbf{A} = \mathbf{B}$ it writes a Gram matrix as a sum of
positive semidefinite rank-one matrices, the form row-sampling arguments use. -/
theorem conjTranspose_mul_eq_sum_vecMulVec (A : Matrix n q α) (B : Matrix n r α) :
    Aᴴ * B = ∑ i, vecMulVec (star (A i)) (B i) := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, sum_apply, vecMulVec_apply, Pi.star_apply]

end Gram

/-- Conjugating a diagonal matrix by a rectangular matrix expands into the rank-one
outer products of its columns, weighted by the diagonal entries. [HornJohnson2013, §2.5]. -/
theorem mul_diagonal_mul_conjTranspose_eq_sum_vecMulVec {R m n : Type*} [CommSemiring R]
    [Star R] [Fintype m] [DecidableEq m] (U : Matrix n m R) (d : m → R) :
    U * Matrix.diagonal d * Uᴴ = ∑ i, d i • Matrix.vecMulVec (U.col i) (star (U.col i)) := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.col_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ac_rfl


section Congruence

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- A congruence by a scaled product of Hermitian factors: for $\mathbf{S}^{\mathsf{H}} =
\mathbf{S}$, $\mathbf{R}^{\mathsf{H}} = \mathbf{R}$ and $c \ge 0$,
$$(\sqrt{c}\,\mathbf{S}\mathbf{R})^{\mathsf{H}} \mathbf{N} (\sqrt{c}\,\mathbf{S}\mathbf{R})
= c\, \mathbf{R}\mathbf{S}\mathbf{N}\mathbf{S}\mathbf{R}\,.$$
The step of the operator Jensen inequality for the two-term families
$\mathbf{K}_i = \sqrt{a_i}\,\mathbf{S}_i\mathbf{R}$. -/
theorem conjTranspose_smul_mul_mul_smul {c : ℝ} (hc : 0 ≤ c) {S R : Matrix n n 𝕜}
    (hS : Sᴴ = S) (hR : Rᴴ = R) (N : Matrix n n 𝕜) :
    (√c • (S * R))ᴴ * N * (√c • (S * R)) = c • (R * (S * N * S) * R) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hR, hS, star_trivial]
  simp only [Matrix.smul_mul, Matrix.mul_smul, _root_.smul_smul, Real.mul_self_sqrt hc,
    Matrix.mul_assoc]

/-- The split residual: the residual of $\mathbf{C}\mathbf{y}$ for
$\mathbf{A}\mathbf{x} = \mathbf{b}$, multiplied by $\mathbf{C}^{\mathsf{H}}$, is the residual of
$\mathbf{y}$ for the congruent system
$(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C})\mathbf{y} = \mathbf{C}^{\mathsf{H}}\mathbf{b}$:
$$\mathbf{C}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{C}\mathbf{y})
= \mathbf{C}^{\mathsf{H}}\mathbf{b} - \mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}\mathbf{y}\,.$$
The step that turns split preconditioning (PCG, preconditioned MINRES) into the unpreconditioned
method on $\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$. -/
theorem conjTranspose_mulVec_sub_mulVec_mulVec (A C : Matrix n n 𝕜) (b y : n → 𝕜) :
    Cᴴ *ᵥ (b - A *ᵥ (C *ᵥ y)) = Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y := by
  rw [Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end Congruence

end Matrix
