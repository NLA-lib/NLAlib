/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Krylov.Basic.BlockSpace

/-!
# Measurability of Krylov quantities

For a random starting block, the block Krylov matrix is a measurable function of the block: it is
linear in it; so is the Krylov matrix of a random starting vector. With `NLAlib.measurable_rsvd`
this makes randomized block Krylov iteration, the randomized SVD at the test matrix
$\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$, a measurable function of
$\mathbf{\Omega}$. Matrices carry the product σ-algebra `Matrix.instMeasurableSpace`.

## Main results

* `NLAlib.measurable_blockKrylovMatrix`: $\mathbf{B} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{B})$
  is measurable.
* `NLAlib.measurable_krylovMatrix`: $\mathbf{b} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{b})$
  is measurable.
* `NLAlib.measurable_fromCols_blockKrylovMatrix`: two block Krylov matrices side by side are a
  measurable function of the pair of starting blocks.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [DecidableEq n]


/-- The block Krylov matrix $\mathbf{B} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{B})$ is a
measurable function of the starting block. -/
theorem measurable_blockKrylovMatrix (A : Matrix n n 𝕜) (q : ℕ) :
    Measurable fun B : Matrix n p 𝕜 => blockKrylovMatrix A B q := by
  refine Matrix.measurable_iff.2 fun i jc => ?_
  change Measurable fun B : Matrix n p 𝕜 => (A ^ (jc.1 : ℕ) * B) i jc.2
  exact (Matrix.measurable_apply i jc.2).comp (measurable_const.matrix_mul measurable_id)

/-- Two block Krylov matrices side by side,
$(\mathbf{B}_1, \mathbf{B}_2) \mapsto \begin{bmatrix} \mathbf{K}_{q_1}(\mathbf{A}, \mathbf{B}_1) &
\mathbf{K}_{q_2}(\mathbf{A}, \mathbf{B}_2)\end{bmatrix}$, are a measurable function of the pair
of starting blocks. With `NLAlib.measurable_rsvd` this is the measurability that the randomized
SVD at a test matrix built from two random blocks needs. -/
theorem measurable_fromCols_blockKrylovMatrix {p' : Type*} (A : Matrix n n 𝕜) (q₁ q₂ : ℕ) :
    Measurable fun B : Matrix n p 𝕜 × Matrix n p' 𝕜 =>
      Matrix.fromCols (blockKrylovMatrix A B.1 q₁) (blockKrylovMatrix A B.2 q₂) := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  rcases j with j | j
  · exact (Matrix.measurable_apply i j).comp
      ((measurable_blockKrylovMatrix A q₁).comp measurable_fst)
  · exact (Matrix.measurable_apply i j).comp
      ((measurable_blockKrylovMatrix A q₂).comp measurable_snd)

/-- The Krylov matrix $\mathbf{b} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{b})$ is a measurable
function of the starting vector: it is linear in it. -/
theorem measurable_krylovMatrix (A : Matrix n n 𝕜) (q : ℕ) :
    Measurable fun b : n → 𝕜 => krylovMatrix A b q := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  change Measurable fun b : n → 𝕜 => (A ^ (j : ℕ) *ᵥ b) i
  exact (measurable_pi_apply i).comp (measurable_const.matrix_mulVec measurable_id)

end NLAlib
