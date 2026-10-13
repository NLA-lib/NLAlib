/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Norms.Spectral

/-!
# Orthonormal frames of a subspace

Matrices with orthonormal columns as bases of subspaces: two frames of the same subspace differ
by a unitary factor, two matrices with the same Gram matrix differ by an isometry, a unitary
matrix is determined by its first block of columns up to a unitary factor on the complement, and
the set of frames is compact.

## Main results

* `NLAlib.HasOrthonormalCols.conjTranspose_mul_of_range_le`,
  `NLAlib.HasOrthonormalCols.mul_conjTranspose_mul_of_range_le`: change of frame.
* `NLAlib.conjTranspose_mul_self_eq_iff_exists_mul`: equal Gram matrices.
* `NLAlib.isCompact_setOf_hasOrthonormalCols`: compactness of the set of frames.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq p] [DecidableEq q]

/-! ### Change of frame -/

/-- If the column space of `V` lies in that of the frame `U`, then `V = U * (Uᴴ * V)`. -/
theorem HasOrthonormalCols.mul_conjTranspose_mul_of_range_le {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {V : Matrix n q 𝕜}
    (h : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) : U * (Uᴴ * V) = V := by
  sorry

/-- If the column space of the frame `V` lies in that of the frame `U`, the transition matrix
`Uᴴ * V` has orthonormal columns. -/
theorem HasOrthonormalCols.conjTranspose_mul_of_range_le {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {V : Matrix n q 𝕜} (hV : HasOrthonormalCols V)
    (h : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasOrthonormalCols (Uᴴ * V) := by
  sorry

/-- **Two frames of the same subspace differ by a unitary factor.**
[HornJohnson2013, Theorem 2.1.4 context].
Port of `NLAlib.exists_orthogonal_frame_transition`, there over `ℝ`. -/
theorem HasOrthonormalCols.exists_mul_eq_of_range_eq {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (h : LinearMap.range U.mulVecLin = LinearMap.range V.mulVecLin) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧ U * T = V := by
  sorry

/-- There are orthonormal frames with `card p` columns in a space of dimension at least
`card p`. Port of `NLAlib.exists_hasOrthonormalCols_of_card_le`. -/
theorem exists_hasOrthonormalCols_of_card_le (𝕜 : Type*) [RCLike 𝕜]
    (h : Fintype.card p ≤ Fintype.card n) : ∃ J : Matrix n p 𝕜, HasOrthonormalCols J := by
  sorry

/-! ### Equal Gram matrices -/

/-- Matrices with the same Gram matrix have the same action on norms.
Port of `NLAlib.norm_toEuclideanLin_apply_eq_of_gram_eq`. -/
theorem norm_mulVec_eq_of_conjTranspose_mul_self_eq {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
    (h : Aᴴ * A = Bᴴ * B) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ = ‖WithLp.toLp 2 (B *ᵥ x)‖ := by
  sorry

/-- **Equal Gram matrices.** `Aᴴ * A = Bᴴ * B` exactly when `A = W * B` for some `W` with
orthonormal columns, provided `A` has at least as many rows as `B`.
[HornJohnson2013, Theorem 7.3.11].
Port of `NLAlib.gram_eq_iff_exists_isometry_mul_eq`, there over `ℝ`.
Result: gram-isometry -/
theorem conjTranspose_mul_self_eq_iff_exists_mul {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
    (hcard : Fintype.card p ≤ Fintype.card m) :
    Aᴴ * A = Bᴴ * B ↔ ∃ W : Matrix m p 𝕜, HasOrthonormalCols W ∧ A = W * B := by
  sorry

/-! ### Completion -/

/-- Two unitary matrices with the same first block of columns differ by a unitary factor on the
remaining columns. [HornJohnson2013, Theorem 2.7.1, completion step].
Port of `NLAlib.exists_unitary_right_block_of_first_columns_eq`. -/
theorem HasOrthonormalCols.exists_mul_fromBlocks_one_eq {X Y : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hX : HasOrthonormalCols X) (hY : HasOrthonormalCols Y)
    (h : X.submatrix id Sum.inl = Y.submatrix id Sum.inl) :
    ∃ W : Matrix q q 𝕜, HasOrthonormalCols W ∧ X * Matrix.fromBlocks 1 0 0 W = Y := by
  sorry

/-- A block-diagonal matrix of two frames is a frame.
Port of `NLAlib.HasOrthonormalCols.fromBlocks_diagonal`. -/
theorem HasOrthonormalCols.fromBlocks_diagonal {A : Matrix m p 𝕜} {B : Matrix n q 𝕜}
    (hA : HasOrthonormalCols A) (hB : HasOrthonormalCols B) :
    HasOrthonormalCols (Matrix.fromBlocks A 0 0 B) := by
  sorry

/-! ### Topology -/

/-- The set of matrices with orthonormal columns is closed. Port of `NLAlib.isClosed_stiefel`. -/
theorem isClosed_setOf_hasOrthonormalCols :
    IsClosed {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} := by
  sorry

/-- **The set of matrices with orthonormal columns (the Stiefel manifold) is compact.**
Port of `NLAlib.stiefelCompactSpace`, there for `Fin` indices over `ℝ`. -/
theorem isCompact_setOf_hasOrthonormalCols :
    IsCompact {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} := by
  sorry

/-- A continuous real function on matrices attains its minimum over the frames, when there is at
least one. Port of `NLAlib.exists_orthogonal_isMinOn_of_continuous`. -/
theorem exists_isMinOn_setOf_hasOrthonormalCols {f : Matrix n p 𝕜 → ℝ} (hf : Continuous f)
    (h : Fintype.card p ≤ Fintype.card n) :
    ∃ Q : Matrix n p 𝕜, HasOrthonormalCols Q ∧
      IsMinOn f {Q : Matrix n p 𝕜 | HasOrthonormalCols Q} Q := by
  sorry

end NLAlib
