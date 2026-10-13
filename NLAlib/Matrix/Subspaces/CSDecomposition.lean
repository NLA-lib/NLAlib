/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.Frames
public import NLAlib.Matrix.Subspaces.ProjectorPair
public import NLAlib.Matrix.Spectral.SVD

/-!
# The CS decomposition

A unitary matrix partitioned into four blocks is reduced, by unitary factors acting on the two
row blocks and the two column blocks separately, to a canonical matrix of cosines and sines. The
singular values of the four blocks are therefore tied together; those relations are also stated
directly.

## Main definitions

* `NLAlib.csMatrix`: the canonical matrix of a CS decomposition.

## Main results

* `NLAlib.exists_cs_decomposition`: the CS decomposition of a partitioned unitary matrix.
* `NLAlib.HasOrthonormalCols.rank_toBlocks₁₂`, `NLAlib.HasOrthonormalCols.rank_toBlocks₂₂_add`:
  the ranks of the blocks.
* `NLAlib.HasOrthonormalCols.sq_singularValues_toBlocks₂₁`: the singular values of the blocks of a
  column block.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
  [DecidableEq q]

/-- The **canonical matrix of a CS decomposition** with cosines `c`, sines `s` and an injection
`e` of the first index block into the second: in block form
`[C, S Eᴴ; -E S, E C Eᴴ + (1 - E Eᴴ)]` with `C`, `S` the diagonal matrices of `c`, `s` and `E` the
coordinate inclusion of `e`.
[HornJohnson2013, Theorem 2.7.1]; [GolubVanLoan2013, Theorem 2.5.3].
Port of `NLAlib.csCanonicalMatrix`. -/
def csMatrix (𝕜 : Type*) [RCLike 𝕜] (c s : p → ℝ) (e : p ↪ q) : Matrix (p ⊕ q) (p ⊕ q) 𝕜 :=
  let E : Matrix q p 𝕜 := (1 : Matrix q q 𝕜).submatrix id e
  let C : Matrix p p 𝕜 := Matrix.diagonal fun i => ((c i : ℝ) : 𝕜)
  let S : Matrix p p 𝕜 := Matrix.diagonal fun i => ((s i : ℝ) : 𝕜)
  Matrix.fromBlocks C (S * Eᴴ) (-(E * S)) (E * C * Eᴴ + (1 - E * Eᴴ))

/-- The canonical CS matrix is unitary when `c i ^ 2 + s i ^ 2 = 1`.
Port of `NLAlib.hasOrthonormalCols_csCanonicalMatrix`. -/
theorem hasOrthonormalCols_csMatrix {c s : p → ℝ} (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) (e : p ↪ q) :
    HasOrthonormalCols (csMatrix 𝕜 c s e) := by
  sorry

/-- **The CS decomposition.** A unitary matrix `U` partitioned into blocks over `p ⊕ q`, with
`p` no larger than `q`, factors as `diag(V₁, V₂) * csMatrix c s e * diag(W₁, W₂)ᴴ` with unitary
`V₁`, `W₁`, `V₂`, `W₂` and `c i, s i ≥ 0`, `c i ^ 2 + s i ^ 2 = 1`.
[HornJohnson2013, Theorem 2.7.1]; [GolubVanLoan2013, Theorem 2.5.3]; [PaigeWei1994].
Port of `NLAlib.exists_cs_decomposition_of_embedding` and
`NLAlib.exists_complex_cs_decomposition_of_embedding`.
Result: cs-decomposition -/
theorem exists_cs_decomposition {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜} (hU : HasOrthonormalCols U)
    (e : p ↪ q) :
    ∃ (V₁ W₁ : Matrix p p 𝕜) (V₂ W₂ : Matrix q q 𝕜) (c s : p → ℝ),
      HasOrthonormalCols V₁ ∧ HasOrthonormalCols W₁ ∧ HasOrthonormalCols V₂ ∧
      HasOrthonormalCols W₂ ∧ (∀ i, 0 ≤ c i) ∧ (∀ i, 0 ≤ s i) ∧
      (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      U = Matrix.fromBlocks V₁ 0 0 V₂ * csMatrix 𝕜 c s e * (Matrix.fromBlocks W₁ 0 0 W₂)ᴴ := by
  sorry

/-- The off-diagonal blocks of a partitioned unitary matrix have the same rank.
Port of `NLAlib.rank_offDiagonal_blocks_eq_of_unitary`. -/
theorem HasOrthonormalCols.rank_toBlocks₁₂ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) : U.toBlocks₁₂.rank = U.toBlocks₂₁.rank := by
  sorry

/-- The ranks of the diagonal blocks of a partitioned unitary matrix differ by the difference of
the block sizes. Port of `NLAlib.rank_bottomRight_eq_rank_topLeft_add_card_sub_of_unitary`. -/
theorem HasOrthonormalCols.rank_toBlocks₂₂_add {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) :
    U.toBlocks₂₂.rank + Fintype.card p = U.toBlocks₁₁.rank + Fintype.card q := by
  sorry

/-- The singular values of the two blocks of the first block column of a partitioned unitary
matrix: `σ_i(U₂₁)² = 1 - σ_j(U₁₁)²` for `i + j + 1 = card p`.
[GolubVanLoan2013, Theorem 2.5.2]. -/
theorem HasOrthonormalCols.sq_singularValues_toBlocks₂₁ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) {i j : ℕ} (hij : i + j + 1 = Fintype.card p) :
    singularValues U.toBlocks₂₁ i ^ 2 = 1 - singularValues U.toBlocks₁₁ j ^ 2 := by
  sorry

/-- The diagonal blocks of a partitioned unitary matrix have the same singular values below one:
`σ_i(U₂₂) = σ_j(U₁₁)` whenever `i = j + (card q - card p)`, stated without subtraction. -/
theorem HasOrthonormalCols.singularValues_toBlocks₂₂ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) {i j : ℕ} (hij : i + Fintype.card p = j + Fintype.card q) :
    singularValues U.toBlocks₂₂ i = singularValues U.toBlocks₁₁ j := by
  sorry

end NLAlib
