/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.ConjTranspose
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
* `NLAlib.HasOrthonormalCols.sq_singularValues_toBlocks₂₁`,
  `NLAlib.HasOrthonormalCols.singularValues_toBlocks₂₂`,
  `NLAlib.HasOrthonormalCols.singularValues_toBlocks₁₂`: the singular values of the blocks.
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

/-- The block computation behind the unitarity of the canonical CS matrix. -/
private theorem conjTranspose_fromBlocks_mul_self_eq_one {C S : Matrix p p 𝕜} {E : Matrix q p 𝕜}
    (hC : Cᴴ = C) (hS : Sᴴ = S) (hE : Eᴴ * E = 1) (hCS : C * C + S * S = 1)
    (hcomm : C * S = S * C) :
    (Matrix.fromBlocks C (S * Eᴴ) (-(E * S)) (E * C * Eᴴ + (1 - E * Eᴴ)))ᴴ *
      Matrix.fromBlocks C (S * Eᴴ) (-(E * S)) (E * C * Eᴴ + (1 - E * Eᴴ)) = 1 := by
  obtain ⟨R, hR⟩ : ∃ R, R = E * C * Eᴴ + (1 - E * Eᴴ) := ⟨_, rfl⟩
  rw [← hR]
  have hRt : Rᴴ = R := by
    rw [hR]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, hC, Matrix.mul_assoc]
  have hER : Eᴴ * R = C * Eᴴ := by
    rw [hR]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hE,
      Matrix.one_mul, sub_self, add_zero]
  have hRE : R * E = E * C := by
    have h := congrArg Matrix.conjTranspose hER
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hRt, hC] at h
  have hRR : R * R = E * (C * C) * Eᴴ + (1 - E * Eᴴ) := by
    calc R * R = R * (E * C * Eᴴ + (1 - E * Eᴴ)) := by rw [← hR]
      _ = R * E * C * Eᴴ + (R - R * E * Eᴴ) := by
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = E * (C * C) * Eᴴ + (1 - E * Eᴴ) := by
        rw [hRE, hR]
        simp only [Matrix.mul_assoc]
        abel
  have h11 : Cᴴ * C + (-(E * S))ᴴ * (-(E * S)) = 1 := by
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.conjTranspose_mul,
      hC, hS, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, hCS]
  have h12 : Cᴴ * (S * Eᴴ) + (-(E * S))ᴴ * R = 0 := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hC, hS, Matrix.neg_mul,
      Matrix.mul_assoc S, hER, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm, add_neg_cancel]
  have h21 : (S * Eᴴ)ᴴ * C + Rᴴ * (-(E * S)) = 0 := by
    have h := congrArg Matrix.conjTranspose h12
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using h
  have h22 : (S * Eᴴ)ᴴ * (S * Eᴴ) + Rᴴ * R = 1 := by
    have h : E * S * (S * Eᴴ) + E * (C * C) * Eᴴ = E * Eᴴ := by
      rw [Matrix.mul_assoc E S, ← Matrix.mul_assoc S S, ← Matrix.mul_assoc E (S * S),
        ← Matrix.add_mul, ← Matrix.mul_add, add_comm, hCS, Matrix.mul_one]
    rw [hRt, hRR, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS, ← add_assoc,
      h, add_sub_cancel]
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h11, h12, h21, h22,
    Matrix.fromBlocks_one]

/-- The canonical CS matrix is unitary when `c i ^ 2 + s i ^ 2 = 1`.
Port of `NLAlib.hasOrthonormalCols_csCanonicalMatrix`. -/
theorem hasOrthonormalCols_csMatrix {c s : p → ℝ} (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) (e : p ↪ q) :
    HasOrthonormalCols (csMatrix 𝕜 c s e) := by
  refine conjTranspose_fromBlocks_mul_self_eq_one (Matrix.conjTranspose_diagonal_ofReal c)
    (Matrix.conjTranspose_diagonal_ofReal s)
    (hasOrthonormalCols_one.submatrix (Equiv.refl q) e.injective) ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_add, ← sq, ← sq, h i,
      RCLike.ofReal_one]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

/-- The Gram identities of the two block columns of a partitioned unitary matrix. -/
private theorem toBlocks_gram {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜} (hU : HasOrthonormalCols U) :
    U.toBlocks₁₁ᴴ * U.toBlocks₁₁ + U.toBlocks₂₁ᴴ * U.toBlocks₂₁ = 1 ∧
      U.toBlocks₁₂ᴴ * U.toBlocks₁₂ + U.toBlocks₂₂ᴴ * U.toBlocks₂₂ = 1 := by
  have h := hU.conjTranspose_mul_self
  rw [← Matrix.fromBlocks_toBlocks U, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  exact ⟨h.1, h.2.2.2⟩

/-- The Gram identities of the two block rows of a partitioned unitary matrix, written for the
conjugate transposes of the blocks. -/
private theorem toBlocks_conjTranspose_gram {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) :
    U.toBlocks₁₁ᴴᴴ * U.toBlocks₁₁ᴴ + U.toBlocks₁₂ᴴᴴ * U.toBlocks₁₂ᴴ = 1 ∧
      U.toBlocks₂₁ᴴᴴ * U.toBlocks₂₁ᴴ + U.toBlocks₂₂ᴴᴴ * U.toBlocks₂₂ᴴ = 1 := by
  have h := hU.mul_conjTranspose_self
  rw [← Matrix.fromBlocks_toBlocks U, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  simp only [Matrix.conjTranspose_conjTranspose]
  exact ⟨h.1, h.2.2.2⟩

omit [DecidableEq p] [DecidableEq q] in
/-- The leading block of a matrix multiplied on both sides by block-diagonal matrices. -/
private theorem toBlocks₁₁_fromBlocks_mul_mul (V W : Matrix p p 𝕜) (O Z : Matrix q q 𝕜)
    (U : Matrix (p ⊕ q) (p ⊕ q) 𝕜) :
    (Matrix.fromBlocks V 0 0 O * U * Matrix.fromBlocks W 0 0 Z).toBlocks₁₁ =
      V * U.toBlocks₁₁ * W := by
  nth_rw 1 [← Matrix.fromBlocks_toBlocks U]
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₁]

/-- A partitioned unitary matrix whose leading block is the diagonal matrix of cosines is
reduced to the canonical CS matrix by unitary factors acting on the second block. -/
private theorem exists_fromBlocks_one_mul_mul_eq_csMatrix {M : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hM : HasOrthonormalCols M) {c s : p → ℝ} (h : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hC : M.toBlocks₁₁ = Matrix.diagonal fun i => ((c i : ℝ) : 𝕜)) (e : p ↪ q) :
    ∃ O Z : Matrix q q 𝕜, HasOrthonormalCols O ∧ HasOrthonormalCols Z ∧
      Matrix.fromBlocks 1 0 0 O * M * Matrix.fromBlocks 1 0 0 Z = csMatrix 𝕜 c s e := by
  have hK : HasOrthonormalCols (csMatrix 𝕜 c s e) := hasOrthonormalCols_csMatrix h e
  have hK₁₁ : (csMatrix 𝕜 c s e).toBlocks₁₁ = M.toBlocks₁₁ := hC.symm
  have hG : (csMatrix 𝕜 c s e).toBlocks₂₁ᴴ * (csMatrix 𝕜 c s e).toBlocks₂₁ =
      M.toBlocks₂₁ᴴ * M.toBlocks₂₁ := by
    have h₁ := (toBlocks_gram hK).1
    rw [hK₁₁] at h₁
    exact add_left_cancel (h₁.trans (toBlocks_gram hM).1.symm)
  obtain ⟨O, hO, hOM⟩ := (conjTranspose_mul_self_eq_iff_exists_mul le_rfl).mp hG
  have hN : HasOrthonormalCols (Matrix.fromBlocks 1 0 0 O * M) :=
    (hasOrthonormalCols_one.fromBlocks_diagonal hO).mul hM
  have hN_eq : Matrix.fromBlocks 1 0 0 O * M =
      Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ (O * M.toBlocks₂₁) (O * M.toBlocks₂₂) := by
    nth_rw 1 [← Matrix.fromBlocks_toBlocks M]
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hFirst : (Matrix.fromBlocks 1 0 0 O * M).submatrix id Sum.inl =
      (csMatrix 𝕜 c s e).submatrix id Sum.inl := by
    rw [hN_eq, ← hK₁₁, ← hOM]
    ext (i | i) j <;> rfl
  obtain ⟨Z, hZ, hNZ⟩ := hN.exists_mul_fromBlocks_one_eq hK hFirst
  exact ⟨O, Z, hO, hZ, hNZ⟩

/-- **The CS decomposition.** A unitary matrix `U` partitioned into blocks over `p ⊕ q`, with
`p` no larger than `q`, factors as `diag(V₁, V₂) * csMatrix c s e * diag(W₁, W₂)ᴴ` with unitary
`V₁`, `W₁`, `V₂`, `W₂` and `c i, s i ≥ 0`, `c i ^ 2 + s i ^ 2 = 1`; the cosines `c` are the
singular values of the leading block, in some order.
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
      (∃ f : p ≃ Fin (Fintype.card p), ∀ i, c i = singularValues U.toBlocks₁₁ (f i)) ∧
      U = Matrix.fromBlocks V₁ 0 0 V₂ * csMatrix 𝕜 c s e * (Matrix.fromBlocks W₁ 0 0 W₂)ᴴ := by
  obtain ⟨V₀, W₀, h₀⟩ := exists_isSVD U.toBlocks₁₁ (k := Fintype.card p)
    (Matrix.rank_le_card_width _) le_rfl le_rfl
  have hSVD := h₀.reindex (Fintype.equivFin p)
  obtain ⟨V, hVdef⟩ : ∃ V, V = V₀.submatrix id (Fintype.equivFin p) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = W₀.submatrix id (Fintype.equivFin p) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ :
      ∃ c : p → ℝ, c = fun i => singularValues U.toBlocks₁₁ (Fintype.equivFin p i) := ⟨_, rfl⟩
  rw [← hVdef, ← hWdef] at hSVD
  have hc0 : ∀ i, 0 ≤ c i := fun i => by rw [hcdef]; exact singularValues_nonneg _ _
  have hc1 : ∀ i, c i ≤ 1 := fun i => by
    rw [hcdef]
    exact singularValues_le_one_of_conjTranspose_mul_self_add_eq_one (toBlocks_gram hU).1 _
  have hcs : ∀ i, c i ^ 2 + √(1 - c i ^ 2) ^ 2 = 1 := fun i => by
    rw [Real.sq_sqrt (by nlinarith [hc0 i, hc1 i]), add_sub_cancel]
  have hV := hSVD.hasOrthonormalCols_left
  have hW := hSVD.hasOrthonormalCols_right
  have hM := ((hV.fromBlocks_diagonal (hasOrthonormalCols_one (n := q))).conjTranspose.mul hU).mul
    (hW.fromBlocks_diagonal (hasOrthonormalCols_one (n := q)))
  have hM₁₁ : ((Matrix.fromBlocks V 0 0 (1 : Matrix q q 𝕜))ᴴ * U *
      Matrix.fromBlocks W 0 0 (1 : Matrix q q 𝕜)).toBlocks₁₁ =
      Matrix.diagonal fun i => ((c i : ℝ) : 𝕜) := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
      toBlocks₁₁_fromBlocks_mul_mul, hcdef]
    exact hSVD.conjTranspose_mul_mul_eq
  obtain ⟨O, Z, hO, hZ, hOZ⟩ := exists_fromBlocks_one_mul_mul_eq_csMatrix hM hcs hM₁₁ e
  have hP := hV.fromBlocks_diagonal hO.conjTranspose
  have hR := hW.fromBlocks_diagonal hZ
  refine ⟨V, W, Oᴴ, Z, c, fun i => √(1 - c i ^ 2), hV, hW, hO.conjTranspose, hZ, hc0,
    fun i => Real.sqrt_nonneg _, hcs, ⟨Fintype.equivFin p, fun i => by rw [hcdef]⟩, ?_⟩
  have hL : Matrix.fromBlocks 1 0 0 O * (Matrix.fromBlocks V 0 0 (1 : Matrix q q 𝕜))ᴴ =
      (Matrix.fromBlocks V 0 0 Oᴴ)ᴴ := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  have hR' : Matrix.fromBlocks W 0 0 (1 : Matrix q q 𝕜) * Matrix.fromBlocks 1 0 0 Z =
      Matrix.fromBlocks W 0 0 Z := by
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  have hK : (Matrix.fromBlocks V 0 0 Oᴴ)ᴴ * U * Matrix.fromBlocks W 0 0 Z =
      csMatrix 𝕜 c (fun i => √(1 - c i ^ 2)) e := by
    rw [← hOZ, ← hL, ← hR']
    simp only [Matrix.mul_assoc]
  rw [← hK]
  simp only [Matrix.mul_assoc]
  rw [hR.mul_conjTranspose_self, Matrix.mul_one, ← Matrix.mul_assoc, hP.mul_conjTranspose_self,
    Matrix.one_mul]

/-- The singular values of the two blocks of the first block column of a partitioned unitary
matrix: `σ_i(U₂₁)² = 1 - σ_j(U₁₁)²` for `i + j + 1 = card p`.
[GolubVanLoan2013, Theorem 2.5.2]. -/
theorem HasOrthonormalCols.sq_singularValues_toBlocks₂₁ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) {i j : ℕ} (hij : i + j + 1 = Fintype.card p) :
    singularValues U.toBlocks₂₁ i ^ 2 = 1 - singularValues U.toBlocks₁₁ j ^ 2 :=
  sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one (toBlocks_gram hU).1 hij

/-- The diagonal blocks of a partitioned unitary matrix have the same singular values below one:
`σ_i(U₂₂) = σ_j(U₁₁)` whenever `i = j + (card q - card p)`, stated without subtraction. -/
theorem HasOrthonormalCols.singularValues_toBlocks₂₂ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) {i j : ℕ} (hij : i + Fintype.card p = j + Fintype.card q) :
    singularValues U.toBlocks₂₂ i = singularValues U.toBlocks₁₁ j := by
  rcases le_or_gt (Fintype.card q) i with hi | hi
  · rw [singularValues_of_card_cols_le _ hi, singularValues_of_card_cols_le _ (by omega)]
  · obtain ⟨k, hk⟩ : ∃ k, i + k + 1 = Fintype.card q := ⟨Fintype.card q - 1 - i, by omega⟩
    have h₁ := sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one
      (toBlocks_conjTranspose_gram hU).2 hk
    rw [singularValues_conjTranspose, singularValues_conjTranspose,
      hU.sq_singularValues_toBlocks₂₁ (by omega : k + j + 1 = Fintype.card p),
      sub_sub_cancel] at h₁
    exact (sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp h₁

/-- The off-diagonal blocks of a partitioned unitary matrix have the same singular values.
[GolubVanLoan2013, Theorem 2.5.3 context]. -/
theorem HasOrthonormalCols.singularValues_toBlocks₁₂ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) (k : ℕ) :
    singularValues U.toBlocks₁₂ k = singularValues U.toBlocks₂₁ k := by
  rcases le_or_gt (Fintype.card p) k with hk | hk
  · rw [singularValues_of_card_rows_le _ hk, singularValues_of_card_cols_le _ hk]
  · obtain ⟨j, hj⟩ : ∃ j, k + j + 1 = Fintype.card p := ⟨Fintype.card p - 1 - k, by omega⟩
    have h₁ := sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one
      (toBlocks_conjTranspose_gram hU).1 hj
    rw [singularValues_conjTranspose, singularValues_conjTranspose,
      ← hU.sq_singularValues_toBlocks₂₁ hj] at h₁
    exact (sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp h₁

/-- The off-diagonal blocks of a partitioned unitary matrix have the same rank.
Port of `NLAlib.rank_offDiagonal_blocks_eq_of_unitary`. -/
theorem HasOrthonormalCols.rank_toBlocks₁₂ {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) : U.toBlocks₁₂.rank = U.toBlocks₂₁.rank := by
  refine le_antisymm ?_ ?_
  · rw [← singularValues_eq_zero_iff, hU.singularValues_toBlocks₁₂, singularValues_eq_zero_iff]
  · rw [← singularValues_eq_zero_iff, ← hU.singularValues_toBlocks₁₂, singularValues_eq_zero_iff]

/-- The ranks of the diagonal blocks of a partitioned unitary matrix differ by the difference of
the block sizes. Port of `NLAlib.rank_bottomRight_eq_rank_topLeft_add_card_sub_of_unitary`. -/
theorem HasOrthonormalCols.rank_toBlocks₂₂_add {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜}
    (hU : HasOrthonormalCols U) :
    U.toBlocks₂₂.rank + Fintype.card p = U.toBlocks₁₁.rank + Fintype.card q := by
  have h₂ : Fintype.card q ≤ U.toBlocks₂₂.rank + Fintype.card p := by
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k, U.toBlocks₂₂.rank + k + 1 = Fintype.card q :=
      ⟨Fintype.card q - 1 - U.toBlocks₂₂.rank, by omega⟩
    have h := sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one
      (toBlocks_conjTranspose_gram hU).2 hk
    rw [singularValues_conjTranspose, singularValues_conjTranspose,
      (singularValues_eq_zero_iff _).mpr le_rfl,
      singularValues_of_card_cols_le _ (by omega : Fintype.card p ≤ k)] at h
    norm_num at h
  have h₁ : Fintype.card p ≤ U.toBlocks₁₁.rank + Fintype.card q := by
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k, k + U.toBlocks₁₁.rank + 1 = Fintype.card p :=
      ⟨Fintype.card p - 1 - U.toBlocks₁₁.rank, by omega⟩
    have h := hU.sq_singularValues_toBlocks₂₁ hk
    rw [(singularValues_eq_zero_iff U.toBlocks₁₁).mpr le_rfl,
      singularValues_of_card_rows_le _ (by omega : Fintype.card q ≤ k)] at h
    norm_num at h
  rcases Nat.lt_trichotomy (U.toBlocks₂₂.rank + Fintype.card p)
    (U.toBlocks₁₁.rank + Fintype.card q) with hlt | heq | hgt
  · obtain ⟨j, hj⟩ : ∃ j, U.toBlocks₂₂.rank + Fintype.card p = j + Fintype.card q :=
      ⟨U.toBlocks₂₂.rank + Fintype.card p - Fintype.card q, by omega⟩
    have h := hU.singularValues_toBlocks₂₂ hj
    rw [(singularValues_eq_zero_iff _).mpr le_rfl] at h
    exact absurd h.symm ((singularValues_pos_iff _).mpr (by omega)).ne'
  · exact heq
  · obtain ⟨i, hi⟩ : ∃ i, i + Fintype.card p = U.toBlocks₁₁.rank + Fintype.card q :=
      ⟨U.toBlocks₁₁.rank + Fintype.card q - Fintype.card p, by omega⟩
    have h := hU.singularValues_toBlocks₂₂ hi
    rw [(singularValues_eq_zero_iff U.toBlocks₁₁).mpr le_rfl] at h
    exact absurd h ((singularValues_pos_iff _).mpr (by omega)).ne'

end NLAlib
