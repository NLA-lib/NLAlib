/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Spectral.SingularValues

/-!
# The singular value decomposition

`NLAlib.IsSVD A U σ V` says that `A = U * diagonal σ * Vᴴ` with `U` and `V` having orthonormal
columns and `σ` nonnegative. The columns are indexed by an arbitrary finite type `r`, so the
predicate covers the compact SVD, the thin SVD and partial decompositions, and with `r` a sum
type and `Matrix.fromCols` it expresses the splitting of `A` into two blocks of singular triples.
The factors need not be square and no rectangular diagonal matrix appears. A full SVD with
unitary factors is obtained from a thin one by orthonormal completion
(`NLAlib.HasOrthonormalCols.exists_fromCols`).

`σ` is not required to be sorted. When the columns are indexed by `Fin k` and `σ` is
non-increasing, `σ` is the sequence of singular values (`NLAlib.IsSVD.singularValues_eq`).

## Main definitions

* `NLAlib.IsSVD`: the thin singular value decomposition, as a predicate.

## Main results

* `NLAlib.exists_isSVD`: every matrix has an SVD with `k` columns, for every `k` between its rank
  and its smaller dimension, with `σ` the singular values.
* `NLAlib.IsSVD.singularValues_eq`, `NLAlib.IsSVD.exists_equiv_singularValues_eq`: the entries of
  `σ` are the singular values.
* `NLAlib.IsSVD.rank_eq`, `NLAlib.IsSVD.specNorm_eq`, `NLAlib.IsSVD.frobNorm_sq_eq`: rank and norms
  from any SVD.
* `NLAlib.IsSVD.conjTranspose`, `NLAlib.IsSVD.mul_left`, `NLAlib.IsSVD.reindex`: stability.
* `NLAlib.IsSVD.eq_add`, `NLAlib.exists_isSVD_fromCols`: splitting into two blocks.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r r₁ r₂ r' : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r] [Fintype r₁] [Fintype r₂] [Fintype r'] [DecidableEq r] [DecidableEq r₁]
  [DecidableEq r₂] [DecidableEq r']

/-- **Singular value decomposition**, thin form. `IsSVD A U σ V` means that `U` and `V` have
orthonormal columns indexed by the same finite type `r`, the real numbers `σ i` are nonnegative,
and `A = U * diagonal σ * Vᴴ`. The index type is arbitrary and `σ` need not be sorted.
[HornJohnson2013, Theorem 2.6.3]; [GolubVanLoan2013, §2.4]. There the factors are square and
unitary and the middle factor is a rectangular diagonal matrix; the thin form used here carries
the same information and composes with products and block splittings. -/
structure IsSVD (A : Matrix m n 𝕜) (U : Matrix m r 𝕜) (σ : r → ℝ) (V : Matrix n r 𝕜) : Prop where
  /-- The left singular vectors are orthonormal. -/
  hasOrthonormalCols_left : HasOrthonormalCols U
  /-- The right singular vectors are orthonormal. -/
  hasOrthonormalCols_right : HasOrthonormalCols V
  /-- The singular values are nonnegative. -/
  nonneg : ∀ i, 0 ≤ σ i
  /-- The decomposition `A = U Σ Vᴴ`. -/
  eq : A = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ

omit [Fintype r] in
/-- A diagonal matrix with real entries is its own conjugate transpose. -/
private theorem conjTranspose_diagonal_ofReal (σ : r → ℝ) :
    (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))ᴴ = Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact RCLike.conj_ofReal (σ i)

namespace IsSVD

variable {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}

/-- The decomposition, associated to the right. -/
private theorem eq_mul_mul (h : IsSVD A U σ V) :
    A = U * (Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ) := by
  rw [← Matrix.mul_assoc]
  exact h.eq

/-- The decomposition of the conjugate transpose. -/
private theorem conjTranspose_eq_mul_mul (h : IsSVD A U σ V) :
    Aᴴ = V * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Uᴴ := by
  rw [h.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, conjTranspose_diagonal_ofReal, Matrix.mul_assoc]

/-! ### Consequences of the decomposition -/

/-- `A * V = U * Σ`: the right singular vectors are mapped to multiples of the left ones.
Port of `NLAlib.IsSVD.mul_right`. -/
theorem mul_right_eq (h : IsSVD A U σ V) :
    A * V = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.eq, h.hasOrthonormalCols_right.mul_conjTranspose_mul_cancel_right]

/-- `Uᴴ * A = Σ * Vᴴ`. Port of `NLAlib.IsSVD.conjTranspose_mul`. -/
theorem conjTranspose_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.conjTranspose_mul_cancel_left]

/-- `Uᴴ * A * V = Σ`. Port of `NLAlib.IsSVD.conjTranspose_mul_mul`. -/
theorem conjTranspose_mul_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A * V = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.conjTranspose_mul_eq, h.hasOrthonormalCols_right.mul_conjTranspose_mul_cancel_right]

/-- The Gram matrix from an SVD: `Aᴴ * A = V * Σ² * Vᴴ`.
Port of `NLAlib.IsSVD.conjTranspose_mul_self`. -/
theorem conjTranspose_mul_self_eq (h : IsSVD A U σ V) :
    Aᴴ * A = V * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  rw [h.conjTranspose_eq_mul_mul, Matrix.mul_assoc _ _ A, h.conjTranspose_mul_eq,
    ← Matrix.mul_assoc, Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
  simp only [sq, RCLike.ofReal_mul]

/-- The other Gram matrix from an SVD: `A * Aᴴ = U * Σ² * Uᴴ`.
Port of `NLAlib.IsSVD.mul_conjTranspose_self`. -/
theorem mul_conjTranspose_self_eq (h : IsSVD A U σ V) :
    A * Aᴴ = U * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Uᴴ := by
  rw [h.conjTranspose_eq_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.mul_right_eq,
    Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
  simp only [sq, RCLike.ofReal_mul]

/-- A right singular vector is mapped to `σ i` times the left singular vector. -/
theorem mulVec_col (h : IsSVD A U σ V) (i : r) : A *ᵥ V.col i = σ i • U.col i := by
  funext j
  have hj : (A * V) j i = U j i * ((σ i : ℝ) : 𝕜) := by
    rw [h.mul_right_eq, Matrix.mul_diagonal]
  rw [Pi.smul_apply, Matrix.col_apply, RCLike.real_smul_eq_coe_mul, mul_comm, ← hj]
  rfl

/-! ### Stability -/

/-- An SVD of `A` gives an SVD of `Aᴴ` with the factors exchanged.
Port of `NLAlib.IsSVD.conjTranspose_eq`. -/
protected theorem conjTranspose (h : IsSVD A U σ V) : IsSVD Aᴴ V σ U :=
  ⟨h.hasOrthonormalCols_right, h.hasOrthonormalCols_left, h.nonneg,
    h.conjTranspose_eq_mul_mul⟩

/-- Left multiplication by a matrix with orthonormal columns: `Q * A = (Q * U) * Σ * Vᴴ` is an
SVD. This is the step that lifts the SVD of a small projected matrix to the full space. -/
theorem mul_left [DecidableEq m] (h : IsSVD A U σ V) {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (Q * A) (Q * U) σ V := by
  refine ⟨hQ.mul h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, h.nonneg, ?_⟩
  rw [Matrix.mul_assoc Q U, Matrix.mul_assoc Q, ← h.eq]

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns:
`A * Qᴴ = U * Σ * (Q * V)ᴴ` is an SVD. -/
theorem mul_conjTranspose_right [DecidableEq n] (h : IsSVD A U σ V) {Q : Matrix l n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (A * Qᴴ) U σ (Q * V) := by
  refine ⟨h.hasOrthonormalCols_left, hQ.mul h.hasOrthonormalCols_right, h.nonneg, ?_⟩
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, ← h.eq]

/-- Relabelling the singular triples by a bijection. -/
theorem reindex (h : IsSVD A U σ V) (e : r' ≃ r) :
    IsSVD A (U.submatrix id e) (σ ∘ e) (V.submatrix id e) := by
  refine ⟨h.hasOrthonormalCols_left.submatrix (Equiv.refl m) e.injective,
    h.hasOrthonormalCols_right.submatrix (Equiv.refl n) e.injective, fun i => h.nonneg (e i), ?_⟩
  have hD : Matrix.diagonal (fun i => (((σ ∘ e) i : ℝ) : 𝕜)) =
      (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)).submatrix e e :=
    (Matrix.submatrix_diagonal_equiv (fun i => ((σ i : ℝ) : 𝕜)) e).symm
  rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, ← h.eq, Matrix.submatrix_id_id]

/-! ### Rank and norms -/

/-- The rank is the number of nonzero entries of `σ`. -/
theorem rank_eq (h : IsSVD A U σ V) : A.rank = (Finset.univ.filter fun i => σ i ≠ 0).card := by
  classical
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.rank_mul, ← Matrix.rank_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    h.hasOrthonormalCols_right.rank_mul, Matrix.rank_conjTranspose, Matrix.rank_diagonal,
    Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr fun i _ => not_congr RCLike.ofReal_eq_zero)

/-- The spectral norm is the largest entry of `σ`: the supremum norm of `σ`. -/
theorem specNorm_eq (h : IsSVD A U σ V) : specNorm A = ‖σ‖ := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.specNorm_mul_left,
    h.hasOrthonormalCols_right.specNorm_mul_conjTranspose_right, specNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [RCLike.norm_ofReal]
    exact norm_le_pi_norm σ i
  · rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜)]
    exact norm_le_pi_norm (fun i => ((σ i : ℝ) : 𝕜)) i

/-- The squared Frobenius norm is the sum of the squares of the entries of `σ`. -/
theorem frobNorm_sq_eq (h : IsSVD A U σ V) : frobNorm A ^ 2 = ∑ i, σ i ^ 2 := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.frobNorm_mul_left,
    h.hasOrthonormalCols_right.frobNorm_mul_conjTranspose_right, frobNorm_diagonal_sq]
  exact Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_ofReal, sq_abs]

/-! ### The entries of `σ` are the singular values -/

/-- The singular values of `A` are those of the diagonal factor. -/
private theorem singularValues_eq_singularValues_diagonal (h : IsSVD A U σ V) :
    singularValues A = singularValues (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.singularValues_mul_left,
    h.hasOrthonormalCols_right.singularValues_mul_conjTranspose_right]

/-- In an SVD with columns indexed by `Fin k` and `σ` non-increasing, `σ` is the sequence of
singular values. Port of `NLAlib.singularValues_eq_of_eq_mul_rectDiag_mul`.
Result: svd-uniqueness -/
theorem singularValues_eq {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) (hσ : Antitone σ) (i : Fin k) :
    singularValues A i = σ i := by
  have hD : (Matrix.diagonal fun j => ((σ j : ℝ) : 𝕜)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun j => RCLike.ofReal_nonneg.mpr (h.nonneg j)
  rw [h.singularValues_eq_singularValues_diagonal, hD.singularValues_eq_eigenvalue,
    eigenvalue_diagonal hσ]

/-- In an SVD, the singular values vanish from the number of columns on, whatever the column
type. -/
theorem singularValues_of_card_le (h : IsSVD A U σ V) {i : ℕ} (hi : Fintype.card r ≤ i) :
    singularValues A i = 0 := by
  rw [h.singularValues_eq_singularValues_diagonal]
  exact singularValues_of_card_cols_le _ hi

/-- In an SVD with `k` columns, the singular values vanish from index `k` on. -/
theorem singularValues_of_le {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) {i : ℕ} (hi : k ≤ i) :
    singularValues A i = 0 :=
  h.singularValues_of_card_le (by rwa [Fintype.card_fin])

/-- In any SVD, the entries of `σ` are the leading singular values in some order. -/
theorem exists_equiv_singularValues_eq (h : IsSVD A U σ V) :
    ∃ e : r ≃ Fin (Fintype.card r), ∀ i, σ i = singularValues A (e i) := by
  let e₀ : Fin (Fintype.card r) ≃ r := (Fintype.equivFin r).symm
  let τ : Equiv.Perm (Fin (Fintype.card r)) := Tuple.sort fun j => -σ (e₀ j)
  have hmono : Monotone ((fun j => -σ (e₀ j)) ∘ τ) := Tuple.monotone_sort _
  have hanti : Antitone (σ ∘ (τ.trans e₀)) := fun a b hab => neg_le_neg_iff.mp (hmono hab)
  refine ⟨(τ.trans e₀).symm, fun i => ?_⟩
  rw [(h.reindex (τ.trans e₀)).singularValues_eq hanti, Function.comp_apply,
    Equiv.apply_symm_apply]

/-! ### Splitting into two blocks -/

omit [Fintype r₁] [Fintype r₂] in
/-- The diagonal matrix of a `Sum.elim` is block diagonal. -/
private theorem diagonal_sumElim_ofReal (σ₁ : r₁ → ℝ) (σ₂ : r₂ → ℝ) :
    Matrix.diagonal (fun i => ((Sum.elim σ₁ σ₂ i : ℝ) : 𝕜)) =
      Matrix.fromBlocks (Matrix.diagonal fun i => ((σ₁ i : ℝ) : 𝕜)) 0 0
        (Matrix.diagonal fun i => ((σ₂ i : ℝ) : 𝕜)) := by
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  cases i <;> rfl

/-- An SVD whose singular triples are split into two groups writes `A` as a sum of two pieces
with mutually orthogonal factors. This is the form in which Wedin's theorem and the analysis of
truncation consume an SVD. -/
theorem eq_add {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    A = U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ +
      U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ := by
  have hA := h.eq
  rwa [diagonal_sumElim_ofReal, Matrix.fromCols_mul_fromBlocks,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add] at hA

/-- The first block of a split SVD is an SVD of its own piece. -/
theorem fromCols_left {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ) U₁ σ₁ V₁ :=
  ⟨(hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_left).1,
    (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right).1,
    fun i => h.nonneg (Sum.inl i), rfl⟩

/-- The second block of a split SVD is an SVD of its own piece. -/
theorem fromCols_right {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ) U₂ σ₂ V₂ :=
  ⟨(hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_left).2.1,
    (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right).2.1,
    fun i => h.nonneg (Sum.inr i), rfl⟩

end IsSVD

/-! ### Existence -/

omit [Fintype r] in
/-- A column of `B` whose diagonal entry in the Gram matrix `Bᴴ * B` vanishes is zero. -/
private theorem apply_eq_zero_of_conjTranspose_mul_self_eq_diagonal {B : Matrix m r 𝕜}
    {d : r → 𝕜} (hB : Bᴴ * B = Matrix.diagonal d) {i : r} (hi : d i = 0) (j : m) :
    B j i = 0 := by
  have h0 : star (B.col i) ⬝ᵥ B.col i = 0 := by
    have hii := congrFun (congrFun hB i) i
    rwa [Matrix.diagonal_apply_eq, hi] at hii
  exact congrFun (dotProduct_star_self_eq_zero.mp h0) j

/-- A matrix `B` whose Gram matrix is `diagonal (s ^ 2)` is `U * diagonal s` for a `U` with
orthonormal columns: normalise the columns with `s i ≠ 0` and complete them. -/
private theorem exists_hasOrthonormalCols_mul_diagonal_eq {B : Matrix m r 𝕜} {s : r → ℝ}
    (hB : Bᴴ * B = Matrix.diagonal fun i => ((s i ^ 2 : ℝ) : 𝕜))
    (hr : Fintype.card r ≤ Fintype.card m) :
    ∃ U : Matrix m r 𝕜, HasOrthonormalCols U ∧
      U * Matrix.diagonal (fun i => ((s i : ℝ) : 𝕜)) = B := by
  classical
  obtain ⟨C, hCB⟩ : ∃ C : Matrix m r 𝕜,
      C = B * Matrix.diagonal fun i => (((s i)⁻¹ : ℝ) : 𝕜) := ⟨_, rfl⟩
  have hC : Cᴴ * C =
      Matrix.diagonal fun i => (((s i)⁻¹ : ℝ) : 𝕜) * (((s i ^ 2 : ℝ) : 𝕜) * ((s i)⁻¹ : ℝ)) := by
    rw [hCB, Matrix.conjTranspose_mul, conjTranspose_diagonal_ofReal, Matrix.mul_assoc,
      ← Matrix.mul_assoc Bᴴ, hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hQ₁ : HasOrthonormalCols (C.submatrix id (Subtype.val : {i // s i ≠ 0} → r)) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hC,
      Matrix.submatrix_diagonal _ _ Subtype.val_injective, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hi : s i ≠ 0 := i.2
    rw [Function.comp_apply, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul,
      show (s i)⁻¹ * (s i ^ 2 * (s i)⁻¹) = 1 by field_simp, RCLike.ofReal_one]
  obtain ⟨Q₂, hQ⟩ := hQ₁.exists_fromCols_of_card_le (p := {i // ¬ s i ≠ 0}) (by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => s i ≠ 0)]
    exact hr)
  refine ⟨(Matrix.fromCols _ Q₂).submatrix id (Equiv.sumCompl fun i => s i ≠ 0).symm,
    hQ.submatrix (Equiv.refl m) (Equiv.injective _), ?_⟩
  ext j i
  rw [Matrix.mul_diagonal, Matrix.submatrix_apply]
  by_cases hi : s i ≠ 0
  · rw [Equiv.sumCompl_symm_apply_of_pos (p := fun i => s i ≠ 0) hi, Matrix.fromCols_apply_inl,
      Matrix.submatrix_apply, hCB, Matrix.mul_diagonal]
    change B j i * (((s i)⁻¹ : ℝ) : 𝕜) * ((s i : ℝ) : 𝕜) = B j i
    rw [mul_assoc, ← RCLike.ofReal_mul, inv_mul_cancel₀ hi, RCLike.ofReal_one, mul_one]
  · have hi0 : s i = 0 := not_not.mp hi
    rw [hi0, RCLike.ofReal_zero, mul_zero]
    refine (apply_eq_zero_of_conjTranspose_mul_self_eq_diagonal hB ?_ j).symm
    rw [hi0, zero_pow two_ne_zero, RCLike.ofReal_zero]

/-- **Existence of the singular value decomposition.** For every `k` between the rank of `A` and
its smaller dimension, `A = U * diagonal σ * Vᴴ` with `U`, `V` having `k` orthonormal columns and
`σ` the first `k` singular values of `A`. With `k = rank A` this is the compact SVD and with
`k = min (card m) (card n)` the thin SVD.
[HornJohnson2013, Theorem 2.6.3]; [GolubVanLoan2013, Theorem 2.4.1].
Port of `NLAlib.exists_isSVD`, there with square factors.
Result: svd-existence -/
theorem exists_isSVD (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) (hkm : k ≤ Fintype.card m)
    (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜),
      IsSVD A U (fun i => singularValues A i) V := by
  classical
  obtain ⟨W, hW, hGW⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_eq_mul_diagonal_mul_conjTranspose
  simp only [← sq_singularValues] at hGW
  have hAW : (A * W)ᴴ * (A * W) =
      Matrix.diagonal fun i : Fin (Fintype.card n) => ((singularValues A i ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hGW,
      Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.mul_one,
      hW.conjTranspose_mul_cancel_left]
  have hV : HasOrthonormalCols (W.submatrix id (Fin.castLE hkn)) :=
    hW.submatrix (Equiv.refl n) (Fin.castLE_injective hkn)
  have hAV : A * W.submatrix id (Fin.castLE hkn) = (A * W).submatrix id (Fin.castLE hkn) := by
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  have hB : (A * W.submatrix id (Fin.castLE hkn))ᴴ * (A * W.submatrix id (Fin.castLE hkn)) =
      Matrix.diagonal fun i : Fin k => ((singularValues A i ^ 2 : ℝ) : 𝕜) := by
    rw [hAV, Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hAW,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hkn)]
    rfl
  obtain ⟨U, hU, hUB⟩ := exists_hasOrthonormalCols_mul_diagonal_eq hB (by rwa [Fintype.card_fin])
  refine ⟨U, _, hU, hV, fun i => singularValues_nonneg A i, ?_⟩
  rw [hUB, hAV]
  have hWW : W * Wᴴ = 1 := hW.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  have hAWW : A = A * W * Wᴴ := by rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  refine hAWW.trans ?_
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.conjTranspose_submatrix]
  refine (Fintype.sum_of_injective (Fin.castLE hkn) (Fin.castLE_injective hkn) _ _ ?_
    fun i => rfl).symm
  intro i hi
  have hki : k ≤ i := by
    by_contra hlt
    exact hi ⟨⟨i, not_le.mp hlt⟩, Fin.ext rfl⟩
  rw [apply_eq_zero_of_conjTranspose_mul_self_eq_diagonal hAW ?_ a, zero_mul]
  rw [(singularValues_eq_zero_iff A).mpr (hk.trans hki), zero_pow two_ne_zero,
    RCLike.ofReal_zero]

/-- **Existence of a split singular value decomposition.** For `k + d` between the rank of `A`
and its smaller dimension, `A` has an SVD whose first block carries the `k` largest singular
values and whose second block carries the next `d`.
Port of `NLAlib.exists_svd_right_blocks`, there over `ℝ` with `Fin` matrices. -/
theorem exists_isSVD_fromCols (A : Matrix m n 𝕜) {k d : ℕ} (hk : A.rank ≤ k + d)
    (hkm : k + d ≤ Fintype.card m) (hkn : k + d ≤ Fintype.card n) :
    ∃ (U₁ : Matrix m (Fin k) 𝕜) (U₂ : Matrix m (Fin d) 𝕜) (V₁ : Matrix n (Fin k) 𝕜)
      (V₂ : Matrix n (Fin d) 𝕜),
      IsSVD A (Matrix.fromCols U₁ U₂)
        (Sum.elim (fun i : Fin k => singularValues A i) (fun j : Fin d => singularValues A (k + j)))
        (Matrix.fromCols V₁ V₂) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A hk hkm hkn
  have h' := h.reindex finSumFinEquiv
  have hσ : (fun i : Fin (k + d) => singularValues A i) ∘ finSumFinEquiv =
      Sum.elim (fun i : Fin k => singularValues A i)
        (fun j : Fin d => singularValues A (k + j)) := by
    funext i
    rcases i with i | j
    · rw [Function.comp_apply, finSumFinEquiv_apply_left, Fin.val_castAdd, Sum.elim_inl]
    · rw [Function.comp_apply, finSumFinEquiv_apply_right, Fin.val_natAdd, Sum.elim_inr]
  rw [hσ, ← Matrix.fromCols_toCols (U.submatrix id finSumFinEquiv),
    ← Matrix.fromCols_toCols (V.submatrix id finSumFinEquiv)] at h'
  exact ⟨_, _, _, _, h'⟩

omit [Fintype m] in
/-- Every matrix of rank `k` factors as `B * Cᴴ` through `k` columns; more precisely
`A = U * (V * Σ)ᴴ` from the compact SVD. The rank factorisation used when a proof only needs
"`A` has rank at most `k`" in product form. -/
theorem exists_eq_mul_conjTranspose_of_rank_le [Finite m] (A : Matrix m n 𝕜) {k : ℕ}
    (hk : A.rank ≤ k) : ∃ (B : Matrix m (Fin k) 𝕜) (C : Matrix n (Fin k) 𝕜), A = B * Cᴴ := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hS : HasOrthonormalCols
      ((1 : Matrix (Fin k) (Fin k) 𝕜).submatrix id (Fin.castLE hk)) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl _) (Fin.castLE_injective hk)
  refine ⟨U * ((1 : Matrix (Fin k) (Fin k) 𝕜).submatrix id (Fin.castLE hk))ᴴ,
    V * Matrix.diagonal (fun i : Fin A.rank => ((singularValues A i : ℝ) : 𝕜)) *
      ((1 : Matrix (Fin k) (Fin k) 𝕜).submatrix id (Fin.castLE hk))ᴴ, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    conjTranspose_diagonal_ofReal, Matrix.mul_assoc U, hS.conjTranspose_mul_cancel_left,
    ← Matrix.mul_assoc]
  exact h.eq

end NLAlib
