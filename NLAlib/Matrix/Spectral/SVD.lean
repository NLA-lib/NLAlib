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

open scoped Matrix

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

namespace IsSVD

variable {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}

/-! ### Consequences of the decomposition -/

/-- `A * V = U * Σ`: the right singular vectors are mapped to multiples of the left ones.
Port of `NLAlib.IsSVD.mul_right`. -/
theorem mul_right_eq (h : IsSVD A U σ V) :
    A * V = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  sorry

/-- `Uᴴ * A = Σ * Vᴴ`. Port of `NLAlib.IsSVD.conjTranspose_mul`. -/
theorem conjTranspose_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
  sorry

/-- `Uᴴ * A * V = Σ`. Port of `NLAlib.IsSVD.conjTranspose_mul_mul`. -/
theorem conjTranspose_mul_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A * V = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  sorry

/-- The Gram matrix from an SVD: `Aᴴ * A = V * Σ² * Vᴴ`.
Port of `NLAlib.IsSVD.conjTranspose_mul_self`. -/
theorem conjTranspose_mul_self_eq (h : IsSVD A U σ V) :
    Aᴴ * A = V * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  sorry

/-- The other Gram matrix from an SVD: `A * Aᴴ = U * Σ² * Uᴴ`.
Port of `NLAlib.IsSVD.mul_conjTranspose_self`. -/
theorem mul_conjTranspose_self_eq (h : IsSVD A U σ V) :
    A * Aᴴ = U * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Uᴴ := by
  sorry

/-- A right singular vector is mapped to `σ i` times the left singular vector. -/
theorem mulVec_col (h : IsSVD A U σ V) (i : r) : A *ᵥ V.col i = σ i • U.col i := by
  sorry

/-! ### Stability -/

/-- An SVD of `A` gives an SVD of `Aᴴ` with the factors exchanged.
Port of `NLAlib.IsSVD.conjTranspose_eq`. -/
protected theorem conjTranspose (h : IsSVD A U σ V) : IsSVD Aᴴ V σ U := by
  sorry

/-- Left multiplication by a matrix with orthonormal columns: `Q * A = (Q * U) * Σ * Vᴴ` is an
SVD. This is the step that lifts the SVD of a small projected matrix to the full space. -/
theorem mul_left [DecidableEq m] (h : IsSVD A U σ V) {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (Q * A) (Q * U) σ V := by
  sorry

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns:
`A * Qᴴ = U * Σ * (Q * V)ᴴ` is an SVD. -/
theorem mul_conjTranspose_right [DecidableEq n] (h : IsSVD A U σ V) {Q : Matrix l n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (A * Qᴴ) U σ (Q * V) := by
  sorry

/-- Relabelling the singular triples by a bijection. -/
theorem reindex (h : IsSVD A U σ V) (e : r' ≃ r) :
    IsSVD A (U.submatrix id e) (σ ∘ e) (V.submatrix id e) := by
  sorry

/-! ### Rank and norms -/

/-- The rank is the number of nonzero entries of `σ`. -/
theorem rank_eq (h : IsSVD A U σ V) : A.rank = (Finset.univ.filter fun i => σ i ≠ 0).card := by
  sorry

/-- The spectral norm is the largest entry of `σ`: the supremum norm of `σ`. -/
theorem specNorm_eq (h : IsSVD A U σ V) : specNorm A = ‖σ‖ := by
  sorry

/-- The squared Frobenius norm is the sum of the squares of the entries of `σ`. -/
theorem frobNorm_sq_eq (h : IsSVD A U σ V) : frobNorm A ^ 2 = ∑ i, σ i ^ 2 := by
  sorry

/-! ### The entries of `σ` are the singular values -/

/-- In an SVD with columns indexed by `Fin k` and `σ` non-increasing, `σ` is the sequence of
singular values. Port of `NLAlib.singularValues_eq_of_eq_mul_rectDiag_mul`.
Result: svd-uniqueness -/
theorem singularValues_eq {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) (hσ : Antitone σ) (i : Fin k) :
    singularValues A i = σ i := by
  sorry

/-- In an SVD with `k` columns, the singular values vanish from index `k` on. -/
theorem singularValues_of_le {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) {i : ℕ} (hi : k ≤ i) :
    singularValues A i = 0 := by
  sorry

/-- In any SVD, the entries of `σ` are the leading singular values in some order. -/
theorem exists_equiv_singularValues_eq (h : IsSVD A U σ V) :
    ∃ e : r ≃ Fin (Fintype.card r), ∀ i, σ i = singularValues A (e i) := by
  sorry

/-! ### Splitting into two blocks -/

/-- An SVD whose singular triples are split into two groups writes `A` as a sum of two pieces
with mutually orthogonal factors. This is the form in which Wedin's theorem and the analysis of
truncation consume an SVD. -/
theorem eq_add {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    A = U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ +
      U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ := by
  sorry

/-- The first block of a split SVD is an SVD of its own piece. -/
theorem fromCols_left {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ) U₁ σ₁ V₁ := by
  sorry

/-- The second block of a split SVD is an SVD of its own piece. -/
theorem fromCols_right {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ) U₂ σ₂ V₂ := by
  sorry

end IsSVD

/-! ### Existence -/

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
  sorry

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
  sorry

/-- Every matrix of rank `k` factors as `B * Cᴴ` through `k` columns; more precisely
`A = U * (V * Σ)ᴴ` from the compact SVD. The rank factorisation used when a proof only needs
"`A` has rank at most `k`" in product form. -/
theorem exists_eq_mul_conjTranspose_of_rank_le (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) :
    ∃ (B : Matrix m (Fin k) 𝕜) (C : Matrix n (Fin k) 𝕜), A = B * Cᴴ := by
  sorry

end NLAlib
