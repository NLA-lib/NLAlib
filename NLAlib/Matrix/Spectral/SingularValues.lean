/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Norms.Block
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Singular values

`NLAlib.singularValues A k` is the `k`-th largest singular value of a matrix `A` of any shape,
indexed from `0`, non-increasing, and `0` for `k` at least the rank of `A`. It is Mathlib's
`LinearMap.singularValues` of the map `x ↦ A *ᵥ x` between Euclidean spaces, as a function
`ℕ → ℝ`; `NLAlib.singularValues_eq_linearMap` is the bridge, by `rfl`.

The largest singular value is `singularValues A 0 = specNorm A`. For a matrix with `n` columns,
the smallest singular value is `singularValues A k` with `k + 1 = Fintype.card n`; it is positive
exactly when `A` has full column rank.

## Main definitions

* `NLAlib.singularValues`: the sorted, zero-padded singular values.

## Main results

* `NLAlib.sq_singularValues`: `singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k`, for every `k`.
* `NLAlib.singularValues_pos_iff`: positivity exactly below the rank.
* `NLAlib.singularValues_zero_eq_specNorm`, `NLAlib.frobNorm_sq_eq_sum_singularValues_sq`: the two
  norms in terms of singular values.
* `NLAlib.HasOrthonormalCols.singularValues_mul_left`: invariance under orthonormal factors.
* `NLAlib.le_singularValues_of_forall_mem`, `NLAlib.singularValues_le_of_forall_mem`: the
  variational bounds.
* `NLAlib.exists_submodule_singularValues_mul_norm_le`, `NLAlib.exists_submodule_norm_mulVec_le`:
  the subspaces attaining them.
* `NLAlib.singularValues_last_mul_norm_le`: the smallest singular value bounds `‖A x‖` below.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **singular values** of a matrix, in non-increasing order, indexed from `0` and padded with
zeros: `singularValues A k = 0` for `k ≥ rank A`. This is Mathlib's `LinearMap.singularValues` of
the map `x ↦ A *ᵥ x` from `EuclideanSpace 𝕜 n` to `EuclideanSpace 𝕜 m`, as a function.
[HornJohnson2013, §2.6]. -/
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ :=
  ⇑(LinearMap.singularValues
    ((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap))

/-- **Bridge to Mathlib.** `singularValues A` is `LinearMap.singularValues` of
`Matrix.toEuclideanLin A`. Port of `NLAlib.singularValues_eq_linearMap`. -/
theorem singularValues_eq_linearMap [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValues A = ⇑(Matrix.toEuclideanLin A).singularValues :=
  rfl

/-! ### Basic properties -/

/-- Singular values are nonnegative. -/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularValues A k :=
  LinearMap.singularValues_nonneg _ k

/-- Singular values are non-increasing. -/
theorem singularValues_antitone (A : Matrix m n 𝕜) : Antitone (singularValues A) :=
  fun _ _ h => LinearMap.singularValues_antitone _ h

/-- Sorted eigenvalues of a symmetric operator do not depend on how the operator is spelled. -/
private theorem eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T₁ T₂ : E →ₗ[𝕜] E} (h : T₁ = T₂) (h₁ : T₁.IsSymmetric)
    (h₂ : T₂.IsSymmetric) {d : ℕ} (hd : Module.finrank 𝕜 E = d) (i : Fin d) :
    h₁.eigenvalues hd i = h₂.eigenvalues hd i := by
  subst h
  rfl

/-- **Singular values are the square roots of the eigenvalues of the Gram matrix**, for every
index: both sequences are zero-padded. [HornJohnson2013, §2.6].
Port of `NLAlib.sq_singularValues_eq_eigenvalues₀`. -/
theorem sq_singularValues (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k := by
  classical
  by_cases hk : k < Fintype.card n
  · have heq : LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A =
        Matrix.toEuclideanLin (Aᴴ * A) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    have hG : eigenvalue (Aᴴ * A) k =
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ ⟨k, hk⟩ :=
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_eq_eigenvalues₀ ⟨k, hk⟩
    rw [hG, singularValues_eq_linearMap,
      (Matrix.toEuclideanLin A).sq_singularValues_of_lt finrank_euclideanSpace hk]
    exact eigenvalues_congr heq _ _ finrank_euclideanSpace ⟨k, hk⟩
  · have hk' : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) ≤ k := by
      rw [finrank_euclideanSpace]
      exact not_lt.mp hk
    rw [eigenvalue_of_card_le _ (not_lt.mp hk), singularValues_eq_linearMap,
      LinearMap.singularValues_of_finrank_le _ hk', zero_pow two_ne_zero]

open Polynomial in
/-- The characteristic polynomial of a Hermitian matrix, padded with a power of `X`, is the
product of the linear factors of its zero-padded eigenvalue sequence. -/
private theorem X_pow_mul_charpoly_eq_prod_range [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (d : ℕ) :
    X ^ d * A.charpoly =
      ∏ k ∈ Finset.range (Fintype.card n + d), (X - C ((eigenvalue A k : ℝ) : 𝕜)) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  have h0 : ∏ k ∈ Finset.range d, (X - C ((eigenvalue A (Fintype.card n + k) : ℝ) : 𝕜)) =
      X ^ d := by
    rw [Finset.prod_congr rfl fun k _ => by
      rw [eigenvalue_of_card_le A (Nat.le_add_right _ k), RCLike.ofReal_zero, map_zero,
        sub_zero], Finset.prod_const, Finset.card_range]
  rw [Finset.prod_range_add, h0, mul_comm, hA.charpoly_eq,
    ← Fin.prod_univ_eq_prod_range fun k => X - C ((eigenvalue A k : ℝ) : 𝕜), ← e.prod_comp]
  simp only [he]

/-- Two antitone real sequences with the same first `N` values up to order agree on the first
`N` indices. -/
private theorem eq_of_map_range_eq {f g : ℕ → ℝ} (hf : Antitone f) (hg : Antitone g) {N : ℕ}
    (h : (Multiset.range N).map f = (Multiset.range N).map g) {k : ℕ} (hk : k < N) :
    f k = g k := by
  have hs : ∀ {f : ℕ → ℝ}, Antitone f → ((List.range N).map f).Pairwise (· ≥ ·) := fun hf =>
    List.pairwise_map.mpr (List.pairwise_lt_range.imp fun hab => hf hab.le)
  have hp : ((List.range N).map f).Perm ((List.range N).map g) := Multiset.coe_eq_coe.mp h
  exact List.map_inj_left.mp
    (hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₂ h₁) (hs hf) (hs hg)) k
    (List.mem_range.mpr hk)

open Polynomial in
/-- Positive semidefinite matrices, possibly of different sizes, whose characteristic
polynomials agree up to a power of `X` have the same zero-padded eigenvalue sequence. -/
private theorem eigenvalue_eq_of_X_pow_mul_charpoly_eq [DecidableEq m] [DecidableEq n]
    {P : Matrix n n 𝕜} {Q : Matrix m m 𝕜} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (h : X ^ Fintype.card m * P.charpoly = X ^ Fintype.card n * Q.charpoly) (k : ℕ) :
    eigenvalue P k = eigenvalue Q k := by
  by_cases hk : k < Fintype.card n + Fintype.card m
  · have hr : ∀ f : ℕ → ℝ, ((∏ k ∈ Finset.range (Fintype.card n + Fintype.card m),
        (X - C ((f k : ℝ) : 𝕜))).roots.map RCLike.re) =
          (Multiset.range (Fintype.card n + Fintype.card m)).map f := fun f => by
      rw [Polynomial.roots_prod _ _ (by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
      simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
        Function.comp_def, RCLike.ofReal_re, Finset.range_val]
    rw [X_pow_mul_charpoly_eq_prod_range hP.isHermitian,
      X_pow_mul_charpoly_eq_prod_range hQ.isHermitian, add_comm (Fintype.card m)] at h
    have h2 := congrArg (fun p : 𝕜[X] => p.roots.map RCLike.re) h
    simp only [hr] at h2
    exact eq_of_map_range_eq hP.eigenvalue_antitone hQ.eigenvalue_antitone h2 hk
  · rw [eigenvalue_of_card_le _ (by omega), eigenvalue_of_card_le _ (by omega)]

/-- The same with the other Gram matrix: `singularValues A k ^ 2 = eigenvalue (A * Aᴴ) k`. -/
theorem sq_singularValues_eq_eigenvalue_mul_conjTranspose_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (A * Aᴴ) k := by
  classical
  rw [sq_singularValues]
  exact eigenvalue_eq_of_X_pow_mul_charpoly_eq (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.posSemidef_self_mul_conjTranspose A) (Matrix.charpoly_mul_comm' A Aᴴ).symm k

/-- The Gram determinant is the product of the squared singular values, as many as the matrix
has columns: `det (Aᴴ * A) = ∏ i < card n, σ_i(A) ^ 2`. [HornJohnson2013, Section 7.3]. -/
theorem det_conjTranspose_mul_self_eq_prod_sq_singularValues [DecidableEq n] (A : Matrix m n 𝕜) :
    (Aᴴ * A).det =
      ((∏ i ∈ Finset.range (Fintype.card n), singularValues A i ^ 2 : ℝ) : 𝕜) := by
  rw [(Matrix.isHermitian_conjTranspose_mul_self A).det_eq_prod_range_eigenvalue]
  simp only [sq_singularValues]

/-- A singular value is positive exactly when its index is below the rank.
Port of `NLAlib.singularValues_pos_iff`. -/
theorem singularValues_pos_iff (A : Matrix m n 𝕜) {k : ℕ} :
    0 < singularValues A k ↔ k < A.rank := by
  classical
  rw [singularValues_eq_linearMap, LinearMap.singularValues_pos_iff_lt_finrank_range,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]

/-- A singular value vanishes exactly when its index is at least the rank. -/
theorem singularValues_eq_zero_iff (A : Matrix m n 𝕜) {k : ℕ} :
    singularValues A k = 0 ↔ A.rank ≤ k := by
  rw [← not_lt, ← singularValues_pos_iff, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (singularValues_nonneg A k)⟩

/-- Singular values vanish from the number of rows on. -/
theorem singularValues_of_card_rows_le (A : Matrix m n 𝕜) {k : ℕ} (hk : Fintype.card m ≤ k) :
    singularValues A k = 0 :=
  (singularValues_eq_zero_iff A).mpr (A.rank_le_card_height.trans hk)

/-- Singular values vanish from the number of columns on. -/
theorem singularValues_of_card_cols_le (A : Matrix m n 𝕜) {k : ℕ} (hk : Fintype.card n ≤ k) :
    singularValues A k = 0 :=
  (singularValues_eq_zero_iff A).mpr (A.rank_le_card_width.trans hk)

/-- The singular values of the zero matrix are zero. -/
@[simp]
theorem singularValues_zero : singularValues (0 : Matrix m n 𝕜) = 0 := by
  funext k
  exact (singularValues_eq_zero_iff 0).mpr (by rw [Matrix.rank_zero]; exact Nat.zero_le k)

/-- Only the zero matrix has all singular values zero. -/
theorem singularValues_eq_zero {A : Matrix m n 𝕜} : singularValues A = 0 ↔ A = 0 := by
  classical
  rw [singularValues_eq_linearMap, Finsupp.coe_eq_zero, LinearMap.singularValues_eq_zero_iff,
    LinearEquiv.map_eq_zero_iff]

/-! ### Norms -/

/-- **The largest singular value is the spectral norm.**
Port of `NLAlib.singularValues_zero_eq_specNorm`. -/
theorem singularValues_zero_eq_specNorm (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A := by
  refine (sq_eq_sq₀ (singularValues_nonneg A 0) (specNorm_nonneg A)).mp ?_
  rw [sq_singularValues, ← specNorm_conjTranspose_mul_self,
    (Matrix.posSemidef_conjTranspose_mul_self A).specNorm_eq_eigenvalue_zero]

/-- Every singular value is at most the spectral norm. -/
theorem singularValues_le_specNorm (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≤ specNorm A :=
  (singularValues_antitone A (Nat.zero_le k)).trans_eq (singularValues_zero_eq_specNorm A)

/-- **The squared Frobenius norm is the sum of the squared singular values.** The sum may be
taken over any range that reaches the rank; this is the form over the number of columns.
[HornJohnson2013, §2.6]. Port of `NLAlib.frobSq_eq_sum_sq_singularValues`. -/
theorem frobNorm_sq_eq_sum_singularValues_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range (Fintype.card n), singularValues A k ^ 2 := by
  rw [frobNorm_sq_eq_re_trace,
    (Matrix.isHermitian_conjTranspose_mul_self A).re_trace_eq_sum_range_eigenvalue]
  exact Finset.sum_congr rfl fun k _ => (sq_singularValues A k).symm

/-- A sum of squared singular values over a range that reaches the rank is the sum up to the
rank. -/
private theorem sum_range_singularValues_sq (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    ∑ k ∈ Finset.range N, singularValues A k ^ 2 =
      ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2 := by
  refine (Finset.sum_subset (Finset.range_mono hN) fun k _ hk => ?_).symm
  rw [(singularValues_eq_zero_iff A).mpr (not_lt.mp fun h => hk (Finset.mem_range.mpr h)),
    zero_pow two_ne_zero]

/-- The squared Frobenius norm is the sum of the squared singular values up to any index that
reaches the rank. Port of `NLAlib.frobSq_eq_sum_rank_singularValues_sq`. -/
theorem frobNorm_sq_eq_sum_range_singularValues_sq (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range N, singularValues A k ^ 2 := by
  rw [frobNorm_sq_eq_sum_singularValues_sq, sum_range_singularValues_sq A A.rank_le_card_width,
    sum_range_singularValues_sq A hN]

/-- The squared Frobenius norm is at most the rank times the squared spectral norm.
Port of `NLAlib.frobSq_le_rank_mul_specNorm_sq`. -/
theorem frobNorm_sq_le_rank_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ A.rank * specNorm A ^ 2 := by
  rw [frobNorm_sq_eq_sum_range_singularValues_sq A le_rfl]
  calc ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2
      ≤ ∑ _k ∈ Finset.range A.rank, specNorm A ^ 2 := Finset.sum_le_sum fun k _ =>
        pow_le_pow_left₀ (singularValues_nonneg A k) (singularValues_le_specNorm A k) 2
    _ = A.rank * specNorm A ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The Frobenius norm is at most `√(rank A)` times the spectral norm.
[GolubVanLoan2013, (2.3.7)]. Port of `NLAlib.frobNorm_le_sqrt_rank_mul_specNorm`. -/
theorem frobNorm_le_sqrt_rank_mul_specNorm (A : Matrix m n 𝕜) :
    frobNorm A ≤ √(A.rank : ℝ) * specNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg A))).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact frobNorm_sq_le_rank_mul_specNorm_sq A

/-! ### Transformations -/

/-- The conjugate transpose has the same singular values.
Port of `NLAlib.singularValues_conjTranspose`. -/
@[simp]
theorem singularValues_conjTranspose (A : Matrix m n 𝕜) :
    singularValues Aᴴ = singularValues A := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  rw [sq_singularValues, Matrix.conjTranspose_conjTranspose,
    sq_singularValues_eq_eigenvalue_mul_conjTranspose_self]

/-- The transpose has the same singular values. -/
@[simp]
theorem singularValues_transpose (A : Matrix m n 𝕜) : singularValues Aᵀ = singularValues A := by
  classical
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  have hT : Aᵀᴴ * Aᵀ = (A * Aᴴ)ᵀ := by
    rw [Matrix.transpose_mul]
    rfl
  rw [sq_singularValues, sq_singularValues_eq_eigenvalue_mul_conjTranspose_self, hT]
  exact eigenvalue_eq_of_X_pow_mul_charpoly_eq
    (Matrix.posSemidef_self_mul_conjTranspose A).transpose
    (Matrix.posSemidef_self_mul_conjTranspose A) (by rw [Matrix.charpoly_transpose]) k

/-- Scaling a matrix scales its singular values by the modulus of the scalar. -/
theorem singularValues_smul (c : 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = ‖c‖ * singularValues A k := by
  refine (sq_eq_sq₀ (singularValues_nonneg _ k)
    (mul_nonneg (norm_nonneg c) (singularValues_nonneg A k))).mp ?_
  have hG : (c • A)ᴴ * (c • A) = (‖c‖ ^ 2) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def,
      RCLike.conj_mul, RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_pow]
  rw [sq_singularValues, hG,
    eigenvalue_real_smul _ (sq_nonneg _), mul_pow,
    sq_singularValues]

/-- Scaling a matrix by a real number scales its singular values by the absolute value.
Port of `NLAlib.singularValues_smul`, there over `ℝ`. -/
theorem singularValues_real_smul (c : ℝ) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = |c| * singularValues A k := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), singularValues_smul, RCLike.norm_ofReal]

/-- Negation does not change the singular values. -/
@[simp]
theorem singularValues_neg (A : Matrix m n 𝕜) : singularValues (-A) = singularValues A := by
  funext k
  rw [← neg_one_smul 𝕜 A, singularValues_smul, norm_neg, norm_one, one_mul]

/-- Relabelling rows and columns by bijections does not change the singular values.
Port of `NLAlib.singularValues_reindex`. -/
@[simp]
theorem singularValues_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    singularValues (A.submatrix e₁ e₂) = singularValues A := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  rw [sq_singularValues, sq_singularValues, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, eigenvalue_submatrix_equiv]

/-- Matrices with the same Gram matrix have the same singular values, whatever their numbers of
rows. Port of `NLAlib.singularValues_eq_of_gram_eq`. -/
theorem singularValues_eq_of_conjTranspose_mul_self_eq {A : Matrix m n 𝕜} {B : Matrix l n 𝕜}
    (h : Aᴴ * A = Bᴴ * B) : singularValues A = singularValues B := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg A k) (singularValues_nonneg B k)).mp ?_
  rw [sq_singularValues, sq_singularValues, h]

/-- Left multiplication by a matrix with orthonormal columns preserves the singular values.
Port of `NLAlib.singularValues_isometry_mul`. -/
theorem HasOrthonormalCols.singularValues_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (Q * A) = singularValues A :=
  singularValues_eq_of_conjTranspose_mul_self_eq (hQ.conjTranspose_mul_mul A A)

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the singular values. Port of `NLAlib.singularValues_mul_isometry_conjTranspose`. -/
theorem HasOrthonormalCols.singularValues_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (A * Qᴴ) = singularValues A := by
  rw [← singularValues_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.singularValues_mul_left,
    singularValues_conjTranspose]

/-! ### Variational bounds -/

/-- The quadratic form of the Gram matrix is the squared norm of the image. -/
private theorem re_quadForm_conjTranspose_mul_self (A : Matrix m n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (Aᴴ * A) x) = ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  rw [quadForm_conjTranspose_mul_self, RCLike.ofReal_re]

/-- **Courant–Fischer for singular values, lower bound.** If `c * ‖x‖ ≤ ‖A x‖` on a subspace of
dimension at least `k + 1`, then `c ≤ singularValues A k`.
[HornJohnson2013, Theorem 7.3.8].
Port of `NLAlib.le_singularValues_of_forall_mem`, there with squared norms as dot products. -/
theorem le_singularValues_of_forall_mem (A : Matrix m n 𝕜) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜))
    (hS : k + 1 ≤ Module.finrank 𝕜 S) {c : ℝ}
    (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) :
    c ≤ singularValues A k := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (singularValues_nonneg A k)
  · have h2 : c ^ 2 ≤ eigenvalue (Aᴴ * A) k :=
      (Matrix.isHermitian_conjTranspose_mul_self A).le_eigenvalue_of_forall_mem S hS
        fun x hx => by
          rw [re_quadForm_conjTranspose_mul_self, ← mul_pow]
          exact pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) (h x hx) 2
    rw [← sq_singularValues] at h2
    exact (pow_le_pow_iff_left₀ hc.le (singularValues_nonneg A k) two_ne_zero).mp h2

/-- **Courant–Fischer for singular values, upper bound.** If `‖A x‖ ≤ c * ‖x‖` on a subspace of
codimension at most `k`, with `0 ≤ c`, then `singularValues A k ≤ c`.
[HornJohnson2013, Theorem 7.3.8].
Port of `NLAlib.singularValues_le_of_forall_mem`. -/
theorem singularValues_le_of_forall_mem (A : Matrix m n 𝕜) {k : ℕ} (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ W, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖) :
    singularValues A k ≤ c := by
  by_cases hk : k < Fintype.card n
  · have h2 : eigenvalue (Aᴴ * A) k ≤ c ^ 2 :=
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_le_of_forall_mem hk W hW
        fun x hx => by
          rw [re_quadForm_conjTranspose_mul_self, ← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (h x hx) 2
    rw [← sq_singularValues] at h2
    exact (pow_le_pow_iff_left₀ (singularValues_nonneg A k) hc two_ne_zero).mp h2
  · rw [singularValues_of_card_cols_le A (not_lt.mp hk)]
    exact hc

/-- **Courant–Fischer for singular values, existence of the extremal subspace.** For every `k`
there is a subspace of codimension at most `k` on which `‖A x‖ ≤ singularValues A k * ‖x‖`. This
is the existence half of the variational upper bound `NLAlib.singularValues_le_of_forall_mem`:
intersecting such subspaces is how inequalities between singular values of different matrices
are proved. [HornJohnson2013, Theorem 7.3.8]. -/
theorem exists_submodule_norm_mulVec_le (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Fintype.card n ≤ Module.finrank 𝕜 W + k ∧
      ∀ x ∈ W, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ singularValues A k * ‖WithLp.toLp 2 x‖ := by
  by_cases hk : k < Fintype.card n
  · obtain ⟨W, hW, h⟩ :=
      (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_le_eigenvalue_mul hk
    refine ⟨W, hW.ge, fun x hx => ?_⟩
    have h2 := h x hx
    rw [re_quadForm_conjTranspose_mul_self, ← sq_singularValues, ← mul_pow] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _)) two_ne_zero).mp h2
  · refine ⟨⊥, by rw [finrank_bot]; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot 𝕜).mp hx, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero]
    exact mul_nonneg (singularValues_nonneg A k) (norm_nonneg _)

/-- **Courant–Fischer for singular values, existence of the leading subspace.** For `k` below the
number of columns there is a subspace of dimension `k + 1` on which
`singularValues A k * ‖x‖ ≤ ‖A x‖` (the span of the first `k + 1` right singular vectors). This
is the existence half of the variational lower bound `NLAlib.le_singularValues_of_forall_mem`.
[HornJohnson2013, Theorem 7.3.8]. -/
theorem exists_submodule_singularValues_mul_norm_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = k + 1 ∧
      ∀ x ∈ S, singularValues A k * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  obtain ⟨S, hS, h⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_eigenvalue_mul_le hk
  refine ⟨S, hS, fun x hx => ?_⟩
  have h2 := h x hx
  rw [← sq_singularValues, re_quadForm_conjTranspose_mul_self, ← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp h2

/-! ### The smallest singular value -/

/-- **The smallest singular value bounds `‖A x‖` from below.** For a matrix with `n` columns and
`k + 1 = Fintype.card n`, `singularValues A k * ‖x‖ ≤ ‖A x‖`.
Port of `NLAlib.singularValues_last_mul_norm_le`. -/
theorem singularValues_last_mul_norm_le (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (x : n → 𝕜) : singularValues A k * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have h2 := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_last_mul_le_re_quadForm hk x
  rw [← sq_singularValues, re_quadForm_conjTranspose_mul_self, ← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp h2

/-- A lower bound `c * ‖x‖ ≤ ‖A x‖` for all `x` is a lower bound on the smallest singular value.
Port of `NLAlib.le_singularValues_last`. -/
theorem le_singularValues_last (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ}
    (h : ∀ x, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) : c ≤ singularValues A k := by
  refine le_singularValues_of_forall_mem A ⊤ ?_ fun x _ => h x
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, hk]

/-- The smallest singular value in the Loewner order: `σ_min(A) ^ 2 • 1 ≤ Aᴴ * A`. -/
theorem sq_singularValues_last_smul_one_le [DecidableEq n] (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    (singularValues A k ^ 2) • (1 : Matrix n n 𝕜) ≤ Aᴴ * A := by
  rw [sq_singularValues]
  exact (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_last_smul_one_le hk

/-- A lower Loewner bound on the Gram matrix is a lower bound on the smallest singular value.
This is how a subspace embedding bounds `σ_min`. -/
theorem le_sq_singularValues_last_of_smul_one_le [DecidableEq n] {A : Matrix m n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) {a : ℝ} (h : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) :
    a ≤ singularValues A k ^ 2 := by
  rw [sq_singularValues]
  exact ((Matrix.isHermitian_conjTranspose_mul_self A).smul_one_le_iff hk).mp h

/-- The smallest singular value is positive exactly when the matrix has full column rank.
Port of `NLAlib.singularValues_last_pos_iff_rank_eq_card`. -/
theorem singularValues_last_pos_iff_injective (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : 0 < singularValues A k ↔ Function.Injective A.mulVec := by
  rw [singularValues_pos_iff, mulVec_injective_iff_rank_eq]
  have := A.rank_le_card_width
  omega

/-! ### Positive semidefinite matrices -/

/-- The singular values of a positive semidefinite matrix are its eigenvalues. -/
theorem _root_.Matrix.PosSemidef.singularValues_eq_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : singularValues A = eigenvalue A := by
  classical
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg A k) (hA.eigenvalue_nonneg k)).mp ?_
  rw [sq_singularValues, hA.isHermitian.eq]
  by_cases hk : k < Fintype.card n
  · obtain ⟨U, hU, hAU⟩ := hA.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
    have hμ : Antitone fun i : Fin (Fintype.card n) => eigenvalue A i ^ 2 := fun a b hab =>
      pow_le_pow_left₀ (hA.eigenvalue_nonneg b) (hA.eigenvalue_antitone hab) 2
    refine eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hμ ?_ ⟨k, hk⟩
    conv_lhs => rw [hAU]
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
    rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    simp only [← sq, RCLike.ofReal_pow]
  · rw [eigenvalue_of_card_le _ (not_lt.mp hk), eigenvalue_of_card_le _ (not_lt.mp hk),
      zero_pow two_ne_zero]

end NLAlib
