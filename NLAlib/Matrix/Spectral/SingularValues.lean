/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Tactic.Positivity.Core
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Norms.Block
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Singular values

`NLAlib.singularValues A k` is $\sigma_k(\mathbf{A})$, the $k$-th largest singular value of a
matrix $\mathbf{A}$ of any shape, indexed from $0$, non-increasing, and $0$ for $k$ at least the
rank of $\mathbf{A}$. It is Mathlib's `LinearMap.singularValues` of the map
$\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ between Euclidean spaces, as a function `ℕ → ℝ`;
`NLAlib.singularValues_eq_linearMap` is the bridge, by `rfl`.

The largest singular value is $\sigma_0(\mathbf{A}) = \|\mathbf{A}\|_2$. For a matrix with columns
indexed by $n$, the smallest singular value is $\sigma_k(\mathbf{A})$ with $k + 1 = \lvert n
\rvert$; it is positive exactly when $\mathbf{A}$ has full column rank. The zeros beyond the rank
are padding, so an index quantified by `∃`, or by `∀` in a hypothesis, needs a range:
`∃ k, singularValues A k < 1` holds for every matrix. See the module docstring of
`NLAlib/Matrix/Spectral/Eigenvalues.lean`.

## Main definitions

* `NLAlib.singularValues`: the sorted, zero-padded singular values.

## Main results

* `NLAlib.singularValues_sq`:
  $\sigma_k(\mathbf{A})^2 = \lambda_k(\mathbf{A}^{\mathsf{H}}\mathbf{A})$, for every $k$.
* `NLAlib.singularValues_pos_iff`: positivity exactly below the rank.
* `NLAlib.singularValues_zero_eq_specNorm`, `NLAlib.frobNorm_sq_eq_sum_singularValues_sq`: the two
  norms in terms of singular values.
* `NLAlib.HasOrthonormalCols.singularValues_mul_left`: invariance under orthonormal factors.
* `NLAlib.le_singularValues_of_forall_mem`, `NLAlib.singularValues_le_of_forall_mem`: the
  variational bounds.
* `NLAlib.exists_submodule_singularValues_mul_norm_le`, `NLAlib.exists_submodule_norm_mulVec_le`:
  the subspaces attaining them.
* `NLAlib.singularValues_last_mul_norm_le`: the smallest singular value bounds
  $\|\mathbf{A}\mathbf{x}\|$ below.
* `NLAlib.singularValues_conjTranspose_mul_self`, `NLAlib.singularValues_mul_conjTranspose_self`:
  the singular values of a Gram matrix are the squared singular values.
* `NLAlib.HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose`: a frame conjugation of a positive
  semidefinite matrix keeps its eigenvalue sequence.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **singular values** $\sigma_k(\mathbf{A})$ of a matrix, in non-increasing order, indexed
from $0$ and padded with zeros: $\sigma_k(\mathbf{A}) = 0$ for $k \ge \operatorname{rank}
\mathbf{A}$. This is Mathlib's `LinearMap.singularValues` of the map
$\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ from `EuclideanSpace 𝕜 n` to `EuclideanSpace 𝕜 m`, as a
function.
[HornJohnson2013, §2.6]. -/
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ :=
  ⇑(LinearMap.singularValues
    ((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap))

/-- Bridge to Mathlib. `singularValues A` is `LinearMap.singularValues` of
`Matrix.toEuclideanLin A`. -/
theorem singularValues_eq_linearMap [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValues A = ⇑(Matrix.toEuclideanLin A).singularValues :=
  rfl

/-! ### Basic properties -/

/-- Singular values are nonnegative: $0 \le \sigma_k(\mathbf{A})$. -/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularValues A k :=
  LinearMap.singularValues_nonneg _ k

/-- Singular values are non-increasing in the index. -/
theorem singularValues_antitone (A : Matrix m n 𝕜) : Antitone (singularValues A) :=
  fun _ _ h => LinearMap.singularValues_antitone _ h

/-- Sorted eigenvalues of a symmetric operator do not depend on how the operator is spelled. -/
private theorem eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T₁ T₂ : E →ₗ[𝕜] E} (h : T₁ = T₂) (h₁ : T₁.IsSymmetric)
    (h₂ : T₂.IsSymmetric) {d : ℕ} (hd : Module.finrank 𝕜 E = d) (i : Fin d) :
    h₁.eigenvalues hd i = h₂.eigenvalues hd i := by
  subst h
  rfl

/-- **Singular values are the square roots of the eigenvalues of the Gram matrix**:
$\sigma_k(\mathbf{A})^2 = \lambda_k(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ for every index $k$, both
sequences being zero-padded. [HornJohnson2013, §2.6]. -/
theorem singularValues_sq (A : Matrix m n 𝕜) (k : ℕ) :
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
/-- The characteristic polynomial of a Hermitian matrix, padded with a power of $X$, is the
product of the linear factors of its zero-padded eigenvalue sequence:
$X^d \det(X\mathbf{I} - \mathbf{A}) = \prod_{k < \lvert n \rvert + d} (X - \lambda_k(\mathbf{A}))$.
-/
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

/-- Two antitone real sequences with the same first $N$ values up to order agree on the first
$N$ indices. -/
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
polynomials agree up to a power of $X$ have the same zero-padded eigenvalue sequence. -/
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

/-- The same with the other Gram matrix:
$\sigma_k(\mathbf{A})^2 = \lambda_k(\mathbf{A}\mathbf{A}^{\mathsf{H}})$ for every $k$. -/
theorem singularValues_sq_eq_eigenvalue_mul_conjTranspose_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (A * Aᴴ) k := by
  classical
  rw [singularValues_sq]
  exact eigenvalue_eq_of_X_pow_mul_charpoly_eq (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.posSemidef_self_mul_conjTranspose A) (Matrix.charpoly_mul_comm' A Aᴴ).symm k

/-- Eigenvalues under a frame conjugation: for $\mathbf{U}$ with orthonormal columns and a
positive semidefinite $\mathbf{T}$ on its column index,
$\lambda_k(\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}) = \lambda_k(\mathbf{T})$ for every
$k$: the conjugation only adds zero eigenvalues, which sort below those of $\mathbf{T}$. It links
the projector form $\mathbf{P}\mathbf{A}\mathbf{P}$ of Ritz values to the frame form
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$, with
$\mathbf{P} = \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$. -/
theorem HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose [DecidableEq m] {U : Matrix n m 𝕜}
    (hU : HasOrthonormalCols U) {T : Matrix m m 𝕜} (hT : T.PosSemidef) (k : ℕ) :
    eigenvalue (U * T * Uᴴ) k = eigenvalue T k := by
  classical
  refine eigenvalue_eq_of_X_pow_mul_charpoly_eq (hT.mul_mul_conjTranspose_same U) hT ?_ k
  have h := Matrix.charpoly_mul_comm' U (T * Uᴴ)
  rwa [← Matrix.mul_assoc, Matrix.mul_assoc T, hU.conjTranspose_mul_self, Matrix.mul_one] at h

/-- The Gram determinant is the product of the squared singular values, as many as the matrix
has columns: $\det(\mathbf{A}^{\mathsf{H}}\mathbf{A}) = \prod_{i < \lvert n \rvert}
\sigma_i(\mathbf{A})^2$. [HornJohnson2013, Section 7.3]. -/
theorem det_conjTranspose_mul_self_eq_prod_singularValues_sq [DecidableEq n] (A : Matrix m n 𝕜) :
    (Aᴴ * A).det =
      ((∏ i ∈ Finset.range (Fintype.card n), singularValues A i ^ 2 : ℝ) : 𝕜) := by
  rw [(Matrix.isHermitian_conjTranspose_mul_self A).det_eq_prod_range_eigenvalue]
  simp only [singularValues_sq]

/-- A singular value is positive exactly when its index is below the rank:
$0 < \sigma_k(\mathbf{A}) \iff k < \operatorname{rank} \mathbf{A}$. -/
theorem singularValues_pos_iff (A : Matrix m n 𝕜) {k : ℕ} :
    0 < singularValues A k ↔ k < A.rank := by
  classical
  rw [singularValues_eq_linearMap, LinearMap.singularValues_pos_iff_lt_finrank_range,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]

/-- A singular value vanishes exactly when its index is at least the rank:
$\sigma_k(\mathbf{A}) = 0 \iff \operatorname{rank} \mathbf{A} \le k$. -/
theorem singularValues_eq_zero_iff (A : Matrix m n 𝕜) {k : ℕ} :
    singularValues A k = 0 ↔ A.rank ≤ k := by
  rw [← not_lt, ← singularValues_pos_iff, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (singularValues_nonneg A k)⟩

/-- Singular values vanish from the number of rows on: $\sigma_k(\mathbf{A}) = 0$ for
$k \ge \lvert m \rvert$. -/
theorem singularValues_of_card_rows_le (A : Matrix m n 𝕜) {k : ℕ} (hk : Fintype.card m ≤ k) :
    singularValues A k = 0 :=
  (singularValues_eq_zero_iff A).mpr (A.rank_le_card_height.trans hk)

/-- Singular values vanish from the number of columns on: $\sigma_k(\mathbf{A}) = 0$ for
$k \ge \lvert n \rvert$. -/
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

/-- The largest singular value is the spectral norm: $\sigma_0(\mathbf{A}) = \|\mathbf{A}\|_2$. -/
theorem singularValues_zero_eq_specNorm (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A := by
  refine (sq_eq_sq₀ (singularValues_nonneg A 0) (specNorm_nonneg A)).mp ?_
  rw [singularValues_sq, ← specNorm_conjTranspose_mul_self,
    (Matrix.posSemidef_conjTranspose_mul_self A).specNorm_eq_eigenvalue_zero]

/-- Every singular value is at most the spectral norm: $\sigma_k(\mathbf{A}) \le \|\mathbf{A}\|_2$.
-/
theorem singularValues_le_specNorm (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≤ specNorm A :=
  (singularValues_antitone A (Nat.zero_le k)).trans_eq (singularValues_zero_eq_specNorm A)

/-- **The squared Frobenius norm is the sum of the squared singular values**:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \sum_{k < \lvert n \rvert} \sigma_k(\mathbf{A})^2$. The sum may be
taken over any range that reaches the rank; this is the form over the number of columns.
[HornJohnson2013, §2.6]. -/
theorem frobNorm_sq_eq_sum_singularValues_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range (Fintype.card n), singularValues A k ^ 2 := by
  rw [frobNorm_sq_eq_re_trace,
    (Matrix.isHermitian_conjTranspose_mul_self A).re_trace_eq_sum_range_eigenvalue]
  exact Finset.sum_congr rfl fun k _ => (singularValues_sq A k).symm

/-- A sum of squared singular values over a range that reaches the rank is the sum up to the
rank. -/
private theorem sum_range_singularValues_sq (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    ∑ k ∈ Finset.range N, singularValues A k ^ 2 =
      ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2 := by
  refine (Finset.sum_subset (Finset.range_mono hN) fun k _ hk => ?_).symm
  rw [(singularValues_eq_zero_iff A).mpr (not_lt.mp fun h => hk (Finset.mem_range.mpr h)),
    zero_pow two_ne_zero]

/-- The squared Frobenius norm is the sum of the squared singular values up to any index that
reaches the rank: $\|\mathbf{A}\|_{\mathsf{F}}^2 = \sum_{k < N} \sigma_k(\mathbf{A})^2$ for
$\operatorname{rank} \mathbf{A} \le N$. -/
theorem frobNorm_sq_eq_sum_range_singularValues_sq (A : Matrix m n 𝕜) {N : ℕ} (hN : A.rank ≤ N) :
    frobNorm A ^ 2 = ∑ k ∈ Finset.range N, singularValues A k ^ 2 := by
  rw [frobNorm_sq_eq_sum_singularValues_sq, sum_range_singularValues_sq A A.rank_le_card_width,
    sum_range_singularValues_sq A hN]

/-- The squared Frobenius norm is at most the rank times the squared spectral norm:
$\|\mathbf{A}\|_{\mathsf{F}}^2 \le \operatorname{rank} \mathbf{A} \, \|\mathbf{A}\|_2^2$. -/
theorem frobNorm_sq_le_rank_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ A.rank * specNorm A ^ 2 := by
  rw [frobNorm_sq_eq_sum_range_singularValues_sq A le_rfl]
  calc ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2
      ≤ ∑ _k ∈ Finset.range A.rank, specNorm A ^ 2 := Finset.sum_le_sum fun k _ =>
        pow_le_pow_left₀ (singularValues_nonneg A k) (singularValues_le_specNorm A k) 2
    _ = A.rank * specNorm A ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The Frobenius norm is at most $\sqrt{\operatorname{rank} \mathbf{A}}$ times the spectral norm:
$\|\mathbf{A}\|_{\mathsf{F}} \le \sqrt{\operatorname{rank} \mathbf{A}} \, \|\mathbf{A}\|_2$.
[GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_le_sqrt_rank_mul_specNorm (A : Matrix m n 𝕜) :
    frobNorm A ≤ √(A.rank : ℝ) * specNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg A))).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact frobNorm_sq_le_rank_mul_specNorm_sq A

/-! ### Transformations -/

/-- The conjugate transpose has the same singular values:
$\sigma_k(\mathbf{A}^{\mathsf{H}}) = \sigma_k(\mathbf{A})$. -/
@[simp]
theorem singularValues_conjTranspose (A : Matrix m n 𝕜) :
    singularValues Aᴴ = singularValues A := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  rw [singularValues_sq, Matrix.conjTranspose_conjTranspose,
    singularValues_sq_eq_eigenvalue_mul_conjTranspose_self]

/-- The transpose has the same singular values:
$\sigma_k(\mathbf{A}^{\mathsf{T}}) = \sigma_k(\mathbf{A})$. -/
@[simp]
theorem singularValues_transpose (A : Matrix m n 𝕜) : singularValues Aᵀ = singularValues A := by
  classical
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  have hT : Aᵀᴴ * Aᵀ = (A * Aᴴ)ᵀ := by
    rw [Matrix.transpose_mul]
    rfl
  rw [singularValues_sq, singularValues_sq_eq_eigenvalue_mul_conjTranspose_self, hT]
  exact eigenvalue_eq_of_X_pow_mul_charpoly_eq
    (Matrix.posSemidef_self_mul_conjTranspose A).transpose
    (Matrix.posSemidef_self_mul_conjTranspose A) (by rw [Matrix.charpoly_transpose]) k

/-- Scaling a matrix scales its singular values by the modulus of the scalar:
$\sigma_k(c\mathbf{A}) = \lvert c \rvert \, \sigma_k(\mathbf{A})$ for $c \in \Bbbk$. -/
theorem singularValues_smul (c : 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = ‖c‖ * singularValues A k := by
  refine (sq_eq_sq₀ (singularValues_nonneg _ k)
    (mul_nonneg (norm_nonneg c) (singularValues_nonneg A k))).mp ?_
  have hG : (c • A)ᴴ * (c • A) = (‖c‖ ^ 2) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def,
      RCLike.conj_mul, RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_pow]
  rw [singularValues_sq, hG,
    eigenvalue_real_smul _ (sq_nonneg _), mul_pow,
    singularValues_sq]

/-- Scaling a matrix by a real number scales its singular values by the absolute value:
$\sigma_k(c\mathbf{A}) = \lvert c \rvert \, \sigma_k(\mathbf{A})$ for $c \in \mathbb{R}$. -/
theorem singularValues_real_smul (c : ℝ) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (c • A) k = |c| * singularValues A k := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), singularValues_smul, RCLike.norm_ofReal]

/-- Negation does not change the singular values. -/
@[simp]
theorem singularValues_neg (A : Matrix m n 𝕜) : singularValues (-A) = singularValues A := by
  funext k
  rw [← neg_one_smul 𝕜 A, singularValues_smul, norm_neg, norm_one, one_mul]

/-- Relabelling rows and columns by bijections does not change the singular values. -/
@[simp]
theorem singularValues_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    singularValues (A.submatrix e₁ e₂) = singularValues A := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).mp ?_
  rw [singularValues_sq, singularValues_sq, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, eigenvalue_submatrix_equiv]

/-- Matrices with the same Gram matrix have the same singular values, whatever their numbers of
rows: if $\mathbf{A}^{\mathsf{H}}\mathbf{A} = \mathbf{B}^{\mathsf{H}}\mathbf{B}$ then
$\sigma_k(\mathbf{A}) = \sigma_k(\mathbf{B})$ for every $k$. -/
theorem singularValues_eq_of_conjTranspose_mul_self_eq {A : Matrix m n 𝕜} {B : Matrix l n 𝕜}
    (h : Aᴴ * A = Bᴴ * B) : singularValues A = singularValues B := by
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg A k) (singularValues_nonneg B k)).mp ?_
  rw [singularValues_sq, singularValues_sq, h]

/-- Left multiplication by a matrix with orthonormal columns preserves the singular values:
$\sigma_k(\mathbf{Q}\mathbf{A}) = \sigma_k(\mathbf{A})$ when
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$. -/
theorem HasOrthonormalCols.singularValues_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (Q * A) = singularValues A :=
  singularValues_eq_of_conjTranspose_mul_self_eq (hQ.conjTranspose_mul_mul A A)

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the singular values: $\sigma_k(\mathbf{A}\mathbf{Q}^{\mathsf{H}}) = \sigma_k(\mathbf{A})$
when $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$. -/
theorem HasOrthonormalCols.singularValues_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    singularValues (A * Qᴴ) = singularValues A := by
  rw [← singularValues_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.singularValues_mul_left,
    singularValues_conjTranspose]

/-! ### Variational bounds -/

/-- The quadratic form of the Gram matrix is the squared norm of the image:
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{x})
= \|\mathbf{A}\mathbf{x}\|^2$. -/
private theorem re_quadForm_conjTranspose_mul_self (A : Matrix m n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm (Aᴴ * A) x) = ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  rw [quadForm_conjTranspose_mul_self, RCLike.ofReal_re]

/-- **Courant–Fischer for singular values, lower bound.** If
$c \|\mathbf{x}\| \le \|\mathbf{A}\mathbf{x}\|$ for every $\mathbf{x}$ in a subspace of dimension
at least $k + 1$, then $c \le \sigma_k(\mathbf{A})$.
[HornJohnson2013, Theorem 7.3.8]. -/
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
    rw [← singularValues_sq] at h2
    exact (pow_le_pow_iff_left₀ hc.le (singularValues_nonneg A k) two_ne_zero).mp h2

/-- **Courant–Fischer for singular values, upper bound.** If
$\|\mathbf{A}\mathbf{x}\| \le c \|\mathbf{x}\|$ for every $\mathbf{x}$ in a subspace of
codimension at most $k$, with $0 \le c$, then $\sigma_k(\mathbf{A}) \le c$.
[HornJohnson2013, Theorem 7.3.8]. -/
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
    rw [← singularValues_sq] at h2
    exact (pow_le_pow_iff_left₀ (singularValues_nonneg A k) hc two_ne_zero).mp h2
  · rw [singularValues_of_card_cols_le A (not_lt.mp hk)]
    exact hc

/-- **Courant–Fischer for singular values, existence of the extremal subspace.** For every $k$
there is a subspace of codimension at most $k$ on which
$\|\mathbf{A}\mathbf{x}\| \le \sigma_k(\mathbf{A}) \|\mathbf{x}\|$. This is the existence half of
the variational upper bound `NLAlib.singularValues_le_of_forall_mem`: intersecting such subspaces
is how inequalities between singular values of different matrices are proved.
[HornJohnson2013, Theorem 7.3.8]. -/
theorem exists_submodule_norm_mulVec_le (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Fintype.card n ≤ Module.finrank 𝕜 W + k ∧
      ∀ x ∈ W, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ singularValues A k * ‖WithLp.toLp 2 x‖ := by
  by_cases hk : k < Fintype.card n
  · obtain ⟨W, hW, h⟩ :=
      (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_le_eigenvalue_mul hk
    refine ⟨W, hW.ge, fun x hx => ?_⟩
    have h2 := h x hx
    rw [re_quadForm_conjTranspose_mul_self, ← singularValues_sq, ← mul_pow] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _)) two_ne_zero).mp h2
  · refine ⟨⊥, by rw [finrank_bot]; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot 𝕜).mp hx, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero]
    exact mul_nonneg (singularValues_nonneg A k) (norm_nonneg _)

/-- **Courant–Fischer for singular values, existence of the leading subspace.** For
$k < \lvert n \rvert$, the number of columns, there is a subspace of dimension $k + 1$ on which
$\sigma_k(\mathbf{A}) \|\mathbf{x}\| \le \|\mathbf{A}\mathbf{x}\|$ (the span of the first $k + 1$
right singular vectors). This is the existence half of the variational lower bound
`NLAlib.le_singularValues_of_forall_mem`.
[HornJohnson2013, Theorem 7.3.8]. -/
theorem exists_submodule_singularValues_mul_norm_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = k + 1 ∧
      ∀ x ∈ S, singularValues A k * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  obtain ⟨S, hS, h⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_eigenvalue_mul_le hk
  refine ⟨S, hS, fun x hx => ?_⟩
  have h2 := h x hx
  rw [← singularValues_sq, re_quadForm_conjTranspose_mul_self, ← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp h2

/-! ### The smallest singular value -/

/-- The smallest singular value bounds $\|\mathbf{A}\mathbf{x}\|$ from below: for a matrix with
columns indexed by $n$ and $k + 1 = \lvert n \rvert$,
$\sigma_k(\mathbf{A}) \|\mathbf{x}\| \le \|\mathbf{A}\mathbf{x}\|$ for every $\mathbf{x}$. -/
theorem singularValues_last_mul_norm_le (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (x : n → 𝕜) : singularValues A k * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have h2 := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_last_mul_le_re_quadForm hk x
  rw [← singularValues_sq, re_quadForm_conjTranspose_mul_self, ← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (mul_nonneg (singularValues_nonneg A k) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp h2

/-- A lower bound $c \|\mathbf{x}\| \le \|\mathbf{A}\mathbf{x}\|$ for all $\mathbf{x}$ is a lower
bound on the smallest singular value: $c \le \sigma_k(\mathbf{A})$ for $k + 1 = \lvert n \rvert$. -/
theorem le_singularValues_last (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ}
    (h : ∀ x, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) : c ≤ singularValues A k := by
  refine le_singularValues_of_forall_mem A ⊤ ?_ fun x _ => h x
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, hk]

/-- The smallest singular value in the Loewner order:
$\sigma_k(\mathbf{A})^2 \mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$ for
$k + 1 = \lvert n \rvert$. -/
theorem singularValues_last_sq_smul_one_le [DecidableEq n] (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    (singularValues A k ^ 2) • (1 : Matrix n n 𝕜) ≤ Aᴴ * A := by
  rw [singularValues_sq]
  exact (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_last_smul_one_le hk

/-- A lower Loewner bound on the Gram matrix is a lower bound on the smallest singular value: if
$a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$ then $a \le \sigma_k(\mathbf{A})^2$ for
$k + 1 = \lvert n \rvert$. This is how a subspace embedding bounds $\sigma_{\min}$. -/
theorem le_singularValues_last_sq_of_smul_one_le [DecidableEq n] {A : Matrix m n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) {a : ℝ} (h : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) :
    a ≤ singularValues A k ^ 2 := by
  rw [singularValues_sq]
  exact ((Matrix.isHermitian_conjTranspose_mul_self A).smul_one_le_iff hk).mp h

/-- The smallest singular value $\sigma_k(\mathbf{A})$, $k + 1 = \lvert n \rvert$, is positive
exactly when $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective, that is, when the matrix has
full column rank. -/
theorem singularValues_last_pos_iff_injective (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : 0 < singularValues A k ↔ Function.Injective A.mulVec := by
  rw [singularValues_pos_iff, mulVec_injective_iff_rank_eq]
  have := A.rank_le_card_width
  omega

/-! ### Positive semidefinite matrices -/

/-- The singular values of a positive semidefinite matrix are its eigenvalues:
$\sigma_k(\mathbf{A}) = \lambda_k(\mathbf{A})$ for every $k$. -/
theorem _root_.Matrix.PosSemidef.singularValues_eq_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : singularValues A = eigenvalue A := by
  classical
  funext k
  refine (sq_eq_sq₀ (singularValues_nonneg A k) (hA.eigenvalue_nonneg k)).mp ?_
  rw [singularValues_sq, hA.isHermitian.eq]
  by_cases hk : k < Fintype.card n
  · obtain ⟨U, hU, hAU⟩ := hA.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
    have hμ : Antitone fun i : Fin (Fintype.card n) => eigenvalue A i ^ 2 := fun a b hab =>
      pow_le_pow_left₀ (hA.eigenvalue_nonneg b) (hA.eigenvalue_antitone hab) 2
    refine HasOrthonormalCols.eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hμ ?_
      ⟨k, hk⟩
    conv_lhs => rw [hAU]
    simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
    rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    simp only [← sq, RCLike.ofReal_pow]
  · rw [eigenvalue_of_card_le _ (not_lt.mp hk), eigenvalue_of_card_le _ (not_lt.mp hk),
      zero_pow two_ne_zero]

/-- The singular values of the Gram matrix are the squared singular values:
$\sigma_k(\mathbf{A}^{\mathsf{H}}\mathbf{A}) = \sigma_k(\mathbf{A})^2$ for every index $k$,
the zero padding included. Mathlib's `LinearMap.singularValues` has no such statement. -/
theorem singularValues_conjTranspose_mul_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (Aᴴ * A) k = singularValues A k ^ 2 := by
  rw [(Matrix.posSemidef_conjTranspose_mul_self A).singularValues_eq_eigenvalue,
    singularValues_sq]

/-- The same for the other Gram matrix:
$\sigma_k(\mathbf{A}\mathbf{A}^{\mathsf{H}}) = \sigma_k(\mathbf{A})^2$ for every index $k$. -/
theorem singularValues_mul_conjTranspose_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (A * Aᴴ) k = singularValues A k ^ 2 := by
  rw [(Matrix.posSemidef_self_mul_conjTranspose A).singularValues_eq_eigenvalue,
    singularValues_sq_eq_eigenvalue_mul_conjTranspose_self]

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Recognize the nonnegativity of every matrix singular value, including padded indices. -/
@[positivity NLAlib.singularValues _ _]
meta def evalSingularValues : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    match (← whnfR e).getAppFnArgs with
    | (``NLAlib.singularValues, #[_, _, _, _, _, _, A, k]) =>
      pure (.nonnegative (← mkAppM ``NLAlib.singularValues_nonneg #[A, k]))
    | _ => failure

end Mathlib.Meta.Positivity
