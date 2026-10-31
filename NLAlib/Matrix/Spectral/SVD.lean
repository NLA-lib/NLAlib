/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.ConjTranspose
public import NLAlib.ForMathlib.Topology.Algebra.Module.FiniteDimension
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Subspaces.Frames

/-!
# The singular value decomposition

`NLAlib.IsSVD A U σ V` says that
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ with
$\mathbf{U}$ and $\mathbf{V}$ having orthonormal columns and $\boldsymbol{\sigma}$ nonnegative. The
columns are indexed by an arbitrary finite type $r$, so the predicate covers the compact SVD, the
thin SVD and partial decompositions, and with $r$ a sum type and `Matrix.fromCols` it expresses
the splitting of $\mathbf{A}$ into two blocks of singular triples. The factors need not be square
and no rectangular diagonal matrix appears. A full SVD with unitary factors is obtained from a
thin one by orthonormal completion (`NLAlib.HasOrthonormalCols.exists_fromCols`).

$\boldsymbol{\sigma}$ is not required to be sorted. When the columns are indexed by `Fin k` and
$\boldsymbol{\sigma}$ is non-increasing, $\boldsymbol{\sigma}$ is the sequence of singular values
(`NLAlib.IsSVD.singularValues_eq`).

The library's chosen thin SVD of a matrix, `NLAlib.svdU A` and `NLAlib.svdV A`, is the
lexicographically least one in fixed real coordinates; `NLAlib.truncatedSVD` is built from it.

## Main definitions

* `NLAlib.IsSVD`: the thin singular value decomposition, as a predicate.
* `NLAlib.svdU`, `NLAlib.svdV`: the factors of the chosen thin SVD.

## Main results

* `NLAlib.exists_isSVD`: every matrix has an SVD with $k$ columns, for every $k$ between its rank
  and its smaller dimension, with $\boldsymbol{\sigma}$ the singular values.
* `NLAlib.isSVD_svdU_svdV`, `NLAlib.IsSVD.toLex_equivFun_svdU_svdV_le`: the chosen SVD is an SVD,
  and the lexicographically least one.
* `NLAlib.IsSVD.singularValues_eq`, `NLAlib.IsSVD.exists_equiv_singularValues_eq`: the entries of
  $\boldsymbol{\sigma}$ are the singular values.
* `NLAlib.IsSVD.rank_eq`, `NLAlib.IsSVD.specNorm_eq`, `NLAlib.IsSVD.frobNorm_sq_eq`: rank and norms
  from any SVD; `NLAlib.IsSVD.frobInner_eq` for two matrices with the same singular vectors.
* `NLAlib.IsSVD.conjTranspose`, `NLAlib.IsSVD.mul_left`, `NLAlib.IsSVD.reindex`: stability.
* `NLAlib.IsSVD.eq_add`, `NLAlib.exists_isSVD_fromCols`: splitting into two blocks.
* `Matrix.IsHermitian.exists_equiv_abs_eigenvalue_eq_singularValues`: the singular values of a
  Hermitian matrix are the absolute values of its eigenvalues.
* `NLAlib.HasOrthonormalCols.singularValues_eq_one`: the singular values of an isometry.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r r₁ r₂ r' : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r] [Fintype r₁] [Fintype r₂] [Fintype r'] [DecidableEq r] [DecidableEq r₁]
  [DecidableEq r₂] [DecidableEq r']

/-- **Singular value decomposition**, thin form. `IsSVD A U σ V` means that $\mathbf{U}$ and
$\mathbf{V}$ have orthonormal columns indexed by the same finite type $r$, the real numbers
$\boldsymbol{\sigma}_i$ are nonnegative, and
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$. The
index type is arbitrary and $\boldsymbol{\sigma}$ need not be sorted.
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
  /-- The decomposition $\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$,
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$. -/
  eq : A = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ

namespace IsSVD

variable {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}

/-- The decomposition, associated to the right. -/
private theorem eq_mul_mul (h : IsSVD A U σ V) :
    A = U * (Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ) := by
  rw [← Matrix.mul_assoc]
  exact h.eq

/-- The decomposition of the conjugate transpose:
$\mathbf{A}^{\mathsf{H}} = \mathbf{V}\mathbf{\Sigma}\mathbf{U}^{\mathsf{H}}$. -/
private theorem conjTranspose_eq_mul_mul (h : IsSVD A U σ V) :
    Aᴴ = V * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Uᴴ := by
  rw [h.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_diagonal_ofReal, Matrix.mul_assoc]

/-! ### Consequences of the decomposition -/

/-- $\mathbf{A}\mathbf{V} = \mathbf{U}\mathbf{\Sigma}$, with
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$: the right singular vectors are mapped
to multiples of the left ones. -/
theorem mul_right_eq (h : IsSVD A U σ V) :
    A * V = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.eq, h.hasOrthonormalCols_right.mul_conjTranspose_mul_cancel_right]

/-- $\mathbf{U}^{\mathsf{H}}\mathbf{A} = \mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$, with
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$. -/
theorem conjTranspose_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.conjTranspose_mul_cancel_left]

/-- $\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V} = \mathbf{\Sigma}$, with
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$. -/
theorem conjTranspose_mul_mul_eq (h : IsSVD A U σ V) :
    Uᴴ * A * V = Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.conjTranspose_mul_eq, h.hasOrthonormalCols_right.mul_conjTranspose_mul_cancel_right]

/-- The Gram matrix from an SVD:
$\mathbf{A}^{\mathsf{H}}\mathbf{A} = \mathbf{V}\mathbf{\Sigma}^2\mathbf{V}^{\mathsf{H}}$, with
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$. -/
theorem conjTranspose_mul_self_eq (h : IsSVD A U σ V) :
    Aᴴ * A = V * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  rw [h.conjTranspose_eq_mul_mul, Matrix.mul_assoc _ _ A, h.conjTranspose_mul_eq,
    ← Matrix.mul_assoc, Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
  simp only [sq, RCLike.ofReal_mul]

/-- The other Gram matrix from an SVD:
$\mathbf{A}\mathbf{A}^{\mathsf{H}} = \mathbf{U}\mathbf{\Sigma}^2\mathbf{U}^{\mathsf{H}}$, with
$\mathbf{\Sigma} = \operatorname{diag}(\boldsymbol{\sigma})$. -/
theorem mul_conjTranspose_self_eq (h : IsSVD A U σ V) :
    A * Aᴴ = U * Matrix.diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) * Uᴴ := by
  rw [h.conjTranspose_eq_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.mul_right_eq,
    Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
  simp only [sq, RCLike.ofReal_mul]

/-- A right singular vector is mapped to $\boldsymbol{\sigma}_i$ times the left singular vector:
$\mathbf{A}\mathbf{v}_i = \boldsymbol{\sigma}_i \mathbf{u}_i$ for the $i$-th columns
$\mathbf{v}_i$ of $\mathbf{V}$ and $\mathbf{u}_i$ of $\mathbf{U}$. -/
theorem mulVec_col (h : IsSVD A U σ V) (i : r) : A *ᵥ V.col i = σ i • U.col i := by
  funext j
  have hj : (A * V) j i = U j i * ((σ i : ℝ) : 𝕜) := by
    rw [h.mul_right_eq, Matrix.mul_diagonal]
  rw [Pi.smul_apply, Matrix.col_apply, RCLike.real_smul_eq_coe_mul, mul_comm, ← hj]
  rfl

/-! ### Stability -/

/-- An SVD of $\mathbf{A}$ gives an SVD of $\mathbf{A}^{\mathsf{H}}$ with the factors exchanged. -/
protected theorem conjTranspose (h : IsSVD A U σ V) : IsSVD Aᴴ V σ U :=
  ⟨h.hasOrthonormalCols_right, h.hasOrthonormalCols_left, h.nonneg,
    h.conjTranspose_eq_mul_mul⟩

/-- Left multiplication by a matrix with orthonormal columns:
$\mathbf{Q}\mathbf{A} = (\mathbf{Q}\mathbf{U})\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ is an SVD.
This is the step that lifts the SVD of a small projected matrix to the full space. -/
theorem mul_left [DecidableEq m] (h : IsSVD A U σ V) {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (Q * A) (Q * U) σ V := by
  refine ⟨hQ.mul h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, h.nonneg, ?_⟩
  rw [Matrix.mul_assoc Q U, Matrix.mul_assoc Q, ← h.eq]

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns:
$\mathbf{A}\mathbf{Q}^{\mathsf{H}} = \mathbf{U}\mathbf{\Sigma}(\mathbf{Q}\mathbf{V})^{\mathsf{H}}$
is an SVD. -/
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

/-- The rank is the number of nonzero entries of $\boldsymbol{\sigma}$. -/
theorem rank_eq (h : IsSVD A U σ V) : A.rank = (Finset.univ.filter fun i => σ i ≠ 0).card := by
  classical
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.rank_mul, ← Matrix.rank_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    h.hasOrthonormalCols_right.rank_mul, Matrix.rank_conjTranspose, Matrix.rank_diagonal,
    Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr fun i _ => not_congr RCLike.ofReal_eq_zero)

/-- The spectral norm is the largest entry of $\boldsymbol{\sigma}$:
$\|\mathbf{A}\|_2 = \max_i \boldsymbol{\sigma}_i$, the supremum norm of $\boldsymbol{\sigma}$. -/
theorem specNorm_eq (h : IsSVD A U σ V) : specNorm A = ‖σ‖ := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.specNorm_mul_left,
    h.hasOrthonormalCols_right.specNorm_mul_conjTranspose_right, specNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [RCLike.norm_ofReal]
    exact norm_le_pi_norm σ i
  · rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜)]
    exact norm_le_pi_norm (fun i => ((σ i : ℝ) : 𝕜)) i

/-- The squared Frobenius norm is the sum of the squares of the entries of $\boldsymbol{\sigma}$:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \sum_i \boldsymbol{\sigma}_i^2$. -/
theorem frobNorm_sq_eq (h : IsSVD A U σ V) : frobNorm A ^ 2 = ∑ i, σ i ^ 2 := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.frobNorm_mul_left,
    h.hasOrthonormalCols_right.frobNorm_mul_conjTranspose_right, frobNorm_diagonal_sq]
  exact Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_ofReal, sq_abs]

/-- The Frobenius inner product of two matrices with the same singular vectors is the inner
product of their diagonal factors: if
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ and
$\mathbf{B} = \mathbf{U} \operatorname{diag}(\boldsymbol{\tau}) \mathbf{V}^{\mathsf{H}}$ are SVDs,
then $\langle \mathbf{A}, \mathbf{B} \rangle_{\mathsf{F}} = \sum_i \boldsymbol{\sigma}_i
\boldsymbol{\tau}_i$. -/
theorem frobInner_eq {B : Matrix m n 𝕜} {τ : r → ℝ} (h : IsSVD A U σ V) (hB : IsSVD B U τ V) :
    frobInner A B = ∑ i, σ i * τ i := by
  rw [h.eq, hB.eq, Matrix.mul_assoc, Matrix.mul_assoc, frobInner_mul_left,
    h.hasOrthonormalCols_left.conjTranspose_mul_cancel_left, frobInner_mul_right,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    h.hasOrthonormalCols_right.conjTranspose_mul_self, Matrix.mul_one, frobInner_eq_re_trace,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
    ← RCLike.ofReal_sum, RCLike.ofReal_re]

/-! ### The entries of $\boldsymbol{\sigma}$ are the singular values -/

/-- The singular values of $\mathbf{A}$ are those of the diagonal factor. -/
private theorem singularValues_eq_singularValues_diagonal (h : IsSVD A U σ V) :
    singularValues A = singularValues (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) := by
  rw [h.eq_mul_mul, h.hasOrthonormalCols_left.singularValues_mul_left,
    h.hasOrthonormalCols_right.singularValues_mul_conjTranspose_right]

/-- **Uniqueness of the singular values.** In an SVD with columns indexed by `Fin k` and
$\boldsymbol{\sigma}$ non-increasing, $\boldsymbol{\sigma}$ is the sequence of singular values:
$\sigma_i(\mathbf{A}) = \boldsymbol{\sigma}_i$ for $i < k$.
Result: svd-uniqueness -/
theorem singularValues_eq {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) (hσ : Antitone σ) (i : Fin k) :
    singularValues A i = σ i := by
  have hD : (Matrix.diagonal fun j => ((σ j : ℝ) : 𝕜)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun j => RCLike.ofReal_nonneg.mpr (h.nonneg j)
  rw [h.singularValues_eq_singularValues_diagonal, hD.singularValues_eq_eigenvalue,
    eigenvalue_diagonal hσ]

/-- In an SVD, the singular values vanish from the number of columns on, whatever the column
type: $\sigma_i(\mathbf{A}) = 0$ for $i \ge \lvert r \rvert$. -/
theorem singularValues_of_card_le (h : IsSVD A U σ V) {i : ℕ} (hi : Fintype.card r ≤ i) :
    singularValues A i = 0 := by
  rw [h.singularValues_eq_singularValues_diagonal]
  exact singularValues_of_card_cols_le _ hi

/-- In an SVD with $k$ columns, the singular values vanish from index $k$ on. -/
theorem singularValues_of_le {k : ℕ} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
    {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) {i : ℕ} (hi : k ≤ i) :
    singularValues A i = 0 :=
  h.singularValues_of_card_le (by rwa [Fintype.card_fin])

/-- In any SVD, the entries of $\boldsymbol{\sigma}$ are the leading singular values in some
order: $\boldsymbol{\sigma}_i = \sigma_{e(i)}(\mathbf{A})$ for a bijection $e$ from $r$ onto
$\{0, \dots, \lvert r \rvert - 1\}$. -/
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

/-- An SVD whose singular triples are split into two groups writes $\mathbf{A}$ as a sum of two
pieces with mutually orthogonal factors: if
$[\mathbf{U}_1 \; \mathbf{U}_2]$, $(\boldsymbol{\sigma}_1, \boldsymbol{\sigma}_2)$,
$[\mathbf{V}_1 \; \mathbf{V}_2]$ is an SVD of $\mathbf{A}$, then
$$\mathbf{A} = \mathbf{U}_1 \operatorname{diag}(\boldsymbol{\sigma}_1) \mathbf{V}_1^{\mathsf{H}} +
  \mathbf{U}_2 \operatorname{diag}(\boldsymbol{\sigma}_2) \mathbf{V}_2^{\mathsf{H}}.$$
This is the form in which Wedin's theorem and the analysis of truncation consume an SVD. -/
theorem eq_add {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    A = U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ +
      U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ := by
  have hA := h.eq
  rwa [diagonal_sumElim_ofReal, Matrix.fromCols_mul_fromBlocks,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add] at hA

/-- The first block of a split SVD is an SVD of its own piece,
$\mathbf{U}_1 \operatorname{diag}(\boldsymbol{\sigma}_1) \mathbf{V}_1^{\mathsf{H}}$. -/
theorem fromCols_left {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ) U₁ σ₁ V₁ :=
  ⟨(hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_left).1,
    (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right).1,
    fun i => h.nonneg (Sum.inl i), rfl⟩

/-- The second block of a split SVD is an SVD of its own piece,
$\mathbf{U}_2 \operatorname{diag}(\boldsymbol{\sigma}_2) \mathbf{V}_2^{\mathsf{H}}$. -/
theorem fromCols_right {U₁ : Matrix m r₁ 𝕜} {U₂ : Matrix m r₂ 𝕜} {σ₁ : r₁ → ℝ} {σ₂ : r₂ → ℝ}
    {V₁ : Matrix n r₁ 𝕜} {V₂ : Matrix n r₂ 𝕜}
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂) (Matrix.fromCols V₁ V₂)) :
    IsSVD (U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ) U₂ σ₂ V₂ :=
  ⟨(hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_left).2.1,
    (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right).2.1,
    fun i => h.nonneg (Sum.inr i), rfl⟩

end IsSVD

/-! ### Existence -/

/-- A matrix $\mathbf{B}$ whose Gram matrix is $\operatorname{diag}(\mathbf{s})^2$ is
$\mathbf{U} \operatorname{diag}(\mathbf{s})$ for a $\mathbf{U}$ with orthonormal columns, when
$\lvert r \rvert \le \lvert m \rvert$: normalise the columns with $\mathbf{s}_i \ne 0$ and complete
them. -/
private theorem exists_hasOrthonormalCols_mul_diagonal_eq {B : Matrix m r 𝕜} {s : r → ℝ}
    (hB : Bᴴ * B = Matrix.diagonal fun i => ((s i ^ 2 : ℝ) : 𝕜))
    (hr : Fintype.card r ≤ Fintype.card m) :
    ∃ U : Matrix m r 𝕜, HasOrthonormalCols U ∧
      U * Matrix.diagonal (fun i => ((s i : ℝ) : 𝕜)) = B := by
  classical
  obtain ⟨C, hCB⟩ : ∃ C : Matrix m r 𝕜,
      C = B * Matrix.diagonal fun i => (((s i)⁻¹ : ℝ) : 𝕜) := ⟨_, rfl⟩
  have hQ₁ : HasOrthonormalCols (C.submatrix id (Subtype.val : {i // s i ≠ 0} → r)) := by
    have hQ := hasOrthonormalCols_div_of_conjTranspose_mul_self_eq_diagonal hB
      (Subtype.val : {i // s i ≠ 0} → r) Subtype.val_injective (fun i => i.2)
    convert hQ using 1
    ext j i
    simp only [hCB, Matrix.submatrix_apply, id_eq, Matrix.mul_diagonal, Matrix.of_apply,
      RCLike.ofReal_inv, div_eq_mul_inv]
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
    exact (congrFun (col_eq_zero_of_conjTranspose_mul_self_apply_eq_zero B
      (by rw [hB, Matrix.diagonal_apply_eq, hi0, zero_pow two_ne_zero,
        RCLike.ofReal_zero])) j).symm

/-- **Existence of the singular value decomposition.** For every $k$ between the rank of
$\mathbf{A}$ and its smaller dimension,
$$\mathbf{A} = \mathbf{U}
  \operatorname{diag}\bigl(\sigma_0(\mathbf{A}), \dots, \sigma_{k-1}(\mathbf{A})\bigr)
  \mathbf{V}^{\mathsf{H}}$$
with $\mathbf{U}$, $\mathbf{V}$ having $k$ orthonormal columns. With
$k = \operatorname{rank} \mathbf{A}$ this is the compact SVD and with
$k = \min(\lvert m \rvert, \lvert n \rvert)$ the thin SVD.
[HornJohnson2013, Theorem 2.6.3]; [GolubVanLoan2013, Theorem 2.4.1].
Result: svd-existence -/
theorem exists_isSVD (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) (hkm : k ≤ Fintype.card m)
    (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜),
      IsSVD A U (fun i => singularValues A i) V := by
  classical
  obtain ⟨W, hW, hGW⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_eq_mul_diagonal_mul_conjTranspose
  simp only [← singularValues_sq] at hGW
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
  have hi0 : (A * W).col i = 0 :=
    col_eq_zero_of_conjTranspose_mul_self_apply_eq_zero (A * W) (by
      rw [hAW, Matrix.diagonal_apply_eq, (singularValues_eq_zero_iff A).mpr (hk.trans hki),
        zero_pow two_ne_zero, RCLike.ofReal_zero])
  rw [show (A * W) a i = 0 from congrFun hi0 a, zero_mul]

/-- Existence of a split singular value decomposition: for $k + d$ between the rank of
$\mathbf{A}$ and its smaller dimension, $\mathbf{A}$ has an SVD whose first block carries the $k$
largest singular values $\sigma_0(\mathbf{A}), \dots, \sigma_{k-1}(\mathbf{A})$ and whose second
block carries the next $d$, $\sigma_k(\mathbf{A}), \dots, \sigma_{k+d-1}(\mathbf{A})$. -/
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
/-- Every matrix of rank at most $k$ factors as $\mathbf{B}\mathbf{C}^{\mathsf{H}}$ through $k$
columns; more precisely $\mathbf{A} = \mathbf{U}(\mathbf{V}\mathbf{\Sigma})^{\mathsf{H}}$ from the
compact SVD. The rank factorisation used when a proof only needs "$\mathbf{A}$ has rank at most
$k$" in product form. -/
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
    Matrix.conjTranspose_diagonal_ofReal, Matrix.mul_assoc U, hS.conjTranspose_mul_cancel_left,
    ← Matrix.mul_assoc]
  exact h.eq

/-! ### The chosen SVD -/

/-- The thin SVDs of $\mathbf{A}$ with $\boldsymbol{\sigma}$ the singular values form a compact
set of factor pairs: a closed subset of a product of two Stiefel sets. -/
private theorem isCompact_setOf_isSVD_singularValues (A : Matrix m n 𝕜) {r : ℕ} :
    IsCompact {p : Matrix m (Fin r) 𝕜 × Matrix n (Fin r) 𝕜 |
      IsSVD A p.1 (fun i => singularValues A i) p.2} := by
  refine (isCompact_setOf_hasOrthonormalCols.prod
    isCompact_setOf_hasOrthonormalCols).of_isClosed_subset ?_
    fun p hp => ⟨hp.hasOrthonormalCols_left, hp.hasOrthonormalCols_right⟩
  have h : {p : Matrix m (Fin r) 𝕜 × Matrix n (Fin r) 𝕜 |
      IsSVD A p.1 (fun i => singularValues A i) p.2} =
      ({p | HasOrthonormalCols p.1} ∩ {p | HasOrthonormalCols p.2}) ∩
        {p | A = p.1 * Matrix.diagonal (fun i : Fin r => ((singularValues A i : ℝ) : 𝕜)) *
          p.2ᴴ} := by
    ext p
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.4⟩,
      fun h => ⟨h.1.1, h.1.2, fun i => singularValues_nonneg A i, h.2⟩⟩
  rw [h]
  exact ((isClosed_setOf_hasOrthonormalCols.preimage continuous_fst).inter
    (isClosed_setOf_hasOrthonormalCols.preimage continuous_snd)).inter
    (isClosed_eq continuous_const
      ((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd.matrix_conjTranspose))

/-- A thin SVD of $\mathbf{A}$ whose coordinates are lexicographically least. -/
private theorem exists_isSVD_forall_toLex_le (A : Matrix m n 𝕜) :
    ∃ p : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
        Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
      IsSVD A p.1 (fun i => singularValues A i) p.2 ∧
        ∀ q : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
            Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
          IsSVD A q.1 (fun i => singularValues A i) q.2 →
            toLex ((Module.finBasis ℝ _).equivFun p) ≤
              toLex ((Module.finBasis ℝ _).equivFun q) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A (le_min A.rank_le_card_height A.rank_le_card_width)
    (min_le_left _ _) (min_le_right _ _)
  exact (isCompact_setOf_isSVD_singularValues A).exists_forall_toLex_equivFun_le _ ⟨(U, V), h⟩

open Classical in
/-- The **left singular vectors of the chosen SVD**: $\mathsf{svdU}(\mathbf{A})$ has
$r = \min(\lvert m\rvert, \lvert n\rvert)$ orthonormal columns and, with
$\mathsf{svdV}(\mathbf{A})$, gives
$$\mathbf{A} = \mathsf{svdU}(\mathbf{A})\,\operatorname{diag}\bigl(\sigma_0(\mathbf{A}), \dots,
\sigma_{r-1}(\mathbf{A})\bigr)\,\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$$
(`NLAlib.isSVD_svdU_svdV`). Among all such thin SVDs it is the one whose real coordinates, in the
basis `Module.finBasis ℝ _` of the pairs of factors, are lexicographically least
(`NLAlib.IsSVD.toLex_equivFun_svdU_svdV_le`), so it is a fixed function of $\mathbf{A}$; it is Borel
measurable (`NLAlib.measurable_svdU`). `NLAlib.truncatedSVD` is built from it. -/
noncomputable def svdU (A : Matrix m n 𝕜) :
    Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 :=
  if h : ∃ p : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
      Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
      IsSVD A p.1 (fun i => singularValues A i) p.2 ∧
        ∀ q : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
            Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
          IsSVD A q.1 (fun i => singularValues A i) q.2 →
            toLex ((Module.finBasis ℝ _).equivFun p) ≤ toLex ((Module.finBasis ℝ _).equivFun q)
  then h.choose.1 else 0

open Classical in
/-- The **right singular vectors of the chosen SVD**, $\mathsf{svdV}(\mathbf{A})$, with $r =
\min(\lvert m\rvert, \lvert n\rvert)$ orthonormal columns; see `NLAlib.svdU`. -/
noncomputable def svdV (A : Matrix m n 𝕜) :
    Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 :=
  if h : ∃ p : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
      Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
      IsSVD A p.1 (fun i => singularValues A i) p.2 ∧
        ∀ q : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜 ×
            Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜,
          IsSVD A q.1 (fun i => singularValues A i) q.2 →
            toLex ((Module.finBasis ℝ _).equivFun p) ≤ toLex ((Module.finBasis ℝ _).equivFun q)
  then h.choose.2 else 0

/-- The pair of factors of the chosen SVD is the chosen lexicographically least SVD. -/
private theorem svdU_svdV_eq_choose (A : Matrix m n 𝕜) :
    (svdU A, svdV A) = (exists_isSVD_forall_toLex_le A).choose := by
  rw [svdU, svdV, dif_pos (exists_isSVD_forall_toLex_le A),
    dif_pos (exists_isSVD_forall_toLex_le A)]

/-- The chosen SVD is an SVD: $\mathbf{A} = \mathsf{svdU}(\mathbf{A})\,\mathbf{\Sigma}\,
\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$ with orthonormal columns and $\mathbf{\Sigma} =
\operatorname{diag}(\sigma_i(\mathbf{A}))_{i<r}$, $r = \min(\lvert m\rvert, \lvert n\rvert)$, the
singular values in non-increasing order. -/
theorem isSVD_svdU_svdV (A : Matrix m n 𝕜) :
    IsSVD A (svdU A) (fun i => singularValues A i) (svdV A) := by
  have h := (exists_isSVD_forall_toLex_le A).choose_spec.1
  rwa [← svdU_svdV_eq_choose] at h

/-- Construction lemma (consumed by `NLAlib.measurable_svdU`; not needed for using the SVD):
$(\mathsf{svdU}(\mathbf{A}), \mathsf{svdV}(\mathbf{A}))$ has the lexicographically least
coordinates in the basis `Module.finBasis ℝ _` among the thin SVDs of $\mathbf{A}$ with
$\mathbf{\Sigma} = \operatorname{diag}(\sigma_i(\mathbf{A}))_{i<r}$. -/
theorem IsSVD.toLex_equivFun_svdU_svdV_le {A : Matrix m n 𝕜}
    {U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜}
    {V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜}
    (h : IsSVD A U (fun i => singularValues A i) V) :
    toLex ((Module.finBasis ℝ _).equivFun (svdU A, svdV A)) ≤
      toLex ((Module.finBasis ℝ _).equivFun (U, V)) := by
  rw [svdU_svdV_eq_choose]
  exact (exists_isSVD_forall_toLex_le A).choose_spec.2 (U, V) h

/-! ### Hermitian matrices -/

/-- The absolute values of the eigenvalues of a Hermitian matrix are its singular values, up to a
permutation $e$ of $\{0, \dots, \lvert n \rvert - 1\}$:
$\lvert \lambda_i(\mathbf{A}) \rvert = \sigma_{e(i)}(\mathbf{A})$. The eigendecomposition is a
singular value decomposition once the signs of the eigenvalues are moved into the left factor.
For a positive semidefinite matrix no permutation is needed
(`Matrix.PosSemidef.singularValues_eq_eigenvalue`). -/
theorem _root_.Matrix.IsHermitian.exists_equiv_abs_eigenvalue_eq_singularValues
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ e : Fin (Fintype.card n) ≃ Fin (Fintype.card n),
      ∀ i : Fin (Fintype.card n), |eigenvalue A i| = singularValues A (e i) := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  let s : Fin (Fintype.card n) → ℝ := fun i => if 0 ≤ eigenvalue A i then 1 else -1
  have hs : ∀ i, s i * s i = 1 := fun i => by
    simp only [s]
    split_ifs <;> norm_num
  have hsa : ∀ i, s i * |eigenvalue A i| = eigenvalue A i := fun i => by
    simp only [s]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h), neg_mul_neg, one_mul]
  have hD : HasOrthonormalCols (Matrix.diagonal fun i => ((s i : ℝ) : 𝕜)) := by
    rw [HasOrthonormalCols, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, hs,
      RCLike.ofReal_one]
  have h : IsSVD A (U * Matrix.diagonal fun i => ((s i : ℝ) : 𝕜))
      (fun i => |eigenvalue A i|) U := by
    refine ⟨hU.mul hD, hU, fun i => abs_nonneg _, ?_⟩
    rw [Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
    simp only [← RCLike.ofReal_mul, hsa]
    exact hAU
  obtain ⟨e, he⟩ := h.exists_equiv_singularValues_eq
  exact ⟨e.trans (finCongr (Fintype.card_fin _)), fun i => he i⟩

/-- The singular values of a matrix with orthonormal columns are $1$, as many as it has
columns: $\sigma_i(\mathbf{V}) = 1$ for $i < \lvert n \rvert$. -/
theorem HasOrthonormalCols.singularValues_eq_one [DecidableEq n] {V : Matrix m n 𝕜}
    (hV : HasOrthonormalCols V) {i : ℕ} (hi : i < Fintype.card n) : singularValues V i = 1 := by
  have h1 : singularValues V = singularValues (1 : Matrix n n 𝕜) :=
    singularValues_eq_of_conjTranspose_mul_self_eq
      (by rw [hV.conjTranspose_mul_self, Matrix.conjTranspose_one, Matrix.one_mul])
  rw [h1, Matrix.PosSemidef.one.singularValues_eq_eigenvalue, eigenvalue_one hi]

end NLAlib
