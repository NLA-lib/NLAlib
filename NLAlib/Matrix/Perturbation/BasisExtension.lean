/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Norms.Block

/-!
# Extension of a basis by a block: the orthogonalization contract

A block orthogonalization scheme extends a stored basis $\mathbf{Q}$ by a block $\mathbf{W}$: it
returns new columns $\mathbf{Q}'$ and coefficients $\mathbf{H}$, $\mathbf{R}$ with
$\mathbf{W} \approx \mathbf{Q}\mathbf{H} + \mathbf{Q}'\mathbf{R}$, and it may return a zero column
where it finds $\mathbf{W}$ numerically dependent. A basis with zero columns is not near
orthonormal as a matrix, so orthonormality is measured by the Gram defect on the support,
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ with $s_j = 0$ for a zero
column and $s_j = 1$ otherwise. `NLAlib.IsBasisExtension` is the exact contract and
`NLAlib.IsBasisExtensionErr` the rounded one, with parameters $(\eta_0, \mu, \varepsilon)$.
Design: `docs/design/LowRank-BlockLanczos.md` §3.1a.

## Main definitions

* `NLAlib.colSupport`, `NLAlib.gramDefect`: the indicator of the nonzero columns and the Gram
  defect on the support.
* `NLAlib.IsBasisExtension`: the exact extension of a basis by a block.
* `NLAlib.ExtensionWindow`, `NLAlib.IsBasisExtensionErr`: the rounded extension and its
  antecedent.
* `NLAlib.blockPrefix`, `NLAlib.blockCols`: the first $j$ blocks and the block $j$ of a matrix
  stored as consecutive blocks of $b$ columns.
* `NLAlib.blockRowPrefix`, `NLAlib.blockRows`: the first $j$ blocks of rows and block $j$ of the
  rows of a matrix stored as consecutive blocks of $b$ rows.
* `NLAlib.blockSuccEquiv`: the identification of the indices of $j$ blocks followed by one block
  with the indices of $j + 1$ blocks.

## Main results

* `NLAlib.gramDefect_eq_zero_iff`, `NLAlib.mul_conjTranspose_mul_self_of_gramDefect_eq_zero`,
  `NLAlib.mul_conjTranspose_eq_rangeProjector_of_gramDefect_eq_zero`: a matrix with zero Gram
  defect is a partial isometry.
* `NLAlib.gramDefect_eq_conjTranspose_mul_self_sub_one`,
  `NLAlib.hasOrthonormalCols_iff_gramDefect_eq_zero`: the case of no zero column.
* `NLAlib.gramDefect_fromCols`, `NLAlib.frobNorm_gramDefect_fromCols_sq`: the block form of the
  Gram defect of two blocks of columns.
* `NLAlib.gramDefect_submatrix`,
  `NLAlib.specNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect`,
  `NLAlib.specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect`,
  `NLAlib.card_filter_col_ne_zero_le`: compression to nonzero columns.
* `NLAlib.IsBasisExtension.range_eq`, `NLAlib.IsBasisExtension.coef_left_eq`,
  `NLAlib.IsBasisExtension.coef_right_eq`: consequences of the exact contract.
* `NLAlib.IsBasisExtensionErr.mono`, `NLAlib.IsBasisExtension.isBasisExtensionErr`: monotonicity,
  and the exact contract as the rounded one at $(0, 0, 0)$.
* `NLAlib.IsBasisExtensionErr.frobNorm_gramDefect_fromCols_sq_le`,
  `NLAlib.frobNorm_gramDefect_le_of_blocks`: the loss of orthogonality block by block.
* `NLAlib.blockPrefix_succ_submatrix`, `NLAlib.blockRowPrefix_succ_submatrix`,
  `NLAlib.blockPrefix_succ_mul_blockRowPrefix_succ`, `NLAlib.range_blockPrefix_succ`,
  `NLAlib.gramDefect_blockPrefix_succ_eq_zero_iff`: the prefix of $j + 1$ blocks is the prefix
  of $j$ blocks followed by block $j$, up to the identification `NLAlib.blockSuccEquiv` of the
  indices.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m ι κ : Type*}

/-! ### The Gram defect on the support -/

open Classical in
/-- The indicator of the nonzero columns of $\mathbf{Q}$: $s_j = 0$ if column $j$ of $\mathbf{Q}$
is zero and $s_j = 1$ otherwise. -/
noncomputable def colSupport (Q : Matrix m ι 𝕜) (j : ι) : 𝕜 :=
  if Q.col j = 0 then 0 else 1

/-- The indicator of the nonzero columns is $0$ at a zero column. -/
theorem colSupport_of_col_eq_zero {Q : Matrix m ι 𝕜} {j : ι} (h : Q.col j = 0) :
    colSupport Q j = 0 := by
  rw [colSupport, if_pos h]

/-- The indicator of the nonzero columns is $1$ at a nonzero column. -/
theorem colSupport_of_col_ne_zero {Q : Matrix m ι 𝕜} {j : ι} (h : Q.col j ≠ 0) :
    colSupport Q j = 1 := by
  rw [colSupport, if_neg h]

/-- The indicator of the nonzero columns of $[\mathbf{Q}, \mathbf{Q}']$ is the indicator of
$\mathbf{Q}$ on the first block of columns and that of $\mathbf{Q}'$ on the second. -/
theorem colSupport_fromCols (Q : Matrix m ι 𝕜) (Q' : Matrix m κ 𝕜) :
    colSupport (Matrix.fromCols Q Q') = Sum.elim (colSupport Q) (colSupport Q') := by
  funext j
  rcases j with j | j <;> rfl

/-- Multiplying $\mathbf{Q}$ on the right by the diagonal indicator $\operatorname{diag}
(\mathbf{s})$ of its nonzero columns leaves it unchanged. -/
theorem mul_diagonal_colSupport [Fintype ι] [DecidableEq ι] (Q : Matrix m ι 𝕜) :
    Q * Matrix.diagonal (colSupport Q) = Q := by
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases h : Q.col j = 0
  · rw [colSupport_of_col_eq_zero h, mul_zero]
    exact (congrFun h i).symm
  · rw [colSupport_of_col_ne_zero h, mul_one]

/-- The **Gram defect on the support** of $\mathbf{Q}$: the matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$, where $s_j = 0$ if column
$j$ of $\mathbf{Q}$ is zero and $s_j = 1$ otherwise. It is zero exactly when the nonzero columns
of $\mathbf{Q}$ are orthonormal, and it is $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \mathbf{I}$ when
no column is zero. -/
noncomputable def gramDefect [Fintype m] [DecidableEq ι] (Q : Matrix m ι 𝕜) : Matrix ι ι 𝕜 :=
  Qᴴ * Q - Matrix.diagonal (colSupport Q)

/-- The Gram defect on the support vanishes exactly when
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \operatorname{diag}(\mathbf{s})$, $\mathbf{s}$ the indicator
of the nonzero columns of $\mathbf{Q}$: distinct columns are orthogonal and every nonzero column
has norm one. -/
theorem gramDefect_eq_zero_iff [Fintype m] [DecidableEq ι] {Q : Matrix m ι 𝕜} :
    gramDefect Q = 0 ↔ Qᴴ * Q = Matrix.diagonal (colSupport Q) :=
  sub_eq_zero

/-- The Gram defect on the support of a matrix $\mathbf{Q}$ with no zero column is
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \mathbf{I}$. -/
theorem gramDefect_eq_conjTranspose_mul_self_sub_one [Fintype m] [DecidableEq ι]
    {Q : Matrix m ι 𝕜} (h : ∀ j, Q.col j ≠ 0) : gramDefect Q = Qᴴ * Q - 1 := by
  have hs : colSupport Q = fun _ => 1 := funext fun j => colSupport_of_col_ne_zero (h j)
  rw [gramDefect, hs, Matrix.diagonal_one]

/-- A matrix $\mathbf{Q}$ with orthonormal columns has no zero column. -/
theorem HasOrthonormalCols.col_ne_zero [Fintype m] [DecidableEq ι] {Q : Matrix m ι 𝕜}
    (hQ : HasOrthonormalCols Q) (j : ι) : Q.col j ≠ 0 := by
  intro h
  have h1 : (Qᴴ * Q) j j = 1 := by rw [hQ.conjTranspose_mul_self, Matrix.one_apply_eq]
  have h0 : (Qᴴ * Q) j j = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [show Q i j = 0 from congrFun h i, mul_zero]
  exact one_ne_zero (h1.symm.trans h0)

/-- A matrix $\mathbf{Q}$ with orthonormal columns has zero Gram defect on the support. -/
theorem HasOrthonormalCols.gramDefect_eq_zero [Fintype m] [DecidableEq ι] {Q : Matrix m ι 𝕜}
    (hQ : HasOrthonormalCols Q) : gramDefect Q = 0 := by
  rw [gramDefect_eq_conjTranspose_mul_self_sub_one hQ.col_ne_zero, hQ.conjTranspose_mul_self,
    sub_self]

/-- A matrix $\mathbf{Q}$ with no zero column has orthonormal columns exactly when its Gram
defect on the support vanishes. -/
theorem hasOrthonormalCols_iff_gramDefect_eq_zero [Fintype m] [DecidableEq ι]
    {Q : Matrix m ι 𝕜} (h : ∀ j, Q.col j ≠ 0) : HasOrthonormalCols Q ↔ gramDefect Q = 0 := by
  rw [gramDefect_eq_conjTranspose_mul_self_sub_one h, sub_eq_zero, hasOrthonormalCols_iff]

/-- The Gram defect on the support, $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ with $\mathbf{s}$ the indicator of the nonzero columns of
$\mathbf{Q}$, is Hermitian. -/
theorem isHermitian_gramDefect [Fintype m] [DecidableEq ι] (Q : Matrix m ι 𝕜) :
    (gramDefect Q).IsHermitian := by
  have hs : IsSelfAdjoint (colSupport Q) := by
    change star (colSupport Q) = colSupport Q
    funext j
    rw [Pi.star_apply]
    by_cases h : Q.col j = 0
    · rw [colSupport_of_col_eq_zero h, star_zero]
    · rw [colSupport_of_col_ne_zero h, star_one]
  exact (Matrix.isHermitian_conjTranspose_mul_self Q).sub
    (Matrix.isHermitian_diagonal_of_self_adjoint _ hs)

/-- The spectral norm of the Gram defect on the support $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ is at most its Frobenius
norm: $\|\mathbf{D}\|_2 \le \|\mathbf{D}\|_{\mathsf{F}}$. -/
theorem specNorm_gramDefect_le_frobNorm [Fintype m] [Fintype ι] [DecidableEq ι]
    (Q : Matrix m ι 𝕜) : specNorm (gramDefect Q) ≤ frobNorm (gramDefect Q) :=
  specNorm_le_frobNorm _

/-- A matrix whose nonzero columns are orthonormal is a partial isometry: if the Gram defect on
the support of $\mathbf{Q}$ vanishes then $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} =
\mathbf{Q}$. -/
theorem mul_conjTranspose_mul_self_of_gramDefect_eq_zero [Fintype m] [Fintype ι] [DecidableEq ι]
    {Q : Matrix m ι 𝕜} (h : gramDefect Q = 0) : Q * Qᴴ * Q = Q := by
  rw [Matrix.mul_assoc, gramDefect_eq_zero_iff.1 h, mul_diagonal_colSupport]

/-- If the nonzero columns of $\mathbf{Q}$ are orthonormal (the Gram defect on the support of
$\mathbf{Q}$ vanishes) then $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ is the orthogonal projector
$\mathbf{P}_{\mathbf{Q}}$ onto the column space of $\mathbf{Q}$. -/
theorem mul_conjTranspose_eq_rangeProjector_of_gramDefect_eq_zero [Fintype m] [Fintype ι]
    [DecidableEq ι] {Q : Matrix m ι 𝕜} (h : gramDefect Q = 0) : Q * Qᴴ = rangeProjector Q :=
  (rangeProjector_eq_mul_conjTranspose_of_mul_conjTranspose_mul_self
    (mul_conjTranspose_mul_self_of_gramDefect_eq_zero h)).symm

/-- The Gram defect on the support of two blocks of columns side by side, in block form: with
$\mathbf{D}(\cdot)$ the Gram defect on the support,
$$\mathbf{D}([\mathbf{Q}, \mathbf{Q}']) = \begin{bmatrix} \mathbf{D}(\mathbf{Q}) &
\mathbf{Q}^{\mathsf{H}}\mathbf{Q}' \\ \mathbf{Q}'^{\mathsf{H}}\mathbf{Q} & \mathbf{D}(\mathbf{Q}')
\end{bmatrix}.$$ -/
theorem gramDefect_fromCols [Fintype m] [DecidableEq ι] [DecidableEq κ] (Q : Matrix m ι 𝕜)
    (Q' : Matrix m κ 𝕜) :
    gramDefect (Matrix.fromCols Q Q') =
      Matrix.fromBlocks (gramDefect Q) (Qᴴ * Q') (Q'ᴴ * Q) (gramDefect Q') := by
  rw [gramDefect, colSupport_fromCols, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  ext (i | i) (j | j) <;> simp [gramDefect, Matrix.diagonal_apply]

/-- The loss of orthogonality when a block of columns is appended, with zero columns allowed:
with $\mathbf{D}(\cdot)$ the Gram defect on the support,
$$\|\mathbf{D}([\mathbf{Q}, \mathbf{Q}'])\|_{\mathsf{F}}^2 =
\|\mathbf{D}(\mathbf{Q})\|_{\mathsf{F}}^2 + 2\|\mathbf{Q}^{\mathsf{H}}\mathbf{Q}'\|_{\mathsf{F}}^2 +
\|\mathbf{D}(\mathbf{Q}')\|_{\mathsf{F}}^2.$$ -/
theorem frobNorm_gramDefect_fromCols_sq [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (Q : Matrix m ι 𝕜) (Q' : Matrix m κ 𝕜) :
    frobNorm (gramDefect (Matrix.fromCols Q Q')) ^ 2 =
      frobNorm (gramDefect Q) ^ 2 + 2 * frobNorm (Qᴴ * Q') ^ 2 + frobNorm (gramDefect Q') ^ 2 := by
  have hc : frobNorm (Q'ᴴ * Q) = frobNorm (Qᴴ * Q') := by
    rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [gramDefect_fromCols, frobNorm_fromBlocks_sq, hc]
  ring

/-! ### Compression to nonzero columns -/

/-- Selecting distinct columns commutes with the Gram defect on the support: for an injective
selection $e$ of columns of $\mathbf{Q}$, the Gram defect of the selected columns is the
principal submatrix of the Gram defect of $\mathbf{Q}$ on the rows and columns $e$. -/
theorem gramDefect_submatrix [Fintype m] [DecidableEq ι] [DecidableEq κ] (Q : Matrix m ι 𝕜)
    {e : κ → ι} (he : Function.Injective e) :
    gramDefect (Q.submatrix id e) = (gramDefect Q).submatrix e e := by
  ext i j
  simp only [gramDefect, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, he.eq_iff, id_eq]
  rfl

/-- The compression bridge: for an injective selection $e$ of nonzero columns of $\mathbf{Q}$,
the selected columns $\mathbf{Q}_e$ satisfy $\|\mathbf{Q}_e^{\mathsf{H}}\mathbf{Q}_e -
\mathbf{I}\|_2 \le \|\mathbf{D}\|_2$, where $\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ is the Gram defect on the support of $\mathbf{Q}$. -/
theorem specNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect [Fintype m] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Q : Matrix m ι 𝕜) {e : κ → ι}
    (he : Function.Injective e) (h : ∀ j, Q.col (e j) ≠ 0) :
    specNorm ((Q.submatrix id e)ᴴ * Q.submatrix id e - 1) ≤ specNorm (gramDefect Q) := by
  rw [← gramDefect_eq_conjTranspose_mul_self_sub_one (Q := Q.submatrix id e) h,
    gramDefect_submatrix Q he]
  exact specNorm_submatrix_le _ he he

/-- The compression bridge in the Frobenius norm: for an injective selection $e$ of nonzero
columns of $\mathbf{Q}$, the selected columns $\mathbf{Q}_e$ satisfy
$\|\mathbf{Q}_e^{\mathsf{H}}\mathbf{Q}_e - \mathbf{I}\|_{\mathsf{F}} \le
\|\mathbf{D}\|_{\mathsf{F}}$, where $\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ is the Gram defect on the support of $\mathbf{Q}$. -/
theorem frobNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect [Fintype m] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Q : Matrix m ι 𝕜) {e : κ → ι}
    (he : Function.Injective e) (h : ∀ j, Q.col (e j) ≠ 0) :
    frobNorm ((Q.submatrix id e)ᴴ * Q.submatrix id e - 1) ≤ frobNorm (gramDefect Q) := by
  rw [← gramDefect_eq_conjTranspose_mul_self_sub_one (Q := Q.submatrix id e) h,
    gramDefect_submatrix Q he]
  exact frobNorm_submatrix_le _ he he

/-- The compression bridge for a real matrix, in the transpose form consumed by
`NLAlib.IsOrthErr`: for an injective selection $e$ of nonzero columns of $\mathbf{Q}$, the
selected columns $\mathbf{Q}_e$ satisfy $\|\mathbf{Q}_e^{\mathsf{T}}\mathbf{Q}_e -
\mathbf{I}\|_2 \le \|\mathbf{D}\|_2$, where $\mathbf{D} = \mathbf{Q}^{\mathsf{T}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ is the Gram defect on the support of $\mathbf{Q}$. -/
theorem specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect [Fintype m] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Q : Matrix m ι ℝ) {e : κ → ι}
    (he : Function.Injective e) (h : ∀ j, Q.col (e j) ≠ 0) :
    specNorm ((Q.submatrix id e)ᵀ * Q.submatrix id e - 1) ≤ specNorm (gramDefect Q) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact specNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect Q he h

/-- A nearly orthonormal matrix has independent columns: if
$\|\mathbf{V}^{\mathsf{H}}\mathbf{V} - \mathbf{I}\|_2 < 1$ then $\mathbf{x} \mapsto
\mathbf{V}\mathbf{x}$ is injective. -/
theorem injective_mulVec_of_specNorm_conjTranspose_mul_self_sub_one_lt_one [Fintype m]
    [Fintype ι] [DecidableEq ι] {V : Matrix m ι 𝕜} (hV : specNorm (Vᴴ * V - 1) < 1) :
    Function.Injective V.mulVec := by
  have key : ∀ z, V *ᵥ z = 0 → z = 0 := by
    intro z hz
    have hG : (Vᴴ * V - 1) *ᵥ z = -z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
        zero_sub]
    have hle : ‖WithLp.toLp 2 z‖ ≤ specNorm (Vᴴ * V - 1) * ‖WithLp.toLp 2 z‖ := by
      have := norm_toLp_mulVec_le (Vᴴ * V - 1) z
      rwa [hG, WithLp.toLp_neg, norm_neg] at this
    have hz0 : ‖WithLp.toLp 2 z‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (WithLp.toLp 2 z), specNorm_nonneg (Vᴴ * V - 1)])
        (norm_nonneg _)
    have : WithLp.toLp 2 z = 0 := norm_eq_zero.1 hz0
    simpa using congrArg WithLp.ofLp this
  intro x y hxy
  have h0 : x - y = 0 := key _ (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 h0

/-- A nearly orthonormal basis with zero columns has at most as many nonzero columns as rows:
if the Gram defect on the support $\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ of a matrix $\mathbf{Q}$ with $n$ rows satisfies
$\|\mathbf{D}\|_2 < 1$, then $\mathbf{Q}$ has at most $n$ nonzero columns. -/
theorem card_filter_col_ne_zero_le [Fintype m] [Fintype ι] [DecidableEq ι] {Q : Matrix m ι 𝕜}
    [DecidablePred fun j => Q.col j ≠ 0] (hQ : specNorm (gramDefect Q) < 1) :
    (Finset.univ.filter fun j => Q.col j ≠ 0).card ≤ Fintype.card m := by
  have hle := specNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect Q
    (e := fun j : {j // Q.col j ≠ 0} => (j : ι)) Subtype.val_injective fun j => j.2
  have hinj : Function.Injective
      (Matrix.mulVecLin (Q.submatrix id fun j : {j // Q.col j ≠ 0} => (j : ι))) :=
    injective_mulVec_of_specNorm_conjTranspose_mul_self_sub_one_lt_one (lt_of_le_of_lt hle hQ)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype] at h
  exact h

/-! ### Entries of the Gram defect -/

/-- The column of the Gram defect on the support $\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ at a zero column of $\mathbf{Q}$ is zero: if column $j$ of
$\mathbf{Q}$ is zero then $\mathbf{D}_{i,j} = 0$ for every $i$. -/
theorem gramDefect_apply_of_col_eq_zero_right [Fintype m] [DecidableEq ι] {Q : Matrix m ι 𝕜}
    {j : ι} (h : Q.col j = 0) (i : ι) : gramDefect Q i j = 0 := by
  have h0 : ∀ k, Q k j = 0 := fun k => congrFun h k
  rw [gramDefect, Matrix.sub_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.sum_eq_zero fun k _ => by rw [h0 k, mul_zero]]
  split_ifs with hij
  · subst hij
    rw [colSupport_of_col_eq_zero h, sub_zero]
  · rw [sub_zero]

/-- The entries off the diagonal of the Gram defect on the support $\mathbf{D}$ of a real matrix
$\mathbf{Q}$ are the inner products of its columns: $\mathbf{D}_{i,j} = \mathbf{q}_i \cdot
\mathbf{q}_j$ for $i \ne j$. -/
theorem gramDefect_apply_of_ne [Fintype m] [DecidableEq ι] {Q : Matrix m ι ℝ} {i j : ι}
    (h : i ≠ j) : gramDefect Q i j = Q.col i ⬝ᵥ Q.col j := by
  rw [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, sub_zero,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

/-- The diagonal entry of the Gram defect on the support $\mathbf{D}$ of a real matrix
$\mathbf{Q}$ at a nonzero column $\mathbf{q}_j$: $\mathbf{D}_{j,j} = \|\mathbf{q}_j\|^2 - 1$. -/
theorem gramDefect_apply_self_of_col_ne_zero [Fintype m] [DecidableEq ι] {Q : Matrix m ι ℝ}
    {j : ι} (h : Q.col j ≠ 0) : gramDefect Q j j = ‖WithLp.toLp 2 (Q.col j)‖ ^ 2 - 1 := by
  rw [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply_eq, colSupport_of_col_ne_zero h,
    Matrix.conjTranspose_eq_transpose_of_trivial, EuclideanSpace.norm_sq_eq, sub_left_inj]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.col_apply, Real.norm_eq_abs,
    sq_abs]
  exact Finset.sum_congr rfl fun k _ => (sq _).symm

/-- Column $c$ of $\mathbf{Q}^{\mathsf{H}}\mathbf{Q}'$, for real matrices, is
$\mathbf{Q}^{\mathsf{T}}\mathbf{q}'_c$ with $\mathbf{q}'_c$ column $c$ of $\mathbf{Q}'$. -/
theorem col_conjTranspose_mul_eq_transpose_mulVec [Fintype m] (Q : Matrix m ι ℝ)
    (Q' : Matrix m κ ℝ) (c : κ) : (Qᴴ * Q').col c = Qᵀ *ᵥ Q'.col c := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

/-- A double sum of a symmetric function $f$ on $\{0, \dots, b - 1\}^2$ by columns:
$\sum_{i,j} f(i, j) = \sum_c \bigl(f(c, c) + 2\sum_{c' < c} f(c', c)\bigr)$. -/
private theorem sum_sum_eq_sum_diag_add_two_mul_sum_Iio {b : ℕ} (f : Fin b → Fin b → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ c, (f c c + 2 * ∑ c' ∈ Finset.Iio c, f c' c) := by
  have hI : ∀ (c : Fin b) (g : Fin b → ℝ),
      ∑ c' ∈ Finset.Iio c, g c' = ∑ c', if c' < c then g c' else 0 := by
    intro c g
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp
  have hswap : ∑ c, ∑ c', (if c < c' then f c' c else 0) =
      ∑ c, ∑ c', if c' < c then f c' c else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [hf c c']
  have hsplit : ∀ c c', f c' c = (if c' = c then f c c else 0) +
      (if c' < c then f c' c else 0) + (if c < c' then f c' c else 0) := by
    intro c c'
    rcases lt_trichotomy c' c with h | rfl | h
    · simp [h, h.ne, lt_asymm h]
    · simp
    · simp [h, h.ne', lt_asymm h]
  calc ∑ i, ∑ j, f i j = ∑ c, ∑ c', f c' c := Finset.sum_comm
    _ = ∑ c, (f c c + ∑ c', (if c' < c then f c' c else 0) +
          ∑ c', (if c < c' then f c' c else 0)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_congr rfl fun c' _ => hsplit c c', Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c fun _ => f c c,
          if_pos (Finset.mem_univ c)]
    _ = ∑ c, (f c c + 2 * ∑ c' ∈ Finset.Iio c, f c' c) := by
        simp only [hI, Finset.sum_add_distrib, ← Finset.mul_sum, hswap]
        ring

/-! ### The exact contract -/

section Exact

variable {n k b : ℕ}

/-- **The exact extension of a basis by a block.** The new block $\mathbf{Q}'$ and the
coefficients $\mathbf{H}$, $\mathbf{R}$ extend the basis $\mathbf{Q}$ by the block $\mathbf{W}$:
$\mathbf{W} = \mathbf{Q}\mathbf{H} + \mathbf{Q}'\mathbf{R}$ with $\mathbf{R}$ upper triangular;
the columns of $\mathbf{Q}'$ lie in the span of the columns of $\mathbf{Q}$ and $\mathbf{W}$; a
zero column of $\mathbf{W}$ gives a zero column of $\mathbf{Q}'$; the rows of $\mathbf{H}$ and
$\mathbf{R}$ at zero columns of $\mathbf{Q}$ and $\mathbf{Q}'$ are zero; and if the nonzero
columns of $\mathbf{Q}$ are orthonormal, so are the nonzero columns of
$[\mathbf{Q}, \mathbf{Q}']$. The scheme chooses which columns of $\mathbf{Q}'$ are zero. -/
structure IsBasisExtension (Q : Matrix (Fin n) (Fin k) 𝕜) (W Q' : Matrix (Fin n) (Fin b) 𝕜)
    (H : Matrix (Fin k) (Fin b) 𝕜) (R : Matrix (Fin b) (Fin b) 𝕜) : Prop where
  /-- The representation of the input block. -/
  repr : W = Q * H + Q' * R
  /-- The coefficient block against the new columns is upper triangular. -/
  upper : R.BlockTriangular id
  /-- The range is not enlarged: the new columns are combinations of the old basis and the
  input block. -/
  span : ∃ (M : Matrix (Fin k) (Fin b) 𝕜) (T : Matrix (Fin b) (Fin b) 𝕜), Q' = Q * M + W * T
  /-- A zero input column gives a zero output column. -/
  zero_col : ∀ c, W.col c = 0 → Q'.col c = 0
  /-- The coefficient rows at zero columns of the old basis are zero. -/
  coef_zero_left : ∀ j, Q.col j = 0 → H j = 0
  /-- The coefficient rows at zero columns of the new block are zero. -/
  coef_zero_right : ∀ c, Q'.col c = 0 → R c = 0
  /-- Orthonormality on the support is preserved. -/
  orth : gramDefect Q = 0 → gramDefect (Matrix.fromCols Q Q') = 0

variable {Q : Matrix (Fin n) (Fin k) 𝕜} {W Q' : Matrix (Fin n) (Fin b) 𝕜}
  {H : Matrix (Fin k) (Fin b) 𝕜} {R : Matrix (Fin b) (Fin b) 𝕜}

/-- An exact extension spans what the old basis and the input block span: if
$(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$,
then $[\mathbf{Q}, \mathbf{Q}']$ and $[\mathbf{Q}, \mathbf{W}]$ have the same column space. -/
theorem IsBasisExtension.range_eq (h : IsBasisExtension Q W Q' H R) :
    LinearMap.range (Matrix.fromCols Q Q').mulVecLin =
      LinearMap.range (Matrix.fromCols Q W).mulVecLin := by
  obtain ⟨M, T, hQ'⟩ := h.span
  refine le_antisymm (range_le_iff_exists_mul.2 ⟨Matrix.fromBlocks 1 M 0 T, ?_⟩)
    (range_le_iff_exists_mul.2 ⟨Matrix.fromBlocks 1 H 0 R, ?_⟩)
  · rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero, ← hQ']
  · rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero, ← h.repr]

/-- The coefficients of an exact extension against the old basis: if
$(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$ and
the nonzero columns of $\mathbf{Q}$ are orthonormal (its Gram defect on the support vanishes),
then $\mathbf{H} = \mathbf{Q}^{\mathsf{H}}\mathbf{W}$. -/
theorem IsBasisExtension.coef_left_eq (h : IsBasisExtension Q W Q' H R)
    (hQ : gramDefect Q = 0) : H = Qᴴ * W := by
  have h0 := h.orth hQ
  rw [gramDefect_fromCols, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
  obtain ⟨-, h12, -, -⟩ := h0
  have hD : Matrix.diagonal (colSupport Q) * H = H := by
    ext j c
    rw [Matrix.diagonal_mul]
    by_cases hj : Q.col j = 0
    · rw [colSupport_of_col_eq_zero hj, zero_mul, h.coef_zero_left j hj]
      rfl
    · rw [colSupport_of_col_ne_zero hj, one_mul]
  conv_rhs => rw [h.repr]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h12, Matrix.zero_mul, add_zero,
    gramDefect_eq_zero_iff.1 hQ, hD]

/-- The coefficients of an exact extension against the new block: if
$(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$ and
the nonzero columns of $\mathbf{Q}$ are orthonormal (its Gram defect on the support vanishes),
then $\mathbf{R} = \mathbf{Q}'^{\mathsf{H}}\mathbf{W}$. -/
theorem IsBasisExtension.coef_right_eq (h : IsBasisExtension Q W Q' H R)
    (hQ : gramDefect Q = 0) : R = Q'ᴴ * W := by
  have h0 := h.orth hQ
  rw [gramDefect_fromCols, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
  obtain ⟨-, -, h21, h22⟩ := h0
  have hD : Matrix.diagonal (colSupport Q') * R = R := by
    ext j c
    rw [Matrix.diagonal_mul]
    by_cases hj : Q'.col j = 0
    · rw [colSupport_of_col_eq_zero hj, zero_mul, h.coef_zero_right j hj]
      rfl
    · rw [colSupport_of_col_ne_zero hj, one_mul]
  conv_rhs => rw [h.repr]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h21, Matrix.zero_mul, zero_add,
    gramDefect_eq_zero_iff.1 h22, hD]

end Exact

/-! ### The rounded contract -/

section Rounded

variable {n k b : ℕ}

/-- The antecedent of the rounded extension contract: the Gram defect on the support $\mathbf{D}$
of the basis $\mathbf{Q}$, after $b$ more columns each contributing at most $3\mu^2$ to its
squared Frobenius norm, stays within $\eta_0$:
$\sqrt{\|\mathbf{D}\|_{\mathsf{F}}^2 + 3b\mu^2} \le \eta_0$. -/
def ExtensionWindow (η₀ μ : ℝ) (b : ℕ) (Q : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  Real.sqrt (frobNorm (gramDefect Q) ^ 2 + 3 * b * μ ^ 2) ≤ η₀

/-- **The rounded extension of a basis by a block**, with parameters
$(\eta_0, \mu, \varepsilon)$. The coefficient block $\mathbf{R}$ is upper triangular and a zero
column of $\mathbf{W}$ gives a zero column of $\mathbf{Q}'$. If the basis $\mathbf{Q}$ is in the
window `NLAlib.ExtensionWindow` for $(\eta_0, \mu)$ and the block width, then
$\|\mathbf{W} - \mathbf{Q}\mathbf{H} - \mathbf{Q}'\mathbf{R}\|_{\mathsf{F}} \le
\varepsilon\|\mathbf{W}\|_{\mathsf{F}}$, and every column $\mathbf{q}'_c$ of $\mathbf{Q}'$ is
zero or satisfies $\lvert\|\mathbf{q}'_c\|^2 - 1\rvert \le \mu$ and
$\|\mathbf{Q}^{\mathsf{T}}\mathbf{q}'_c\|^2 + \sum_{c' < c} (\mathbf{q}'_{c'} \cdot
\mathbf{q}'_c)^2 \le \mu^2$. The bound on a kept column is absolute: the scheme owns the rank
decision. -/
structure IsBasisExtensionErr (η₀ μ ε : ℝ) (Q : Matrix (Fin n) (Fin k) ℝ)
    (W Q' : Matrix (Fin n) (Fin b) ℝ) (H : Matrix (Fin k) (Fin b) ℝ)
    (R : Matrix (Fin b) (Fin b) ℝ) : Prop where
  /-- The coefficient block against the new columns is upper triangular. -/
  upper : R.BlockTriangular id
  /-- A zero input column gives a zero output column. -/
  zero_col : ∀ c, W.col c = 0 → Q'.col c = 0
  /-- The representation of the input block. -/
  residual : ExtensionWindow η₀ μ b Q → frobNorm (W - Q * H - Q' * R) ≤ ε * frobNorm W
  /-- Every new column is zero, or nearly normalized and nearly orthogonal to the old basis and
  to the earlier new columns. -/
  column : ExtensionWindow η₀ μ b Q → ∀ c, Q'.col c = 0 ∨
    (|‖WithLp.toLp 2 (Q'.col c)‖ ^ 2 - 1| ≤ μ ∧
      ‖WithLp.toLp 2 (Qᵀ *ᵥ Q'.col c)‖ ^ 2 +
        ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 ≤ μ ^ 2)

variable {η₀ μ ε : ℝ} {Q : Matrix (Fin n) (Fin k) ℝ} {W Q' : Matrix (Fin n) (Fin b) ℝ}
  {H : Matrix (Fin k) (Fin b) ℝ} {R : Matrix (Fin b) (Fin b) ℝ}

/-- `NLAlib.IsBasisExtensionErr` is monotone: for $\mu \ge 0$ it survives a smaller window
$\eta_0' \le \eta_0$ and larger parameters $\mu \le \mu'$, $\varepsilon \le \varepsilon'$. -/
theorem IsBasisExtensionErr.mono {η₀' μ' ε' : ℝ} (hE : IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (hμ0 : 0 ≤ μ) (hη : η₀' ≤ η₀) (hμ : μ ≤ μ') (hε : ε ≤ ε') :
    IsBasisExtensionErr η₀' μ' ε' Q W Q' H R := by
  have hw : ExtensionWindow η₀' μ' b Q → ExtensionWindow η₀ μ b Q := fun h => by
    unfold ExtensionWindow at h ⊢
    exact (Real.sqrt_le_sqrt (by gcongr)).trans (h.trans hη)
  refine ⟨hE.upper, hE.zero_col, fun h => ?_, fun h c => ?_⟩
  · exact (hE.residual (hw h)).trans (mul_le_mul_of_nonneg_right hε (frobNorm_nonneg _))
  · rcases hE.column (hw h) c with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨h1.trans hμ, h2.trans (by gcongr)⟩

/-- The exact contract is the rounded one at $(\eta_0, \mu, \varepsilon) = (0, 0, 0)$: an exact
extension $(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ of a real basis $\mathbf{Q}$ by $\mathbf{W}$ is
a rounded extension with all three parameters zero. -/
theorem IsBasisExtension.isBasisExtensionErr (h : IsBasisExtension Q W Q' H R) :
    IsBasisExtensionErr 0 0 0 Q W Q' H R := by
  have hD : ExtensionWindow 0 0 b Q → Qᴴ * Q' = 0 ∧ gramDefect Q' = 0 := fun hw => by
    unfold ExtensionWindow at hw
    have h1 := Real.sqrt_eq_zero'.1 (le_antisymm hw (Real.sqrt_nonneg _))
    have h3 : (3 : ℝ) * b * 0 ^ 2 = 0 := by ring
    rw [h3, add_zero] at h1
    have h2 : gramDefect Q = 0 :=
      frobNorm_eq_zero_iff.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h1 (sq_nonneg _)))
    have h0 := h.orth h2
    rw [gramDefect_fromCols, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
    exact ⟨h0.2.1, h0.2.2.2⟩
  refine ⟨h.upper, h.zero_col, fun _ => ?_, fun hw c => ?_⟩
  · have hres : W - Q * H - Q' * R = 0 := by rw [h.repr, add_sub_cancel_left, sub_self]
    rw [hres, frobNorm_zero, zero_mul]
  · obtain ⟨h12, h22⟩ := hD hw
    by_cases hc : Q'.col c = 0
    · exact Or.inl hc
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← gramDefect_apply_self_of_col_ne_zero hc, h22, Matrix.zero_apply, abs_zero]
      · have hs : ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 = 0 :=
          Finset.sum_eq_zero fun c' hc' => by
            rw [← gramDefect_apply_of_ne (Finset.mem_Iio.1 hc').ne, h22, Matrix.zero_apply]
            exact zero_pow two_ne_zero
        have hv : Qᵀ *ᵥ Q'.col c = 0 := by
          rw [← col_conjTranspose_mul_eq_transpose_mulVec, h12]
          rfl
        rw [hs, hv, WithLp.toLp_zero, norm_zero]
        simp

/-- The contribution of one new column to the loss of orthogonality: if $(\mathbf{Q}',
\mathbf{H}, \mathbf{R})$ is a rounded extension of $\mathbf{Q}$ with parameters
$(\eta_0, \mu, \varepsilon)$ and $\mathbf{Q}$ is in the window, then, with $\mathbf{D}'$ the Gram
defect on the support of $\mathbf{Q}'$, every column $c$ satisfies
$2\|(\mathbf{Q}^{\mathsf{H}}\mathbf{Q}')_{:,c}\|^2 + \mathbf{D}'^2_{c,c} +
2\sum_{c' < c} \mathbf{D}'^2_{c',c} \le 3\mu^2$. -/
theorem IsBasisExtensionErr.column_sq_le (hE : IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (hw : ExtensionWindow η₀ μ b Q) (c : Fin b) :
    2 * ‖WithLp.toLp 2 ((Qᴴ * Q').col c)‖ ^ 2 + (gramDefect Q' c c ^ 2 +
      2 * ∑ c' ∈ Finset.Iio c, gramDefect Q' c' c ^ 2) ≤ 3 * μ ^ 2 := by
  rw [col_conjTranspose_mul_eq_transpose_mulVec]
  by_cases h0 : Q'.col c = 0
  · have hz : ∑ c' ∈ Finset.Iio c, gramDefect Q' c' c ^ 2 = 0 :=
      Finset.sum_eq_zero fun c' _ => by
        rw [gramDefect_apply_of_col_eq_zero_right h0]
        exact zero_pow two_ne_zero
    rw [hz, gramDefect_apply_of_col_eq_zero_right h0, h0, Matrix.mulVec_zero, WithLp.toLp_zero,
      norm_zero]
    nlinarith [sq_nonneg μ]
  · rcases hE.column hw c with h | ⟨h1, h2⟩
    · exact absurd h h0
    · have hd : gramDefect Q' c c ^ 2 ≤ μ ^ 2 := by
        rw [gramDefect_apply_self_of_col_ne_zero h0, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hs : ∑ c' ∈ Finset.Iio c, gramDefect Q' c' c ^ 2 =
          ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 :=
        Finset.sum_congr rfl fun c' hc' => by
          rw [gramDefect_apply_of_ne (Finset.mem_Iio.1 hc').ne]
      rw [hs]
      linarith

/-- **One block step of the loss of orthogonality**: let $\mathbf{D}(\cdot)$ be the Gram defect
on the support, $\mathbf{D}(\mathbf{Q}) = \mathbf{Q}^{\mathsf{T}}\mathbf{Q} -
\operatorname{diag}(\mathbf{s})$ with $s_j = 0$ at a zero column of $\mathbf{Q}$ and $s_j = 1$
otherwise. If $(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is a rounded extension
(`NLAlib.IsBasisExtensionErr`) of the real basis $\mathbf{Q}$ with parameters
$(\eta_0, \mu, \varepsilon)$, $\mathbf{Q}'$ has $b$ columns and $\mathbf{Q}$ is in the window,
$\sqrt{\|\mathbf{D}(\mathbf{Q})\|_{\mathsf{F}}^2 + 3b\mu^2} \le \eta_0$, then
$$\|\mathbf{D}([\mathbf{Q}, \mathbf{Q}'])\|_{\mathsf{F}}^2 \le
\|\mathbf{D}(\mathbf{Q})\|_{\mathsf{F}}^2 + 3b\mu^2\,.$$
No printed source.
Result: basis-extension-gram-defect -/
theorem IsBasisExtensionErr.frobNorm_gramDefect_fromCols_sq_le
    (hE : IsBasisExtensionErr η₀ μ ε Q W Q' H R) (hw : ExtensionWindow η₀ μ b Q) :
    frobNorm (gramDefect (Matrix.fromCols Q Q')) ^ 2 ≤
      frobNorm (gramDefect Q) ^ 2 + 3 * b * μ ^ 2 := by
  have hsym : ∀ i j : Fin b, gramDefect Q' i j ^ 2 = gramDefect Q' j i ^ 2 := fun i j => by
    rw [← (isHermitian_gramDefect Q').apply i j, star_trivial]
  have hsum := (Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hE.column_sq_le hw c).trans_eq
    (show ∑ _c : Fin b, 3 * μ ^ 2 = b * (3 * μ ^ 2) by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [frobNorm_gramDefect_fromCols_sq, frobNorm_sq_eq_sum_col (Qᴴ * Q'),
    frobNorm_sq_eq_sum_sq (gramDefect Q'),
    sum_sum_eq_sum_diag_add_two_mul_sum_Iio (fun i j => gramDefect Q' i j ^ 2) hsym]
  linarith

end Rounded

/-! ### A run of blocks stored in one matrix -/

section Blocks

variable {N : ℕ}

/-- The first $j$ blocks of a matrix $\mathbf{V}$ stored as consecutive blocks of $b$ columns:
its columns $0, \dots, jb - 1$. A column index beyond the width of $\mathbf{V}$ gives a zero
column, which does not change the Gram defect on the support. -/
def blockPrefix (b : ℕ) (V : Matrix m (Fin N) 𝕜) (j : ℕ) : Matrix m (Fin (j * b)) 𝕜 :=
  Matrix.of fun i d => if h : (d : ℕ) < N then V i ⟨d, h⟩ else 0

/-- Block $j$ of a matrix $\mathbf{V}$ stored as consecutive blocks of $b$ columns: its columns
$jb, \dots, jb + b - 1$. A column index beyond the width of $\mathbf{V}$ gives a zero column. -/
def blockCols (b : ℕ) (V : Matrix m (Fin N) 𝕜) (j : ℕ) : Matrix m (Fin b) 𝕜 :=
  Matrix.of fun i c => if h : j * b + (c : ℕ) < N then V i ⟨j * b + c, h⟩ else 0

/-- The prefix of all $q$ blocks of a matrix with $qb$ columns is the matrix. -/
theorem blockPrefix_self {b q : ℕ} (V : Matrix m (Fin (q * b)) 𝕜) : blockPrefix b V q = V := by
  ext i d
  simp [blockPrefix]

/-- The first $j$ blocks of rows of a matrix $\mathbf{C}$ whose rows are stored as consecutive
blocks of $b$ rows: its rows $0, \dots, jb - 1$. A row index beyond the height of $\mathbf{C}$
gives a zero row. -/
def blockRowPrefix (b : ℕ) (C : Matrix (Fin N) κ 𝕜) (j : ℕ) : Matrix (Fin (j * b)) κ 𝕜 :=
  Matrix.of fun d c => if h : (d : ℕ) < N then C ⟨d, h⟩ c else 0

/-- Block $j$ of the rows of a matrix $\mathbf{C}$ whose rows are stored as consecutive blocks of
$b$ rows: its rows $jb, \dots, jb + b - 1$. A row index beyond the height of $\mathbf{C}$ gives a
zero row. -/
def blockRows (b : ℕ) (C : Matrix (Fin N) κ 𝕜) (j : ℕ) : Matrix (Fin b) κ 𝕜 :=
  Matrix.of fun r c => if h : j * b + (r : ℕ) < N then C ⟨j * b + r, h⟩ c else 0

/-- The prefix of all $q$ blocks of rows of a matrix with $qb$ rows is the matrix. -/
theorem blockRowPrefix_self {b q : ℕ} (C : Matrix (Fin (q * b)) κ 𝕜) :
    blockRowPrefix b C q = C := by
  ext d c
  simp [blockRowPrefix]

/-- The identification of the column indices of $j$ blocks of width $b$ followed by one more
block with the column indices of $j + 1$ blocks: the index $d$ of the first $jb$ columns goes to
$d$ and the index $c$ of the last block goes to $jb + c$. -/
def blockSuccEquiv (b j : ℕ) : Fin (j * b) ⊕ Fin b ≃ Fin ((j + 1) * b) :=
  finSumFinEquiv.trans (finCongr (Nat.add_one_mul j b).symm)

/-- The identification `NLAlib.blockSuccEquiv` sends the index $d$ of the first $j$ blocks to
$d$. -/
@[simp]
theorem blockSuccEquiv_inl (b j : ℕ) (d : Fin (j * b)) :
    ((blockSuccEquiv b j (Sum.inl d) : Fin ((j + 1) * b)) : ℕ) = d := by
  simp [blockSuccEquiv]

/-- The identification `NLAlib.blockSuccEquiv` sends the index $c$ of block $j$ to $jb + c$. -/
@[simp]
theorem blockSuccEquiv_inr (b j : ℕ) (c : Fin b) :
    ((blockSuccEquiv b j (Sum.inr c) : Fin ((j + 1) * b)) : ℕ) = j * b + c := by
  simp [blockSuccEquiv]

/-- The prefix of $j + 1$ blocks is the prefix of $j$ blocks followed by block $j$:
$\mathbf{V}_{j+1} = [\mathbf{V}_j, \mathbf{V}^{(j)}]$ after the identification
`NLAlib.blockSuccEquiv` of the column indices. -/
theorem blockPrefix_succ_submatrix (b : ℕ) (V : Matrix m (Fin N) 𝕜) (j : ℕ) :
    (blockPrefix b V (j + 1)).submatrix id (blockSuccEquiv b j) =
      Matrix.fromCols (blockPrefix b V j) (blockCols b V j) := by
  ext i (d | c)
  · simp only [Matrix.submatrix_apply, Matrix.fromCols_apply_inl, blockPrefix, Matrix.of_apply,
      blockSuccEquiv_inl, id_eq]
  · simp only [Matrix.submatrix_apply, Matrix.fromCols_apply_inr, blockPrefix, blockCols,
      Matrix.of_apply, blockSuccEquiv_inr, id_eq]

/-- The prefix of $j + 1$ blocks, written from the prefix of $j$ blocks and block $j$:
$\mathbf{V}_{j+1}$ is $[\mathbf{V}_j, \mathbf{V}^{(j)}]$ with its columns reindexed by the inverse
of `NLAlib.blockSuccEquiv`. -/
theorem blockPrefix_succ (b : ℕ) (V : Matrix m (Fin N) 𝕜) (j : ℕ) :
    blockPrefix b V (j + 1) =
      (Matrix.fromCols (blockPrefix b V j) (blockCols b V j)).submatrix id
        (blockSuccEquiv b j).symm := by
  rw [← blockPrefix_succ_submatrix, Matrix.submatrix_submatrix, Function.comp_id,
    Equiv.self_comp_symm, Matrix.submatrix_id_id]

/-- The first $j + 1$ blocks of rows are the first $j$ blocks of rows above block $j$:
$\mathbf{C}_{j+1} = \begin{bmatrix} \mathbf{C}_j \\ \mathbf{C}^{(j)} \end{bmatrix}$ after the
identification `NLAlib.blockSuccEquiv` of the row indices. -/
theorem blockRowPrefix_succ_submatrix (b : ℕ) (C : Matrix (Fin N) κ 𝕜) (j : ℕ) :
    (blockRowPrefix b C (j + 1)).submatrix (blockSuccEquiv b j) id =
      Matrix.fromRows (blockRowPrefix b C j) (blockRows b C j) := by
  ext (d | r) c
  · simp only [Matrix.submatrix_apply, Matrix.fromRows_apply_inl, blockRowPrefix,
      Matrix.of_apply, blockSuccEquiv_inl, id_eq]
  · simp only [Matrix.submatrix_apply, Matrix.fromRows_apply_inr, blockRowPrefix, blockRows,
      Matrix.of_apply, blockSuccEquiv_inr, id_eq]

/-- The first $j + 1$ blocks of rows, written from the first $j$ blocks of rows and block $j$:
$\mathbf{C}_{j+1}$ is $\begin{bmatrix} \mathbf{C}_j \\ \mathbf{C}^{(j)} \end{bmatrix}$ with its
rows reindexed by the inverse of `NLAlib.blockSuccEquiv`. -/
theorem blockRowPrefix_succ (b : ℕ) (C : Matrix (Fin N) κ 𝕜) (j : ℕ) :
    blockRowPrefix b C (j + 1) =
      (Matrix.fromRows (blockRowPrefix b C j) (blockRows b C j)).submatrix
        (blockSuccEquiv b j).symm id := by
  rw [← blockRowPrefix_succ_submatrix, Matrix.submatrix_submatrix, Function.comp_id,
    Equiv.self_comp_symm, Matrix.submatrix_id_id]

/-- The product of a prefix of blocks of columns with a prefix of blocks of rows, one block at a
time: $\mathbf{V}_{j+1}\mathbf{C}_{j+1} = \mathbf{V}_j\mathbf{C}_j +
\mathbf{V}^{(j)}\mathbf{C}^{(j)}$. -/
theorem blockPrefix_succ_mul_blockRowPrefix_succ {M : ℕ} (b : ℕ) (V : Matrix m (Fin N) 𝕜)
    (C : Matrix (Fin M) κ 𝕜) (j : ℕ) :
    blockPrefix b V (j + 1) * blockRowPrefix b C (j + 1) =
      blockPrefix b V j * blockRowPrefix b C j + blockCols b V j * blockRows b C j := by
  have h := Matrix.submatrix_mul_equiv (blockPrefix b V (j + 1)) (blockRowPrefix b C (j + 1))
    (id : m → m) (blockSuccEquiv b j) (id : κ → κ)
  rw [blockPrefix_succ_submatrix, blockRowPrefix_succ_submatrix, Matrix.fromCols_mul_fromRows,
    Matrix.submatrix_id_id] at h
  exact h.symm

/-- Relabelling the columns of $\mathbf{A}$ by a bijection does not change its column space. -/
theorem range_submatrix_equiv [Fintype ι] [Fintype κ] (A : Matrix m ι 𝕜)
    (e : κ ≃ ι) :
    LinearMap.range (A.submatrix id e).mulVecLin = LinearMap.range A.mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  exact congrArg (Submodule.span 𝕜) (e.surjective.range_comp A.col)

/-- The prefix of $j + 1$ blocks and the prefix of $j$ blocks followed by block $j$ have the same
column space: $\operatorname{range}(\mathbf{V}_{j+1}) =
\operatorname{range}([\mathbf{V}_j, \mathbf{V}^{(j)}])$. -/
theorem range_blockPrefix_succ (b : ℕ) (V : Matrix m (Fin N) 𝕜) (j : ℕ) :
    LinearMap.range (blockPrefix b V (j + 1)).mulVecLin =
      LinearMap.range (Matrix.fromCols (blockPrefix b V j) (blockCols b V j)).mulVecLin := by
  rw [← blockPrefix_succ_submatrix, range_submatrix_equiv]

/-- The Gram defect on the support of the prefix of $j$ blocks followed by block $j$ is that of
the prefix of $j + 1$ blocks, with rows and columns identified by `NLAlib.blockSuccEquiv`. -/
theorem gramDefect_fromCols_blockPrefix_blockCols [Fintype m] (b : ℕ) (V : Matrix m (Fin N) 𝕜)
    (j : ℕ) :
    gramDefect (Matrix.fromCols (blockPrefix b V j) (blockCols b V j)) =
      (gramDefect (blockPrefix b V (j + 1))).submatrix (blockSuccEquiv b j)
        (blockSuccEquiv b j) := by
  rw [← blockPrefix_succ_submatrix, gramDefect_submatrix _ (blockSuccEquiv b j).injective]

/-- The prefix of $j + 1$ blocks is the prefix of $j$ blocks followed by block $j$, up to the
identification of the column indices; in particular the two have the same Gram defect on the
support in the Frobenius norm. -/
theorem frobNorm_gramDefect_blockPrefix_succ [Fintype m] (b : ℕ) (V : Matrix m (Fin N) 𝕜)
    (j : ℕ) :
    frobNorm (gramDefect (blockPrefix b V (j + 1))) =
      frobNorm (gramDefect (Matrix.fromCols (blockPrefix b V j) (blockCols b V j))) := by
  rw [gramDefect_fromCols_blockPrefix_blockCols, frobNorm_submatrix_equiv]

/-- The prefix of $j + 1$ blocks and the prefix of $j$ blocks followed by block $j$ have the same
Gram defect on the support in the spectral norm. -/
theorem specNorm_gramDefect_blockPrefix_succ [Fintype m] (b : ℕ) (V : Matrix m (Fin N) 𝕜)
    (j : ℕ) :
    specNorm (gramDefect (blockPrefix b V (j + 1))) =
      specNorm (gramDefect (Matrix.fromCols (blockPrefix b V j) (blockCols b V j))) := by
  rw [gramDefect_fromCols_blockPrefix_blockCols, specNorm_submatrix_equiv]

/-- The nonzero columns of the prefix of $j + 1$ blocks are orthonormal exactly when those of
the prefix of $j$ blocks followed by block $j$ are: with $\mathbf{D}(\cdot)$ the Gram defect on
the support, $\mathbf{D}(\mathbf{V}_{j+1}) = 0$ if and only if
$\mathbf{D}([\mathbf{V}_j, \mathbf{V}^{(j)}]) = 0$. -/
theorem gramDefect_blockPrefix_succ_eq_zero_iff [Fintype m] (b : ℕ) (V : Matrix m (Fin N) 𝕜)
    (j : ℕ) :
    gramDefect (blockPrefix b V (j + 1)) = 0 ↔
      gramDefect (Matrix.fromCols (blockPrefix b V j) (blockCols b V j)) = 0 := by
  rw [← frobNorm_eq_zero_iff, frobNorm_gramDefect_blockPrefix_succ, frobNorm_eq_zero_iff]

/-- **The loss of orthogonality of a run of block extensions**: let the columns of the real
matrix $\mathbf{V}$ be stored as consecutive blocks of width $b$, with $\mathbf{V}_j$ the first
$j$ blocks, and assume that for every $j < q$ block $j$ is a rounded extension
(`NLAlib.IsBasisExtensionErr`) of $\mathbf{V}_j$ with parameters $(\eta_0, \mu, \varepsilon)$,
for some input block and coefficients. If $\mu \ge 0$ and $\sqrt{3qb}\,\mu \le \eta_0$, then for
every $j \le q$ the Gram defect on the support $\mathbf{D}_j =
\mathbf{V}_j^{\mathsf{T}}\mathbf{V}_j - \operatorname{diag}(\mathbf{s})$ ($s_c = 0$ at a zero
column of $\mathbf{V}_j$, $s_c = 1$ otherwise) satisfies
$$\|\mathbf{D}_j\|_{\mathsf{F}} \le \sqrt{3jb}\,\mu\,.$$
The window of every step follows from the bound of the previous one.
No printed source.
Result: basis-extension-gram-defect -/
theorem frobNorm_gramDefect_le_of_blocks {n b q : ℕ} {η₀ μ ε : ℝ} (V : Matrix (Fin n) (Fin N) ℝ)
    (W : ℕ → Matrix (Fin n) (Fin b) ℝ) (H : ∀ j : ℕ, Matrix (Fin (j * b)) (Fin b) ℝ)
    (R : ℕ → Matrix (Fin b) (Fin b) ℝ) (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * q * b) * μ ≤ η₀)
    (hE : ∀ j < q, IsBasisExtensionErr η₀ μ ε (blockPrefix b V j) (W j) (blockCols b V j)
      (H j) (R j)) {j : ℕ} (hj : j ≤ q) :
    frobNorm (gramDefect (blockPrefix b V j)) ≤ Real.sqrt (3 * j * b) * μ := by
  have hw' : Real.sqrt (3 * q * b * μ ^ 2) ≤ η₀ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hμ]
    exact hw
  have key : ∀ i, i ≤ q →
      frobNorm (gramDefect (blockPrefix b V i)) ^ 2 ≤ 3 * i * b * μ ^ 2 := by
    intro i
    induction i with
    | zero =>
      intro _
      have : IsEmpty (Fin (0 * b)) := by rw [Nat.zero_mul]; infer_instance
      rw [frobNorm_sq_eq_sum]
      simp
    | succ i ih =>
      intro hi
      have hi' := ih (by omega)
      have hq : (i : ℝ) + 1 ≤ q := by exact_mod_cast hi
      have hwin : ExtensionWindow η₀ μ b (blockPrefix b V i) := by
        unfold ExtensionWindow
        refine (Real.sqrt_le_sqrt ?_).trans hw'
        nlinarith [mul_nonneg (sub_nonneg.2 hq)
          (mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (sq_nonneg μ))]
      have hstep := (hE i (by omega)).frobNorm_gramDefect_fromCols_sq_le hwin
      rw [frobNorm_gramDefect_blockPrefix_succ]
      push_cast
      linarith
  have hb2 : (Real.sqrt (3 * j * b) * μ) ^ 2 = 3 * j * b * μ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 ?_
  rw [hb2]
  exact key j hj

end Blocks

end NLAlib
