/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Matrix.Perturbation.BasisExtension

/-!
# Block Golub–Kahan bidiagonalization with full reorthogonalization

Block Golub–Kahan bidiagonalization of $\mathbf{A}$ ($m \times n$) from a start block
$\mathbf{\Omega}$ ($n \times b$), $q$ steps, in exact arithmetic and for an abstract
orthogonalization scheme. With $\operatorname{extend}(\mathbf{Q}, \mathbf{W})$ any exact
extension of a basis by a block (`NLAlib.IsBasisExtension`):
$\mathbf{V}_0, \mathbf{R}_0 = \operatorname{extend}(\emptyset, \mathbf{\Omega})$ and, for
$j < q$, $\mathbf{U}_j = \operatorname{extend}(\mathbf{U}_{<j}, \mathbf{A}\mathbf{V}_j)$ with
coefficients in block column $j$ of $\mathbf{R}$, then
$\mathbf{V}_{j+1} = \operatorname{extend}(\mathbf{V}_{\le j}, \mathbf{A}^{\mathsf{H}}\mathbf{U}_j)$
with coefficients in block column $j$ of $\mathbf{S}$. The scheme is not a function of its input
(it chooses which columns are zero), so the process is the relation `NLAlib.IsBlockGolubKahan`
on the stored matrices, not a recurrence. Design: `docs/design/LowRank-BlockLanczos.md` §3.1.

Encoding. All blocks have width $b$ and are stored side by side: $\mathbf{U}$ is $m \times qb$,
$\mathbf{V}$ is $n \times (q+1)b$, $\mathbf{R}$ is $qb \times qb$ and $\mathbf{S}$ is
$(q+1)b \times qb$. Block $j$ of the columns is `NLAlib.blockCols`, the first $j$ blocks are
`NLAlib.blockPrefix`; for the rows of a coefficient matrix the same two selections are
`NLAlib.blockRows` and `NLAlib.blockRowPrefix`. All four are total (zero outside the matrix), so
no index arithmetic appears in a type beyond the widths $jb$ and $b$. In step $j$ the
coefficients against the old basis are the first $j$ row blocks of block column $j$ of
$\mathbf{R}$ (the first $j + 1$ for $\mathbf{S}$), the coefficients against the new block are row
block $j$ (row block $j + 1$ for $\mathbf{S}$), and the rows below are zero. The empty basis of the
start block is the prefix of zero blocks of $\mathbf{V}$, a matrix with no columns. In the names,
`left` refers to $\mathbf{U}$ and $\mathbf{R}$, `right` to $\mathbf{V}$ and $\mathbf{S}$.

## Main definitions

* `NLAlib.IsBlockGolubKahan`: the process as a relation on the stored matrices.

## Main results

* `NLAlib.IsBlockGolubKahan.gramDefect_left_eq_zero`,
  `NLAlib.IsBlockGolubKahan.gramDefect_right_eq_zero`,
  `NLAlib.IsBlockGolubKahan.gramDefect_blockPrefix_left_eq_zero`,
  `NLAlib.IsBlockGolubKahan.gramDefect_blockPrefix_right_eq_zero`: the nonzero columns of both
  bases are orthonormal.
* `NLAlib.IsBlockGolubKahan.range_blockPrefix_right`,
  `NLAlib.IsBlockGolubKahan.range_blockPrefix_left`: the first blocks span the block Krylov
  spaces of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ and their images under $\mathbf{A}$.
* `NLAlib.IsBlockGolubKahan.mul_conjTranspose_left_eq_rangeProjector`:
  $\mathbf{U}\mathbf{U}^{\mathsf{H}}$ is the projector onto the range of $\mathbf{A}$ times the
  block Krylov matrix.
* `NLAlib.IsBlockGolubKahan.mul_blockPrefix_right_eq`,
  `NLAlib.IsBlockGolubKahan.conjTranspose_mul_left_eq`: the two block relations
  $\mathbf{A}\mathbf{V}_{<q} = \mathbf{U}\mathbf{R}$ and
  $\mathbf{A}^{\mathsf{H}}\mathbf{U} = \mathbf{V}\mathbf{S}$.
* `NLAlib.IsBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rsvd`: the factored output
  $\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ is the randomized SVD approximation at
  the block Krylov matrix, for every input and every exact scheme.
* `NLAlib.IsBlockGolubKahan.coef_left_eq`, `NLAlib.IsBlockGolubKahan.coef_right_eq`,
  `NLAlib.IsBlockGolubKahan.coef_left_eq_conjTranspose_blockRowPrefix`: the coefficient matrices
  are the projected matrices, and $\mathbf{R}$ is the adjoint of the first $qb$ rows of
  $\mathbf{S}$.
* `NLAlib.IsBlockGolubKahan.blockTriangular_left`,
  `NLAlib.IsBlockGolubKahan.coef_left_apply_eq_zero_of_add_lt`,
  `NLAlib.IsBlockGolubKahan.coef_right_apply_eq_zero_of_add_lt`,
  `NLAlib.IsBlockGolubKahan.coef_right_apply_eq_zero_of_lt`: the band structure.
* `NLAlib.exists_isBasisExtension`, `NLAlib.exists_isBlockGolubKahan`: an exact extension and a
  run of the process exist for every input.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The process -/

variable {m n b : ℕ}

/-- Block Golub–Kahan bidiagonalization with full reorthogonalization, in exact arithmetic, as
a relation between the input $\mathbf{A}$ ($m \times n$), $\mathbf{\Omega}$ ($n \times b$), the
number of steps $q$ and the stored output: the left basis $\mathbf{U}$ ($m \times qb$), the right
basis $\mathbf{V}$ ($n \times (q+1)b$), the start coefficients $\mathbf{R}_0$ ($b \times b$) and
the coefficient matrices $\mathbf{R}$ ($qb \times qb$) and $\mathbf{S}$ ($(q+1)b \times qb$), all
stored as consecutive blocks of width $b$. Block $0$ of $\mathbf{V}$ with $\mathbf{R}_0$ is an
exact extension of the empty basis by $\mathbf{\Omega}$. For $j < q$, block $j$ of $\mathbf{U}$
is an exact extension of the first $j$ blocks of $\mathbf{U}$ by $\mathbf{A}\mathbf{V}_j$, with
coefficients the first $j$ row blocks and row block $j$ of block column $j$ of $\mathbf{R}$; and
block $j + 1$ of $\mathbf{V}$ is an exact extension of the first $j + 1$ blocks of $\mathbf{V}$
by $\mathbf{A}^{\mathsf{H}}\mathbf{U}_j$, with coefficients the first $j + 1$ row blocks and row
block $j + 1$ of block column $j$ of $\mathbf{S}$. The remaining rows of both block columns are
zero. Full reorthogonalization is the fact that each block is extended against all earlier
blocks of its side.
Algorithm: block-golub-kahan (specification) -/
structure IsBlockGolubKahan (A : Matrix (Fin m) (Fin n) 𝕜) (Ω : Matrix (Fin n) (Fin b) 𝕜)
    (q : ℕ) (U : Matrix (Fin m) (Fin (q * b)) 𝕜) (V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜)
    (R₀ : Matrix (Fin b) (Fin b) 𝕜) (R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜)
    (S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜) : Prop where
  /-- The start block: block $0$ of $\mathbf{V}$ extends the empty basis by $\mathbf{\Omega}$. -/
  start : IsBasisExtension (blockPrefix b V 0) Ω (blockCols b V 0) 0 R₀
  /-- Step $j$ on the left: block $j$ of $\mathbf{U}$ extends the earlier blocks by
  $\mathbf{A}\mathbf{V}_j$. -/
  left : ∀ j < q, IsBasisExtension (blockPrefix b U j) (A * blockCols b V j) (blockCols b U j)
    (blockRowPrefix b (blockCols b R j) j) (blockRows b (blockCols b R j) j)
  /-- Step $j$ on the right: block $j + 1$ of $\mathbf{V}$ extends the earlier blocks by
  $\mathbf{A}^{\mathsf{H}}\mathbf{U}_j$. -/
  right : ∀ j < q, IsBasisExtension (blockPrefix b V (j + 1)) (Aᴴ * blockCols b U j)
    (blockCols b V (j + 1)) (blockRowPrefix b (blockCols b S j) (j + 1))
    (blockRows b (blockCols b S j) (j + 1))
  /-- Block column $j$ of $\mathbf{R}$ is zero below row block $j$. -/
  left_support : ∀ j < q, ∀ (i : Fin (q * b)) (c : Fin b), (j + 1) * b ≤ (i : ℕ) →
    blockCols b R j i c = 0
  /-- Block column $j$ of $\mathbf{S}$ is zero below row block $j + 1$. -/
  right_support : ∀ j < q, ∀ (i : Fin ((q + 1) * b)) (c : Fin b), (j + 2) * b ≤ (i : ℕ) →
    blockCols b S j i c = 0

/-! ### Existence -/

/-- Every basis has an exact extension by every block: for every $\mathbf{Q}$ and $\mathbf{W}$
with the same number of rows there are $\mathbf{Q}'$, $\mathbf{H}$ and $\mathbf{R}$ such that
$(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$.
No orthonormality of $\mathbf{Q}$ is assumed. -/
theorem exists_isBasisExtension {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) 𝕜)
    (W : Matrix (Fin n) (Fin b) 𝕜) :
    ∃ (Q' : Matrix (Fin n) (Fin b) 𝕜) (H : Matrix (Fin k) (Fin b) 𝕜)
      (R : Matrix (Fin b) (Fin b) 𝕜), IsBasisExtension Q W Q' H R := by
  -- If `gramDefect Q ≠ 0` take `Q' = W`, `H = 0`, `R = diagonal (colSupport W)`
  -- (`mul_diagonal_colSupport`; `orth` is vacuous). Otherwise let `W' = W - Q * (Qᴴ * W)` and take
  -- `Q' = gramSchmidtQ W'`, `H = Qᴴ * W`, `R = gramSchmidtR W'` (import
  -- `NLAlib.Matrix.Factorizations.GramSchmidt`): `gramSchmidtQ_mul_gramSchmidtR` gives `repr`,
  -- `isUpperTriangular_gramSchmidtR` gives `upper`, `range_gramSchmidtQ` with
  -- `range_le_iff_exists_mul` gives `span`, `gramSchmidtQ_col_eq_zero_iff` the zero columns, and
  -- `Qᴴ * W' = 0` (`mul_conjTranspose_mul_self_of_gramDefect_eq_zero`) with
  -- `conjTranspose_gramSchmidtQ_mul_self` gives `orth` through `gramDefect_fromCols`.
  sorry

/-- The process has a run for every input: for every $\mathbf{A}$, $\mathbf{\Omega}$ and $q$
there are $\mathbf{U}$, $\mathbf{V}$, $\mathbf{R}_0$, $\mathbf{R}$, $\mathbf{S}$ related to them by
block Golub–Kahan bidiagonalization with full reorthogonalization in exact arithmetic. -/
theorem exists_isBlockGolubKahan (A : Matrix (Fin m) (Fin n) 𝕜) (Ω : Matrix (Fin n) (Fin b) 𝕜)
    (q : ℕ) :
    ∃ (U : Matrix (Fin m) (Fin (q * b)) 𝕜) (V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜)
      (R₀ : Matrix (Fin b) (Fin b) 𝕜) (R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜)
      (S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜), IsBlockGolubKahan A Ω q U V R₀ R S := by
  -- Induction on `q`. For `q = 0` take `V` from `exists_isBasisExtension` for the empty basis and
  -- `Ω` (reindexed along `Fin b ≃ Fin ((0 + 1) * b)`). For `q + 1`, apply
  -- `exists_isBasisExtension` to `U`, `A * blockCols b V q`, then to `V`,
  -- `Aᴴ * (the new block of U)`, and append the new blocks and coefficient block columns
  -- (`Matrix.fromCols`, `Matrix.fromBlocks` reindexed along `finSumFinEquiv`); the fields for
  -- `j < q` are those of the induction hypothesis because `blockPrefix`, `blockCols`,
  -- `blockRowPrefix` and `blockRows` of the earlier blocks are unchanged.
  sorry

namespace IsBlockGolubKahan

variable {A : Matrix (Fin m) (Fin n) 𝕜} {Ω : Matrix (Fin n) (Fin b) 𝕜} {q : ℕ}
  {U : Matrix (Fin m) (Fin (q * b)) 𝕜} {V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜}
  {R₀ : Matrix (Fin b) (Fin b) 𝕜} {R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜}
  {S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜}

/-! ### Orthonormality on the support -/

/-- The nonzero columns of the first $j \le q$ blocks of the left basis $\mathbf{U}$ of block
Golub–Kahan bidiagonalization in exact arithmetic are orthonormal: their Gram defect on the
support vanishes. -/
theorem gramDefect_blockPrefix_left_eq_zero (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ}
    (hj : j ≤ q) : gramDefect (blockPrefix b U j) = 0 := by
  -- Induction on `j`. The prefix of zero blocks has no columns. For `j + 1`,
  -- `(h.left j _).orth` gives `gramDefect (fromCols (blockPrefix b U j) (blockCols b U j)) = 0`,
  -- and `frobNorm_gramDefect_blockPrefix_succ` with `frobNorm_eq_zero_iff` transfers it to
  -- `blockPrefix b U (j + 1)`.
  sorry

/-- The nonzero columns of the first $j + 1 \le q + 1$ blocks of the right basis $\mathbf{V}$ of
block Golub–Kahan bidiagonalization in exact arithmetic are orthonormal: their Gram defect on
the support vanishes. -/
theorem gramDefect_blockPrefix_right_eq_zero (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ}
    (hj : j ≤ q) : gramDefect (blockPrefix b V (j + 1)) = 0 := by
  -- Induction on `j` as for the left basis: `h.start.orth` (the empty basis has zero Gram
  -- defect) for `j = 0`, `(h.right j _).orth` for the step, each transferred by
  -- `frobNorm_gramDefect_blockPrefix_succ` and `frobNorm_eq_zero_iff`.
  sorry

/-- The nonzero columns of the left basis $\mathbf{U}$ of block Golub–Kahan bidiagonalization in
exact arithmetic are orthonormal: $\mathbf{U}^{\mathsf{H}}\mathbf{U} =
\operatorname{diag}(\mathbf{s})$ with $s_c = 0$ at a zero column and $s_c = 1$ otherwise. -/
theorem gramDefect_left_eq_zero (h : IsBlockGolubKahan A Ω q U V R₀ R S) : gramDefect U = 0 := by
  have h0 := h.gramDefect_blockPrefix_left_eq_zero (le_refl q)
  rwa [blockPrefix_self] at h0

/-- The nonzero columns of the right basis $\mathbf{V}$ of block Golub–Kahan bidiagonalization
in exact arithmetic are orthonormal: $\mathbf{V}^{\mathsf{H}}\mathbf{V} =
\operatorname{diag}(\mathbf{s})$ with $s_c = 0$ at a zero column and $s_c = 1$ otherwise. -/
theorem gramDefect_right_eq_zero (h : IsBlockGolubKahan A Ω q U V R₀ R S) : gramDefect V = 0 := by
  have h0 := h.gramDefect_blockPrefix_right_eq_zero (le_refl q)
  rwa [blockPrefix_self] at h0

/-! ### The Krylov ranges -/

/-- The first $j + 1 \le q + 1$ blocks of the right basis $\mathbf{V}$ of block Golub–Kahan
bidiagonalization in exact arithmetic span the block Krylov space
$\mathcal{K}_{j+1}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}) =
\operatorname{range}[\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{j}\mathbf{\Omega}]$, for every start block
$\mathbf{\Omega}$ and every exact orthogonalization scheme, zero columns included. -/
theorem range_blockPrefix_right (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ} (hj : j ≤ q) :
    LinearMap.range (blockPrefix b V (j + 1)).mulVecLin = blockKrylovSpace (Aᴴ * A) Ω (j + 1) := by
  -- Joint induction on `j` with `range_blockPrefix_left`. The range of `blockPrefix b X (j + 1)`
  -- is that of `fromCols (blockPrefix b X j) (blockCols b X j)` (the reindexing of
  -- `frobNorm_gramDefect_blockPrefix_succ`), which by `IsBasisExtension.range_eq` is the range of
  -- the old prefix plus the range of the input block. `j = 0`: `h.start` and
  -- `blockKrylovSpace_one`. Step: the range of `Aᴴ * blockCols b U j` plus `K (j + 1)` equals
  -- `K (j + 1)` plus the image under `Aᴴ * A` of `K (j + 1)` (the left statement at `j + 1` and at
  -- `j`, with `mulVec_mem_blockKrylovSpace_succ`), which is `K (j + 2)` by
  -- `blockKrylovSpace_succ` and `blockKrylovSpace_mono`.
  sorry

/-- The first $j \le q$ blocks of the left basis $\mathbf{U}$ of block Golub–Kahan
bidiagonalization in exact arithmetic span the image under $\mathbf{A}$ of the block Krylov space
$\mathcal{K}_{j}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}) =
\operatorname{range}[\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{j-1}\mathbf{\Omega}]$ (the zero space for $j = 0$), for
every start block $\mathbf{\Omega}$ and every exact orthogonalization scheme. -/
theorem range_blockPrefix_left (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ} (hj : j ≤ q) :
    LinearMap.range (blockPrefix b U j).mulVecLin =
      (blockKrylovSpace (Aᴴ * A) Ω j).map A.mulVecLin := by
  -- Joint induction on `j` with `range_blockPrefix_right`. `j = 0`: no columns and
  -- `blockKrylovSpace_zero`. Step: by `(h.left j _).range_eq` the range of the first `j + 1`
  -- blocks is the image under `A` of `K j` plus the image of the range of `blockCols b V j`,
  -- that is the image of the range of `blockPrefix b V (j + 1)` (`Submodule.map_sup`,
  -- `LinearMap.range_comp`), which is `K (j + 1)` by the right statement at `j`.
  sorry

/-- The left basis $\mathbf{U}$ of block Golub–Kahan bidiagonalization in exact arithmetic gives
the orthogonal projector onto the range of $\mathbf{A}\mathbf{K}_q$, where
$\mathbf{K}_q = [\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}]$ is the block Krylov matrix:
$\mathbf{U}\mathbf{U}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}\mathbf{K}_q}$. -/
theorem mul_conjTranspose_left_eq_rangeProjector (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    U * Uᴴ = rangeProjector (A * blockKrylovMatrix (Aᴴ * A) Ω q) := by
  have hU := h.range_blockPrefix_left (le_refl q)
  rw [blockPrefix_self] at hU
  rw [mul_conjTranspose_eq_rangeProjector_of_gramDefect_eq_zero h.gramDefect_left_eq_zero,
    rangeProjector_inj, hU, blockKrylovSpace, Matrix.mulVecLin_mul, LinearMap.range_comp]

/-! ### The block relations -/

/-- The first block relation of block Golub–Kahan bidiagonalization in exact arithmetic:
$\mathbf{A}\mathbf{V}_{<q} = \mathbf{U}\mathbf{R}$, where $\mathbf{V}_{<q}$ is the first $q$
blocks of the right basis $\mathbf{V}$, $\mathbf{U}$ the left basis and $\mathbf{R}$ the
coefficient matrix of the left steps. -/
theorem mul_blockPrefix_right_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    A * blockPrefix b V q = U * R := by
  -- Entry `(i, d)` with `d = j * b + c`, `j < q`, `c < b` (`Nat.div_add_mod`): the left side is
  -- entry `(i, c)` of `A * blockCols b V j`, by `(h.left j _).repr` the sum of
  -- `blockPrefix b U j * blockRowPrefix b (blockCols b R j) j` and
  -- `blockCols b U j * blockRows b (blockCols b R j) j`. These are the parts of
  -- `∑ k, U i k * R k d` over `k < j * b` and `j * b ≤ k < (j + 1) * b`
  -- (`Fin.sum_univ_add`-style splitting); the rest vanishes by `h.left_support`.
  sorry

/-- The second block relation of block Golub–Kahan bidiagonalization in exact arithmetic:
$\mathbf{A}^{\mathsf{H}}\mathbf{U} = \mathbf{V}\mathbf{S}$, with $\mathbf{U}$ the left basis,
$\mathbf{V}$ the right basis (all $q + 1$ blocks) and $\mathbf{S}$ the coefficient matrix of the
right steps. -/
theorem conjTranspose_mul_left_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    Aᴴ * U = V * S := by
  -- As `mul_blockPrefix_right_eq`, with `(h.right j _).repr` for block column `j` and
  -- `h.right_support` for the rows from `(j + 2) * b` on.
  sorry

/-- The factored output of block Golub–Kahan bidiagonalization in exact arithmetic is the
randomized SVD approximation at the block Krylov matrix:
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rsvd}(\mathbf{A}, \mathbf{K}_q) = \mathbf{P}_{\mathbf{A}\mathbf{K}_q}\mathbf{A},
\qquad \mathbf{K}_q = [\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}],$$
for every $\mathbf{A}$, every start block $\mathbf{\Omega}$ and every exact orthogonalization
scheme: dependent start columns, rank-deficient $\mathbf{A}$ and breakdown inside the run are
included. -/
theorem mul_conjTranspose_mul_conjTranspose_eq_rsvd (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    U * Sᴴ * Vᴴ = rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q) := by
  rw [rsvd, ← h.mul_conjTranspose_left_eq_rangeProjector, Matrix.mul_assoc U Sᴴ,
    ← Matrix.conjTranspose_mul, ← h.conjTranspose_mul_left_eq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-! ### The coefficients and the band structure -/

/-- The coefficient matrix of the left steps of block Golub–Kahan bidiagonalization in exact
arithmetic is the projected matrix: $\mathbf{R} =
\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V}_{<q}$, with $\mathbf{V}_{<q}$ the first $q$ blocks of
the right basis. The rows of $\mathbf{R}$ at zero columns of $\mathbf{U}$ are zero. -/
theorem coef_left_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    R = Uᴴ * A * blockPrefix b V q := by
  -- `Uᴴ * (A * blockPrefix b V q) = Uᴴ * U * R = diagonal (colSupport U) * R` by
  -- `mul_blockPrefix_right_eq` and `gramDefect_eq_zero_iff` with `gramDefect_left_eq_zero`. Row
  -- `i` of `R` at a zero column `i` of `U` is zero: in block column `j`, by
  -- `(h.left j _).coef_zero_left` if `i < j * b`, `(h.left j _).coef_zero_right` if `i` is in row
  -- block `j`, and `h.left_support` below. Hence `diagonal (colSupport U) * R = R`.
  sorry

/-- The coefficient matrix of the right steps of block Golub–Kahan bidiagonalization in exact
arithmetic is the projected matrix: $\mathbf{S} =
\mathbf{V}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}}\mathbf{U}$. The rows of $\mathbf{S}$ at zero columns
of $\mathbf{V}$ are zero. -/
theorem coef_right_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) : S = Vᴴ * Aᴴ * U := by
  -- As `coef_left_eq`: `Vᴴ * (Aᴴ * U) = Vᴴ * V * S = diagonal (colSupport V) * S` by
  -- `conjTranspose_mul_left_eq` and `gramDefect_right_eq_zero`, and the rows of `S` at zero
  -- columns of `V` vanish by `coef_zero_left`, `coef_zero_right` of `h.right j _` and
  -- `h.right_support`.
  sorry

/-- The two coefficient matrices of block Golub–Kahan bidiagonalization in exact arithmetic
carry the same entries: $\mathbf{R} = \mathbf{S}_{<q}^{\mathsf{H}}$, where $\mathbf{S}_{<q}$ is
the first $q$ row blocks (the first $qb$ rows) of $\mathbf{S}$. -/
theorem coef_left_eq_conjTranspose_blockRowPrefix (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    R = (blockRowPrefix b S q)ᴴ := by
  -- Entrywise from `coef_left_eq` and `coef_right_eq`: for `i`, `d < q * b`,
  -- `R i d = ∑ ∑ star (U k i) * A k l * V l d` and `S d i` (row `d` of `S`, read through
  -- `blockRowPrefix`) is `∑ ∑ star (V l d) * star (A k l) * U k i`; `star_sum`, `star_mul'`.
  sorry

/-- The coefficient matrix $\mathbf{R}$ of the left steps of block Golub–Kahan bidiagonalization
in exact arithmetic is upper triangular. -/
theorem blockTriangular_left (h : IsBlockGolubKahan A Ω q U V R₀ R S) : R.BlockTriangular id := by
  -- Let `d = j * b + c` be the column and `d < i` the row. If `(j + 1) * b ≤ i` the entry is
  -- zero by `h.left_support`; otherwise `i = j * b + r` with `c < r` and the entry is entry
  -- `(r, c)` of `blockRows b (blockCols b R j) j`, zero by `(h.left j _).upper`.
  sorry

/-- The coefficient matrix $\mathbf{S}$ of the right steps of block Golub–Kahan
bidiagonalization in exact arithmetic, with blocks of width $b$, is zero below its $b$-th
subdiagonal: $S_{ic} = 0$ for $i > c + b$. -/
theorem coef_right_apply_eq_zero_of_add_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i : Fin ((q + 1) * b)) (c : Fin (q * b)) (hic : (c : ℕ) + b < (i : ℕ)) : S i c = 0 := by
  -- Let `c = j * b + c'`. If `(j + 2) * b ≤ i` the entry is zero by `h.right_support`; otherwise
  -- `i = (j + 1) * b + r` with `c' < r` and the entry is entry `(r, c')` of
  -- `blockRows b (blockCols b S j) (j + 1)`, zero by `(h.right j _).upper`.
  sorry

/-- The coefficient matrix $\mathbf{S}$ of the right steps of block Golub–Kahan
bidiagonalization in exact arithmetic is zero above its diagonal: $S_{ic} = 0$ for $i < c$.
With the vanishing below the $b$-th subdiagonal, $\mathbf{S}^{\mathsf{H}}$ is zero outside the
band $0 \le \text{column} - \text{row} \le b$; for $b = 1$ it is upper bidiagonal. -/
theorem coef_right_apply_eq_zero_of_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i : Fin ((q + 1) * b)) (c : Fin (q * b)) (hic : (i : ℕ) < (c : ℕ)) : S i c = 0 := by
  -- With `i' : Fin (q * b)` of value `i`, `coef_left_eq_conjTranspose_blockRowPrefix` gives
  -- `R c i' = star (S i c)`, and `R c i' = 0` by `blockTriangular_left` since `i' < c`.
  sorry

/-- The coefficient matrix $\mathbf{R}$ of the left steps of block Golub–Kahan bidiagonalization
in exact arithmetic, with blocks of width $b$, is zero above its $b$-th superdiagonal:
$R_{ic} = 0$ for $c > i + b$. With upper triangularity, $\mathbf{R}$ is zero outside the band
$0 \le \text{column} - \text{row} \le b$. -/
theorem coef_left_apply_eq_zero_of_add_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i c : Fin (q * b)) (hic : (i : ℕ) + b < (c : ℕ)) : R i c = 0 := by
  -- `coef_left_eq_conjTranspose_blockRowPrefix` gives `R i c = star (S c' i)` with
  -- `c' : Fin ((q + 1) * b)` of value `c`, zero by `coef_right_apply_eq_zero_of_add_lt`.
  sorry

end IsBlockGolubKahan

end NLAlib
