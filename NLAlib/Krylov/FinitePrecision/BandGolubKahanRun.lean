/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.BandGolubKahan
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Finite-precision runs of block Golub–Kahan bidiagonalization

`NLAlib.IsBlockGolubKahanErr` is the rounded form of `NLAlib.IsBlockGolubKahan`: the same stored
matrices $\mathbf{U}$ ($m \times qb$), $\mathbf{V}$ ($n \times (q+1)b$), $\mathbf{R}_0$,
$\mathbf{R}$, $\mathbf{S}$ in the same block encoding, every block a rounded extension
(`NLAlib.IsBasisExtensionErr`, parameters $\eta_0$, $\mu$, $\varepsilon$) of the earlier blocks
of its side by a computed product. The computed products $\mathbf{P}_j \approx
\mathbf{A}\mathbf{V}_j$ and $\mathbf{P}_j' \approx \mathbf{A}^{\mathsf{T}}\mathbf{U}_j$ are not
stored, so they are quantified inside the predicate; their error is bounded column by column
with the parameter $\varepsilon_{\mathrm{mv}}$, so that a zero basis column has a zero product.
The statements are pure matrix facts in $(\eta_0, \mu, \varepsilon, \varepsilon_{\mathrm{mv}})$,
for every orthogonalization scheme, under the window $\sqrt{3(q+1)b}\,\mu \le \eta_0$.
Design: `docs/design/LowRank-BlockLanczos.md` §4.3.

## Main definitions

* `NLAlib.IsBlockGolubKahanErr`: the rounded process as a relation on the stored matrices.

## Main results

* `NLAlib.IsBlockGolubKahanErr.frobNorm_gramDefect_left_le`,
  `NLAlib.IsBlockGolubKahanErr.frobNorm_gramDefect_right_le`: orthogonality of both bases on the
  nonzero columns.
* `NLAlib.IsBlockGolubKahanErr.card_filter_col_left_ne_zero_le`,
  `NLAlib.IsBlockGolubKahanErr.card_filter_col_right_ne_zero_le`: the number of nonzero columns.
* `NLAlib.IsBlockGolubKahanErr.frobNorm_mul_blockPrefix_sub_mul_le`,
  `NLAlib.IsBlockGolubKahanErr.frobNorm_transpose_mul_sub_mul_le`: the two residual relations.
* `NLAlib.IsBlockGolubKahanErr.specNorm_sub_mul_transpose_mul_transpose_le`,
  `NLAlib.IsBlockGolubKahanErr.frobNorm_sub_mul_transpose_mul_transpose_le`: the forward bound
  for the returned factors against the projection onto the computed left range.
* `NLAlib.IsBlockGolubKahan.isBlockGolubKahanErr`: an exact run is a rounded run with all
  parameters zero.
* `NLAlib.specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect`,
  `NLAlib.frobNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect`,
  `NLAlib.specNorm_le_sqrt_of_specNorm_gramDefect_le`,
  `NLAlib.frobNorm_le_sqrt_of_specNorm_gramDefect_le`: a basis with small Gram defect on the
  support is close to a partial isometry.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-! ### A basis with small Gram defect on the support -/

section GramDefect

variable {𝕜 : Type*} [RCLike 𝕜] {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]

/-- For every matrix $\mathbf{Q}$, with zero columns allowed, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$
differs from the orthogonal projector $\mathbf{P}_{\mathbf{Q}}$ onto the column space of
$\mathbf{Q}$ by at most the Gram defect on the support $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column,
$s_j = 1$ otherwise): $\|\mathbf{Q}\mathbf{Q}^{\mathsf{H}} - \mathbf{P}_{\mathbf{Q}}\|_2 \le
\|\mathbf{D}\|_2$. -/
theorem specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect (Q : Matrix m ι 𝕜) :
    specNorm (Q * Qᴴ - rangeProjector Q) ≤ specNorm (gramDefect Q) := by
  -- Let `Qe` be the nonzero columns (`Q.submatrix id e`, `e` the inclusion of the subtype):
  -- `Q * Qᴴ = Qe * Qeᴴ` and the ranges agree, so `rangeProjector Q = rangeProjector Qe`
  -- (`rangeProjector_inj`). With a singular value decomposition of `Qe`, the difference is
  -- unitarily similar to the diagonal of `σ i ^ 2 - 1` over the nonzero singular values, and
  -- these are eigenvalues of `Qeᴴ * Qe - 1`; conclude by
  -- `specNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect`.
  sorry

/-- For every matrix $\mathbf{Q}$, with zero columns allowed, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$
differs from the orthogonal projector $\mathbf{P}_{\mathbf{Q}}$ onto the column space of
$\mathbf{Q}$ by at most the Gram defect on the support $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column,
$s_j = 1$ otherwise), in the Frobenius norm: $\|\mathbf{Q}\mathbf{Q}^{\mathsf{H}} -
\mathbf{P}_{\mathbf{Q}}\|_{\mathsf{F}} \le \|\mathbf{D}\|_{\mathsf{F}}$. -/
theorem frobNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect (Q : Matrix m ι 𝕜) :
    frobNorm (Q * Qᴴ - rangeProjector Q) ≤ frobNorm (gramDefect Q) := by
  -- As the spectral form: the squared Frobenius norm of the difference is the sum of
  -- `(σ i ^ 2 - 1) ^ 2` over the nonzero singular values of the nonzero columns `Qe`, at most
  -- the sum over all eigenvalues of `Qeᴴ * Qe - 1`; conclude by
  -- `frobNorm_submatrix_conjTranspose_mul_self_sub_one_le_gramDefect`.
  sorry

/-- A basis with small Gram defect on the support has spectral norm close to one: if
$\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a
zero column of $\mathbf{Q}$, $s_j = 1$ otherwise) satisfies $\|\mathbf{D}\|_2 \le \eta$, then
$\|\mathbf{Q}\|_2 \le \sqrt{1 + \eta}$. -/
theorem specNorm_le_sqrt_of_specNorm_gramDefect_le {Q : Matrix m ι 𝕜} {η : ℝ}
    (hQ : specNorm (gramDefect Q) ≤ η) : specNorm Q ≤ Real.sqrt (1 + η) := by
  -- As `specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le`:
  -- `specNorm Q ^ 2 = specNorm (Qᴴ * Q)` (`specNorm_conjTranspose_mul_self`), and
  -- `Qᴴ * Q = gramDefect Q + diagonal (colSupport Q)` with the diagonal of entries `0` and `1` of
  -- spectral norm at most `1`.
  sorry

/-- A basis with small Gram defect on the support has Frobenius norm at most the square root of
its number of columns, nearly: if $\mathbf{Q}$ has $k$ columns and $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column of
$\mathbf{Q}$, $s_j = 1$ otherwise) satisfies $\|\mathbf{D}\|_2 \le \eta$, then
$\|\mathbf{Q}\|_{\mathsf{F}} \le \sqrt{k(1 + \eta)}$. -/
theorem frobNorm_le_sqrt_of_specNorm_gramDefect_le {Q : Matrix m ι 𝕜} {η : ℝ}
    (hQ : specNorm (gramDefect Q) ≤ η) :
    frobNorm Q ≤ Real.sqrt (Fintype.card ι * (1 + η)) := by
  -- As `frobNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le`: `frobNorm Q ^ 2` is the real
  -- part of the trace of `Qᴴ * Q` (`frobNorm_sq_eq_re_trace`), and each diagonal entry is
  -- `colSupport Q j` plus an entry of `gramDefect Q`, at most `1 + η` by
  -- `norm_apply_le_specNorm`.
  sorry

end GramDefect

/-! ### The rounded process -/

variable {m n b : ℕ}

/-- Block Golub–Kahan bidiagonalization with full reorthogonalization in rounded arithmetic, as
a relation between the input $\mathbf{A}$ ($m \times n$), $\mathbf{\Omega}$ ($n \times b$), the
number of steps $q$ and the stored output $\mathbf{U}$ ($m \times qb$), $\mathbf{V}$
($n \times (q+1)b$), $\mathbf{R}_0$ ($b \times b$), $\mathbf{R}$ ($qb \times qb$), $\mathbf{S}$
($(q+1)b \times qb$), stored as consecutive blocks of width $b$, with parameters
$(\eta_0, \mu, \varepsilon)$ of the orthogonalization scheme and $\varepsilon_{\mathrm{mv}}$ of
the products. Block $0$ of $\mathbf{V}$ with $\mathbf{R}_0$ is a rounded extension of the empty
basis by $\mathbf{\Omega}$. For $j < q$ there is a computed product $\mathbf{P}$ with
$\|(\mathbf{P} - \mathbf{A}\mathbf{V}_j)\mathbf{e}_c\| \le \varepsilon_{\mathrm{mv}}
\|\mathbf{A}\|_2\|\mathbf{V}_j\mathbf{e}_c\|$ for every column $c$, such that block $j$ of
$\mathbf{U}$ is a rounded extension of the first $j$ blocks of $\mathbf{U}$ by $\mathbf{P}$, with
coefficients the first $j$ row blocks and row block $j$ of block column $j$ of $\mathbf{R}$; and
a computed product $\mathbf{P}'$ with $\|(\mathbf{P}' - \mathbf{A}^{\mathsf{T}}\mathbf{U}_j)
\mathbf{e}_c\| \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2\|\mathbf{U}_j\mathbf{e}_c\|$ for
every column $c$, such that block $j + 1$ of $\mathbf{V}$ is a rounded extension of the first
$j + 1$ blocks of $\mathbf{V}$ by $\mathbf{P}'$, with coefficients the first $j + 1$ row blocks
and row block $j + 1$ of block column $j$ of $\mathbf{S}$. The remaining rows of both block
columns are zero.
Algorithm: block-golub-kahan (run model) -/
structure IsBlockGolubKahanErr (η₀ μ ε εmv : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (Ω : Matrix (Fin n) (Fin b) ℝ) (q : ℕ) (U : Matrix (Fin m) (Fin (q * b)) ℝ)
    (V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ) (R₀ : Matrix (Fin b) (Fin b) ℝ)
    (R : Matrix (Fin (q * b)) (Fin (q * b)) ℝ)
    (S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) ℝ) : Prop where
  /-- The start block: block $0$ of $\mathbf{V}$ extends the empty basis by $\mathbf{\Omega}$. -/
  start : IsBasisExtensionErr η₀ μ ε (blockPrefix b V 0) Ω (blockCols b V 0) 0 R₀
  /-- Step $j$ on the left: block $j$ of $\mathbf{U}$ extends the earlier blocks by a computed
  product $\mathbf{P} \approx \mathbf{A}\mathbf{V}_j$. -/
  left : ∀ j < q, ∃ P : Matrix (Fin m) (Fin b) ℝ,
    (∀ c, ‖WithLp.toLp 2 ((P - A * blockCols b V j).col c)‖ ≤
      εmv * specNorm A * ‖WithLp.toLp 2 ((blockCols b V j).col c)‖) ∧
    IsBasisExtensionErr η₀ μ ε (blockPrefix b U j) P (blockCols b U j)
      (blockRowPrefix b (blockCols b R j) j) (blockRows b (blockCols b R j) j)
  /-- Step $j$ on the right: block $j + 1$ of $\mathbf{V}$ extends the earlier blocks by a
  computed product $\mathbf{P}' \approx \mathbf{A}^{\mathsf{T}}\mathbf{U}_j$. -/
  right : ∀ j < q, ∃ P : Matrix (Fin n) (Fin b) ℝ,
    (∀ c, ‖WithLp.toLp 2 ((P - Aᵀ * blockCols b U j).col c)‖ ≤
      εmv * specNorm A * ‖WithLp.toLp 2 ((blockCols b U j).col c)‖) ∧
    IsBasisExtensionErr η₀ μ ε (blockPrefix b V (j + 1)) P (blockCols b V (j + 1))
      (blockRowPrefix b (blockCols b S j) (j + 1)) (blockRows b (blockCols b S j) (j + 1))
  /-- Block column $j$ of $\mathbf{R}$ is zero below row block $j$. -/
  left_support : ∀ j < q, ∀ (i : Fin (q * b)) (c : Fin b), (j + 1) * b ≤ (i : ℕ) →
    blockCols b R j i c = 0
  /-- Block column $j$ of $\mathbf{S}$ is zero below row block $j + 1$. -/
  right_support : ∀ j < q, ∀ (i : Fin ((q + 1) * b)) (c : Fin b), (j + 2) * b ≤ (i : ℕ) →
    blockCols b S j i c = 0

variable {η₀ μ ε εmv : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {Ω : Matrix (Fin n) (Fin b) ℝ} {q : ℕ}
  {U : Matrix (Fin m) (Fin (q * b)) ℝ} {V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ}
  {R₀ : Matrix (Fin b) (Fin b) ℝ} {R : Matrix (Fin (q * b)) (Fin (q * b)) ℝ}
  {S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) ℝ}

/-- An exact run is a rounded run with all parameters zero: if real $\mathbf{U}$, $\mathbf{V}$,
$\mathbf{R}_0$, $\mathbf{R}$, $\mathbf{S}$ are related to $\mathbf{A}$, $\mathbf{\Omega}$, $q$ by
block Golub–Kahan bidiagonalization in exact arithmetic, they are related by the rounded process
with $\eta_0 = \mu = \varepsilon = \varepsilon_{\mathrm{mv}} = 0$, the computed products being the
exact ones. -/
theorem IsBlockGolubKahan.isBlockGolubKahanErr (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    IsBlockGolubKahanErr 0 0 0 0 A Ω q U V R₀ R S := by
  refine ⟨h.start.isBasisExtensionErr,
    fun j hj => ⟨A * blockCols b V j, fun c => ?_, (h.left j hj).isBasisExtensionErr⟩,
    fun j hj => ⟨Aᵀ * blockCols b U j, fun c => ?_, ?_⟩, h.left_support, h.right_support⟩
  · rw [sub_self, zero_mul, zero_mul]
    exact (by simp : ‖WithLp.toLp 2 (0 : Fin m → ℝ)‖ = 0).le
  · rw [sub_self, zero_mul, zero_mul]
    exact (by simp : ‖WithLp.toLp 2 (0 : Fin n → ℝ)‖ = 0).le
  · have h0 := (h.right j hj).isBasisExtensionErr
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h0

namespace IsBlockGolubKahanErr

/-! ### Orthogonality on the support -/

/-- Orthogonality of the computed left basis on its nonzero columns. Let $\mathbf{U}$
($qb$ columns) be the left basis of a rounded run of block Golub–Kahan bidiagonalization with
scheme parameters $(\eta_0, \mu, \varepsilon)$, and let $\mathbf{D} =
\mathbf{U}^{\mathsf{T}}\mathbf{U} - \operatorname{diag}(\mathbf{s})$ be its Gram defect on the
support ($s_c = 0$ at a zero column, $s_c = 1$ otherwise). If $\mu \ge 0$ and
$\sqrt{3qb}\,\mu \le \eta_0$ then $\|\mathbf{D}\|_{\mathsf{F}} \le \sqrt{3qb}\,\mu$. -/
theorem frobNorm_gramDefect_left_le (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S)
    (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * q * b) * μ ≤ η₀) :
    frobNorm (gramDefect U) ≤ Real.sqrt (3 * q * b) * μ := by
  choose P _ hE using h.left
  have h0 := frobNorm_gramDefect_le_of_blocks U (fun j => if hj : j < q then P j hj else 0)
    (fun j => blockRowPrefix b (blockCols b R j) j) (fun j => blockRows b (blockCols b R j) j)
    hμ hw (fun j hj => by simp only [dif_pos hj]; exact hE j hj) (le_refl q)
  rwa [blockPrefix_self] at h0

/-- Orthogonality of the computed right basis on its nonzero columns. Let $\mathbf{V}$
($(q+1)b$ columns) be the right basis of a rounded run of block Golub–Kahan bidiagonalization
with scheme parameters $(\eta_0, \mu, \varepsilon)$, and let $\mathbf{D} =
\mathbf{V}^{\mathsf{T}}\mathbf{V} - \operatorname{diag}(\mathbf{s})$ be its Gram defect on the
support ($s_c = 0$ at a zero column, $s_c = 1$ otherwise). If $\mu \ge 0$ and
$\sqrt{3(q+1)b}\,\mu \le \eta_0$ then $\|\mathbf{D}\|_{\mathsf{F}} \le \sqrt{3(q+1)b}\,\mu$. -/
theorem frobNorm_gramDefect_right_le (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S)
    (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (gramDefect V) ≤ Real.sqrt (3 * (q + 1 : ℕ) * b) * μ := by
  choose P _ hE using h.right
  have h0 := frobNorm_gramDefect_le_of_blocks (q := q + 1) V
    (fun j => match j with
      | 0 => Ω
      | j + 1 => if hj : j < q then P j hj else 0)
    (fun j => match j with
      | 0 => 0
      | j + 1 => blockRowPrefix b (blockCols b S j) (j + 1))
    (fun j => match j with
      | 0 => R₀
      | j + 1 => blockRows b (blockCols b S j) (j + 1))
    hμ hw (fun j hj => by
      rcases j with _ | j
      · exact h.start
      · simp only [dif_pos (Nat.lt_of_succ_lt_succ hj)]
        exact hE j (Nat.lt_of_succ_lt_succ hj)) (le_refl (q + 1))
  rwa [blockPrefix_self] at h0

/-- The computed left basis has at most $m$ nonzero columns: if $\mathbf{U}$ ($m$ rows) is the
left basis of a rounded run of block Golub–Kahan bidiagonalization with scheme parameters
$(\eta_0, \mu, \varepsilon)$, $\mu \ge 0$ and $\sqrt{3qb}\,\mu \le \eta_0 < 1$, then the number of
nonzero columns of $\mathbf{U}$ is at most $m$. -/
theorem card_filter_col_left_ne_zero_le [DecidablePred fun j => U.col j ≠ 0]
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * q * b) * μ ≤ η₀) (hη : η₀ < 1) :
    (Finset.univ.filter fun j => U.col j ≠ 0).card ≤ m := by
  have hU := (specNorm_gramDefect_le_frobNorm U).trans
    ((h.frobNorm_gramDefect_left_le hμ hw).trans hw)
  simpa using card_filter_col_ne_zero_le (lt_of_le_of_lt hU hη)

/-- The computed right basis has at most $n$ nonzero columns: if $\mathbf{V}$ ($n$ rows) is the
right basis of a rounded run of block Golub–Kahan bidiagonalization with scheme parameters
$(\eta_0, \mu, \varepsilon)$, $\mu \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0 < 1$, then the
number of nonzero columns of $\mathbf{V}$ is at most $n$. -/
theorem card_filter_col_right_ne_zero_le [DecidablePred fun j => V.col j ≠ 0]
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) (hη : η₀ < 1) :
    (Finset.univ.filter fun j => V.col j ≠ 0).card ≤ n := by
  have hV := (specNorm_gramDefect_le_frobNorm V).trans
    ((h.frobNorm_gramDefect_right_le hμ hw).trans hw)
  simpa using card_filter_col_ne_zero_le (lt_of_le_of_lt hV hη)

/-! ### The residual relations -/

/-- The first residual relation of a rounded run of block Golub–Kahan bidiagonalization with
scheme parameters $(\eta_0, \mu, \varepsilon)$ and product parameter
$\varepsilon_{\mathrm{mv}}$, $q$ steps and block width $b$. With $\mathbf{V}_{<q}$ the first $q$
blocks of the right basis, $\mathbf{U}$ the left basis and $\mathbf{R}$ the stored coefficients:
if $\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A}\mathbf{V}_{<q} - \mathbf{U}\mathbf{R}\|_{\mathsf{F}} \le
\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})\bigr)
\sqrt{qb(1 + \eta_0)}\,\|\mathbf{A}\|_2.$$ -/
theorem frobNorm_mul_blockPrefix_sub_mul_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hmv : 0 ≤ εmv) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (A * blockPrefix b V q - U * R) ≤
      (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by
  -- Block column `j < q` of the residual is `(A * Vj - P) + (P - Uj' * H - Uj * R')` with `P` the
  -- computed product of `h.left j _`, `Vj = blockCols b V j`, `Uj' = blockPrefix b U j`,
  -- `Uj = blockCols b U j` (`h.left_support`, as in `IsBlockGolubKahan.mul_blockPrefix_right_eq`).
  -- The first term is at most `εmv * specNorm A * frobNorm Vj` (columns,
  -- `frobNorm_sq_eq_sum_col`); the second at most `ε * frobNorm P` by the residual clause, whose
  -- window follows from `frobNorm_gramDefect_le_of_blocks` as in its proof, and
  -- `frobNorm P ≤ (1 + εmv) * specNorm A * frobNorm Vj` (`frobNorm_mul_le_specNorm_mul_frobNorm`).
  -- Sum the squares over `j`: the squares of `frobNorm Vj` add to
  -- `frobNorm (blockPrefix b V q) ^ 2 ≤ q * b * (1 + η₀)`, by
  -- `frobNorm_le_sqrt_of_specNorm_gramDefect_le` and `frobNorm_gramDefect_le_of_blocks`.
  sorry

/-- The second residual relation of a rounded run of block Golub–Kahan bidiagonalization with
scheme parameters $(\eta_0, \mu, \varepsilon)$ and product parameter
$\varepsilon_{\mathrm{mv}}$, $q$ steps and block width $b$. With $\mathbf{U}$ the left basis,
$\mathbf{V}$ the right basis (all $q + 1$ blocks) and $\mathbf{S}$ the stored coefficients: if
$\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A}^{\mathsf{T}}\mathbf{U} - \mathbf{V}\mathbf{S}\|_{\mathsf{F}} \le
\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})\bigr)
\sqrt{qb(1 + \eta_0)}\,\|\mathbf{A}\|_2.$$ -/
theorem frobNorm_transpose_mul_sub_mul_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hmv : 0 ≤ εmv) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (Aᵀ * U - V * S) ≤
      (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by
  -- As `frobNorm_mul_blockPrefix_sub_mul_le` with `h.right j _` and `h.right_support`; the window
  -- of step `j` is `3 * (j + 2) * b * μ ^ 2 ≤ 3 * (q + 1) * b * μ ^ 2`, `specNorm_transpose`
  -- gives `specNorm Aᵀ = specNorm A`, and the squares of the block norms add to
  -- `frobNorm U ^ 2 ≤ q * b * (1 + η₀)` by `frobNorm_gramDefect_left_le`.
  sorry

/-! ### The forward bound -/

/-- The forward bound for the factors returned by a rounded run of block Golub–Kahan
bidiagonalization, in the spectral norm. Let $\mathbf{U}$, $\mathbf{V}$, $\mathbf{S}$ be the
stored bases and coefficients of a run of $q$ steps with block width $b$, scheme parameters
$(\eta_0, \mu, \varepsilon)$ and product parameter $\varepsilon_{\mathrm{mv}}$, and
$\mathbf{P}_{\mathbf{U}}$ the orthogonal projector onto the range of $\mathbf{U}$. If
$\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}\|_2 \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A}\|_2 + \Bigl(\sqrt{3qb}\,\mu +
\sqrt{1 + \eta_0}\,\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})
\bigr)\sqrt{qb(1 + \eta_0)}\Bigr)\|\mathbf{A}\|_2.$$
The returned factors are as accurate as the projection of $\mathbf{A}$ onto the computed left
range, up to the loss of orthogonality and the residual of the second relation. -/
theorem specNorm_sub_mul_transpose_mul_transpose_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hmv : 0 ≤ εmv) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    specNorm (A - U * Sᵀ * Vᵀ) ≤ specNorm ((1 - rangeProjector U) * A) +
      (Real.sqrt (3 * q * b) * μ + Real.sqrt (1 + η₀) *
        ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)))) * specNorm A := by
  -- `A - U * Sᵀ * Vᵀ = (1 - rangeProjector U) * A + (rangeProjector U - U * Uᵀ) * A +
  -- U * (Aᵀ * U - V * S)ᵀ`. Second term: `specNorm_mul_le`,
  -- `specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect`,
  -- `specNorm_gramDefect_le_frobNorm` and `frobNorm_gramDefect_left_le` (window for `q` blocks
  -- from `hw` by `Real.sqrt_le_sqrt`). Third term: `specNorm_mul_le`,
  -- `specNorm_le_sqrt_of_specNorm_gramDefect_le` (`specNorm U ≤ √(1 + η₀)`),
  -- `specNorm_le_frobNorm`, `frobNorm_transpose` and `frobNorm_transpose_mul_sub_mul_le`.
  sorry

/-- The forward bound for the factors returned by a rounded run of block Golub–Kahan
bidiagonalization, in the Frobenius norm. Let $\mathbf{U}$, $\mathbf{V}$, $\mathbf{S}$ be the
stored bases and coefficients of a run of $q$ steps with block width $b$, scheme parameters
$(\eta_0, \mu, \varepsilon)$ and product parameter $\varepsilon_{\mathrm{mv}}$, and
$\mathbf{P}_{\mathbf{U}}$ the orthogonal projector onto the range of $\mathbf{U}$. If
$\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}\|_{\mathsf{F}} \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A}\|_{\mathsf{F}} + \Bigl(\sqrt{3qb}\,\mu +
\sqrt{1 + \eta_0}\,\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})
\bigr)\sqrt{qb(1 + \eta_0)}\Bigr)\|\mathbf{A}\|_2.$$ -/
theorem frobNorm_sub_mul_transpose_mul_transpose_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hmv : 0 ≤ εmv) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (A - U * Sᵀ * Vᵀ) ≤ frobNorm ((1 - rangeProjector U) * A) +
      (Real.sqrt (3 * q * b) * μ + Real.sqrt (1 + η₀) *
        ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)))) * specNorm A := by
  -- The decomposition of `specNorm_sub_mul_transpose_mul_transpose_le`. Second term:
  -- `frobNorm_mul_le_frobNorm_mul_specNorm` and
  -- `frobNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect` with
  -- `frobNorm_gramDefect_left_le`. Third term: `frobNorm_mul_le_specNorm_mul_frobNorm`,
  -- `specNorm_le_sqrt_of_specNorm_gramDefect_le`, `frobNorm_transpose` and
  -- `frobNorm_transpose_mul_sub_mul_le`.
  sorry

end IsBlockGolubKahanErr

end NLAlib
