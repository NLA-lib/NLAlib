/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.Matrix.Factorizations.GramSchmidt
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

/-! ### Entries and blocks of a matrix stored as consecutive blocks -/

section Blocks

variable {ι κ : Type*} {N : ℕ}

/-- Entry $(i, c)$ of block $j$ of the columns of $\mathbf{V}$ is entry $(i, jb + c)$ of
$\mathbf{V}$. -/
private theorem blockCols_apply_of_eq (V : Matrix ι (Fin N) 𝕜) (i : ι) {j : ℕ} {c : Fin b}
    {d : Fin N} (h : j * b + (c : ℕ) = d) : blockCols b V j i c = V i d := by
  have hlt : j * b + (c : ℕ) < N := by rw [h]; exact d.isLt
  change (if h' : j * b + (c : ℕ) < N then V i ⟨j * b + c, h'⟩ else 0) = V i d
  rw [dif_pos hlt]
  exact congrArg (V i) (Fin.ext h)

/-- Entry $(r, c)$ of block $j$ of the rows of $\mathbf{C}$ is entry $(jb + r, c)$ of
$\mathbf{C}$. -/
private theorem blockRows_apply_of_eq (C : Matrix (Fin N) κ 𝕜) {j : ℕ} {r : Fin b} {i : Fin N}
    (h : j * b + (r : ℕ) = i) (c : κ) : blockRows b C j r c = C i c := by
  have hlt : j * b + (r : ℕ) < N := by rw [h]; exact i.isLt
  change (if h' : j * b + (r : ℕ) < N then C ⟨j * b + r, h'⟩ c else 0) = C i c
  rw [dif_pos hlt]
  exact congrFun (congrArg C (Fin.ext h)) c

/-- Entry $(i, d)$ of the first $j$ blocks of the columns of $\mathbf{V}$ is entry $(i, d)$ of
$\mathbf{V}$. -/
private theorem blockPrefix_apply_of_eq (V : Matrix ι (Fin N) 𝕜) (i : ι) {j : ℕ}
    {d : Fin (j * b)} {d' : Fin N} (h : (d : ℕ) = d') : blockPrefix b V j i d = V i d' := by
  have hlt : (d : ℕ) < N := by rw [h]; exact d'.isLt
  change (if h' : (d : ℕ) < N then V i ⟨d, h'⟩ else 0) = V i d'
  rw [dif_pos hlt]
  exact congrArg (V i) (Fin.ext h)

/-- Entry $(d, c)$ of the first $j$ blocks of the rows of $\mathbf{C}$ is entry $(d, c)$ of
$\mathbf{C}$. -/
private theorem blockRowPrefix_apply_of_eq (C : Matrix (Fin N) κ 𝕜) {j : ℕ} {d : Fin (j * b)}
    {d' : Fin N} (h : (d : ℕ) = d') (c : κ) : blockRowPrefix b C j d c = C d' c := by
  have hlt : (d : ℕ) < N := by rw [h]; exact d'.isLt
  change (if h' : (d : ℕ) < N then C ⟨d, h'⟩ c else 0) = C d' c
  rw [dif_pos hlt]
  exact congrFun (congrArg C (Fin.ext h)) c

/-- Every index $d < qb$ is $jb + c$ for a block $j < q$ and a position $c < b$ in the block. -/
private theorem exists_block_index {q : ℕ} (d : Fin (q * b)) :
    ∃ j < q, ∃ c : Fin b, j * b + (c : ℕ) = d := by
  have hd := d.isLt
  have hb : 0 < b := by
    by_contra h0
    have h1 : q * b = 0 := by rw [Nat.eq_zero_of_not_pos h0, Nat.mul_zero]
    omega
  exact ⟨(d : ℕ) / b, (Nat.div_lt_iff_lt_mul hb).2 hd, ⟨(d : ℕ) % b, Nat.mod_lt _ hb⟩,
    Nat.div_add_mod' _ _⟩

/-- Two matrices with $qb$ columns whose blocks of $b$ columns agree are equal. -/
private theorem ext_blockCols {q : ℕ} {X Y : Matrix ι (Fin (q * b)) 𝕜}
    (h : ∀ j < q, blockCols b X j = blockCols b Y j) : X = Y := by
  ext i d
  obtain ⟨j, hj, c, hd⟩ := exists_block_index d
  rw [← blockCols_apply_of_eq X i hd, ← blockCols_apply_of_eq Y i hd, h j hj]

/-- Block $j$ of the columns of $\mathbf{A}\mathbf{X}$ is $\mathbf{A}$ times block $j$ of the
columns of $\mathbf{X}$. -/
private theorem blockCols_mul [Fintype κ] (A : Matrix ι κ 𝕜) (X : Matrix κ (Fin N) 𝕜) (j : ℕ) :
    blockCols b (A * X) j = A * blockCols b X j := by
  ext i c
  by_cases h : j * b + (c : ℕ) < N <;> simp [blockCols, Matrix.mul_apply, h]

/-- Block $j$ of the columns of the zero matrix is zero. -/
private theorem blockCols_zero (j : ℕ) :
    blockCols b (0 : Matrix ι (Fin N) 𝕜) j = 0 := by
  ext i c
  simp [blockCols]

/-- Block $j < k$ of the first $k$ blocks of columns of $\mathbf{V}$ is block $j$ of
$\mathbf{V}$. -/
private theorem blockCols_blockPrefix (V : Matrix ι (Fin N) 𝕜) {j k : ℕ} (hj : j < k) :
    blockCols b (blockPrefix b V k) j = blockCols b V j := by
  ext i c
  have h1 : j * b + (c : ℕ) < k * b := by
    have h2 := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at h2
    have := c.isLt
    omega
  simp [blockCols, blockPrefix, h1]

/-- The first $j \le k$ blocks of the first $k$ blocks of columns of $\mathbf{V}$ are the first
$j$ blocks of $\mathbf{V}$. -/
private theorem blockPrefix_blockPrefix (V : Matrix ι (Fin N) 𝕜) {j k : ℕ} (hj : j ≤ k) :
    blockPrefix b (blockPrefix b V k) j = blockPrefix b V j := by
  ext i d
  have h1 : (d : ℕ) < k * b := d.isLt.trans_le (Nat.mul_le_mul_right b hj)
  simp [blockPrefix, h1]

/-- Block $j < k$ of the first $k$ blocks of rows of $\mathbf{C}$ is block $j$ of
$\mathbf{C}$. -/
private theorem blockRows_blockRowPrefix (C : Matrix (Fin N) κ 𝕜) {j k : ℕ} (hj : j < k) :
    blockRows b (blockRowPrefix b C k) j = blockRows b C j := by
  ext r c
  have h1 : j * b + (r : ℕ) < k * b := by
    have h2 := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at h2
    have := r.isLt
    omega
  simp [blockRows, blockRowPrefix, h1]

/-- The first $j \le k$ blocks of the first $k$ blocks of rows of $\mathbf{C}$ are the first
$j$ blocks of $\mathbf{C}$. -/
private theorem blockRowPrefix_blockRowPrefix (C : Matrix (Fin N) κ 𝕜) {j k : ℕ}
    (hj : j ≤ k) : blockRowPrefix b (blockRowPrefix b C k) j = blockRowPrefix b C j := by
  ext d c
  have h1 : (d : ℕ) < k * b := d.isLt.trans_le (Nat.mul_le_mul_right b hj)
  simp [blockRowPrefix, h1]

/-- If the rows of $\mathbf{C}$ from $kb$ on are zero, the product $\mathbf{U}\mathbf{C}$ only
uses the first $k$ blocks: $\mathbf{U}_{<k}\mathbf{C}_{<k} = \mathbf{U}\mathbf{C}$. -/
private theorem blockPrefix_mul_blockRowPrefix_eq_mul (U : Matrix ι (Fin N) 𝕜)
    (C : Matrix (Fin N) κ 𝕜) {k : ℕ} (hk : k * b ≤ N)
    (hC : ∀ (i : Fin N) (c : κ), k * b ≤ (i : ℕ) → C i c = 0) :
    blockPrefix b U k * blockRowPrefix b C k = U * C := by
  ext i c
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_fin_eq_sum_range,
    Finset.sum_fin_eq_sum_range]
  refine (Finset.sum_congr rfl fun d hd => ?_).trans
    (Finset.sum_subset (Finset.range_mono hk) fun d hd hd' => ?_)
  · have h1 : d < k * b := Finset.mem_range.1 hd
    have h2 : d < N := h1.trans_le hk
    rw [dif_pos h1, dif_pos h2,
      blockPrefix_apply_of_eq U i (j := k) (d := ⟨d, h1⟩) (d' := ⟨d, h2⟩) rfl,
      blockRowPrefix_apply_of_eq C (j := k) (d := ⟨d, h1⟩) (d' := ⟨d, h2⟩) rfl c]
  · have h2 : d < N := Finset.mem_range.1 hd
    rw [dif_pos h2, hC ⟨d, h2⟩ c (not_lt.1 fun h' => hd' (Finset.mem_range.2 h')), mul_zero]

/-- The first $j$ blocks of rows of $\mathbf{X}^{\mathsf{H}}\mathbf{Y}$ are
$\mathbf{X}_{<j}^{\mathsf{H}}\mathbf{Y}$, with $\mathbf{X}_{<j}$ the first $j$ blocks of columns
of $\mathbf{X}$. -/
private theorem blockRowPrefix_conjTranspose_mul [Fintype ι] (X : Matrix ι (Fin N) 𝕜)
    (Y : Matrix ι κ 𝕜) (j : ℕ) :
    blockRowPrefix b (Xᴴ * Y) j = (blockPrefix b X j)ᴴ * Y := by
  ext d c
  by_cases h : (d : ℕ) < N <;> simp [blockRowPrefix, blockPrefix, Matrix.mul_apply, h]

/-- A coefficient block column $\mathbf{C}$ that is zero from row $(k+1)b$ on and whose first
$k$ row blocks and row block $k$ have zero rows at the zero columns of the first $k$ blocks and
of block $k$ of $\mathbf{X}$ has zero rows at all zero columns of $\mathbf{X}$. -/
private theorem row_eq_zero_of_block (X : Matrix ι (Fin N) 𝕜) (C : Matrix (Fin N) κ 𝕜) {k : ℕ}
    (hsupp : ∀ (i : Fin N) (c : κ), (k + 1) * b ≤ (i : ℕ) → C i c = 0)
    (hl : ∀ d, (blockPrefix b X k).col d = 0 → blockRowPrefix b C k d = 0)
    (hr : ∀ r, (blockCols b X k).col r = 0 → blockRows b C k r = 0)
    (i : Fin N) (hi : X.col i = 0) : C i = 0 := by
  funext c
  rcases lt_or_ge (i : ℕ) (k * b) with h1 | h1
  · have hcol : (blockPrefix b X k).col ⟨i, h1⟩ = 0 := funext fun a =>
      (blockPrefix_apply_of_eq X a (j := k) (d := ⟨i, h1⟩) (d' := i) rfl).trans (congrFun hi a)
    exact (blockRowPrefix_apply_of_eq C (j := k) (d := ⟨i, h1⟩) (d' := i) rfl c).symm.trans
      (congrFun (hl _ hcol) c)
  · rcases lt_or_ge (i : ℕ) ((k + 1) * b) with h2 | h2
    · have hr' : (i : ℕ) - k * b < b := by rw [Nat.add_one_mul] at h2; omega
      have hri : k * b + ((⟨(i : ℕ) - k * b, hr'⟩ : Fin b) : ℕ) = i := Nat.add_sub_of_le h1
      have hcol : (blockCols b X k).col ⟨(i : ℕ) - k * b, hr'⟩ = 0 := funext fun a =>
        (blockCols_apply_of_eq X a hri).trans (congrFun hi a)
      exact (blockRows_apply_of_eq C hri c).symm.trans (congrFun (hr _ hcol) c)
    · exact hsupp i c h2

/-- A coefficient block column $\mathbf{C}$ that is zero from row $(k+1)b$ on and whose row
block $k$ is upper triangular is zero below the diagonal of row block $k$: $C_{ic} = 0$ for
$i > kb + c$. -/
private theorem apply_eq_zero_of_block (C : Matrix (Fin N) (Fin b) 𝕜) {k : ℕ}
    (hsupp : ∀ (i : Fin N) (c : Fin b), (k + 1) * b ≤ (i : ℕ) → C i c = 0)
    (hup : (blockRows b C k).BlockTriangular id) (i : Fin N) (c : Fin b)
    (h : k * b + (c : ℕ) < i) : C i c = 0 := by
  rcases lt_or_ge (i : ℕ) ((k + 1) * b) with h2 | h2
  · have hr' : (i : ℕ) - k * b < b := by rw [Nat.add_one_mul] at h2; omega
    have hri : k * b + ((⟨(i : ℕ) - k * b, hr'⟩ : Fin b) : ℕ) = i :=
      Nat.add_sub_of_le (by omega)
    have hcr : c < (⟨(i : ℕ) - k * b, hr'⟩ : Fin b) := by
      change (c : ℕ) < (i : ℕ) - k * b
      omega
    rw [← blockRows_apply_of_eq C hri c]
    exact hup hcr
  · exact hsupp i c h2

/-- If the nonzero columns of $\mathbf{X}$ are orthonormal, the rows of $\mathbf{C}$ at the zero
columns of $\mathbf{X}$ are zero and $\mathbf{W} = \mathbf{X}\mathbf{C}$, then
$\mathbf{C} = \mathbf{X}^{\mathsf{H}}\mathbf{W}$. -/
private theorem eq_conjTranspose_mul_of_gramDefect_eq_zero [Fintype ι] {X : Matrix ι (Fin N) 𝕜}
    {C : Matrix (Fin N) κ 𝕜} {W : Matrix ι κ 𝕜} (hX : gramDefect X = 0)
    (hz : ∀ i, X.col i = 0 → C i = 0) (hW : W = X * C) : C = Xᴴ * W := by
  have hD : Matrix.diagonal (colSupport X) * C = C := by
    ext i c
    rw [Matrix.diagonal_mul]
    by_cases hi : X.col i = 0
    · rw [colSupport_of_col_eq_zero hi, zero_mul, hz i hi]
      rfl
    · rw [colSupport_of_col_ne_zero hi, one_mul]
  rw [hW, ← Matrix.mul_assoc, gramDefect_eq_zero_iff.1 hX, hD]

/-- The column space of $[\mathbf{P}, \mathbf{B}]$ is the sum of the column spaces of
$\mathbf{P}$ and $\mathbf{B}$. -/
private theorem range_mulVecLin_fromCols {κ' : Type*} [Fintype κ] [Fintype κ']
    (P : Matrix ι κ 𝕜) (B : Matrix ι κ' 𝕜) :
    LinearMap.range (Matrix.fromCols P B).mulVecLin =
      LinearMap.range P.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  have h : (Matrix.fromCols P B).col = Sum.elim P.col B.col := by
    funext s
    rcases s with s | s <;> rfl
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, Matrix.range_mulVecLin, h,
    Set.Sum.elim_range, Submodule.span_union]

/-- The column space of the first $j + 1$ blocks is the sum of the column spaces of the first
$j$ blocks and of block $j$. -/
private theorem range_blockPrefix_succ_eq_sup (V : Matrix ι (Fin N) 𝕜) (j : ℕ) :
    LinearMap.range (blockPrefix b V (j + 1)).mulVecLin =
      LinearMap.range (blockPrefix b V j).mulVecLin ⊔
        LinearMap.range (blockCols b V j).mulVecLin := by
  rw [range_blockPrefix_succ, range_mulVecLin_fromCols]

/-- The prefix of zero blocks has no columns: its column space is zero. -/
private theorem range_blockPrefix_zero (V : Matrix ι (Fin N) 𝕜) :
    LinearMap.range (blockPrefix b V 0).mulVecLin = ⊥ := by
  have : IsEmpty (Fin (0 * b)) := by rw [Nat.zero_mul]; infer_instance
  rw [Matrix.range_mulVecLin, Set.range_eq_empty, Submodule.span_empty]

/-- The prefix of zero blocks has no columns: its Gram defect on the support is zero. -/
private theorem gramDefect_blockPrefix_zero [Fintype ι] (V : Matrix ι (Fin N) 𝕜) :
    gramDefect (blockPrefix b V 0) = 0 := by
  have : IsEmpty (Fin (0 * b)) := by rw [Nat.zero_mul]; infer_instance
  exact Subsingleton.elim _ _

/-- If block $j$ of $\mathbf{X}$ is an exact extension of the first $j$ blocks by $\mathbf{W}$,
the column space of the first $j + 1$ blocks is the sum of the column space of the first $j$
blocks and that of $\mathbf{W}$. -/
private theorem range_blockPrefix_succ_of_isBasisExtension {n' : ℕ}
    {X : Matrix (Fin n') (Fin N) 𝕜} {j : ℕ} {W : Matrix (Fin n') (Fin b) 𝕜}
    {H : Matrix (Fin (j * b)) (Fin b) 𝕜} {R : Matrix (Fin b) (Fin b) 𝕜}
    (hE : IsBasisExtension (blockPrefix b X j) W (blockCols b X j) H R) :
    LinearMap.range (blockPrefix b X (j + 1)).mulVecLin =
      LinearMap.range (blockPrefix b X j).mulVecLin ⊔ LinearMap.range W.mulVecLin := by
  rw [range_blockPrefix_succ, hE.range_eq, range_mulVecLin_fromCols]

/-- One more block of a block Krylov space: $\mathcal{K}_{q+2}(\mathbf{M}, \mathbf{B}) =
\mathcal{K}_{q+1}(\mathbf{M}, \mathbf{B}) + \mathbf{M}\mathcal{K}_{q+1}(\mathbf{M}, \mathbf{B})$. -/
private theorem blockKrylovSpace_succ_sup_map [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix ι ι 𝕜) (B : Matrix ι κ 𝕜) (q : ℕ) :
    blockKrylovSpace M B (q + 1) ⊔ (blockKrylovSpace M B (q + 1)).map M.mulVecLin =
      blockKrylovSpace M B (q + 1 + 1) := by
  refine le_antisymm (sup_le (blockKrylovSpace_mono M B (Nat.le_succ _))
    (Submodule.map_le_iff_le_comap.2 fun x hx => mulVec_mem_blockKrylovSpace_succ hx)) ?_
  rw [blockKrylovSpace_succ M B (q + 1)]
  refine sup_le le_sup_left (le_sup_of_le_right ?_)
  rw [pow_succ', Matrix.mul_assoc, Matrix.mulVecLin_mul, LinearMap.range_comp]
  refine Submodule.map_mono ?_
  rw [blockKrylovSpace_succ]
  exact le_sup_right

/-! ### Appending a block -/

/-- The matrix whose first $j$ blocks of columns are $\mathbf{P}$ and whose block $j$ is
$\mathbf{B}$. -/
private def appendBlockCols {j : ℕ} (P : Matrix ι (Fin (j * b)) 𝕜) (B : Matrix ι (Fin b) 𝕜) :
    Matrix ι (Fin ((j + 1) * b)) 𝕜 :=
  (Matrix.fromCols P B).submatrix id (blockSuccEquiv b j).symm

/-- The matrix whose first $k$ blocks of rows are $\mathbf{D}$ and whose block $k$ of rows is
$\mathbf{Z}$. -/
private def appendBlockRows {k : ℕ} (D : Matrix (Fin (k * b)) κ 𝕜) (Z : Matrix (Fin b) κ 𝕜) :
    Matrix (Fin ((k + 1) * b)) κ 𝕜 :=
  (Matrix.fromRows D Z).submatrix (blockSuccEquiv b k).symm id

/-- The first $j$ blocks and block $j$ of the columns of $[\mathbf{P}, \mathbf{B}]$ are
$\mathbf{P}$ and $\mathbf{B}$. -/
private theorem blockPrefix_appendBlockCols {j : ℕ} (P : Matrix ι (Fin (j * b)) 𝕜)
    (B : Matrix ι (Fin b) 𝕜) :
    blockPrefix b (appendBlockCols P B) j = P ∧ blockCols b (appendBlockCols P B) j = B := by
  have key : Matrix.fromCols (blockPrefix b (appendBlockCols P B) j)
      (blockCols b (appendBlockCols P B) j) = Matrix.fromCols P B := by
    rw [← blockPrefix_succ_submatrix, blockPrefix_self, appendBlockCols,
      Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  exact Matrix.fromCols_inj key

/-- The first $j' \le j$ blocks of the columns of $[\mathbf{P}, \mathbf{B}]$ are those of
$\mathbf{P}$, which has $j$ blocks. -/
private theorem blockPrefix_appendBlockCols_of_le {j j' : ℕ} (P : Matrix ι (Fin (j * b)) 𝕜)
    (B : Matrix ι (Fin b) 𝕜) (hj : j' ≤ j) :
    blockPrefix b (appendBlockCols P B) j' = blockPrefix b P j' := by
  rw [← blockPrefix_blockPrefix (appendBlockCols P B) hj, (blockPrefix_appendBlockCols P B).1]

/-- Block $j' < j$ of the columns of $[\mathbf{P}, \mathbf{B}]$ is that of $\mathbf{P}$, which
has $j$ blocks. -/
private theorem blockCols_appendBlockCols_of_lt {j j' : ℕ} (P : Matrix ι (Fin (j * b)) 𝕜)
    (B : Matrix ι (Fin b) 𝕜) (hj : j' < j) :
    blockCols b (appendBlockCols P B) j' = blockCols b P j' := by
  rw [← blockCols_blockPrefix (appendBlockCols P B) hj, (blockPrefix_appendBlockCols P B).1]

/-- The first $k$ blocks and block $k$ of the rows of $\mathbf{D}$ above $\mathbf{Z}$ are
$\mathbf{D}$ and $\mathbf{Z}$. -/
private theorem blockRowPrefix_appendBlockRows {k : ℕ} (D : Matrix (Fin (k * b)) κ 𝕜)
    (Z : Matrix (Fin b) κ 𝕜) :
    blockRowPrefix b (appendBlockRows D Z) k = D ∧ blockRows b (appendBlockRows D Z) k = Z := by
  have key : Matrix.fromRows (blockRowPrefix b (appendBlockRows D Z) k)
      (blockRows b (appendBlockRows D Z) k) = Matrix.fromRows D Z := by
    rw [← blockRowPrefix_succ_submatrix, blockRowPrefix_self, appendBlockRows,
      Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  exact Matrix.fromRows_inj key

/-- The first $k' \le k$ blocks of the rows of $\mathbf{D}$ above $\mathbf{Z}$ are those of
$\mathbf{D}$, which has $k$ blocks. -/
private theorem blockRowPrefix_appendBlockRows_of_le {k k' : ℕ} (D : Matrix (Fin (k * b)) κ 𝕜)
    (Z : Matrix (Fin b) κ 𝕜) (hk : k' ≤ k) :
    blockRowPrefix b (appendBlockRows D Z) k' = blockRowPrefix b D k' := by
  rw [← blockRowPrefix_blockRowPrefix (appendBlockRows D Z) hk,
    (blockRowPrefix_appendBlockRows D Z).1]

/-- Block $k' < k$ of the rows of $\mathbf{D}$ above $\mathbf{Z}$ is that of $\mathbf{D}$, which
has $k$ blocks. -/
private theorem blockRows_appendBlockRows_of_lt {k k' : ℕ} (D : Matrix (Fin (k * b)) κ 𝕜)
    (Z : Matrix (Fin b) κ 𝕜) (hk : k' < k) :
    blockRows b (appendBlockRows D Z) k' = blockRows b D k' := by
  rw [← blockRows_blockRowPrefix (appendBlockRows D Z) hk,
    (blockRowPrefix_appendBlockRows D Z).1]

/-- Block $j$ of the columns of $\mathbf{D}$ above $\mathbf{Z}$ is block $j$ of $\mathbf{D}$
above block $j$ of $\mathbf{Z}$. -/
private theorem blockCols_appendBlockRows {k : ℕ} (D : Matrix (Fin (k * b)) (Fin N) 𝕜)
    (Z : Matrix (Fin b) (Fin N) 𝕜) (j : ℕ) :
    blockCols b (appendBlockRows D Z) j =
      appendBlockRows (blockCols b D j) (blockCols b Z j) := by
  ext i c
  change (if h : j * b + (c : ℕ) < N then
      Matrix.fromRows D Z ((blockSuccEquiv b k).symm i) ⟨j * b + c, h⟩ else 0) =
    Matrix.fromRows (blockCols b D j) (blockCols b Z j) ((blockSuccEquiv b k).symm i) c
  rcases (blockSuccEquiv b k).symm i with a | a <;> rfl

/-- The matrix $\mathbf{D}$ above a zero block is zero from row $t$ on if $\mathbf{D}$ is. -/
private theorem appendBlockRows_zero_apply_eq_zero {k : ℕ} (D : Matrix (Fin (k * b)) κ 𝕜)
    {t : ℕ} (hD : ∀ (i : Fin (k * b)) (c : κ), t ≤ (i : ℕ) → D i c = 0)
    (i : Fin ((k + 1) * b)) (c : κ) (hi : t ≤ (i : ℕ)) :
    appendBlockRows D (0 : Matrix (Fin b) κ 𝕜) i c = 0 := by
  rcases lt_or_ge (i : ℕ) (k * b) with h1 | h1
  · exact (blockRowPrefix_apply_of_eq (appendBlockRows D 0) (j := k) (d := ⟨i, h1⟩) (d' := i)
      rfl c).symm.trans ((congrFun (congrFun (blockRowPrefix_appendBlockRows D 0).1 _) c).trans
        (hD ⟨i, h1⟩ c hi))
  · have hr' : (i : ℕ) - k * b < b := by
      have h2 : (i : ℕ) < k * b + b := lt_of_lt_of_eq i.isLt (Nat.add_one_mul k b)
      omega
    have hri : k * b + ((⟨(i : ℕ) - k * b, hr'⟩ : Fin b) : ℕ) = i := Nat.add_sub_of_le h1
    exact (blockRows_apply_of_eq (appendBlockRows D 0) hri c).symm.trans
      (congrFun (congrFun (blockRowPrefix_appendBlockRows D 0).2 _) c)

end Blocks

/-- One more step of block Golub–Kahan bidiagonalization: a run of $q$ steps, an exact extension
of $\mathbf{U}$ by $\mathbf{A}\mathbf{V}_q$ and an exact extension of $\mathbf{V}$ by
$\mathbf{A}^{\mathsf{H}}$ times the new left block give a run of $q + 1$ steps on the appended
matrices. -/
private theorem IsBlockGolubKahan.succ {A : Matrix (Fin m) (Fin n) 𝕜}
    {Ω : Matrix (Fin n) (Fin b) 𝕜} {q : ℕ} {U : Matrix (Fin m) (Fin (q * b)) 𝕜}
    {V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜} {R₀ : Matrix (Fin b) (Fin b) 𝕜}
    {R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜} {S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜}
    (h : IsBlockGolubKahan A Ω q U V R₀ R S) {Un : Matrix (Fin m) (Fin b) 𝕜}
    {H : Matrix (Fin (q * b)) (Fin b) 𝕜} {Rn : Matrix (Fin b) (Fin b) 𝕜}
    {Vn : Matrix (Fin n) (Fin b) 𝕜} {Hs : Matrix (Fin ((q + 1) * b)) (Fin b) 𝕜}
    {Rs : Matrix (Fin b) (Fin b) 𝕜} (hL : IsBasisExtension U (A * blockCols b V q) Un H Rn)
    (hR : IsBasisExtension V (Aᴴ * Un) Vn Hs Rs) :
    IsBlockGolubKahan A Ω (q + 1) (appendBlockCols U Un) (appendBlockCols V Vn) R₀
      (appendBlockCols (appendBlockRows R 0) (appendBlockRows H Rn))
      (appendBlockCols (appendBlockRows S 0) (appendBlockRows Hs Rs)) := by
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_, fun j hj i c hi => ?_, fun j hj i c hi => ?_⟩
  · rw [blockPrefix_appendBlockCols_of_le _ _ (Nat.zero_le _),
      blockCols_appendBlockCols_of_lt _ _ (Nat.succ_pos _)]
    exact h.start
  · rcases Nat.lt_or_ge j q with hj' | hj'
    · rw [blockPrefix_appendBlockCols_of_le _ _ hj'.le,
        blockCols_appendBlockCols_of_lt _ _ (Nat.lt_succ_of_lt hj'),
        blockCols_appendBlockCols_of_lt _ _ hj', blockCols_appendBlockCols_of_lt _ _ hj',
        blockCols_appendBlockRows, blockCols_zero,
        blockRowPrefix_appendBlockRows_of_le _ _ hj'.le, blockRows_appendBlockRows_of_lt _ _ hj']
      exact h.left j hj'
    · obtain rfl : j = q := by omega
      rw [(blockPrefix_appendBlockCols _ _).1,
        blockCols_appendBlockCols_of_lt _ _ (Nat.lt_add_one _),
        (blockPrefix_appendBlockCols _ _).2, (blockPrefix_appendBlockCols _ _).2,
        (blockRowPrefix_appendBlockRows _ _).1, (blockRowPrefix_appendBlockRows _ _).2]
      exact hL
  · rcases Nat.lt_or_ge j q with hj' | hj'
    · rw [blockPrefix_appendBlockCols_of_le _ _ (Nat.add_le_add_right hj'.le 1),
        blockCols_appendBlockCols_of_lt _ _ hj', blockCols_appendBlockCols_of_lt _ _ hj',
        blockCols_appendBlockCols_of_lt _ _ (Nat.add_lt_add_right hj' 1),
        blockCols_appendBlockRows, blockCols_zero,
        blockRowPrefix_appendBlockRows_of_le _ _ (Nat.add_le_add_right hj'.le 1),
        blockRows_appendBlockRows_of_lt _ _ (Nat.add_lt_add_right hj' 1)]
      exact h.right j hj'
    · obtain rfl : j = q := by omega
      rw [(blockPrefix_appendBlockCols _ _).1, (blockPrefix_appendBlockCols _ _).2,
        (blockPrefix_appendBlockCols _ _).2, (blockPrefix_appendBlockCols _ _).2,
        (blockRowPrefix_appendBlockRows _ _).1, (blockRowPrefix_appendBlockRows _ _).2]
      exact hR
  · rcases Nat.lt_or_ge j q with hj' | hj'
    · rw [blockCols_appendBlockCols_of_lt _ _ hj', blockCols_appendBlockRows, blockCols_zero]
      exact appendBlockRows_zero_apply_eq_zero _ (h.left_support j hj') i c hi
    · obtain rfl : j = q := by omega
      exact absurd i.isLt (not_lt.2 hi)
  · rcases Nat.lt_or_ge j q with hj' | hj'
    · rw [blockCols_appendBlockCols_of_lt _ _ hj', blockCols_appendBlockRows, blockCols_zero]
      exact appendBlockRows_zero_apply_eq_zero _ (h.right_support j hj') i c hi
    · obtain rfl : j = q := by omega
      exact absurd i.isLt (not_lt.2 hi)

/-- The nonzero columns of the Gram–Schmidt factor $\mathbf{Q}$ of $\mathbf{W}$ are orthonormal:
its Gram defect on the support is zero. -/
private theorem gramDefect_gramSchmidtQ {n' : ℕ} (W : Matrix (Fin n') (Fin b) 𝕜) :
    gramDefect (gramSchmidtQ W) = 0 := by
  rw [gramDefect_eq_zero_iff, conjTranspose_gramSchmidtQ_mul_self]
  refine congrArg Matrix.diagonal (funext fun j => ?_)
  by_cases hj : gramSchmidtR W j j = 0
  · rw [if_pos hj, colSupport_of_col_eq_zero ((gramSchmidtQ_col_eq_zero_iff W j).2 hj)]
  · rw [if_neg hj,
      colSupport_of_col_ne_zero fun h0 => hj ((gramSchmidtQ_col_eq_zero_iff W j).1 h0)]

/-- Classical Gram–Schmidt of $\mathbf{W} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}$ keeps
orthonormality on the support: if the nonzero columns of $\mathbf{Q}$ are orthonormal and
$\mathbf{Q}'$ is the Gram–Schmidt factor of $\mathbf{W} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}
\mathbf{W}$, the nonzero columns of $[\mathbf{Q}, \mathbf{Q}']$ are orthonormal. -/
private theorem gramDefect_fromCols_gramSchmidtQ {n' k : ℕ} (Q : Matrix (Fin n') (Fin k) 𝕜)
    (W : Matrix (Fin n') (Fin b) 𝕜) (hQ : gramDefect Q = 0) :
    gramDefect (Matrix.fromCols Q (gramSchmidtQ (W - Q * (Qᴴ * W)))) = 0 := by
  obtain ⟨T, hT⟩ := range_le_iff_exists_mul.1 (range_gramSchmidtQ (W - Q * (Qᴴ * W))).le
  have hQQ : Qᴴ * Q * Qᴴ = Qᴴ := by
    have h0 := congrArg Matrix.conjTranspose (mul_conjTranspose_mul_self_of_gramDefect_eq_zero hQ)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h0
  have h1 : Qᴴ * (W - Q * (Qᴴ * W)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc Qᴴ Q, ← Matrix.mul_assoc (Qᴴ * Q), hQQ, sub_self]
  have h12 : Qᴴ * gramSchmidtQ (W - Q * (Qᴴ * W)) = 0 := by
    rw [hT, ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have h21 : (gramSchmidtQ (W - Q * (Qᴴ * W)))ᴴ * Q = 0 := by
    have h0 := congrArg Matrix.conjTranspose h12
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h0
  rw [gramDefect_fromCols, hQ, h12, h21, gramDefect_gramSchmidtQ, Matrix.fromBlocks_zero]

/-! ### Existence -/

/-- Every basis has an exact extension by every block: for every $\mathbf{Q}$ and $\mathbf{W}$
with the same number of rows there are $\mathbf{Q}'$, $\mathbf{H}$ and $\mathbf{R}$ such that
$(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is an exact extension of $\mathbf{Q}$ by $\mathbf{W}$.
No orthonormality of $\mathbf{Q}$ is assumed. -/
theorem exists_isBasisExtension {n k b : ℕ} (Q : Matrix (Fin n) (Fin k) 𝕜)
    (W : Matrix (Fin n) (Fin b) 𝕜) :
    ∃ (Q' : Matrix (Fin n) (Fin b) 𝕜) (H : Matrix (Fin k) (Fin b) 𝕜)
      (R : Matrix (Fin b) (Fin b) 𝕜), IsBasisExtension Q W Q' H R := by
  obtain ⟨T, hT⟩ := range_le_iff_exists_mul.1 (range_gramSchmidtQ (W - Q * (Qᴴ * W))).le
  refine ⟨gramSchmidtQ (W - Q * (Qᴴ * W)), Qᴴ * W, gramSchmidtR (W - Q * (Qᴴ * W)),
    ?_, isUpperTriangular_gramSchmidtR _, ⟨-(Qᴴ * W * T), T, ?_⟩, fun c hc => ?_,
    fun j hj => ?_, fun c hc => ?_, gramDefect_fromCols_gramSchmidtQ Q W⟩
  · rw [gramSchmidtQ_mul_gramSchmidtR, add_sub_cancel]
  · rw [hT, Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc Q, neg_add_eq_sub]
  · have e : (W - Q * (Qᴴ * W)).col c = W.col c - Q *ᵥ (Qᴴ *ᵥ W.col c) := rfl
    rw [gramSchmidtQ_col_eq_zero_iff, gramSchmidtR_apply_self_eq_zero_iff, e, hc,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
    exact Submodule.zero_mem _
  · funext c
    change (Qᴴ * W) j c = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [Matrix.conjTranspose_apply, show Q i j = 0 from congrFun hj i, star_zero, zero_mul]
  · funext d
    change ((gramSchmidtQ (W - Q * (Qᴴ * W)))ᴴ * (W - Q * (Qᴴ * W))) c d = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [Matrix.conjTranspose_apply,
        show gramSchmidtQ (W - Q * (Qᴴ * W)) i c = 0 from congrFun hc i, star_zero, zero_mul]

/-- **Block Golub–Kahan bidiagonalization has a run for every input**: for every
$\mathbf{A}$, $\mathbf{\Omega}$ and $q$
there are $\mathbf{U}$, $\mathbf{V}$, $\mathbf{R}_0$, $\mathbf{R}$, $\mathbf{S}$ related to them by
block Golub–Kahan bidiagonalization with full reorthogonalization in exact arithmetic.
No printed source.
Result: block-golub-kahan-existence -/
theorem exists_isBlockGolubKahan (A : Matrix (Fin m) (Fin n) 𝕜) (Ω : Matrix (Fin n) (Fin b) 𝕜)
    (q : ℕ) :
    ∃ (U : Matrix (Fin m) (Fin (q * b)) 𝕜) (V : Matrix (Fin n) (Fin ((q + 1) * b)) 𝕜)
      (R₀ : Matrix (Fin b) (Fin b) 𝕜) (R : Matrix (Fin (q * b)) (Fin (q * b)) 𝕜)
      (S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜), IsBlockGolubKahan A Ω q U V R₀ R S := by
  induction q with
  | zero =>
    have : IsEmpty (Fin (0 * b)) := by rw [Nat.zero_mul]; infer_instance
    obtain ⟨Q', H, R₀, hext⟩ := exists_isBasisExtension (0 : Matrix (Fin n) (Fin (0 * b)) 𝕜) Ω
    rw [Subsingleton.elim H 0] at hext
    refine ⟨0, appendBlockCols 0 Q', R₀, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(blockPrefix_appendBlockCols _ _).1, (blockPrefix_appendBlockCols _ _).2]
      exact hext
    all_goals exact fun j hj => absurd hj (Nat.not_lt_zero j)
  | succ q ih =>
    obtain ⟨U, V, R₀, R, S, hGK⟩ := ih
    obtain ⟨Un, H, Rn, hL⟩ := exists_isBasisExtension U (A * blockCols b V q)
    obtain ⟨Vn, Hs, Rs, hR⟩ := exists_isBasisExtension V (Aᴴ * Un)
    exact ⟨_, _, R₀, _, _, IsBlockGolubKahan.succ hGK hL hR⟩

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
  induction j with
  | zero => exact gramDefect_blockPrefix_zero U
  | succ j ih =>
    rw [gramDefect_blockPrefix_succ_eq_zero_iff]
    exact (h.left j (by omega)).orth (ih (by omega))

/-- The nonzero columns of the first $j + 1 \le q + 1$ blocks of the right basis $\mathbf{V}$ of
block Golub–Kahan bidiagonalization in exact arithmetic are orthonormal: their Gram defect on
the support vanishes. -/
theorem gramDefect_blockPrefix_right_eq_zero (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ}
    (hj : j ≤ q) : gramDefect (blockPrefix b V (j + 1)) = 0 := by
  induction j with
  | zero =>
    rw [gramDefect_blockPrefix_succ_eq_zero_iff]
    exact h.start.orth (gramDefect_blockPrefix_zero V)
  | succ j ih =>
    rw [gramDefect_blockPrefix_succ_eq_zero_iff]
    exact (h.right j (by omega)).orth (ih (by omega))

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

/-- The joint induction for the Krylov ranges of block Golub–Kahan bidiagonalization in exact
arithmetic: the first $j$ blocks of $\mathbf{U}$ span $\mathbf{A}\mathcal{K}_j$, and the first
$j$ and $j + 1$ blocks of $\mathbf{V}$ span $\mathcal{K}_j$ and $\mathcal{K}_{j+1}$, the block
Krylov spaces of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ and $\mathbf{\Omega}$. -/
private theorem range_blockPrefix_aux (h : IsBlockGolubKahan A Ω q U V R₀ R S) (j : ℕ) :
    (j ≤ q → LinearMap.range (blockPrefix b U j).mulVecLin =
      (blockKrylovSpace (Aᴴ * A) Ω j).map A.mulVecLin) ∧
    (j ≤ q + 1 → LinearMap.range (blockPrefix b V j).mulVecLin =
      blockKrylovSpace (Aᴴ * A) Ω j) ∧
    (j ≤ q → LinearMap.range (blockPrefix b V (j + 1)).mulVecLin =
      blockKrylovSpace (Aᴴ * A) Ω (j + 1)) := by
  induction j with
  | zero =>
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [range_blockPrefix_zero, blockKrylovSpace_zero, Submodule.map_bot]
    · rw [range_blockPrefix_zero, blockKrylovSpace_zero]
    · rw [range_blockPrefix_succ_of_isBasisExtension h.start, range_blockPrefix_zero,
        bot_sup_eq]
      exact (blockKrylovSpace_one _ _).symm
  | succ j ih =>
    obtain ⟨hL, hR, hR'⟩ := ih
    have hLs : j + 1 ≤ q → LinearMap.range (blockPrefix b U (j + 1)).mulVecLin =
        (blockKrylovSpace (Aᴴ * A) Ω (j + 1)).map A.mulVecLin := by
      intro hj
      have e : blockKrylovSpace (Aᴴ * A) Ω j ⊔ LinearMap.range (blockCols b V j).mulVecLin =
          blockKrylovSpace (Aᴴ * A) Ω (j + 1) := by
        rw [← hR (by omega), ← range_blockPrefix_succ_eq_sup, hR' (by omega)]
      rw [range_blockPrefix_succ_of_isBasisExtension (h.left j (by omega)), hL (by omega),
        Matrix.mulVecLin_mul, LinearMap.range_comp, ← Submodule.map_sup, e]
    refine ⟨hLs, fun hj => hR' (by omega), fun hj => ?_⟩
    have hsum : LinearMap.range (blockPrefix b U j).mulVecLin ⊔
        LinearMap.range (blockCols b U j).mulVecLin =
          (blockKrylovSpace (Aᴴ * A) Ω (j + 1)).map A.mulVecLin := by
      rw [← range_blockPrefix_succ_eq_sup, hLs hj]
    have hle : (LinearMap.range (blockPrefix b U j).mulVecLin).map Aᴴ.mulVecLin ≤
        blockKrylovSpace (Aᴴ * A) Ω (j + 1) := by
      rw [hL (by omega), ← Submodule.map_comp, ← Matrix.mulVecLin_mul]
      exact Submodule.map_le_iff_le_comap.2 fun x hx => mulVec_mem_blockKrylovSpace_succ hx
    rw [range_blockPrefix_succ_of_isBasisExtension (h.right j (by omega)), hR' (by omega),
      Matrix.mulVecLin_mul, LinearMap.range_comp, ← blockKrylovSpace_succ_sup_map,
      Matrix.mulVecLin_mul, Submodule.map_comp, ← hsum, Submodule.map_sup, ← sup_assoc,
      sup_eq_left.2 hle]

/-- **The right basis of block Golub–Kahan bidiagonalization spans the block Krylov space.**
The first $j + 1 \le q + 1$ blocks of the right basis $\mathbf{V}$ of block Golub–Kahan
bidiagonalization in exact arithmetic span the block Krylov space
$\mathcal{K}_{j+1}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}) =
\operatorname{range}[\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{j}\mathbf{\Omega}]$, for every start block
$\mathbf{\Omega}$ and every exact orthogonalization scheme, zero columns included.
No printed source.
Result: block-golub-kahan-krylov-range -/
theorem range_blockPrefix_right (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ} (hj : j ≤ q) :
    LinearMap.range (blockPrefix b V (j + 1)).mulVecLin = blockKrylovSpace (Aᴴ * A) Ω (j + 1) := by
  exact (range_blockPrefix_aux h j).2.2 hj

/-- **The left basis of block Golub–Kahan bidiagonalization spans the image of the block Krylov
space.** The first $j \le q$ blocks of the left basis $\mathbf{U}$ of block Golub–Kahan
bidiagonalization in exact arithmetic span the image under $\mathbf{A}$ of the block Krylov space
$\mathcal{K}_{j}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}) =
\operatorname{range}[\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{j-1}\mathbf{\Omega}]$ (the zero space for $j = 0$), for
every start block $\mathbf{\Omega}$ and every exact orthogonalization scheme.
No printed source.
Result: block-golub-kahan-krylov-range -/
theorem range_blockPrefix_left (h : IsBlockGolubKahan A Ω q U V R₀ R S) {j : ℕ} (hj : j ≤ q) :
    LinearMap.range (blockPrefix b U j).mulVecLin =
      (blockKrylovSpace (Aᴴ * A) Ω j).map A.mulVecLin := by
  exact (range_blockPrefix_aux h j).1 hj

/-- **The left basis of block Golub–Kahan bidiagonalization gives the range projector.**
The left basis $\mathbf{U}$ of block Golub–Kahan bidiagonalization in exact arithmetic gives
the orthogonal projector onto the range of $\mathbf{A}\mathbf{K}_q$, where
$\mathbf{K}_q = [\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}]$ is the block Krylov matrix:
$$\mathbf{U}\mathbf{U}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}\mathbf{K}_q}\,.$$
No printed source.
Result: block-golub-kahan-krylov-range -/
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
  refine ext_blockCols fun j hj => ?_
  rw [blockCols_mul, blockCols_mul, blockCols_blockPrefix V hj, (h.left j hj).repr,
    ← blockPrefix_succ_mul_blockRowPrefix_succ,
    blockPrefix_mul_blockRowPrefix_eq_mul U (blockCols b R j) (k := j + 1)
      (Nat.mul_le_mul_right b hj) (h.left_support j hj)]

/-- The second block relation of block Golub–Kahan bidiagonalization in exact arithmetic:
$\mathbf{A}^{\mathsf{H}}\mathbf{U} = \mathbf{V}\mathbf{S}$, with $\mathbf{U}$ the left basis,
$\mathbf{V}$ the right basis (all $q + 1$ blocks) and $\mathbf{S}$ the coefficient matrix of the
right steps. -/
theorem conjTranspose_mul_left_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    Aᴴ * U = V * S := by
  refine ext_blockCols fun j hj => ?_
  rw [blockCols_mul, blockCols_mul, (h.right j hj).repr,
    ← blockPrefix_succ_mul_blockRowPrefix_succ,
    blockPrefix_mul_blockRowPrefix_eq_mul V (blockCols b S j) (k := j + 1 + 1)
      (Nat.mul_le_mul_right b (by omega)) (fun i c hi => h.right_support j hj i c hi)]

/-- **The factored output of block Golub–Kahan bidiagonalization in exact arithmetic is the
randomized SVD approximation at the block Krylov matrix**:
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rsvd}(\mathbf{A}, \mathbf{K}_q) = \mathbf{P}_{\mathbf{A}\mathbf{K}_q}\mathbf{A},
\qquad \mathbf{K}_q = [\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}],$$
for every $\mathbf{A}$, every start block $\mathbf{\Omega}$ and every exact orthogonalization
scheme: dependent start columns, rank-deficient $\mathbf{A}$ and breakdown inside the run are
included.
No printed source.
Result: block-golub-kahan-factored-output -/
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
  rw [Matrix.mul_assoc]
  refine eq_conjTranspose_mul_of_gramDefect_eq_zero h.gramDefect_left_eq_zero (fun i hi => ?_)
    h.mul_blockPrefix_right_eq
  funext d
  obtain ⟨j, hj, c, hd⟩ := exists_block_index d
  rw [← blockCols_apply_of_eq R i hd]
  exact congrFun (row_eq_zero_of_block U (blockCols b R j) (k := j) (h.left_support j hj)
    (h.left j hj).coef_zero_left (h.left j hj).coef_zero_right i hi) c

/-- The coefficient matrix of the right steps of block Golub–Kahan bidiagonalization in exact
arithmetic is the projected matrix: $\mathbf{S} =
\mathbf{V}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}}\mathbf{U}$. The rows of $\mathbf{S}$ at zero columns
of $\mathbf{V}$ are zero. -/
theorem coef_right_eq (h : IsBlockGolubKahan A Ω q U V R₀ R S) : S = Vᴴ * Aᴴ * U := by
  rw [Matrix.mul_assoc]
  refine eq_conjTranspose_mul_of_gramDefect_eq_zero h.gramDefect_right_eq_zero (fun i hi => ?_)
    h.conjTranspose_mul_left_eq
  funext d
  obtain ⟨j, hj, c, hd⟩ := exists_block_index d
  rw [← blockCols_apply_of_eq S i hd]
  exact congrFun (row_eq_zero_of_block V (blockCols b S j) (k := j + 1)
    (fun i c hi => h.right_support j hj i c hi) (h.right j hj).coef_zero_left
    (h.right j hj).coef_zero_right i hi) c

/-- The two coefficient matrices of block Golub–Kahan bidiagonalization in exact arithmetic
carry the same entries: $\mathbf{R} = \mathbf{S}_{<q}^{\mathsf{H}}$, where $\mathbf{S}_{<q}$ is
the first $q$ row blocks (the first $qb$ rows) of $\mathbf{S}$. -/
theorem coef_left_eq_conjTranspose_blockRowPrefix (h : IsBlockGolubKahan A Ω q U V R₀ R S) :
    R = (blockRowPrefix b S q)ᴴ := by
  rw [h.coef_right_eq, Matrix.mul_assoc, blockRowPrefix_conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact h.coef_left_eq

/-- **The left coefficient matrix of block Golub–Kahan bidiagonalization is upper triangular.**
The coefficient matrix $\mathbf{R}$ of the left steps of block Golub–Kahan bidiagonalization
in exact arithmetic is upper triangular.
No printed source.
Result: block-golub-kahan-band-structure -/
theorem blockTriangular_left (h : IsBlockGolubKahan A Ω q U V R₀ R S) : R.BlockTriangular id := by
  intro i d hdi
  obtain ⟨j, hj, c, hd⟩ := exists_block_index d
  rw [← blockCols_apply_of_eq R i hd]
  exact apply_eq_zero_of_block (blockCols b R j) (k := j) (h.left_support j hj)
    (h.left j hj).upper i c (by rw [hd]; exact hdi)

/-- **The right coefficient matrix of block Golub–Kahan bidiagonalization is banded.**
The coefficient matrix $\mathbf{S}$ of the right steps of block Golub–Kahan
bidiagonalization in exact arithmetic, with blocks of width $b$, is zero below its $b$-th
subdiagonal: $S_{ic} = 0$ for $i > c + b$.
No printed source.
Result: block-golub-kahan-band-structure -/
theorem coef_right_apply_eq_zero_of_add_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i : Fin ((q + 1) * b)) (c : Fin (q * b)) (hic : (c : ℕ) + b < (i : ℕ)) : S i c = 0 := by
  obtain ⟨j, hj, c', hd⟩ := exists_block_index c
  rw [← blockCols_apply_of_eq S i hd]
  exact apply_eq_zero_of_block (blockCols b S j) (k := j + 1)
    (fun i c hi => h.right_support j hj i c hi) (h.right j hj).upper i c'
    (by rw [Nat.add_one_mul]; omega)

/-- **The right coefficient matrix of block Golub–Kahan bidiagonalization is zero above its
diagonal.** The coefficient matrix $\mathbf{S}$ of the right steps of block Golub–Kahan
bidiagonalization in exact arithmetic is zero above its diagonal: $S_{ic} = 0$ for $i < c$.
With the vanishing below the $b$-th subdiagonal, $\mathbf{S}^{\mathsf{H}}$ is zero outside the
band $0 \le \text{column} - \text{row} \le b$; for $b = 1$ it is upper bidiagonal.
No printed source.
Result: block-golub-kahan-band-structure -/
theorem coef_right_apply_eq_zero_of_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i : Fin ((q + 1) * b)) (c : Fin (q * b)) (hic : (i : ℕ) < (c : ℕ)) : S i c = 0 := by
  have hi' : (i : ℕ) < q * b := hic.trans c.isLt
  have hR := congrFun (congrFun h.coef_left_eq_conjTranspose_blockRowPrefix c) ⟨i, hi'⟩
  rw [h.blockTriangular_left (show id (⟨(i : ℕ), hi'⟩ : Fin (q * b)) < id c from hic),
    Matrix.conjTranspose_apply,
    blockRowPrefix_apply_of_eq S (j := q) (d := ⟨i, hi'⟩) (d' := i) rfl c] at hR
  exact star_eq_zero.1 hR.symm

/-- **The left coefficient matrix of block Golub–Kahan bidiagonalization is banded.**
The coefficient matrix $\mathbf{R}$ of the left steps of block Golub–Kahan bidiagonalization
in exact arithmetic, with blocks of width $b$, is zero above its $b$-th superdiagonal:
$R_{ic} = 0$ for $c > i + b$. With upper triangularity, $\mathbf{R}$ is zero outside the band
$0 \le \text{column} - \text{row} \le b$.
No printed source.
Result: block-golub-kahan-band-structure -/
theorem coef_left_apply_eq_zero_of_add_lt (h : IsBlockGolubKahan A Ω q U V R₀ R S)
    (i c : Fin (q * b)) (hic : (i : ℕ) + b < (c : ℕ)) : R i c = 0 := by
  have hc' : (c : ℕ) < (q + 1) * b := c.isLt.trans_le (Nat.mul_le_mul_right b (Nat.le_succ q))
  have hR := congrFun (congrFun h.coef_left_eq_conjTranspose_blockRowPrefix i) c
  rw [Matrix.conjTranspose_apply,
    blockRowPrefix_apply_of_eq S (j := q) (d := c) (d' := ⟨c, hc'⟩) rfl i,
    h.coef_right_apply_eq_zero_of_add_lt ⟨c, hc'⟩ i hic, star_zero] at hR
  exact hR

end IsBlockGolubKahan

end NLAlib
