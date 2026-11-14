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

section GramHelpers

variable {𝕜 : Type*} [RCLike 𝕜] {l l' p : Type*} [Fintype l] [Fintype l'] [Fintype p]

/-- Two matrices with the same Gram matrix have the same spectral norm. -/
private theorem specNorm_eq_of_conjTranspose_mul_self_eq {X : Matrix l p 𝕜} {Y : Matrix l' p 𝕜}
    (h : Xᴴ * X = Yᴴ * Y) : specNorm X = specNorm Y := by
  have h2 : specNorm X ^ 2 = specNorm Y ^ 2 := by
    rw [← specNorm_conjTranspose_mul_self, ← specNorm_conjTranspose_mul_self, h]
  exact (sq_eq_sq₀ (specNorm_nonneg X) (specNorm_nonneg Y)).1 h2

/-- Two matrices with the same Gram matrix have the same Frobenius norm. -/
private theorem frobNorm_eq_of_conjTranspose_mul_self_eq {X : Matrix l p 𝕜} {Y : Matrix l' p 𝕜}
    (h : Xᴴ * X = Yᴴ * Y) : frobNorm X = frobNorm Y := by
  have h2 : frobNorm X ^ 2 = frobNorm Y ^ 2 := by
    rw [frobNorm_sq_eq_re_trace, frobNorm_sq_eq_re_trace, h]
  exact (sq_eq_sq₀ (frobNorm_nonneg X) (frobNorm_nonneg Y)).1 h2

/-- If $\mathbf{S}$ is Hermitian with $\mathbf{S}^2 = \mathbf{Q}^{\mathsf{H}}\mathbf{Q}$ then
$\mathbf{Q}\mathbf{X}$ and $\mathbf{S}\mathbf{X}$ have the same Gram matrix. -/
private theorem conjTranspose_mul_mul_mul_eq {r : Type*} {Q : Matrix l p 𝕜} {S : Matrix p p 𝕜}
    (hSH : Sᴴ = S) (hS2 : S * S = Qᴴ * Q) (X : Matrix p r 𝕜) :
    (Q * X)ᴴ * (Q * X) = (S * X)ᴴ * (S * X) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSH, Matrix.mul_assoc Xᴴ Qᴴ (Q * X),
    ← Matrix.mul_assoc Qᴴ Q X, ← hS2, Matrix.mul_assoc Xᴴ S (S * X), ← Matrix.mul_assoc S S X]

open scoped MatrixOrder ComplexOrder in
/-- The Gram matrix $\mathbf{Q}^{\mathsf{H}}\mathbf{Q}$ has a Hermitian square root. -/
private theorem exists_conjTranspose_eq_and_mul_self_eq (Q : Matrix l p 𝕜) :
    ∃ S : Matrix p p 𝕜, Sᴴ = S ∧ S * S = Qᴴ * Q := by
  classical
  have h0 : (0 : Matrix p p 𝕜) ≤ Qᴴ * Q := (Matrix.posSemidef_conjTranspose_mul_self Q).nonneg
  exact ⟨CFC.sqrt (Qᴴ * Q), (CFC.sqrt_nonneg _).isSelfAdjoint, CFC.sqrt_mul_sqrt_self _ h0⟩

end GramHelpers

section GramDefect

variable {𝕜 : Type*} [RCLike 𝕜] {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]

omit [Fintype m] [Fintype ι] [DecidableEq ι] in
/-- The indicator of the nonzero columns has modulus at most one. -/
private theorem norm_colSupport_le_one (Q : Matrix m ι 𝕜) (j : ι) : ‖colSupport Q j‖ ≤ 1 := by
  by_cases h : Q.col j = 0
  · rw [colSupport_of_col_eq_zero h, norm_zero]
    exact zero_le_one
  · rw [colSupport_of_col_ne_zero h, norm_one]

/-- With $\mathbf{P}_{\mathbf{Q}}$ the orthogonal projector onto the column space of $\mathbf{Q}$
and $\mathbf{D}$ the Gram defect on the support of $\mathbf{Q}$,
$(\mathbf{Q}\mathbf{Q}^{\mathsf{H}} - \mathbf{P}_{\mathbf{Q}})\mathbf{Q} = \mathbf{Q}\mathbf{D}$. -/
private theorem mul_conjTranspose_sub_rangeProjector_mul_self (Q : Matrix m ι 𝕜) :
    (Q * Qᴴ - rangeProjector Q) * Q = Q * gramDefect Q := by
  rw [Matrix.sub_mul, rangeProjector_mul_self, Matrix.mul_assoc, gramDefect, Matrix.mul_sub,
    mul_diagonal_colSupport]

open scoped ComplexOrder in
/-- A Hermitian square root $\mathbf{S}$ of $\mathbf{Q}^{\mathsf{H}}\mathbf{Q}$ commutes with the
Gram defect on the support of $\mathbf{Q}$. -/
private theorem gramDefect_mul_eq_mul_gramDefect {Q : Matrix m ι 𝕜} {S : Matrix ι ι 𝕜}
    (hSH : Sᴴ = S) (hS2 : S * S = Qᴴ * Q) : gramDefect Q * S = S * gramDefect Q := by
  have hSd : S * Matrix.diagonal (colSupport Q) = S := by
    have hZ : S * (1 - Matrix.diagonal (colSupport Q)) = 0 := by
      rw [← Matrix.conjTranspose_mul_self_eq_zero, Matrix.conjTranspose_mul, hSH,
        Matrix.mul_assoc, ← Matrix.mul_assoc S S, hS2, Matrix.mul_assoc Qᴴ, Matrix.mul_sub Q,
        Matrix.mul_one, mul_diagonal_colSupport, sub_self, Matrix.mul_zero, Matrix.mul_zero]
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hZ
    exact hZ.symm
  have hSD : S * gramDefect Q = S * (S * S) - S := by
    rw [gramDefect, Matrix.mul_sub, hSd, hS2]
  have h := congrArg Matrix.conjTranspose hSD
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hSH,
    (isHermitian_gramDefect Q).eq] at h
  rw [h, hSD, Matrix.mul_assoc]

/-- With $\mathbf{P}_{\mathbf{Q}}$ the orthogonal projector onto the column space of $\mathbf{Q}$
and $\mathbf{D}$ the Gram defect on the support of $\mathbf{Q}$, the difference
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}} - \mathbf{P}_{\mathbf{Q}}$ has the spectral and Frobenius norms
of $\mathbf{D}\mathbf{C}$ for some $\mathbf{C}$ with $\|\mathbf{C}\|_2 \le 1$. -/
private theorem exists_norm_mul_conjTranspose_sub_rangeProjector_eq (Q : Matrix m ι 𝕜) :
    ∃ C : Matrix ι m 𝕜, specNorm C ≤ 1 ∧
      specNorm (Q * Qᴴ - rangeProjector Q) = specNorm (gramDefect Q * C) ∧
      frobNorm (Q * Qᴴ - rangeProjector Q) = frobNorm (gramDefect Q * C) := by
  obtain ⟨S, hSH, hS2⟩ := exists_conjTranspose_eq_and_mul_self_eq Q
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι m 𝕜, rangeProjector Q = Q * B :=
    range_le_iff_exists_mul.1 (range_rangeProjector Q).le
  have hMP : (Q * Qᴴ - rangeProjector Q) * rangeProjector Q = Q * Qᴴ - rangeProjector Q := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, conjTranspose_mul_rangeProjector,
      rangeProjector_mul_rangeProjector]
  have hM : Q * Qᴴ - rangeProjector Q = Q * (gramDefect Q * B) := by
    calc Q * Qᴴ - rangeProjector Q
        = (Q * Qᴴ - rangeProjector Q) * Q * B := by
          rw [Matrix.mul_assoc, ← hB, hMP]
      _ = Q * (gramDefect Q * B) := by
          rw [mul_conjTranspose_sub_rangeProjector_mul_self, Matrix.mul_assoc]
  have he : gramDefect Q * (S * B) = S * (gramDefect Q * B) := by
    rw [← Matrix.mul_assoc, gramDefect_mul_eq_mul_gramDefect hSH hS2, Matrix.mul_assoc]
  have hg : (Q * (gramDefect Q * B))ᴴ * (Q * (gramDefect Q * B)) =
      (gramDefect Q * (S * B))ᴴ * (gramDefect Q * (S * B)) := by
    rw [he]
    exact conjTranspose_mul_mul_mul_eq hSH hS2 _
  have hC : specNorm (S * B) ≤ 1 := by
    rw [← specNorm_eq_of_conjTranspose_mul_self_eq (conjTranspose_mul_mul_mul_eq hSH hS2 B),
      ← hB]
    exact (isStarProjection_rangeProjector Q).specNorm_le_one
  refine ⟨S * B, hC, ?_, ?_⟩
  · rw [hM]
    exact specNorm_eq_of_conjTranspose_mul_self_eq hg
  · rw [hM]
    exact frobNorm_eq_of_conjTranspose_mul_self_eq hg

/-- For every matrix $\mathbf{Q}$, with zero columns allowed, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$
differs from the orthogonal projector $\mathbf{P}_{\mathbf{Q}}$ onto the column space of
$\mathbf{Q}$ by at most the Gram defect on the support $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column,
$s_j = 1$ otherwise): $\|\mathbf{Q}\mathbf{Q}^{\mathsf{H}} - \mathbf{P}_{\mathbf{Q}}\|_2 \le
\|\mathbf{D}\|_2$. -/
theorem specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect (Q : Matrix m ι 𝕜) :
    specNorm (Q * Qᴴ - rangeProjector Q) ≤ specNorm (gramDefect Q) := by
  obtain ⟨C, hC, hs, -⟩ := exists_norm_mul_conjTranspose_sub_rangeProjector_eq Q
  rw [hs]
  exact (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _) hC)

/-- For every matrix $\mathbf{Q}$, with zero columns allowed, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$
differs from the orthogonal projector $\mathbf{P}_{\mathbf{Q}}$ onto the column space of
$\mathbf{Q}$ by at most the Gram defect on the support $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column,
$s_j = 1$ otherwise), in the Frobenius norm: $\|\mathbf{Q}\mathbf{Q}^{\mathsf{H}} -
\mathbf{P}_{\mathbf{Q}}\|_{\mathsf{F}} \le \|\mathbf{D}\|_{\mathsf{F}}$. -/
theorem frobNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect (Q : Matrix m ι 𝕜) :
    frobNorm (Q * Qᴴ - rangeProjector Q) ≤ frobNorm (gramDefect Q) := by
  obtain ⟨C, hC, -, hf⟩ := exists_norm_mul_conjTranspose_sub_rangeProjector_eq Q
  rw [hf]
  exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
    (mul_le_of_le_one_right (frobNorm_nonneg _) hC)

/-- A basis with small Gram defect on the support has spectral norm close to one: if
$\mathbf{D} = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a
zero column of $\mathbf{Q}$, $s_j = 1$ otherwise) satisfies $\|\mathbf{D}\|_2 \le \eta$, then
$\|\mathbf{Q}\|_2 \le \sqrt{1 + \eta}$. -/
theorem specNorm_le_sqrt_of_specNorm_gramDefect_le {Q : Matrix m ι 𝕜} {η : ℝ}
    (hQ : specNorm (gramDefect Q) ≤ η) : specNorm Q ≤ Real.sqrt (1 + η) := by
  have hd : specNorm (Matrix.diagonal (colSupport Q)) ≤ 1 :=
    specNorm_diagonal_le zero_le_one fun j => norm_colSupport_le_one Q j
  have h1 : specNorm (Qᴴ * Q) ≤ 1 + η := by
    calc specNorm (Qᴴ * Q) = specNorm (gramDefect Q + Matrix.diagonal (colSupport Q)) := by
          rw [gramDefect, sub_add_cancel]
      _ ≤ specNorm (gramDefect Q) + specNorm (Matrix.diagonal (colSupport Q)) :=
          specNorm_add_le _ _
      _ ≤ η + 1 := add_le_add hQ hd
      _ = 1 + η := add_comm _ _
  rw [specNorm_conjTranspose_mul_self] at h1
  exact (Real.le_sqrt (specNorm_nonneg Q) ((sq_nonneg _).trans h1)).2 h1

/-- A basis with small Gram defect on the support has Frobenius norm at most the square root of
its number of columns, nearly: if $\mathbf{Q}$ has $k$ columns and $\mathbf{D} =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} - \operatorname{diag}(\mathbf{s})$ ($s_j = 0$ at a zero column of
$\mathbf{Q}$, $s_j = 1$ otherwise) satisfies $\|\mathbf{D}\|_2 \le \eta$, then
$\|\mathbf{Q}\|_{\mathsf{F}} \le \sqrt{k(1 + \eta)}$. -/
theorem frobNorm_le_sqrt_of_specNorm_gramDefect_le {Q : Matrix m ι 𝕜} {η : ℝ}
    (hQ : specNorm (gramDefect Q) ≤ η) :
    frobNorm Q ≤ Real.sqrt (Fintype.card ι * (1 + η)) := by
  have hdiag : ∀ j, RCLike.re ((Qᴴ * Q) j j) ≤ 1 + η := fun j => by
    have h := (norm_apply_le_specNorm (gramDefect Q) j j).trans hQ
    have h2 : (Qᴴ * Q) j j = gramDefect Q j j + colSupport Q j := by
      rw [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_add_cancel]
    rw [h2, map_add]
    have h3 := RCLike.re_le_norm (gramDefect Q j j)
    have h4 := (RCLike.re_le_norm (colSupport Q j)).trans (norm_colSupport_le_one Q j)
    linarith
  have h2 : frobNorm Q ^ 2 ≤ Fintype.card ι * (1 + η) := by
    rw [frobNorm_sq_eq_re_trace, Matrix.trace, map_sum]
    calc ∑ j, RCLike.re ((Qᴴ * Q).diag j) ≤ ∑ _j : ι, (1 + η) :=
          Finset.sum_le_sum fun j _ => hdiag j
      _ = Fintype.card ι * (1 + η) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Real.le_sqrt (frobNorm_nonneg Q) ((sq_nonneg _).trans h2)).2 h2

end GramDefect

/-! ### Blocks of columns of products and residuals -/

section BlockNorms

variable {𝕜 : Type*} [RCLike 𝕜] {l l' κ : Type*} {N b : ℕ}

/-- Block $j$ of the columns of $\mathbf{A}\mathbf{W}$ is $\mathbf{A}$ times block $j$ of the
columns of $\mathbf{W}$. -/
private theorem blockCols_mul [Fintype κ] (A : Matrix l κ 𝕜) (W : Matrix κ (Fin N) 𝕜) (j : ℕ) :
    blockCols b (A * W) j = A * blockCols b W j := by
  ext i c
  by_cases h : j * b + (c : ℕ) < N <;> simp [blockCols, h, Matrix.mul_apply]

/-- Block $j$ of the columns of a difference is the difference of the blocks. -/
private theorem blockCols_sub (X Y : Matrix l (Fin N) 𝕜) (j : ℕ) :
    blockCols b (X - Y) j = blockCols b X j - blockCols b Y j := by
  ext i c
  by_cases h : j * b + (c : ℕ) < N <;> simp [blockCols, h]

/-- Block $j < q$ of the first $q$ blocks of $\mathbf{V}$ is block $j$ of $\mathbf{V}$. -/
private theorem blockCols_blockPrefix {q : ℕ} (V : Matrix l (Fin N) 𝕜) {j : ℕ} (hj : j < q) :
    blockCols b (blockPrefix b V q) j = blockCols b V j := by
  ext i c
  have h1 : (j + 1) * b ≤ q * b := Nat.mul_le_mul_right b hj
  have h2 := c.2
  have h : j * b + (c : ℕ) < q * b := by
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  simp [blockCols, blockPrefix, h]

/-- The squared Frobenius norm of the first $j + 1$ blocks of columns is that of the first $j$
blocks plus that of block $j$. -/
private theorem frobNorm_blockPrefix_succ_sq [Fintype l] (V : Matrix l (Fin N) 𝕜) (j : ℕ) :
    frobNorm (blockPrefix b V (j + 1)) ^ 2 =
      frobNorm (blockPrefix b V j) ^ 2 + frobNorm (blockCols b V j) ^ 2 := by
  rw [← frobNorm_fromCols_sq, ← blockPrefix_succ_submatrix]
  exact congrArg (· ^ 2)
    (frobNorm_submatrix_equiv _ (Equiv.refl l) (blockSuccEquiv b j)).symm

/-- The squared Frobenius norm of the first $j$ blocks of columns is the sum of the squared
Frobenius norms of the blocks. -/
private theorem frobNorm_blockPrefix_sq_eq_sum [Fintype l] (V : Matrix l (Fin N) 𝕜) (j : ℕ) :
    frobNorm (blockPrefix b V j) ^ 2 =
      ∑ i ∈ Finset.range j, frobNorm (blockCols b V i) ^ 2 := by
  induction j with
  | zero =>
    have : IsEmpty (Fin (0 * b)) := by rw [Nat.zero_mul]; infer_instance
    rw [frobNorm_sq_eq_sum]
    simp
  | succ j ih => rw [frobNorm_blockPrefix_succ_sq, ih, Finset.sum_range_succ]

/-- If every block of columns of $\mathbf{X}$ ($q$ blocks) has Frobenius norm at most $a$ times
that of the same block of $\mathbf{Y}$, $a \ge 0$, then $\|\mathbf{X}\|_{\mathsf{F}} \le
a\|\mathbf{Y}_{<q}\|_{\mathsf{F}}$, with $\mathbf{Y}_{<q}$ the first $q$ blocks of $\mathbf{Y}$. -/
private theorem frobNorm_le_mul_frobNorm_blockPrefix_of_blocks [Fintype l] [Fintype l'] {q : ℕ}
    (X : Matrix l (Fin (q * b)) 𝕜) (Y : Matrix l' (Fin N) 𝕜) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ j < q, frobNorm (blockCols b X j) ≤ a * frobNorm (blockCols b Y j)) :
    frobNorm X ≤ a * frobNorm (blockPrefix b Y q) := by
  have hX := frobNorm_blockPrefix_sq_eq_sum (b := b) X q
  rw [blockPrefix_self] at hX
  refine (sq_le_sq₀ (frobNorm_nonneg _) (mul_nonneg ha (frobNorm_nonneg _))).1 ?_
  rw [mul_pow, frobNorm_blockPrefix_sq_eq_sum Y, hX, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (frobNorm_nonneg _) (h j (Finset.mem_range.1 hj)) 2

/-- If every column of $\mathbf{X}$ has norm at most $a$ times that of the same column of
$\mathbf{Y}$, $a \ge 0$, then $\|\mathbf{X}\|_{\mathsf{F}} \le a\|\mathbf{Y}\|_{\mathsf{F}}$. -/
private theorem frobNorm_le_mul_frobNorm_of_col [Fintype l] [Fintype l'] [Fintype κ]
    {X : Matrix l κ 𝕜} {Y : Matrix l' κ 𝕜} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ c, ‖WithLp.toLp 2 (X.col c)‖ ≤ a * ‖WithLp.toLp 2 (Y.col c)‖) :
    frobNorm X ≤ a * frobNorm Y := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (mul_nonneg ha (frobNorm_nonneg _))).1 ?_
  rw [mul_pow, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h c) 2

/-- If the rows of $\mathbf{C}$ from row $kb$ on are zero, then $\mathbf{U}\mathbf{C}$ is the
product of the first $k$ blocks of columns of $\mathbf{U}$ with the first $k$ blocks of rows of
$\mathbf{C}$. -/
private theorem mul_eq_blockPrefix_mul_blockRowPrefix {k : ℕ} (U : Matrix l (Fin N) 𝕜)
    (C : Matrix (Fin N) κ 𝕜) (hk : k * b ≤ N)
    (hC : ∀ (i : Fin N) (c : κ), k * b ≤ (i : ℕ) → C i c = 0) :
    U * C = blockPrefix b U k * blockRowPrefix b C k := by
  ext i c
  obtain ⟨g, hg⟩ : ∃ g : ℕ → 𝕜,
      ∀ x, g x = if h : x < N then U i ⟨x, h⟩ * C ⟨x, h⟩ c else 0 := ⟨_, fun _ => rfl⟩
  have hL : (U * C) i c = ∑ x ∈ Finset.range N, g x := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun x _ => by rw [hg, dif_pos x.2]
  have hR : (blockPrefix b U k * blockRowPrefix b C k) i c =
      ∑ x ∈ Finset.range (k * b), g x := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < N := lt_of_lt_of_le x.2 hk
    rw [hg, dif_pos hx]
    simp [blockPrefix, blockRowPrefix, hx]
  rw [hL, hR]
  refine (Finset.sum_subset (Finset.range_mono hk) fun x hx hx' => ?_).symm
  have h1 : x < N := Finset.mem_range.1 hx
  have h2 : k * b ≤ x := not_lt.1 fun h => hx' (Finset.mem_range.2 h)
  rw [hg, dif_pos h1, hC ⟨x, h1⟩ c h2, mul_zero]

end BlockNorms

section Step

variable {n k b p N q : ℕ} {η₀ μ ε εmv : ℝ}

/-- One step of the residual relations: let $(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ be a rounded
extension of $\mathbf{Q}$ by $\mathbf{P}$ with parameters $(\eta_0, \mu, \varepsilon)$,
$\mathbf{Q}$ in the window, and let $\mathbf{P}$ be a computed product with
$\|(\mathbf{P} - \mathbf{B}\mathbf{W})\mathbf{e}_c\| \le \varepsilon_{\mathrm{mv}}
\|\mathbf{B}\|_2\|\mathbf{W}\mathbf{e}_c\|$ for every column $c$. If
$\varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ then
$\|\mathbf{B}\mathbf{W} - (\mathbf{Q}\mathbf{H} + \mathbf{Q}'\mathbf{R})\|_{\mathsf{F}} \le
(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}}))
\|\mathbf{B}\|_2\|\mathbf{W}\|_{\mathsf{F}}$. -/
private theorem IsBasisExtensionErr.frobNorm_mul_sub_le {Q : Matrix (Fin n) (Fin k) ℝ}
    {P Q' : Matrix (Fin n) (Fin b) ℝ} {H : Matrix (Fin k) (Fin b) ℝ}
    {R : Matrix (Fin b) (Fin b) ℝ} (hE : IsBasisExtensionErr η₀ μ ε Q P Q' H R)
    (hw : ExtensionWindow η₀ μ b Q) (hε : 0 ≤ ε) (hmv : 0 ≤ εmv)
    (B : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin b) ℝ)
    (hP : ∀ c, ‖WithLp.toLp 2 ((P - B * W).col c)‖ ≤
      εmv * specNorm B * ‖WithLp.toLp 2 (W.col c)‖) :
    frobNorm (B * W - (Q * H + Q' * R)) ≤
      (εmv + ε * (1 + εmv)) * specNorm B * frobNorm W := by
  have h1 : frobNorm (P - B * W) ≤ εmv * specNorm B * frobNorm W :=
    frobNorm_le_mul_frobNorm_of_col (mul_nonneg hmv (specNorm_nonneg B)) hP
  have h2 : frobNorm (B * W) ≤ specNorm B * frobNorm W :=
    frobNorm_mul_le_specNorm_mul_frobNorm B W
  have h3 : frobNorm P ≤ (1 + εmv) * specNorm B * frobNorm W := by
    calc frobNorm P = frobNorm ((P - B * W) + B * W) := by rw [sub_add_cancel]
      _ ≤ frobNorm (P - B * W) + frobNorm (B * W) := frobNorm_add_le _ _
      _ ≤ εmv * specNorm B * frobNorm W + specNorm B * frobNorm W := add_le_add h1 h2
      _ = (1 + εmv) * specNorm B * frobNorm W := by ring
  have h4 := hE.residual hw
  have h5 : B * W - (Q * H + Q' * R) = (P - Q * H - Q' * R) - (P - B * W) := by abel
  rw [h5]
  calc frobNorm ((P - Q * H - Q' * R) - (P - B * W))
      ≤ frobNorm (P - Q * H - Q' * R) + frobNorm (P - B * W) := frobNorm_sub_le _ _
    _ ≤ ε * ((1 + εmv) * specNorm B * frobNorm W) + εmv * specNorm B * frobNorm W :=
        add_le_add (h4.trans (mul_le_mul_of_nonneg_left h3 hε)) h1
    _ = (εmv + ε * (1 + εmv)) * specNorm B * frobNorm W := by ring

/-- The window of every step of a run of block extensions: let the columns of $\mathbf{V}$ be
stored as consecutive blocks of width $b$, with $\mathbf{V}_j$ the first $j$ blocks, and assume
that for every $j < q$ block $j$ is a rounded extension of $\mathbf{V}_j$ with parameters
$(\eta_0, \mu, \varepsilon)$. If $\mu \ge 0$ and $\sqrt{3qb}\,\mu \le \eta_0$, then for every
$j < q$ the Gram defect on the support $\mathbf{D}_j$ of $\mathbf{V}_j$ satisfies
$\sqrt{\|\mathbf{D}_j\|_{\mathsf{F}}^2 + 3b\mu^2} \le \eta_0$. -/
private theorem extensionWindow_blockPrefix_of_blocks (V : Matrix (Fin n) (Fin N) ℝ)
    (W : ℕ → Matrix (Fin n) (Fin b) ℝ) (H : ∀ j : ℕ, Matrix (Fin (j * b)) (Fin b) ℝ)
    (R : ℕ → Matrix (Fin b) (Fin b) ℝ) (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * q * b) * μ ≤ η₀)
    (hE : ∀ j < q, IsBasisExtensionErr η₀ μ ε (blockPrefix b V j) (W j) (blockCols b V j)
      (H j) (R j)) {j : ℕ} (hj : j < q) : ExtensionWindow η₀ μ b (blockPrefix b V j) := by
  have hD := frobNorm_gramDefect_le_of_blocks V W H R hμ hw hE hj.le
  have hw' : Real.sqrt (3 * q * b * μ ^ 2) ≤ η₀ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hμ]
    exact hw
  have hq : (j : ℝ) + 1 ≤ q := by exact_mod_cast hj
  have h2 : frobNorm (gramDefect (blockPrefix b V j)) ^ 2 ≤ 3 * j * b * μ ^ 2 := by
    calc frobNorm (gramDefect (blockPrefix b V j)) ^ 2
        ≤ (Real.sqrt (3 * j * b) * μ) ^ 2 := pow_le_pow_left₀ (frobNorm_nonneg _) hD 2
      _ = 3 * j * b * μ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  unfold ExtensionWindow
  refine (Real.sqrt_le_sqrt ?_).trans hw'
  nlinarith [mul_nonneg (sub_nonneg.2 hq)
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (sq_nonneg μ))]

end Step

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

/-! ### The blocks of a run -/

/-- The window for $q$ blocks follows from the window for $q + 1$ blocks: if $\mu \ge 0$ and
$\sqrt{3(q+1)b}\,\mu \le \eta_0$ then $\sqrt{3qb}\,\mu \le \eta_0$. -/
private theorem sqrt_mul_le_of_window (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) : Real.sqrt (3 * q * b) * μ ≤ η₀ := by
  have hq : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ q
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by gcongr)) hμ).trans hw

/-- The left steps of a rounded run as a run of block extensions of the left basis. -/
private theorem exists_blocks_left (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) :
    ∃ (W : ℕ → Matrix (Fin m) (Fin b) ℝ) (H : ∀ j : ℕ, Matrix (Fin (j * b)) (Fin b) ℝ)
      (R' : ℕ → Matrix (Fin b) (Fin b) ℝ), ∀ j < q,
      IsBasisExtensionErr η₀ μ ε (blockPrefix b U j) (W j) (blockCols b U j) (H j) (R' j) := by
  choose P _ hE using h.left
  exact ⟨fun j => if hj : j < q then P j hj else 0,
    fun j => blockRowPrefix b (blockCols b R j) j, fun j => blockRows b (blockCols b R j) j,
    fun j hj => by simp only [dif_pos hj]; exact hE j hj⟩

/-- The start and the right steps of a rounded run as a run of block extensions of the right
basis. -/
private theorem exists_blocks_right (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) :
    ∃ (W : ℕ → Matrix (Fin n) (Fin b) ℝ) (H : ∀ j : ℕ, Matrix (Fin (j * b)) (Fin b) ℝ)
      (R' : ℕ → Matrix (Fin b) (Fin b) ℝ), ∀ j < q + 1,
      IsBasisExtensionErr η₀ μ ε (blockPrefix b V j) (W j) (blockCols b V j) (H j) (R' j) := by
  choose P _ hE using h.right
  refine ⟨fun j => match j with
      | 0 => Ω
      | j + 1 => if hj : j < q then P j hj else 0,
    fun j => match j with
      | 0 => 0
      | j + 1 => blockRowPrefix b (blockCols b S j) (j + 1),
    fun j => match j with
      | 0 => R₀
      | j + 1 => blockRows b (blockCols b S j) (j + 1), fun j hj => ?_⟩
  rcases j with _ | j
  · exact h.start
  · simp only [dif_pos (Nat.lt_of_succ_lt_succ hj)]
    exact hE j (Nat.lt_of_succ_lt_succ hj)

/-- Every left step of a rounded run is in the window. -/
private theorem window_left (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S)
    (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * q * b) * μ ≤ η₀) {j : ℕ} (hj : j < q) :
    ExtensionWindow η₀ μ b (blockPrefix b U j) := by
  obtain ⟨W, H, R', hE⟩ := h.exists_blocks_left
  exact extensionWindow_blockPrefix_of_blocks U W H R' hμ hw hE hj

/-- The start and every right step of a rounded run are in the window. -/
private theorem window_right (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S)
    (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) {j : ℕ} (hj : j < q + 1) :
    ExtensionWindow η₀ μ b (blockPrefix b V j) := by
  obtain ⟨W, H, R', hE⟩ := h.exists_blocks_right
  exact extensionWindow_blockPrefix_of_blocks V W H R' hμ hw hE hj

/-- The Frobenius norm of the first $q$ blocks of the right basis of a rounded run is at most
$\sqrt{qb(1 + \eta_0)}$. -/
private theorem frobNorm_blockPrefix_right_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (blockPrefix b V q) ≤ Real.sqrt (q * b * (1 + η₀)) := by
  obtain ⟨W, H, R', hE⟩ := h.exists_blocks_right
  have hD := frobNorm_gramDefect_le_of_blocks V W H R' hμ hw hE (Nat.le_succ q)
  have hs : specNorm (gramDefect (blockPrefix b V q)) ≤ η₀ :=
    (specNorm_gramDefect_le_frobNorm _).trans (hD.trans (sqrt_mul_le_of_window hμ hw))
  have h0 := frobNorm_le_sqrt_of_specNorm_gramDefect_le hs
  rwa [Fintype.card_fin, Nat.cast_mul] at h0

/-- The spectral norm of the Gram defect on the support of the left basis of a rounded run is
within the window $\eta_0$. -/
private theorem specNorm_gramDefect_left_le
    (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) : specNorm (gramDefect U) ≤ η₀ :=
  (specNorm_gramDefect_le_frobNorm U).trans
    ((h.frobNorm_gramDefect_left_le hμ (sqrt_mul_le_of_window hμ hw)).trans
      (sqrt_mul_le_of_window hμ hw))

/-- The Frobenius norm of the left basis of a rounded run is at most $\sqrt{qb(1 + \eta_0)}$. -/
private theorem frobNorm_left_le (h : IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V R₀ R S)
    (hμ : 0 ≤ μ) (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm U ≤ Real.sqrt (q * b * (1 + η₀)) := by
  have h0 := frobNorm_le_sqrt_of_specNorm_gramDefect_le (h.specNorm_gramDefect_left_le hμ hw)
  rwa [Fintype.card_fin, Nat.cast_mul] at h0

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
  have hκ : 0 ≤ (εmv + ε * (1 + εmv)) * specNorm A :=
    mul_nonneg (add_nonneg hmv (mul_nonneg hε (add_nonneg zero_le_one hmv))) (specNorm_nonneg A)
  have hstep : ∀ j < q, frobNorm (blockCols b (A * blockPrefix b V q - U * R) j) ≤
      (εmv + ε * (1 + εmv)) * specNorm A * frobNorm (blockCols b V j) := by
    intro j hj
    obtain ⟨P, hP, hE⟩ := h.left j hj
    have hk : (j + 1) * b ≤ q * b := Nat.mul_le_mul_right b hj
    rw [blockCols_sub, blockCols_mul, blockCols_mul, blockCols_blockPrefix V hj,
      mul_eq_blockPrefix_mul_blockRowPrefix (b := b) U (blockCols b R j) hk
        (h.left_support j hj), blockPrefix_succ_mul_blockRowPrefix_succ]
    exact hE.frobNorm_mul_sub_le (h.window_left hμ (sqrt_mul_le_of_window hμ hw) hj) hε hmv A _
      hP
  calc frobNorm (A * blockPrefix b V q - U * R)
      ≤ (εmv + ε * (1 + εmv)) * specNorm A * frobNorm (blockPrefix b V q) :=
        frobNorm_le_mul_frobNorm_blockPrefix_of_blocks _ V hκ hstep
    _ ≤ (εmv + ε * (1 + εmv)) * specNorm A * Real.sqrt (q * b * (1 + η₀)) :=
        mul_le_mul_of_nonneg_left (h.frobNorm_blockPrefix_right_le hμ hw) hκ
    _ = (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by ring

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
  have hκ : 0 ≤ (εmv + ε * (1 + εmv)) * specNorm A :=
    mul_nonneg (add_nonneg hmv (mul_nonneg hε (add_nonneg zero_le_one hmv))) (specNorm_nonneg A)
  have hstep : ∀ j < q, frobNorm (blockCols b (Aᵀ * U - V * S) j) ≤
      (εmv + ε * (1 + εmv)) * specNorm A * frobNorm (blockCols b U j) := by
    intro j hj
    obtain ⟨P, hP, hE⟩ := h.right j hj
    have hk : (j + 1 + 1) * b ≤ (q + 1) * b := Nat.mul_le_mul_right b (Nat.succ_lt_succ hj)
    have hP' : ∀ c, ‖WithLp.toLp 2 ((P - Aᵀ * blockCols b U j).col c)‖ ≤
        εmv * specNorm Aᵀ * ‖WithLp.toLp 2 ((blockCols b U j).col c)‖ := by
      rw [specNorm_transpose]
      exact hP
    have h0 := hE.frobNorm_mul_sub_le (h.window_right hμ hw (Nat.succ_lt_succ hj)) hε hmv Aᵀ _
      hP'
    rw [specNorm_transpose] at h0
    rw [blockCols_sub, blockCols_mul, blockCols_mul,
      mul_eq_blockPrefix_mul_blockRowPrefix (b := b) V (blockCols b S j) hk
        (fun i c hi => h.right_support j hj i c hi),
      blockPrefix_succ_mul_blockRowPrefix_succ b V (blockCols b S j) (j + 1)]
    exact h0
  have h1 := frobNorm_le_mul_frobNorm_blockPrefix_of_blocks _ U hκ hstep
  rw [blockPrefix_self] at h1
  calc frobNorm (Aᵀ * U - V * S)
      ≤ (εmv + ε * (1 + εmv)) * specNorm A * frobNorm U := h1
    _ ≤ (εmv + ε * (1 + εmv)) * specNorm A * Real.sqrt (q * b * (1 + η₀)) :=
        mul_le_mul_of_nonneg_left (h.frobNorm_left_le hμ hw) hκ
    _ = (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by ring

/-! ### The forward bound -/

/-- The splitting behind the forward bound: with $\mathbf{P}_{\mathbf{U}}$ the orthogonal
projector onto the range of $\mathbf{U}$,
$$\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}} =
(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A} -
(\mathbf{U}\mathbf{U}^{\mathsf{T}} - \mathbf{P}_{\mathbf{U}})\mathbf{A} +
\mathbf{U}(\mathbf{A}^{\mathsf{T}}\mathbf{U} - \mathbf{V}\mathbf{S})^{\mathsf{T}}.$$ -/
private theorem sub_mul_transpose_mul_transpose_eq (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin (q * b)) ℝ) (V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ)
    (S : Matrix (Fin ((q + 1) * b)) (Fin (q * b)) ℝ) :
    A - U * Sᵀ * Vᵀ = (1 - rangeProjector U) * A - (U * Uᵀ - rangeProjector U) * A +
      U * (Aᵀ * U - V * S)ᵀ := by
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  abel

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
  have hwl := sqrt_mul_le_of_window hμ hw
  have hD := h.frobNorm_gramDefect_left_le hμ hwl
  have hU : specNorm U ≤ Real.sqrt (1 + η₀) :=
    specNorm_le_sqrt_of_specNorm_gramDefect_le (h.specNorm_gramDefect_left_le hμ hw)
  have hP : specNorm (U * Uᵀ - rangeProjector U) ≤ Real.sqrt (3 * q * b) * μ := by
    have h0 := specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect U
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h0
    exact h0.trans ((specNorm_gramDefect_le_frobNorm U).trans hD)
  have hR : frobNorm (Aᵀ * U - V * S)ᵀ ≤
      (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by
    rw [frobNorm_transpose]
    exact h.frobNorm_transpose_mul_sub_mul_le hμ hε hmv hw
  have h2 : specNorm ((U * Uᵀ - rangeProjector U) * A) ≤
      Real.sqrt (3 * q * b) * μ * specNorm A :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hP (specNorm_nonneg A))
  have h3 : specNorm (U * (Aᵀ * U - V * S)ᵀ) ≤ Real.sqrt (1 + η₀) *
      ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A) :=
    (specNorm_mul_le _ _).trans (mul_le_mul hU ((specNorm_le_frobNorm _).trans hR)
      (specNorm_nonneg _) (Real.sqrt_nonneg _))
  rw [sub_mul_transpose_mul_transpose_eq A U V S]
  exact ((specNorm_add_le _ _).trans (add_le_add ((specNorm_sub_le _ _).trans
    (add_le_add le_rfl h2)) h3)).trans_eq (by ring)

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
  have hwl := sqrt_mul_le_of_window hμ hw
  have hD := h.frobNorm_gramDefect_left_le hμ hwl
  have hU : specNorm U ≤ Real.sqrt (1 + η₀) :=
    specNorm_le_sqrt_of_specNorm_gramDefect_le (h.specNorm_gramDefect_left_le hμ hw)
  have hP : frobNorm (U * Uᵀ - rangeProjector U) ≤ Real.sqrt (3 * q * b) * μ := by
    have h0 := frobNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect U
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h0
    exact h0.trans hD
  have hR : frobNorm (Aᵀ * U - V * S)ᵀ ≤
      (εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A := by
    rw [frobNorm_transpose]
    exact h.frobNorm_transpose_mul_sub_mul_le hμ hε hmv hw
  have h2 : frobNorm ((U * Uᵀ - rangeProjector U) * A) ≤
      Real.sqrt (3 * q * b) * μ * specNorm A :=
    (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_right hP (specNorm_nonneg A))
  have h3 : frobNorm (U * (Aᵀ * U - V * S)ᵀ) ≤ Real.sqrt (1 + η₀) *
      ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)) * specNorm A) :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans (mul_le_mul hU hR
      (frobNorm_nonneg _) (Real.sqrt_nonneg _))
  rw [sub_mul_transpose_mul_transpose_eq A U V S]
  exact ((frobNorm_add_le _ _).trans (add_le_add ((frobNorm_sub_le _ _).trans
    (add_le_add le_rfl h2)) h3)).trans_eq (by ring)

end IsBlockGolubKahanErr

end NLAlib
