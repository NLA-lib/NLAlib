/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Inequalities for singular values

Singular values are subadditive in Weyl's sense, $1$-Lipschitz in the spectral norm,
submultiplicative, decrease under projections and under passing to submatrices, and move by at
most $r$ positions under a perturbation of rank $r$. Because singular values are padded with
zeros, none of these statements carries an index side condition.

`NLAlib.singularGap A k` is the gap $\sigma_{k-1}(\mathbf{A}) - \sigma_k(\mathbf{A})$ separating the
$k$ largest singular values from the rest.

## Main definitions

* `NLAlib.singularGap`: the gap below the $k$ largest singular values.
* `NLAlib.singularGapRatio`: the relative gap
  $(\sigma_i(\mathbf{A}) - \sigma_j(\mathbf{A}))/(\sigma_i(\mathbf{A}) + \sigma_j(\mathbf{A}))$.

## Main results

* `NLAlib.singularValues_add_le`: Weyl's inequality for singular values.
* `NLAlib.abs_singularValues_sub_le_specNorm`: singular values are $1$-Lipschitz.
* `NLAlib.singularValues_mul_le_specNorm_mul`, `NLAlib.singularValues_mul_add_le`: products.
* `NLAlib.singularValues_add_le_of_rank_le`: low-rank perturbations.
* `NLAlib.singularValues_submatrix_le`: submatrices.
* `IsStarProjection.singularValues_mul_le`: projections.
* `NLAlib.singularValues_one_sub_rangeProjector_mul_le_of_range_le`: a larger range gives a smaller
  projection residual, singular value by singular value.
* `NLAlib.specNorm_conjTranspose_mul_self_sub_one_le_iff`,
  `NLAlib.specNorm_conjTranspose_mul_self_sub_one_eq_iSup`: the Gram error
  $\|\mathbf{A}^{\mathsf{H}}\mathbf{A} - \mathbf{I}\|_2$ through the singular values.
* `NLAlib.specNorm_le_sqrt_mul_one_add_of_specNorm_sub_smul_one_le`,
  `NLAlib.sqrt_mul_one_sub_le_singularValues_of_specNorm_sub_smul_one_le`: from a Gram error
  relative to $N\mathbf{I}$ to bounds on the extreme singular values.
* `NLAlib.exists_degree_lt_div_sq_le_exp_singularGapRatio`: a Chebyshev filter of degree $d$
  separating the head from the tail at the rate $4e^{-8d\sqrt{\gamma}}$ of the relative gap.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Dimension counts -/

/-- The preimage of a subspace under a matrix has codimension at most that of the subspace. -/
private theorem card_add_finrank_le_finrank_comap_add_card (B : Matrix p n 𝕜)
    (W : Submodule 𝕜 (p → 𝕜)) :
    Fintype.card n + Module.finrank 𝕜 W ≤
      Module.finrank 𝕜 (W.comap B.mulVecLin) + Fintype.card p := by
  have hker : W.comap B.mulVecLin = LinearMap.ker (W.mkQ ∘ₗ B.mulVecLin) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h1 := (W.mkQ ∘ₗ B.mulVecLin).finrank_range_add_finrank_ker
  have h2 : Module.finrank 𝕜 (LinearMap.range (W.mkQ ∘ₗ B.mulVecLin)) ≤
      Module.finrank 𝕜 ((p → 𝕜) ⧸ W) := Submodule.finrank_le _
  have h3 := W.finrank_quotient_add_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1 h3
  rw [hker]
  omega

/-! ### Sums -/

/-- **Weyl's inequality for singular values.**
$\sigma_{i+j}(\mathbf{A} + \mathbf{B}) \le \sigma_i(\mathbf{A}) + \sigma_j(\mathbf{B})$, for all
indices from $0$. [HornJohnson1991, Theorem 3.3.16].
Result: weyl-singular-values -/
theorem singularValues_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    singularValues (A + B) (i + j) ≤ singularValues A i + singularValues B j := by
  obtain ⟨W₁, h₁, hA⟩ := exists_submodule_norm_mulVec_le A i
  obtain ⟨W₂, h₂, hB⟩ := exists_submodule_norm_mulVec_le B j
  refine singularValues_le_of_forall_mem (A + B) (W₁ ⊓ W₂) ?_
    (add_nonneg (singularValues_nonneg A i) (singularValues_nonneg B j)) fun x hx => ?_
  · have h := Submodule.finrank_add_finrank_le_card_add_finrank_inf W₁ W₂
    omega
  · rw [Matrix.add_mulVec, WithLp.toLp_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA x hx.1) (hB x hx.2))

/-- A perturbation raises each singular value by at most its spectral norm:
$\sigma_k(\mathbf{A} + \mathbf{E}) \le \sigma_k(\mathbf{A}) + \|\mathbf{E}\|_2$. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix m n 𝕜) (k : ℕ) :
    singularValues (A + E) k ≤ singularValues A k + specNorm E := by
  have h := singularValues_add_le A E k 0
  rwa [add_zero, singularValues_zero_eq_specNorm] at h

/-- **Singular values are $1$-Lipschitz in the spectral norm**:
$\lvert \sigma_k(\mathbf{A}) - \sigma_k(\mathbf{B}) \rvert \le \|\mathbf{A} - \mathbf{B}\|_2$ for
every $k$.
[HornJohnson2013, Corollary 7.3.5].
Result: weyl-singular-values, singular-value-perturbation -/
theorem abs_singularValues_sub_le_specNorm (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularValues A k - singularValues B k| ≤ specNorm (A - B) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := singularValues_add_le_add_specNorm B (A - B) k
    rw [add_sub_cancel] at h
    linarith
  · have h := singularValues_add_le_add_specNorm A (B - A) k
    rw [add_sub_cancel, specNorm_sub_comm] at h
    linarith

/-- Singular values are $1$-Lipschitz in the Frobenius norm:
$\lvert \sigma_k(\mathbf{A}) - \sigma_k(\mathbf{B}) \rvert \le
\|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$. -/
theorem abs_singularValues_sub_le_frobNorm (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularValues A k - singularValues B k| ≤ frobNorm (A - B) := by
  exact (abs_singularValues_sub_le_specNorm A B k).trans (specNorm_le_frobNorm _)

/-- **Low-rank perturbation.** If $\operatorname{rank} \mathbf{B} \le r$ then
$\sigma_{k+r}(\mathbf{A} + \mathbf{B}) \le \sigma_k(\mathbf{A})$ for every $k$.
[HornJohnson1991, Theorem 3.3.16].
Result: low-rank-interlacing -/
theorem singularValues_add_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {r : ℕ}
    (hB : B.rank ≤ r) (k : ℕ) : singularValues (A + B) (k + r) ≤ singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_norm_mulVec_le A k
  refine singularValues_le_of_forall_mem (A + B) (W ⊓ LinearMap.ker B.mulVecLin) ?_
    (singularValues_nonneg A k) fun x hx => ?_
  · have h₁ := Submodule.finrank_add_finrank_le_card_add_finrank_inf W (LinearMap.ker B.mulVecLin)
    have h₂ := Matrix.finrank_ker_add_rank B
    omega
  · have hx₂ : B *ᵥ x = 0 := LinearMap.mem_ker.mp hx.2
    rw [Matrix.add_mulVec, hx₂, add_zero]
    exact hA x hx.1

/-- **Low-rank perturbation, lower.** If $\operatorname{rank} \mathbf{B} \le r$ then
$\sigma_{k+r}(\mathbf{A}) \le \sigma_k(\mathbf{A} + \mathbf{B})$ for every $k$: the mirror of
`NLAlib.singularValues_add_le_of_rank_le`.
[HornJohnson1991, Theorem 3.3.16].
Result: low-rank-interlacing -/
theorem singularValues_le_singularValues_add_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜}
    {r : ℕ} (hB : B.rank ≤ r) (k : ℕ) :
    singularValues A (k + r) ≤ singularValues (A + B) k := by
  have h := singularValues_add_le_of_rank_le (A + B) ((Matrix.rank_neg B).trans_le hB) k
  rwa [add_neg_cancel_right] at h

/-- Subtracting a matrix of rank at most $k$ lowers the index of a singular value by at most
$k$: $\sigma_{k+i}(\mathbf{A}) \le \sigma_i(\mathbf{A} - \mathbf{B})$. With $i = 0$ this is the
Eckart–Young lower bound in the spectral norm. [HornJohnson1991, Theorem 3.3.16]. -/
theorem singularValues_add_le_singularValues_sub_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) (i : ℕ) :
    singularValues A (k + i) ≤ singularValues (A - B) i := by
  have h := singularValues_add_le_of_rank_le (A - B) hB i
  rwa [sub_add_cancel, add_comm] at h

/-! ### Products -/

/-- A left factor scales singular values by at most its spectral norm:
$\sigma_k(\mathbf{B}\mathbf{A}) \le \|\mathbf{B}\|_2 \, \sigma_k(\mathbf{A})$.
[HornJohnson1991, Theorem 3.3.16]. -/
theorem singularValues_mul_le_specNorm_mul (B : Matrix l m 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (B * A) k ≤ specNorm B * singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_norm_mulVec_le A k
  refine singularValues_le_of_forall_mem (B * A) W hW
    (mul_nonneg (specNorm_nonneg B) (singularValues_nonneg A k)) fun x hx => ?_
  rw [← Matrix.mulVec_mulVec, mul_assoc]
  exact (norm_toLp_mulVec_le B _).trans
    (mul_le_mul_of_nonneg_left (hA x hx) (specNorm_nonneg B))

/-- A right factor scales singular values by at most its spectral norm:
$\sigma_k(\mathbf{A}\mathbf{C}) \le \sigma_k(\mathbf{A}) \, \|\mathbf{C}\|_2$. -/
theorem singularValues_mul_le_mul_specNorm (A : Matrix m n 𝕜) (C : Matrix n p 𝕜) (k : ℕ) :
    singularValues (A * C) k ≤ singularValues A k * specNorm C := by
  have h := singularValues_mul_le_specNorm_mul Cᴴ Aᴴ k
  rwa [← Matrix.conjTranspose_mul, singularValues_conjTranspose, singularValues_conjTranspose,
    specNorm_conjTranspose, mul_comm] at h

/-- **Singular values of a product.**
$\sigma_{i+j}(\mathbf{A}\mathbf{B}) \le \sigma_i(\mathbf{A}) \, \sigma_j(\mathbf{B})$ for all
indices from $0$.
[HornJohnson1991, Theorem 3.3.16].
Result: weyl-singular-values-product -/
theorem singularValues_mul_add_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (i j : ℕ) :
    singularValues (A * B) (i + j) ≤ singularValues A i * singularValues B j := by
  obtain ⟨W₁, h₁, hA⟩ := exists_submodule_norm_mulVec_le A i
  obtain ⟨W₂, h₂, hB⟩ := exists_submodule_norm_mulVec_le B j
  refine singularValues_le_of_forall_mem (A * B) (W₂ ⊓ W₁.comap B.mulVecLin) ?_
    (mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B j)) fun x hx => ?_
  · have h := Submodule.finrank_add_finrank_le_card_add_finrank_inf W₂ (W₁.comap B.mulVecLin)
    have hc := card_add_finrank_le_finrank_comap_add_card B W₁
    omega
  · rw [← Matrix.mulVec_mulVec, mul_assoc]
    exact (hA _ hx.2).trans
      (mul_le_mul_of_nonneg_left (hB x hx.1) (singularValues_nonneg A i))

omit [Fintype n] in
/-- The Gram matrix of a product, as a conjugation of the Gram matrix of the left factor:
$(\mathbf{T}\mathbf{X})^{\mathsf{H}}(\mathbf{T}\mathbf{X}) =
\mathbf{X}^{\mathsf{H}}(\mathbf{T}^{\mathsf{H}}\mathbf{T})\mathbf{X}$. -/
private theorem conjTranspose_mul_mul_mul (T : Matrix l m 𝕜) (X : Matrix m n 𝕜) :
    (T * X)ᴴ * (T * X) = Xᴴ * (Tᴴ * T) * X := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A left factor $\mathbf{T}$ with $\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq a\mathbf{I}$
enlarges squared singular values by at most $a$:
$\sigma_k(\mathbf{T}\mathbf{X})^2 \le a \, \sigma_k(\mathbf{X})^2$. -/
theorem singularValues_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m]
    {T : Matrix l m 𝕜} {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜)
    (k : ℕ) : singularValues (T * X) k ^ 2 ≤ a * singularValues X k ^ 2 := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim X 0, Matrix.mul_zero, singularValues_zero, singularValues_zero,
      Pi.zero_apply, zero_pow two_ne_zero, mul_zero]
  · have ha : 0 ≤ a := by
      have hi := conjTranspose_mul_self_le_smul_one_iff.mp h (Pi.single i 1)
      rw [PiLp.toLp_single, PiLp.norm_single, norm_one, one_pow, mul_one] at hi
      exact (sq_nonneg _).trans hi
    have hle := conjTranspose_mul_mul_le_conjTranspose_mul_mul h X
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← conjTranspose_mul_mul_mul] at hle
    have hk := eigenvalue_le_eigenvalue_of_le hle (Matrix.isHermitian_conjTranspose_mul_self _) k
    rwa [eigenvalue_real_smul _ ha,
      ← singularValues_sq, ← singularValues_sq] at hk

/-- A left factor $\mathbf{T}$ with $a\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ shrinks
squared singular values by at most $a$:
$a \, \sigma_k(\mathbf{X})^2 \le \sigma_k(\mathbf{T}\mathbf{X})^2$. This is how a subspace
embedding transfers singular values from the sketched matrix to the original one. -/
theorem mul_singularValues_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) (k : ℕ) :
    a * singularValues X k ^ 2 ≤ singularValues (T * X) k ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · have hle := conjTranspose_mul_mul_le_conjTranspose_mul_mul h X
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← conjTranspose_mul_mul_mul] at hle
    have hk := eigenvalue_le_eigenvalue_of_le hle
      ((Matrix.isHermitian_conjTranspose_mul_self X).smul (IsSelfAdjoint.all a)) k
    rwa [eigenvalue_real_smul _ ha,
      ← singularValues_sq, ← singularValues_sq] at hk
  · exact (mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)).trans (sq_nonneg _)

/-- For a square matrix, a lower Loewner bound on $\mathbf{T}^{\mathsf{H}}\mathbf{T}$ is also a
lower bound on $\mathbf{T}\mathbf{T}^{\mathsf{H}}$: if
$a\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ then
$a\mathbf{I} \preceq \mathbf{T}\mathbf{T}^{\mathsf{H}}$. The two Gram matrices have the same
smallest eigenvalue. -/
theorem smul_one_le_mul_conjTranspose_self_of_smul_one_le [DecidableEq m] {T : Matrix m m 𝕜}
    {a : ℝ} (hT : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) : a • (1 : Matrix m m 𝕜) ≤ T * Tᴴ := by
  rcases Nat.eq_zero_or_pos (Fintype.card m) with h0 | hpos
  · have : IsEmpty m := Fintype.card_eq_zero_iff.mp h0
    exact le_of_eq (Subsingleton.elim _ _)
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card m := ⟨Fintype.card m - 1, by omega⟩
    have h₁ := le_singularValues_last_sq_of_smul_one_le hk hT
    have h₂ := singularValues_last_sq_smul_one_le Tᴴ hk
    rw [singularValues_conjTranspose, smul_one_le_conjTranspose_mul_self_iff] at h₂
    have e : T * Tᴴ = Tᴴᴴ * Tᴴ := by rw [Matrix.conjTranspose_conjTranspose]
    rw [e, smul_one_le_conjTranspose_mul_self_iff]
    exact fun x => (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)).trans (h₂ x)

/-! ### Submatrices and projections -/

/-- Selecting columns by an injective map does not increase any singular value. -/
private theorem singularValues_submatrix_cols_le (A : Matrix m n 𝕜) {c : p → n}
    (hc : Function.Injective c) (k : ℕ) :
    singularValues (A.submatrix id c) k ≤ singularValues A k := by
  classical
  rw [← mul_selectionMatrix]
  exact (singularValues_mul_le_mul_specNorm A _ k).trans (mul_le_of_le_one_right
    (singularValues_nonneg A k) (hasOrthonormalCols_selectionMatrix hc).specNorm_le_one)

/-- **Singular values of a submatrix.** A submatrix selected by injective maps $r$ (rows) and $c$
(columns) has singular values at most those of the matrix:
$\sigma_k(\mathbf{A}_{r,c}) \le \sigma_k(\mathbf{A})$, where $\mathbf{A}_{r,c}$ is
`A.submatrix r c`. [HornJohnson1991, Corollary 3.1.3].
Result: singular-value-interlacing -/
theorem singularValues_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) (k : ℕ) :
    singularValues (A.submatrix r c) k ≤ singularValues A k := by
  have h : A.submatrix r c = ((Aᴴ.submatrix id r)ᴴ).submatrix id c := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose,
      Matrix.submatrix_submatrix]
    rfl
  rw [h]
  refine (singularValues_submatrix_cols_le _ hc k).trans ?_
  rw [singularValues_conjTranspose, ← singularValues_conjTranspose A]
  exact singularValues_submatrix_cols_le Aᴴ hr k

/-- **Interlacing for deleted columns.** If the injective $c : p \to n$ selects $\lvert p \rvert$
of the $\lvert p \rvert + d$ columns of $\mathbf{A}$, then
$\sigma_{k+d}(\mathbf{A}) \le \sigma_k(\mathbf{A}')$ for every $k$, where $\mathbf{A}'$ is
`A.submatrix id c`. [HornJohnson1991, Corollary 3.1.3].
Result: singular-value-interlacing -/
theorem singularValues_le_singularValues_submatrix_cols (A : Matrix m n 𝕜) {c : p → n}
    (hc : Function.Injective c) {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) (k : ℕ) :
    singularValues A (k + d) ≤ singularValues (A.submatrix id c) k := by
  by_cases hk : k < Fintype.card p
  · have hG : (A.submatrix id c)ᴴ * A.submatrix id c = (Aᴴ * A).submatrix c c := by
      rw [Matrix.conjTranspose_submatrix]
      exact Matrix.submatrix_mul_equiv Aᴴ A c (Equiv.refl m) c
    refine (pow_le_pow_iff_left₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)
      two_ne_zero).mp ?_
    rw [singularValues_sq, singularValues_sq, hG]
    exact (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_le_eigenvalue_submatrix
      hc hk hd
  · rw [singularValues_of_card_cols_le A (by omega)]
    exact singularValues_nonneg _ k

/-- **Interlacing for deleted rows.** If the injective $r : l \to m$ selects $\lvert l \rvert$ of
the $\lvert l \rvert + d$ rows of $\mathbf{A}$, then
$\sigma_{k+d}(\mathbf{A}) \le \sigma_k(\mathbf{A}')$ for every $k$, where $\mathbf{A}'$ is
`A.submatrix r id`. [HornJohnson1991, Corollary 3.1.3].
Result: singular-value-interlacing -/
theorem singularValues_le_singularValues_submatrix_rows (A : Matrix m n 𝕜) {r : l → m}
    (hr : Function.Injective r) {d : ℕ} (hd : Fintype.card l + d = Fintype.card m) (k : ℕ) :
    singularValues A (k + d) ≤ singularValues (A.submatrix r id) k := by
  have h := singularValues_le_singularValues_submatrix_cols Aᴴ hr hd k
  rwa [singularValues_conjTranspose, ← singularValues_conjTranspose (Aᴴ.submatrix id r),
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose] at h

/-- Left multiplication by an orthogonal projector does not increase any singular value:
$\sigma_k(\mathbf{P}\mathbf{A}) \le \sigma_k(\mathbf{A})$. -/
theorem _root_.IsStarProjection.singularValues_mul_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (P * A) k ≤ singularValues A k := by
  exact (singularValues_mul_le_specNorm_mul P A k).trans
    (mul_le_of_le_one_left (singularValues_nonneg A k) hP.specNorm_le_one)

/-- The projection residual has singular values at most those of the matrix:
$\sigma_k((\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}) \le \sigma_k(\mathbf{A})$. -/
theorem singularValues_one_sub_rangeProjector_mul_le [DecidableEq m] (Y : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues ((1 - rangeProjector Y) * A) k ≤ singularValues A k := by
  exact (isStarProjection_one_sub_rangeProjector Y).singularValues_mul_le A k

/-! ### Gram matrices close to a multiple of the identity -/

/-- The Gram error is the largest deviation of a squared singular value from one:
$$\|\mathbf{A}^{\mathsf{H}}\mathbf{A} - \mathbf{I}\|_2
  = \max_{k < \lvert n \rvert} \lvert \sigma_k(\mathbf{A})^2 - 1 \rvert,$$
the maximum over the indices below the number of columns (an empty supremum, zero, when there are
none). -/
theorem specNorm_conjTranspose_mul_self_sub_one_eq_iSup [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm (Aᴴ * A - 1) = ⨆ k : Fin (Fintype.card n), |singularValues A k ^ 2 - 1| := by
  have hG := Matrix.isHermitian_conjTranspose_mul_self A
  have hH : (Aᴴ * A - 1).IsHermitian := hG.sub Matrix.isHermitian_one
  have he : ∀ k < Fintype.card n,
      eigenvalue (Aᴴ * A - 1) k = singularValues A k ^ 2 - 1 := fun k hk => by
    rw [singularValues_sq, sub_eq_add_neg, ← neg_one_smul ℝ (1 : Matrix n n 𝕜),
      hG.eigenvalue_add_smul_one _ hk, ← sub_eq_add_neg]
  have hbdd : BddAbove (Set.range fun k : Fin (Fintype.card n) =>
      |singularValues A k ^ 2 - 1|) := (Set.finite_range _).bddAbove
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    have : IsEmpty (Fin (Fintype.card n)) := by rw [h0]; infer_instance
    rw [Real.iSup_of_isEmpty, Subsingleton.elim (Aᴴ * A - 1) 0, specNorm_zero]
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
    have : Nonempty (Fin (Fintype.card n)) := ⟨⟨0, hpos⟩⟩
    refine le_antisymm ?_ (ciSup_le fun i => ?_)
    · rw [hH.specNorm_eq_max hk, he 0 hpos, he k (by omega)]
      exact max_le (le_ciSup hbdd ⟨0, hpos⟩) (le_ciSup hbdd ⟨k, by omega⟩)
    · rw [← he i i.isLt]
      exact hH.abs_eigenvalue_le_specNorm i

/-- A Gram error of at most $\varepsilon$ says that every squared singular value is within
$\varepsilon$ of one: $\|\mathbf{A}^{\mathsf{H}}\mathbf{A} - \mathbf{I}\|_2 \le \varepsilon$ if
and only if $\lvert \sigma_k(\mathbf{A})^2 - 1 \rvert \le \varepsilon$ for every
$k < \lvert n \rvert$. This is the equivalence between the Gram form of a subspace embedding and
its singular value form. The hypothesis $0 \le \varepsilon$ is needed only for a matrix with no
columns. -/
theorem specNorm_conjTranspose_mul_self_sub_one_le_iff [DecidableEq n] {A : Matrix m n 𝕜}
    {ε : ℝ} (hε : 0 ≤ ε) :
    specNorm (Aᴴ * A - 1) ≤ ε ↔ ∀ k < Fintype.card n, |singularValues A k ^ 2 - 1| ≤ ε := by
  rw [specNorm_conjTranspose_mul_self_sub_one_eq_iSup]
  refine ⟨fun h k hk => ?_, fun h => Real.iSup_le (fun i => h i i.isLt) hε⟩
  exact (le_ciSup (f := fun k : Fin (Fintype.card n) => |singularValues A k ^ 2 - 1|)
    (Set.finite_range _).bddAbove ⟨k, hk⟩).trans h

/-- **Approximate isometries, upper bound.** For $\alpha \ge 0$, if
$\|\mathbf{A}^{\mathsf{H}}\mathbf{A} - N\mathbf{I}\|_2 \le N \max(\alpha, \alpha^2)$, then
$\|\mathbf{A}\|_2 \le \sqrt{N} (1 + \alpha)$. This is the deterministic step from a
concentration bound for $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, with $N$ the number of rows, to the
largest singular value. [Vershynin2018, Lemma 4.1.5]; stated there for $N = 1$ over $\mathbb{R}$. -/
theorem specNorm_le_sqrt_mul_one_add_of_specNorm_sub_smul_one_le [DecidableEq n]
    {A : Matrix m n 𝕜} {N α : ℝ} (hα : 0 ≤ α)
    (h : specNorm (Aᴴ * A - N • (1 : Matrix n n 𝕜)) ≤ N * max α (α ^ 2)) :
    specNorm A ≤ √N * (1 + α) := by
  have hle := conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le h
  have hmax : max α (α ^ 2) ≤ 2 * α + α ^ 2 := max_le (by nlinarith) (by nlinarith)
  rw [conjTranspose_mul_self_le_smul_one_iff] at hle
  rw [specNorm_le_iff (by positivity)]
  intro x
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ((hle x).trans ?_)
  rw [mul_pow, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rcases le_total 0 N with hN | hN
  · rw [Real.sq_sqrt hN]
    nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos hN]
    nlinarith [le_max_right α (α ^ 2), sq_nonneg α]

/-- **Approximate isometries, lower bound.** For $\alpha \ge 0$, if
$\|\mathbf{A}^{\mathsf{H}}\mathbf{A} - N\mathbf{I}\|_2 \le N \max(\alpha, \alpha^2)$, then the
smallest singular value of $\mathbf{A}$ is at least $\sqrt{N}(1 - \alpha)$:
$\sqrt{N}(1 - \alpha) \le \sigma_k(\mathbf{A})$ for $k + 1 = \lvert n \rvert$.
[Vershynin2018, Lemma 4.1.5]; stated there for $N = 1$ over $\mathbb{R}$. -/
theorem sqrt_mul_one_sub_le_singularValues_of_specNorm_sub_smul_one_le [DecidableEq n]
    {A : Matrix m n 𝕜} {N α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (h : specNorm (Aᴴ * A - N • (1 : Matrix n n 𝕜)) ≤ N * max α (α ^ 2)) :
    √N * (1 - α) ≤ singularValues A k := by
  rcases le_total 1 α with hα1 | hα1
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg N) (by linarith)).trans
      (singularValues_nonneg A k)
  rcases le_total N 0 with hN | hN
  · rw [Real.sqrt_eq_zero_of_nonpos hN, zero_mul]
    exact singularValues_nonneg A k
  have hle := sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le h
  have h2 := le_singularValues_last_sq_of_smul_one_le hk hle
  rw [max_eq_left (by nlinarith)] at h2
  refine (sq_le_sq₀ (by have := Real.sqrt_nonneg N; nlinarith) (singularValues_nonneg A k)).mp
    (le_trans ?_ h2)
  rw [mul_pow, Real.sq_sqrt hN]
  nlinarith [mul_nonneg (mul_nonneg hN (sub_nonneg.mpr hα1)) hα]

/-! ### The singular gap -/

/-- The **singular gap** below the $k$ largest singular values:
$\sigma_{k-1}(\mathbf{A}) - \sigma_k(\mathbf{A})$ with singular values indexed from $0$, the gap
that separates the leading $k$-dimensional singular subspaces from the rest. The index is the
dimension of those subspaces. With truncated subtraction `singularGap A 0 = 0`, so a hypothesis
`0 < singularGap A k` already excludes $k = 0$. -/
noncomputable def singularGap (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  singularValues A (k - 1) - singularValues A k

/-- The singular gap at dimension zero is zero. -/
@[simp]
theorem singularGap_zero (A : Matrix m n 𝕜) : singularGap A 0 = 0 := by
  rw [singularGap, Nat.zero_sub, sub_self]

/-- The singular gap at dimension $k + 1$ is $\sigma_k(\mathbf{A}) - \sigma_{k+1}(\mathbf{A})$.
This is the form to compute with. -/
theorem singularGap_succ (A : Matrix m n 𝕜) (k : ℕ) :
    singularGap A (k + 1) = singularValues A k - singularValues A (k + 1) := by
  rw [singularGap, Nat.add_sub_cancel]

/-- The singular gap is nonnegative. -/
theorem singularGap_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularGap A k := by
  exact sub_nonneg.mpr (singularValues_antitone A (Nat.sub_le k 1))

/-- Stability of the singular gap: a perturbation changes the gap by at most twice its
spectral norm: writing $\delta_k$ for the singular gap `singularGap`,
$\lvert \delta_k(\mathbf{A}) - \delta_k(\mathbf{B}) \rvert \le 2 \|\mathbf{A} - \mathbf{B}\|_2$. -/
theorem abs_singularGap_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularGap A k - singularGap B k| ≤ 2 * specNorm (A - B) := by
  have h₁ := abs_le.mp (abs_singularValues_sub_le_specNorm A B (k - 1))
  have h₂ := abs_le.mp (abs_singularValues_sub_le_specNorm A B k)
  rw [singularGap, singularGap, abs_le]
  constructor <;> linarith


/-- **A larger range gives a smaller projection residual**, singular value by singular value: if
the range of $\mathbf{Y}$ is contained in the range of $\mathbf{B}$ then
$$\sigma_i((\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}) \le
\sigma_i((\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A})$$
for every $i$, so in every unitarily invariant norm.
[TroppWebber2023, Lemma 5.1]; [HalkoMartinssonTropp2011, Proposition 8.5]; there in the Schatten
and spectral norms. -/
theorem singularValues_one_sub_rangeProjector_mul_le_of_range_le [DecidableEq m]
    {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues ((1 - rangeProjector B) * A) i ≤
      singularValues ((1 - rangeProjector Y) * A) i := by
  have hmul : (1 - rangeProjector B) * (1 - rangeProjector Y) = 1 - rangeProjector B := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      rangeProjector_mul_rangeProjector_of_range_le h, sub_self, sub_zero]
  rw [← hmul, Matrix.mul_assoc]
  exact (isStarProjection_one_sub_rangeProjector B).singularValues_mul_le _ i

/-- The **relative singular gap**
$$\gamma = \frac{\sigma_i(\mathbf{A}) - \sigma_j(\mathbf{A})}{\sigma_i(\mathbf{A}) +
\sigma_j(\mathbf{A})}$$
between the singular values of indices $i$ and $j$ (from $0$), in $[0, 1]$ when $i \le j$
(`NLAlib.singularGapRatio_nonneg`, `NLAlib.singularGapRatio_le_one`). It is the gap of the gapped
bounds for Krylov methods, through $(1 - \gamma)/(1 + \gamma) = \sigma_j/\sigma_i$
(`NLAlib.one_sub_singularGapRatio_div_one_add_singularGapRatio`). Junk value: $0$ when
$\sigma_i(\mathbf{A}) = \sigma_j(\mathbf{A}) = 0$.
[TroppWebber2023, Theorem 9.2]; there $\sigma_r$ and $\sigma_s$ indexed from $1$. -/
noncomputable def singularGapRatio (A : Matrix m n 𝕜) (i j : ℕ) : ℝ :=
  (singularValues A i - singularValues A j) / (singularValues A i + singularValues A j)

/-- The relative singular gap is nonnegative for $i \le j$. -/
theorem singularGapRatio_nonneg (A : Matrix m n 𝕜) {i j : ℕ} (h : i ≤ j) :
    0 ≤ singularGapRatio A i j := by
  exact div_nonneg (sub_nonneg.mpr (singularValues_antitone A h))
    (add_nonneg (singularValues_nonneg A i) (singularValues_nonneg A j))

/-- The relative singular gap is at most $1$. -/
theorem singularGapRatio_le_one (A : Matrix m n 𝕜) (i j : ℕ) : singularGapRatio A i j ≤ 1 := by
  have hi := singularValues_nonneg A i
  have hj := singularValues_nonneg A j
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- The relative singular gap recovers the ratio of the two singular values:
$$\frac{1 - \gamma}{1 + \gamma} = \frac{\sigma_j(\mathbf{A})}{\sigma_i(\mathbf{A})}$$
for $\sigma_i(\mathbf{A}) > 0$. -/
theorem one_sub_singularGapRatio_div_one_add_singularGapRatio (A : Matrix m n 𝕜) {i j : ℕ}
    (hi : 0 < singularValues A i) :
    (1 - singularGapRatio A i j) / (1 + singularGapRatio A i j) =
      singularValues A j / singularValues A i := by
  have hj := singularValues_nonneg A j
  have hsum : singularValues A i + singularValues A j ≠ 0 := by positivity
  rw [singularGapRatio]
  field_simp [hi.ne']
  ring

/-! ### A Chebyshev filter at the relative gap -/

open Polynomial in
/-- **A Chebyshev filter at the relative singular gap**: for a matrix $\mathbf{A}$, a head of
$r = h + 1$ singular values, a tail index $t \ge r$ and a degree $d$, there are a real
polynomial $f$ of degree at most $d$ and constants $c > 0$ and $a$ with
$\lvert f(\sigma_i^2) \rvert \ge c$ for $i < r$, $\lvert f \rvert \le a$ on $[0, \sigma_t^2]$,
and
$$\Bigl(\frac{a}{c}\Bigr)^2 \le 4e^{-8d\sqrt{\gamma}}\,,$$
where $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ is the relative gap
`NLAlib.singularGapRatio A h t` (zero when $\sigma_h = 0$). For $\sigma_t > 0$ the filter is
$f(x) = T_d(2x/\sigma_t^2 - 1)$ with $a = 1$ and $c = \tfrac12 e^{4d\sqrt{\gamma}}$; for
$\sigma_t = 0 < \sigma_h$ it is $x^d$, and for $\sigma_h = 0$ it is $1$: the instance of
`Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_of_le` at the levels $\sigma_h$ and
$\sigma_t$. [MuscoMusco2015, Lemma 5]; there a polynomial normalized at one level and bounded
on $[0, \alpha]$, here the ratio $(a/c)^2$ at two singular values. -/
theorem exists_degree_lt_div_sq_le_exp_singularGapRatio (A : Matrix m n 𝕜) {h r t : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt (singularGapRatio A h t)) := by
  have hht : h ≤ t := by omega
  rcases (singularValues_nonneg A h).eq_or_lt with hσh | hσh
  · -- $\sigma_h = 0$: then $\sigma_t = 0$, the gap ratio is zero and the constant filter does.
    have hσt : singularValues A t = 0 :=
      le_antisymm (hσh ▸ singularValues_antitone A hht) (singularValues_nonneg A t)
    refine ⟨1, by rw [degree_one]; exact_mod_cast Nat.succ_pos d, 1, 1, one_pos,
      fun i _ => by simp, fun x _ => by simp, ?_⟩
    simp [singularGapRatio, hσt, ← hσh]
  obtain ⟨f, hf, c, a, hc, hhead, htail, hac⟩ :=
    Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_of_le
      (singularValues_nonneg A t) (singularValues_antitone A hht) hσh d
  refine ⟨f, hf, c, a, hc, fun i hi => hhead _ ?_, htail, hac⟩
  exact pow_le_pow_left₀ (singularValues_nonneg A h) (singularValues_antitone A (by omega)) 2

end NLAlib
