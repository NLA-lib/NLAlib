/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Inequalities for singular values

Singular values are subadditive in Weyl's sense, `1`-Lipschitz in the spectral norm,
submultiplicative, decrease under projections and under passing to submatrices, and move by at
most `r` positions under a perturbation of rank `r`. Because singular values are padded with
zeros, none of these statements carries an index side condition.

`NLAlib.singularGap A k` is the gap `singularValues A (k - 1) - singularValues A k` separating the
`k` largest singular values from the rest.

## Main definitions

* `NLAlib.singularGap`: the gap below the `k` largest singular values.

## Main results

* `NLAlib.singularValues_add_le`: Weyl's inequality for singular values.
* `NLAlib.abs_singularValues_sub_le_specNorm`: singular values are `1`-Lipschitz.
* `NLAlib.singularValues_mul_le_specNorm_mul`, `NLAlib.singularValues_mul_add_le`: products.
* `NLAlib.singularValues_add_le_of_rank_le`: low-rank perturbations.
* `NLAlib.singularValues_submatrix_le`: submatrices.
* `IsStarProjection.singularValues_mul_le`: projections.
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

/-- **Weyl's inequality for singular values.** `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`, for all
indices from `0`. [HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_add_add_le`.
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

/-- A perturbation raises each singular value by at most its spectral norm.
Port of `NLAlib.singularValues_add_le_add_specNorm`. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix m n 𝕜) (k : ℕ) :
    singularValues (A + E) k ≤ singularValues A k + specNorm E := by
  have h := singularValues_add_le A E k 0
  rwa [add_zero, singularValues_zero_eq_specNorm] at h

/-- **Singular values are `1`-Lipschitz in the spectral norm.**
[HornJohnson2013, Corollary 7.3.5].
Port of `NLAlib.abs_singularValues_sub_le_specNorm`.
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

/-- Singular values are `1`-Lipschitz in the Frobenius norm.
Port of `NLAlib.abs_singularValues_sub_le_frobNorm`. -/
theorem abs_singularValues_sub_le_frobNorm (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularValues A k - singularValues B k| ≤ frobNorm (A - B) := by
  exact (abs_singularValues_sub_le_specNorm A B k).trans (specNorm_le_frobNorm _)

/-- **Low-rank perturbation.** If `B` has rank at most `r` then `σ_{k+r}(A + B) ≤ σ_k(A)`.
[HornJohnson1991, Theorem 3.3.16].
Result: low-rank-interlacing -/
theorem singularValues_add_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {r : ℕ}
    (hB : B.rank ≤ r) (k : ℕ) : singularValues (A + B) (k + r) ≤ singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_norm_mulVec_le A k
  refine singularValues_le_of_forall_mem (A + B) (W ⊓ LinearMap.ker B.mulVecLin) ?_
    (singularValues_nonneg A k) fun x hx => ?_
  · have h₁ := Submodule.finrank_add_finrank_le_card_add_finrank_inf W (LinearMap.ker B.mulVecLin)
    have h₂ := Matrix.finrank_ker_mulVecLin_add_rank B
    omega
  · have hx₂ : B *ᵥ x = 0 := LinearMap.mem_ker.mp hx.2
    rw [Matrix.add_mulVec, hx₂, add_zero]
    exact hA x hx.1

/-- **Low-rank perturbation, lower.** If `B` has rank at most `r` then `σ_{k+r}(A) ≤ σ_k(A + B)`:
the mirror of `NLAlib.singularValues_add_le_of_rank_le`.
[HornJohnson1991, Theorem 3.3.16].
Result: low-rank-interlacing -/
theorem singularValues_le_singularValues_add_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜}
    {r : ℕ} (hB : B.rank ≤ r) (k : ℕ) :
    singularValues A (k + r) ≤ singularValues (A + B) k := by
  have h := singularValues_add_le_of_rank_le (A + B) ((Matrix.rank_neg B).trans_le hB) k
  rwa [add_neg_cancel_right] at h

/-- Subtracting a matrix of rank at most `k` lowers the index of a singular value by at most
`k`: `σ_{k+i}(A) ≤ σ_i(A - B)`. With `i = 0` this is the Eckart–Young lower bound in the spectral
norm. [HornJohnson1991, Theorem 3.3.16]. -/
theorem singularValues_add_le_singularValues_sub_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) (i : ℕ) :
    singularValues A (k + i) ≤ singularValues (A - B) i := by
  have h := singularValues_add_le_of_rank_le (A - B) hB i
  rwa [sub_add_cancel, add_comm] at h

/-! ### Products -/

/-- A left factor scales singular values by at most its spectral norm.
[HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_mul_le_specNorm_mul`. -/
theorem singularValues_mul_le_specNorm_mul (B : Matrix l m 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (B * A) k ≤ specNorm B * singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_norm_mulVec_le A k
  refine singularValues_le_of_forall_mem (B * A) W hW
    (mul_nonneg (specNorm_nonneg B) (singularValues_nonneg A k)) fun x hx => ?_
  rw [← Matrix.mulVec_mulVec, mul_assoc]
  exact (norm_toLp_mulVec_le B _).trans
    (mul_le_mul_of_nonneg_left (hA x hx) (specNorm_nonneg B))

/-- A right factor scales singular values by at most its spectral norm.
Port of `NLAlib.singularValues_mul_le_mul_specNorm`. -/
theorem singularValues_mul_le_mul_specNorm (A : Matrix m n 𝕜) (C : Matrix n p 𝕜) (k : ℕ) :
    singularValues (A * C) k ≤ singularValues A k * specNorm C := by
  have h := singularValues_mul_le_specNorm_mul Cᴴ Aᴴ k
  rwa [← Matrix.conjTranspose_mul, singularValues_conjTranspose, singularValues_conjTranspose,
    specNorm_conjTranspose, mul_comm] at h

/-- **Singular values of a product.** `σ_{i+j}(A * B) ≤ σ_i(A) * σ_j(B)`.
[HornJohnson1991, Theorem 3.3.16].
Port of `NLAlib.singularValues_mul_add_le`, there over `ℝ`.
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
/-- The Gram matrix of a product, as a conjugation of the Gram matrix of the left factor. -/
private theorem conjTranspose_mul_mul_mul (T : Matrix l m 𝕜) (X : Matrix m n 𝕜) :
    (T * X)ᴴ * (T * X) = Xᴴ * (Tᴴ * T) * X := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype n] in
/-- Conjugating a real multiple of the identity gives that multiple of the Gram matrix. -/
private theorem conjTranspose_mul_smul_one_mul [DecidableEq m] (a : ℝ) (X : Matrix m n 𝕜) :
    Xᴴ * a • (1 : Matrix m m 𝕜) * X = a • (Xᴴ * X) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- A left factor `T` with `Tᴴ * T ≤ a • 1` enlarges squared singular values by at most `a`. -/
theorem sq_singularValues_mul_le_of_conjTranspose_mul_self_le [DecidableEq m]
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
    rw [conjTranspose_mul_smul_one_mul, ← conjTranspose_mul_mul_mul] at hle
    have hk := eigenvalue_le_eigenvalue_of_le hle (Matrix.isHermitian_conjTranspose_mul_self _) k
    rwa [eigenvalue_real_smul _ ha,
      ← sq_singularValues, ← sq_singularValues] at hk

/-- A left factor `T` with `a • 1 ≤ Tᴴ * T` shrinks squared singular values by at most `a`. This
is how a subspace embedding transfers singular values from the sketched matrix to the original
one. -/
theorem mul_sq_singularValues_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) (k : ℕ) :
    a * singularValues X k ^ 2 ≤ singularValues (T * X) k ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · have hle := conjTranspose_mul_mul_le_conjTranspose_mul_mul h X
    rw [conjTranspose_mul_smul_one_mul, ← conjTranspose_mul_mul_mul] at hle
    have hk := eigenvalue_le_eigenvalue_of_le hle
      ((Matrix.isHermitian_conjTranspose_mul_self X).smul (IsSelfAdjoint.all a)) k
    rwa [eigenvalue_real_smul _ ha,
      ← sq_singularValues, ← sq_singularValues] at hk
  · exact (mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)).trans (sq_nonneg _)

/-! ### Submatrices and projections -/

/-- Selecting columns by an injective map does not increase any singular value. -/
private theorem singularValues_submatrix_cols_le (A : Matrix m n 𝕜) {c : p → n}
    (hc : Function.Injective c) (k : ℕ) :
    singularValues (A.submatrix id c) k ≤ singularValues A k := by
  classical
  rw [← mul_selectionMatrix]
  exact (singularValues_mul_le_mul_specNorm A _ k).trans (mul_le_of_le_one_right
    (singularValues_nonneg A k) (hasOrthonormalCols_selectionMatrix hc).specNorm_le_one)

/-- **Singular values of a submatrix.** A submatrix selected by injective maps has singular
values at most those of the matrix. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_submatrix_rows_le` and `NLAlib.singularValues_submatrix_cols_le`,
there over `ℝ`.
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

/-- **Interlacing for deleted columns.** If `c` selects `card p` of the `card p + d` columns of
`A`, then `σ_{k+d}(A) ≤ σ_k(A.submatrix id c)`. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_le_submatrix_cols`, there over `ℝ` with truncated subtraction.
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
    rw [sq_singularValues, sq_singularValues, hG]
    exact (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalue_le_eigenvalue_submatrix
      hc hk hd
  · rw [singularValues_of_card_cols_le A (by omega)]
    exact singularValues_nonneg _ k

/-- **Interlacing for deleted rows.** If `r` selects `card l` of the `card l + d` rows of `A`,
then `σ_{k+d}(A) ≤ σ_k(A.submatrix r id)`. [HornJohnson1991, Corollary 3.1.3].
Port of `NLAlib.singularValues_le_submatrix_rows`, there over `ℝ` with truncated subtraction.
Result: singular-value-interlacing -/
theorem singularValues_le_singularValues_submatrix_rows (A : Matrix m n 𝕜) {r : l → m}
    (hr : Function.Injective r) {d : ℕ} (hd : Fintype.card l + d = Fintype.card m) (k : ℕ) :
    singularValues A (k + d) ≤ singularValues (A.submatrix r id) k := by
  have h := singularValues_le_singularValues_submatrix_cols Aᴴ hr hd k
  rwa [singularValues_conjTranspose, ← singularValues_conjTranspose (Aᴴ.submatrix id r),
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose] at h

/-- Left multiplication by an orthogonal projector does not increase any singular value.
Port of `NLAlib.singularValues_residual_le`, there for the residual of an orthonormal `Q`. -/
theorem _root_.IsStarProjection.singularValues_mul_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (P * A) k ≤ singularValues A k := by
  exact (singularValues_mul_le_specNorm_mul P A k).trans
    (mul_le_of_le_one_left (singularValues_nonneg A k) hP.specNorm_le_one)

/-- The projection residual has singular values at most those of the matrix. -/
theorem singularValues_one_sub_rangeProjector_mul_le [DecidableEq m] (Y : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues ((1 - rangeProjector Y) * A) k ≤ singularValues A k := by
  exact (isStarProjection_one_sub_rangeProjector Y).singularValues_mul_le A k

/-! ### The singular gap -/

/-- The **singular gap** below the `k` largest singular values: `σ_{k-1}(A) - σ_k(A)` with
singular values indexed from `0`, the gap that separates the leading `k`-dimensional singular
subspaces from the rest. The index is the dimension of those subspaces. With truncated
subtraction `singularGap A 0 = 0`, so a hypothesis `0 < singularGap A k` already excludes
`k = 0`. -/
noncomputable def singularGap (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  singularValues A (k - 1) - singularValues A k

/-- The singular gap at dimension zero is zero. -/
@[simp]
theorem singularGap_zero (A : Matrix m n 𝕜) : singularGap A 0 = 0 := by
  rw [singularGap, Nat.zero_sub, sub_self]

/-- The singular gap at dimension `k + 1` is `σ_k - σ_{k+1}`. This is the form to compute
with. -/
theorem singularGap_succ (A : Matrix m n 𝕜) (k : ℕ) :
    singularGap A (k + 1) = singularValues A k - singularValues A (k + 1) := by
  rw [singularGap, Nat.add_sub_cancel]

/-- The singular gap is nonnegative. -/
theorem singularGap_nonneg (A : Matrix m n 𝕜) (k : ℕ) : 0 ≤ singularGap A k := by
  exact sub_nonneg.mpr (singularValues_antitone A (Nat.sub_le k 1))

/-- **Stability of the singular gap.** A perturbation changes the gap by at most twice its
spectral norm. -/
theorem abs_singularGap_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |singularGap A k - singularGap B k| ≤ 2 * specNorm (A - B) := by
  have h₁ := abs_le.mp (abs_singularValues_sub_le_specNorm A B (k - 1))
  have h₂ := abs_le.mp (abs_singularValues_sub_le_specNorm A B k)
  rw [singularGap, singularGap, abs_le]
  constructor <;> linarith

end NLAlib
