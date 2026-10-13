/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GaussState

/-!
# The Cholesky factorization

`NLAlib.IsCholesky A L` says that `A = L * Lᴴ` with `L` lower triangular with positive diagonal.
A matrix has a Cholesky factorization exactly when it is positive definite, and the factor is
unique. A positive semidefinite matrix has a factorization with nonnegative diagonal, and after a
symmetric permutation one whose nonzero columns are the first `rank A`.

## Main definitions

* `NLAlib.IsCholesky`: the factorization predicate.
* `NLAlib.choleskyLower`: the factor computed by elimination, for a matrix indexed by `Fin n`.

## Main results

* `NLAlib.IsCholesky.posDef`, `NLAlib.IsCholesky.unique`.
* `NLAlib.exists_isCholesky_iff_posDef`, `Matrix.PosDef.existsUnique_isCholesky`.
* `Matrix.PosDef.isCholesky_choleskyLower`: elimination computes the factorization.
* `Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose`: the pivoted factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [LinearOrder n] [Fintype n]

/-- `IsCholesky A L`: **`A = L * Lᴴ` is a Cholesky factorization**, with `L` lower triangular
with positive diagonal. [GolubVanLoan2013, Theorem 4.2.7]; [HornJohnson2013, Corollary 7.2.9].
Port of `NLAlib.IsCholesky`, there over `ℝ`. -/
structure IsCholesky (A L : Matrix n n 𝕜) : Prop where
  /-- The factor is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal of the factor is positive. -/
  apply_self_pos : ∀ i, 0 < L i i
  /-- The matrix is the factor times its conjugate transpose. -/
  eq_mul_conjTranspose : A = L * Lᴴ

section

variable [DecidableEq n] {A L : Matrix n n 𝕜}

/-- A Cholesky factor is invertible. Port of `NLAlib.IsCholesky.isUnit_det`. -/
theorem IsCholesky.isUnit_det (h : IsCholesky A L) : IsUnit L.det :=
  h.isLowerTriangular.isUnit_det_iff.mpr fun i => (h.apply_self_pos i).ne'.isUnit

omit [DecidableEq n] in
/-- A matrix with a Cholesky factorization is positive definite.
Port of `NLAlib.IsCholesky.posDef`. -/
theorem IsCholesky.posDef (h : IsCholesky A L) : A.PosDef := by
  classical
  rw [h.eq_mul_conjTranspose]
  exact Matrix.PosDef.mul_conjTranspose_self L
    (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det L).mpr h.isUnit_det))

omit [DecidableEq n] in
/-- **The Cholesky factor is unique.** [GolubVanLoan2013, Theorem 4.2.7].
Port of `NLAlib.IsCholesky.unique`. -/
theorem IsCholesky.unique {L' : Matrix n n 𝕜} (h : IsCholesky A L) (h' : IsCholesky A L') :
    L = L' := by
  classical
  have hL := h.isUnit_det
  have hL' := h'.isUnit_det
  have hLt : IsUnit Lᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hL.star
  have hL't : IsUnit L'ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hL'.star
  have hLL : L * Lᴴ = L' * L'ᴴ := h.eq_mul_conjTranspose.symm.trans h'.eq_mul_conjTranspose
  have hDlow : (L'⁻¹ * L).IsLowerTriangular :=
    Matrix.BlockTriangular.mul h'.isLowerTriangular.inv h.isLowerTriangular
  have hD2 : L'⁻¹ * L = L'ᴴ * (Lᴴ)⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * L * (Lᴴ * (Lᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hLt, Matrix.mul_one]
      _ = L'⁻¹ * (L * Lᴴ) * (Lᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L'ᴴ * (Lᴴ)⁻¹ := by
          rw [hLL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul]
  have hDup : (L'⁻¹ * L).IsUpperTriangular := by
    rw [hD2]
    exact Matrix.BlockTriangular.mul h'.isLowerTriangular.conjTranspose
      h.isLowerTriangular.conjTranspose.inv
  have hpos : ∀ i, 0 < (L'⁻¹ * L) i i := fun i => by
    rw [h'.isLowerTriangular.inv.mul_apply_self h.isLowerTriangular,
      h'.isLowerTriangular.inv_apply_self fun j => (h'.apply_self_pos j).ne']
    exact mul_pos (RCLike.inv_pos_of_pos (h'.apply_self_pos i)) (h.apply_self_pos i)
  have hDD : L'⁻¹ * L * (L'⁻¹ * L)ᴴ = 1 := by
    calc L'⁻¹ * L * (L'⁻¹ * L)ᴴ = L'⁻¹ * (L * Lᴴ) * (L'ᴴ)⁻¹ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hLL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hL't]
  have hone : ∀ i, (L'⁻¹ * L) i i = 1 := fun i => by
    have h1 := congrFun (congrFun hDD i) i
    rw [hDlow.mul_apply_self hDup.conjTranspose, Matrix.conjTranspose_apply,
      (IsSelfAdjoint.of_nonneg (hpos i).le).star_eq, Matrix.one_apply_eq] at h1
    have h2 : ((L'⁻¹ * L) i i - 1) * ((L'⁻¹ * L) i i + 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (add_pos (hpos i) one_pos).ne'
  have hD1 : L'⁻¹ * L = 1 := by
    rw [eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hDlow hDup]
    simp only [hone, Matrix.diagonal_one]
  calc L = L' * (L'⁻¹ * L) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL', Matrix.one_mul]
    _ = L' := by rw [hD1, Matrix.mul_one]

/-- The determinant is the product of the squared diagonal of the Cholesky factor.
Port of `NLAlib.det_eq_prod_sq_diag_of_cholesky`. -/
theorem IsCholesky.det_eq_prod (h : IsCholesky A L) : A.det = ∏ i, L i i ^ 2 := by
  rw [h.eq_mul_conjTranspose, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_of_isLowerTriangular _ h.isLowerTriangular, star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(IsSelfAdjoint.of_nonneg (h.apply_self_pos i).le).star_eq, sq]

/-- **Solving through a Cholesky factorization**: `A x = b` exactly when `Lᴴ x = L⁻¹ b`. -/
theorem IsCholesky.mulVec_eq_iff (h : IsCholesky A L) {x b : n → 𝕜} :
    A *ᵥ x = b ↔ Lᴴ *ᵥ x = L⁻¹ *ᵥ b := by
  have hL := h.isUnit_det
  rw [h.eq_mul_conjTranspose, ← Matrix.mulVec_mulVec]
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL, Matrix.one_mulVec]
  · intro hx
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hL, Matrix.one_mulVec]

end

/-! ### Elimination -/

section Recursion

variable {n : ℕ}

/-- The Cholesky factor computed by elimination: column `j` is the pivot column of step `j`
divided by the square root of the pivot. A zero pivot gives a zero column.
Port of `NLAlib.cholesky`, there by recursion on the dimension over `ℝ`. -/
noncomputable def choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j =>
    if j ≤ i then gaussState A j i j / ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) else 0

/-- The factor computed by elimination is lower triangular.
Port of `NLAlib.isLowerTriangular_cholesky`. -/
theorem isLowerTriangular_choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) :
    (choleskyLower A).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp only [choleskyLower, Matrix.of_apply, if_neg hij'.not_ge]

/-- Elimination preserves Hermitian matrices. -/
private theorem isHermitian_gaussState {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (k : ℕ) : (gaussState A k).IsHermitian := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    by_cases hk : k < n
    · rw [gaussState_succ A hk]
      exact ih.eliminationStep _
    · rw [gaussState, dif_neg hk]
      exact ih

/-- Elimination preserves positive semidefinite matrices. -/
private theorem posSemidef_gaussState {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef)
    (k : ℕ) : (gaussState A k).PosSemidef := by
  rw [gaussState_eq_foldl]
  exact hA.foldl_eliminationStep _

/-- Elimination on a positive semidefinite matrix clears the rows of the pivots used, whether
or not the pivots are zero. -/
private theorem gaussState_apply_eq_zero_of_posSemidef {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosSemidef) {k : ℕ} {i : Fin n} (hi : (i : ℕ) < k) (l : Fin n) :
    gaussState A k i l = 0 := by
  induction k generalizing l with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases hk : k < n
    · rw [gaussState_succ A hk]
      by_cases hik : (i : ℕ) = k
      · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
        exact (posSemidef_gaussState hA k).eliminationStep_apply_pivot_left _ l
      · exact eliminationStep_apply_eq_zero_of_row (fun l => ih (by omega) l) _ l
    · rw [gaussState, dif_neg hk]
      exact ih (by have := i.2; omega) l

/-- The diagonal of the factor computed by elimination on a Hermitian matrix. -/
private theorem choleskyLower_apply_self {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (i : Fin n) : choleskyLower A i i = ((√(RCLike.re (gaussState A i i i)) : ℝ) : 𝕜) := by
  simp only [choleskyLower, Matrix.of_apply, le_refl, if_true]
  nth_rewrite 1 [← (isHermitian_gaussState hA i).coe_re_apply_self i]
  rw [← RCLike.ofReal_div, Real.div_sqrt]

/-- The diagonal entry of the computed factor is positive exactly when the pivot is. -/
private theorem choleskyLower_apply_self_pos_iff {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (i : Fin n) :
    0 < choleskyLower A i i ↔ 0 < gaussState A i i i := by
  rw [choleskyLower_apply_self hA, RCLike.ofReal_pos, Real.sqrt_pos,
    ← (isHermitian_gaussState hA i).coe_re_apply_self i, RCLike.ofReal_pos, RCLike.ofReal_re]

/-- The diagonal of the factor computed by elimination on a Hermitian matrix is nonnegative.
Port of `NLAlib.cholesky_apply_self_nonneg`. -/
theorem _root_.Matrix.IsHermitian.choleskyLower_apply_self_nonneg
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (i : Fin n) :
    0 ≤ choleskyLower A i i := by
  rw [choleskyLower_apply_self hA]
  exact RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)

/-- The entries of the product of the computed factor with its conjugate transpose, when the
pivots are nonnegative. -/
private theorem choleskyLower_mul_conjTranspose_apply {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (h0 : ∀ j : Fin n, 0 ≤ gaussState A j j j) (i l : Fin n) :
    (choleskyLower A * (choleskyLower A)ᴴ) i l =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i ∧ j ≤ l),
        (gaussState A j j j)⁻¹ * (gaussState A j i j * gaussState A j j l) := by
  rw [Matrix.mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [choleskyLower, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hji : j ≤ i
  · by_cases hjl : j ≤ l
    · have hsq : ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) *
          ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) = gaussState A j j j := by
        rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (RCLike.nonneg_iff.mp (h0 j)).1,
          (isHermitian_gaussState hA j).coe_re_apply_self j]
      rw [if_pos hji, if_pos hjl, if_pos ⟨hji, hjl⟩, star_div₀, RCLike.star_def,
        RCLike.conj_ofReal, ← RCLike.star_def, (isHermitian_gaussState hA j).apply,
        div_mul_div_comm, hsq]
      ring
    · rw [if_neg hjl, if_neg (not_and_of_not_right _ hjl), star_zero, mul_zero]
  · rw [if_neg hji, if_neg (not_and_of_not_left _ hji), zero_mul]

/-- Elimination factors a Hermitian matrix whose pivots are nonnegative, as soon as a zero
pivot has a zero column. -/
private theorem eq_choleskyLower_mul_conjTranspose_of {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (h0 : ∀ j : Fin n, 0 ≤ gaussState A j j j)
    (hz : ∀ j i : Fin n, gaussState A j j j = 0 → gaussState A j i j = 0) :
    A = choleskyLower A * (choleskyLower A)ᴴ := by
  have hcol : ∀ j i : Fin n, gaussState A ((j : ℕ) + 1) i j = 0 := by
    intro j i
    rw [gaussState_succ A j.2]
    by_cases hp : gaussState A j j j = 0
    · rw [eliminationStep_eq_self_of_apply_self_eq_zero hp]
      exact hz j i hp
    · exact eliminationStep_apply_pivot_right hp i
  have hrow : ∀ j l : Fin n, gaussState A ((j : ℕ) + 1) j l = 0 := by
    intro j l
    rw [← (isHermitian_gaussState hA ((j : ℕ) + 1)).apply, hcol j l, star_zero]
  have ht : ∀ (k : ℕ) (i l : Fin n), A i l = gaussState A k i l +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        (gaussState A j j j)⁻¹ * (gaussState A j i j * gaussState A j j l) := by
    intro k i l
    have h := congrFun (congrFun (eq_gaussState_add_sum A k) i) l
    simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul] using h
  ext i l
  rw [choleskyLower_mul_conjTranspose_apply hA h0]
  rcases le_total i l with hil | hil
  · rw [ht ((i : ℕ) + 1) i l, hrow i l, zero_add]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hil ⊢
    omega
  · rw [ht ((l : ℕ) + 1) i l, hcol l i, zero_add]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hil ⊢
    omega

/-- Elimination factors a positive semidefinite matrix.
Port of `NLAlib.eq_cholesky_mul_transpose_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.eq_choleskyLower_mul_conjTranspose
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    A = choleskyLower A * (choleskyLower A)ᴴ :=
  eq_choleskyLower_mul_conjTranspose_of hA.isHermitian
    (fun j => (posSemidef_gaussState hA j).diag_nonneg)
    fun j i hj => congrFun ((posSemidef_gaussState hA j).col_eq_zero_of_apply_self_eq_zero hj) i

/-- **Elimination computes the Cholesky factorization** of a positive definite matrix.
Port of `NLAlib.isCholesky_cholesky_of_posDef`. -/
theorem _root_.Matrix.PosDef.isCholesky_choleskyLower {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) : IsCholesky A (choleskyLower A) :=
  ⟨isLowerTriangular_choleskyLower A,
    fun i => (choleskyLower_apply_self_pos_iff hA.isHermitian i).mpr
      (hA.gaussState_apply_self_pos i),
    hA.posSemidef.eq_choleskyLower_mul_conjTranspose⟩

/-- **Elimination on a Hermitian matrix produces a positive diagonal exactly when the matrix is
positive definite.** Port of `NLAlib.choleskySucceeds_iff_posDef`. -/
theorem _root_.Matrix.IsHermitian.forall_choleskyLower_apply_self_pos_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (∀ i, 0 < choleskyLower A i i) ↔ A.PosDef := by
  refine ⟨fun h => ?_, fun h => h.isCholesky_choleskyLower.apply_self_pos⟩
  have hp : ∀ j : Fin n, 0 < gaussState A j j j := fun j =>
    (choleskyLower_apply_self_pos_iff hA j).mp (h j)
  exact IsCholesky.posDef ⟨isLowerTriangular_choleskyLower A, h,
    eq_choleskyLower_mul_conjTranspose_of hA (fun j => (hp j).le)
      fun j i hj => absurd hj (hp j).ne'⟩

/-- Diagonal pivoting on a positive semidefinite matrix: a simultaneous permutation of rows and
columns after which the computed factor has exactly `rank A` positive diagonal entries, the
first ones, and zero columns after them. -/
private theorem exists_perm_choleskyLower {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ i : Fin n, 0 < choleskyLower (A.submatrix σ σ) i i ↔ (i : ℕ) < A.rank) ∧
      ∀ i j : Fin n, A.rank ≤ (j : ℕ) → choleskyLower (A.submatrix σ σ) i j = 0 := by
  have hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, RCLike.re (gaussState (A.submatrix (τ.trans σ) (τ.trans σ)) j i i) =
        RCLike.re (gaussState (A.submatrix σ σ) j (τ i) (τ i)) := by
    intro σ τ j hτ i
    have hsub : A.submatrix (τ.trans σ) (τ.trans σ) = (A.submatrix σ σ).submatrix τ τ := rfl
    rw [hsub, gaussState_submatrix _ τ j fun l hl => hτ l (Fin.lt_def.mpr hl)]
    rfl
  obtain ⟨σ, hσ⟩ := exists_perm_forall_le_apply_self
    (fun σ j i => RCLike.re (gaussState (A.submatrix σ σ) j i i)) hs n
  refine ⟨σ, ?_⟩
  have hrank : (A.submatrix σ σ).rank = A.rank := Matrix.rank_submatrix A σ σ
  have hB : (A.submatrix σ σ).PosSemidef := hA.submatrix σ
  generalize A.submatrix σ σ = B at hσ hrank hB
  rw [← hrank]
  have hG := posSemidef_gaussState hB
  -- a zero pivot means that elimination has reached the zero matrix
  have hzero : ∀ j : Fin n, gaussState B j j j = 0 → gaussState B j = 0 := by
    intro j hj
    have hdiag : ∀ i : Fin n, gaussState B j i i = 0 := by
      intro i
      rcases lt_or_ge i j with hij | hij
      · exact gaussState_apply_eq_zero_of_posSemidef hB (Fin.lt_def.mp hij) i
      · have h1 := hσ j i j.2 hij
        rw [hj, map_zero] at h1
        have h2 := (hG j).diag_nonneg (i := i)
        rw [← (hG j).isHermitian.coe_re_apply_self i] at h2 ⊢
        rw [le_antisymm h1 (RCLike.ofReal_nonneg.mp h2), RCLike.ofReal_zero]
    ext i l
    exact congrFun ((hG j).col_eq_zero_of_apply_self_eq_zero (hdiag l)) i
  -- the pivots before the rank are nonzero
  have hne : ∀ (k : ℕ) (i : Fin n), (i : ℕ) = k → k < B.rank → gaussState B i i i ≠ 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik hk hi
      have hp : ∀ l : Fin n, (l : ℕ) < (i : ℕ) → gaussState B l l l ≠ 0 := fun l hl =>
        ih l (hik ▸ hl) l rfl (by omega)
      have hr := rank_gaussState_add B i.2.le hp
      rw [hzero i hi, Matrix.rank_zero] at hr
      omega
  have h0 : gaussState B B.rank = 0 := by
    have hr := rank_gaussState_add B B.rank_le_width fun l hl => hne l l rfl hl
    exact Matrix.rank_eq_zero.mp (by omega)
  refine ⟨fun i => ?_, fun i j hj => ?_⟩
  · rw [choleskyLower_apply_self_pos_iff hB.isHermitian]
    constructor
    · intro hi
      by_contra hlt
      rw [gaussState_eq_zero_of_le h0 (not_lt.mp hlt)] at hi
      exact lt_irrefl _ hi
    · exact fun hi => lt_of_le_of_ne (hG i).diag_nonneg (hne i i rfl hi).symm
  · simp only [choleskyLower, Matrix.of_apply, gaussState_eq_zero_of_le h0 hj, Matrix.zero_apply,
      zero_div, ite_self]

end Recursion

/-! ### Existence -/

section

variable {A : Matrix n n 𝕜}

/-- A Cholesky factorization transported along an order isomorphism of the index type. -/
private theorem IsCholesky.submatrix_orderIso {m : Type*} [LinearOrder m] [Fintype m]
    {L : Matrix n n 𝕜} (h : IsCholesky A L) (e : m ≃o n) :
    IsCholesky (A.submatrix e e) (L.submatrix e e) := by
  refine ⟨h.isLowerTriangular.submatrix_of_strictMono e.strictMono,
    fun i => h.apply_self_pos _, ?_⟩
  rw [h.eq_mul_conjTranspose, Matrix.conjTranspose_submatrix]
  exact (Matrix.submatrix_mul_equiv L Lᴴ e e.toEquiv e).symm

/-- **A matrix has a Cholesky factorization exactly when it is positive definite.**
Port of `NLAlib.exists_isCholesky_iff_posDef`.
Result: cholesky-existence -/
theorem exists_isCholesky_iff_posDef (A : Matrix n n 𝕜) : (∃ L, IsCholesky A L) ↔ A.PosDef := by
  refine ⟨fun ⟨L, h⟩ => h.posDef, fun hA => ?_⟩
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have h := (hA.submatrix e.injective).isCholesky_choleskyLower.submatrix_orderIso e.symm
  have hAe : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp only [Matrix.submatrix_apply, OrderIso.apply_symm_apply]
  rw [hAe] at h
  exact ⟨_, h⟩

/-- A positive definite matrix has exactly one Cholesky factor.
Port of `NLAlib.existsUnique_cholesky_of_posDef`. -/
theorem _root_.Matrix.PosDef.existsUnique_isCholesky (hA : A.PosDef) :
    ∃! L, IsCholesky A L := by
  obtain ⟨L, hL⟩ := (exists_isCholesky_iff_posDef A).mpr hA
  exact ⟨L, hL, fun L' hL' => hL'.unique hL⟩

/-- A positive semidefinite matrix is `L * Lᴴ` for a lower triangular `L` with nonnegative
diagonal. Port of `NLAlib.exists_eq_mul_transpose_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.exists_eq_mul_conjTranspose_of_isLowerTriangular
    (hA : A.PosSemidef) :
    ∃ L : Matrix n n 𝕜, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ A = L * Lᴴ := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have hA' : (A.submatrix e e).PosSemidef := hA.submatrix e
  refine ⟨(choleskyLower (A.submatrix e e)).submatrix e.symm e.symm,
    (isLowerTriangular_choleskyLower _).submatrix_of_strictMono e.symm.strictMono,
    fun i => hA'.isHermitian.choleskyLower_apply_self_nonneg _, ?_⟩
  rw [Matrix.conjTranspose_submatrix]
  refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ e.symm e.symm.toEquiv e.symm).symm
  rw [← hA'.eq_choleskyLower_mul_conjTranspose]
  ext i j
  simp only [Matrix.submatrix_apply, OrderIso.apply_symm_apply]

/-- **Pivoted Cholesky.** A positive semidefinite matrix has, after a symmetric permutation, a
factorization `L * Lᴴ` with `L` lower triangular whose first `rank A` diagonal entries are
positive and whose remaining columns vanish. [Higham2002, Theorem 10.9].
Port of `NLAlib.isPivotedCholesky_choleskyPivoted`, with the rank statements
`NLAlib.choleskyPivoted_apply_self_pos_iff_lt_rank` and
`NLAlib.choleskyPivoted_apply_eq_zero_of_rank_le`, which the prototype leaves unproved. -/
theorem _root_.Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose [LocallyFiniteOrderBot n]
    (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm n) (L : Matrix n n 𝕜), L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧
      A.submatrix σ σ = L * Lᴴ ∧ (∀ i, 0 < L i i ↔ (Finset.Iio i).card < A.rank) ∧
      ∀ i j, A.rank ≤ (Finset.Iio j).card → L i j = 0 := by
  set e := Fintype.orderIsoFinOfCardEq n rfl with he
  have hA' : (A.submatrix e e).PosSemidef := hA.submatrix e
  obtain ⟨σ, hpos, hzero⟩ := exists_perm_choleskyLower hA'
  have hB : ((A.submatrix e e).submatrix σ σ).PosSemidef := hA'.submatrix σ
  have hrank : (A.submatrix e e).rank = A.rank := Matrix.rank_submatrix A e.toEquiv e.toEquiv
  have hcard : ∀ i : n, (Finset.Iio i).card = (e.symm i : ℕ) := by
    intro i
    rw [← Fin.card_Iio, ← Finset.card_image_of_injective _ e.injective]
    congr 1
    refine Finset.coe_injective ?_
    rw [Finset.coe_image, Finset.coe_Iio, Finset.coe_Iio, OrderIso.image_Iio,
      OrderIso.apply_symm_apply]
  rw [hrank] at hpos hzero
  refine ⟨(e.symm.toEquiv.trans σ).trans e.toEquiv,
    (choleskyLower ((A.submatrix e e).submatrix σ σ)).submatrix e.symm e.symm,
    (isLowerTriangular_choleskyLower _).submatrix_of_strictMono e.symm.strictMono,
    fun i => hB.isHermitian.choleskyLower_apply_self_nonneg _, ?_,
    fun i => by rw [hcard]; exact hpos _, fun i j hj => hzero _ _ (by rwa [hcard] at hj)⟩
  rw [Matrix.conjTranspose_submatrix]
  refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ e.symm e.symm.toEquiv e.symm).symm
  rw [← hB.eq_choleskyLower_mul_conjTranspose]
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.trans_apply, RelIso.coe_fn_toEquiv]

end

end NLAlib
